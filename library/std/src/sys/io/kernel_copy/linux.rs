//! This module contains specializations that can offload `io::copy()` operations on file descriptor
//! containing types (`File`, `TcpStream`, etc.) to more efficient syscalls than `read(2)` and `write(2)`.
//!
//! Specialization is only applied to wholly std-owned types so that user code can't observe
//! that the `Read` and `Write` traits are not used.
//!
//! Since a copy operation involves a reader and writer side where each can consist of different types
//! and also involve generic wrappers (e.g. `Take`, `BufReader`) it is not practical to specialize
//! a single method on all possible combinations.
//!
//! Instead readers and writers are handled separately by the `CopyRead` and `CopyWrite` specialization
//! traits and then specialized on by the `Copier::copy` method.
//!
//! `Copier` uses the specialization traits to unpack the underlying file descriptors and
//! additional prerequisites and constraints imposed by the wrapper types.
//!
//! Once it has obtained all necessary pieces and brought any wrapper types into a state where they
//! can be safely bypassed it will attempt to use the `copy_file_range(2)`,
//! `sendfile(2)` or `splice(2)` syscalls to move data directly between file descriptors.
//! Since those syscalls have requirements that cannot be fully checked in advance it attempts
//! to use them one after another (guided by hints) to figure out which one works and
//! falls back to the generic read-write copy loop if none of them does.
//! Once a working syscall is found for a pair of file descriptors it will be called in a loop
//! until the copy operation is completed.
//!
//! Advantages of using these syscalls:
//!
//! * fewer context switches since reads and writes are coalesced into a single syscall
//!   and more bytes are transferred per syscall. This translates to higher throughput
//!   and fewer CPU cycles, at least for sufficiently large transfers to amortize the initial probing.
//! * `copy_file_range` creates reflink copies on CoW filesystems, thus moving less data and
//!   consuming less disk space
//! * `sendfile` and `splice` can perform zero-copy IO under some circumstances while
//!   a naive copy loop would move every byte through the CPU.
//!
//! Drawbacks:
//!
//! * copy operations smaller than the default buffer size can under some circumstances, especially
//!   on older kernels, incur more syscalls than the naive approach would. As mentioned above
//!   the syscall selection is guided by hints to minimize this possibility but they are not perfect.
//! * optimizations only apply to std types. If a user adds a custom wrapper type, e.g. to report
//!   progress, they can hit a performance cliff.
//! * complexity

#[cfg(not(any(all(target_os = "linux", target_env = "gnu"), target_os = "hurd")))]
use libc::sendfile as sendfile64;
#[cfg(any(all(target_os = "linux", target_env = "gnu"), target_os = "hurd"))]
use libc::sendfile64;
use libc::{EBADF, EINVAL, ENOSYS, EOPNOTSUPP, EOVERFLOW, EPERM, EXDEV};

use super::CopyState;
use crate::cmp::min;
use crate::fs::{File, Metadata};
use crate::io::{
    BufRead, BufReader, BufWriter, Error, PipeReader, PipeWriter, Read, Result, StderrLock,
    StdinLock, StdoutLock, Take, Write,
};
use crate::mem::ManuallyDrop;
use crate::net::TcpStream;
use crate::os::unix::fs::FileTypeExt;
use crate::os::unix::io::{AsRawFd, FromRawFd, RawFd};
use crate::os::unix::net::UnixStream;
use crate::process::{ChildStderr, ChildStdin, ChildStdout};
use crate::ptr;
use crate::sync::atomic::{Atomic, AtomicBool, AtomicU8, Ordering};
use crate::sys::cvt;
use crate::sys::fs::CachedFileMetadata;
use crate::sys::weak::syscall;

#[cfg(test)]
mod tests;

pub fn kernel_copy<R: Read + ?Sized, W: Write + ?Sized>(
    read: &mut R,
    write: &mut W,
) -> Result<CopyState> {
    let copier = Copier { read, write };
    SpecCopy::copy(copier)
}

/// This type represents either the inferred `FileType` of a `RawFd` based on the source
/// type from which it was extracted or the actual metadata
///
/// The methods on this type only provide hints, due to `AsRawFd` and `FromRawFd` the inferred
/// type may be wrong.
enum FdMeta {
    Metadata(Metadata),
    Socket,
    Pipe,
    /// We don't have any metadata because the stat syscall failed
    NoneObtained,
}

#[derive(PartialEq)]
enum FdHandle {
    Input,
    Output,
}

impl FdMeta {
    fn maybe_fifo(&self) -> bool {
        match self {
            FdMeta::Metadata(meta) => meta.file_type().is_fifo(),
            FdMeta::Socket => false,
            FdMeta::Pipe => true,
            FdMeta::NoneObtained => true,
        }
    }

    fn potential_sendfile_source(&self) -> bool {
        match self {
            // procfs erroneously shows 0 length on non-empty readable files.
            // and if a file is truly empty then a `read` syscall will determine that and skip the write syscall
            // thus there would be benefit from attempting sendfile
            FdMeta::Metadata(meta)
                if meta.file_type().is_file() && meta.len() > 0
                    || meta.file_type().is_block_device() =>
            {
                true
            }
            _ => false,
        }
    }

    fn copy_file_range_candidate(&self, f: FdHandle) -> bool {
        match self {
            // copy_file_range will fail on empty procfs files. `read` can determine whether EOF has been reached
            // without extra cost and skip the write, thus there is no benefit in attempting copy_file_range
            FdMeta::Metadata(meta) if f == FdHandle::Input && meta.is_file() && meta.len() > 0 => {
                true
            }
            FdMeta::Metadata(meta) if f == FdHandle::Output && meta.is_file() => true,
            _ => false,
        }
    }
}

/// Returns true either if changes made to the source after a sendfile/splice call won't become
/// visible in the sink or the source has explicitly opted into such behavior (e.g. by splicing
/// a file into a pipe, the pipe being the source in this case).
///
/// This will prevent File -> Pipe and File -> Socket splicing/sendfile optimizations to uphold
/// the Read/Write API semantics of io::copy.
///
/// Note: This is not 100% airtight, the caller can use the RawFd conversion methods to turn a
/// regular file into a TcpSocket which will be treated as a socket here without checking.
fn safe_kernel_copy(source: &FdMeta, sink: &FdMeta) -> bool {
    match (source, sink) {
        // Data arriving from a socket is safe because the sender can't modify the socket buffer.
        // Data arriving from a pipe is safe(-ish) because either the sender *copied*
        // the bytes into the pipe OR explicitly performed an operation that enables zero-copy,
        // thus promising not to modify the data later.
        (FdMeta::Socket, _) => true,
        (FdMeta::Pipe, _) => true,
        (FdMeta::Metadata(meta), _)
            if meta.file_type().is_fifo() || meta.file_type().is_socket() =>
        {
            true
        }
        // Data going into non-pipes/non-sockets is safe because the "later changes may become visible" issue
        // only happens for pages sitting in send buffers or pipes.
        (_, FdMeta::Metadata(meta))
            if !meta.file_type().is_fifo() && !meta.file_type().is_socket() =>
        {
            true
        }
        _ => false,
    }
}

struct CopyParams(FdMeta, Option<RawFd>);

struct Copier<'a, 'b, R: Read + ?Sized, W: Write + ?Sized> {
    read: &'a mut R,
    write: &'b mut W,
}

trait SpecCopy {
    fn copy(self) -> Result<CopyState>;
}

impl<R: Read + ?Sized, W: Write + ?Sized> SpecCopy for Copier<'_, '_, R, W> {
    fn copy(self) -> Result<CopyState> {
        Ok(CopyState::Fallback(0))
    }
}

fn fd_to_meta<T: AsRawFd>(fd: &T) -> FdMeta {
    let fd = fd.as_raw_fd();
    let file: ManuallyDrop<File> = ManuallyDrop::new(unsafe { File::from_raw_fd(fd) });
    match file.metadata() {
        Ok(meta) => FdMeta::Metadata(meta),
        Err(_) => FdMeta::NoneObtained,
    }
}
