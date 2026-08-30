use super::loan_set::{BATCH_SIZE, LoanSet};

#[test]
fn loans() {
    let empty = LoanSet::EMPTY;
    assert!(empty.is_empty());
    assert_eq!(empty.iter().count(), 0);

    let a = LoanSet::single(0);
    let b = LoanSet::single(BATCH_SIZE - 1);
    let both = a.union(b);
    assert!(!both.is_empty());
    assert_eq!(both.iter().collect::<Vec<_>>(), vec![0, BATCH_SIZE - 1]);

    assert_eq!(both.difference(a), b);
    assert_eq!(both.difference(both), empty);
    assert_eq!(a.difference(b), a);

    let mut set = LoanSet::single(3);
    set.insert(LoanSet::single(1));
    set.insert(LoanSet::single(3));
    assert_eq!(set.iter().collect::<Vec<_>>(), vec![1, 3]);
}
