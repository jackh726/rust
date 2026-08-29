use rustc_mir_dataflow::points::PointIndex;

use super::LiveLoans;
use crate::dataflow::BorrowIndex;

fn point(index: usize) -> PointIndex {
    PointIndex::from_usize(index)
}

const LOAN: BorrowIndex = BorrowIndex::ZERO;

fn is_live(live_loans: &LiveLoans, loan: BorrowIndex, index: usize) -> bool {
    live_loans.first_dead_in(loan, point(index), point(index)).is_none()
}

#[test]
fn insert_and_query() {
    let mut live_loans = LiveLoans::new(2, 200);
    let other = BorrowIndex::from_u32(1);

    assert!(!is_live(&live_loans, LOAN, 0));
    live_loans.insert(point(0), LOAN);
    live_loans.insert(point(63), LOAN);
    live_loans.insert(point(64), LOAN);
    live_loans.insert(point(199), LOAN);

    for index in 0..200 {
        let expected = matches!(index, 0 | 63 | 64 | 199);
        assert_eq!(is_live(&live_loans, LOAN, index), expected, "point {index}");
        // A loan that was never recorded is live nowhere.
        assert!(!is_live(&live_loans, other, index));
    }
}

#[test]
fn first_dead_in_a_row_that_was_never_recorded() {
    let live_loans = LiveLoans::new(1, 100);
    assert_eq!(live_loans.first_dead_in(LOAN, point(10), point(20)), Some(point(10)));
}

#[test]
fn first_dead_in_within_and_across_words() {
    let mut live_loans = LiveLoans::new(1, 300);
    // Live over 10..=70 and 100..=250, crossing word boundaries at 64, 128 and 192.
    for index in (10..=70).chain(100..=250) {
        live_loans.insert(point(index), LOAN);
    }

    // Fully live ranges, within a word and across words.
    assert_eq!(live_loans.first_dead_in(LOAN, point(10), point(20)), None);
    assert_eq!(live_loans.first_dead_in(LOAN, point(10), point(70)), None);
    assert_eq!(live_loans.first_dead_in(LOAN, point(100), point(250)), None);

    // The first dead point, whether it is in the same word as the start or a later one.
    assert_eq!(live_loans.first_dead_in(LOAN, point(60), point(80)), Some(point(71)));
    assert_eq!(live_loans.first_dead_in(LOAN, point(10), point(299)), Some(point(71)));
    assert_eq!(live_loans.first_dead_in(LOAN, point(200), point(299)), Some(point(251)));

    // A dead start point is found immediately, and the range is inclusive at both ends.
    assert_eq!(live_loans.first_dead_in(LOAN, point(0), point(5)), Some(point(0)));
    assert_eq!(live_loans.first_dead_in(LOAN, point(71), point(71)), Some(point(71)));
    assert_eq!(live_loans.first_dead_in(LOAN, point(70), point(70)), None);
    assert_eq!(live_loans.first_dead_in(LOAN, point(250), point(251)), Some(point(251)));

    // Exact word boundaries.
    assert_eq!(live_loans.first_dead_in(LOAN, point(63), point(64)), None);
    assert_eq!(live_loans.first_dead_in(LOAN, point(128), point(191)), None);
    assert_eq!(live_loans.first_dead_in(LOAN, point(192), point(255)), Some(point(251)));
}
