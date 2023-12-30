use std::fmt::{self, Display, Formatter};
use std::ops::Neg;

use serde::{Deserialize, Serialize};

pub type Centipawns = i16;

const MAX_CENTIPAWNS: Centipawns = 30_000;
const MIN_CENTIPAWNS: Centipawns = -MAX_CENTIPAWNS;
const CHECKMATED_VALUE: Centipawns = Centipawns::MAX - 1;

#[derive(Clone, Copy, Debug, Deserialize, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
pub struct Evaluation(Centipawns);

impl Evaluation {

    /// A theoretical evaluation worse than checkmate in 1 for the opponent.
    pub const NEG_INFINITY: Evaluation = Evaluation(-Centipawns::MAX);

    /// A theoretical evaluation better than checkmate in 1 for the active player.
    pub const INFINITY: Evaluation = Evaluation(Centipawns::MAX);

    pub const ZERO: Evaluation = Evaluation(0);
    pub const CHECKMATED: Evaluation = Evaluation(-CHECKMATED_VALUE);

    #[inline]
    pub fn from_centipawns_unchecked(centipawns: Centipawns) -> Evaluation {
        Evaluation(centipawns)
    }

    #[inline]
    pub fn from_centipawns(centipawns: Centipawns) -> Option<Evaluation> {
        let evaluation = Evaluation(centipawns);

        if evaluation.is_forced_checkmate() {
            None
        }
        else {
            Some(evaluation)
        }
    }

    #[inline]
    pub fn in_previous_turn(self) -> Evaluation {
        let mut evaluation = Evaluation(-self.0);

        if evaluation.is_forced_checkmate_for_turn() {
            evaluation.0 -= 1;
        }

        evaluation
    }

    #[inline]
    pub fn is_forced_checkmate(self) -> bool {
        self.is_forced_checkmate_for_turn() || self.is_forced_checkmate_for_opponent()
    }

    #[inline]
    pub fn is_forced_checkmate_for_turn(self) -> bool {
        self.0 > MAX_CENTIPAWNS
    }

    #[inline]
    pub fn is_forced_checkmate_for_opponent(self) -> bool {
        self.0 < MIN_CENTIPAWNS
    }

    pub fn as_centipawns(self) -> Option<Centipawns> {
        if self.is_forced_checkmate() {
            None
        }
        else {
            Some(self.0)
        }
    }

    pub fn as_checkmate_in(self) -> Option<Centipawns> {
        if self.is_forced_checkmate() {
            Some((CHECKMATED_VALUE - self.0.abs()) * self.0.signum())
        }
        else {
            None
        }
    }

    #[inline]
    pub fn min(self, other: Evaluation) -> Evaluation {
        Evaluation(self.0.min(other.0))
    }

    #[inline]
    pub fn max(self, other: Evaluation) -> Evaluation {
        Evaluation(self.0.max(other.0))
    }
}

impl Neg for Evaluation {
    type Output = Evaluation;

    fn neg(self) -> Evaluation {
        Evaluation(-self.0)
    }
}

impl Display for Evaluation {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if let Some(checkmate_in) = self.as_checkmate_in() {
            write!(f, "#{checkmate_in}")
        }
        else {
            let centipawns = self.as_centipawns().unwrap();

            if centipawns.is_negative() {
                write!(f, "-")?;
            }

            let pawns = centipawns.abs() / 100;
            let sub_pawn_centipawns = centipawns.abs() - pawns * 100;

            write!(f, "{pawns}.{sub_pawn_centipawns:02}")
        }
    }
}

#[cfg(test)]
mod tests {
    use kernal::num::{Signed, Zero};
    use kernal::prelude::*;

    use rstest::rstest;

    use super::*;

    impl Zero for Evaluation {
        const ZERO: Self = Evaluation::ZERO;
    }

    impl Signed for Evaluation { }

    #[rstest]
    #[case::zero(0, Some(0))]
    #[case::positive_centipawns(25, Some(25))]
    #[case::max_centipawns(MAX_CENTIPAWNS, Some(MAX_CENTIPAWNS))]
    #[case::negative_centipawns(-42, Some(-42))]
    #[case::min_centipawns(MIN_CENTIPAWNS, Some(MIN_CENTIPAWNS))]
    #[case::maximally_long_checkmate_for_turn(MAX_CENTIPAWNS + 1, None)]
    #[case::maximally_long_checkmate_for_opponent(MIN_CENTIPAWNS - 1, None)]
    #[case::checkmate_in_1_for_turn(CHECKMATED_VALUE - 1, None)]
    #[case::checkmate_in_1_for_for_opponent(-CHECKMATED_VALUE + 1, None)]
    #[case::checkmated_opponent(CHECKMATED_VALUE, None)]
    #[case::checkmated_turn(-CHECKMATED_VALUE, None)]
    fn centipawn_eval(#[case] value: Centipawns, #[case] expected_centipawns: Option<Centipawns>) {
        let evaluation = Evaluation(value);

        assert_that!(evaluation.as_centipawns()).is_equal_to(expected_centipawns);
    }

    #[rstest]
    #[case::zero(0, None)]
    #[case::positive_centipawns(25, None)]
    #[case::max_centipawns(MAX_CENTIPAWNS, None)]
    #[case::negative_centipawns(-42, None)]
    #[case::min_centipawns(MIN_CENTIPAWNS, None)]
    #[case::checkmate_in_1_for_turn(CHECKMATED_VALUE - 1, Some(1))]
    #[case::checkmate_in_1_for_for_opponent(-CHECKMATED_VALUE + 1, Some(-1))]
    #[case::longer_checkmate_for_turn(CHECKMATED_VALUE - 5, Some(5))]
    #[case::longer_checkmate_for_for_opponent(-CHECKMATED_VALUE + 5, Some(-5))]
    #[case::maximally_long_checkmate_for_turn(MAX_CENTIPAWNS + 1,
        Some(CHECKMATED_VALUE - 1 - MAX_CENTIPAWNS))]
    #[case::maximally_long_checkmate_for_opponent(MIN_CENTIPAWNS - 1,
        Some(MAX_CENTIPAWNS - CHECKMATED_VALUE + 1))]
    #[case::checkmated_opponent(CHECKMATED_VALUE, Some(0))]
    #[case::checkmated_turn(-CHECKMATED_VALUE, Some(0))]
    fn checkmate_in_eval(#[case] value: Centipawns, #[case] expected_checkmate_in: Option<Centipawns>) {
        let evaluation = Evaluation(value);

        assert_that!(evaluation.as_checkmate_in()).is_equal_to(expected_checkmate_in);
    }

    #[rstest]
    #[case::zero(0, 0)]
    #[case::positive_centipawns(25, -25)]
    #[case::max_centipawns(MAX_CENTIPAWNS, MIN_CENTIPAWNS)]
    #[case::negative_centipawns(-42, 42)]
    #[case::min_centipawns(MIN_CENTIPAWNS, MAX_CENTIPAWNS)]
    #[case::checkmated_opponent(CHECKMATED_VALUE, -CHECKMATED_VALUE)]
    #[case::checkmated_turn(-CHECKMATED_VALUE, CHECKMATED_VALUE - 1)]
    #[case::checkmate_in_1_for_turn(CHECKMATED_VALUE - 1, -CHECKMATED_VALUE + 1)]
    #[case::checkmate_in_1_for_for_opponent(-CHECKMATED_VALUE + 1, CHECKMATED_VALUE - 2)]
    fn previous_turn(#[case] value: Centipawns, #[case] expected_value_previous_turn: Centipawns) {
        let evaluation = Evaluation(value);

        let previous_turn = evaluation.in_previous_turn();

        assert_that!(previous_turn.0).is_equal_to(expected_value_previous_turn);
    }

    #[rstest]
    #[case::zero(0, false, false)]
    #[case::positive_centipawns(25, false, false)]
    #[case::max_centipawns(MAX_CENTIPAWNS, false, false)]
    #[case::negative_centipawns(-42, false, false)]
    #[case::min_centipawns(MIN_CENTIPAWNS, false, false)]
    #[case::checkmated_opponent(CHECKMATED_VALUE, true, false)]
    #[case::checkmate_in_1_for_turn(CHECKMATED_VALUE - 1, true, false)]
    #[case::longer_checkmate_for_turn(CHECKMATED_VALUE - 5, true, false)]
    #[case::maximally_long_checkmate_for_turn(MAX_CENTIPAWNS + 1, true, false)]
    #[case::checkmated_turn(-CHECKMATED_VALUE, false, true)]
    #[case::checkmate_in_1_for_opponent(-CHECKMATED_VALUE + 1, false, true)]
    #[case::longer_checkmate_for_opponent(-CHECKMATED_VALUE + 5, false, true)]
    #[case::maximally_long_checkmate_for_opponent(MIN_CENTIPAWNS - 1, false, true)]
    fn forced_checkmate(#[case] value: Centipawns,
            #[case] expected_forced_checkmate_for_turn: bool,
            #[case] expected_forced_checkmate_for_opponent: bool) {
        let evaluation = Evaluation(value);

        let expected_forced_checkmate =
            expected_forced_checkmate_for_turn || expected_forced_checkmate_for_opponent;

        assert_that!(evaluation.is_forced_checkmate()).is_equal_to(expected_forced_checkmate);
        assert_that!(evaluation.is_forced_checkmate_for_turn())
            .is_equal_to(expected_forced_checkmate_for_turn);
        assert_that!(evaluation.is_forced_checkmate_for_opponent())
            .is_equal_to(expected_forced_checkmate_for_opponent);
    }

    #[rstest]
    #[case::zero(0, "0.00")]
    #[case::single_digit(3, "0.03")]
    #[case::two_digits(42, "0.42")]
    #[case::three_digits(320, "3.20")]
    #[case::four_digits(1234, "12.34")]
    #[case::max(MAX_CENTIPAWNS, "300.00")]
    #[case::negative_single_digit(-3, "-0.03")]
    #[case::negative_two_digits(-42, "-0.42")]
    #[case::negative_three_digits(-320, "-3.20")]
    #[case::negative_four_digits(-1234, "-12.34")]
    #[case::min(MIN_CENTIPAWNS, "-300.00")]
    #[case::checkmate_in_1_for_turn(CHECKMATED_VALUE - 1, "#1")]
    #[case::longer_checkmate_for_turn(CHECKMATED_VALUE - 5, "#5")]
    #[case::checkmate_in_1_for_opponent(-CHECKMATED_VALUE + 1, "#-1")]
    #[case::longer_checkmate_for_opponent(-CHECKMATED_VALUE + 5, "#-5")]
    fn formatting(#[case] value: Centipawns, #[case] expected_formatted: &str) {
        let evaluation = Evaluation(value);

        let formatted = format!("{evaluation}");

        assert_that!(formatted.as_str()).is_equal_to(expected_formatted);
    }
}
