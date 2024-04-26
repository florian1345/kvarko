use std::fmt::{self, Display, Formatter};
use std::ops::Neg;

use serde::{Deserialize, Serialize};

pub type Centipawns = i16;

/// The maximum centipawn evaluation representable by [Evaluation].
pub const MAX_CENTIPAWNS: Centipawns = 30_000;

/// The minimum centipawn evaluation representable by [Evaluation].
pub const MIN_CENTIPAWNS: Centipawns = -MAX_CENTIPAWNS;

const CHECKMATED_VALUE: Centipawns = Centipawns::MAX - 1;

/// The evaluation of a position, indicating how good it is for the active player. This comes in two
/// different flavors.
///
/// * **Centipawn-evaluations** represent situations in which no forced-checkmate-sequence could be
/// found and contain an evaluation measured in centipawns (1/100 of a pawn's material value). They
/// are compared by their centipawn value.
/// * **Forced-checkmate-evaluations** represent situations in which a forced-checkmate-sequence was
/// found. They are distinguished by the length of the sequence, with a shorter sequence being
/// considered superior for the player who is winning.
#[derive(Clone, Copy, Debug, Deserialize, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
pub struct Evaluation(Centipawns);

impl Evaluation {

    /// A theoretical evaluation worse than checkmate in 1 for the opponent.
    pub const NEG_INFINITY: Evaluation = Evaluation(-Centipawns::MAX);

    /// A theoretical evaluation better than checkmate in 1 for the active player.
    pub const INFINITY: Evaluation = Evaluation(Centipawns::MAX);

    /// An evaluation of zero, indicating that neither player has an advantage. This is also the
    /// evaluation of a draw.
    pub const ZERO: Evaluation = Evaluation(0);
    
    /// An evaluation from the perspective of the player who has been checkmated, i.e. the worst
    /// possible achievable evaluation.
    pub const CHECKMATED: Evaluation = Evaluation(-CHECKMATED_VALUE);

    /// Constructs a centipawn-evaluation (i.e. no forced checkmate) from the centipawn value,
    /// _without_ checking whether the value is in the legal range for centipawn evaluation. This
    /// condition is violated for too high or too low centipawn evaluations, which reach the range
    /// used by the [Evaluation] type internally to represent forced-checkmate-evaluations. In this
    /// case, the resulting evaluation will be an undefined forced-checkmate-evaluation. If you
    /// are not sufficiently sure that the given centipawns are in the legal range, use
    /// [Evaluation::from_centipawns] instead.
    ///
    /// # Arguments
    ///
    /// * `centipawns`: The centipawn value of the evaluation to construct. Must be in the range
    /// [MIN_CENTIPAWNS] to [MAX_CENTIPAWNS], otherwise the result is not well-defined.
    ///
    /// # Returns
    ///
    /// An evaluation representing the given amount of centipawns.
    #[inline]
    pub fn from_centipawns_unchecked(centipawns: Centipawns) -> Evaluation {
        Evaluation(centipawns)
    }

    /// Constructs a centipawn-evaluation (i.e. no forced checkmate) from the centipawn value.
    ///
    /// # Arguments
    ///
    /// * `centipawns`: The centipawn value of the evaluation to construct. Must be in the range
    /// [MIN_CENTIPAWNS] to [MAX_CENTIPAWNS].
    ///
    /// # Returns
    ///
    /// An evaluation representing the given amount of centipawns or `None`, if `centipawns` is
    /// outside the legal range.
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

    /// Computes the evaluation viewed from the opponent's perspective one ply before the state
    /// evaluated by this evaluation. This is the inverse of the current evaluation, with
    /// potentially a one ply longer forced checkmate sequence in case of a
    /// forced-checkmate-evaluation.
    ///
    /// # Returns
    ///
    /// The evaluation viewed from the opponent's perspective one ply earlier.
    #[inline]
    pub fn in_previous_turn(self) -> Evaluation {
        let mut evaluation = Evaluation(-self.0);

        if evaluation.is_forced_checkmate_for_turn() {
            evaluation.0 -= 1;
        }

        evaluation
    }

    /// Indicates whether this evaluation represents a forced-checkmate-evaluation for either the
    /// active player or their opponent.
    ///
    /// # Returns
    ///
    /// `true` if this evaluation is a forced-checkmate-evaluation and `false` if it is a
    /// centipawn-evaluation.
    #[inline]
    pub fn is_forced_checkmate(self) -> bool {
        self.is_forced_checkmate_for_turn() || self.is_forced_checkmate_for_opponent()
    }

    /// Indicates whether this evaluation represents a forced-checkmate-evaluation for the active
    /// player.
    ///
    /// # Returns
    ///
    /// `true` if this evaluation is a forced-checkmate-evaluation for the active player and `false`
    /// if it is a centipawn-evaluation or a forced-checkmate-evaluation for the opponent.
    #[inline]
    pub fn is_forced_checkmate_for_turn(self) -> bool {
        self.0 > MAX_CENTIPAWNS
    }

    /// Indicates whether this evaluation represents a forced-checkmate-evaluation for the opponent
    /// of the active player.
    ///
    /// # Returns
    ///
    /// `true` if this evaluation is a forced-checkmate-evaluation for the opponent of the active
    /// player and `false` if it is a centipawn-evaluation or a forced-checkmate-evaluation for the
    /// active player.
    #[inline]
    pub fn is_forced_checkmate_for_opponent(self) -> bool {
        self.0 < MIN_CENTIPAWNS
    }

    /// Gets the centipawn-value of this evaluation.
    ///
    /// # Returns
    ///
    /// The centipawn-value of this evaluation or `None`, if it is a forced-checkmate-evaluation.
    pub fn as_centipawns(self) -> Option<Centipawns> {
        if self.is_forced_checkmate() {
            None
        }
        else {
            Some(self.0)
        }
    }

    /// Gets the length of the forced-checkmate-sequence represented by a
    /// forced-checkmate-evaluation. A positive number represents a forced-checkmate-sequence for
    /// the active player, a negative number one for the opponent. The magnitude represents the
    /// number of moves.
    ///
    /// # Returns
    ///
    /// The length of the forced-checkmate-sequence or `None`, if this evaluation is a
    /// centipawn-evaluation.
    pub fn as_checkmate_in(self) -> Option<Centipawns> {
        if self.is_forced_checkmate() {
            Some((CHECKMATED_VALUE - self.0.abs()) * self.0.signum())
        }
        else {
            None
        }
    }

    /// Returns the smaller (i.e. worse for the active player) evaluation of two.
    ///
    /// # Arguments
    ///
    /// `other`: The other evaluation to compare to this one.
    ///
    /// # Return
    ///
    /// The smaller evaluation between this one and the given `other`.
    #[inline]
    pub fn min(self, other: Evaluation) -> Evaluation {
        Evaluation(self.0.min(other.0))
    }

    /// Returns the larger (i.e. better for the active player) evaluation of two.
    ///
    /// # Arguments
    ///
    /// `other`: The other evaluation to compare to this one.
    ///
    /// # Return
    ///
    /// The larger evaluation between this one and the given `other`.
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
