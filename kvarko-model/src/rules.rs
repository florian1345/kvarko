//! This module defines some constants which specify some of the rules of the
//! game.

/// The number of times a certain position must occur in order to declare a
/// draw by repetition.
pub const DRAW_REPETITION_COUNT: usize = 3;

/// The number of half-moves without progress that must happen in order to
/// declare a draw by the "fifty move rule".
pub const DRAW_NO_PROGRESS_COUNT: usize = 100;
