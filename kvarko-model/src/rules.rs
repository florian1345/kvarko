//! This module defines some constants which specify some of the rules of the
//! game.

use crate::piece::Piece;

/// The number of times a certain position must occur in order to declare a
/// draw by repetition.
pub const DRAW_REPETITION_COUNT: usize = 3;

/// The number of half-moves without progress that must happen in order to
/// declare a draw by the "fifty move rule".
pub const DRAW_NO_PROGRESS_COUNT: usize = 100;

/// An array of all [Piece]s to which a pawn that has progressed to the end of
/// the board may be promoted.
pub const PROMOTABLE: [Piece; 4] = [
    Piece::Knight,
    Piece::Bishop,
    Piece::Rook,
    Piece::Queen
];
