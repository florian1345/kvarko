//! This module defines the [Piece] enumeration and any associated
//! functionality.

use crate::error::{FenResult, FenError};

/// An enumeration of the different kinds of pieces on the board. Does not
/// encode the [Player] who owns the piece. This can be converted to a [usize]
/// to obtain the piece index.
#[repr(usize)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Piece {

    /// A pawn. Can move forwards (towards the enemy's base) by one without
    /// taking, if on the starting rank can move forwards by two without
    /// taking. Can take on squares that are forward and diagonally adjacent.
    /// Can take "en passant", i.e. if on the same rank and adjacent to an
    /// enemy pawn who just moved two squares, can take them by moving
    /// diagonally behind the enemy pawn.
    Pawn = 0,

    // A knight. Can move and take on all squares that have a distance of two
    /// on one axis and a distance of one on the other axis.
    Knight = 1,

    /// A bishop. Can move and take by sliding diagonally, but not through
    /// other pieces.
    Bishop = 2,

    /// A rook. Can move and take by sliding horizontally or vertically, but
    /// not through other pieces.
    Rook = 3,

    /// A queen. Can move and take by sliding horizontally, vertically, or
    /// diagonally, but not through other pieces.
    Queen = 4,

    /// A king. Can move and take on all squares orthogonally or diagonally
    /// adjacent to their location.
    King = 5
}

impl Piece {

    /// Reads the piece kind from a character representing that piece in FEN
    /// notation. For example, in the FEN of the starting position
    /// (`rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1`), this may
    /// be an `'r'` for a [Piece::Rook] or a `'P'` for a [Piece::Pawn].
    ///
    /// # Arguments
    ///
    /// * `c`: The character representing the piece in FEN notation. Must be a
    /// valid piece abbreviation (P, N, B, R, Q, or K) in upper or lower case.
    ///
    /// # Returns
    ///
    /// The piece represented by the given character.
    ///
    /// # Errors
    ///
    /// [FenError::InvalidPieceChar] if the character is not a valid piece
    /// abbreviation.
    pub fn from_fen_char(c: char) -> FenResult<Piece> {
        match c.to_ascii_lowercase() {
            'p' => Ok(Piece::Pawn),
            'n' => Ok(Piece::Knight),
            'b' => Ok(Piece::Bishop),
            'r' => Ok(Piece::Rook),
            'q' => Ok(Piece::Queen),
            'k' => Ok(Piece::King),
            _ => Err(FenError::InvalidPiece(c))
        }
    }

    /// Indicates whether this piece moves in a sliding manner. This is the
    /// case for [Piece::Bishop], [Piece::Rook], and [Piece::Queen].
    ///
    /// # Returns
    ///
    /// `true`, if and only if this piece is a slider.
    pub fn is_slider(self) -> bool {
        const BISHOP_IDX: usize = Piece::Bishop as usize;
        const QUEEN_IDX: usize = Piece::Queen as usize;

        let idx = self as usize;
        idx >= BISHOP_IDX && idx <= QUEEN_IDX
    }

    /// Converts this piece into its lower case FEN representation.
    ///
    /// # Returns
    ///
    /// The piece abbreviation of this piece in lower case.
    pub fn to_fen_char(self) -> char {
        match self {
            Piece::Pawn => 'p',
            Piece::Knight => 'n',
            Piece::Bishop => 'b',
            Piece::Rook => 'r',
            Piece::Queen => 'q',
            Piece::King => 'k'
        }
    }
}

/// The number of different pieces, i.e. the length of [PIECES].
pub const PIECE_COUNT: usize = 6;

/// A list containing all [Piece]s in order of their indices.
pub const PIECES: [Piece; PIECE_COUNT] = [
    Piece::Pawn,
    Piece::Knight,
    Piece::Bishop,
    Piece::Rook,
    Piece::Queen,
    Piece::King
];
