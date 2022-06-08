//! This module defines the [Player] enumeration and any associated
//! functionality.

use crate::error::{FenResult, FenError};

use std::mem;

/// An enumeration of the two different players. This can be converted to a
/// [usize] to obtain the player index.
#[repr(usize)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Player {

    /// The white player who initially occupies the lower ranks and starts the
    /// game.
    White = 0,

    /// The black player who initially occupies the upper ranks and plays
    /// second every round.
    Black = 1
}

impl Player {

    /// Reads the player whose turn it is from the part specifying that
    /// information in the FEN notation of a position. For example, in the FEN
    /// of the starting position
    /// (`rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1`), this
    /// would be `"w"` for [Player::White] (after the first space).
    ///
    /// # Arguments
    ///
    /// * `fen`: The FEN part representing the turn. Must be `"w"` or `"b"`.
    ///
    /// # Returns
    ///
    /// [Player::White] if `fen` is `"w"` and [Player::Black] if `fen` is
    /// `"b"`.
    ///
    /// # Errors
    ///
    /// [FenError::InvalidTurnSpecifier] if `c` is neither `"w"` nor `"b"`.
    pub fn from_fen_turn_specifier(fen: &str) -> FenResult<Player> {
        match fen {
            "w" => Ok(Player::White),
            "b" => Ok(Player::Black),
            _ => Err(FenError::InvalidTurn(fen.to_owned()))
        }
    }

    /// Reads the player who a piece belongs to from the char representing that
    /// piece in the FEN notation of a position. In FEN, this is encoded by
    /// case sensitivity. Upper case characters represent [Player::White]'s
    /// pieces, lower case characters belong to [Player::Black]. For example,
    /// in the FEN of the starting position
    /// (`rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1`), this may
    /// be `'r'` for the first rook, in which this function would return
    /// [Player::Black]'s, or `'P'` for white's first pawn, in which case this
    /// function would return [Player::White].
    ///
    /// # Arguments
    ///
    /// * `c`: The FEN char representing the piece.
    ///
    /// # Returns
    ///
    /// [Player::White] if `c` is upper case, and [Player::Black] otherwise.
    pub fn from_fen_piece_char(c: char) -> Player {
        if c.is_uppercase() {
            Player::White
        }
        else {
            Player::Black
        }
    }

    /// Gets the opponent who plays against this player, i.e. the other player.
    ///
    /// # Returns
    ///
    /// [Player::White] if this player is black, and [Player::Black] otherwise.
    pub fn opponent(self) -> Player {
        unsafe {
            mem::transmute(1 - self as usize)
        }
    }

    /// Gets the FEN character encoding that it is this player's turn. For
    /// example, in the FEN of the starting position
    /// (`rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1`), this
    /// would be `'w'` for [Player::White] (after the first space).
    ///
    /// # Returns
    ///
    /// `'w'` if this player is white, and `'b'` otherwise.
    pub fn to_fen_turn_char(self) -> char {
        match self {
            Player::White => 'w',
            Player::Black => 'b'
        }
    }

    /// Converts a FEN piece char to one representing a piece owned by this
    /// player. That is, encodes this player on the given character's casing.
    ///
    /// # Arguments
    ///
    /// * `c`: The character representing the piece in any casing. Note this
    /// method assumes this to be a valid piece char.
    ///
    /// # Returns
    ///
    /// Uppercase version of `c` if this player is [Player::White] and its
    /// lowercase form for [Player::Black].
    pub fn convert_fen_piece_char(self, c: char) -> char {
        match self {
            Player::White => c.to_ascii_uppercase(),
            Player::Black => c.to_ascii_lowercase()
        }
    }
}

/// The number of different players participating in a Chess game. Since there
/// are only white and black, this is two. This is the length of [PLAYERS].
pub const PLAYER_COUNT: usize = 2;

/// A list of all [Player]s, i.e. [Player::White] and [Player::Black].
pub const PLAYERS: [Player; 2] = [
    Player::White,
    Player::Black
];
