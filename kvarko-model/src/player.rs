//! This module defines the [Player] enumeration and any associated
//! functionality.

use crate::board::{Bitboard, BOARD_WIDTH, Rank};
use crate::error::{FenResult, FenError};

use std::mem;
use crate::board::locations::{A1, A8, B1, B8, C1, C8, D1, D8, E1, E8, F1, F8, G1, G8, H1, H8};

/// An enumeration of the two different players. This can be converted to a
/// [usize] to obtain the player index.
#[repr(u8)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
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
    /// [FenError::InvalidTurn] if `c` is neither `"w"` nor `"b"`.
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
            mem::transmute(1 - self as u8)
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

pub(crate) struct CastleInfo {
    pub(crate) intermediate: Bitboard,
    pub(crate) passed: Bitboard,
    pub(crate) king_delta_mask: Bitboard,
    pub(crate) rook_delta_mask: Bitboard
}

pub(crate) trait StaticPlayer {

    type Opponent: StaticPlayer;

    const SECOND_RANK: Bitboard;
    const FOURTH_RANK: Bitboard;
    const FIFTH_RANK: Bitboard;
    const EIGHTH_RANK: Bitboard;

    const CLOSE_ROOK_SINGLETON: Bitboard;
    const FAR_ROOK_SINGLETON: Bitboard;

    const SHORT_CASTLE_INFO: CastleInfo;
    const LONG_CASTLE_INFO: CastleInfo;

    fn forward(bitboard: Bitboard) -> Bitboard;

    fn back(bitboard: Bitboard) -> Bitboard;
}

pub(crate) struct White;

impl StaticPlayer for White {

    type Opponent = Black;

    const SECOND_RANK: Bitboard = Bitboard::of_rank(Rank::R2);
    const FOURTH_RANK: Bitboard = Bitboard::of_rank(Rank::R4);
    const FIFTH_RANK: Bitboard = Bitboard::of_rank(Rank::R5);
    const EIGHTH_RANK: Bitboard = Bitboard::of_rank(Rank::R8);

    const CLOSE_ROOK_SINGLETON: Bitboard = Bitboard::singleton(H1);
    const FAR_ROOK_SINGLETON: Bitboard = Bitboard::singleton(A1);

    const SHORT_CASTLE_INFO: CastleInfo = CastleInfo {
        intermediate: Bitboard::of([F1, G1]),
        passed: Bitboard::of([F1, G1]),
        king_delta_mask: Bitboard::of([E1, G1]),
        rook_delta_mask: Bitboard::of([H1, F1])
    };

    const LONG_CASTLE_INFO: CastleInfo = CastleInfo {
        intermediate: Bitboard::of([B1, C1, D1]),
        passed: Bitboard::of([C1, D1]),
        king_delta_mask: Bitboard::of([E1, C1]),
        rook_delta_mask: Bitboard::of([A1, D1])
    };

    fn forward(bitboard: Bitboard) -> Bitboard {
        bitboard << BOARD_WIDTH
    }

    fn back(bitboard: Bitboard) -> Bitboard {
        bitboard >> BOARD_WIDTH
    }
}

pub(crate) struct Black;

impl StaticPlayer for Black {

    type Opponent = White;

    const SECOND_RANK: Bitboard = Bitboard::of_rank(Rank::R7);
    const FOURTH_RANK: Bitboard = Bitboard::of_rank(Rank::R5);
    const FIFTH_RANK: Bitboard = Bitboard::of_rank(Rank::R4);
    const EIGHTH_RANK: Bitboard = Bitboard::of_rank(Rank::R1);

    const CLOSE_ROOK_SINGLETON: Bitboard = Bitboard::singleton(H8);
    const FAR_ROOK_SINGLETON: Bitboard = Bitboard::singleton(A8);

    const SHORT_CASTLE_INFO: CastleInfo = CastleInfo {
        intermediate: Bitboard::of([F8, G8]),
        passed: Bitboard::of([F8, G8]),
        king_delta_mask: Bitboard::of([E8, G8]),
        rook_delta_mask: Bitboard::of([H8, F8])
    };

    const LONG_CASTLE_INFO: CastleInfo = CastleInfo {
        intermediate: Bitboard::of([B8, C8, D8]),
        passed: Bitboard::of([C8, D8]),
        king_delta_mask: Bitboard::of([E8, C8]),
        rook_delta_mask: Bitboard::of([A8, D8])
    };

    fn forward(bitboard: Bitboard) -> Bitboard {
        bitboard >> BOARD_WIDTH
    }

    fn back(bitboard: Bitboard) -> Bitboard {
        bitboard << BOARD_WIDTH
    }
}
