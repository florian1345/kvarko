//! This module defines all error types that could not be localized to a
//! specific module.

use crate::player::Player;
use crate::rules;

use std::error::Error;
use std::fmt::{self, Display, Formatter};
use std::num::ParseIntError;

/// An enumeration of the different errors that can occur when parsing FEN
/// strings.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum FenError {

    /// Indicates that the board representation contained some character which
    /// does not represent any valid piece. The character in question is
    /// provided.
    InvalidPiece(char),

    /// Indicates that the part of the FEN notation which specifies the player
    /// to move is invalid. That is, it is not `"w"` or `"b"`. The full turn
    /// specifier is provided.
    InvalidTurn(String),

    /// Indicates that the part of the FEN notation which specifies castling
    /// rights is malformed. It is expected to be either `"-"` or a non-empty
    /// string of `'k'`, `'q'`, `'K'`, and `'Q'`. The full castling rights
    /// specifier is provided.
    InvalidCastlingRight(String),

    /// Indicates that the part of the FEN notation which specifies the en
    /// passant target is malformed. It is expected to be either `"-"` or the
    /// name of the target square of an en passant move in algebraic notation.
    /// The full en passant target specifier is provided.
    InvalidEnPassantTarget(String),

    /// Indicates that the part of the FEN notation which specifies the state
    /// of the half move clock (which increments every half-move and is reset
    /// to 0 once a pawn is pushed or a piece is captured) could not be parsed
    /// to a valid integer.
    ParseHalfMoveClockError {

        /// The part of the FEN notation specifying the state of the half move
        /// clock.
        part: String,

        /// The [ParseIntError] that occurred while attempting to parse the
        /// part as a [usize].
        error: ParseIntError
    },

    /// Indicates that the part of the FEN notation which specifies the state
    /// of the full move clock (which starts at 1 and is incremented every full
    /// move after black's turn) could not be parsed to a valid integer.
    ParseFullMoveClockError {

        /// The part of the FEN notation specifying the state of the full move
        /// clock.
        part: String,

        /// The [ParseIntError] that occurred while attempting to parse the
        /// part as a [usize].
        error: ParseIntError
    },

    /// Indicates that the value of the half move clock (which increments every
    /// half-move and is reset to 0 once a pawn is pushed or a piece is
    /// captured) is overflowing its ordinary bounds, i.e. 100 or greater.
    HalfMoveClockOverflow(usize),

    /// Indicates that the value of the full move clock (which starts at 1 and
    /// is incremented every full move after black's turn) is 0.
    FullMoveClockZero,

    /// Indicates that the value of the full move clock is too small to
    /// accomodate the value of the half move clock, considering the current
    /// turn. Both clock states and the turn are provided.
    HistoryTooShort {

        /// The value of the half move clock, which is incremented every
        /// half move and is reset to 0 once a pawn is pushed or a piece is
        /// captured. It must be less than twice the value of the full move
        /// clock to be valid if it is [Player::Black]'s turn, and one lower
        /// than that if it is [Player::White]'s turn.
        half_move_clock: usize,

        /// The value of the full move clock, which starts at 1 and is
        /// incremented every full move after black's turn. It must be greater
        /// than half the half move clock if it is [Player::Black]'s turn, and
        /// greater than half of one more than the fifty move clock if it is
        /// [Player::White]'s turn.
        full_move_clock: usize,

        /// The [Player] whose turn it is.
        turn: Player
    },

    /// Indicates that one rank in the board representation had an incorrect
    /// size, i.e. too many or too few fields. The string representing that
    /// rank is provided.
    WrongRankSize(String),

    /// Indicates that the board representation had an incorrect number of
    /// ranks. The string representing the board is provided.
    WrongRankCount(String),

    /// Indicates that the FEN had an incorrect number of parts. While
    /// ordinarily this means it has any other number than 6 parts, when
    /// parsing a [Position](crate::state::Position) and not a full
    /// [State](crate::state::State), only the first 4 parts are expected.
    WrongPartCount {

        /// The FEN string that was provided.
        fen: String,

        /// A description of the parts that were expected. The number of parts
        /// in `fen` was different to the length of this list.
        expected: Vec<String>
    }
}

fn fmt_list<D, I>(mut iter: I, f: &mut Formatter<'_>) -> fmt::Result
where
    D: Display,
    I: ExactSizeIterator + Iterator<Item = D>
{
    match iter.len() {
        0 => Ok(()),
        1 => write!(f, "{}", iter.next().unwrap()),
        2 => write!(f, "{} and {}", iter.next().unwrap(),
            iter.next().unwrap()),
        _ => {
            write!(f, "{}", iter.next().unwrap())?;
    
            while let Some(d) = iter.next() {
                write!(f, ", {}", d)?;
    
                if iter.len() == 1 {
                    break;
                }
            }
    
            write!(f, ", and {}", iter.next().unwrap())
        }
    }
}

impl Display for FenError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            FenError::InvalidPiece(c) =>
                write!(f, "invalid piece char: \'{}\'", c),
            FenError::InvalidTurn(fen) =>
                write!(f, "invalid turn specifier: \"{}\"", fen),
            FenError::InvalidCastlingRight(fen) =>
                write!(f, "invalid castling rights specifier: \"{}\"", fen),
            FenError::InvalidEnPassantTarget(fen) =>
                write!(f, "invalid en passant target square: \"{}\"", fen),
            FenError::ParseHalfMoveClockError { part, error } =>
                write!(f, "error parsing \"{}\" as half move clock: {}", part,
                    error),
            FenError::ParseFullMoveClockError { part, error } =>
                write!(f, "error parsing \"{}\" as full move clock: {}", part,
                    error),
            FenError::HalfMoveClockOverflow(clock) =>
                write!(f, "half move clock may be at most {}, but was {}",
                    rules::DRAW_NO_PROGRESS_COUNT, clock),
            FenError::FullMoveClockZero =>
                write!(f, "full move clock was zero"),
            &FenError::HistoryTooShort {
                half_move_clock,
                full_move_clock,
                turn
            } => {
                let max_half_move_clock =
                    full_move_clock * 2 + turn as usize - 2;
                let turn_s = if turn == Player::White {
                    "white"
                }
                else {
                    "black"
                };

                write!(f, "with move clock of {} and {} to move, the half \
                    move clock may be at most {}, but was {}",
                    full_move_clock, turn_s, max_half_move_clock,
                    half_move_clock)
            },
            FenError::WrongRankSize(rank) =>
                write!(f, "wrong rank size: \"{}\"", rank),
            FenError::WrongRankCount(board) =>
                write!(f, "wrong rank count: \"{}\"", board),
            FenError::WrongPartCount { fen, expected } => {
                write!(f, "wrong part count: \"{}\", expected ", fen)?;
                fmt_list(expected.iter(), f)
            }
        }
    }
}

impl Error for FenError { }

/// Syntactic sugar for `Result<T, FenError>`.
pub type FenResult<T = ()> = Result<T, FenError>;