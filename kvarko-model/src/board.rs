//! This module defines the [Board] data structure, which stores the state of a
//! Chess board, i.e. the pieces on the squares.

use crate::error::{FenResult, FenError};
use crate::piece::{PIECE_COUNT, Piece, PIECES};
use crate::player::{PLAYER_COUNT, Player};

use std::cmp::Ordering;
use std::ops::{
    BitAnd,
    BitAndAssign,
    BitOr,
    BitOrAssign,
    BitXor,
    BitXorAssign,
    Not,
    Shl,
    ShlAssign,
    Shr,
    ShrAssign,
    Sub,
    SubAssign
};

/// A bitboard is a 64-bit data type that has one bit associated with each
/// square of a board. It can be viewed as a subset of squares, or a predicate
/// on the squares.
///
/// Various set operations are offered through operators.
///
/// * Union through the bitwise or operator (`|`, [BitOr]).
/// * Intersection through the bitwise and operator (`&`, [BitAnd]).
/// * Difference through the subtraction operator (`-`, [Sub]).
/// * Symmetric difference through the bitwise exclusive or operator (`^`,
/// [BitXor]).
/// * Complement through the not operator (`!`, [Not]).
///
/// Assignment operators associated with the above binary operators are also
/// implemented. [PartialOrd] is implemented in a manner consistent with the
/// subset operation, i.e. `a <= b` if `a` is a subset of `b` or `a > b` if `a`
/// is a proper superset of `b`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Bitboard(pub(crate) u64);

impl Bitboard {

    /// The bitboard which contains no field.
    pub const EMPTY: Bitboard = Bitboard(0);

    /// Creates a new bitboard which contains exactly one field.
    ///
    /// # Arguments
    ///
    /// * `location`: The location of the field which shall be contained in the
    /// resulting bitboard.
    ///
    /// # Returns
    ///
    /// A new bitboard which contains `location` and nothing else.
    pub fn singleton(location: usize) -> Bitboard {
        Bitboard(1 << location)
    }

    /// Gets the number of fields contained in this bitboard.
    pub fn len(self) -> u32 {
        self.0.count_ones()
    }

    /// Indicates whether this bitboard is empty, i.e. it contains no fields.
    ///
    /// # Returns
    ///
    /// True, if and only if this bitboard is empty.
    pub fn is_empty(self) -> bool {
        self.0 == 0
    }
}

impl BitOr for Bitboard {
    type Output = Bitboard;

    fn bitor(self, rhs: Bitboard) -> Bitboard {
        Bitboard(self.0 | rhs.0)
    }
}

impl BitOrAssign for Bitboard {
    fn bitor_assign(&mut self, rhs: Bitboard) {
        *self = *self | rhs;
    }
}

impl BitAnd for Bitboard {
    type Output = Bitboard;

    fn bitand(self, rhs: Bitboard) -> Bitboard {
        Bitboard(self.0 & rhs.0)
    }
}

impl BitAndAssign for Bitboard {
    fn bitand_assign(&mut self, rhs: Bitboard) {
        *self = *self & rhs;
    }
}

impl BitXor for Bitboard {
    type Output = Bitboard;

    fn bitxor(self, rhs: Bitboard) -> Bitboard {
        Bitboard(self.0 ^ rhs.0)
    }
}

impl BitXorAssign for Bitboard {
    fn bitxor_assign(&mut self, rhs: Bitboard) {
        *self = *self ^ rhs;
    }
}

impl Sub for Bitboard {
    type Output = Bitboard;

    fn sub(self, rhs: Bitboard) -> Bitboard {
        Bitboard(self.0 & !rhs.0)
    }
}

impl SubAssign for Bitboard {
    fn sub_assign(&mut self, rhs: Bitboard) {
        *self = *self - rhs;
    }
}

impl Not for Bitboard {
    type Output = Bitboard;

    fn not(self) -> Bitboard {
        Bitboard(!self.0)
    }
}

impl<T> Shl<T> for Bitboard
where
    u64: Shl<T, Output = u64>
{
    type Output = Bitboard;

    fn shl(self, rhs: T) -> Bitboard {
        Bitboard(self.0 << rhs)
    }
}

impl<T> ShlAssign<T> for Bitboard
where
    u64: ShlAssign<T>
{
    fn shl_assign(&mut self, rhs: T) {
        self.0 <<= rhs;
    }
}

impl<T> Shr<T> for Bitboard
where
    u64: Shr<T, Output = u64>
{
    type Output = Bitboard;

    fn shr(self, rhs: T) -> Bitboard {
        Bitboard(self.0 >> rhs)
    }
}

impl<T> ShrAssign<T> for Bitboard
where
    u64: ShrAssign<T>
{
    fn shr_assign(&mut self, rhs: T) {
        self.0 >>= rhs;
    }
}

impl PartialOrd for Bitboard {
    fn partial_cmp(&self, other: &Bitboard) -> Option<Ordering> {
        if self == other {
            Some(Ordering::Equal)
        }
        else if self <= other {
            Some(Ordering::Less)
        }
        else if self >= other {
            Some(Ordering::Greater)
        }
        else {
            None
        }
    }

    fn le(&self, other: &Bitboard) -> bool {
        *self & *other == *self
    }

    fn lt(&self, other: &Bitboard) -> bool {
        self <= other && self != other
    }

    fn ge(&self, other: &Bitboard) -> bool {
        *self & *other == *other
    }

    fn gt(&self, other: &Bitboard) -> bool {
        self >= other && self != other
    }
}

/// The width of a Chess board, i.e. the number of files.
pub const BOARD_WIDTH: usize = 8;

/// The height of a Chess board, i.e. the number of ranks.
pub const BOARD_HEIGHT: usize = 8;

const INITIAL_WHITE: Bitboard = Bitboard(0xffff000000000000);
const INITIAL_BLACK: Bitboard = Bitboard(0x000000000000ffff);

const INITIAL_PAWN: Bitboard = Bitboard(0x00ff00000000ff00);
const INITIAL_KNIGHT: Bitboard = Bitboard(0x4200000000000042);
const INITIAL_BISHOP: Bitboard = Bitboard(0x2400000000000024);
const INITIAL_ROOK: Bitboard = Bitboard(0x8100000000000081);
const INITIAL_QUEEN: Bitboard = Bitboard(0x1000000000000010);
const INITIAL_KING: Bitboard = Bitboard(0x0800000000000008);

fn write_fen_gap(fen: &mut String, gap_counter: &mut usize) {
    if *gap_counter != 0 {
        fen.push((b'0' + *gap_counter as u8) as char);
        *gap_counter = 0;
    }
}

/// Represents the arrangement of pieces on a Chess board. This does not
/// contain any other state information, such as whose turn it is or whether
/// players may still castle.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Board {
    players: [Bitboard; PLAYER_COUNT],
    pieces: [Bitboard; PIECE_COUNT]
}

impl Board {

    /// Creates a new Chess board without any pieces on it.
    ///
    /// # Returns
    ///
    /// A new empty board.
    pub fn empty() -> Board {
        Board {
            players: [Bitboard::EMPTY; PLAYER_COUNT],
            pieces: [Bitboard::EMPTY; PIECE_COUNT]
        }
    }

    /// Creates a new Chess board in the initial configuration as defined by
    /// the Chess rules, i.e. each player has eight pawns in front, and rook,
    /// knight, bishop, queen, king, bishop, knight, and rook behind, in that
    /// order from left to right. White is generated at the bottom of the board
    /// and black at the top.
    ///
    /// # Returns
    ///
    /// A new board in the initial position.
    pub fn initial() -> Board {
        Board {
            players: [
                INITIAL_WHITE,
                INITIAL_BLACK
            ],
            pieces: [
                INITIAL_PAWN,
                INITIAL_KNIGHT,
                INITIAL_BISHOP,
                INITIAL_ROOK,
                INITIAL_QUEEN,
                INITIAL_KING
            ]
        }
    }

    fn players(&self, player: Player) -> Bitboard {
        self.players[player as usize]
    }

    fn pieces(&self, piece: Piece) -> Bitboard {
        self.pieces[piece as usize]
    }

    fn players_mut(&mut self, player: Player) -> &mut Bitboard {
        &mut self.players[player as usize]
    }

    fn pieces_mut(&mut self, piece: Piece) -> &mut Bitboard {
        &mut self.pieces[piece as usize]
    }

    fn set(&mut self, location: usize, piece: Piece, player: Player) {
        let mask = Bitboard::singleton(location);

        *self.players_mut(player) |= mask;
        *self.players_mut(player.opponent()) -= mask;

        for piece_i in PIECES {
            if piece_i == piece {
                *self.pieces_mut(piece_i) |= mask;
            }
            else {
                *self.pieces_mut(piece_i) -= mask;
            }
        }
    }

    fn get(&self, location: usize) -> Option<(Piece, Player)> {
        let mask = Bitboard::singleton(location);
        let player = if !(self.players(Player::White) & mask).is_empty() {
            Player::White
        }
        else if !(self.players(Player::Black) & mask).is_empty() {
            Player::Black
        }
        else {
            return None;
        };
        let piece = *PIECES.iter()
            .filter(|&&p| !(self.pieces(p) & mask).is_empty())
            .next()
            .expect("no piece in occupied field");

        Some((piece, player))
    }

    /// Parses the part representing the board of a FEN string.
    ///
    /// # Arguments
    ///
    /// * `fen`: A FEN board representation. Note this does not include
    /// castling, en passant, turn, 50-move-rule, and game length information.
    ///
    /// # Returns
    ///
    /// A new board in the configuration specified by the given FEN string.
    ///
    /// # Errors
    ///
    /// * [FenError::WrongRankCount] if the number of ranks (parts separated by
    /// `'/'`) is not equal to [BOARD_HEIGHT].
    /// * [FenError::WrongRankSize] if any rank represents a list of fields
    /// which is not equal to [BOARD_WIDTH] in length.
    /// * [FenError::InvalidPieceChar] if any character that appears in a rank
    /// does not represent a piece or a gap of valid size (i.e. greater than 0
    /// and less than [BOARD_WIDTH]).
    pub fn from_fen(fen: &str) -> FenResult<Board> {
        let mut board = Board::empty();
        let ranks = fen.split('/').rev();
        let mut location = 0;
        let mut rank_count = 0;

        for (rank_idx, rank) in ranks.enumerate() {
            if rank_count >= BOARD_HEIGHT {
                return Err(FenError::WrongRankCount(fen.to_owned()));
            }

            for piece_char in rank.chars() {
                if piece_char.is_numeric() {
                    let diff = piece_char as usize - '0' as usize;

                    if diff == 0 || diff > BOARD_WIDTH {
                        return Err(FenError::InvalidPiece(piece_char));
                    }

                    location += diff;
                }
                else {
                    let piece = Piece::from_fen_char(piece_char)?;
                    let player = Player::from_fen_piece_char(piece_char);
                    board.set(location, piece, player);
                    location += 1;
                }
            }

            if location != (rank_idx + 1) * BOARD_WIDTH {
                return Err(FenError::WrongRankSize(rank.to_owned()));
            }

            rank_count += 1;
        }

        if rank_count < BOARD_HEIGHT {
            return Err(FenError::WrongRankCount(fen.to_owned()));
        }

        Ok(board)
    }

    /// Converts this board to a FEN board representation. Note this does not
    /// include castling, en passant, turn, 50-move-rule, and game length
    /// information.
    ///
    /// # Returns
    ///
    /// A new [String] containing the FEN board representation for this board.
    pub fn to_fen(&self) -> String {
        let mut fen = String::new();
        let mut gap_counter = 0;

        for rank in (0..BOARD_HEIGHT).rev() {
            if rank < BOARD_HEIGHT - 1 {
                fen.push('/');
            }

            for file in 0..BOARD_WIDTH {
                let location = rank * BOARD_WIDTH + file;

                if let Some((piece, player)) = self.get(location) {
                    write_fen_gap(&mut fen, &mut gap_counter);
                    fen.push(player.convert_fen_piece_char(piece.to_fen_char()));
                }
                else {
                    gap_counter += 1;
                }
            }

            write_fen_gap(&mut fen, &mut gap_counter);
        }

        fen
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    fn assert_board_fen_reproducible(fen: &str) {
        let board = Board::from_fen(fen).expect("test board FEN not accepted");
        let new_fen = board.to_fen();

        assert_eq!(fen, &new_fen);
    }

    #[test]
    fn empty_board_fen_reproducible() {
        assert_board_fen_reproducible("8/8/8/8/8/8/8/8");
    }

    #[test]
    fn initial_board_fen_reproducible() {
        assert_board_fen_reproducible(
            "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR");
    }

    #[test]
    fn arbitrary_board_fen_reproducible() {
        assert_board_fen_reproducible(
            "r2q1rk1/p2n1pp1/2pb1np1/1p6/2BP1P2/6N1/PPP3PP/R1BQR1K1");
    }
}
