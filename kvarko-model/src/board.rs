//! This module defines the [Board] data structure, which stores the state of a
//! Chess board, i.e. the pieces on the squares.

use crate::error::{FenError, FenResult, LocationError, LocationResult};
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

/// Represents the location of a single square on the board as an index.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Location(pub(crate) usize);

impl Location {

    /// Creates a new location that represents the square in the given file and
    /// rank.
    ///
    /// # Arguments
    ///
    /// * `file`: The 0-based index of the file (starting with the A-file) of
    /// the square for which to construct a location. Must be less than
    /// [BOARD_WIDTH].
    /// * `rank`: The 0-based index of the rank (starting with rank 1) of the
    /// square for which to construct a location. Must be less than
    /// [BOARD_HEIGHT].
    ///
    /// # Returns
    ///
    /// A new location representing the square at the given file and rank.
    ///
    /// # Errors
    ///
    /// * [LocationError::FileOutOfBounds] if `file` is too large, i.e. greater
    /// than or equal to [BOARD_WIDTH].
    /// * [LocationError::RankOutOfBounds] if `rank` is too large, i.e. greater
    /// than or equal to [BOARD_HEIGHT].
    pub fn from_file_and_rank<F, R>(file: F, rank: R)
        -> LocationResult<Location>
    where
        F: Into<usize>,
        R: Into<usize>
    {
        let file = file.into();
        let rank = rank.into();

        if file >= BOARD_WIDTH {
            Err(LocationError::FileOutOfBounds)
        }
        else if rank >= BOARD_HEIGHT {
            Err(LocationError::RankOutOfBounds)
        }
        else {
            Ok(Location(rank * BOARD_WIDTH + file))
        }
    }
}

/// An [Iterator] over [Location]s of the squares contained in a [Bitboard].
pub struct BitboardLocationIter {
    bitboard: Bitboard
}

impl Iterator for BitboardLocationIter {
    type Item = Location;

    fn next(&mut self) -> Option<Location> {
        if self.bitboard.is_empty() {
            None
        }
        else {
            let trailing_zeros = self.bitboard.0.trailing_zeros();
            self.bitboard -= Bitboard(1) << trailing_zeros;
            Some(Location(trailing_zeros as usize))
        }
    }
}

/// An [Iterator] over singletons of the squares contained in a [Bitboard].
/// That is, this iterator yields for each square in the bitboard over which is
/// iterated another bitboard containing only that square.
pub struct BitboardSingletonIter {
    bitboard: Bitboard
}

impl Iterator for BitboardSingletonIter {
    type Item = Bitboard;

    fn next(&mut self) -> Option<Bitboard> {
        if self.bitboard.is_empty() {
            None
        }
        else {
            let trailing_zeros = self.bitboard.0.trailing_zeros();
            let result = Bitboard(1) << trailing_zeros;
            self.bitboard -= result;
            Some(result)
        }
    }
}

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

    /// The bitboard which contains every field.
    pub const FULL: Bitboard = Bitboard(0xffffffffffffffff);

    /// Creates a new bitboard which contains exactly one field.
    ///
    /// # Arguments
    ///
    /// * `location`: The [Location] of the field which shall be contained in
    /// the resulting bitboard.
    ///
    /// # Returns
    ///
    /// A new bitboard which contains `location` and nothing else.
    pub fn singleton(location: Location) -> Bitboard {
        Bitboard(1 << location.0)
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

    /// Gets the location of the square with minimum index contained in this
    /// bitboard. The main purpose for this is efficiently extracting the
    /// location of the square contained in a singleton bitboard.
    ///
    /// This method does not check that this bitboard is non-empty. If it is
    /// empty, an invalid location is returned, which may cause a hard-to-find
    /// error down the road. If you are unsure whether your bitboard is
    /// non-empty, use [Bitboard::min] instead.
    ///
    /// # Returns
    ///
    /// A new location representing the square with minimum index contained in
    /// this bitboard.
    pub fn min_unchecked(self) -> Location {
        Location(self.0.trailing_zeros() as usize)
    }

    /// Gets the location of the square with minimum index contained in this
    /// bitboard, if one exists. The main purpose for this is efficiently
    /// extracting the location of the square contained in a singleton
    /// bitboard.
    ///
    /// # Returns
    ///
    /// `Some(location)` with the location representingthe square with minimum
    /// index contained in this bitboard, if it is non-empty. `None` if this
    /// bitboard is empty.
    pub fn min(self) -> Option<Location> {
        if self.is_empty() {
            None
        }
        else {
            Some(self.min_unchecked())
        }
    }

    /// Indicates whether the square with the given location is contained in
    /// this bitboard.
    ///
    /// # Arguments
    ///
    /// * `location`: The [Location] for which to check whether it is contained
    /// in this bitboard.
    ///
    /// # Returns
    ///
    /// True if and only if the square with the given location is contained in
    /// this bitboard.
    pub fn contains(self, location: Location) -> bool {
        (self.0 & (1u64 << location.0)) != 0
    }

    /// Creates an iterator over the locations of all squared contained in this
    /// bitboard, in ascending order of index.
    ///
    /// # Returns
    ///
    /// A new [BitboardLocationIter] over this bitboard.
    pub fn locations(self) -> BitboardLocationIter {
        BitboardLocationIter {
            bitboard: self
        }
    }

    /// Creates an iterator over singleton bitboards for all squares contained
    /// in this bitboard, in ascending order of location index. That is, for
    /// every square in this bitboard, the created iterator yields another
    /// bitboard which contains only that square.
    ///
    /// # Returns
    ///
    /// A new [BitboardSingletonIter] over this bitboard.
    pub fn singletons(self) -> BitboardSingletonIter {
        BitboardSingletonIter {
            bitboard: self
        }
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

const INITIAL_WHITE: Bitboard = Bitboard(0x000000000000ffff);
const INITIAL_BLACK: Bitboard = Bitboard(0xffff000000000000);

const INITIAL_PAWN: Bitboard = Bitboard(0x00ff00000000ff00);
const INITIAL_KNIGHT: Bitboard = Bitboard(0x4200000000000042);
const INITIAL_BISHOP: Bitboard = Bitboard(0x2400000000000024);
const INITIAL_ROOK: Bitboard = Bitboard(0x8100000000000081);
const INITIAL_QUEEN: Bitboard = Bitboard(0x0800000000000008);
const INITIAL_KING: Bitboard = Bitboard(0x1000000000000010);

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

    /// Gets a bitboard containing the fields on which a piece of the given
    /// player stands.
    ///
    /// # Arguments
    ///
    /// * `player`: The [Player] for which to get a bitboard of their pieces.
    ///
    /// # Returns
    ///
    /// A [Bitboard] containing the fields with a piece of `player`.
    pub fn of_player(&self, player: Player) -> Bitboard {
        self.players[player as usize]
    }

    /// Gets a bitboard containing the fields on which a piece of the given
    /// kind stands.
    ///
    /// # Arguments
    ///
    /// * `piece`: The [Piece] kind for which to get a bitboard of its pieces.
    ///
    /// # Returns
    ///
    /// A [Bitboard] containing the fields with a piece of the given `piece`
    /// kind.
    pub fn of_kind(&self, piece: Piece) -> Bitboard {
        self.pieces[piece as usize]
    }

    /// Gets a bitboard containing the fields on which a piece of the given
    /// player and kind stands.
    ///
    /// # Arguments
    ///
    /// * `player`: The [Player] for which to get a bitboard of their pieces of
    /// the given kind.
    /// * `piece`: The [Piece] kind for which to get a bitboard of its pieces
    /// of the given player.
    ///
    /// # Returns
    ///
    /// A [Bitboard] containing the fields with a piece of `player` and `piece`
    /// kind.
    pub fn of_player_and_kind(&self, player: Player, piece: Piece)
            -> Bitboard {
        self.of_player(player) & self.of_kind(piece)
    }

    pub fn is_of_kind(&self, piece: Piece, location: Location) -> bool {
        self.of_kind(piece).contains(location)
    }

    pub fn is_of_kind_any(&self, piece: Piece, fields: Bitboard) -> bool {
        !(self.of_kind(piece) & fields).is_empty()
    }

    pub fn is_of_kind_all(&self, piece: Piece, fields: Bitboard) -> bool {
        self.of_kind(piece) & fields == fields
    }

    pub(crate) fn kind_at(&self, singleton: Bitboard) -> Piece {
        for piece in PIECES {
            if !(self.pieces[piece as usize] & singleton).is_empty() {
                return piece;
            }
        }

        panic!("no piece at given singleton, internal error")
    }

    fn players_mut(&mut self, player: Player) -> &mut Bitboard {
        &mut self.players[player as usize]
    }

    fn pieces_mut(&mut self, piece: Piece) -> &mut Bitboard {
        &mut self.pieces[piece as usize]
    }

    fn set(&mut self, location: usize, piece: Piece, player: Player) {
        let mask = Bitboard::singleton(Location(location));

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
        let mask = Bitboard::singleton(Location(location));
        let player = if !(self.of_player(Player::White) & mask).is_empty() {
            Player::White
        }
        else if !(self.of_player(Player::Black) & mask).is_empty() {
            Player::Black
        }
        else {
            return None;
        };
        let piece = *PIECES.iter()
            .filter(|&&p| !(self.of_kind(p) & mask).is_empty())
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

    #[test]
    fn empty_bitboard_location_iterator() {
        assert!(Bitboard::EMPTY.locations().next().is_none());
    }

    #[test]
    fn bitboard_with_min_location_iterator() {
        let bitboard = Bitboard(0x0000000000000131);
        let locations = bitboard.locations().collect::<Vec<_>>();

        assert_eq!(
            vec![Location(0), Location(4), Location(5), Location(8)],
            locations);
    }

    #[test]
    fn bitboard_with_max_location_iterator() {
        let bitboard = Bitboard(0x8000000000000130);
        let locations = bitboard.locations().collect::<Vec<_>>();

        assert_eq!(
            vec![Location(4), Location(5), Location(8), Location(63)],
            locations);
    }

    #[test]
    fn empty_bitboard_singleton_iterator() {
        assert!(Bitboard::EMPTY.singletons().next().is_none());
    }

    #[test]
    fn bitboard_with_min_singleton_iterator() {
        let bitboard = Bitboard(0x0000000000000131);
        let locations = bitboard.singletons().collect::<Vec<_>>();

        assert_eq!(
            vec![
                Bitboard(0x1),
                Bitboard(0x10),
                Bitboard(0x20),
                Bitboard(0x100)],
            locations);
    }

    #[test]
    fn bitboard_with_max_singleton_iterator() {
        let bitboard = Bitboard(0x8000000000000130);
        let locations = bitboard.singletons().collect::<Vec<_>>();

        assert_eq!(
            vec![
                Bitboard(0x10),
                Bitboard(0x20),
                Bitboard(0x100),
                Bitboard(0x8000000000000000)],
            locations);
    }

    const INITIAL_FEN: &str = "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR";

    #[test]
    fn initial_board_equals_initial_fen() {
        let initial = Board::initial();
        let initial_fen = Board::from_fen(INITIAL_FEN).unwrap();

        assert_eq!(initial_fen, initial);
    }

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
        assert_board_fen_reproducible(INITIAL_FEN);
    }

    #[test]
    fn arbitrary_board_fen_reproducible() {
        assert_board_fen_reproducible(
            "r2q1rk1/p2n1pp1/2pb1np1/1p6/2BP1P2/6N1/PPP3PP/R1BQR1K1");
    }
}
