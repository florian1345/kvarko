//! This module defines the [Board] data structure, which stores the state of a
//! Chess board, i.e. the pieces on the squares.

pub mod locations;

use crate::error::{FenError, FenResult};
use crate::movement::Move;
use crate::piece::{PIECE_COUNT, Piece, PIECES};
use crate::player::{PLAYER_COUNT, Player, PLAYERS};

use serde::{Deserialize, Serialize};

use std::cmp::Ordering;
use std::fmt;
use std::fmt::{Display, Formatter};
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
use crate::board::locations::{A1, A8, B1, B8, C1, C8, D1, D8, E1, E8, F1, F8, G1, G8, H1, H8};

/// Represents a file (column of fields) on the Chess board. Can be converted to and from 0-based
/// file indices using [File::from_usize] and [File::as_usize].
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct File(usize);

impl File {

    /// The A-file with (index 0, queen-side rook file).
    pub const A: File = File(0);

    /// The B-file with (index 1, queen-side knight file).
    pub const B: File = File(1);

    /// The C-file with (index 2, queen-side bishop file).
    pub const C: File = File(2);

    /// The D-file with (index 3, queen file).
    pub const D: File = File(3);

    /// The E-file with (index 4, king file).
    pub const E: File = File(4);

    /// The F-file with (index 5, king-side bishop file).
    pub const F: File = File(5);

    /// The G-file with (index 6, king-side knight file).
    pub const G: File = File(6);

    /// The H-file with (index 7, king-side rook file).
    pub const H: File = File(7);

    /// An array of all files from A to H (indices 0 to 7, queen-side rook to king-side rook files).
    pub const FILES: [File; BOARD_WIDTH] = [
        File::A,
        File::B,
        File::C,
        File::D,
        File::E,
        File::F,
        File::G,
        File::H
    ];

    /// Converts this file to its 0-based index starting at the A-file (A = 0, B = 1, ...).
    ///
    /// # Returns
    ///
    /// The 0-based index of this file as a [usize].
    pub const fn as_usize(self) -> usize {
        self.0
    }

    /// Constructs a file from its 0-based index starting at the A-file (0 = A, 1 = B, ...).
    ///
    /// # Arguments
    ///
    /// * `file`: The 0-based index of the file to construct. Must be in the range 0 to 7 to yield a
    /// result.
    ///
    /// # Returns
    ///
    /// `Some(...)` with the file with the given index, if it is in the valid range, and `None`
    /// otherwise.
    pub const fn from_usize(file: usize) -> Option<File> {
        if file < BOARD_WIDTH {
            Some(File(file))
        }
        else {
            None
        }
    }

    /// Gets the lowercase letter representing this file.
    ///
    /// # Returns
    ///
    /// A [char] containing the lowercase letter representing this file (`'a'`, `'b'`, ..., `'h'`).
    pub fn as_char(self) -> char {
        char::from_u32('a' as u32 + self.0 as u32).unwrap()
    }

    /// Gets the lowercase letter representing this file as a UTF-8 byte.
    ///
    /// # Returns
    ///
    /// A [u8] that constitutes the UTF-8 representation of the lowercase letter representing this
    /// file (`b'a'`, `b'b'`, ..., `b'h'`).
    pub const fn as_utf8_char(self) -> u8 {
        b'a' + self.0 as u8
    }

    /// Parses a file from its lowercase letter.
    ///
    /// # Arguments
    ///
    /// * `file`: A character containing the lowercase letter representing the file to return
    /// (`'a'`, `'b'`, ..., `'h'`).
    ///
    /// # Returns
    ///
    /// `Some(...)` with the file represented by the given letter, if it is in the valid range, and
    /// `None` otherwise.
    pub const fn from_char(file: char) -> Option<File> {
        if file >= 'a' {
            File::from_usize(file as usize - 'a' as usize)
        }
        else {
            None
        }
    }
}

impl Display for File {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_char())
    }
}

/// Represents a rank (row of fields) on the Chess board. Can be converted to and from 0-based rank
/// indices using [Rank::from_usize] and [Rank::as_usize].
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Rank(usize);

impl Rank {

    /// The first rank (index 0, initially containing White's non-pawn pieces).
    pub const R1: Rank = Rank(0);

    /// The second rank (index 1, initially containing White's pawns).
    pub const R2: Rank = Rank(1);

    /// The third rank (index 2, initially the rank in front of White's pawns).
    pub const R3: Rank = Rank(2);

    /// The fourth rank (index 3, initially the central rank leaning towards White).
    pub const R4: Rank = Rank(3);

    /// The fifth rank (index 4, initially the central rank leaning towards Black).
    pub const R5: Rank = Rank(4);

    /// The sixth rank (index 5, initially the rank in front of Black's pawns).
    pub const R6: Rank = Rank(5);

    /// The seventh rank (index 6, initially containing Black's pawns).
    pub const R7: Rank = Rank(6);

    /// The eighth rank (index 7, initially containing Black's non-pawn pieces).
    pub const R8: Rank = Rank(7);

    /// An array of all ranks from 1st to 8th (indices 0 to 7, White's side to Black's side).
    pub const RANKS: [Rank; BOARD_HEIGHT] = [
        Rank::R1,
        Rank::R2,
        Rank::R3,
        Rank::R4,
        Rank::R5,
        Rank::R6,
        Rank::R7,
        Rank::R8
    ];

    /// Converts this rank to its 0-based index starting at the first rank (1st = 0, 2nd = 1, ...).
    ///
    /// # Returns
    ///
    /// The 0-based index of this rank as a [usize].
    pub const fn as_usize(self) -> usize {
        self.0
    }

    /// Constructs a rank from its 0-based index starting at the first rank (0 = 1st, 1 = 2nd, ...).
    ///
    /// # Arguments
    ///
    /// * `rank`: The 0-based index of the rank to construct. Must be in the range 0 to 7 to yield a
    /// result.
    ///
    /// # Returns
    ///
    /// `Some(...)` with the rank with the given index, if it is in the valid range, and `None`
    /// otherwise.
    pub const fn from_usize(rank: usize) -> Option<Rank> {
        if rank < BOARD_HEIGHT {
            Some(Rank(rank))
        }
        else {
            None
        }
    }

    /// Gets the digit representing this rank.
    ///
    /// # Returns
    ///
    /// A [char] containing the digit representing this rank (`'1'`, `'2'`, ..., `'8'`).
    pub fn as_char(self) -> char {
        char::from_u32('1' as u32 + self.0 as u32).unwrap()
    }

    /// Gets the digit representing this rank as a UTF-8 byte.
    ///
    /// # Returns
    ///
    /// A [u8] that constitutes the UTF-8 representation of the digit representing this rank
    /// (`b'1'`, `b'2'`, ..., `b'8'`).
    pub const fn as_utf8_char(self) -> u8 {
        b'1' + self.0 as u8
    }

    /// Parses a rank from its digit.
    ///
    /// # Arguments
    ///
    /// * `rank`: A character containing the digit representing the rank to return (`'1'`, `'2'`,
    /// ..., `'8'`).
    ///
    /// # Returns
    ///
    /// `Some(...)` with the rank represented by the given digit, if it is in the valid range, and
    /// `None` otherwise.
    pub const fn from_char(rank: char) -> Option<Rank> {
        if rank >= '1' {
            Rank::from_usize(rank as usize - '1' as usize)
        }
        else {
            None
        }
    }
}

impl Display for Rank {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_char())
    }
}

/// Represents the location of a single square on the board as an index.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Location(pub(crate) usize);

impl Location {

    /// Gets the 0-based index of the [File] (column) in which this square lies.
    pub fn file(self) -> File {
        File::from_usize(self.0 % BOARD_WIDTH).unwrap()
    }

    /// Gets the 0-based index of the [Rank] (row) on which this square lies.
    pub fn rank(self) -> Rank {
        Rank::from_usize(self.0 / BOARD_WIDTH).unwrap()
    }

    /// Creates a new location that represents the square in the given file and
    /// rank.
    ///
    /// # Arguments
    ///
    /// * `file`: The [File] of the square for which to construct a location.
    /// * `rank`: The [Rank] of the square for which to construct a location.
    ///
    /// # Returns
    ///
    /// A new location representing the square at the given file and rank.
    pub const fn from_file_and_rank(file: File, rank: Rank) -> Location {
        Location(rank.as_usize() * BOARD_WIDTH + file.as_usize())
    }
}

impl Display for Location {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", self.file(), self.rank())
    }
}

impl From<(File, Rank)> for Location {
    fn from((file, rank): (File, Rank)) -> Location {
        Location::from_file_and_rank(file, rank)
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
#[derive(Clone, Copy, Debug, Deserialize, Eq, Hash, PartialEq, Serialize)]
pub struct Bitboard(pub u64);

impl Bitboard {

    /// The bitboard which contains no field.
    pub const EMPTY: Bitboard = Bitboard(0);

    /// The bitboard which contains every field.
    pub const FULL: Bitboard = Bitboard(0xffffffffffffffff);

    /// The bitboard which contains all light squares.
    pub const LIGHT_SQUARES: Bitboard = Bitboard(0x55aa55aa55aa55aa);

    /// The bitboard which contains all dark squares.
    pub const DARK_SQUARES: Bitboard = Bitboard(0xaa55aa55aa55aa55);

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
    pub const fn singleton(location: Location) -> Bitboard {
        Bitboard(1 << location.0)
    }

    /// Creates a new bitboards which contains all fields specified by the given array.
    ///
    /// # Arguments
    ///
    /// * `locations`: An array of [Location]s, each of which is added to the resulting bitboard.
    ///
    /// # Returns
    ///
    /// A new bitboard which contains the given `locations` and nothing else.
    pub const fn of<const LEN: usize>(locations: [Location; LEN]) -> Bitboard {
        // TODO cleanup once more features become const (for loop, |=-operator)

        let mut result = Bitboard::EMPTY;
        let mut index = 0;

        loop {
            if index == LEN {
                return result;
            }

            result = result.union(Bitboard::singleton(locations[index]));
            index += 1;
        }
    }

    /// Gets a bitboard of all fields in the given file.
    ///
    /// # Arguments
    ///
    /// * `file`: The file for which to get a bitboard.
    ///
    /// # Returns
    ///
    /// A bitboard which contains all fields in the given `file`.
    pub const fn of_file(file: File) -> Bitboard {
        const OF_A_FILE: u64 = 0x0101010101010101;

        Bitboard(OF_A_FILE << file.as_usize())
    }

    /// Gets a bitboard of all fields on the given rank.
    ///
    /// # Arguments
    ///
    /// * `rank`: The rank for which to get a bitboard.
    ///
    /// # Returns
    ///
    /// A bitboard which contains all fields on the given `rank`.
    pub const fn of_rank(rank: Rank) -> Bitboard {
        const OF_RANK_1: u64 = 0x00000000000000ff;

        Bitboard(OF_RANK_1 << (rank.as_usize() * BOARD_WIDTH))
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

    pub fn is_subset(self, other: Bitboard) -> bool {
        self & other == self
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

    /// Computes the union of this and the given other bitboard, containing all fields which are
    /// contained in either one. Also accessible through the operator [BitOr].
    ///
    /// # Arguments
    ///
    /// * `other`: The other operand in the union operation, besides the callee.
    ///
    /// # Returns
    ///
    /// A bitboard containing exactly those fields contained in this or the `other` bitboard.
    #[inline]
    pub const fn union(self, other: Bitboard) -> Bitboard {
        Bitboard(self.0 | other.0)
    }

    /// Computes the intersection of this and the given other bitboard, containing all fields which
    /// are contained in both. Also accessible through the operator [BitAnd].
    ///
    /// # Arguments
    ///
    /// * `other`: The other operand in the intersection operation, besides the callee.
    ///
    /// # Returns
    ///
    /// A bitboard containing exactly those fields contained in this and the `other` bitboard.
    #[inline]
    pub const fn intersection(self, other: Bitboard) -> Bitboard {
        Bitboard(self.0 & other.0)
    }

    /// Computes the symmetric difference between this and the given other bitboard, containing all
    /// fields which are contained in one, but not both. Also accessible through the operator
    /// [BitXor].
    ///
    /// # Arguments
    ///
    /// * `other`: The other operand in the symmetric difference operation, besides the callee.
    ///
    /// # Returns
    ///
    /// A bitboard containing exactly those fields contained in this or the `other` bitboard, but
    /// not both.
    #[inline]
    pub const fn symmetric_difference(self, other: Bitboard) -> Bitboard {
        Bitboard(self.0 ^ other.0)
    }

    /// Computes the difference between this and the given other bitboard, containing all fields
    /// which are contained in this one, but not the `other`. Also accessible through the operator
    /// [BitAnd].
    ///
    /// # Arguments
    ///
    /// * `other`: The other operand in the difference operation, containing the fields to be
    /// excluded from the callee.
    ///
    /// # Returns
    ///
    /// A bitboard containing exactly those fields contained in this bitboard, but not the `other`.
    #[inline]
    pub const fn difference(self, other: Bitboard) -> Bitboard {
        Bitboard(self.0 & !other.0)
    }
}

impl BitOr for Bitboard {
    type Output = Bitboard;

    fn bitor(self, rhs: Bitboard) -> Bitboard {
        self.union(rhs)
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
        self.intersection(rhs)
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
        self.symmetric_difference(rhs)
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
        self.difference(rhs)
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

const INITIAL_WHITE: Bitboard = Bitboard::of_rank(Rank::R1).union(Bitboard::of_rank(Rank::R2));
const INITIAL_BLACK: Bitboard = Bitboard::of_rank(Rank::R8).union(Bitboard::of_rank(Rank::R7));

const INITIAL_PAWN: Bitboard = Bitboard::of_rank(Rank::R2).union(Bitboard::of_rank(Rank::R7));
const INITIAL_KNIGHT: Bitboard = Bitboard::of([B1, G1, B8, G8]);
const INITIAL_BISHOP: Bitboard = Bitboard::of([C1, F1, C8, F8]);
const INITIAL_ROOK: Bitboard = Bitboard::of([A1, H1, A8, H8]);
const INITIAL_QUEEN: Bitboard = Bitboard::of([D1, D8]);
const INITIAL_KING: Bitboard = Bitboard::of([E1, E8]);

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

    pub fn unique_id(&self) -> [Bitboard; 4] {
        [
            self.players[0],
            self.pieces[0] | self.pieces[1] | self.pieces[2],
            self.pieces[0] | self.pieces[3] | self.pieces[4],
            self.pieces[2] | self.pieces[3] | self.pieces[5]
        ]
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

    /// Indicates whether a given field contains a piece of a specific kind.
    ///
    /// # Arguments
    ///
    /// * `piece`: The [Piece] kind to check whether it is contained on the
    /// given field.
    /// * `location`: The [Location] of the field to check for the given piece.
    ///
    /// # Returns
    ///
    /// True, if and only if there is a piece of the given `piece` kind on the
    /// field with the given `location`.
    pub fn is_of_kind(&self, piece: Piece, location: Location) -> bool {
        self.of_kind(piece).contains(location)
    }

    /// Indicates whether any of the given fields contain a piece of a specific
    /// kind.
    ///
    /// # Arguments
    ///
    /// * `piece`: The [Piece] kind to check whether it is contained on the
    /// given fields.
    /// * `fields`: A [Bitboard] containing the fields to check for the given
    /// piece.
    ///
    /// # Returns
    ///
    /// True, if and only if there is a piece of the given `piece` kind on any
    /// of the given `fields` in the bitboard.
    pub fn is_of_kind_any(&self, piece: Piece, fields: Bitboard) -> bool {
        !(self.of_kind(piece) & fields).is_empty()
    }

    /// Indicates whether all of the given fields contain a piece of a specific
    /// kind.
    ///
    /// # Arguments
    ///
    /// * `piece`: The [Piece] kind to check whether it is contained on the
    /// given fields.
    /// * `fields`: A [Bitboard] containing the fields to check for the given
    /// piece.
    ///
    /// # Returns
    ///
    /// True, if and only if there is a piece of the given `piece` kind on all
    /// of the given `fields` in the bitboard.
    pub fn is_of_kind_all(&self, piece: Piece, fields: Bitboard) -> bool {
        self.of_kind(piece) & fields == fields
    }

    pub fn piece_at(&self, location: Location) -> Option<Piece> {
        PIECES.into_iter()
            .find(|&p| self.pieces[p as usize].contains(location))
    }

    pub fn player_at(&self, location: Location) -> Option<Player> {
        PLAYERS.into_iter()
            .find(|&p| self.players[p as usize].contains(location))
    }

    pub(crate) fn piece_at_singleton(&self, singleton: Bitboard) -> Piece {
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

    fn pieces_players_mut(&mut self, piece: Piece, player: Player)
            -> (&mut Bitboard, &mut Bitboard) {
        (&mut self.pieces[piece as usize], &mut self.players[player as usize])
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
            .find(|&&p| !(self.of_kind(p) & mask).is_empty())
            .expect("no piece in occupied field");

        Some((piece, player))
    }

    fn apply_capture(&mut self, captured: Option<Piece>, target: Bitboard,
            player: Player) {
        if let Some(captured) = captured {
            let (piece_bb, player_bb) =
                self.pieces_players_mut(captured, player.opponent());

            *piece_bb ^= target;
            *player_bb ^= target;
        }
    }

    fn apply_move<F>(&mut self, player: Player, mov: &Move, get_target: F)
    where
        F: Fn(Bitboard, Bitboard) -> Bitboard
    {
        match *mov {
            Move::Ordinary { moved, captured, delta_mask } => {
                let (piece_bb, player_bb) =
                    self.pieces_players_mut(moved, player);
                let target = get_target(delta_mask, *player_bb);

                *piece_bb ^= delta_mask;
                *player_bb ^= delta_mask;

                self.apply_capture(captured, target, player);
            },
            Move::EnPassant { delta_mask, target } => {
                *self.players_mut(player) ^= delta_mask;
                *self.players_mut(player.opponent()) ^= target;
                *self.pieces_mut(Piece::Pawn) ^= delta_mask | target;
            },
            Move::Promotion { promotion, captured, delta_mask } => {
                let (pawn_bb, player_bb) =
                    self.pieces_players_mut(Piece::Pawn, player);
                let target = get_target(delta_mask, *player_bb);
                let origin = delta_mask - target;

                *pawn_bb ^= origin;
                *player_bb ^= delta_mask;
                *self.pieces_mut(promotion) ^= target;

                self.apply_capture(captured, target, player);
            },
            Move::Castle { king_delta_mask, rook_delta_mask } => {
                *self.players_mut(player) ^= king_delta_mask | rook_delta_mask;
                *self.pieces_mut(Piece::King) ^= king_delta_mask;
                *self.pieces_mut(Piece::Rook) ^= rook_delta_mask;
            }
        }
    }

    /// Applies the given move made by the given player to this board, that is,
    /// moves/removes/promotes all necessary pieces.
    ///
    /// # Arguments
    ///
    /// * `player`: The [Player] who makes the move to apply.
    /// * `mov`: The [Move] to apply.
    pub fn make_move(&mut self, player: Player, mov: &Move) {
        self.apply_move(player, mov,
            |delta_mask, player_bb| delta_mask - player_bb)
    }

    /// Reverts the given move made by the given player to this board, that is,
    /// moves all pieces back, puts back captured pieces, and reverts
    /// promotions. This restores the state of the board after a call to
    /// [Board::make_move] with the same arguments.
    ///
    /// # Arguments
    ///
    /// * `player`: The [Player] who made the move to revert.
    /// * `mov`: The [Move] to revert.
    pub fn unmake_move(&mut self, player: Player, mov: &Move) {
        self.apply_move(player, mov,
            |delta_mask, player_bb| delta_mask & player_bb)
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
    /// * [FenError::InvalidPiece] if any character that appears in a rank does
    /// not represent a piece or a gap of valid size (i.e. greater than 0 and
    /// less than [BOARD_WIDTH]).
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

    use kernal::prelude::*;

    use rstest::rstest;

    use super::*;

    use crate::board::locations::*;

    #[test]
    fn empty_bitboard_location_iterator() {
        assert!(Bitboard::EMPTY.locations().next().is_none());
    }

    #[test]
    fn bitboard_with_min_location_iterator() {
        let bitboard = Bitboard::of([A1, E1, F1, A2]);
        let locations = bitboard.locations().collect::<Vec<_>>();

        assert_eq!(vec![A1, E1, F1, A2], locations);
    }

    #[test]
    fn bitboard_with_max_location_iterator() {
        let bitboard = Bitboard::of([E1, F1, A2, H8]);
        let locations = bitboard.locations().collect::<Vec<_>>();

        assert_eq!(vec![E1, F1, A2, H8], locations);
    }

    #[test]
    fn empty_bitboard_singleton_iterator() {
        assert!(Bitboard::EMPTY.singletons().next().is_none());
    }

    #[test]
    fn bitboard_with_min_singleton_iterator() {
        let bitboard = Bitboard::of([A1, E1, F1, A2]);
        let locations = bitboard.singletons().collect::<Vec<_>>();

        assert_eq!(
            vec![
                Bitboard::singleton(A1),
                Bitboard::singleton(E1),
                Bitboard::singleton(F1),
                Bitboard::singleton(A2)],
            locations);
    }

    #[test]
    fn bitboard_with_max_singleton_iterator() {
        let bitboard = Bitboard::of([E1, F1, A2, H8]);
        let locations = bitboard.singletons().collect::<Vec<_>>();

        assert_eq!(
            vec![
                Bitboard::singleton(E1),
                Bitboard::singleton(F1),
                Bitboard::singleton(A2),
                Bitboard::singleton(H8)],
            locations);
    }

    #[rstest]
    #[case::empty([], Bitboard(0))]
    #[case::single([A1], Bitboard(1))]
    #[case::multiple([A1, B1], Bitboard(3))]
    #[case::repeats([B1, C1, B1], Bitboard(6))]
    fn bitboard_from_multiple_locations<const LEN: usize>(
            #[case] locations: [Location; LEN],
            #[case] expected: Bitboard) {
        let actual = Bitboard::of(locations);

        assert_that!(actual).is_equal_to(expected);
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

    fn assert_consistent(board: &Board) {
        let mut all_pieces = Bitboard::EMPTY;

        for piece in PIECES {
            let bitboard = board.of_kind(piece);
            all_pieces |= bitboard;

            for other_piece in PIECES {
                if piece == other_piece {
                    continue;
                }

                let other_bitboard = board.of_kind(other_piece);

                assert!((bitboard & other_bitboard).is_empty());
            }
        }

        assert!(
            (board.of_player(Player::White) & board.of_player(Player::Black))
                .is_empty());

        let all_players = board.of_player(Player::White) |
            board.of_player(Player::Black);

        assert!(all_pieces == all_players);
    }

    fn test_move(original_fen: &str, player: Player, mov: Move,
            expected_fen: &str) {
        let mut board = Board::from_fen(original_fen).unwrap();
        board.make_move(player, &mov);

        assert_eq!(expected_fen, &board.to_fen());
        assert_consistent(&board);

        board.unmake_move(player, &mov);

        assert_eq!(original_fen, &board.to_fen());
        assert_consistent(&board);
    }

    #[test]
    fn pawn_push_applied_and_reverted_correctly() {
        // Board (black to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │ r │   │   │ q │ r │   │ k │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ p │ p │   │   │   │ p │ p │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │ p │   │ n │   │ p │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ p │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ B │ n │ P │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ N │   │   │   │   │ P │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ P │ P │ P │   │   │   │ P │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ R │   │   │ Q │   │ R │ K │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // Black pushes the pawn on b7.

        let original_fen =
            "r2qr1k1/pp3pp1/3p1n1p/2p5/2BnP3/2N4P/PPP3P1/R2Q1RK1";
        let mov = Move::Ordinary {
            moved: Piece::Pawn,
            captured: None,
            delta_mask: Bitboard::of([B7, B6])
        };
        let expected_fen =
            "r2qr1k1/p4pp1/1p1p1n1p/2p5/2BnP3/2N4P/PPP3P1/R2Q1RK1";

        test_move(original_fen, Player::Black, mov, expected_fen);
    }

    #[test]
    fn pawn_double_push_applied_and_reverted_correctly() {
        // Board (black to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │ r │   │   │ q │ r │   │ k │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ p │ p │   │   │   │ p │ p │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │ p │   │ n │   │ p │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ p │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ B │ n │ P │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ N │   │   │   │   │ P │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ P │ P │ P │   │   │   │ P │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ R │   │   │ Q │   │ R │ K │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // Black pushes the pawn on b7 by 2 squares.

        let original_fen =
            "r2qr1k1/pp3pp1/3p1n1p/2p5/2BnP3/2N4P/PPP3P1/R2Q1RK1";
        let mov = Move::Ordinary {
            moved: Piece::Pawn,
            captured: None,
            delta_mask: Bitboard::of([B7, B5])
        };
        let expected_fen =
            "r2qr1k1/p4pp1/3p1n1p/1pp5/2BnP3/2N4P/PPP3P1/R2Q1RK1";

        test_move(original_fen, Player::Black, mov, expected_fen);
    }

    #[test]
    fn pawn_capture_applied_and_reverted_correctly() {
        // Board (white to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │ r │ n │ b │ q │ k │ b │ n │ r │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ p │ p │ p │ p │   │ p │ p │ p │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │ p │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │ P │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ P │ P │ P │   │ P │ P │ P │ P │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ R │ N │ B │ Q │ K │ B │ N │ R │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // White captures the pawn on e5.

        let original_fen = "rnbqkbnr/pppp1ppp/8/4p3/3P4/8/PPP1PPPP/RNBQKBNR";
        let mov = Move::Ordinary {
            moved: Piece::Pawn,
            captured: Some(Piece::Pawn),
            delta_mask: Bitboard::of([D4, E5])
        };
        let expected_fen = "rnbqkbnr/pppp1ppp/8/4P3/8/8/PPP1PPPP/RNBQKBNR";

        test_move(original_fen, Player::White, mov, expected_fen);
    }

    #[test]
    fn promotion_applied_and_reverted_correctly() {
        // Board (black to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ P │   │   │   │   │   │ b │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │ P │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ P │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │ K │   │   │   │ p │ k │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │ R │   │   │   │   │   │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // Black pushes the pawn to f1 and promotes to a queen.

        let original_fen = "8/8/8/P5b1/1P6/2P5/1K3pk1/1R6";
        let mov = Move::Promotion {
            promotion: Piece::Queen,
            captured: None,
            delta_mask: Bitboard::of([F2, F1])
        };
        let expected_fen = "8/8/8/P5b1/1P6/2P5/1K4k1/1R3q2";

        test_move(original_fen, Player::Black, mov, expected_fen);
    }

    #[test]
    fn capture_promotion_applied_and_reverted_correctly() {
        // Board (white to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │   │   │   │ n │   │   │ k │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ P │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │ K │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // White takes the knight on d8 with the pawn and promotes to a rook.

        let original_fen = "3n2k1/2P5/8/1K6/8/8/8/8";
        let mov = Move::Promotion {
            promotion: Piece::Rook,
            captured: Some(Piece::Knight),
            delta_mask: Bitboard::of([C7, D8])
        };
        let expected_fen = "3R2k1/8/8/1K6/8/8/8/8";

        test_move(original_fen, Player::White, mov, expected_fen);
    }

    #[test]
    fn en_passant_applied_and_reverted_correctly() {
        // Board (black to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │ k │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │ p │ P │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │ K │   │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // Where white just pushed the pawn to f4. Black takes en-passant.

        let original_fen = "8/8/8/4k3/4pP2/8/8/5K2";
        let mov = Move::EnPassant {
            delta_mask: Bitboard::of([E4, F3]),
            target: Bitboard::singleton(F4)
        };
        let expected_fen = "8/8/8/4k3/8/5p2/8/5K2";

        test_move(original_fen, Player::Black, mov, expected_fen);
    }

    #[test]
    fn knight_move_applied_and_reverted_correctly() {
        // Board (white to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │ r │ n │ b │ q │ k │ b │ n │ r │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ p │ p │ p │ p │   │ p │ p │ p │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │ p │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │ P │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ P │ P │ P │ P │   │ P │ P │ P │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ R │ N │ B │ Q │ K │ B │ N │ R │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // White plays knight to f3.

        let original_fen = "rnbqkbnr/pppp1ppp/8/4p3/4P3/8/PPPP1PPP/RNBQKBNR";
        let mov = Move::Ordinary {
            moved: Piece::Knight,
            captured: None,
            delta_mask: Bitboard::of([G1, F3])
        };
        let expected_fen = "rnbqkbnr/pppp1ppp/8/4p3/4P3/5N2/PPPP1PPP/RNBQKB1R";

        test_move(original_fen, Player::White, mov, expected_fen);
    }

    #[test]
    fn knight_capture_applied_and_reverted_correctly() {
        // Board (black to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │ r │ n │ b │ q │ k │ b │   │ r │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ p │ p │ p │ p │   │ p │ p │ p │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │ n │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │ N │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │ P │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ P │ P │ P │ P │   │ P │ P │ P │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ R │ N │ B │ Q │ K │ B │   │ R │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // Black takes the pawn on e4 with the knight on f6.

        let original_fen = "rnbqkb1r/pppp1ppp/5n2/4N3/4P3/8/PPPP1PPP/RNBQKB1R";
        let mov = Move::Ordinary {
            moved: Piece::Knight,
            captured: Some(Piece::Pawn),
            delta_mask: Bitboard::of([F6, E4])
        };
        let expected_fen = "rnbqkb1r/pppp1ppp/8/4N3/4n3/8/PPPP1PPP/RNBQKB1R";

        test_move(original_fen, Player::Black, mov, expected_fen);
    }

    #[test]
    fn bishop_move_applied_and_reverted_correctly() {
        // Board (black to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │ r │ n │ b │ q │ k │ b │   │ r │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ p │ p │ p │ p │   │ p │ p │ p │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │ N │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │ n │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │ B │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ P │ P │ P │ P │   │ P │ P │ P │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ R │ N │ B │ Q │ K │   │   │ R │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // Black moves the bishop to d6.

        let original_fen = "rnbqkb1r/pppp1ppp/8/4N3/4n3/3B4/PPPP1PPP/RNBQK2R";
        let mov = Move::Ordinary {
            moved: Piece::Bishop,
            captured: None,
            delta_mask: Bitboard::of([F8, D6])
        };
        let expected_fen = "rnbqk2r/pppp1ppp/3b4/4N3/4n3/3B4/PPPP1PPP/RNBQK2R";

        test_move(original_fen, Player::Black, mov, expected_fen);
    }

    #[test]
    fn bishop_capture_applied_and_reverted_correctly() {
        // Board (white to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │ r │ n │ b │ q │ k │   │   │ r │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ p │ p │ p │ p │   │ p │ p │ p │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │ b │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │ N │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │ n │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │ B │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ P │ P │ P │ P │   │ P │ P │ P │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ R │ N │ B │ Q │ K │   │   │ R │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // White captures the knight on e4 with the bishop.

        let original_fen = "rnbqk2r/pppp1ppp/3b4/4N3/4n3/3B4/PPPP1PPP/RNBQK2R";
        let mov = Move::Ordinary {
            moved: Piece::Bishop,
            captured: Some(Piece::Knight),
            delta_mask: Bitboard::of([D3, E4])
        };
        let expected_fen = "rnbqk2r/pppp1ppp/3b4/4N3/4B3/8/PPPP1PPP/RNBQK2R";

        test_move(original_fen, Player::White, mov, expected_fen);
    }

    #[test]
    fn rook_move_applied_and_reverted_correctly() {
        // Board (white to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │   │   │   │   │ r │   │ k │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ p │   │   │   │ p │ p │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │ p │   │ p │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │ q │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │ N │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ P │   │   │   │   │ P │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ P │ P │   │   │   │ P │ P │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │ R │   │   │   │ R │ K │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // White moves the rook from b1 to e1.

        let original_fen = "4r1k1/2p3pp/3p1p2/7q/5N2/2P4P/PP3PP1/1R3RK1";
        let mov = Move::Ordinary {
            moved: Piece::Rook,
            captured: None,
            delta_mask: Bitboard::of([B1, E1])
        };
        let expected_fen = "4r1k1/2p3pp/3p1p2/7q/5N2/2P4P/PP3PP1/4RRK1";

        test_move(original_fen, Player::White, mov, expected_fen);
    }

    #[test]
    fn rook_capture_applied_and_reverted_correctly() {
        // Board (black to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │   │   │   │   │ r │   │ k │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ p │   │   │   │ p │ p │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │ p │   │ p │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │ q │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │ N │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ P │   │   │   │   │ P │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ P │ P │   │   │   │ P │ P │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │ R │ R │ K │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // Black captures the rook on e1 with their own rook.

        let original_fen = "4r1k1/2p3pp/3p1p2/7q/5N2/2P4P/PP3PP1/4RRK1";
        let mov = Move::Ordinary {
            moved: Piece::Rook,
            captured: Some(Piece::Rook),
            delta_mask: Bitboard::of([E8, E1])
        };
        let expected_fen = "6k1/2p3pp/3p1p2/7q/5N2/2P4P/PP3PP1/4rRK1";

        test_move(original_fen, Player::Black, mov, expected_fen);
    }

    #[test]
    fn queen_move_applied_and_reverted_correctly() {
        // Board (black to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │   │   │   │   │   │   │ k │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ p │   │   │   │ p │ p │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │ p │   │ p │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │ q │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │ N │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ P │   │   │   │   │ P │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ P │ P │   │   │   │ P │ P │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │ R │   │ K │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // Black moves the queen to g5.

        let original_fen = "6k1/2p3pp/3p1p2/7q/5N2/2P4P/PP3PP1/4R1K1";
        let mov = Move::Ordinary {
            moved: Piece::Queen,
            captured: None,
            delta_mask: Bitboard::of([H5, G5])
        };
        let expected_fen = "6k1/2p3pp/3p1p2/6q1/5N2/2P4P/PP3PP1/4R1K1";

        test_move(original_fen, Player::Black, mov, expected_fen);
    }

    #[test]
    fn queen_capture_applied_and_reverted_correctly() {
        // Board (black to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │   │   │   │   │   │   │ k │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ p │   │ R │   │ p │ p │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │ p │   │ p │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │ q │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │ N │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ P │   │   │   │   │ P │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ P │ P │   │   │   │ P │ P │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │ K │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // Black captures the knight on f4 with the queen

        let original_fen = "6k1/2p1R1pp/3p1p2/6q1/5N2/2P4P/PP3PP1/6K1";
        let mov = Move::Ordinary {
            moved: Piece::Queen,
            captured: Some(Piece::Knight),
            delta_mask: Bitboard::of([G5, F4])
        };
        let expected_fen = "6k1/2p1R1pp/3p1p2/8/5q2/2P4P/PP3PP1/6K1";

        test_move(original_fen, Player::Black, mov, expected_fen);
    }

    #[test]
    fn king_move_applied_and_reverted_correctly() {
        // Board (black to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ k │   │ p │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │ P │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ K │   │   │   │   │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // Black moves the king to d3.

        let original_fen = "8/8/8/8/2k1p3/4P3/8/2K5";
        let mov = Move::Ordinary {
            moved: Piece::King,
            captured: None,
            delta_mask: Bitboard::of([C4, D3])
        };
        let expected_fen = "8/8/8/8/4p3/3kP3/8/2K5";

        test_move(original_fen, Player::Black, mov, expected_fen);
    }

    #[test]
    fn king_capture_applied_and_reverted_correctly() {
        // Board (black to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │ p │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │ k │ P │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │ K │   │   │   │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // Black captures the pawn on e3 with their king.

        let original_fen = "8/8/8/8/4p3/3kP3/8/3K4";
        let mov = Move::Ordinary {
            moved: Piece::King,
            captured: Some(Piece::Pawn),
            delta_mask: Bitboard::of([D3, E3])
        };
        let expected_fen = "8/8/8/8/4p3/4k3/8/3K4";

        test_move(original_fen, Player::Black, mov, expected_fen);
    }

    #[test]
    fn white_long_castle_applied_and_reverted_correctly() {
        // Board (white to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │ r │   │   │   │ k │   │   │ r │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ p │ b │ p │ p │ q │ p │ p │ p │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │ p │ n │   │   │ n │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ b │   │ p │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ B │   │ P │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │ P │ N │   │   │ N │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ P │ B │ P │ P │ Q │ P │ P │ P │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ R │   │   │   │ K │   │   │ R │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // White castles long.

        let original_fen =
            "r3k2r/pbppqppp/1pn2n2/2b1p3/2B1P3/1PN2N2/PBPPQPPP/R3K2R";
        let mov = Move::Castle {
            king_delta_mask: Bitboard::of([E1, C1]),
            rook_delta_mask: Bitboard::of([A1, D1])
        };
        let expected_fen =
            "r3k2r/pbppqppp/1pn2n2/2b1p3/2B1P3/1PN2N2/PBPPQPPP/2KR3R";

        test_move(original_fen, Player::White, mov, expected_fen);
    }

    #[test]
    fn white_short_castle_applied_and_reverted_correctly() {
        // Board (white to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │ r │   │ b │ q │ k │   │   │ r │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ p │ p │ p │ p │   │ p │ p │ p │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ n │   │   │ n │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ b │   │ p │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ B │   │ P │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ N │   │   │ N │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ P │ P │ P │ P │   │ P │ P │ P │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ R │   │ B │ Q │ K │   │   │ R │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // White castles short.

        let original_fen =
            "r1bqk2r/pppp1ppp/2n2n2/2b1p3/2B1P3/2N2N2/PPPP1PPP/R1BQK2R";
        let mov = Move::Castle {
            king_delta_mask: Bitboard::of([E1, G1]),
            rook_delta_mask: Bitboard::of([H1, F1])
        };
        let expected_fen =
            "r1bqk2r/pppp1ppp/2n2n2/2b1p3/2B1P3/2N2N2/PPPP1PPP/R1BQ1RK1";

        test_move(original_fen, Player::White, mov, expected_fen);
    }

    #[test]
    fn black_long_castle_applied_and_reverted_correctly() {
        // Board (black to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │ r │   │   │   │ k │   │   │ r │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ p │ b │ p │ p │ q │ p │ p │ p │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │ p │ n │   │   │ n │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ b │   │ p │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ B │   │ P │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │ P │ N │   │   │ N │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ P │ B │ P │ P │ Q │ P │ P │ P │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ K │ R │   │   │   │ R │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // Black castles long.

        let original_fen =
            "r3k2r/pbppqppp/1pn2n2/2b1p3/2B1P3/1PN2N2/PBPPQPPP/2KR3R";
        let mov = Move::Castle {
            king_delta_mask: Bitboard::of([E8, C8]),
            rook_delta_mask: Bitboard::of([A8, D8])
        };
        let expected_fen =
            "2kr3r/pbppqppp/1pn2n2/2b1p3/2B1P3/1PN2N2/PBPPQPPP/2KR3R";

        test_move(original_fen, Player::Black, mov, expected_fen);
    }

    #[test]
    fn black_short_castle_applied_and_reverted_correctly() {
        // Board (black to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │ r │   │ b │ q │ k │   │   │ r │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ p │ p │ p │ p │   │ p │ p │ p │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ n │   │   │ n │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ b │   │ p │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ B │   │ P │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │ P │ N │   │   │ N │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ P │   │ P │ P │   │ P │ P │ P │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ R │   │ B │ Q │ K │   │   │ R │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // Black castles short.

        let original_fen =
            "r1bqk2r/pppp1ppp/2n2n2/2b1p3/2B1P3/1PN2N2/P1PP1PPP/R1BQK2R";
        let mov = Move::Castle {
            king_delta_mask: Bitboard::of([E8, G8]),
            rook_delta_mask: Bitboard::of([H8, F8])
        };
        let expected_fen =
            "r1bq1rk1/pppp1ppp/2n2n2/2b1p3/2B1P3/1PN2N2/P1PP1PPP/R1BQK2R";

        test_move(original_fen, Player::Black, mov, expected_fen);
    }
}
