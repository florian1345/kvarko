use std::convert::TryInto;
use std::fmt::Debug;
use std::iter;
use std::ops::BitXorAssign;

use rand::{SeedableRng, Rng};
use rand::distributions::Standard;
use rand::prelude::Distribution;
use rand::rngs::StdRng;

use crate::board::{Location, BOARD_WIDTH, BOARD_HEIGHT, Bitboard, File};
use crate::piece::{Piece, PIECE_COUNT};
use crate::player::{Player, PLAYER_COUNT, PLAYERS};
use crate::state::{Position, PositionId};

/// A trait for types which can convert a [Position] into some
/// [PositionHasher::Hash] value, which is usually smaller and easier to
/// process. Along with the expected [PositionHasher::hash] method, which
/// returns the hash of the given position, there are a number of other methods
/// that the hasher can rely on to notify it of any changes that occur to the
/// position.
pub trait PositionHasher {

    /// The type of hash values produced by this hasher.
    type Hash: Clone + Eq + PartialEq;

    /// Creates a new position hasher with state initialized to the given
    /// position.
    ///
    /// # Arguments
    ///
    /// * `position`: The [Position] to which the hasher shall be initialized.
    /// That is, if [PositionHasher::hash] is called immediately after the
    /// construction, it should return a valid hash for this position.
    ///
    /// # Returns
    ///
    /// A new position hasher initialized to the given position.
    fn init(position: &Position) -> Self;

    /// Computes the hash for the given position. It is required that the
    /// position is obtained by applying the given notifications to the initial
    /// position provided in [PositionHasher::init].
    ///
    /// # Arguments
    ///
    /// * `position`: The [Position] to hash. While this should be knowable, it
    /// is re-supplied here for simpler implementation of stateless hasher.
    ///
    /// # Returns
    ///
    /// The [PositionHasher::Hash] of the given/current position.
    fn hash(&self, position: &Position) -> Self::Hash;

    /// Notification that a piece entered a field. It is possible that two
    /// pieces temporarily inhabit the same field by this method.
    ///
    /// # Arguments
    ///
    /// * `piece`: The kind [Piece] which entered a field.
    /// * `player`: The [Player] whose piece entered a field.
    /// * `location`: The [Location] of the field which the piece entered.
    fn on_piece_entered(&mut self, piece: Piece, player: Player,
        location: Location);

    /// Notification that a piece left a field.
    ///
    /// # Arguments
    ///
    /// * `piece`: The kind [Piece] which left a field.
    /// * `player`: The [Player] whose piece left a field.
    /// * `location`: The [Location] of the field which the piece left.
    fn on_piece_left(&mut self, piece: Piece, player: Player,
        location: Location);

    /// Notification that capturing en-passant became available on a given file
    /// of the board. It is possible that two files temporarily allow
    /// en-passant by this method.
    ///
    /// # Arguments
    ///
    /// * `file`: The [File] on which capturing en passant is now available.
    fn on_en_passant_enabled(&mut self, file: File);

    /// Notification that capturing en-passant became unavailable on a given
    /// file of the board.
    ///
    /// # Arguments
    ///
    /// * `previous_file`: The [File] on which capturing en passant is no longer available.
    fn on_en_passant_disabled(&mut self, previous_file: File);

    /// Notification that a player lost one right to castle, that is, on one
    /// side.
    ///
    /// # Arguments
    ///
    /// * `player`: The [Player] who lost a castling right.
    /// * `long`: If this is true, the player lost the right to castle
    /// long/queen side. Otherwise, the player lost the right to castle
    /// short/king side.
    fn on_castling_right_lost(&mut self, player: Player, long: bool);

    /// Notification that a player gained one right to castle, that is, on one
    /// side. This can only occur during unmaking of moves.
    ///
    /// # Arguments
    ///
    /// * `player`: The [Player] who gained a castling right.
    /// * `long`: If this is true, the player gained the right to castle
    /// long/queen side. Otherwise, the player gained the right to castle
    /// short/king side.
    fn on_castling_right_gained(&mut self, player: Player, long: bool);

    /// Notification that a half-move was completed and the state whose turn it
    /// currently is changed.
    ///
    /// # Arguments
    ///
    /// * `turn`: The [Player] whose turn it is now (after the notification).
    fn on_turn_changed(&mut self, turn: Player);
}

const SQUARE_COUNT: usize = BOARD_WIDTH * BOARD_HEIGHT;

/// A [PositionHasher] which uses random IDs for every atomic state flag (e.g.
/// there is a white pawn on e4, en-passant is possible on the d-file, black
/// may castle short, it is white's turn) and computes a hash by XOR-ing all
/// IDs of flags that are true. This has the advantage of being fast if
/// computed alongside normal state changes. However, it can make no guarantees
/// about uniqueness of hashes.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ZobristHasher<H> {
    piece_hashes:
        Box<[[[H; SQUARE_COUNT]; PIECE_COUNT]; PLAYER_COUNT]>,
    en_passant_hashes: Box<[H; BOARD_WIDTH]>,
    castling_right_hashes: Box<[[H; PLAYER_COUNT]; 2]>,
    turn_hash: H,
    current_hash: H
}

impl<H> ZobristHasher<H>
where
    H: BitXorAssign + Clone + Copy
{
    fn toggle_piece(&mut self, piece: Piece, player: Player,
            location: Location) {
        self.current_hash ^=
            self.piece_hashes[player as usize][piece as usize][location.0];
    }

    fn toggle_en_passant(&mut self, file: File) {
        self.current_hash ^= self.en_passant_hashes[file.as_usize()];
    }

    fn toggle_castling_right(&mut self, player: Player, long: bool) {
        self.current_hash ^=
            self.castling_right_hashes[long as usize][player as usize];
    }

    fn toggle_turn(&mut self) {
        self.current_hash ^= self.turn_hash;
    }

    fn init(&mut self, position: &Position) {
        for location in Bitboard::FULL.locations() {
            if let Some(piece) = position.board().piece_at(location) {
                let player = position.board().player_at(location).unwrap();
                self.toggle_piece(piece, player, location);
            }
        }

        if let Some(en_passant_file) = position.en_passant_file() {
            self.toggle_en_passant(en_passant_file);
        }

        for player in PLAYERS {
            if position.may_short_castle(player) {
                self.toggle_castling_right(player, false);
            }

            if position.may_long_castle(player) {
                self.toggle_castling_right(player, true);
            }
        }

        if position.turn() == Player::Black {
            self.toggle_turn();
        }
    }
}

fn array_with<T, F, const N: usize>(cons: F) -> [T; N]
where
    T: Debug,
    F: FnMut() -> T
{
    iter::repeat_with(cons)
        .take(N)
        .collect::<Vec<_>>()
        .try_into()
        .unwrap()
}

impl<H> ZobristHasher<H>
where
    H: BitXorAssign + Clone + Copy + Debug + Default,
    Standard: Distribution<H>
{
    fn new(seed: [u8; 32], position: &Position) -> ZobristHasher<H> {
        let mut rng = StdRng::from_seed(seed);
        let piece_hashes =
            Box::new(array_with::<_, _, PLAYER_COUNT>(||
                array_with::<_, _, PIECE_COUNT>(||
                    array_with::<_, _, SQUARE_COUNT>(|| rng.gen::<H>()))));
        let en_passant_hashes =
            Box::new(array_with::<_, _, BOARD_WIDTH>(|| rng.gen::<H>()));
        let castling_right_hashes =
            Box::new(array_with::<_, _, 2>(||
                array_with::<_, _, PLAYER_COUNT>(|| rng.gen::<H>())));
        let turn_hash = rng.gen::<H>();
        let mut hasher = ZobristHasher {
            piece_hashes,
            en_passant_hashes,
            castling_right_hashes,
            turn_hash,
            current_hash: H::default()
        };

        hasher.init(position);

        hasher
    }

    pub fn current_hash(&self) -> H {
        self.current_hash
    }
}

const SEED: [u8; 32] = [
    0xe6, 0x38, 0x9d, 0xa7, 0x85, 0x26, 0xee, 0x45,
    0x00, 0x69, 0x04, 0xfb, 0xf0, 0x81, 0x12, 0x90,
    0xb4, 0x6c, 0x1a, 0x63, 0x08, 0x1d, 0xae, 0xe8,
    0xec, 0x5f, 0xef, 0x75, 0x08, 0x4e, 0x1d, 0x6d
];

impl<H> PositionHasher for ZobristHasher<H>
where
    H: BitXorAssign + Clone + Copy + Debug + Default + Eq + PartialEq,
    Standard: Distribution<H>
{
    type Hash = H;

    fn init(position: &Position) -> ZobristHasher<H> {
        ZobristHasher::new(SEED, position)
    }

    fn hash(&self, _position: &Position) -> H {
        self.current_hash()
    }

    fn on_piece_entered(&mut self, piece: Piece, player: Player,
            location: Location) {
        self.toggle_piece(piece, player, location);
    }

    fn on_piece_left(&mut self, piece: Piece, player: Player,
            location: Location) {
        self.toggle_piece(piece, player, location);
    }

    fn on_en_passant_enabled(&mut self, file: File) {
        self.toggle_en_passant(file);
    }

    fn on_en_passant_disabled(&mut self, previous_file: File) {
        self.toggle_en_passant(previous_file);
    }

    fn on_castling_right_lost(&mut self, player: Player, long: bool) {
        self.toggle_castling_right(player, long);
    }

    fn on_castling_right_gained(&mut self, player: Player, long: bool) {
        self.toggle_castling_right(player, long);
    }

    fn on_turn_changed(&mut self, _turn: Player) {
        self.toggle_turn();
    }
}

/// A [PositionHasher] that uses unique IDs provided by positions in
/// [Position::unique_id] as hash values. This is normally slower than using a
/// [ZobristHasher], but guarantees no hash collisions happen.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct IdHasher;

impl PositionHasher for IdHasher {
    type Hash = PositionId;

    fn init(_: &Position) -> IdHasher {
        IdHasher
    }

    fn hash(&self, position: &Position) -> PositionId {
        position.unique_id()
    }

    fn on_piece_entered(&mut self, _: Piece, _: Player, _: Location) { }

    fn on_piece_left(&mut self, _: Piece, _: Player, _: Location) { }

    fn on_en_passant_enabled(&mut self, _: File) { }

    fn on_en_passant_disabled(&mut self, _: File) { }

    fn on_castling_right_lost(&mut self, _: Player, _: bool) { }

    fn on_castling_right_gained(&mut self, _: Player, _: bool) { }

    fn on_turn_changed(&mut self, _: Player) { }
}
