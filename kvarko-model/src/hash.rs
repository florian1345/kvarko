use std::convert::TryInto;
use std::fmt::Debug;
use std::iter;
use std::ops::BitXorAssign;

use rand::{SeedableRng, Rng};
use rand::distributions::Standard;
use rand::prelude::Distribution;
use rand::rngs::StdRng;

use crate::board::{Location, BOARD_WIDTH, BOARD_HEIGHT, Bitboard};
use crate::piece::{Piece, PIECE_COUNT};
use crate::player::{Player, PLAYER_COUNT, PLAYERS};
use crate::state::Position;

pub trait PositionHasher {
    fn on_piece_entered(&mut self, piece: Piece, player: Player,
        location: Location);

    fn on_piece_left(&mut self, piece: Piece, player: Player,
        location: Location);

    fn on_en_passant_enabled(&mut self, file: usize);

    fn on_en_passant_disabled(&mut self, previous_file: usize);

    fn on_castling_right_lost(&mut self, player: Player, long: bool);

    fn on_castling_right_gained(&mut self, player: Player, long: bool);

    fn on_turn_changed(&mut self, turn: Player);
}

const SQUARE_COUNT: usize = BOARD_WIDTH * BOARD_HEIGHT;

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

    fn toggle_en_passant(&mut self, file: usize) {
        self.current_hash ^= self.en_passant_hashes[file];
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
    pub fn new(seed: [u8; 32], position: &Position) -> ZobristHasher<H> {
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

impl<H> PositionHasher for ZobristHasher<H>
where
    H: BitXorAssign + Clone + Copy
{
    fn on_piece_entered(&mut self, piece: Piece, player: Player,
            location: Location) {
        self.toggle_piece(piece, player, location);
    }

    fn on_piece_left(&mut self, piece: Piece, player: Player,
            location: Location) {
        self.toggle_piece(piece, player, location);
    }

    fn on_en_passant_enabled(&mut self, file: usize) {
        self.toggle_en_passant(file);
    }

    fn on_en_passant_disabled(&mut self, previous_file: usize) {
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

pub(crate) struct NopHasher;

impl PositionHasher for NopHasher {
    fn on_piece_entered(&mut self, _: Piece, _: Player, _: Location) { }

    fn on_piece_left(&mut self, _: Piece, _: Player, _: Location) { }

    fn on_en_passant_enabled(&mut self, _: usize) { }

    fn on_en_passant_disabled(&mut self, _: usize) { }

    fn on_castling_right_lost(&mut self, _: Player, _: bool) { }

    fn on_castling_right_gained(&mut self, _: Player, _: bool) { }

    fn on_turn_changed(&mut self, _: Player) { }
}
