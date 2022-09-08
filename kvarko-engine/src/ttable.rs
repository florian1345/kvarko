use kvarko_model::movement::Move;
use kvarko_model::state::{Position, PositionId};

use std::iter;

pub trait PositionHash : Copy + Clone + Eq {
    fn as_usize(self) -> usize;
}

pub trait PositionHasher {
    type Hash : PositionHash;

    fn get(&self, position: &PositionId) -> Self::Hash;
}

impl PositionHash for u64 {
    fn as_usize(self) -> usize {
        self as usize
    }
}

const PRIMES: [u64; 9] = [
    1768914325752446339,
    1770762389520301717,
    7361957799628335583,
    4677770329780902253,
    7582026240224591227,
    3614182435694795611,
    9015491412946165507,
    2508389373864496531,
    7358950217208819701
];

pub struct StatelessHasher;

impl PositionHasher for StatelessHasher {
    type Hash = u64;

    fn get(&self, id: &PositionId) -> u64 {
        /*let board = position.board();
        let raw_inputs = [
            board.of_player(Player::White).0,
            board.of_player(Player::Black).0,
            board.of_kind(Piece::Pawn).0,
            board.of_kind(Piece::Knight).0,
            board.of_kind(Piece::Bishop).0,
            board.of_kind(Piece::Rook).0,
            board.of_kind(Piece::Queen).0,
            board.of_kind(Piece::King).0,
            position.en_passant_file().unwrap_or(8) as u64 +
                (position.may_short_castle(Player::White) as u64) << 5 +
                (position.may_short_castle(Player::Black) as u64) << 6 +
                (position.may_long_castle(Player::White) as u64) << 7 +
                (position.may_long_castle(Player::Black) as u64) << 8 +
                (position.turn() as u64) << 9
        ];*/
        let raw_inputs = [
            id.board_id[0].0,
            id.board_id[1].0,
            id.board_id[2].0,
            id.board_id[3].0,
            id.additional_data as u64
        ];
        let mut sum = 0u64;

        for i in 0..5 {
            sum = sum.wrapping_add(raw_inputs[i].wrapping_mul(PRIMES[i]));
        }

        sum
    }
}

#[derive(Clone, Copy, Eq, PartialEq)]
pub enum ValueBound {
    Exact,
    Lower,
    Upper
}

impl ValueBound {
    pub fn invert(self) -> ValueBound {
        match self {
            ValueBound::Exact => ValueBound::Exact,
            ValueBound::Lower => ValueBound::Upper,
            ValueBound::Upper => ValueBound::Lower
        }
    }
}

#[derive(Clone)]
pub struct TranspositionTableEntry {
    id: PositionId,
    pub depth: u32,
    pub eval: f32,
    pub recommended_move: Move,
    pub bound: ValueBound
}

pub struct TranspositionTable<H: PositionHasher> {
    hasher: H,
    entries: Box<[Option<TranspositionTableEntry>]>,
    mask: usize
}

impl<H: PositionHasher> TranspositionTable<H> {

    pub fn new(bits: u32, hasher: H) -> TranspositionTable<H> {
        let len = 1usize << bits;
        let entries = iter::repeat_with(|| Option::None).take(len).collect();
        let mask = len - 1;

        TranspositionTable {
            hasher,
            entries,
            mask
        }
    }

    pub fn get_entry(&self, id: &PositionId)
            -> Option<&TranspositionTableEntry> {
        let hash = self.hasher.get(id);
        let idx = hash.as_usize() & self.mask;

        self.entries[idx].as_ref().filter(|e| &e.id == id)
    }

    pub fn enter(&mut self, id: PositionId, depth: u32, evaluation: f32, recommended_move: Move, node_type: ValueBound) {
        let hash = self.hasher.get(&id);
        let idx = hash.as_usize() & self.mask;
        let entry = TranspositionTableEntry {
            id,
            depth,
            eval: evaluation,
            recommended_move,
            bound: node_type
        };

        self.entries[idx] = Some(entry);
    }
}
