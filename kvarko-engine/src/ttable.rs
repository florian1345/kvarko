use kvarko_model::hash::{PositionHasher, ZobristHasher};
use kvarko_model::movement::Move;
use kvarko_model::state::Position;
use rand::distributions::Standard;
use rand::prelude::Distribution;

use std::fmt::Debug;
use std::iter;
use std::ops::BitXorAssign;

pub trait PositionHash : Copy + Clone + Eq {
    fn as_usize(self) -> usize;
}

pub trait TTableHasher : PositionHasher {
    type Hash : PositionHash;

    fn init(position: &Position) -> Self;

    fn hash(&self) -> Self::Hash;
}

impl PositionHash for u64 {
    fn as_usize(self) -> usize {
        self as usize
    }
}

const SEED: [u8; 32] = [
    0xe6, 0x38, 0x9d, 0xa7, 0x85, 0x26, 0xee, 0x45,
    0x00, 0x69, 0x04, 0xfb, 0xf0, 0x81, 0x12, 0x90,
    0xb4, 0x6c, 0x1a, 0x63, 0x08, 0x1d, 0xae, 0xe8,
    0xec, 0x5f, 0xef, 0x75, 0x08, 0x4e, 0x1d, 0x6d
];

impl<H> TTableHasher for ZobristHasher<H>
where
    H: PositionHash + BitXorAssign + Debug + Default,
    Standard: Distribution<H>
{
    type Hash = H;

    fn init(position: &Position) -> Self {
        ZobristHasher::new(SEED.clone(), position)
    }

    fn hash(&self) -> H {
        self.current_hash()
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
pub struct TranspositionTableEntry<H> {
    hash: H,
    pub depth: u32,
    pub eval: f32,
    pub recommended_move: Move,
    pub bound: ValueBound
}

pub struct TranspositionTable<H: TTableHasher> {
    hasher: H,
    entries: Box<[Option<TranspositionTableEntry<H::Hash>>]>,
    mask: usize
}

impl<H: TTableHasher> TranspositionTable<H> {

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

    pub fn get_entry(&self)
            -> Option<&TranspositionTableEntry<H::Hash>> {
        let hash = self.hasher.hash();
        let idx = hash.as_usize() & self.mask;

        self.entries[idx].as_ref().filter(|e| e.hash == hash)
    }

    pub fn enter(&mut self, depth: u32, evaluation: f32, recommended_move: Move, node_type: ValueBound) {
        let hash = self.hasher.hash();
        let idx = hash.as_usize() & self.mask;
        let entry = &mut self.entries[idx];

        if let Some(entry) = entry {
            if entry.depth > depth {
                return;
            }
        }

        *entry = Some(TranspositionTableEntry {
            hash,
            depth,
            eval: evaluation,
            recommended_move,
            bound: node_type
        });
    }

    pub fn hasher_mut(&mut self) -> &mut H {
        &mut self.hasher
    }
}
