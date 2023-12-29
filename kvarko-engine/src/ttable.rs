use std::fmt::Debug;
use std::iter;
use std::mem::MaybeUninit;

use kvarko_model::hash::PositionHasher;
use kvarko_model::movement::Move;

use bitvec::bitbox;
use bitvec::boxed::BitBox;

use crate::CHECKMATE_DELTA;
use crate::depth::Depth;

/// A trait for types to be used as position hashes for transposition tables.
pub trait TTableHash : Copy + Clone + Debug + Eq {

    /// Converts the hash into a `usize` index. In case this type is larger
    /// than `usize`, this shall return the least significant bits.
    fn as_usize(self) -> usize;
}

impl TTableHash for u64 {
    fn as_usize(self) -> usize {
        self as usize
    }
}

/// An enumeration of the different bounds on the evaluation a transposition
/// table entry can provide. This depends on the amount and kind of pruning
/// that occurred during its evaluation.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
pub enum ValueBound {

    /// The value provided is a lower bound on the actual value given the
    /// depth. This is the case if the node evaluation was shortcut due to the
    /// beta value being exceeded.
    Lower,

    /// The value provided is an upper bound on the actual value given the
    /// depth. This is the case if no child of the evaluated node managed to
    /// exceed the alpha value, in which case alpha is an upper bound.
    Upper,

    /// The value provided is exact given the depth. This is the case if it
    /// lied between alpha and beta.
    Exact
}

impl ValueBound {

    /// Returns the opposite of this value bound, i.e. [ValueBound::Lower] for
    /// [ValueBound::Upper] and vice versa. [ValueBound::Exact] remains
    /// unchanged.
    pub fn invert(self) -> ValueBound {
        match self {
            ValueBound::Exact => ValueBound::Exact,
            ValueBound::Lower => ValueBound::Upper,
            ValueBound::Upper => ValueBound::Lower
        }
    }
}

/// A trait for replacement policies that can be employed by transposition
/// tables. A replacement policy determines whether a new entry found during
/// evaluation should replace an old one in case a hash collision occurs. The
/// trait is generic over the type of entries used in the table.
pub trait ReplacementPolicy<E> {

    /// Determines whether the given new value should replace the current one
    /// according to this replacement policy. This method is called when a
    /// collision occurs.
    ///
    /// # Arguments
    ///
    /// * `current`: A reference to the entry that is currently in the table.
    /// * `new`: A reference to the entry that may or may not replace the
    /// current one.
    ///
    /// # Returns
    ///
    /// True, if the `new` value should replace the `current` one.
    fn replace(&self, current: &E, new: &E) -> bool;
}

/// A [ReplacementPolicy] that chooses to replace every old value with a new
/// one when a collision occurs.
#[derive(Clone, Copy, Debug)]
pub struct AlwaysReplace;

impl<E> ReplacementPolicy<E> for AlwaysReplace {
    fn replace(&self, _: &E, _: &E) -> bool {
        true
    }
}

/// A [ReplacementPolicy] for [TreeSearchTableEntry]s that favours entries with
/// higher depth and exact bound.
#[derive(Clone, Copy, Debug)]
pub struct DepthAndBound;

impl ReplacementPolicy<TreeSearchTableEntry> for DepthAndBound {
    fn replace(&self, current: &TreeSearchTableEntry,
            new: &TreeSearchTableEntry) -> bool {
        if new.depth > current.depth {
            return true;
        }

        if new.depth < current.depth {
            return false;
        }

        match (new.bound, current.bound) {
            (ValueBound::Exact, _) => true,
            (ValueBound::Upper, ValueBound::Upper) => new.eval <= current.eval,
            (ValueBound::Lower, ValueBound::Lower) => new.eval >= current.eval,
            (ValueBound::Upper, ValueBound::Lower) => new.eval <= -current.eval,
            (ValueBound::Lower, ValueBound::Upper) => new.eval >= -current.eval,
            _ => false
        }
    }
}

/// This trait defines the basic information any kind of transposition table
/// entry should carry.
pub trait TTableEntry {

    /// Gets the evaluation of found from the search. This may also be a lower
    /// or upper bound as determined by [TTableEntry::bound].
    fn eval(&self) -> f32;

    /// Gets the kind [ValueBound] provided in [TTableEntry::eval], that is,
    /// whether it is a exact value or a lower or upper bound.
    fn bound(&self) -> ValueBound;
}

/// A transposition table entry used during ordinary tree search with known
/// search depth.
#[derive(Clone, Copy, Debug)]
pub struct TreeSearchTableEntry {

    /// The search depth starting from the node for which this entry is made.
    pub depth: Depth,

    /// The evaluation found from the search. This may also be a lower or upper
    /// bound as determined by [TreeSearchTableEntry::bound].
    pub eval: f32,

    /// The [Move] that search yielded as optimal.
    pub recommended_move: Move,

    /// The kind [ValueBound] provided in [TreeSearchTableEntry::eval], that
    /// is, whether it is a exact value or a lower or upper bound.
    pub bound: ValueBound
}

impl TreeSearchTableEntry {
    #[inline]
    pub(crate) fn is_forced_checkmate(&self) -> bool {
        match self.bound {
            ValueBound::Lower => self.eval > CHECKMATE_DELTA,
            ValueBound::Upper => self.eval < -CHECKMATE_DELTA,
            ValueBound::Exact => self.eval > CHECKMATE_DELTA || self.eval < -CHECKMATE_DELTA
        }
    }
}

impl TTableEntry for TreeSearchTableEntry {
    fn eval(&self) -> f32 {
        self.eval
    }

    fn bound(&self) -> ValueBound {
        self.bound
    }
}

/// A transposition table entry used in quiescence search. As that is done
/// without tracking an explicit depth and recommended move, these pieces of
/// information are missing.
#[derive(Clone, Copy, Debug)]
pub struct QuiescenceTableEntry {

    /// The evaluation found from the quiescence search. This may also be a
    /// lower or upper bound as determined by [QuiescenceTableEntry::bound].
    pub eval: f32,

    /// The kind [ValueBound] provided in [QuiescenceTableEntry::eval], that
    /// is, whether it is a exact value or a lower or upper bound.
    pub bound: ValueBound
}

impl TTableEntry for QuiescenceTableEntry {
    fn eval(&self) -> f32 {
        self.eval
    }

    fn bound(&self) -> ValueBound {
        self.bound
    }
}

#[derive(Clone)]
#[allow(clippy::type_complexity)]
pub struct TranspositionTable<H, E, R>
where
    H: PositionHasher,
    H::Hash: TTableHash + Copy,
    E: Copy,
    R: ReplacementPolicy<E>
{
    // Sadly, we cannot create a type alias for table cells as that does not
    // allow necessary annotations for the generics.

    entries: Box<[MaybeUninit<(H::Hash, E)>]>,
    control: BitBox,
    mask: usize,
    replacement_policy: R
}

impl<H, E, R> TranspositionTable<H, E, R>
where
    H: PositionHasher,
    H::Hash: TTableHash + Copy,
    E: Copy,
    R: ReplacementPolicy<E>
{
    pub fn new(bits: u32, replacement_policy: R)
            -> TranspositionTable<H, E, R> {
        let len = 1usize << bits;
        let entries = iter::repeat_with(MaybeUninit::uninit).take(len).collect();
        let control = bitbox![0; len];
        let mask = len - 1;

        TranspositionTable {
            entries,
            control,
            mask,
            replacement_policy
        }
    }

    pub fn get_entry(&self, hash: H::Hash) -> Option<&E> {
        let idx = hash.as_usize() & self.mask;

        if self.control[idx] {
            let (entry_hash, entry) = unsafe { self.entries[idx].assume_init_ref() };

            if entry_hash == &hash {
                Some(entry)
            }
            else {
                None
            }
        }
        else {
            None
        }
    }

    pub fn enter(&mut self, hash: H::Hash, new_entry: E) {
        let idx = hash.as_usize() & self.mask;
        let entry = &mut self.entries[idx];

        if self.control[idx] {
            let old_entry = unsafe { &entry.assume_init_ref().1 };

            if !self.replacement_policy.replace(old_entry, &new_entry) {
                return;
            }
        }

        *entry = MaybeUninit::new((hash, new_entry));
        self.control.set(idx, true);
    }
}

impl<H, E, R> TranspositionTable<H, E, R>
where
    H: PositionHasher,
    H::Hash: TTableHash + Copy,
    E: Copy,
    R: ReplacementPolicy<E>,
    E: Clone
{

    /// Removes all entries from the transposition table.
    pub fn clear(&mut self) {
        self.control.fill(false)
    }
}
