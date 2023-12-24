use std::cmp::Ordering;
use std::iter;
use std::time::Duration;
use base_evaluator::BaseEvaluator;

use kvarko_model::game::Controller;
use kvarko_model::hash::PositionHasher;
use kvarko_model::movement::{self, Move, MoveProcessor};
use kvarko_model::piece::Piece;
use kvarko_model::state::{Position, State};
use crate::base_evaluator::KvarkoBaseEvaluator;

use crate::book::OpeningBook;
use crate::depth::{Depth, DepthStrategy, IterativeDeepeningForDuration};
use crate::sort::{CapturePromotionValuePresorter, Presorter};
use crate::ttable::{
    AlwaysReplace,
    DepthAndBound,
    QuiescenceTableEntry,
    TranspositionTable,
    TreeSearchTableEntry,
    TTableEntry,
    TTableHash,
    ValueBound
};

pub mod base_evaluator;
pub mod book;
pub mod depth;
pub mod ordering;
pub mod sort;
pub mod ttable;

#[derive(PartialEq)]
struct OrdF32(f32);

impl Eq for OrdF32 { }

impl PartialOrd for OrdF32 {
    fn partial_cmp(&self, other: &OrdF32) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for OrdF32 {
    fn cmp(&self, other: &OrdF32) -> Ordering {
        self.0.partial_cmp(&other.0).unwrap()
    }
}

/// The output given by a [StateEvaluator] on evaluation of a state.
pub struct StateEvaluatorOutput<M> {

    /// The evaluation of the position according to the evaluator.
    pub evaluation: f32,

    /// The move which the evaluator determined to be best.
    pub recommended_move: Move,

    /// Any metadata defined by the [StateEvaluator::Metadata].
    pub metadata: M
}

/// A trait for types which can give an evaluation for a game [State], that is,
/// a number representing how good the state is for the player whose turn it
/// is.
pub trait StateEvaluator<H: PositionHasher> {

    /// Metadata provided by the state evaluator, for diagnostics or similar
    /// purposes.
    type Metadata;

    /// Provides an evaluation for the given state from the player's
    /// perspective whose turn it currently is.
    ///
    /// # Arguments
    ///
    /// * `state`: A mutable reference to the current game [State]. This also
    /// contains information about the player whose turn it is. Must be left in
    /// the same state as before the method call.
    ///
    /// # Returns
    ///
    /// The [StateEvaluatorOutput] which contains the evaluation, recommended
    /// move, and any evaluator-specific metadata defined by the
    /// [StateEvaluator::Metadata] type.
    fn evaluate_state(&mut self, state: &mut State<H>)
        -> StateEvaluatorOutput<Self::Metadata>;
}

const CHECKMATE_DELTA: f32 = 1_000_000.0;

pub trait ListMovesIn {
    fn list_moves_in(&self, position: &Position, moves: &mut Vec<Move>)
        -> (bool, usize);
}

#[derive(Clone)]
pub struct ListAllMovesIn;

impl ListMovesIn for ListAllMovesIn {
    fn list_moves_in(&self, position: &Position, moves: &mut Vec<Move>)
            -> (bool, usize) {
        let check = movement::list_moves_in(position, moves);
        (check, moves.len())
    }
}

#[derive(Clone)]
pub struct ListNonPawnCapturesIn;

impl ListMovesIn for ListNonPawnCapturesIn {
    fn list_moves_in(&self, position: &Position, moves: &mut Vec<Move>)
            -> (bool, usize) {
        struct NonPawnCapturesLister<'a> {
            moves: &'a mut Vec<Move>,
            count: usize
        }

        impl<'a> MoveProcessor for NonPawnCapturesLister<'a> {
            fn process(&mut self, mov: Move) {
                self.count += 1;

                match &mov {
                    Move::Ordinary { captured, .. }
                            | Move::Promotion { captured, .. } => {
                        if captured.iter().any(|&captured| captured != Piece::Pawn) {
                            self.moves.push(mov);
                        }
                    },
                    _ => { }
                }
            }
        }

        let mut processor = NonPawnCapturesLister {
            moves,
            count: 0
        };
        let check = movement::process_moves(position, &mut processor);

        (check, processor.count)
    }
}

// More than 14 to account for possible promotions.
const QUIESCENSE_BUFFER_COUNT: usize = 30;

/// Applies the information stored in `entry` to the given alpha and beta
/// bounds. If an early return is possible, `true` is returned.
fn should_use_ttable_entry<E>(alpha: &mut f32, beta: &mut f32,
    entry: &E) -> bool
where
    E: TTableEntry
{
    match entry.bound() {
        ValueBound::Exact => {
            true
        },
        ValueBound::Lower => {
            if entry.eval() >= *beta {
                true
            }
            else {
                *alpha = alpha.max(entry.eval());
                false
            }
        },
        ValueBound::Upper => {
            if entry.eval() <= *alpha {
                true
            }
            else {
                *beta = beta.min(entry.eval());
                false
            }
        }
    }
}

#[inline]
fn apply_penalty_for_extra_move_if_checkmate(value: &mut f32) {
    if *value > CHECKMATE_DELTA {
        *value -= CHECKMATE_DELTA;
    }
    else if *value < -CHECKMATE_DELTA {
        *value += CHECKMATE_DELTA;
    }
}

#[inline]
fn determine_bound(max: f32, alpha: f32, beta: f32) -> ValueBound {
    if max >= beta {
        ValueBound::Lower
    }
    else if max > alpha {
        ValueBound::Exact
    }
    else {
        ValueBound::Upper
    }
}

/// A [BaseEvaluator] which does quiescense search on all moves provided by
/// some [ListMovesIn] implementation. This searches the full tree, without any
/// maximum depth. Alpha-beta-pruning is still applied.
#[derive(Clone)]
pub struct QuiescenseTreeSearchEvaluator<H, E, L, S>
where
    H: PositionHasher,
    H::Hash: TTableHash
{
    base_evaluator: E,
    list_moves_in: L,
    bufs: Vec<Vec<Move>>,
    transposition_table:
        TranspositionTable<H, QuiescenceTableEntry, AlwaysReplace>,
    presorter: S
}

impl<H, E, L, S> QuiescenseTreeSearchEvaluator<H, E, L, S>
where
    H: PositionHasher,
    H::Hash: TTableHash
{
    pub fn new(base_evaluator: E, list_moves_in: L, presorter: S,
            ttable_bits: u32)
            -> QuiescenseTreeSearchEvaluator<H, E, L, S> {
        QuiescenseTreeSearchEvaluator {
            base_evaluator,
            list_moves_in,
            bufs: iter::repeat_with(Vec::new)
                .take(QUIESCENSE_BUFFER_COUNT)
                .collect(),
            transposition_table:
                TranspositionTable::new(ttable_bits, AlwaysReplace),
            presorter
        }
    }
}

impl<H, E, L, S> QuiescenseTreeSearchEvaluator<H, E, L, S>
where
    H: PositionHasher,
    H::Hash: TTableHash,
    E: BaseEvaluator<H>,
    L: ListMovesIn,
    S: Presorter
{
    fn evaluate_rec(&mut self, state: &mut State<H>, mut alpha: f32,
            mut beta: f32) -> f32 {
        let entry = self.transposition_table.get_entry(state.position_hash());

        if let Some(entry) = entry {
            if should_use_ttable_entry(&mut alpha, &mut beta, entry) {
                return entry.eval;
            }
        }

        // TODO reduce code duplication

        let mut moves = self.bufs.pop().unwrap();
        moves.clear();
        let (check, move_count) =
            self.list_moves_in.list_moves_in(state.position(), &mut moves);
        self.presorter.pre_sort(&mut moves, state.position());

        // Actor can stop trading now, if they want.

        let mut max = self.base_evaluator.evaluate_state_with_precomputed_data(
            state, alpha, beta, move_count, check);
        alpha = alpha.max(max);

        for mov in &moves {
            if alpha >= beta {
                break;
            }

            let revert_info = state.make_move(mov);
            let value = -self.evaluate_rec(state, -beta, -alpha);
            state.unmake_move(mov, revert_info);

            if value > max {
                max = value;
                alpha = alpha.max(max);
            }
        }

        self.transposition_table.enter(
            state.position_hash(), QuiescenceTableEntry {
                eval: max,
                bound: determine_bound(max, alpha, beta)
            });
        self.bufs.push(moves);

        max
    }
}

impl<H, E, L, S> BaseEvaluator<H> for QuiescenseTreeSearchEvaluator<H, E, L, S>
where
    H: PositionHasher,
    H::Hash: TTableHash,
    E: BaseEvaluator<H>,
    L: ListMovesIn,
    S: Presorter
{
    fn evaluate_state(&mut self, state: &mut State<H>, alpha: f32, beta: f32)
            -> f32 {
        self.evaluate_rec(state, alpha, beta)
    }

    fn evaluate_state_with_precomputed_data(&mut self, state: &mut State<H>,
            alpha: f32, beta: f32, _: usize, _: bool) -> f32 {
        self.evaluate_state(state, alpha, beta)
    }
}

#[inline]
fn presort_moves(presorter: &mut impl Presorter, moves: &mut [Move],
        position: &Position, ttable_entry: Option<&TreeSearchTableEntry>) {
    if let Some(entry) = ttable_entry {
        let recommended_idx = moves.iter().enumerate()
            .find(|(_, m)| *m == &entry.recommended_move)
            .unwrap().0;
        moves.swap(0, recommended_idx);
        presorter.pre_sort(&mut moves[1..], position);
    } else {
        presorter.pre_sort(moves, position);
    }
}

/// A [StateEvaluator] that does a negimax tree search on the input state,
/// using alpha-beta-pruning.
#[derive(Clone)]
pub struct TreeSearchEvaluator<H, E, S, D>
where
    H: PositionHasher,
    H::Hash: TTableHash
{
    pub base_evaluator: E,
    pub presorter: S,
    pub depth_strategy: D,
    pub ttable: TranspositionTable<H, TreeSearchTableEntry, DepthAndBound>
}

impl<H, E, S, D> TreeSearchEvaluator<H, E, S, D>
where
    H: PositionHasher,
    H::Hash: TTableHash
{
    pub fn new(base_evaluator: E, presorter: S, depth_strategy: D,
            ttable_bits: u32) -> TreeSearchEvaluator<H, E, S, D> {
        TreeSearchEvaluator {
            base_evaluator,
            presorter,
            depth_strategy,
            ttable: TranspositionTable::new(ttable_bits, DepthAndBound)
        }
    }
}

impl<H, E, S, D> TreeSearchEvaluator<H, E, S, D>
where
    H: PositionHasher,
    H::Hash: TTableHash,
    E: BaseEvaluator<H>,
    S: Presorter
{
    fn evaluate_rec(&mut self, state: &mut State<H>, bufs: &mut [Vec<Move>],
            mut alpha: f32, mut beta: f32) -> (f32, Option<Move>) {
        let depth = bufs.len() as u32;

        if depth == 0 {
            let evaluation =
                self.base_evaluator.evaluate_state(state, alpha, beta);

            return (evaluation, None);
        }

        if state.is_stateful_draw() {
            // Checkmate is covered later
            return (0.0, None);
        }

        let position_hash = state.position_hash();
        let ttable_entry = self.ttable.get_entry(position_hash);

        if let Some(entry) = ttable_entry {
            if entry.depth == depth && should_use_ttable_entry(&mut alpha, &mut beta, entry) {
                let mov = entry.recommended_move;
                return (entry.eval, Some(mov))
            }
        }

        let position = state.position();
        let (moves, bufs_rest) = bufs.split_first_mut().unwrap();
        moves.clear();
        let check = movement::list_moves_in(position, moves);

        if moves.is_empty() {
            return (base_evaluator::evaluate_if_no_moves_remain(check), None);
        }

        presort_moves(&mut self.presorter, moves, position, ttable_entry);

        let mut max = f32::NEG_INFINITY;
        let mut max_move = None;

        for mov in moves {
            let revert_info = state.make_move(mov);
            let (rec_value, _) =
                self.evaluate_rec(state, bufs_rest, -beta, -alpha);
            let mut value = -rec_value;
            state.unmake_move(mov, revert_info);

            apply_penalty_for_extra_move_if_checkmate(&mut value);

            if value > max {
                max = value;
                max_move = Some(mov);
                alpha = alpha.max(max);

                if alpha >= beta {
                    break;
                }
            }
        }

        let max_move = max_move.cloned().unwrap();
        self.ttable.enter(
            position_hash, TreeSearchTableEntry {
                depth,
                eval: max,
                recommended_move: max_move,
                bound: determine_bound(max, alpha, beta)
            });

        (max, Some(max_move))
    }
}

/// Metadata provided by the [TreeSearchEvaluator].
pub struct TreeSearchEvaluatorMetadata {

    /// The ply-depth to which was searched. A depth of 0 means all moves were
    pub depth: Depth
}

fn get_mut_slice_of_len<T: Default>(vec: &mut Vec<T>, len: usize) -> &mut [T] {
    while vec.len() < len {
        vec.push(T::default());
    }

    &mut vec[..len]
}

impl<H, E, S, D> StateEvaluator<H> for TreeSearchEvaluator<H, E, S, D>
where
    H: PositionHasher,
    H::Hash: TTableHash,
    E: BaseEvaluator<H>,
    S: Presorter,
    D: DepthStrategy
{
    type Metadata = TreeSearchEvaluatorMetadata;

    fn evaluate_state(&mut self, state: &mut State<H>)
            -> StateEvaluatorOutput<TreeSearchEvaluatorMetadata> {
        let mut bufs = vec![];
        self.ttable.clear();
        let mut value = 0.0;
        let mut mov = None;
        let mut max_depth = 0;

        for depth in self.depth_strategy.depth_iterator() {
            max_depth = max_depth.max(depth);
            let bufs = get_mut_slice_of_len(&mut bufs, depth as usize);
            (value, mov) = self.evaluate_rec(
                state, bufs, f32::NEG_INFINITY, f32::INFINITY);
        }

        StateEvaluatorOutput {
            evaluation: value,
            recommended_move: mov.unwrap(),
            metadata: TreeSearchEvaluatorMetadata {
                depth: max_depth
            }
        }
    }
}

/// A wrapper around a [StateEvaluator] that implements [Controller] by playing
/// the recommended move, if one is present, and otherwise checks which move
/// would make the underlying state evaluator return the worst evaluation for
/// the opponent.
#[derive(Clone)]
pub struct StateEvaluatingController<E>(pub E);

impl<H, E> StateEvaluator<H> for StateEvaluatingController<E>
where
    H: PositionHasher,
    E: StateEvaluator<H>
{
    type Metadata = E::Metadata;

    fn evaluate_state(&mut self, state: &mut State<H>)
            -> StateEvaluatorOutput<E::Metadata> {
        self.0.evaluate_state(state)
    }
}

impl<H, E> Controller<H> for StateEvaluatingController<E>
where
    H: PositionHasher + Clone,
    E: StateEvaluator<H>
{
    fn make_move(&mut self, state: &State<H>) -> Move {
        let mut state = state.clone();

        self.0.evaluate_state(&mut state).recommended_move
    }
}

type KvarkoEvaluator<H, D> = TreeSearchEvaluator<
    H,
    QuiescenseTreeSearchEvaluator<
        H,
        KvarkoBaseEvaluator,
        ListNonPawnCapturesIn,
        CapturePromotionValuePresorter
    >,
    CapturePromotionValuePresorter,
    D>;

/// Metadata provided by the [KvarkoEngine].
pub enum KvarkoEngineMetadata {

    /// Indicates that the evaluated state was in the opening book and a book
    /// move has been selected.
    BookMove,

    /// Indicates that the evaluated state was not in the opening book and a
    /// move has been computed using tree search. The metadata of the tree
    /// search is returned.
    ComputedMove(TreeSearchEvaluatorMetadata)
}

/// A [StateEvaluator] that represents the totality of functionality contained
/// in the Kvarko engine. In particular, this uses a [TreeSearchEvaluator]
/// followed by a [QuiescenseTreeSearchEvaluator] which uses the
/// [KvarkoBaseEvaluator] for evaluation of base states. In addition, an
/// [OpeningBook] may be provided.
/// 
/// Construct this engine using [kvarko_engine].
#[derive(Clone)]
pub struct KvarkoEngine<H, D>
where
    H: PositionHasher,
    H::Hash: TTableHash
{
    pub opening_book: Option<OpeningBook>,
    pub evaluator: KvarkoEvaluator<H, D>
}

impl<H, D> StateEvaluator<H> for KvarkoEngine<H, D>
where
    H: PositionHasher,
    H::Hash: TTableHash,
    D: DepthStrategy
{
    type Metadata = KvarkoEngineMetadata;

    fn evaluate_state(&mut self, state: &mut State<H>)
            -> StateEvaluatorOutput<KvarkoEngineMetadata> {
        if let Some(opening_book) = &self.opening_book {
            if let Some(value) = opening_book.get_value(state) {
                let best_move = opening_book.get_best_move(state).unwrap();

                return StateEvaluatorOutput {
                    evaluation: value,
                    recommended_move: *best_move,
                    metadata: KvarkoEngineMetadata::BookMove
                };
            }
        }

        let tree_search_output = self.evaluator.evaluate_state(state);

        StateEvaluatorOutput {
            evaluation: tree_search_output.evaluation,
            recommended_move: tree_search_output.recommended_move,
            metadata:
                KvarkoEngineMetadata::ComputedMove(tree_search_output.metadata)
        }
    }
}

/// Constructs a [KvarkoEngine].
///
/// # Arguments
///
/// * `deepen_for`: If search at some depth is finished within this duration, a
/// search of a depth one higher is started. The new search is always awaited,
/// so this is not an upper bound in any way.
/// * `opening_book`: Optionally, specifies an [OpeningBook] for the engine to
/// use.
///
/// # Returns
///
/// A [StateEvaluatingController] wrapped around a [KvarkoEngine] with the
/// given parameters.
pub fn kvarko_engine<H>(deepen_for: Duration, opening_book: Option<OpeningBook>)
    -> StateEvaluatingController<KvarkoEngine<H, IterativeDeepeningForDuration>>
where
    H: PositionHasher,
    H::Hash: TTableHash
{
    kvarko_engine_with_ttable_bits(deepen_for, opening_book, 22, 16)
}

/// Constructs a [KvarkoEngine] with given transposition table sizes.
///
/// # Arguments
///
/// * `deepen_for`: If search at some depth is finished within this duration, a
/// search of a depth one higher is started. The new search is always awaited,
/// so this is not an upper bound in any way.
/// * `opening_book`: Optionally, specifies an [OpeningBook] for the engine to
/// use.
/// * `tree_search_ttable_bits`: The number of significant bits used for
/// indexing entries in the transposition table used by ordinary tree search.
/// * `quiescence_search_ttable_bits`: The number of significant bits used for
/// indexing entries in the transposition table used by quiescence search.
///
/// # Returns
///
/// A [StateEvaluatingController] wrapped around a [KvarkoEngine] with the
/// given parameters.
pub fn kvarko_engine_with_ttable_bits<H>(deepen_for: Duration,
    opening_book: Option<OpeningBook>, tree_search_ttable_bits: u32,
    quiescence_search_ttable_bits: u32)
    -> StateEvaluatingController<KvarkoEngine<H, IterativeDeepeningForDuration>>
where
    H: PositionHasher,
    H::Hash: TTableHash
{
    let depth_strategy = IterativeDeepeningForDuration {
        deepen_for
    };

    kvarko_engine_with_ttable_bits_and_depth_strategy(depth_strategy,
        opening_book, tree_search_ttable_bits, quiescence_search_ttable_bits)
}

pub fn kvarko_engine_with_ttable_bits_and_depth_strategy<H, D>(depth_strategy: D,
    opening_book: Option<OpeningBook>, tree_search_ttable_bits: u32,
    quiescence_search_ttable_bits: u32)
    -> StateEvaluatingController<KvarkoEngine<H, D>>
where
    H: PositionHasher,
    H::Hash: TTableHash
{
    StateEvaluatingController(KvarkoEngine {
        opening_book,
        evaluator: TreeSearchEvaluator::new(
            QuiescenseTreeSearchEvaluator::new(
                KvarkoBaseEvaluator::default(),
                ListNonPawnCapturesIn,
                CapturePromotionValuePresorter::new(),
                quiescence_search_ttable_bits
            ),
            CapturePromotionValuePresorter::new(),
            depth_strategy,
            tree_search_ttable_bits
        )
    })
}
