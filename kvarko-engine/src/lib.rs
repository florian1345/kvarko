use std::cmp::Ordering;
use std::iter;
use std::time::{Duration, Instant};

use kvarko_model::board::Bitboard;
use kvarko_model::game::Controller;
use kvarko_model::hash::PositionHasher;
use kvarko_model::movement::{self, Move, MoveProcessor};
use kvarko_model::piece::Piece;
use kvarko_model::player::Player;
use kvarko_model::state::{Position, State};

use crate::book::OpeningBook;
use crate::sort::{CaptureValuePresorter, Presorter};
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

pub mod book;
pub mod ordering;
pub mod sort;
pub mod ttable;

#[derive(PartialEq)]
struct OrdF32(f32);

impl Eq for OrdF32 { }

impl PartialOrd for OrdF32 {
    fn partial_cmp(&self, other: &OrdF32) -> Option<Ordering> {
        self.0.partial_cmp(&other.0)
    }
}

impl Ord for OrdF32 {
    fn cmp(&self, other: &OrdF32) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

/// A trait for types which can give an evaluation for a game [State], that is,
/// a number representing how good the state is for the player whose turn it
/// is.
pub trait StateEvaluator<H: PositionHasher> {

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
    /// As a first return parameter, this function returns an evaluation of the
    /// current position, where negative numbers are more probably defeats than
    /// victories and positive numbers are more probably victories than
    /// defeats. The optional second return parameter contains a recommended
    /// move.
    fn evaluate_state(&mut self, state: &mut State<H>) -> (f32, Option<Move>);
}

/// Similar to [StateEvaluator], however accepts additional parameters that are
/// provided by the [TreeSearchEvaluator] or [QuiescenseTreeSearchEvaluator],
/// which can be used to improve performance.
pub trait BaseEvaluator<H: PositionHasher> {

    /// Provides an evaluation for the given state from the player's
    /// perspective whose turn it currently is. Consider calling
    /// [BaseEvaluator::evaluate_state_with_precomputed_data] if you have the
    /// required parameters at hand, in order to improve performance.
    ///
    /// # Arguments
    ///
    /// * `state`: A mutable reference to the current game [State]. This also
    /// contains information about the player whose turn it is. Must be left in
    /// the same state as before the method call.
    /// * `alpha`: The current alpha parameter from alpha-beta-pruning.
    /// * `beta`: The current beta parameter from alpha-beta-pruning.
    ///
    /// # Returns
    ///
    /// As a first return parameter, this function returns an evaluation of the
    /// current position, where negative numbers are more probably defeats than
    /// victories and positive numbers are more probably victories than
    /// defeats.
    fn evaluate_state(&mut self, state: &mut State<H>, alpha: f32, beta: f32)
            -> f32 {
        let (moves, check) = movement::count_moves(state.position());

        self.evaluate_state_with_precomputed_data(
            state, alpha, beta, moves, check)
    }

    /// Provides an evaluation for the given state from the player's
    /// perspective whose turn it currently is. This function is called with
    /// additional data about the state which does not need to be recomputed.
    /// If you do not have this data available, call
    /// [BaseEvaluator::evaluate_state] instead.
    ///
    /// # Arguments
    ///
    /// * `state`: A mutable reference to the current game [State]. This also
    /// contains information about the player whose turn it is. Must be left in
    /// the same state as before the method call.
    /// * `alpha`: The current alpha parameter from alpha-beta-pruning.
    /// * `beta`: The current beta parameter from alpha-beta-pruning.
    /// * `moves`: The number of available moves for the player whose turn it
    /// is.
    /// * `check`: `true`, if and only if the player whose turn it is is
    /// currently in check.
    ///
    /// # Returns
    ///
    /// As a first return parameter, this function returns an evaluation of the
    /// current position, where negative numbers are more probably defeats than
    /// victories and positive numbers are more probably victories than
    /// defeats.
    fn evaluate_state_with_precomputed_data(&mut self, state: &mut State<H>,
        alpha: f32, beta: f32, move_count: usize, check: bool) -> f32;
}

const CHECKMATE_DELTA: f32 = 1_000_000.0;
const CHECKMATE_VALUE: f32 = 1_000_000_000.0;

const DEFAULT_MATERIAL_VALUES: [f32; 6] = [
    1.0,
    3.0,
    3.25,
    5.0,
    9.0,
    10.0
];

const DEFAULT_MOVE_VALUE: f32 = 0.05;
const DEFAULT_DOUBLED_PAWN_PENALTY: f32 = 0.25;
const DEFAULT_PAWN_SIXTH_RANK_VALUE: f32 = 0.1;
const DEFAULT_PAWN_SEVENTH_RANK_VALUE: f32 = 0.3;

const FILES: [Bitboard; 8] = [
    Bitboard(0x0101010101010101),
    Bitboard(0x0202020202020202),
    Bitboard(0x0404040404040404),
    Bitboard(0x0808080808080808),
    Bitboard(0x1010101010101010),
    Bitboard(0x2020202020202020),
    Bitboard(0x4040404040404040),
    Bitboard(0x8080808080808080)
];

const WHITE_SIXTH_RANK: Bitboard = Bitboard(0x0000ff0000000000);
const WHITE_SEVENTH_RANK: Bitboard = Bitboard(0x00ff000000000000);
const BLACK_SIXTH_RANK: Bitboard = Bitboard(0x0000000000ff0000);
const BLACK_SEVENTH_RANK: Bitboard = Bitboard(0x000000000000ff00);

const RELEVANT_PIECES: [Piece; 5] = [
    Piece::Pawn,
    Piece::Knight,
    Piece::Bishop,
    Piece::Rook,
    Piece::Queen
];

/// A [BaseEvaluator] that does no more tree search and gives a value estimate
/// for a given position.
#[derive(Clone)]
pub struct KvarkoBaseEvaluator {
    values: [f32; 6],
    move_value: f32,
    doubled_pawn_penalty: f32,
    pawn_sixth_rank_value: f32,
    pawn_seventh_rank_value: f32
}

impl KvarkoBaseEvaluator {

    #[inline]
    fn evaluate_pawn_ranks(&self, player: Player, pawns: Bitboard) -> f32 {
        let sixth_rank_pawns;
        let seventh_rank_pawns;

        match player {
            Player::White => {
                sixth_rank_pawns = (WHITE_SIXTH_RANK & pawns).len();
                seventh_rank_pawns = (WHITE_SEVENTH_RANK & pawns).len();
            },
            Player::Black => {
                sixth_rank_pawns = (BLACK_SIXTH_RANK & pawns).len();
                seventh_rank_pawns = (BLACK_SEVENTH_RANK & pawns).len();
            }
        }

        sixth_rank_pawns as f32 * self.pawn_sixth_rank_value +
            seventh_rank_pawns as f32 * self.pawn_seventh_rank_value
    }
}

impl Default for KvarkoBaseEvaluator {

    fn default() -> KvarkoBaseEvaluator {
        KvarkoBaseEvaluator {
            values: DEFAULT_MATERIAL_VALUES,
            move_value: DEFAULT_MOVE_VALUE,
            doubled_pawn_penalty: DEFAULT_DOUBLED_PAWN_PENALTY,
            pawn_sixth_rank_value: DEFAULT_PAWN_SIXTH_RANK_VALUE,
            pawn_seventh_rank_value: DEFAULT_PAWN_SEVENTH_RANK_VALUE
        }
    }
}

#[inline]
fn evaluate_if_no_moves_remain(check: bool) -> f32 {
    if check {
        -CHECKMATE_VALUE
    } else {
        0.0
    }
}

impl<H: PositionHasher> BaseEvaluator<H> for KvarkoBaseEvaluator {

    fn evaluate_state_with_precomputed_data(&mut self, state: &mut State<H>,
            _: f32, _: f32, move_count: usize, check: bool) -> f32 {
        if state.is_stateful_draw() {
            return 0.0;
        }

        let turn = state.position().turn();

        if move_count == 0 {
            return evaluate_if_no_moves_remain(check)
        }

        let opponent = turn.opponent();
        let opponent_moves = {
            let mut position = state.position().clone();
            position.set_turn(opponent);
            movement::count_moves(&position).0
        };
        let board = state.position().board();
        let mut value = (move_count as f32 - opponent_moves as f32) *
            self.move_value;

        for piece in RELEVANT_PIECES {
            let piece_value = self.values[piece as usize];

            value += piece_value *
                board.of_player_and_kind(turn, piece).len() as f32;
            value -= piece_value *
                board.of_player_and_kind(opponent, piece).len() as f32;
        }

        let own_pawns = board.of_player_and_kind(turn, Piece::Pawn);
        let opponent_pawns = board.of_player_and_kind(opponent, Piece::Pawn);

        for file in FILES {
            let own_pawns = (own_pawns & file).len().saturating_sub(1);
            value -= self.doubled_pawn_penalty * own_pawns as f32;

            let opponent_pawns = (opponent_pawns & file).len().saturating_sub(1);
            value += self.doubled_pawn_penalty * opponent_pawns as f32;
        }

        value += self.evaluate_pawn_ranks(turn, own_pawns);
        value -= self.evaluate_pawn_ranks(turn, opponent_pawns);

        value
    }
}

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
            mut beta: f32) -> (f32, ValueBound) {
        let entry = self.transposition_table.get_entry(state.position_hash());

        if let Some(entry) = entry {
            if should_use_ttable_entry(&mut alpha, &mut beta, entry) {
                return (entry.eval, entry.bound);
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
        let mut bound = ValueBound::Exact;

        for mov in &moves {
            let revert_info = state.make_move(mov);
            let (value, rec_bound) =
                self.evaluate_rec(state, -beta, -alpha);
            let value = -value;
            state.unmake_move(mov, revert_info);

            if value > max {
                max = value;
                bound = rec_bound.invert();
                alpha = alpha.max(max);
            }

            if alpha >= beta {
                bound = ValueBound::Lower;
                break;
            }
        }

        self.transposition_table.enter(
            state.position_hash(), QuiescenceTableEntry {
                eval: max,
                bound
            });
        self.bufs.push(moves);

        (max, bound)
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
        self.evaluate_rec(state, alpha, beta).0
    }

    fn evaluate_state_with_precomputed_data(&mut self, state: &mut State<H>,
            alpha: f32, beta: f32, _: usize, _: bool) -> f32 {
        self.evaluate_state(state, alpha, beta)
    }
}

/// A [StateEvaluator] that does a negimax tree search on the input state,
/// using alpha-beta-pruning.
#[derive(Clone)]
pub struct TreeSearchEvaluator<H, E, S>
where
    H: PositionHasher,
    H::Hash: TTableHash
{
    base_evaluator: E,
    presorter: S,
    deepen_for: Duration,
    ttable: TranspositionTable<H, TreeSearchTableEntry, DepthAndBound>
}

impl<H, E, S> TreeSearchEvaluator<H, E, S>
where
    H: PositionHasher,
    H::Hash: TTableHash
{
    pub fn new(base_evaluator: E, presorter: S, max_elapsed_time_for_deepening: Duration,
            ttable_bits: u32) -> TreeSearchEvaluator<H, E, S> {
        TreeSearchEvaluator {
            base_evaluator,
            presorter,
            deepen_for: max_elapsed_time_for_deepening,
            ttable: TranspositionTable::new(ttable_bits, DepthAndBound)
        }
    }
}

impl<H, E, S> TreeSearchEvaluator<H, E, S>
where
    H: PositionHasher,
    H::Hash: TTableHash,
    E: BaseEvaluator<H>,
    S: Presorter
{
    fn evaluate_rec(&mut self, state: &mut State<H>, bufs: &mut [Vec<Move>],
            mut alpha: f32, mut beta: f32) -> (f32, Option<Move>, ValueBound) {
        let depth = bufs.len() as u32;

        if depth == 1 {
            let evaluation =
                self.base_evaluator.evaluate_state(state, alpha, beta);

            return (evaluation, None, ValueBound::Exact);
        }

        if state.is_stateful_draw() {
            // Checkmate is covered later
            (0.0, None, ValueBound::Exact)
        }
        else {
            let entry = self.ttable.get_entry(state.position_hash());

            if let Some(entry) = entry {
                if entry.depth == depth && should_use_ttable_entry(&mut alpha, &mut beta, entry) {
                    let mov = entry.recommended_move;
                    return (entry.eval, Some(mov), entry.bound)
                }
            }

            let (moves, bufs_rest) = bufs.split_first_mut().unwrap();
            moves.clear();
            let check = movement::list_moves_in(state.position(), moves);

            if moves.is_empty() {
                return (evaluate_if_no_moves_remain(check), None, ValueBound::Exact);
            }

            self.presorter.pre_sort(moves, state.position());

            if let Some(entry) = entry {
                let recommended_idx = moves.iter().enumerate()
                    .find(|(_, m)| *m == &entry.recommended_move)
                    .unwrap().0;
                moves.swap(0, recommended_idx);
            }

            let mut max = f32::NEG_INFINITY;
            let mut max_move = None;
            let mut bound = ValueBound::Exact;

            for mov in moves {
                let revert_info = state.make_move(mov);
                let (rec_value, _, rec_bound) =
                    self.evaluate_rec(state, bufs_rest, -beta, -alpha);
                let mut value = -rec_value;
                state.unmake_move(mov, revert_info);

                apply_penalty_for_extra_move_if_checkmate(&mut value);

                if value > max {
                    max = value;
                    max_move = Some(mov);
                    bound = rec_bound.invert();
                    alpha = alpha.max(max);
                }

                if alpha >= beta {
                    bound = ValueBound::Lower;
                    break;
                }
            }

            let max_move = max_move.cloned().unwrap();
            self.ttable.enter(
                state.position_hash(), TreeSearchTableEntry {
                    depth,
                    eval: max,
                    recommended_move: max_move,
                    bound
                });

            (max, Some(max_move), bound)
        }
    }
}

impl<H, E, S> StateEvaluator<H> for TreeSearchEvaluator<H, E, S>
where
    H: PositionHasher,
    H::Hash: TTableHash,
    E: BaseEvaluator<H>,
    S: Presorter
{
    fn evaluate_state(&mut self, state: &mut State<H>) -> (f32, Option<Move>) {
        let mut bufs = vec![Vec::new()];
        self.ttable.clear();
        let mut value = 0.0;
        let mut mov = None;
        let before = Instant::now();

        while (Instant::now() - before) < self.deepen_for {
            (value, mov, _) = self.evaluate_rec(
                state, &mut bufs, f32::NEG_INFINITY, f32::INFINITY);
            bufs.push(Vec::new());
        }

        println!("depth: {}", bufs.len() - 1);

        (value, mov)
    }
}

/// A wrapper around a [StateEvaluator] that implements [Controller] by playing
/// the recommended move, if one is present, and otherwise checks which move
/// would make the underlying state evaluator return the worst evaluation for
/// the opponent.
#[derive(Clone)]
pub struct StateEvaluatingController<E>(E);

impl<H, E> StateEvaluator<H> for StateEvaluatingController<E>
where
    H: PositionHasher,
    E: StateEvaluator<H>
{
    fn evaluate_state(&mut self, state: &mut State<H>)
            -> (f32, Option<Move>) {
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

        if let Some(mov) = self.0.evaluate_state(&mut state).1 {
            return mov;
        }

        movement::list_moves(state.position()).0.into_iter()
            .max_by_key(|mov| {
                let mut state = state.clone();
                state.make_move(mov);
                OrdF32(-self.0.evaluate_state(&mut state).0)
            })
            .unwrap()
    }
}

type KvarkoEvaluator<H> = TreeSearchEvaluator<
    H,
    QuiescenseTreeSearchEvaluator<
        H,
        KvarkoBaseEvaluator,
        ListNonPawnCapturesIn,
        CaptureValuePresorter
    >,
    CaptureValuePresorter>;

/// A [StateEvaluator] that represents the totality of functionality contained
/// in the Kvarko engine. In particular, this uses a [TreeSearchEvaluator]
/// followed by a [QuiescenseTreeSearchEvaluator] which uses the
/// [KvarkoBaseEvaluator] for evaluation of base states. In addition, an
/// [OpeningBook] may be provided.
/// 
/// Construct this engine using [kvarko_engine].
#[derive(Clone)]
pub struct KvarkoEngine<H>
where
    H: PositionHasher,
    H::Hash: TTableHash
{
    opening_book: Option<OpeningBook>,
    evaluator: KvarkoEvaluator<H>
}

impl<H> StateEvaluator<H> for KvarkoEngine<H>
where
    H: PositionHasher,
    H::Hash: TTableHash
{
    fn evaluate_state(&mut self, state: &mut State<H>) -> (f32, Option<Move>) {
        if let Some(opening_book) = &self.opening_book {
            if let Some(value) = opening_book.get_value(state) {
                let best_move = opening_book.get_best_move(state).unwrap();

                return (value, Some(*best_move));
            }
        }

        self.evaluator.evaluate_state(state)
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
    -> StateEvaluatingController<KvarkoEngine<H>>
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
    -> StateEvaluatingController<KvarkoEngine<H>>
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
                CaptureValuePresorter::new(),
                quiescence_search_ttable_bits
            ),
            CaptureValuePresorter::new(),
            deepen_for,
            tree_search_ttable_bits
        )
    })
}

#[cfg(test)]
mod tests {
    use kvarko_model::hash::ZobristHasher;

    use super::*;

    #[test]
    fn base_evaluator_punishes_doubled_pawns() {
        // In both scenarios, players have equal number of available moves.

        let no_doubled_pawns_fen = "8/4k3/4p3/3pP3/3P4/3K4/8/8 w - - 0 1";
        let mut no_doubled_pawns: State<ZobristHasher<u64>> =
            State::from_fen(no_doubled_pawns_fen).unwrap();
        let doubled_pawns_fen = "8/8/3Ppk2/3p4/3P4/3K4/8/8 w - - 0 1";
        let mut doubled_pawns: State<ZobristHasher<u64>> =
            State::from_fen(doubled_pawns_fen).unwrap();
        let mut base_evaluator = KvarkoBaseEvaluator::default();

        let no_doubled_pawns_eval = base_evaluator.evaluate_state(
            &mut no_doubled_pawns, f32::NEG_INFINITY, f32::INFINITY);
        let doubled_pawns_eval = base_evaluator.evaluate_state(
            &mut doubled_pawns, f32::NEG_INFINITY, f32::INFINITY);

        assert!(no_doubled_pawns_eval > doubled_pawns_eval + 0.01);
    }
}
