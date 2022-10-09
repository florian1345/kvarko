use kvarko_model::board::Bitboard;
use kvarko_model::game::Controller;
use kvarko_model::hash::PositionHasher;
use kvarko_model::movement::{self, Move, MoveProcessor};
use kvarko_model::state::{State, Position};
use kvarko_model::piece::Piece;
use kvarko_model::player::Player;

use std::cmp::Ordering;
use std::iter;

use crate::book::OpeningBook;
use crate::sort::{Presorter, CaptureValuePresorter};
use crate::ttable::{
    AlwaysReplace,
    DepthAndBound,
    QuiescenceTableEntry,
    ReplacementPolicy,
    TranspositionTable,
    TreeSearchTableEntry,
    TTableEntry,
    TTableHash,
    ValueBound
};

pub mod book;
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
    /// perspective whose turn it currently is.
    ///
    /// # Arguments
    ///
    /// * `state`: A mutable reference to the current game [State]. This also
    /// contains information about the player whose turn it is. Must be left in
    /// the same state as before the method call.
    /// * `alpha`: The current alpha parameter from alpha-beta-pruning.
    /// * `beta`: The current beta parameter from alpha-beta-pruning.
    /// * `moves`: If present, specifies the number of available moves for the
    /// player whose turn it is.
    /// * `check`: If available, specifies whether the player whose turn it is
    /// is currently in check.
    ///
    /// # Returns
    ///
    /// As a first return parameter, this function returns an evaluation of the
    /// current position, where negative numbers are more probably defeats than
    /// victories and positive numbers are more probably victories than
    /// defeats.
    fn evaluate_state(&mut self, state: &mut State<H>, alpha: f32, beta: f32,
        moves: Option<usize>, check: Option<bool>) -> f32;
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

impl<H: PositionHasher> BaseEvaluator<H> for KvarkoBaseEvaluator {

    fn evaluate_state(&mut self, state: &mut State<H>, _: f32, _: f32,
            moves: Option<usize>, check: Option<bool>) -> f32 {
        if state.is_stateful_draw() {
            return 0.0;
        }

        let turn = state.position().turn();
        let (moves, check) =
            if let (Some(moves), Some(check)) = (moves, check) {
                (moves, check)
            }
            else {
                movement::count_moves(state.position())
            };

        if moves == 0 {
            if check {
                return -CHECKMATE_VALUE;
            }
            else {
                return 0.0;
            }
        }

        let opponent = turn.opponent();
        let opponent_moves = {
            let mut position = state.position().clone();
            position.set_turn(opponent);
            movement::count_moves(&position).0
        };
        let board = state.position().board();
        let mut value = (moves as f32 - opponent_moves as f32) *
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
            let own_pawns = (own_pawns & file).len();
            value -= self.doubled_pawn_penalty * (own_pawns as f32 - 1.0);

            let opponent_pawns = (opponent_pawns & file).len();
            value += self.doubled_pawn_penalty * (opponent_pawns as f32 - 1.0);
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
pub struct ListCapturesIn;

impl ListMovesIn for ListCapturesIn {
    fn list_moves_in(&self, position: &Position, moves: &mut Vec<Move>)
            -> (bool, usize) {
        struct CapturesLister<'a> {
            moves: &'a mut Vec<Move>,
            count: usize
        }

        impl<'a> MoveProcessor for CapturesLister<'a> {
            fn process(&mut self, mov: Move) {
                self.count += 1;
                let capture = match &mov {
                    Move::Ordinary { captured, .. } => captured.is_some(),
                    Move::EnPassant { .. } => true,
                    Move::Promotion { captured, .. } => captured.is_some(),
                    Move::Castle { .. } => false
                };

                if capture {
                    self.moves.push(mov);
                }
            }
        }

        let mut processor = CapturesLister {
            moves,
            count: 0
        };
        let check = movement::process_moves(position, &mut processor);

        (check, processor.count)
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
                let captured = match &mov {
                    Move::Ordinary { captured, .. } => *captured,
                    Move::Promotion { captured, .. } => *captured,
                    _ => None
                };

                if let Some(captured) = captured {
                    if captured != Piece::Pawn {
                        self.moves.push(mov);
                    }
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

const QUIESCENSE_BUFFER_COUNT: usize = 15;

/// Applies the information stored in `entry` to the given alpha and beta
/// bounds. If an early return is possible, `true` is returned.
fn process_ttable_entry<E>(alpha: &mut f32, beta: &mut f32,
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

impl<H, E, L, S> BaseEvaluator<H> for QuiescenseTreeSearchEvaluator<H, E, L, S>
where
    H: PositionHasher,
    H::Hash: TTableHash,
    E: BaseEvaluator<H>,
    L: ListMovesIn,
    S: Presorter
{
    fn evaluate_state(&mut self, state: &mut State<H>, alpha: f32, beta: f32,
            _: Option<usize>, _: Option<bool>) -> f32 {

        // TODO maybe this can be done as a method on &mut self?

        #[allow(clippy::too_many_arguments)]
        fn evaluate_rec<H, E, L, S, R>(base_evaluator: &mut E,
            list_moves_in: &mut L, state: &mut State<H>,
            bufs: &mut [Vec<Move>], mut alpha: f32, mut beta: f32,
            ttable: &mut TranspositionTable<H, QuiescenceTableEntry, R>,
            presorter: &mut S) -> (f32, ValueBound)
        where
            H: PositionHasher,
            H::Hash: TTableHash,
            E: BaseEvaluator<H>,
            L: ListMovesIn,
            R: ReplacementPolicy<QuiescenceTableEntry>,
            S: Presorter
        {
            let entry = ttable.get_entry(state.position_hash());
    
            if let Some(entry) = entry {
                if process_ttable_entry(&mut alpha, &mut beta, entry) {
                    return (entry.eval, entry.bound);
                }
            }

            // TODO reduce code duplication

            let (moves, bufs_rest) = bufs.split_first_mut().unwrap();
            moves.clear();
            let (check, move_count) = list_moves_in.list_moves_in(state.position(), moves);
            presorter.pre_sort(moves, state.position());

            // Actor can stop trading now, if they want.

            let mut max = base_evaluator.evaluate_state(
                state, alpha, beta, Some(move_count), Some(check));
            alpha = alpha.max(max);
            let mut bound = ValueBound::Exact;

            for mov in moves {
                let revert_info = state.make_move(mov);
                let (value, rec_bound) = evaluate_rec(
                    base_evaluator, list_moves_in, state, bufs_rest,
                    -beta, -alpha, ttable, presorter);
                let value = -value;
                state.unmake_move(mov, revert_info);

                if value > max {
                    max = value;
                    bound = rec_bound.invert();
                }

                alpha = alpha.max(max);

                if alpha >= beta {
                    bound = ValueBound::Lower;
                    break;
                }
            }

            ttable.enter(
                state.position_hash(), QuiescenceTableEntry {
                    eval: max,
                    bound
                });

            (max, bound)
        }
            
        evaluate_rec(
            &mut self.base_evaluator, &mut self.list_moves_in, state,
            &mut self.bufs, alpha, beta, &mut self.transposition_table,
            &mut self.presorter).0
    }
}

const NO_TRANSPOSITION_SEARCH: u32 = 0;

/// A [StateEvaluator] that does a negimax tree search on the input state,
/// using alpha-beta-pruning.
#[derive(Clone)]
pub struct TreeSearchEvaluator<E, S> {
    base_evaluator: E,
    presorter: S,
    search_depth: u32,
    ttable_bits: u32
}

impl<E, S> TreeSearchEvaluator<E, S> {

    pub fn new(base_evaluator: E, presorter: S, search_depth: u32,
            ttable_bits: u32) -> TreeSearchEvaluator<E, S> {
        TreeSearchEvaluator {
            base_evaluator,
            presorter,
            search_depth,
            ttable_bits
        }
    }
}

impl<E, S> TreeSearchEvaluator<E, S> {
    fn evaluate_rec<H, R>(&mut self, state: &mut State<H>, bufs: &mut [Vec<Move>],
        mut alpha: f32, mut beta: f32,
        ttable: &mut TranspositionTable<H, TreeSearchTableEntry, R>)
        -> (f32, Option<Move>, ValueBound)
    where
        H: PositionHasher,
        H::Hash: TTableHash,
        E: BaseEvaluator<H>,
        R: ReplacementPolicy<TreeSearchTableEntry>,
        S: Presorter
    {
        let depth = bufs.len() as u32;

        if depth == 1 {
            return (self.base_evaluator.evaluate_state(state, alpha, beta, None, None), None, ValueBound::Exact);
        }

        let entry = ttable.get_entry(state.position_hash());

        if let Some(entry) = entry {
            if depth <= self.search_depth + 1 - NO_TRANSPOSITION_SEARCH &&
                    entry.depth >= depth &&
                    process_ttable_entry(&mut alpha, &mut beta, entry) {
                let mov = entry.recommended_move;
                return (entry.eval, Some(mov), entry.bound)
            }
        }

        if state.is_stateful_draw() {
            // Checkmate is covered later
            (0.0, None, ValueBound::Exact)
        }
        else {
            let (moves, bufs_rest) = bufs.split_first_mut().unwrap();
            moves.clear();
            let check = movement::list_moves_in(state.position(), moves);

            if moves.is_empty() {
                if check {
                    return (-CHECKMATE_VALUE, None, ValueBound::Exact);
                }
                else {
                    return (0.0, None, ValueBound::Exact);
                }
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
                    self.evaluate_rec(state, bufs_rest, -beta, -alpha, ttable);
                let mut value = -rec_value;
                state.unmake_move(mov, revert_info);

                // Longer checkmate sequences have lower value.

                if value > CHECKMATE_DELTA {
                    value -= CHECKMATE_DELTA;
                }
                else if value < -CHECKMATE_DELTA {
                    value += CHECKMATE_DELTA;
                }

                if value > max {
                    max = value;
                    max_move = Some(mov);
                    bound = rec_bound.invert();
                }

                alpha = alpha.max(max);

                if alpha >= beta {
                    bound = ValueBound::Lower;
                    break;
                }
            }

            let max_move = max_move.cloned().unwrap();
            ttable.enter(
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

impl<H, E, S> StateEvaluator<H> for TreeSearchEvaluator<E, S>
where
    H: PositionHasher,
    H::Hash: TTableHash,
    E: BaseEvaluator<H>,
    S: Presorter
{
    fn evaluate_state(&mut self, state: &mut State<H>) -> (f32, Option<Move>) {
        let mut bufs = iter::repeat_with(Vec::new)
            .take(self.search_depth as usize + 1)
            .collect::<Vec<_>>();
        let mut ttable =
            TranspositionTable::new(self.ttable_bits, DepthAndBound);
        let (value, mov, _) = self.evaluate_rec(
            state, &mut bufs, f32::NEG_INFINITY, f32::INFINITY, &mut ttable);

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
/// * `depth`: The maximum search depth to which to search the game tree. Depth
/// is counted in half-moves (ply), i.e. a depth of 2 would search all
/// possibilities for 2 ply.
/// * `opening_book`: Optionally, specifies an [OpeningBook] for the engine to
/// use.
///
/// # Returns
///
/// A [StateEvaluatingController] wrapped around a [KvarkoEngine] with the
/// given parameters.
pub fn kvarko_engine<H>(depth: u32, opening_book: Option<OpeningBook>)
    -> StateEvaluatingController<KvarkoEngine<H>>
where
    H: PositionHasher,
    H::Hash: TTableHash
{
    kvarko_engine_with_ttable_bits(depth, opening_book, 20, 18)
}

/// Constructs a [KvarkoEngine] with given transposition table sizes.
///
/// # Arguments
///
/// * `depth`: The maximum search depth to which to search the game tree. Depth
/// is counted in half-moves (ply), i.e. a depth of 2 would search all
/// possibilities for 2 ply.
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
pub fn kvarko_engine_with_ttable_bits<H>(depth: u32,
    opening_book: Option<OpeningBook>, tree_search_ttable_bits: u32,
    quiescence_search_ttable_bits: u32)
    -> StateEvaluatingController<KvarkoEngine<H>>
where
    H: PositionHasher,
    H::Hash: TTableHash
{
    StateEvaluatingController(KvarkoEngine {
        opening_book,
        evaluator: TreeSearchEvaluator {
            base_evaluator: QuiescenseTreeSearchEvaluator::new(
                KvarkoBaseEvaluator::default(),
                ListNonPawnCapturesIn,
                CaptureValuePresorter::new(),
                quiescence_search_ttable_bits
            ),
            presorter: CaptureValuePresorter::new(),
            search_depth: depth,
            ttable_bits: tree_search_ttable_bits
        }
    })
}
