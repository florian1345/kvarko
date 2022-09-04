use kvarko_model::board::Bitboard;
use kvarko_model::game::Controller;
use kvarko_model::movement::{self, Move, MoveProcessor};
use kvarko_model::state::{State, Position};
use kvarko_model::piece::Piece;
use kvarko_model::player::Player;

use std::cmp::Ordering;
use std::iter;

use crate::book::OpeningBook;

pub mod book;

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
pub trait StateEvaluator {

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
    fn evaluate_state(&mut self, state: &mut State) -> (f32, Option<Move>);
}

/// Similar to [StateEvaluator], however accepts additional parameters that are
/// provided by the [TreeSearchEvaluator] or [QuiescenseTreeSearchEvaluator],
/// which can be used to improve performance.
pub trait BaseEvaluator {

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
    fn evaluate_state(&mut self, state: &mut State, alpha: f32, beta: f32,
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
pub struct KvarkoBaseEvaluator {
    values: [f32; 6],
    move_value: f32,
    doubled_pawn_penalty: f32,
    pawn_sixth_rank_value: f32,
    pawn_seventh_rank_value: f32
}

impl KvarkoBaseEvaluator {

    pub fn new(pawn_value: f32, knight_value: f32, bishop_value: f32,
            rook_value: f32, queen_value: f32, move_value: f32,
            doubled_pawn_penalty: f32, pawn_sixth_rank_value: f32,
            pawn_seventh_rank_value: f32) -> KvarkoBaseEvaluator {
        KvarkoBaseEvaluator {
            values: [
                pawn_value,
                knight_value,
                bishop_value,
                rook_value,
                queen_value,
                10.0
            ],
            move_value,
            doubled_pawn_penalty,
            pawn_sixth_rank_value,
            pawn_seventh_rank_value
        }
    }

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
            values: DEFAULT_MATERIAL_VALUES.clone(),
            move_value: DEFAULT_MOVE_VALUE,
            doubled_pawn_penalty: DEFAULT_DOUBLED_PAWN_PENALTY,
            pawn_sixth_rank_value: DEFAULT_PAWN_SIXTH_RANK_VALUE,
            pawn_seventh_rank_value: DEFAULT_PAWN_SEVENTH_RANK_VALUE
        }
    }
}

impl BaseEvaluator for KvarkoBaseEvaluator {

    fn evaluate_state(&mut self, state: &mut State, _: f32, _: f32, moves: Option<usize>, check: Option<bool>) -> f32 {
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

pub struct ListAllMovesIn;

impl ListMovesIn for ListAllMovesIn {
    fn list_moves_in(&self, position: &Position, moves: &mut Vec<Move>)
            -> (bool, usize) {
        let check = movement::list_moves_in(position, moves);
        (check, moves.len())
    }
}

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
                    Move::Ordinary { captured, .. } => captured.clone(),
                    Move::Promotion { captured, .. } => captured.clone(),
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

/// A [BaseEvaluator] which does quiescense search on all moves provided by
/// some [ListMovesIn] implementation. This searches the full tree, without any
/// maximum depth. Alpha-beta-pruning is still applied.
pub struct QuiescenseTreeSearchEvaluator<E, L> {
    base_evaluator: E,
    list_moves_in: L,
    bufs: Vec<Vec<Move>>
}

impl<E, L> QuiescenseTreeSearchEvaluator<E, L> {

    pub fn new(base_evaluator: E, list_moves_in: L)
            -> QuiescenseTreeSearchEvaluator<E, L> {
        QuiescenseTreeSearchEvaluator {
            base_evaluator,
            list_moves_in,
            bufs: iter::repeat_with(Vec::new).take(QUIESCENSE_BUFFER_COUNT).collect()
        }
    }
}

impl<E, L> BaseEvaluator for QuiescenseTreeSearchEvaluator<E, L>
where
    E: BaseEvaluator,
    L: ListMovesIn
{
    fn evaluate_state(&mut self, state: &mut State, alpha: f32, beta: f32,
            _: Option<usize>, _: Option<bool>) -> f32 {

        fn evaluate_rec<E, L>(base_evaluator: &mut E, list_moves_in: &mut L,
            state: &mut State, bufs: &mut [Vec<Move>], mut alpha: f32,
            beta: f32) -> f32
        where
            E: BaseEvaluator,
            L: ListMovesIn
        {
            // TODO reduce code duplication

            let (moves, bufs_rest) = bufs.split_first_mut().unwrap();
            moves.clear();
            let (check, move_count) = list_moves_in.list_moves_in(&state.position(), moves);
            moves.sort_by_cached_key(|m| estimate_move(m));

            // Actor can stop trading now, if they want.

            let mut max = base_evaluator.evaluate_state(
                state, alpha, beta, Some(move_count), Some(check));

            for mov in moves {
                let revert_info = state.make_move(&mov);
                let value = -evaluate_rec(
                    base_evaluator, list_moves_in, state, bufs_rest,
                    -beta, -alpha);
                state.unmake_move(&mov, revert_info);

                max = max.max(value);
                alpha = alpha.max(max);

                if alpha >= beta {
                    break;
                }
            }

            max
        }
            
        evaluate_rec(
            &mut self.base_evaluator, &mut self.list_moves_in, state,
            &mut self.bufs, alpha, beta)
    }
}

/// A [StateEvaluator] that does a negimax tree search on the input state,
/// using alpha-beta-pruning.
pub struct TreeSearchEvaluator<E> {
    base_evaluator: E,
    search_depth: u32
}

impl<E> TreeSearchEvaluator<E> {

    pub fn new(base_evaluator: E, search_depth: u32)
            -> TreeSearchEvaluator<E> {
        TreeSearchEvaluator {
            base_evaluator,
            search_depth
        }
    }
}

fn estimate_move(mov: &Move) -> OrdF32 {
    match mov {
        &Move::Ordinary { moved, captured, .. } => {
            if let Some(captured) = captured {
                let cap_value = DEFAULT_MATERIAL_VALUES[captured as usize];
                let piece_value = DEFAULT_MATERIAL_VALUES[moved as usize];
                OrdF32(-cap_value / piece_value)
            }
            else {
                OrdF32(0.0)
            }
        },
        Move::EnPassant { .. } => return OrdF32(-1.0),
        &Move::Promotion { promotion, captured, .. } => {
            let mut value = DEFAULT_MATERIAL_VALUES[promotion as usize];

            if let Some(captured) = captured {
                value += DEFAULT_MATERIAL_VALUES[captured as usize];
            }

            OrdF32(-value)
        },
        Move::Castle { .. } => OrdF32(0.0)
    }
}

impl<E: BaseEvaluator> TreeSearchEvaluator<E> {

    fn evaluate_rec(&mut self, state: &mut State,
            bufs: &mut [Vec<Move>], mut alpha: f32, beta: f32)
            -> (f32, Option<Move>) {
        if bufs.len() == 1 {
            (self.base_evaluator.evaluate_state(state, alpha, beta, None, None), None)
        }
        else if state.is_stateful_draw() {
            // Checkmate is covered later
            (0.0, None)
        }
        else {
            let (moves, bufs_rest) = bufs.split_first_mut().unwrap();
            moves.clear();
            let check = movement::list_moves_in(&state.position(), moves);

            if moves.is_empty() {
                if check {
                    return (-CHECKMATE_VALUE, None);
                }
                else {
                    return (0.0, None);
                }
            }

            moves.sort_by_cached_key(|m| estimate_move(m));
            let mut max = f32::NEG_INFINITY;
            let mut max_move = None;

            for mov in moves {
                let revert_info = state.make_move(&mov);
                let mut value =
                    -self.evaluate_rec(state, bufs_rest, -beta, -alpha).0;
                state.unmake_move(&mov, revert_info);

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
                }

                alpha = alpha.max(max);

                if alpha >= beta {
                    break;
                }
            }

            (max, max_move.cloned())
        }
    }
}

impl<E: BaseEvaluator> StateEvaluator for TreeSearchEvaluator<E> {

    fn evaluate_state(&mut self, state: &mut State) -> (f32, Option<Move>) {
        let mut bufs = iter::repeat_with(Vec::new)
            .take(self.search_depth as usize + 1)
            .collect::<Vec<_>>();
        self.evaluate_rec(state, &mut bufs, f32::NEG_INFINITY, f32::INFINITY)
    }
}

/// A wrapper around a [StateEvaluator] that implements [Controller] by playing
/// the recommended move, if one is present, and otherwise checks which move
/// would make the underlying state evaluator return the worst evaluation for
/// the opponent.
pub struct StateEvaluatingController<E>(E);

impl<E: StateEvaluator> StateEvaluator for StateEvaluatingController<E> {

    fn evaluate_state(&mut self, state: &mut State)
            -> (f32, Option<Move>) {
        self.0.evaluate_state(state)
    }
}

impl<E: StateEvaluator> Controller for StateEvaluatingController<E> {

    fn make_move(&mut self, state: &State) -> Move {
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

type KvarkoEvaluator = TreeSearchEvaluator<QuiescenseTreeSearchEvaluator<
    KvarkoBaseEvaluator, ListNonPawnCapturesIn>>;

/// A [StateEvaluator] that represents the totality of functionality contained
/// in the Kvarko engine. In particular, this uses a [TreeSearchEvaluator]
/// followed by a [QuiescenseTreeSearchEvaluator] which uses the
/// [KvarkoBaseEvaluator] for evaluation of base states. In addition, an
/// [OpeningBook] may be provided.
/// 
/// Construct this engine using [kvarko_engine].
pub struct KvarkoEngine {
    opening_book: Option<OpeningBook>,
    evaluator: KvarkoEvaluator
}

impl StateEvaluator for KvarkoEngine {

    fn evaluate_state(&mut self, state: &mut State) -> (f32, Option<Move>) {
        if let Some(opening_book) = &self.opening_book {
            if let Some(value) = opening_book.get_value(state) {
                let best_move = opening_book.get_best_move(state).unwrap();

                return (value, Some(best_move.clone()));
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
pub fn kvarko_engine(depth: u32, opening_book: Option<OpeningBook>)
        -> StateEvaluatingController<KvarkoEngine> {
    StateEvaluatingController(KvarkoEngine {
        opening_book,
        evaluator: TreeSearchEvaluator {
            base_evaluator: QuiescenseTreeSearchEvaluator::new(
                KvarkoBaseEvaluator::default(),
                ListNonPawnCapturesIn
            ),
            search_depth: depth
        }
    })
}
