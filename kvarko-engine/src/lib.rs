use kvarko_model::board::Bitboard;
use kvarko_model::game::Controller;
use kvarko_model::movement::{self, Move};
use kvarko_model::state::State;
use kvarko_model::piece::Piece;

use std::cmp::Ordering;
use std::iter;

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
    /// * `state`: A reference to the current game [State]. This also contains
    /// information about the player whose turn it is.
    /// * `moves`: A buffer to use for storing any [Move]s that may be
    /// generated during the evaluation. Using this buffer avoids reallocation.
    ///
    /// # Returns
    ///
    /// As a first return parameter, this function returns an evaluation of the
    /// current position, where negative numbers are more probably defeats than
    /// victories and positive numbers are more probably victories than
    /// defeats. The optional second return parameter contains a recommended
    /// move.
    fn evaluate_state(&mut self, state: &State, moves: &mut Vec<Move>)
        -> (f32, Option<Move>);
}

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

const RELEVANT_PIECES: [Piece; 5] = [
    Piece::Pawn,
    Piece::Knight,
    Piece::Bishop,
    Piece::Rook,
    Piece::Queen
];

pub struct KvarkoBaseEvaluator {
    values: [f32; 6],
    move_value: f32,
    doubled_pawn_penalty: f32
}

impl KvarkoBaseEvaluator {

    pub fn new(pawn_value: f32, knight_value: f32, bishop_value: f32,
            rook_value: f32, queen_value: f32, move_value: f32,
            doubled_pawn_penalty: f32) -> KvarkoBaseEvaluator {
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
            doubled_pawn_penalty
        }
    }
}

impl Default for KvarkoBaseEvaluator {

    fn default() -> KvarkoBaseEvaluator {
        KvarkoBaseEvaluator {
            values: DEFAULT_MATERIAL_VALUES.clone(),
            move_value: DEFAULT_MOVE_VALUE,
            doubled_pawn_penalty: DEFAULT_DOUBLED_PAWN_PENALTY
        }
    }
}

impl StateEvaluator for KvarkoBaseEvaluator {

    fn evaluate_state(&mut self, state: &State, moves: &mut Vec<Move>)
            -> (f32, Option<Move>) {
        if state.is_stateful_draw() {
            return (0.0, None);
        }

        let turn = state.position().turn();
        moves.clear();
        let check = movement::list_moves_in(state.position(), moves);

        if moves.is_empty() {
            if check {
                return (f32::NEG_INFINITY, None);
            }
            else {
                return (0.0, None);
            }
        }

        let opponent = turn.opponent();
        let opponent_moves = {
            let mut position = state.position().clone();
            position.set_turn(opponent);
            movement::list_moves(&position).0
        };
        let board = state.position().board();
        let mut value = (moves.len() as f32 - opponent_moves.len() as f32) *
            self.move_value;

        for piece in RELEVANT_PIECES {
            let piece_value = self.values[piece as usize];

            value += piece_value *
                board.of_player_and_kind(turn, piece).len() as f32;
            value -= piece_value *
                board.of_player_and_kind(opponent, piece).len() as f32;
        }

        for file in FILES {
            let pawns =
                (board.of_player_and_kind(turn, Piece::Pawn) & file).len();
            value -= self.doubled_pawn_penalty * (pawns as f32 - 1.0);

            let opponent_pawns =
                (board.of_player_and_kind(opponent, Piece::Pawn) & file).len();
            value += self.doubled_pawn_penalty * (opponent_pawns as f32 - 1.0);
        }

        (value, None)
    }
}

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

impl<E: StateEvaluator> TreeSearchEvaluator<E> {

    fn evaluate_rec(&mut self, state: &mut State,
            bufs: &mut [Vec<Move>], mut alpha: f32, beta: f32)
            -> (f32, Option<Move>) {
        if bufs.len() == 1 {
            self.base_evaluator.evaluate_state(state, &mut bufs[0])
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
                    return (f32::NEG_INFINITY, None);
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
                let value =
                    -self.evaluate_rec(state, bufs_rest, -beta, -alpha).0;
                state.unmake_move(&mov, revert_info);

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

impl<E: StateEvaluator> StateEvaluator for TreeSearchEvaluator<E> {

    fn evaluate_state(&mut self, state: &State, _: &mut Vec<Move>)
            -> (f32, Option<Move>) {
        let mut state = state.clone();
        let mut bufs = iter::repeat_with(Vec::new)
            .take(self.search_depth as usize + 1)
            .collect::<Vec<_>>();
        self.evaluate_rec(&mut state, &mut bufs, f32::NEG_INFINITY, f32::INFINITY)
    }
}

pub struct StateEvaluatingController<E>(E);

impl<E: StateEvaluator> StateEvaluator for StateEvaluatingController<E> {

    fn evaluate_state(&mut self, state: &State, moves: &mut Vec<Move>)
            -> (f32, Option<Move>) {
        self.0.evaluate_state(state, moves)
    }
}

impl<E: StateEvaluator> Controller for StateEvaluatingController<E> {

    fn make_move(&mut self, state: &State) -> Move {
        let mut moves = Vec::new();

        if let Some(mov) = self.0.evaluate_state(state, &mut moves).1 {
            return mov;
        }

        movement::list_moves(state.position()).0.into_iter()
            .max_by_key(|mov| {
                let mut state = state.clone();
                state.make_move(mov);
                OrdF32(-self.0.evaluate_state(&state, &mut moves).0)
            })
            .unwrap()
    }
}

pub type KvarkoEngine =
    StateEvaluatingController<TreeSearchEvaluator<KvarkoBaseEvaluator>>;

pub fn kvarko_engine(depth: u32) -> KvarkoEngine {
    StateEvaluatingController(TreeSearchEvaluator {
        base_evaluator: KvarkoBaseEvaluator::default(),
        search_depth: depth
    })
}
