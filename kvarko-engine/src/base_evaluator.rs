use crate::eval::{Centipawns, Evaluation};

use kvarko_model::board::{Bitboard, Board};
use kvarko_model::hash::PositionHasher;
use kvarko_model::movement;
use kvarko_model::piece::Piece;
use kvarko_model::player::Player;
use kvarko_model::state::{Position, State};

/// Similar to [StateEvaluator](crate::StateEvaluator), however accepts
/// additional parameters that are rovided by the
/// [TreeSearchEvaluator](crate::TreeSearchEvaluator) or
/// [QuiescenseTreeSearchEvaluator](crate::QuiescenseTreeSearchEvaluator),
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
    fn evaluate_state(&mut self, state: &mut State<H>, alpha: Evaluation, beta: Evaluation)
            -> Evaluation {
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
        alpha: Evaluation, beta: Evaluation, move_count: usize, check: bool) -> Evaluation;
}

const DEFAULT_MATERIAL_VALUES: [Centipawns; 6] = [
    100,
    300,
    305,
    500,
    900,
    1000
];

const DEFAULT_MOVE_VALUE: Centipawns = 5;
const DEFAULT_DOUBLED_PAWN_PENALTY: Centipawns = 25;
const DEFAULT_PAWN_SIXTH_RANK_VALUE: Centipawns = 10;
const DEFAULT_PAWN_SEVENTH_RANK_VALUE: Centipawns = 30;
const DEFAULT_BISHOP_PAIR_VALUE: Centipawns = 45;

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
    values: [Centipawns; 6],
    move_value: Centipawns,
    doubled_pawn_penalty: Centipawns,
    pawn_sixth_rank_value: Centipawns,
    pawn_seventh_rank_value: Centipawns,
    bishop_pair_value: Centipawns
}

impl KvarkoBaseEvaluator {

    #[inline]
    fn evaluate_pawn_ranks(&self, player: Player, pawns: Bitboard) -> Centipawns {
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

        sixth_rank_pawns as Centipawns * self.pawn_sixth_rank_value +
            seventh_rank_pawns as Centipawns * self.pawn_seventh_rank_value
    }

    #[inline]
    fn evaluate_move_count(&self, position: &Position, move_count: usize, opponent: Player)
            -> Centipawns {
        let opponent_moves = {
            let mut position = position.clone();
            position.set_turn(opponent);
            movement::count_moves(&position).0
        };

        (move_count as Centipawns - opponent_moves as Centipawns) * self.move_value
    }

    #[inline]
    fn evaluate_material(&self, board: &Board, turn: Player, opponent: Player) -> Centipawns {
        let mut value = 0;

        for piece in RELEVANT_PIECES {
            let piece_value = self.values[piece as usize];

            value += piece_value *
                board.of_player_and_kind(turn, piece).len() as Centipawns;
            value -= piece_value *
                board.of_player_and_kind(opponent, piece).len() as Centipawns;
        }

        value
    }

    #[inline]
    fn evaluate_bishop_pairs(&self, board: &Board, player: Player) -> Centipawns {
        let bishops = board.of_player_and_kind(player, Piece::Bishop);
        let light_squared_bishops = (bishops & Bitboard::LIGHT_SQUARES).len();
        let dark_squared_bishops = (bishops & Bitboard::DARK_SQUARES).len();
        let bishop_pairs = light_squared_bishops.min(dark_squared_bishops);

        bishop_pairs as Centipawns * self.bishop_pair_value
    }

    #[inline]
    fn evaluate_doubled_pawns(&self, own_pawns: Bitboard, opponent_pawns: Bitboard) -> Centipawns {
        let mut value = 0;

        for file in FILES {
            let own_pawns = (own_pawns & file).len().saturating_sub(1);
            value -= self.doubled_pawn_penalty * own_pawns as Centipawns;

            let opponent_pawns = (opponent_pawns & file).len().saturating_sub(1);
            value += self.doubled_pawn_penalty * opponent_pawns as Centipawns;
        }

        value
    }
}

impl Default for KvarkoBaseEvaluator {

    fn default() -> KvarkoBaseEvaluator {
        KvarkoBaseEvaluator {
            values: DEFAULT_MATERIAL_VALUES,
            move_value: DEFAULT_MOVE_VALUE,
            doubled_pawn_penalty: DEFAULT_DOUBLED_PAWN_PENALTY,
            pawn_sixth_rank_value: DEFAULT_PAWN_SIXTH_RANK_VALUE,
            pawn_seventh_rank_value: DEFAULT_PAWN_SEVENTH_RANK_VALUE,
            bishop_pair_value: DEFAULT_BISHOP_PAIR_VALUE
        }
    }
}

/// The value of a position in which the active player has no moves remaining.
/// The parameter indicates whether the player is in check.
#[inline]
pub fn evaluate_if_no_moves_remain(check: bool) -> Evaluation {
    if check {
        Evaluation::CHECKMATED
    } else {
        Evaluation::ZERO
    }
}

impl<H: PositionHasher> BaseEvaluator<H> for KvarkoBaseEvaluator {

    fn evaluate_state_with_precomputed_data(&mut self, state: &mut State<H>,
            _: Evaluation, _: Evaluation, move_count: usize, check: bool) -> Evaluation {
        if state.is_stateful_draw() {
            return Evaluation::ZERO;
        }

        let position = state.position();
        let turn = position.turn();

        if move_count == 0 {
            return evaluate_if_no_moves_remain(check)
        }

        let opponent = turn.opponent();
        let board = position.board();

        let own_pawns = board.of_player_and_kind(turn, Piece::Pawn);
        let opponent_pawns = board.of_player_and_kind(opponent, Piece::Pawn);

        let centipawns = self.evaluate_move_count(position, move_count, opponent)
            + self.evaluate_material(board, turn, opponent)
            + self.evaluate_doubled_pawns(own_pawns, opponent_pawns)
            + self.evaluate_pawn_ranks(turn, own_pawns)
            - self.evaluate_pawn_ranks(opponent, opponent_pawns)
            + self.evaluate_bishop_pairs(board, turn)
            - self.evaluate_bishop_pairs(board, opponent);

        Evaluation::from_centipawns_unchecked(centipawns)
    }
}

#[cfg(test)]
mod tests {

    use kvarko_model::hash::ZobristHasher;

    use kernal::prelude::*;
    use kvarko_model::movement::Move;

    use super::*;

    fn make_move(state: &mut State<ZobristHasher<u64>>, algebraic: &str) {
        let mov = Move::parse_algebraic(state.position(), algebraic).unwrap();

        state.make_move(&mov);
    }

    fn eval_with_kvarko_base_evaluator(state: &mut State<ZobristHasher<u64>>)
            -> Evaluation {
        let mut base_evaluator = KvarkoBaseEvaluator::default();

        base_evaluator.evaluate_state(state, Evaluation::NEG_INFINITY, Evaluation::INFINITY)
    }

    #[test]
    fn base_evaluator_punishes_doubled_pawns() {
        // In both scenarios, players have equal number of available moves.

        let mut no_doubled_pawns =
            State::from_fen("8/4k3/4p3/3pP3/3P4/3K4/8/8 w - - 0 1").unwrap();
        let mut doubled_pawns =
            State::from_fen("8/8/3Ppk2/3p4/3P4/3K4/8/8 w - - 0 1").unwrap();

        let no_doubled_pawns_eval =
            eval_with_kvarko_base_evaluator(&mut no_doubled_pawns);
        let doubled_pawns_eval =
            eval_with_kvarko_base_evaluator(&mut doubled_pawns);

        assert_that!(no_doubled_pawns_eval).is_greater_than(doubled_pawns_eval);
    }

    #[test]
    fn base_evaluator_has_evaluation_zero_for_draw_by_repetition() {
        let mut state =
            State::from_fen("5K1k/7q/8/8/8/8/R7/r7 w - - 0 1").unwrap();

        for _ in 0..2 {
            make_move(&mut state, "Rb2");
            make_move(&mut state, "Rb1");
            make_move(&mut state, "Ra2");
            make_move(&mut state, "Ra1");
        }

        let eval = eval_with_kvarko_base_evaluator(&mut state);

        assert_that!(eval).is_zero();
    }

    #[test]
    fn base_evaluator_has_evaluation_zero_for_draw_by_fifty_move_rule() {
        let mut state =
            State::from_fen("5K1k/7q/8/8/8/8/R7/r7 b - - 100 60").unwrap();

        let eval = eval_with_kvarko_base_evaluator(&mut state);

        assert_that!(eval).is_zero();
    }

    #[test]
    fn base_evaluator_has_evaluation_zero_for_draw_by_insufficient_material() {
        let mut state =
            State::from_fen("5K1k/7b/8/8/8/8/8/8 w - - 0 1").unwrap();

        let eval = eval_with_kvarko_base_evaluator(&mut state);

        assert_that!(eval).is_zero();
    }

    #[test]
    fn base_evaluator_has_evaluation_zero_for_stalemate() {
        // Board (black to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │ k │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ Q │ K │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // Black has no legal moves.

        let mut state =
            State::from_fen("k7/2QK4/8/8/8/8/8/8 b - - 0 1").unwrap();

        let eval = eval_with_kvarko_base_evaluator(&mut state);

        assert_that!(eval).is_zero();
    }

    #[test]
    fn base_evaluator_has_correct_evaluation_for_checkmate() {
        // Board (white to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │ k │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ q │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ K │   │   │   │   │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // Black checkmated White.

        let mut state =
            State::from_fen("8/8/8/8/8/1k6/2q5/2K5 w - - 0 1").unwrap();

        let eval = eval_with_kvarko_base_evaluator(&mut state);

        assert_that!(eval).is_equal_to(Evaluation::CHECKMATED);
    }

    #[test]
    fn base_evaluator_favors_clear_material_advantage() {
        // Board (black to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │   │   │   │   │   │   │   │ k │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │ b │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ K │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ R │   │   │   │   │   │   │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // Black has more legal moves, but White is up an exchange.

        let mut state =
            State::from_fen("7k/8/8/8/4b3/8/K7/R7 b - - 0 1").unwrap();

        let eval = eval_with_kvarko_base_evaluator(&mut state);

        assert_that!(eval).is_negative();
    }

    #[test]
    fn base_evaluator_favors_mobility() {
        // Board (white to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │   │   │   │   │   │ b │   │ k │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │ B │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │ K │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // Although material is equal, White has more available moves.

        let mut state =
            State::from_fen("5b1k/8/8/8/4B3/8/1K6/8 w - - 0 1").unwrap();

        let eval = eval_with_kvarko_base_evaluator(&mut state);

        assert_that!(eval).is_positive();
    }
}
