use kvarko_model::board::{Bitboard, Board};
use kvarko_model::hash::PositionHasher;
use kvarko_model::movement;
use kvarko_model::piece::Piece;
use kvarko_model::player::Player;
use kvarko_model::state::{Position, State};

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

    #[inline]
    fn evaluate_move_count(&self, position: &Position, move_count: usize,
        opponent: Player) -> f32 {
        let opponent_moves = {
            let mut position = position.clone();
            position.set_turn(opponent);
            movement::count_moves(&position).0
        };

        (move_count as f32 - opponent_moves as f32) * self.move_value
    }

    #[inline]
    fn evaluate_material(&self, board: &Board, turn: Player, opponent: Player)
        -> f32 {
        let mut value = 0.0;

        for piece in RELEVANT_PIECES {
            let piece_value = self.values[piece as usize];

            value += piece_value *
                board.of_player_and_kind(turn, piece).len() as f32;
            value -= piece_value *
                board.of_player_and_kind(opponent, piece).len() as f32;
        }

        value
    }

    #[inline]
    fn evaluate_doubled_pawns(&self, own_pawns: Bitboard,
        opponent_pawns: Bitboard) -> f32 {
        let mut value = 0.0;

        for file in FILES {
            let own_pawns = (own_pawns & file).len().saturating_sub(1);
            value -= self.doubled_pawn_penalty * own_pawns as f32;

            let opponent_pawns = (opponent_pawns & file).len().saturating_sub(1);
            value += self.doubled_pawn_penalty * opponent_pawns as f32;
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
            pawn_seventh_rank_value: DEFAULT_PAWN_SEVENTH_RANK_VALUE
        }
    }
}

const CHECKMATE_VALUE: f32 = 1_000_000_000.0;

/// The value of a position in which the active player has no moves remaining.
/// The parameter indicates whether the player is in check.
#[inline]
pub fn evaluate_if_no_moves_remain(check: bool) -> f32 {
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

        let position = state.position();
        let turn = position.turn();

        if move_count == 0 {
            return evaluate_if_no_moves_remain(check)
        }

        let opponent = turn.opponent();
        let board = position.board();

        let own_pawns = board.of_player_and_kind(turn, Piece::Pawn);
        let opponent_pawns = board.of_player_and_kind(opponent, Piece::Pawn);

        self.evaluate_move_count(position, move_count, opponent)
            + self.evaluate_material(board, turn, opponent)
            + self.evaluate_doubled_pawns(own_pawns, opponent_pawns)
            + self.evaluate_pawn_ranks(turn, own_pawns)
            - self.evaluate_pawn_ranks(opponent, opponent_pawns)
    }
}

#[cfg(test)]
mod tests {

    use kvarko_model::hash::ZobristHasher;

    use kernal::prelude::*;

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

        assert_that!(no_doubled_pawns_eval).is_greater_than(doubled_pawns_eval + 0.01);
    }
}
