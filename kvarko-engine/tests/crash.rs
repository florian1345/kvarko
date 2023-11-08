//! This module contains some test runs with inputs on which the engine
//! previously crashed.

use kvarko_engine::{KvarkoEngine, StateEvaluatingController};
use kvarko_engine::depth::IterativeDeepeningToDepth;

use kvarko_model::game::Controller;
use kvarko_model::hash::ZobristHasher;
use kvarko_model::state::State;

type Kvarko = StateEvaluatingController<
    KvarkoEngine<ZobristHasher<u64>, IterativeDeepeningToDepth>>;

fn kvarko(depth: u32) -> Kvarko {
    kvarko_engine::kvarko_engine_with_ttable_bits_and_depth_strategy(
        IterativeDeepeningToDepth::new(depth), None, 20, 16)
}

fn assert_does_not_crash(depth: u32, fen: &str) {
    let mut kvarko = kvarko(depth);
    let state = State::from_fen(fen).unwrap();
    kvarko.make_move(&state);
}

#[test]
fn quiescence_with_promotions() {
    // We verify that quiescence search also considers new non-pawn pieces
    // which are created due to promotions.

    let fen = "r2q1rk1/1bp1bppp/2np1n2/pp2p3/P2PP3/1BP2N1P/1P3PP1/RNBQR1K1 b \
        - - 0 11";

    assert_does_not_crash(5, fen);
}
