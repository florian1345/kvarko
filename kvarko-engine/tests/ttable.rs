//! This module contains some tests that check that transposition table size
//! does not change the evaluation and best move.

use kvarko_engine::{kvarko_engine_with_ttable_bits, StateEvaluator};

use kvarko_model::hash::ZobristHasher;
use kvarko_model::state::State;

const TTABLE_BITS: [u32; 6] = [
    0,
    10,
    12,
    14,
    16,
    18
];

fn assert_ttable_size_irrelevant(fen: &str, depth: u32) {
    let engines = TTABLE_BITS.iter()
        .map(|&ttable_bits|
            kvarko_engine_with_ttable_bits::<ZobristHasher<u64>>(
                depth, None, ttable_bits, ttable_bits));
    let mut state = State::from_fen(fen).unwrap();
    let mut expected_eval = None;
    let mut expected_move = None;

    for mut engine in engines {
        let (eval, mov) = engine.evaluate_state(&mut state);

        if let (Some(expected_eval), Some(expected_move)) =
                (expected_eval, expected_move) {
            assert_eq!(expected_eval, eval);
            assert_eq!(expected_move, mov);
        }
        else {
            expected_eval = Some(eval);
            expected_move = Some(mov);
        }
    }
}

#[test]
fn initial_position() {
    let fen = "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1";

    assert_ttable_size_irrelevant(fen, 5);
}

#[test]
fn ruy_lopez() {
    let fen =
        "r1bqkbnr/pppp1ppp/2n5/1B2p3/4P3/5N2/PPPP1PPP/RNBQK2R b KQkq - 3 3";

    assert_ttable_size_irrelevant(fen, 5);
}

#[test]
fn queens_gambit_declined() {
    let fen = "rnbqkbnr/ppp2ppp/4p3/3p4/2PP4/8/PP2PPPP/RNBQKBNR w KQkq - 0 3";

    assert_ttable_size_irrelevant(fen, 5);
}

#[test]
fn three_knights_game() {
    let fen =
        "r1bqkbnr/pppp1ppp/2n5/4p3/4P3/2N2N2/PPPP1PPP/R1BQKB1R b KQkq - 3 3";

    assert_ttable_size_irrelevant(fen, 5);
}

#[test]
fn middlegame_1() {
    let fen = "r6r/1ppk1p2/3pb1p1/p1b4p/P1P2R2/3B4/1PPB1PPP/R5K1 w - - 1 19";

    assert_ttable_size_irrelevant(fen, 5);
}

#[test]
fn middlegame_2() {
    let fen = "r3r3/3k1p2/1pppb1p1/7p/PpP2R1P/1P1B4/2P2PP1/4RK2 b - - 1 26";

    assert_ttable_size_irrelevant(fen, 5);
}

#[test]
fn middlegame_3() {
    let fen = "rnq1k2r/pp1b2pp/4p3/2p3B1/2B5/1Q6/P4PPP/1R3RK1 b kq - 0 15";

    assert_ttable_size_irrelevant(fen, 5);
}

#[test]
fn middlegame_4() {
    let fen = "2r1r1k1/6pp/p1q1p3/2Bn4/2Q5/7P/P4PP1/2RR2K1 w - - 2 25";

    assert_ttable_size_irrelevant(fen, 4);
}

#[test]
fn endgame_1() {
    let fen = "8/2r4k/p4R2/7p/8/7P/6P1/7K b - - 0 71";

    assert_ttable_size_irrelevant(fen, 7);
}

#[test]
fn endgame_2() {
    let fen = "8/8/3p2n1/4p3/4KPk1/4B1P1/8/8 w - - 0 1";

    assert_ttable_size_irrelevant(fen, 9);
}

#[test]
fn endgame_3() {
    let fen = "8/8/6q1/8/P1P3kp/2K3p1/6Q1/8 b - - 0 1";

    assert_ttable_size_irrelevant(fen, 7);
}

#[test]
fn endgame_4() {
    let fen = "8/5pp1/5k1p/4p3/4P3/4KP1P/6P1/8 b - - 0 1";

    assert_ttable_size_irrelevant(fen, 8);
}
