//! This module contains some tests that check that transposition table size
//! does not change the evaluation and best move.

use std::collections::HashMap;
use std::time::Duration;
use kvarko_engine::{kvarko_engine_with_ttable_bits, KvarkoEngineMetadata, StateEvaluator};

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

const DEEPEN_FOR: Duration = Duration::from_millis(10);

fn assert_ttable_size_irrelevant(fen: &str) {
    let mut state = State::from_fen(fen).unwrap();
    let mut expectations_by_depth = HashMap::new();

    for ttable_bits in TTABLE_BITS {
        let mut engine = kvarko_engine_with_ttable_bits::<ZobristHasher<u64>>(
            DEEPEN_FOR, None, ttable_bits, ttable_bits);
        let output = engine.evaluate_state(&mut state);
        let depth = match output.metadata {
            KvarkoEngineMetadata::BookMove => panic!(),
            KvarkoEngineMetadata::ComputedMove(metadata) => metadata.depth
        };
        println!("depth {}", depth);
        println!("bits {}", ttable_bits);
        println!("{:?}", &expectations_by_depth);

        if let Some(&(expected_eval, expected_move)) = expectations_by_depth.get(&depth) {
            assert_eq!(expected_eval, output.evaluation);
            assert_eq!(expected_move, output.recommended_move);
        }
        else {
            expectations_by_depth.insert(depth, (output.evaluation, output.recommended_move));
        }
    }
}

#[test]
fn initial_position() {
    let fen = "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1";

    assert_ttable_size_irrelevant(fen);
}

#[test]
fn ruy_lopez() {
    let fen =
        "r1bqkbnr/pppp1ppp/2n5/1B2p3/4P3/5N2/PPPP1PPP/RNBQK2R b KQkq - 3 3";

    assert_ttable_size_irrelevant(fen);
}

#[test]
fn queens_gambit_declined() {
    let fen = "rnbqkbnr/ppp2ppp/4p3/3p4/2PP4/8/PP2PPPP/RNBQKBNR w KQkq - 0 3";

    assert_ttable_size_irrelevant(fen);
}

#[test]
fn three_knights_game() {
    let fen =
        "r1bqkbnr/pppp1ppp/2n5/4p3/4P3/2N2N2/PPPP1PPP/R1BQKB1R b KQkq - 3 3";

    assert_ttable_size_irrelevant(fen);
}

#[test]
fn english() {
    let fen =
        "rnbqkb1r/pppppp1p/5np1/8/2P5/2N3P1/PP1PPP1P/R1BQKBNR b KQkq - 0 3";

    assert_ttable_size_irrelevant(fen);
}

#[test]
fn classical_kings_indian() {
    let fen =
        "rnbq1rk1/ppp1ppbp/3p1np1/8/2PPP3/2N2N2/PP3PPP/R1BQKB1R w KQ - 2 6";

    assert_ttable_size_irrelevant(fen);
}

#[test]
fn open_sicilian() {
    let fen =
        "rnbqkb1r/pp2pppp/3p1n2/8/3NP3/2N5/PPP2PPP/R1BQKB1R b KQkq - 2 5";

    assert_ttable_size_irrelevant(fen);
}

#[test]
fn closed_sicilian() {
    let fen =
        "r1bqkbnr/pp1ppp1p/2n3p1/2p5/4P3/2N3P1/PPPP1P1P/R1BQKBNR w KQkq - 0 4";

    assert_ttable_size_irrelevant(fen);
}

#[test]
fn middlegame_1() {
    let fen = "r6r/1ppk1p2/3pb1p1/p1b4p/P1P2R2/3B4/1PPB1PPP/R5K1 w - - 1 19";

    assert_ttable_size_irrelevant(fen);
}

#[test]
fn middlegame_2() {
    let fen = "r3r3/3k1p2/1pppb1p1/7p/PpP2R1P/1P1B4/2P2PP1/4RK2 b - - 1 26";

    assert_ttable_size_irrelevant(fen);
}

#[test]
fn middlegame_3() {
    let fen = "rnq1k2r/pp1b2pp/4p3/2p3B1/2B5/1Q6/P4PPP/1R3RK1 b kq - 0 15";

    assert_ttable_size_irrelevant(fen);
}

#[test]
fn middlegame_4() {
    let fen = "2r1r1k1/6pp/p1q1p3/2Bn4/2Q5/7P/P4PP1/2RR2K1 w - - 2 25";

    assert_ttable_size_irrelevant(fen);
}

#[test]
fn middlegame_5() {
    let fen = "r1bq1rk1/pp2b1pp/4pn2/5pB1/8/1BPN2Q1/P4PPP/R3R1K1 b - - 5 18";

    assert_ttable_size_irrelevant(fen);
}

#[test]
fn middlegame_6() {
    let fen = "2b2rk1/4q1pp/4p3/1pN5/4p3/1PP1Q3/6PP/R5K1 w - - 0 26";

    assert_ttable_size_irrelevant(fen);
}

#[test]
fn middlegame_7() {
    let fen =
        "2r2rk1/1pqbppbp/p5p1/2PnN3/3BpP2/2P3P1/PP1N3P/R2Q1RK1 b - - 0 15";

    assert_ttable_size_irrelevant(fen);
}

#[test]
fn middlegame_8() {
    let fen =
        "2r3k1/1p4rp/p1q1p1p1/2Pn1p2/2NPpP1P/PQ4P1/1P5R/3R2K1 w - - 1 25";

    assert_ttable_size_irrelevant(fen);
}

#[test]
fn middlegame_9() {
    let fen = "r4rk1/p3ppb1/q1n3p1/2P4p/2b1N2Q/6P1/3RPPBP/2B2RK1 w - - 6 19";

    assert_ttable_size_irrelevant(fen);
}

#[test]
fn middlegame_10() {
    let fen = "r4rk1/p3pp2/q5p1/2P2n2/4Nb2/7Q/5PBP/4RRK1 w - - 2 25";

    assert_ttable_size_irrelevant(fen);
}

#[test]
fn endgame_1() {
    let fen = "8/2r4k/p4R2/7p/8/7P/6P1/7K b - - 0 71";

    assert_ttable_size_irrelevant(fen);
}

#[test]
fn endgame_2() {
    let fen = "8/8/3p2n1/4p3/4KPk1/4B1P1/8/8 w - - 0 1";

    assert_ttable_size_irrelevant(fen);
}

#[test]
fn endgame_3() {
    let fen = "8/8/6q1/8/P1P3kp/2K3p1/6Q1/8 b - - 0 1";

    assert_ttable_size_irrelevant(fen);
}

#[test]
fn endgame_4() {
    let fen = "8/5pp1/5k1p/4p3/4P3/4KP1P/6P1/8 b - - 0 1";

    assert_ttable_size_irrelevant(fen);
}

#[test]
fn endgame_5() {
    let fen = "2R5/1p6/2P1pk2/P4p2/1P4p1/4p1q1/8/5QK1 w - - 0 66";

    assert_ttable_size_irrelevant(fen);
}

#[test]
fn endgame_6() {
    let fen = "8/8/2kp4/8/2KN4/4N3/8/8 b - - 0 1";

    assert_ttable_size_irrelevant(fen);
}

#[test]
fn endgame_7() {
    let fen = "8/5r2/5kp1/5p2/5P2/4QK2/8/8 w - - 0 1";

    assert_ttable_size_irrelevant(fen);
}

#[test]
fn endgame_8() {
    let fen = "8/8/4r2k/8/6R1/4pR2/1r3PK1/8 b - - 1 48";

    assert_ttable_size_irrelevant(fen);
}
