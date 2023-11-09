use kvarko_model::hash::IdHasher;
use kvarko_model::movement::{count_moves, list_moves};
use kvarko_model::state::State;

use kernal::prelude::*;

use rstest::rstest;

fn perft_rec(state: &mut State<IdHasher>, depth: usize) -> usize {
    if depth == 0 {
        return 1;
    }

    if depth == 1 {
        return count_moves(state.position()).0;
    }

    let mut sum = 0;

    for mov in list_moves(state.position()).0 {
        let revert_info = state.make_move(&mov);
        sum += perft_rec(state, depth - 1);
        state.unmake_move(&mov, revert_info);
    }

    sum
}

fn perft(fen: &str, depth: usize) -> usize {
    let mut state = State::from_fen(fen).unwrap();
    perft_rec(&mut state, depth)
}

#[rstest]
// Test positions by Martin Sedlak
// http://www.talkchess.com/forum3/viewtopic.php?t=47318
#[case::avoid_illegal_en_passant_capture(
    "8/5bk1/8/2Pp4/8/1K6/8/8 w - d6 0 1",
    "8/8/1k6/8/2pP4/8/5BK1/8 b - d3 0 1",
    6, 824064
)]
#[case::en_passant_capture_checks_opponent(
    "8/8/1k6/2b5/2pP4/8/5K2/8 b - d3 0 1",
    "8/5k2/8/2Pp4/2B5/1K6/8/8 w - d6 0 1",
    6, 1440467
)]
#[case::short_castling_gives_check(
    "5k2/8/8/8/8/8/8/4K2R w K - 0 1",
    "4k2r/8/8/8/8/8/8/5K2 b k - 0 1",
    6, 661072
)]
#[case::long_castling_gives_check(
    "3k4/8/8/8/8/8/8/R3K3 w Q - 0 1",
    "r3k3/8/8/8/8/8/8/3K4 b q - 0 1",
    6, 803711
)]
#[case::castling_losing_rights_due_to_rook_capture(
    "r3k2r/1b4bq/8/8/8/8/7B/R3K2R w KQkq - 0 1",
    "r3k2r/7b/8/8/8/8/1B4BQ/R3K2R b KQkq - 0 1",
    4, 1274206
)]
#[case::castling_prevented(
    "r3k2r/8/3Q4/8/8/5q2/8/R3K2R b KQkq - 0 1",
    "r3k2r/8/5Q2/8/8/3q4/8/R3K2R w KQkq - 0 1",
    4, 1720476
)]
#[case::promote_out_of_check(
    "2K2r2/4P3/8/8/8/8/8/3k4 w - - 0 1",
    "3K4/8/8/8/8/8/4p3/2k2R2 b - - 0 1",
    6, 3821001
)]
#[case::discovered_check(
    "8/8/1P2K3/8/2n5/1q6/8/5k2 b - - 0 1",
    "5K2/8/1Q6/2N5/8/1p2k3/8/8 w - - 0 1",
    5, 1004658
)]
#[case::promote_to_give_check(
    "4k3/1P6/8/8/8/8/K7/8 w - - 0 1",
    "8/k7/8/8/8/8/1p6/4K3 b - - 0 1",
    6, 217342
)]
#[case::underpromote_to_check(
    "8/P1k5/K7/8/8/8/8/8 w - - 0 1",
    "8/8/8/8/8/k7/p1K5/8 b - - 0 1",
    6, 92683
)]
#[case::self_stalemate(
    "K1k5/8/P7/8/8/8/8/8 w - - 0 1",
    "8/8/8/8/8/p7/8/k1K5 b - - 0 1",
    6, 2217
)]
#[case::stalemate_checkmate(
    "8/k1P5/8/1K6/8/8/8/8 w - - 0 1",
    "8/8/8/8/1k6/8/K1p5/8 b - - 0 1",
    7, 567584
)]
#[case::double_check(
    "8/8/2k5/5q2/5n2/8/5K2/8 b - - 0 1",
    "8/5k2/8/5N2/5Q2/2K5/8/8 w - - 0 1",
    4, 23527
)]
fn position_pair(
        #[case] fen_1: &str,
        #[case] fen_2: &str,
        #[case] depth: usize,
        #[case] expected: usize) {
    let actual_1 = perft(fen_1, depth);
    let actual_2 = perft(fen_2, depth);

    assert_that!(actual_1).is_equal_to(expected);
    assert_that!(actual_2).is_equal_to(expected);
}

#[rstest]
// The following tests are generic complicated positions checked against
// Stockfish's results (https://stockfishchess.org/).
#[case("r1bqkb1r/pppp1ppp/2n2n2/4p3/2B1P3/2N2N2/PPPP1PPP/R1BQK2R b KQkq - 0 1", 5, 33710495)]
#[case("r1bq1rk1/pppp1pbp/2n2np1/4p3/2BPP3/2N1BN2/PPP2PPP/R2QK2R b KQ - 0 1", 5, 47610999)]
#[case("r1bq1rk1/p1pp1pbp/1p3np1/8/2BBP3/2N5/PPP2PPP/R2QK2R w KQ - 0 1", 5, 57832256)]
#[case("r1bq1rk1/p2p1p1p/1p3bp1/3N4/3B4/8/PPP2PPP/R2QK2R b KQ - 0 1", 5, 21002927)]
#[case("r5k1/pb1prp1p/1p4p1/8/6N1/6P1/PPP2P1P/R4RK1 w - - 0 1", 5, 11073221)]
#[case("6k1/p2p1p1p/1p4p1/2P5/1P6/5rP1/P6P/R5K1 w - - 0 1", 6, 57454543)]
#[case("r5k1/P2p1p1p/6p1/8/8/6P1/7P/R5K1 w - - 0 1", 6, 33095154)]
// Various positions taken from Carlsen - Nepomniachtchi World Championship
// Match 2021.
#[case("r1bqkb1r/pppn1ppp/8/3pN3/3Pn3/3B4/PPP2PPP/RNBQK2R w KQkq - 1 6", 4, 2374360)]
#[case("r2qkb1r/pppb1ppp/8/3p4/3P4/3B4/PPPn1PPP/R1BQK2R w KQkq - 0 8", 5, 46821496)]
#[case("r2qk2r/pppb1pp1/3b4/3p3p/3P4/3B4/PPPB1PPP/R3QRK1 b kq - 1 10", 5, 10409263)]
#[case("4rk2/pppb1pp1/3q3r/3p2Qp/3P4/3B4/PPP2PPP/4RRK1 b - - 5 15", 4, 4184479)]
#[case("5k2/pp1b1pp1/2p2q1r/3p3p/3P4/3BQ3/PPP2PPP/4R1K1 w - - 4 19", 5, 61487637)]
#[case("5k2/p2b1pp1/2p2q1r/1p6/2BP3p/Q6P/PP3PP1/4R1K1 b - - 1 22", 5, 7552362)]
#[case("3q2k1/Q4pp1/2p1R3/1p6/3P3p/7P/PP3PP1/6K1 b - - 0 27", 5, 12608371)]
#[case("6k1/6p1/8/1p6/3PQ2p/1P5P/q5PK/8 w - - 0 34", 6, 69178418)]
// More positions from Viswanathan Anand vs Adams Micheal from Oakham YM, where
// double queen-side castle occurred.
#[case("rn1qkbnr/pp2ppp1/2p3bp/8/3P3P/5NN1/PPP2PP1/R1BQKB1R b KQkq - 1 7", 5, 37059409)]
#[case("r3kbnr/ppqnppp1/2p4p/7P/3P4/3Q1NN1/PPPB1PP1/R3K2R b KQkq - 2 11", 5, 71385843)]
#[case("k2r3r/ppq2pp1/2pbpn1p/4N2P/3P4/6P1/PPPBQP2/1K1R3R w - - 7 19", 4, 3356304)]
#[case("4r3/pk1qnr2/1pp1p2p/4PppP/1BPP2P1/8/PP4Q1/1K1R1R2 w - g6 0 33", 5, 63241667)]
#[case("4r3/1k3R2/1pp1q2n/p3P2p/2PPQ3/BP6/P7/1K1R4 b - - 0 40", 5, 16249459)]
#[case("1k2r3/3P4/1p6/p2QP1n1/6q1/1P6/PB5p/1KR5 b - - 0 48", 5, 75749146)]
fn generic_position(
        #[case] fen: &str,
        #[case] depth: usize,
        #[case] expected: usize) {
    let actual = perft(fen, depth);

    assert_that!(actual).is_equal_to(expected);
}
