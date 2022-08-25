use kvarko_model::movement::list_moves;
use kvarko_model::state::State;

fn perft_rec(state: &mut State, depth: usize) -> usize {
    if depth == 0 {
        return 1;
    }

    if depth == 1 {
        return list_moves(state.position()).0.len();
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

// Test positions by Martin Sedlak
// http://www.talkchess.com/forum3/viewtopic.php?t=47318

fn test_perft_pair(fen_1: &str, fen_2: &str, expected: usize, depth: usize) {
    assert_eq!(expected, perft(fen_1, depth));
    assert_eq!(expected, perft(fen_2, depth));
}

#[test]
fn avoid_illegal_en_passant_capture() {
    test_perft_pair(
        "8/5bk1/8/2Pp4/8/1K6/8/8 w - d6 0 1",
        "8/8/1k6/8/2pP4/8/5BK1/8 b - d3 0 1",
        824064, 6
    );
}

#[test]
fn en_passant_capture_checks_opponent() {
    test_perft_pair(
        "8/8/1k6/2b5/2pP4/8/5K2/8 b - d3 0 1",
        "8/5k2/8/2Pp4/2B5/1K6/8/8 w - d6 0 1",
        1440467, 6
    );
}

#[test]
fn short_castling_gives_check() {
    test_perft_pair(
        "5k2/8/8/8/8/8/8/4K2R w K - 0 1",
        "4k2r/8/8/8/8/8/8/5K2 b k - 0 1",
        661072, 6
    );
}

#[test]
fn long_castling_gives_check() {
    test_perft_pair(
        "3k4/8/8/8/8/8/8/R3K3 w Q - 0 1",
        "r3k3/8/8/8/8/8/8/3K4 b q - 0 1",
        803711, 6
    );
}

#[test]
fn castling_losing_rights_due_to_rook_capture() {
    test_perft_pair(
        "r3k2r/1b4bq/8/8/8/8/7B/R3K2R w KQkq - 0 1",
        "r3k2r/7b/8/8/8/8/1B4BQ/R3K2R b KQkq - 0 1",
        1274206, 4
    );
}

#[test]
fn castling_prevented() {
    test_perft_pair(
        "r3k2r/8/3Q4/8/8/5q2/8/R3K2R b KQkq - 0 1",
        "r3k2r/8/5Q2/8/8/3q4/8/R3K2R w KQkq - 0 1",
        1720476, 4
    );
}

#[test]
fn promote_out_of_check() {
    test_perft_pair(
        "2K2r2/4P3/8/8/8/8/8/3k4 w - - 0 1",
        "3K4/8/8/8/8/8/4p3/2k2R2 b - - 0 1",
        3821001, 6
    );
}

#[test]
fn discovered_check() {
    test_perft_pair(
        "8/8/1P2K3/8/2n5/1q6/8/5k2 b - - 0 1",
        "5K2/8/1Q6/2N5/8/1p2k3/8/8 w - - 0 1",
        1004658, 5
    );
}

#[test]
fn promote_to_give_check() {
    test_perft_pair(
        "4k3/1P6/8/8/8/8/K7/8 w - - 0 1",
        "8/k7/8/8/8/8/1p6/4K3 b - - 0 1",
        217342, 6
    );
}

#[test]
fn underpromote_to_check() {
    test_perft_pair(
        "8/P1k5/K7/8/8/8/8/8 w - - 0 1",
        "8/8/8/8/8/k7/p1K5/8 b - - 0 1",
        92683, 6
    );
}

#[test]
fn self_stalemate() {
    test_perft_pair(
        "K1k5/8/P7/8/8/8/8/8 w - - 0 1",
        "8/8/8/8/8/p7/8/k1K5 b - - 0 1",
        2217, 6
    );
}

#[test]
fn stalemate_checkmate() {
    test_perft_pair(
        "8/k1P5/8/1K6/8/8/8/8 w - - 0 1",
        "8/8/8/8/1k6/8/K1p5/8 b - - 0 1",
        567584, 7
    );
}

#[test]
fn double_check() {
    test_perft_pair(
        "8/8/2k5/5q2/5n2/8/5K2/8 b - - 0 1",
        "8/5k2/8/5N2/5Q2/2K5/8/8 w - - 0 1",
        23527, 4
    );
}

// The following tests are generic complicated positions checked against
// Stockfish's results (https://stockfishchess.org/).

#[test]
fn generic_position_1() {
    let fen = "r1bqkb1r/pppp1ppp/2n2n2/4p3/2B1P3/2N2N2/PPPP1PPP/R1BQK2R b \
        KQkq - 0 1";

    assert_eq!(33710495, perft(fen, 5));
}

#[test]
fn generic_position_2() {
    let fen = "r1bq1rk1/pppp1pbp/2n2np1/4p3/2BPP3/2N1BN2/PPP2PPP/R2QK2R b KQ \
        - 0 1";

    assert_eq!(47610999, perft(fen, 5));
}

#[test]
fn generic_position_3() {
    let fen = "r1bq1rk1/p1pp1pbp/1p3np1/8/2BBP3/2N5/PPP2PPP/R2QK2R w KQ - 0 1";

    assert_eq!(57832256, perft(fen, 5));
}

#[test]
fn generic_position_4() {
    let fen = "r1bq1rk1/p2p1p1p/1p3bp1/3N4/3B4/8/PPP2PPP/R2QK2R b KQ - 0 1";

    assert_eq!(21002927, perft(fen, 5));
}

#[test]
fn generic_position_5() {
    let fen = "r5k1/pb1prp1p/1p4p1/8/6N1/6P1/PPP2P1P/R4RK1 w - - 0 1";

    assert_eq!(11073221, perft(fen, 5));
}

#[test]
fn generic_position_6() {
    let fen = "6k1/p2p1p1p/1p4p1/2P5/1P6/5rP1/P6P/R5K1 w - - 0 1";

    assert_eq!(57454543, perft(fen, 6));
}

#[test]
fn generic_position_7() {
    let fen = "r5k1/P2p1p1p/6p1/8/8/6P1/7P/R5K1 w - - 0 1";

    assert_eq!(33095154, perft(fen, 6));
}

// Various positions taken from Carlsen - Nepomniachtchi World Championship
// Match 2021.

#[test]
fn generic_position_8() {
    let fen = "r1bqkb1r/pppn1ppp/8/3pN3/3Pn3/3B4/PPP2PPP/RNBQK2R w KQkq - 1 6";

    assert_eq!(2374360, perft(fen, 4));
}

#[test]
fn generic_position_9() {
    let fen = "r2qkb1r/pppb1ppp/8/3p4/3P4/3B4/PPPn1PPP/R1BQK2R w KQkq - 0 8";

    assert_eq!(46821496, perft(fen, 5));
}

#[test]
fn generic_position_10() {
    let fen = "r2qk2r/pppb1pp1/3b4/3p3p/3P4/3B4/PPPB1PPP/R3QRK1 b kq - 1 10";

    assert_eq!(10409263, perft(fen, 5));
}

#[test]
fn generic_position_11() {
    let fen = "4rk2/pppb1pp1/3q3r/3p2Qp/3P4/3B4/PPP2PPP/4RRK1 b - - 5 15";

    assert_eq!(4184479, perft(fen, 4));
}

#[test]
fn generic_position_12() {
    let fen = "5k2/pp1b1pp1/2p2q1r/3p3p/3P4/3BQ3/PPP2PPP/4R1K1 w - - 4 19";

    assert_eq!(61487637, perft(fen, 5));
}

#[test]
fn generic_position_13() {
    let fen = "5k2/p2b1pp1/2p2q1r/1p6/2BP3p/Q6P/PP3PP1/4R1K1 b - - 1 22";

    assert_eq!(7552362, perft(fen, 5));
}

#[test]
fn generic_position_14() {
    let fen = "3q2k1/Q4pp1/2p1R3/1p6/3P3p/7P/PP3PP1/6K1 b - - 0 27";

    assert_eq!(12608371, perft(fen, 5));
}

#[test]
fn generic_position_15() {
    let fen = "6k1/6p1/8/1p6/3PQ2p/1P5P/q5PK/8 w - - 0 34";

    assert_eq!(69178418, perft(fen, 6));
}

// More positions from Viswanathan Anand vs Adams Micheal from Oakham YM, where
// double queen-side castle occurred.

#[test]
fn generic_position_16() {
    let fen =
        "rn1qkbnr/pp2ppp1/2p3bp/8/3P3P/5NN1/PPP2PP1/R1BQKB1R b KQkq - 1 7";

    assert_eq!(37059409, perft(fen, 5));
}

#[test]
fn generic_position_17() {
    let fen =
        "r3kbnr/ppqnppp1/2p4p/7P/3P4/3Q1NN1/PPPB1PP1/R3K2R b KQkq - 2 11";

    assert_eq!(71385843, perft(fen, 5));
}

#[test]
fn generic_position_18() {
    let fen = "k2r3r/ppq2pp1/2pbpn1p/4N2P/3P4/6P1/PPPBQP2/1K1R3R w - - 7 19";

    assert_eq!(3356304, perft(fen, 4));
}

#[test]
fn generic_position_19() {
    let fen = "4r3/pk1qnr2/1pp1p2p/4PppP/1BPP2P1/8/PP4Q1/1K1R1R2 w - g6 0 33";

    assert_eq!(63241667, perft(fen, 5));
}

#[test]
fn generic_position_20() {
    let fen = "4r3/1k3R2/1pp1q2n/p3P2p/2PPQ3/BP6/P7/1K1R4 b - - 0 40";

    assert_eq!(16249459, perft(fen, 5));
}

#[test]
fn generic_position_21() {
    let fen = "1k2r3/3P4/1p6/p2QP1n1/6q1/1P6/PB5p/1KR5 b - - 0 48";

    assert_eq!(75749146, perft(fen, 5));
}
