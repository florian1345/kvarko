use kvarko_engine::{KvarkoEngine, StateEvaluatingController};

use kvarko_model::board::Bitboard;
use kvarko_model::game::Controller;
use kvarko_model::hash::ZobristHasher;
use kvarko_model::movement::Move;
use kvarko_model::piece::Piece;
use kvarko_model::state::State;

type Kvarko = StateEvaluatingController<KvarkoEngine<ZobristHasher<u64>>>;

fn kvarko(depth: u32) -> Kvarko {
    kvarko_engine::kvarko_engine(depth, None)
}

fn assert_finds_move(fen: &str, depth: u32, mov: Move) {
    let mut kvarko = kvarko(depth);
    let state = State::from_fen(fen).unwrap();
    let kvarko_move = kvarko.make_move(&state);

    assert_eq!(mov, kvarko_move);
}

#[test]
fn mate_in_2() {
    // Board (white to move):
    // ┌───┬───┬───┬───┬───┬───┬───┬───┐
    // │   │   │   │   │   │   │ k │   │
    // ├───┼───┼───┼───┼───┼───┼───┼───┤
    // │   │   │   │   │   │ p │ p │ p │
    // ├───┼───┼───┼───┼───┼───┼───┼───┤
    // │ q │   │   │   │   │   │   │   │
    // ├───┼───┼───┼───┼───┼───┼───┼───┤
    // │   │   │   │   │   │ b │   │   │
    // ├───┼───┼───┼───┼───┼───┼───┼───┤
    // │ p │   │   │   │ r │   │   │   │
    // ├───┼───┼───┼───┼───┼───┼───┼───┤
    // │ P │   │   │   │   │   │   │ P │
    // ├───┼───┼───┼───┼───┼───┼───┼───┤
    // │   │ P │   │ R │   │ P │ P │   │
    // ├───┼───┼───┼───┼───┼───┼───┼───┤
    // │   │   │   │ R │   │   │ K │   │
    // └───┴───┴───┴───┴───┴───┴───┴───┘
    //
    // White has a forced checkmate in 2 by moving the rook on d2 to d8.
    // Black's only move is to block with the rook on e4, which white can
    // capture to deliver checkmate. There is no other move white could make to
    // obtain a shorter or equally long forced checkmate.

    let fen = "6k1/5ppp/q7/5b2/p3r3/P6P/1P1R1PP1/3R2K1 w - - 0 1";
    let best_move = Move::Ordinary {
        moved: Piece::Rook,
        captured: None,
        delta_mask: Bitboard(0x0800000000000800)
    };

    assert_finds_move(fen, 4, best_move);
}

#[test]
fn mate_in_3() {
    // Board (black to move):
    // ┌───┬───┬───┬───┬───┬───┬───┬───┐
    // │   │   │   │   │   │   │ K │   │
    // ├───┼───┼───┼───┼───┼───┼───┼───┤
    // │ r │   │   │   │   │   │   │   │
    // ├───┼───┼───┼───┼───┼───┼───┼───┤
    // │   │   │   │   │ k │   │   │   │
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
    // A basic checkmate with .. Kf6 ; Kh8 Kg6 ; Kg8 Ra8#.

    let fen = "6K1/r7/4k3/8/8/8/8/8 b - - 1 1";
    let best_move = Move::Ordinary {
        moved: Piece::King,
        captured: None,
        delta_mask: Bitboard(0x0000300000000000)
    };

    assert_finds_move(fen, 6, best_move);
}

#[test]
fn fork() {
    // Board (white to move):
    // ┌───┬───┬───┬───┬───┬───┬───┬───┐
    // │ r │   │ b │ q │ k │   │   │ r │
    // ├───┼───┼───┼───┼───┼───┼───┼───┤
    // │ p │ p │ p │ p │   │ p │ p │ p │
    // ├───┼───┼───┼───┼───┼───┼───┼───┤
    // │   │   │ n │   │   │ n │   │   │
    // ├───┼───┼───┼───┼───┼───┼───┼───┤
    // │   │   │ b │   │ p │   │ N │   │
    // ├───┼───┼───┼───┼───┼───┼───┼───┤
    // │   │   │ B │   │ P │   │   │   │
    // ├───┼───┼───┼───┼───┼───┼───┼───┤
    // │   │   │   │   │   │   │   │   │
    // ├───┼───┼───┼───┼───┼───┼───┼───┤
    // │ P │ P │ P │ P │   │ P │ P │ P │
    // ├───┼───┼───┼───┼───┼───┼───┼───┤
    // │ R │ N │ B │ Q │ K │   │   │ R │
    // └───┴───┴───┴───┴───┴───┴───┴───┘
    //
    // A fried liver attack where black did not realize what is going on. White
    // can now fork the black queen and kingside rook by moving the knight from
    // g5 to f7, winning material.

    let fen =
        "r1bqk2r/pppp1ppp/2n2n2/2b1p1N1/2B1P3/8/PPPP1PPP/RNBQK2R w KQkq - 0 1";
    let best_move = Move::Ordinary {
        moved: Piece::Knight,
        captured: Some(Piece::Pawn),
        delta_mask: Bitboard(0x0020004000000000)
    };

    assert_finds_move(fen, 4, best_move);
}

#[test]
fn capture_defended_piece_with_subsequent_fork() {
    // Board (black to move):
    // ┌───┬───┬───┬───┬───┬───┬───┬───┐
    // │   │   │   │   │   │ r │   │   │
    // ├───┼───┼───┼───┼───┼───┼───┼───┤
    // │   │   │   │   │   │   │   │ k │
    // ├───┼───┼───┼───┼───┼───┼───┼───┤
    // │   │ b │   │   │   │   │   │ p │
    // ├───┼───┼───┼───┼───┼───┼───┼───┤
    // │   │   │   │   │   │ p │ p │   │
    // ├───┼───┼───┼───┼───┼───┼───┼───┤
    // │   │   │   │   │   │   │   │   │
    // ├───┼───┼───┼───┼───┼───┼───┼───┤
    // │   │   │   │   │ N │ P │   │ P │
    // ├───┼───┼───┼───┼───┼───┼───┼───┤
    // │   │ B │   │ n │   │   │ P │ K │
    // ├───┼───┼───┼───┼───┼───┼───┼───┤
    // │   │   │   │   │ R │   │   │   │
    // └───┴───┴───┴───┴───┴───┴───┴───┘
    //
    // Black can capture the knight on e3 with the bishop. If white atempts to
    // recapture with the rook, black has a fork with the knight on f1. So,
    // this move wins material.

    let fen = "5r2/7k/1b5p/5pp1/8/4NP1P/1B1n2PK/4R3 b - - 0 1";
    let best_move = Move::Ordinary {
        moved: Piece::Bishop,
        captured: Some(Piece::Knight),
        delta_mask: Bitboard(0x0000020000100000)
    };

    assert_finds_move(fen, 6, best_move);
}

#[test]
fn forced_capture() {
    // Board (white to move):
    // ┌───┬───┬───┬───┬───┬───┬───┬───┐
    // │ k │ b │   │   │   │   │   │   │
    // ├───┼───┼───┼───┼───┼───┼───┼───┤
    // │ p │   │   │   │   │   │   │   │
    // ├───┼───┼───┼───┼───┼───┼───┼───┤
    // │   │ p │   │   │   │   │   │   │
    // ├───┼───┼───┼───┼───┼───┼───┼───┤
    // │   │   │   │   │   │   │   │   │
    // ├───┼───┼───┼───┼───┼───┼───┼───┤
    // │   │   │   │   │   │   │ Q │   │
    // ├───┼───┼───┼───┼───┼───┼───┼───┤
    // │   │   │ P │ B │   │   │   │   │
    // ├───┼───┼───┼───┼───┼───┼───┼───┤
    // │ P │ P │   │   │   │   │   │   │
    // ├───┼───┼───┼───┼───┼───┼───┼───┤
    // │   │ K │   │   │ R │   │   │   │
    // └───┴───┴───┴───┴───┴───┴───┴───┘
    //
    // White can give check by moving the bishop to e4. Black's only move will
    // be to capture the bishop with the queen, allowing white to capture the
    // queen with the rook.

    let fen = "kb6/p7/1p6/8/6q1/2PB4/PP6/1K2R3 w - - 0 1";
    let best_move = Move::Ordinary {
        moved: Piece::Bishop,
        captured: None,
        delta_mask: Bitboard(0x0000000010080000)
    };

    assert_finds_move(fen, 4, best_move);
}

#[test]
fn skewer() {
    // Board (white to move):
    // ┌───┬───┬───┬───┬───┬───┬───┬───┐
    // │   │   │   │   │ k │   │   │ r │
    // ├───┼───┼───┼───┼───┼───┼───┼───┤
    // │ p │ p │ n │   │   │ p │ p │ p │
    // ├───┼───┼───┼───┼───┼───┼───┼───┤
    // │   │ q │ p │   │   │ n │ b │   │
    // ├───┼───┼───┼───┼───┼───┼───┼───┤
    // │   │   │ b │   │   │   │   │   │
    // ├───┼───┼───┼───┼───┼───┼───┼───┤
    // │   │   │ P │   │   │   │ Q │   │
    // ├───┼───┼───┼───┼───┼───┼───┼───┤
    // │   │ P │   │   │   │ N │ B │ P │
    // ├───┼───┼───┼───┼───┼───┼───┼───┤
    // │ P │   │   │   │   │ P │ P │   │
    // ├───┼───┼───┼───┼───┼───┼───┼───┤
    // │   │   │   │ R │   │ B │ K │   │
    // └───┴───┴───┴───┴───┴───┴───┴───┘
    //
    // White can move the queen to c8, skewering the king and rook, leading to
    // won material.

    let fen =
        "4k2r/ppn2ppp/1qp2nb1/2b5/2P3Q1/1P3NBP/P4PP1/3R1BK1 w - - 0 1";
    let best_move = Move::Ordinary {
        moved: Piece::Queen,
        captured: None,
        delta_mask: Bitboard(0x0400000040000000)
    };

    assert_finds_move(fen, 4, best_move);
}
