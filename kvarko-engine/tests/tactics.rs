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
