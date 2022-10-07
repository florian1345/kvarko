//! This module contains integration tests which traverse the move tree from a
//! given initial position to a given depth and assert that after making and
//! unmaking each move, the position and hash are the same.

use std::fmt::Debug;

use kvarko_model::hash::{PositionHasher, ZobristHasher};
use kvarko_model::movement::list_moves;
use kvarko_model::state::State;

fn test_hash_tree<H>(fen: &str, depth: u32)
where
    H: PositionHasher,
    H::Hash: Debug
{
    fn test_hash_tree_rec<H>(state: &mut State<H>, depth: u32) -> H::Hash
    where
        H: PositionHasher,
        H::Hash: Debug
    {
        let hash = state.position_hash();

        if depth == 0 {
            return hash;
        }

        for mov in list_moves(state.position()).0 {
            let revert_info = state.make_move(&mov);
            test_hash_tree_rec(state, depth - 1);
            state.unmake_move(&mov, revert_info);

            assert_eq!(hash, state.position_hash(),
                "Error at state `{}` move `{}`.", state.to_fen(),
                mov.to_coordinate_notation(state.position()).unwrap());
        }

        hash
    }

    let mut state: State<H> = State::from_fen(fen).unwrap();

    test_hash_tree_rec(&mut state, depth);
}

#[test]
fn zobrist_u64_initial() {
    let fen = "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1";

    test_hash_tree::<ZobristHasher<u64>>(fen, 5);
}

#[test]
fn zobrist_u64_pawn_endgame() {
    // To check some en-passant/promotion moves. Also, allows deeper search due
    // to lower branching factor.

    let fen = "7k/2p5/4P3/3P4/8/1p6/8/7K w - - 0 1";

    test_hash_tree::<ZobristHasher<u64>>(fen, 8);
}

#[test]
fn bug_test_1() {
    // This input caused a crash in the engine. It seems to be due to black
    // possibly being able to capture the white rook, messing up the castling
    // rights hash.

    let fen = "Q1bqkbnr/2pp2pp/8/pp2P3/3p4/8/PPPP1PPP/RNB1K2R b KQ - 0 12";

    test_hash_tree::<ZobristHasher<u64>>(fen, 5);
}
