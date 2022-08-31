use crate::args::{Args, Command};

use clap::Parser;

use kvarko_engine::StateEvaluator;

use kvarko_model::error::{FenError, AlgebraicError};
use kvarko_model::movement::{self, Move};
use kvarko_model::state::State;

use std::time::Instant;

mod args;

fn perft(fen: &str, depth: usize) -> Result<usize, FenError> {
    fn perft_rec(state: &mut State, depth: usize, moves: &mut Vec<Move>)
            -> usize {
        if depth == 0 {
            return 1;
        }
    
        if depth == 1 {
            moves.clear();
            movement::list_moves_in(state.position(), moves);
            return moves.len();
        }
    
        let mut sum = 0;
    
        for mov in movement::list_moves(state.position()).0 {
            let revert_info = state.make_move(&mov);
            sum += perft_rec(state, depth - 1, moves);
            state.unmake_move(&mov, revert_info);
        }
    
        sum
    }

    let mut state = State::from_fen(fen)?;
    let mut moves = Vec::new();

    Ok(perft_rec(&mut state, depth, &mut moves))
}

fn eval(history: &str, depth: u32)
        -> Result<(f32, Option<Move>), AlgebraicError> {
    let mut state = State::initial();

    for algebraic in history.split_whitespace() {
        let mov = Move::parse_algebraic(state.position(), algebraic)?;
        state.make_move(&mov);
    }

    let mut engine = kvarko_engine::kvarko_engine(depth);
    Ok(engine.evaluate_state(&state, &mut Vec::new()))
}

fn main() {
    let args = Args::parse();

    match args.command {
        Command::Perft { fen, depth } => {
            let before = Instant::now();

            match perft(&fen, depth) {
                Ok(n) => {
                    let after = Instant::now();
                    let runtime = (after - before).as_secs_f64();
                    let nodes_per_second = n as f64 / runtime;

                    println!("{} leaf nodes.", n);
                    println!("Runtime: {:.03} s ({:.0} nodes/s)",
                        runtime, nodes_per_second);
                },
                Err(e) => {
                    eprintln!("Error with FEN: {}", e);
                }
            }
        },
        Command::Eval { history, depth } => {
            let before = Instant::now();

            match eval(&history, depth) {
                Ok((v, _mov)) => {
                    let after = Instant::now();
                    let runtime = (after - before).as_secs_f64();

                    println!("Evaluation: {}", v);
                    println!("Runtime: {:.03} s", runtime);
                },
                Err(e) => {
                    eprintln!("Error with algebraic notation: {}", e);
                }
            }
        }
    }
}
