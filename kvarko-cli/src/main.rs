use crate::args::{Args, Command};

use clap::Parser;

use kvarko_engine::StateEvaluator;

use kvarko_model::error::{FenError, AlgebraicError};
use kvarko_model::hash::ZobristHasher;
use kvarko_model::movement::{self, Move};
use kvarko_model::state::State;

use std::time::Instant;

mod args;
mod book;

fn perft(fen: &str, depth: usize) -> Result<usize, FenError> {
    fn perft_rec(state: &mut State<ZobristHasher<u64>>, depth: usize,
            moves: &mut Vec<Move>) -> usize {
        if depth == 0 {
            return 1;
        }
    
        if depth == 1 {
            return movement::count_moves(state.position()).0;
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
    let mut state: State<ZobristHasher<u64>> = State::initial();

    for algebraic in history.split_whitespace() {
        let mov = Move::parse_algebraic(state.position(), algebraic)?;
        state.make_move(&mov);
    }

    let mut engine = kvarko_engine::kvarko_engine(depth, None);
    Ok(engine.evaluate_state(&mut state))
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
        },
        Command::MakeBook { in_file, out_file, min_occurrences, max_depth } => {
            match book::make_book(
                    in_file, out_file, min_occurrences, max_depth) {
                Ok(len) => {
                    println!("Successfully created opening book with {} \
                        positions.", len);
                },
                Err(e) => {
                    // TODO proper display for error
                    println!("Error during opening book creation: {:?}", e);
                }
            }
        }
    }
}
