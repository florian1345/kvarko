use crate::args::{Args, Command};

use clap::Parser;

use kvarko_model::error::FenError;
use kvarko_model::movement;
use kvarko_model::state::State;

use std::time::Instant;

mod args;

fn perft(fen: &str, depth: usize) -> Result<usize, FenError> {
    fn perft_rec(state: &mut State, depth: usize) -> usize {
        if depth == 0 {
            return 1;
        }
    
        if depth == 1 {
            return movement::list_moves(state.position()).0.len();
        }
    
        let mut sum = 0;
    
        for mov in movement::list_moves(state.position()).0 {
            let revert_info = state.make_move(&mov);
            sum += perft_rec(state, depth - 1);
            state.unmake_move(&mov, revert_info);
        }
    
        sum
    }

    let mut state = State::from_fen(fen)?;
    Ok(perft_rec(&mut state, depth))
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
        }
    }
}
