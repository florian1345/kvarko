use crate::args::{Args, Command};

use clap::Parser;

use kvarko_engine::{KvarkoEngineMetadata, StateEvaluator, StateEvaluatorOutput};

use kvarko_model::error::{FenError, AlgebraicError};
use kvarko_model::hash::ZobristHasher;
use kvarko_model::movement::{self, Move};
use kvarko_model::state::{Position, State};

use std::time::{Duration, Instant};

mod args;
mod book;

fn perft(fen: &str, depth: usize) -> Result<usize, FenError> {
    fn perft_rec(state: &mut State<ZobristHasher<u64>>, depth: usize) -> usize {
        if depth == 0 {
            return 1;
        }
    
        if depth == 1 {
            return movement::count_moves(state.position()).0;
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

fn parse_history_to_state(history: &str) -> Result<State<ZobristHasher<u64>>, AlgebraicError> {
    let mut state: State<ZobristHasher<u64>> = State::initial();

    for algebraic in history.split_whitespace() {
        let mov = Move::parse_algebraic(state.position(), algebraic)?;
        state.make_move(&mov);
    }

    Ok(state)
}

fn evaluate_with_kvarko(state: &mut State<ZobristHasher<u64>>, deepen_for: Duration)
        -> StateEvaluatorOutput<KvarkoEngineMetadata> {
    kvarko_engine::kvarko_engine(deepen_for, None).evaluate_state(state)
}

fn log_eval_result(position: &Position, output: StateEvaluatorOutput<KvarkoEngineMetadata>,
        runtime: Duration) {
    let recommended_move_str = output.recommended_move.to_coordinate_notation(&position).unwrap();

    println!("Evaluation: {}", output.evaluation);
    println!("Recommended move: {}", recommended_move_str);
    println!("Runtime: {:.03} s", runtime.as_secs_f64());

    match output.metadata {
        KvarkoEngineMetadata::BookMove =>
            println!("Found book move"),
        KvarkoEngineMetadata::ComputedMove(metadata) =>
            println!("Search depth: {} ply", metadata.depth)
    }
}

fn run_eval_command(history: &str, deepen_for: Duration) -> Result<(), AlgebraicError> {
    let mut state = parse_history_to_state(history)?;
    let position = state.position().clone();
    let before = Instant::now();
    let output = evaluate_with_kvarko(&mut state, deepen_for);
    let runtime = Instant::now() - before;

    log_eval_result(&position, output, runtime);

    Ok(())
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
        Command::Eval { history, deepen_for } =>
            if let Err(e) = run_eval_command(&history, deepen_for) {
                eprintln!("Error with algebraic notation: {}", e);
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
