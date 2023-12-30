use std::ops::{Add, AddAssign};
use std::thread;
use std::time::Duration;

use kvarko_engine_old::{KvarkoEngine as OldKvarkoEngine, StateEvaluatingController as OldStateEvaluatingController};
use kvarko_engine_old::depth::IterativeDeepeningForDuration as OldIterativeDeepeningForDuration;
use kvarko_model_old::game::Controller as OldController;
use kvarko_model_old::hash::ZobristHasher as OldZobristHasher;
use kvarko_model_old::state::State as OldState;

use rayon::prelude::*;
use rayon::ThreadPoolBuilder;

use kvarko_engine::{KvarkoEngine, StateEvaluatingController};
use kvarko_engine::depth::IterativeDeepeningForDuration;
use kvarko_model::game::Controller;
use kvarko_model::hash::ZobristHasher;
use kvarko_model::player::Player;
use kvarko_model::state::{Outcome, State};

use crate::openings::TESTED_OPENINGS;

mod openings;
mod validation;

const DEEPEN_FOR: Duration = Duration::from_millis(10);

trait ControllerAdapter {

    fn make_move(&mut self, history: &[String]) -> String;
}

type Kvarko = StateEvaluatingController<KvarkoEngine<ZobristHasher<u64>, IterativeDeepeningForDuration>>;

impl ControllerAdapter for Kvarko {
    fn make_move(&mut self, history: &[String]) -> String {
        let state = State::from_algebraic_history(history.iter()).unwrap();
        let mov = Controller::make_move(self, &state);
        mov.to_algebraic(state.position()).unwrap()
    }
}

fn kvarko() -> Box<dyn ControllerAdapter> {
    Box::new(kvarko_engine::kvarko_engine(DEEPEN_FOR, None))
}

type OldKvarko = OldStateEvaluatingController<OldKvarkoEngine<OldZobristHasher<u64>, OldIterativeDeepeningForDuration>>;

impl ControllerAdapter for OldKvarko {
    fn make_move(&mut self, history: &[String]) -> String {
        let state = OldState::from_algebraic_history(history.iter()).unwrap();
        let mov = OldController::make_move(self, &state);
        mov.to_algebraic(state.position()).unwrap()
    }
}

fn kvarko_old() -> Box<dyn ControllerAdapter> {
    Box::new(kvarko_engine_old::kvarko_engine(DEEPEN_FOR, None))
}

#[derive(Clone, Copy)]
struct Comparison {
    new_score: u32,
    old_score: u32
}

impl AddAssign for Comparison {
    fn add_assign(&mut self, rhs: Comparison) {
        self.new_score += rhs.new_score;
        self.old_score += rhs.old_score;
    }
}

impl Add for Comparison {
    type Output = Comparison;

    fn add(mut self, rhs: Comparison) -> Comparison {
        self += rhs;
        self
    }
}

fn test_opening_with_controllers(tested_opening: &str,
        mut white: Box<dyn ControllerAdapter>,
        mut black: Box<dyn ControllerAdapter>) -> Outcome {
    let mut history = tested_opening.split(' ')
        .map(|slice| slice.to_owned())
        .collect::<Vec<_>>();

    loop {
        let state: State<ZobristHasher<u64>> =
            State::from_algebraic_history(history.iter()).unwrap();

        if let Some(outcome) = state.compute_outcome() {
            return outcome;
        }

        let turn = match state.position().turn() {
            Player::White => white.make_move(&history),
            Player::Black => black.make_move(&history)
        };

        history.push(turn);
    }
}

fn test_opening(tested_opening: &str) -> Comparison {
    let mut old_score = 0;
    let mut new_score = 0;

    match test_opening_with_controllers(tested_opening, kvarko(), kvarko_old()) {
        Outcome::Victory(Player::White) => new_score += 2,
        Outcome::Victory(Player::Black) => old_score += 2,
        Outcome::Draw => {
            new_score += 1;
            old_score += 1;
        }
    }

    match test_opening_with_controllers(tested_opening, kvarko_old(), kvarko()) {
        Outcome::Victory(Player::White) => old_score += 2,
        Outcome::Victory(Player::Black) => new_score += 2,
        Outcome::Draw => {
            new_score += 1;
            old_score += 1;
        }
    }

    println!("Tested opening {}", tested_opening);

    Comparison {
        new_score,
        old_score
    }
}

fn build_thread_pool(num_threads: usize) {
    println!("Using {} threads.", num_threads);

    ThreadPoolBuilder::new()
        .num_threads(num_threads)
        .build_global()
        .unwrap();
}

fn main() {
    let num_threads = thread::available_parallelism().unwrap().get();

    build_thread_pool(num_threads);

    if let Err(error) = validation::validate_openings(TESTED_OPENINGS) {
        eprintln!("{}", error);
        return;
    }

    let result = TESTED_OPENINGS.into_par_iter()
        .map(|&opening| test_opening(opening))
        .reduce(|| Comparison { new_score: 0, old_score: 0 }, Add::add);

    println!("New: {}", result.new_score);
    println!("Old: {}", result.old_score);
}
