use std::env;
use std::fs::File;
use std::thread;

use crate::view::{GameplayState, MuxState};

use ggez::conf::WindowMode;
use ggez::{ContextBuilder, GameResult};
use ggez::event;
use ggez::graphics::{self, FilterMode, Rect};

use kvarko_engine::book::OpeningBook;

use kvarko_model::game::GameBuilder;
use kvarko_model::state::State;

mod sync;
mod view;

fn load_opening_book() -> Option<OpeningBook> {
    const OPENING_BOOK_FILE: &str = "resources/opening-book.kob";

    let mut file = match File::open(OPENING_BOOK_FILE) {
        Ok(file) => file,
        Err(_) => {
            println!("No opening book found.");
            return None;
        }
    };

    match OpeningBook::load(&mut file) {
        Ok(book) => {
            println!("Loaded opening book with {} positions.", book.len());
            Some(book)
        },
        Err(e) => {
            eprintln!("Error loading opening book: {:?}", e);
            None
        }
    }
}

fn main() -> GameResult {
    let mut args = env::args();
    args.next();
    let mut game = State::initial();

    if let Some(fen) = args.next() {
        game = State::from_fen(&fen).unwrap();
    }

    let (mut ctx, event_loop) = ContextBuilder::new("Chess", "quarkey")
        .build()?;
    let (gameplay_state, view_observer, human_controller) =
        GameplayState::new(game);
    let state = MuxState::new(gameplay_state);

    graphics::set_default_filter(&mut ctx, FilterMode::Linear);
    graphics::set_mode(&mut ctx,
        WindowMode::default().dimensions(1280.0, 720.0))?;
    graphics::set_screen_coordinates(&mut ctx,
        Rect::new(0.0, 0.0, 1280.0, 720.0))?;

    thread::spawn(|| {
        let mut game = GameBuilder::new()
            .with_observer(view_observer)
            .with_white(human_controller)
            .with_black(kvarko_engine::kvarko_engine(6, load_opening_book()))
            .build()
            .unwrap();

        game.play_to_end();
    });

    event::run(ctx, event_loop, state)
}
