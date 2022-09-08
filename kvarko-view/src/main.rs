use crate::state::{GameStateManager, MenuState};

use ggez::conf::WindowMode;
use ggez::{ContextBuilder, GameResult};
use ggez::event;
use ggez::graphics::{self, FilterMode, Rect};

mod sync;

pub mod state;
pub mod ui;

fn main() -> GameResult {
    let (mut ctx, event_loop) = ContextBuilder::new("Chess", "quarkey")
        .build()?;

    graphics::set_default_filter(&mut ctx, FilterMode::Linear);
    graphics::set_mode(&mut ctx,
        WindowMode::default().dimensions(1280.0, 720.0))?;
    graphics::set_screen_coordinates(&mut ctx,
        Rect::new(0.0, 0.0, 1280.0, 720.0))?;

    let menu_state = MenuState::new(&ctx);
    let manager = GameStateManager::new(menu_state);

    event::run(ctx, event_loop, manager)
}
