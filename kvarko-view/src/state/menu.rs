use std::fs::File;
use std::thread;

use ggez::{Context, GameResult};
use ggez::event::{EventHandler, MouseButton};
use ggez::graphics::{self, Color, Drawable, DrawParam, Rect};

use kvarko_engine::book::OpeningBook;

use kvarko_model::game::GameBuilder;
use kvarko_model::state::State;

use crate::state::{GameplayState, GameState, Transition, DynGameState};
use crate::ui::{Button, Label, Ui, Alignment, AxisAlignment};

#[derive(Clone)]
struct GameSettings {
    white_kvarko: bool,
    black_kvarko: bool,
    depth: u32,
    use_opening_book: bool,
    start: bool
}

pub struct MenuState {
    ui: Ui<GameSettings>
}

impl MenuState {
    pub fn new(ctx: &Context) -> MenuState {
        let screen = graphics::screen_coordinates(ctx);
        let mut ui = Ui::new(GameSettings {
            white_kvarko: false,
            black_kvarko: true,
            depth: 6,
            use_opening_book: true,
            start: false
        });

        ui.add_element(Label::new(
            Rect::new(
                screen.w * 0.3,
                screen.h * 0.05,
                screen.w * 0.4,
                screen.h * 0.1),
            Color::WHITE, "Kvarko View".to_owned(), Alignment::CENTER, 32.0));

        ui.add_element(Label::new(
            Rect::new(
                screen.w * 0.25,
                screen.h * 0.25,
                screen.w * 0.25,
                screen.h * 0.07),
            Color::WHITE,
            "White".to_owned(),
            Alignment::new(
                AxisAlignment::Min {
                    margin: 0.0
                }, 
                AxisAlignment::Center
            ),
            24.0));

        let white_button = ui.add_element(Button::new(
            Rect::new(
                screen.w * 0.55,
                screen.h * 0.25,
                screen.w * 0.2,
                screen.h * 0.07
            ), Color::WHITE, "Human".to_owned(), 24.0));

        ui.add_element(Label::new(
            Rect::new(
                screen.w * 0.25,
                screen.h * 0.35,
                screen.w * 0.25,
                screen.h * 0.07),
            Color::WHITE,
            "Black".to_owned(),
            Alignment::new(
                AxisAlignment::Min {
                    margin: 0.0
                }, 
                AxisAlignment::Center
            ),
            24.0));

        let black_button = ui.add_element(Button::new(
            Rect::new(
                screen.w * 0.55,
                screen.h * 0.35,
                screen.w * 0.2,
                screen.h * 0.07
            ), Color::WHITE, "Kvarko".to_owned(), 24.0));

        ui.add_element(Label::new(
            Rect::new(
                screen.w * 0.25,
                screen.h * 0.45,
                screen.w * 0.25,
                screen.h * 0.07),
            Color::WHITE,
            "Ply depth".to_owned(),
            Alignment::new(
                AxisAlignment::Min {
                    margin: 0.0
                }, 
                AxisAlignment::Center
            ),
            24.0));

        let depth_button = ui.add_element(Button::new(
            Rect::new(
                screen.w * 0.55,
                screen.h * 0.45,
                screen.w * 0.2,
                screen.h * 0.07
            ), Color::WHITE, "6".to_owned(), 24.0));

        ui.add_element(Label::new(
            Rect::new(
                screen.w * 0.25,
                screen.h * 0.55,
                screen.w * 0.25,
                screen.h * 0.07),
            Color::WHITE,
            "Opening book".to_owned(),
            Alignment::new(
                AxisAlignment::Min {
                    margin: 0.0
                }, 
                AxisAlignment::Center
            ),
            24.0));

        let book_button = ui.add_element(Button::new(
            Rect::new(
                screen.w * 0.55,
                screen.h * 0.55,
                screen.w * 0.2,
                screen.h * 0.07
            ), Color::WHITE, "Yes".to_owned(), 24.0));

        let start_button = ui.add_element(Button::new(
            Rect::new(
                screen.w * 0.375,
                screen.h * 0.65,
                screen.w * 0.25,
                screen.h * 0.07
            ), Color::WHITE, "Start".to_owned(), 24.0));

        // TODO reduce code duplication

        ui.set_on_clicked_action(white_button, move |_, ui, _| {
            let new_white_kvarko = !ui.data_mut().white_kvarko;
            let new_text = if new_white_kvarko {
                "Kvarko"
            }
            else {
                "Human"
            };

            ui.data_mut().white_kvarko = new_white_kvarko;
            ui.element_mut::<Button>(white_button)
                .set_text(new_text.to_owned());
        });

        ui.set_on_clicked_action(black_button, move |_, ui, _| {
            let new_black_kvarko = !ui.data().black_kvarko;
            let new_text = if new_black_kvarko {
                "Kvarko"
            }
            else {
                "Human"
            };

            ui.data_mut().black_kvarko = new_black_kvarko;
            ui.element_mut::<Button>(black_button)
                .set_text(new_text.to_owned());
        });

        ui.set_on_clicked_action(depth_button, move |_, ui, _| {
            let new_depth = (ui.data().depth % 10) + 2;
            let new_text = new_depth.to_string();

            ui.data_mut().depth = new_depth;
            ui.element_mut::<Button>(depth_button).set_text(new_text);
        });

        ui.set_on_clicked_action(book_button, move |_, ui, _| {
            let new_use_opening_book = !ui.data().use_opening_book;
            let new_text = if new_use_opening_book {
                "Yes"
            }
            else {
                "No"
            };

            ui.data_mut().use_opening_book = new_use_opening_book;
            ui.element_mut::<Button>(book_button)
                .set_text(new_text.to_owned());
        });

        ui.set_on_clicked_action(start_button, move |_, ui, _| {
            ui.data_mut().start = true;
        });

        MenuState { ui }
    }
}

impl EventHandler for MenuState {
    fn draw(&mut self, ctx: &mut Context) -> GameResult<()> {
        graphics::clear(ctx, Color::BLACK);
        self.ui.draw(ctx, DrawParam::default())
    }

    fn update(&mut self, ctx: &mut Context) -> GameResult<()> {
        self.ui.update(ctx)
    }

    fn mouse_button_up_event(&mut self, ctx: &mut Context, button: MouseButton,
            x: f32, y: f32) {
        self.ui.mouse_button_up_event(ctx, button, x, y)
    }
}

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

impl GameState for MenuState {
    fn transition(&mut self, ctx: &mut Context) -> Transition {
        let settings = self.ui.data().clone();

        if settings.start {
            let (gameplay_state, view_observer, human_controller) =
                GameplayState::new(ctx, State::initial());
            let kvarko = if settings.white_kvarko || settings.black_kvarko {
                let opening_book = if settings.use_opening_book {
                    load_opening_book()
                }
                else {
                    None
                };

                Some(kvarko_engine::kvarko_engine(settings.depth, opening_book))
            }
            else {
                None
            };

            thread::spawn(move || {
                let mut game_builder = GameBuilder::new()
                    .with_observer(view_observer);

                if settings.white_kvarko {
                    game_builder =
                        game_builder.with_white(kvarko.clone().unwrap());
                }
                else {
                    game_builder =
                        game_builder.with_white(human_controller.clone());
                }

                if settings.black_kvarko {
                    game_builder = game_builder.with_black(kvarko.unwrap());
                }
                else {
                    game_builder = game_builder.with_black(human_controller);
                }

                let mut game = game_builder.build().unwrap();
                game.play_to_end()
            });

            Transition::Push(DynGameState::new(gameplay_state))
        }
        else {
            Transition::None
        }
    }
}
