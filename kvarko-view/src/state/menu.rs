use std::fs::File;
use std::thread;
use std::time::Duration;

use ggez::{Context, GameResult};
use ggez::event::{EventHandler, MouseButton};
use ggez::graphics::{self, Color, Drawable, DrawParam, Rect};

use kvarko_engine::book::OpeningBook;
use kvarko_model::game::GameBuilder;
use kvarko_model::state::State;

use crate::state::{DynGameState, GameplayState, GameState, Transition};
use crate::ui::{Alignment, AxisAlignment, Button, Label, Ui};

const DEEPEN_FOR_MAP: [(Duration, &str); 17] = [
    (Duration::from_millis(20), "20 ms"),
    (Duration::from_millis(30), "30 ms"),
    (Duration::from_millis(50), "50 ms"),
    (Duration::from_millis(100), "100 ms"),
    (Duration::from_millis(200), "200 ms"),
    (Duration::from_millis(300), "300 ms"),
    (Duration::from_millis(500), "500 ms"),
    (Duration::from_millis(700), "700 ms"),
    (Duration::from_secs(1), "1 s"),
    (Duration::from_millis(1500), "1.5 s"),
    (Duration::from_secs(2), "2 s"),
    (Duration::from_secs(3), "3 s"),
    (Duration::from_secs(5), "5 s"),
    (Duration::from_secs(7), "7 s"),
    (Duration::from_secs(10), "10 s"),
    (Duration::from_secs(15), "15 s"),
    (Duration::from_secs(20), "20 s")
];

fn get_next_deepen_for(current_deepen_for: Duration) -> Duration {
    let index = DEEPEN_FOR_MAP.iter()
        .map(|(deepen_for, _)| deepen_for)
        .enumerate()
        .find(|(_, &deepen_for)| deepen_for == current_deepen_for)
        .unwrap().0;
    let next_index = (index + 1) % DEEPEN_FOR_MAP.len();

    DEEPEN_FOR_MAP[next_index].0
}

fn get_deepen_for_label(deepen_for: Duration) -> String {
    DEEPEN_FOR_MAP.iter()
        .find(|(map_deepen_for, _)| map_deepen_for == &deepen_for)
        .unwrap().1.to_owned()
}

#[derive(Clone)]
struct GameSettings {
    white_kvarko: bool,
    black_kvarko: bool,
    deepen_for: Duration,
    use_opening_book: bool,
    start: bool
}

pub struct MenuState {
    ui: Ui<GameSettings>
}

impl MenuState {
    pub fn new(ctx: &Context) -> MenuState {
        let screen = graphics::screen_coordinates(ctx);
        let default_deepen_for = Duration::from_secs(3);
        let mut ui = Ui::new(GameSettings {
            white_kvarko: false,
            black_kvarko: true,
            deepen_for: default_deepen_for,
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
            "Deepen for".to_owned(),
            Alignment::new(
                AxisAlignment::Min {
                    margin: 0.0
                }, 
                AxisAlignment::Center
            ),
            24.0));

        let deepen_for_button = ui.add_element(Button::new(
            Rect::new(
                screen.w * 0.55,
                screen.h * 0.45,
                screen.w * 0.2,
                screen.h * 0.07
            ), Color::WHITE, get_deepen_for_label(default_deepen_for), 24.0));

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

        ui.set_on_clicked_action(deepen_for_button, move |_, ui, _| {
            let new_deepen_for = get_next_deepen_for(ui.data().deepen_for);
            let new_text = get_deepen_for_label(new_deepen_for);

            ui.data_mut().deepen_for = new_deepen_for;
            ui.element_mut::<Button>(deepen_for_button).set_text(new_text);
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

                Some(kvarko_engine::kvarko_engine(settings.deepen_for, opening_book))
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
