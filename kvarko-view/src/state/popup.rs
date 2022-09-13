use ggez::{Context, GameResult};
use ggez::event::{EventHandler, MouseButton};
use ggez::graphics::{
    self,
    Color,
    Drawable,
    Rect,
    DrawParam, Mesh, DrawMode
};

use crate::state::{GameState, Transition, DynGameState};
use crate::ui::{Button, Label, Alignment, Ui};

const POPUP_BG_COLOR: Color = Color::new(0.0, 0.0, 0.0, 0.6);
const POPUP_TEXT_Y: f32 = 0.3;
const POPUP_TEXT_H: f32 = 0.05;
const POPUP_BUTTON_Y: f32 = 0.6;
const POPUP_BUTTON_MARGIN: f32 = 0.02;

pub type Action<S> = Box<dyn FnMut(&mut S)>;

pub struct PopupState<S> {
    parent: Option<S>,
    ui: Ui<Option<Action<S>>>
}

impl<S: 'static> PopupState<S> {

    /// Takes the displayed text and a list of buttons, and constructs a popup
    /// state. The buttons are repositioned to match the layout.
    pub fn new(ctx: &Context, parent: S, text: &str,
            buttons: Vec<(Button, Action<S>)>) -> PopupState<S> {
        let mut ui = Ui::new(None);
        let screen = graphics::screen_coordinates(ctx);
        let button_margin = POPUP_BUTTON_MARGIN * screen.w;
        let buttons_total_width = buttons.iter()
            .map(|(b, _)| b.dimensions().w)
            .sum::<f32>() + button_margin * (buttons.len() - 1) as f32;
        let mut x = (screen.w - buttons_total_width) * 0.5;
        let y = screen.h * POPUP_BUTTON_Y;

        for (mut button, callback) in buttons {
            let mut bounds = *button.dimensions();
            bounds.x = x;
            bounds.y = y;
            button.set_dimensions(bounds);
            x += bounds.w + button_margin;
            let id = ui.add_element(button);
            let mut callback = Some(callback);
            ui.set_on_clicked_action(id, move |_, ui, _| *ui.data_mut() = callback.take());
        }

        let text_y = POPUP_TEXT_Y * screen.h;
        let text_h = POPUP_TEXT_H * screen.h;
        let text_dims = Rect::new(0.0, text_y, screen.w, text_h);
        let label = Label::new(text_dims,
            Color::WHITE, text.to_owned(), Alignment::CENTER, text_h);

        ui.add_element(label);

        PopupState {
            parent: Some(parent),
            ui
        }
    }
}

fn draw_param(x: f32, y: f32) -> DrawParam {
    DrawParam::new().dest([x, y])
}

impl<S: GameState> EventHandler for PopupState<S> {

    fn update(&mut self, _ctx: &mut Context) -> GameResult<()> {
        Ok(())
    }

    fn draw(&mut self, ctx: &mut Context) -> GameResult<()> {
        self.parent.as_mut().unwrap().draw(ctx)?;

        let screen = graphics::screen_coordinates(ctx);
        let bg = Mesh::new_rectangle(ctx, DrawMode::fill(), screen,
            POPUP_BG_COLOR)?;
        graphics::draw(ctx, &bg, draw_param(0.0, 0.0))?;

        self.ui.draw(ctx, draw_param(0.0, 0.0))?;

        Ok(())
    }

    fn mouse_button_up_event(&mut self, ctx: &mut Context,
            button: MouseButton, x: f32, y: f32) {
        self.ui.mouse_button_up_event(ctx, button, x, y)
    }
}

impl<S: GameState + 'static> GameState for PopupState<S> {

    fn transition(&mut self, _ctx: &mut Context) -> Transition {
        if let Some(callback) = self.ui.data_mut() {
            for parent in &mut self.parent {
                callback(parent);
            }

            Transition::change(|_, mut this: PopupState<S>|
                DynGameState::new(this.parent.take().unwrap()))
        }
        else {
            Transition::None
        }
    }
}
