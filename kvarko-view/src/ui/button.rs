use ggez::Context;
use ggez::error::GameResult;
use ggez::graphics::{
    self,
    BlendMode,
    Color,
    Drawable,
    DrawMode,
    DrawParam,
    Mesh,
    Rect,
    StrokeOptions
};
use ggez::input::mouse::MouseButton;

use crate::ui::{Alignment, Label, UiElement};

/// A button which has some text and forwards left-click events to the user.
pub struct Button {
    dimensions: Rect,
    color: Color,
    label: Label,
    blend_mode: Option<BlendMode>
}

impl Button {

    /// Creates a new button from the dimensions, color, and text
    ///
    /// # Parameters
    ///
    /// * `dimensions`: A `Rect` which defines the dimensions of the button.
    /// This determines the area in which a click would be counted as clicking
    /// the button.
    /// * `color`: The color in which the text is printed.
    /// * `text`: The label displayed on the button.
    pub fn new(dimensions: Rect, color: Color, text: String, size: f32)
            -> Button {
        let label =
            Label::new(dimensions, color, text, Alignment::CENTER, size);

        Button {
            dimensions,
            color,
            label,
            blend_mode: None
        }
    }

    pub fn dimensions(&self) -> &Rect {
        &self.dimensions
    }

    pub fn set_dimensions(&mut self, dimensions: Rect) {
        self.dimensions = dimensions;
        self.label.set_dimensions(dimensions);
    }

    pub fn set_text(&mut self, text: String) {
        self.label.set_text(text);
    }
}

impl Drawable for Button {
    fn dimensions(&self, _ctx: &mut Context) -> Option<Rect> {
        Some(self.dimensions)
    }

    fn draw(&self, ctx: &mut Context, params: DrawParam) -> GameResult {
        // TODO make more efficient
        let draw_mode = DrawMode::Stroke(StrokeOptions::DEFAULT);
        let rect =
            Mesh::new_rectangle(ctx, draw_mode, self.dimensions, self.color)?;
        graphics::draw(ctx, &rect, params)?;
        graphics::draw(ctx, &self.label, params)?;
        Ok(())
    }

    fn set_blend_mode(&mut self, mode: Option<BlendMode>) {
        self.label.set_blend_mode(mode);
        self.blend_mode = mode;
    }

    fn blend_mode(&self) -> Option<BlendMode> {
        self.blend_mode
    }
}

impl UiElement for Button {
    fn on_clicked(&mut self, _ctx: &mut Context, button: MouseButton) -> bool {
        button == MouseButton::Left
    }
}
