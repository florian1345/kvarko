use ggez::Context;
use ggez::error::GameResult;
use ggez::graphics::{
    self,
    BlendMode,
    Color,
    Drawable,
    DrawParam,
    Font,
    Rect,
    Text, PxScale
};

use crate::ui::UiElement;

/// An enumeration of the possible alignments along one axis.
pub enum AxisAlignment {

    /// Alignment towards the small values along one axis with some margin. For
    /// example, `AxisAlignment::Min` along the X-axis is left-alignment.
    Min { margin: f32 },

    /// Alignment towards the center along one axis.
    Center,

    /// Alignment towards the large values along one axis with some margin. For
    /// example, `AxisAlignment::Max` along the Y-axis is bottom-alignment.
    Max { margin: f32 }
}

impl AxisAlignment {
    fn compute_pos(&self, text_size: f32, bounds_start: f32,
            bounds_end: f32) -> f32 {
        match self {
            AxisAlignment::Min { margin } =>
                bounds_start + margin,
            AxisAlignment::Center =>
                (bounds_start + bounds_end - text_size) * 0.5,
            AxisAlignment::Max { margin }=>
                bounds_end - margin - text_size 
        }
    }
}

/// Specifies the alignment of text within a rectangle by defining alignment
/// along the horizontal and vertical axis.
pub struct Alignment {
    horizontal: AxisAlignment,
    vertical: AxisAlignment
}

impl Alignment {

    /// Alignment towards the center of the rectangle along both axes.
    pub const CENTER: Alignment = Alignment {
        horizontal: AxisAlignment::Center,
        vertical: AxisAlignment::Center
    };

    pub fn new(horizontal: AxisAlignment, vertical: AxisAlignment)
            -> Alignment {
        Alignment {
            horizontal,
            vertical
        }
    }

    fn compute_pos(&self, text_w: f32, text_h: f32,
            bounds: &Rect) -> [f32; 2] {
        let x = self.horizontal.compute_pos(text_w,
            bounds.left(), bounds.right());
        let y = self.vertical.compute_pos(text_h,
            bounds.top(), bounds.bottom());
        [x, y]
    }
}

/// A label which displays some text.
pub struct Label {
    dimensions: Rect,
    color: Color,
    text: String,
    alignment: Alignment,
    blend_mode: Option<BlendMode>,
    size: f32
}

impl Label {

    /// Creates a new label from the dimensions, color, text, and alignment.
    ///
    /// # Parameters
    ///
    /// * `dimensions`: A `Rect` which defines the dimensions of the label.
    /// * `color`: The color in which the text is printed.
    /// * `text`: The label text.
    /// * `alignment`: The `Alignment` that specifies how the text is laid out
    /// within the dimensions.
    /// * `size`: The text size in pixels.
    pub fn new(dimensions: Rect, color: Color, text: String,
            alignment: Alignment, size: f32) -> Label {
        Label {
            dimensions,
            color,
            text,
            alignment,
            blend_mode: None,
            size
        }
    }

    pub fn set_dimensions(&mut self, dimensions: Rect) {
        self.dimensions = dimensions;
    }

    pub fn set_text(&mut self, text: String) {
        self.text = text;
    }

    pub fn get_text_bounds(&self, ctx: &mut Context) -> Rect {
        let mut text = Text::new(self.text.as_str());
        text.set_font(Font::default(), PxScale::from(self.size));
        let text_rect = text.dimensions(ctx);
        let (w, h) = (text_rect.w, text_rect.h);
        let text_pos = self.alignment.compute_pos(w, h, &self.dimensions);
        Rect::new(text_pos[0], text_pos[1], w, h)
    }
}

impl Drawable for Label {
    fn dimensions(&self, _ctx: &mut Context) -> Option<Rect> {
        Some(self.dimensions)
    }

    fn draw(&self, ctx: &mut Context, params: DrawParam) -> GameResult {
        // TODO make more efficient
        // TODO apply params

        let mut text = Text::new(self.text.as_str());
        text.set_font(Font::default(), PxScale::from(self.size));
        let text_rect = self.get_text_bounds(ctx);
        let params = params
            .dest([text_rect.x, text_rect.y])
            .scale([1.0, 1.0])
            .color(self.color);
        graphics::draw(ctx, &text, params)?;
        Ok(())
    }

    fn set_blend_mode(&mut self, mode: Option<BlendMode>) {
        self.blend_mode = mode;
    }

    fn blend_mode(&self) -> Option<BlendMode> {
        self.blend_mode
    }
}

impl UiElement for Label { }
