use std::any::Any;
use std::marker::PhantomData;

use ggez::{Context, GameResult};
use ggez::event::{MouseButton, EventHandler};
use ggez::graphics::{self, BlendMode, Color, Drawable, DrawParam, Rect};

mod button;
mod label;

pub use button::Button;
pub use label::{Alignment, AxisAlignment, Label};

/// A trait to be implemented for all UI elements/controls.
pub trait UiElement : Drawable {

    /// Called upon each logic update of the UI.
    ///
    /// # Arguments
    ///
    /// * `_ctx`: The game's current [Context] provided by GGEZ.
    fn update(&mut self, _ctx: &mut Context) -> GameResult {
        Ok(())
    }

    /// Called when the user clicks on this UI element as per its dimensions
    /// specified via the [Drawable] implementation and this UI element was on
    /// top of the UI at the clicked point.
    ///
    /// # Arguments
    ///
    /// * `_ctx`: The game's current [Context] provided by GGEZ.
    /// * `_button`: The [MouseButton] with which the user clicked on this UI
    /// element.
    ///
    /// # Returns
    ///
    /// True, if and only if the click should yield a user-facing on-clicked
    /// event.
    fn on_clicked(&mut self, _ctx: &mut Context, _button: MouseButton)
            -> bool {
        false
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct UiElementId(usize);

type OnClicked<D> = Box<dyn FnMut(&mut Context, &mut Ui<D>, MouseButton)>;

// TODO this approach requires double boxing, would be nicer without.

trait DynUiElement : UiElement {

    fn as_any(&self) -> &dyn Any;

    fn as_any_mut(&mut self) -> &mut dyn Any;
}

struct DynUiElementWrapper<E> {
    object: Box<dyn Any>,
    _type: PhantomData<E>
}

impl<E: 'static> DynUiElementWrapper<E> {
    fn as_ref(&self) -> &E {
        self.object.downcast_ref().unwrap()
    }

    fn as_mut(&mut self) -> &mut E {
        self.object.downcast_mut().unwrap()
    }
}

impl<E: Drawable + 'static> Drawable for DynUiElementWrapper<E> {
    fn draw(&self, ctx: &mut Context, param: DrawParam) -> GameResult {
        self.as_ref().draw(ctx, param)
    }

    fn dimensions(&self, ctx: &mut Context) -> Option<Rect> {
        self.as_ref().dimensions(ctx)
    }

    fn set_blend_mode(&mut self, mode: Option<BlendMode>) {
        self.as_mut().set_blend_mode(mode)
    }

    fn blend_mode(&self) -> Option<BlendMode> {
        self.as_ref().blend_mode()
    }
}

impl<E: UiElement + 'static> UiElement for DynUiElementWrapper<E> {
    fn on_clicked(&mut self, ctx: &mut Context, button: MouseButton) -> bool {
        self.as_mut().on_clicked(ctx, button)
    }
}

impl<E: UiElement + 'static> DynUiElement for DynUiElementWrapper<E> {
    fn as_any(&self) -> &dyn Any {
        self.object.as_ref()
    }

    fn as_any_mut(&mut self) -> &mut dyn Any {
        self.object.as_mut()
    }
}

fn box_ui_element<E>(element: E) -> Box<dyn DynUiElement>
where
    E: UiElement + 'static
{
    Box::new(DynUiElementWrapper::<E> {
        object: Box::new(element),
        _type: PhantomData
    })
}

/// A graphical user interface consisting of multiple [UiElement]s.
pub struct Ui<D> {
    elements: Vec<Box<dyn DynUiElement>>,
    on_clicked: Vec<Option<OnClicked<D>>>,
    data: D
}

impl<D> Ui<D> {

    /// Constructs a new user interface that is initially empty.
    pub fn new(data: D) -> Ui<D> {
        Ui {
            elements: Vec::new(),
            on_clicked: Vec::new(),
            data
        }
    }

    pub fn add_element<E>(&mut self, element: E) -> UiElementId
    where
        E: UiElement + 'static
    {
        let id = UiElementId(self.elements.len());
        self.elements.push(box_ui_element(element));
        self.on_clicked.push(None);
        id
    }

    pub fn set_on_clicked_action<F>(&mut self, element: UiElementId,
        on_clicked: F)
    where
        F: FnMut(&mut Context, &mut Ui<D>, MouseButton) + 'static
    {
        let entry = self.on_clicked.get_mut(element.0).unwrap();
        *entry = Some(Box::new(on_clicked));
    }

    pub fn element<E: 'static>(&self, element: UiElementId) -> &E {
        self.elements[element.0]
            .as_any()
            .downcast_ref()
            .unwrap()
    }

    pub fn element_mut<E: 'static>(&mut self, element: UiElementId) -> &mut E {
        self.elements[element.0]
            .as_any_mut()
            .downcast_mut()
            .unwrap()
    }

    pub fn data(&self) -> &D {
        &self.data
    }

    pub fn data_mut(&mut self) -> &mut D {
        &mut self.data
    }
}

impl<D> Drawable for Ui<D> {
    fn draw(&self, ctx: &mut Context, param: DrawParam) -> GameResult {
        for e in self.elements.iter() {
            e.draw(ctx, param)?;
        }

        Ok(())
    }

    fn dimensions(&self, ctx: &mut Context) -> Option<Rect> {
        Some(graphics::screen_coordinates(ctx))
    }

    fn set_blend_mode(&mut self, mode: Option<BlendMode>) {
        for e in self.elements.iter_mut() {
            e.set_blend_mode(mode);
        }
    }

    fn blend_mode(&self) -> Option<BlendMode> {
        self.elements.get(0).and_then(|e| e.blend_mode())
    }
}

impl<D> EventHandler for Ui<D> {
    fn update(&mut self, ctx: &mut Context) -> GameResult {
        for e in self.elements.iter_mut() {
            e.update(ctx)?;
        }

        Ok(())
    }

    fn mouse_button_up_event(&mut self, ctx: &mut Context, button: MouseButton,
            x: f32, y: f32) {
        // We draw from low indices to high indices, i.e. high indices are on
        // top and must be found first when searching for the clicked element.

        let clicked = self.elements.iter_mut()
            .enumerate()
            .rev()
            .find(|(_, e)| if let Some(dimensions) = e.dimensions(ctx) {
                dimensions.contains([x, y])
            }
            else {
                false
            });

        if let Some((clicked_idx, clicked)) = clicked {
            if clicked.on_clicked(ctx, button) {
                if let Some(mut action) = self.on_clicked[clicked_idx].take() {
                    action(ctx, self, button);
                    self.on_clicked[clicked_idx].get_or_insert(action);
                }
            }
        }
    }

    fn draw(&mut self, ctx: &mut Context) -> GameResult {
        graphics::clear(ctx, Color::BLACK);
        graphics::draw(ctx, self, ([0.0, 0.0],))?;
        graphics::present(ctx)
    }
}
