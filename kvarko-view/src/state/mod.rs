use std::any::Any;
use std::marker::PhantomData;

use ggez::{Context, GameError, GameResult, graphics};
use ggez::event::{self, ErrorOrigin, EventHandler, KeyCode, KeyMods, MouseButton};

pub use game::GameplayState;
pub use menu::MenuState;
pub use popup::{Action, PopupState};

mod game;
mod menu;
mod popup;

type Changer<S> = Box<dyn FnOnce(&mut Context, S) -> DynGameState>;

pub enum Transition {
    None,
    Push(DynGameState),
    Pop,
    Change(Box<dyn Any>),
    Exit
}

impl Transition {
    fn change<S, F>(f: F) -> Transition
    where
        S: 'static,
        F: FnOnce(&mut Context, S) -> DynGameState + 'static
    {
        let inner: Changer<S> = Box::new(f);

        Transition::Change(Box::new(inner))
    }
}

pub trait GameState : EventHandler {

    fn transition(&mut self, ctx: &mut Context) -> Transition;
}

trait TransformableGameState : GameState {

    fn transform(&mut self, ctx: &mut Context, transformer: Box<dyn Any>)
        -> DynGameState;
}

struct TransformableGameStateWrapper<S> {
    inner: Option<Box<dyn Any>>,
    inner_type: PhantomData<S>
}

impl<S: 'static> TransformableGameStateWrapper<S> {

    fn inner_mut(&mut self) -> &mut S {
        self.inner.as_mut().unwrap().downcast_mut().unwrap()
    }
}

impl<S> EventHandler for TransformableGameStateWrapper<S>
where
    S: GameState + 'static
{
    fn update(&mut self, ctx: &mut Context) -> GameResult<()> {
        self.inner_mut().update(ctx)
    }

    fn draw(&mut self, ctx: &mut Context) -> GameResult<()> {
        self.inner_mut().draw(ctx)
    }

    fn mouse_button_down_event(&mut self, ctx: &mut Context,
            button: MouseButton, x: f32, y: f32) {
        self.inner_mut().mouse_button_down_event(ctx, button, x, y)
    }

    fn mouse_button_up_event(&mut self, ctx: &mut Context,
            button: MouseButton, x: f32, y: f32) {
        self.inner_mut().mouse_button_up_event(ctx, button, x, y)
    }

    fn mouse_motion_event(&mut self, ctx: &mut Context, x: f32, y: f32,
            dx: f32, dy: f32) {
        self.inner_mut().mouse_motion_event(ctx, x, y, dx, dy)
    }

    fn mouse_enter_or_leave(&mut self, ctx: &mut Context, entered: bool) {
        self.inner_mut().mouse_enter_or_leave(ctx, entered)
    }

    fn mouse_wheel_event(&mut self, ctx: &mut Context, x: f32, y: f32) {
        self.inner_mut().mouse_wheel_event(ctx, x, y)
    }

    fn key_down_event(&mut self, ctx: &mut Context, keycode: KeyCode,
            keymods: KeyMods, repeat: bool) {
        self.inner_mut().key_down_event(ctx, keycode, keymods, repeat)
    }

    fn key_up_event(&mut self, ctx: &mut Context, keycode: KeyCode,
            keymods: KeyMods) {
        self.inner_mut().key_up_event(ctx, keycode, keymods)
    }

    fn text_input_event(&mut self, ctx: &mut Context, character: char) {
        self.inner_mut().text_input_event(ctx, character)
    }

    fn focus_event(&mut self, ctx: &mut Context, gained: bool) {
        self.inner_mut().focus_event(ctx, gained)
    }

    fn quit_event(&mut self, ctx: &mut Context) -> bool {
        self.inner_mut().quit_event(ctx)
    }

    fn resize_event(&mut self, ctx: &mut Context, width: f32, height: f32) {
        self.inner_mut().resize_event(ctx, width, height)
    }

    fn on_error(&mut self, ctx: &mut Context, origin: ErrorOrigin,
            e: GameError) -> bool {
        self.inner_mut().on_error(ctx, origin, e)
    }
}

impl<S> GameState for TransformableGameStateWrapper<S>
where
    S: GameState + 'static
{
    fn transition(&mut self, ctx: &mut Context) -> Transition {
        self.inner_mut().transition(ctx)
    }
}

impl<S> TransformableGameState for TransformableGameStateWrapper<S>
where
    S: GameState + 'static
{
    fn transform(&mut self, ctx: &mut Context, transformer: Box<dyn Any>) -> DynGameState {
        let transformer: Box<Changer<S>> = transformer.downcast().unwrap();
        let inner: Box<S> = self.inner.take().unwrap().downcast().unwrap();

        transformer(ctx, *inner)
    }
}

pub struct DynGameState(Box<dyn TransformableGameState>);

impl DynGameState {
    pub fn new<S>(state: S) -> DynGameState
    where
        S: GameState + 'static
    {
        DynGameState(Box::new(TransformableGameStateWrapper::<S> {
            inner: Some(Box::new(state)),
            inner_type: PhantomData
        }))
    }
}

pub struct GameStateManager {
    stack: Vec<DynGameState>
}

impl GameStateManager {

    pub fn new(initial: impl GameState + 'static) -> GameStateManager {
        GameStateManager {
            stack: vec![DynGameState::new(initial)]
        }
    }

    fn current(&mut self) -> &mut Box<dyn TransformableGameState> {
        &mut self.stack.last_mut().unwrap().0
    }
}

impl EventHandler for GameStateManager {

    fn update(&mut self, ctx: &mut Context) -> GameResult<()> {
        if self.stack.is_empty() {
            event::quit(ctx);
        }

        self.current().update(ctx)?;

        match self.current().transition(ctx) {
            Transition::None => { },
            Transition::Push(state) => self.stack.push(state),
            Transition::Pop => { self.stack.pop(); },
            Transition::Change(transformer) => {
                let mut current = self.stack.pop().unwrap();
                let next = current.0.transform(ctx, transformer);

                self.stack.push(next)
            },
            Transition::Exit => self.stack.clear()
        }

        Ok(())
    }

    fn draw(&mut self, ctx: &mut Context) -> GameResult<()> {
        self.current().draw(ctx)?;
        graphics::present(ctx)
    }

    fn mouse_button_down_event(&mut self, ctx: &mut Context,
            button: MouseButton, x: f32, y: f32) {
        self.current().mouse_button_down_event(ctx, button, x, y)
    }

    fn mouse_motion_event(&mut self, ctx: &mut Context, x: f32, y: f32,
            dx: f32, dy: f32) {
        self.current().mouse_motion_event(ctx, x, y, dx, dy)
    }

    fn mouse_button_up_event(&mut self, ctx: &mut Context,
            button: MouseButton, x: f32, y: f32) {
        self.current().mouse_button_up_event(ctx, button, x, y)
    }

    fn resize_event(&mut self, ctx: &mut Context, width: f32, height: f32) {
        self.current().resize_event(ctx, width, height)
    }
}
