use crate::error::{BuildGameResult, BuildGameError};
use crate::hash::PositionHasher;
use crate::movement::Move;
use crate::player::Player;
use crate::state::{Outcome, State};

/// A trait for types that consume events raised in a game of chess.
pub trait Observer<H: PositionHasher> {

    /// Notification that all initial variables have been specified and the
    /// game is now in the initial state. No moves have been made yet.
    ///
    /// # Arguments
    ///
    /// * `_initial_state`: The initial [State].
    fn on_started(&mut self, _initial_state: &State<H>) { }

    /// Notification that a move has been made and the game state has changed.
    ///
    /// # Arguments
    ///
    /// * `_mov`: The [Move] that has been made.
    /// * `_new_state`: The [State] after the move has been applied. The player
    /// offered by [Position::turn](crate::state::Position::turn) on
    /// [State::position] is now the player whose turn it is after the move,
    /// i.e. the opponent of the player who made the given move.
    fn on_move_made(&mut self, _mov: &Move, _new_state: &State<H>) { }

    /// Notification that an outcome of the game could be determined, that is,
    /// one player checkmated the other or it is a draw.
    ///
    /// This notification comes after the [Observer::on_move_made] notification
    /// of the last move in the game.
    ///
    /// # Arguments
    ///
    /// * `_outcome`: The [Outcome] of the game (victory of one player or
    /// draw).
    /// * `_final_state`: The final [State] of the game.
    fn on_outcome(&mut self, _outcome: Outcome, _final_state: &State<H>) { }
}

/// A controller makes moves for a player in a game of Chess. This trait is to
/// be implemented by all AIs.
pub trait Controller<H: PositionHasher> {

    /// This method is called before the first move is queried and allows any
    /// initialization that needs to be done by this controller. By default, it
    /// does nothing.
    ///
    /// # Arguments
    ///
    /// * `_player`: The [Player] that this controller will represent.
    fn initialize(&mut self, _player: Player) { }

    /// Decides on a move that the player should make. The player whose turn it
    /// is can be found with [Position::turn](crate::state::Position::turn) on
    /// [State::position] on the given input state. It is guaranteed to be the
    /// same as the one passed to the controller in [Controller::initialize].
    ///
    /// # Arguments
    ///
    /// * `state`: The current game [State] in which a move shall be made by
    /// the active player.
    ///
    /// # Returns
    ///
    /// A valid [Move] to be made in the current state.
    fn make_move(&mut self, state: &State<H>) -> Move;
}

/// Manages gameplay of a single game of Chess. Individual players' decisions
/// are made by [Controller]s. Construct this struct using the [GameBuilder].
pub struct Game<H: PositionHasher> {
    state: State<H>,
    white: Box<dyn Controller<H>>,
    black: Box<dyn Controller<H>>,
    observers: Vec<Box<dyn Observer<H>>>,
    outcome: Option<Outcome>
}

impl<H: PositionHasher> Game<H> {

    fn update_outcome(&mut self) {
        self.outcome = self.state.compute_outcome();

        if self.outcome.is_some() {
            for observer in &mut self.observers {
                observer.on_outcome(self.outcome.unwrap(), &self.state);
            }
        }
    }

    fn init(&mut self) {
        self.white.initialize(Player::White);
        self.black.initialize(Player::Black);

        for observer in &mut self.observers {
            observer.on_started(&self.state);
        }

        self.update_outcome();
    }

    /// Plays a single move (or "ply" in Chess terminology) by the currently
    /// active player. The decision is made by the [Controller] associated with
    /// the player whose turn it is. If the game has already ended, nothing is
    /// changed and the outcome is returned.
    ///
    /// # Returns
    ///
    /// The [Outcome] of the game if it was already finished or the move that
    /// has just been made finished it, otherwise `None`.
    pub fn play_move(&mut self) -> Option<Outcome> {
        if self.outcome.is_some() {
            return self.outcome;
        }

        let mov = match self.state.position().turn() {
            Player::White => self.white.make_move(&self.state),
            Player::Black => self.black.make_move(&self.state)
        };

        self.state.make_move(&mov);

        for observer in &mut self.observers {
            observer.on_move_made(&mov, &self.state);
        }

        self.update_outcome();

        self.outcome
    }

    /// Plays moves until the game has ended. That is, repeatedly calls
    /// [Game::play_move] until an outcome could be determined.
    ///
    /// # Returns
    ///
    /// The [Outcome] of the game after it has been finished.
    pub fn play_to_end(&mut self) -> Outcome {
        while self.outcome.is_none() {
            self.play_move();
        }

        self.outcome.unwrap()
    }
}

/// A builder struct for [Game]s.
pub struct GameBuilder<H: PositionHasher> {
    state: State<H>,
    white: Option<Box<dyn Controller<H>>>,
    black: Option<Box<dyn Controller<H>>>,
    observers: Vec<Box<dyn Observer<H>>>
}

impl<H: PositionHasher> GameBuilder<H> {

    /// Creates a new game builder with the default initial position.
    pub fn new() -> GameBuilder<H> {
        GameBuilder {
            state: State::initial(),
            white: None,
            black: None,
            observers: Vec::new()
        }
    }

    /// Specifies the initial state in which to start the game.
    ///
    /// # Arguments
    ///
    /// * `state`: The initial [State] in which to start the game.
    ///
    /// # Returns
    ///
    /// This builder for chaining.
    pub fn with_initial_state(mut self, state: State<H>) -> GameBuilder<H> {
        self.state = state;
        self
    }

    /// Specifies the controller which shall decide the moves for the white
    /// player in the game. This method accepts a boxed controller. To pass any
    /// instance implementing [Controller], use [GameBuilder::with_white].
    ///
    /// # Arguments
    ///
    /// * `controller`: The boxed [Controller] to decide the moves for the
    /// white player.
    ///
    /// # Returns
    ///
    /// This builder for chaining.
    pub fn with_white_box(mut self, controller: Box<dyn Controller<H>>)
            -> GameBuilder<H> {
        self.white = Some(controller);
        self
    }

    /// Specifies the controller which shall decide the moves for the white
    /// player in the game. This method accepts an implementation of
    /// [Controller] directly. To pass a trait object, use
    /// [GameBuilder::with_white_box].
    ///
    /// # Arguments
    ///
    /// * `controller`: The [Controller] to decide the moves for the white
    /// player.
    ///
    /// # Returns
    ///
    /// This builder for chaining.
    pub fn with_white<C>(self, controller: C) -> GameBuilder<H>
    where
        C: Controller<H> + 'static
    {
        self.with_white_box(Box::new(controller))
    }

    /// Specifies the controller which shall decide the moves for the black
    /// player in the game. This method accepts a boxed controller. To pass any
    /// instance implementing [Controller], use [GameBuilder::with_black].
    ///
    /// # Arguments
    ///
    /// * `controller`: The boxed [Controller] to decide the moves for the
    /// black player.
    ///
    /// # Returns
    ///
    /// This builder for chaining.
    pub fn with_black_box(mut self, controller: Box<dyn Controller<H>>)
            -> GameBuilder<H> {
        self.black = Some(controller);
        self
    }

    /// Specifies the controller which shall decide the moves for the black
    /// player in the game. This method accepts an implementation of
    /// [Controller] directly. To pass a trait object, use
    /// [GameBuilder::with_black_box].
    ///
    /// # Arguments
    ///
    /// * `controller`: The [Controller] to decide the moves for the black
    /// player.
    ///
    /// # Returns
    ///
    /// This builder for chaining.
    pub fn with_black<C>(self, controller: C) -> GameBuilder<H>
    where
        C: Controller<H> + 'static
    {
        self.with_black_box(Box::new(controller))
    }

    /// Adds a new observer which will receive game events for the constructed
    /// game. This method accepts a boxed observer. To pass any instance
    /// implementing [Observer], use [GameBuilder::with_observer].
    ///
    /// # Arguments
    ///
    /// * `observer`: The boxed [Observer] to receive game events.
    ///
    /// # Returns
    ///
    /// This builder for chaining.
    pub fn with_observer_box(mut self, observer: Box<dyn Observer<H>>)
            -> GameBuilder<H> {
        self.observers.push(observer);
        self
    }

    /// Adds a new observer which will receive game events for the constructed
    /// game. This method accepts an implementation of [Observer] directly. To
    /// pass a trait object, use [GameBuilder::with_observer_box].
    ///
    /// # Arguments
    ///
    /// * `observer`: The [Observer] to receive game events.
    ///
    /// # Returns
    ///
    /// This builder for chaining.
    pub fn with_observer<O>(self, observer: O) -> GameBuilder<H>
    where
        O: Observer<H> + 'static
    {
        self.with_observer_box(Box::new(observer))
    }

    /// Constructs the final game with the components provided in previous
    /// method calls. It is required that at least the controllers have been
    /// specified, i.e. [GameBuilder::with_white] or
    /// [GameBuilder::with_white_box] as well as [GameBuilder::with_black] or
    /// [GameBuilder::with_black_box] must have been called before this.
    ///
    /// # Returns
    ///
    /// A new [Game] constructed from the components provided before.
    ///
    /// # Errors
    ///
    /// Any [BuildGameError] according to their documentation.
    pub fn build(self) -> BuildGameResult<Game<H>> {
        let white = self.white
            .ok_or(BuildGameError::MissingController(Player::White))?;
        let black = self.black
            .ok_or(BuildGameError::MissingController(Player::Black))?;
        let mut game = Game {
            state: self.state,
            white,
            black,
            outcome: None,
            observers: self.observers
        };

        game.init();

        Ok(game)
    }
}

impl<H: PositionHasher> Default for GameBuilder<H> {
    fn default() -> GameBuilder<H> {
        GameBuilder::new()
    }
}
