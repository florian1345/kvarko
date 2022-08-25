use crate::error::{BuildGameResult, BuildGameError};
use crate::movement::Move;
use crate::player::Player;
use crate::state::{Outcome, State};

/// A controller makes moves for a player in a game of Chess. This trait is to
/// be implemented by all AIs.
pub trait Controller {

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
    fn make_move(&mut self, state: &State) -> Move;
}

/// Manages gameplay of a single game of Chess. Individual players' decisions
/// are made by [Controller]s. Construct this struct using the [GameBuilder].
pub struct Game {
    state: State,
    white: Box<dyn Controller>,
    black: Box<dyn Controller>,
    outcome: Option<Outcome>
}

impl Game {

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
        self.outcome = self.state.compute_outcome();
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
pub struct GameBuilder {
    state: State,
    white: Option<Box<dyn Controller>>,
    black: Option<Box<dyn Controller>>
}

impl GameBuilder {

    /// Creates a new game builder with the default initial position.
    pub fn new() -> GameBuilder {
        GameBuilder {
            state: State::initial(),
            white: None,
            black: None
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
    pub fn with_initial_state(mut self, state: State) -> GameBuilder {
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
    pub fn with_white_box(mut self, controller: Box<dyn Controller>)
            -> GameBuilder {
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
    pub fn with_white<C>(self, controller: C) -> GameBuilder
    where
        C: Controller + 'static
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
    pub fn with_black_box(mut self, controller: Box<dyn Controller>)
            -> GameBuilder {
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
    pub fn with_black<C>(self, controller: C) -> GameBuilder
    where
        C: Controller + 'static
    {
        self.with_black_box(Box::new(controller))
    }

    /// Constructs the final game with the components provided in previous
    /// method calls. It is required that at least the controllers have been
    /// specified, i.e. [GameBuilder::with_white] or
    /// [GameBuilder::with_white_boxed] as well as [GameBuilder::with_black] or
    /// [GameBuilder::with_black_boxed] must have been called before this.
    ///
    /// # Returns
    ///
    /// A new [Game] constructed from the components provided before.
    ///
    /// # Errors
    ///
    /// Any [BuildGameError] according to their documentation.
    pub fn build(self) -> BuildGameResult<Game> {
        let mut white = self.white
            .ok_or(BuildGameError::MissingController(Player::White))?;
        let mut black = self.black
            .ok_or(BuildGameError::MissingController(Player::Black))?;

        white.initialize(Player::White);
        black.initialize(Player::Black);

        let outcome = self.state.compute_outcome();

        Ok(Game {
            state: self.state,
            white,
            black,
            outcome
        })
    }
}
