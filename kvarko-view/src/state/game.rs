use std::collections::{HashMap, HashSet};
use std::sync::mpsc::{self, Receiver, Sender};

use ggez::{Context, GameResult};
use ggez::event::{EventHandler, MouseButton};
use ggez::graphics::{
    self,
    Align,
    Color,
    DrawMode,
    DrawParam,
    Image,
    Mesh,
    Rect,
    Text
};

use kvarko_model::board::{self, Location};
use kvarko_model::game::{Controller, Observer};
use kvarko_model::hash::ZobristHasher;
use kvarko_model::movement::{self, Move};
use kvarko_model::piece::Piece;
use kvarko_model::player::Player;
use kvarko_model::state::Outcome;

use crate::state::{Action, DynGameState, GameState, PopupState, Transition};
use crate::sync::{self, Requester, Responder, ResponseHandle};
use crate::ui::Button;

type State = kvarko_model::state::State<ZobristHasher<u64>>;

struct ImageManager {
    pieces: HashMap<(Player, Piece), Image>
}

fn player_id(player: Player) -> &'static str {
    match player {
        Player::White => "white",
        Player::Black => "black"
    }
}

fn piece_id(piece: Piece) -> &'static str {
    match piece {
        Piece::Pawn => "pawn",
        Piece::Knight => "knight",
        Piece::Bishop => "bishop",
        Piece::Rook => "rook",
        Piece::Queen => "queen",
        Piece::King => "king"
    }
}

fn piece_file_name(player: Player, piece: Piece) -> String {
    format!("/{}_{}.png", player_id(player), piece_id(piece))
}

impl ImageManager {

    fn new() -> ImageManager {
        ImageManager {
            pieces: HashMap::new()
        }
    }

    fn piece_image(&mut self, ctx: &mut Context, player: Player,
            piece: Piece) -> GameResult<&Image> {
        Ok(self.pieces.entry((player, piece))
            .or_insert(Image::new(ctx, piece_file_name(player, piece))?))
    }
}

pub struct ViewObserver {
    move_sender: Sender<State>,
    outcome_sender: Sender<Outcome>
}

impl Observer<ZobristHasher<u64>> for ViewObserver {

    fn on_started(&mut self, initial_state: &State) {
        // Moves are rendered only as state updates, so we can "misuse" the
        // move channel to specify the initial state.

        self.move_sender.send(initial_state.clone()).unwrap();
    }

    fn on_move_made(&mut self, _mov: &Move, new_state: &State) {
        self.move_sender.send(new_state.clone()).unwrap();
    }

    fn on_outcome(&mut self, outcome: Outcome, _final_state: &State) {
        self.outcome_sender.send(outcome).unwrap();
    }
}

#[derive(Clone)]
pub struct HumanController {
    requester: Requester<State, Move>
}

impl Controller<ZobristHasher<u64>> for HumanController {

    fn make_move(&mut self, state: &State) -> Move {
        self.requester.query(state.clone()).unwrap()
    }
}

const BG_COLOR: Color = Color::BLACK;
const LIGHT_COLOR: Color = Color::new(0.88, 0.72, 0.60, 1.0);
const DARK_COLOR: Color = Color::new(0.66, 0.54, 0.45, 1.0);
const HIGHLIGHT_COLOR: Color = Color::new(0.9, 0.9, 0.5, 0.5);
const BOARD_FRACTION: f32 = 0.9;
const PIECE_FRACTION: f32 = 0.9;
const IMAGE_RESOLUTION: f32 = 256.0;

fn draw_param(x: f32, y: f32) -> DrawParam {
    DrawParam::new().dest([x, y])
}

pub struct GameplayState {
    game_state: State,
    image_manager: ImageManager,
    board_start_x: f32,
    board_start_y: f32,
    field_width: f32,
    field_height: f32,
    piece_size: f32,
    piece_offset_x: f32,
    piece_offset_y: f32,
    piece_scale: f32,
    dragged_piece: Option<(usize, usize)>,
    dragged_piece_location: Option<(f32, f32)>,
    highlighted_squares: HashSet<(usize, usize)>,
    legal_moves: Vec<Move>,
    awaiting_moves: Option<Vec<Move>>,
    outcome: Option<Outcome>,
    move_receiver: Receiver<State>,
    outcome_receiver: Receiver<Outcome>,
    move_responder: Responder<State, Move>,
    move_response_handle: Option<ResponseHandle<Move>>,
    turn: Player
}

impl GameplayState {

    pub fn new(ctx: &mut Context, game: State) -> (GameplayState, ViewObserver, HumanController) {
        let (move_sender, move_receiver) = mpsc::channel();
        let (outcome_sender, outcome_receiver) = mpsc::channel();
        let view_observer = ViewObserver {
            move_sender,
            outcome_sender
        };
        let (move_requester, move_responder) = sync::channel();
        let human_controller = HumanController {
            requester: move_requester
        };
        let mut gameplay_state = GameplayState {
            game_state: game,
            image_manager: ImageManager::new(),
            board_start_x: 0.0,
            board_start_y: 0.0,
            field_width: 0.0,
            field_height: 0.0,
            piece_size: 0.0,
            piece_offset_x: 0.0,
            piece_offset_y: 0.0,
            piece_scale: 0.0,
            dragged_piece: None,
            dragged_piece_location: None,
            highlighted_squares: HashSet::new(),
            legal_moves: Vec::new(),
            awaiting_moves: None,
            outcome: None,
            move_receiver,
            outcome_receiver,
            move_responder,
            move_response_handle: None,
            turn: Player::White
        };

        let screen = graphics::screen_coordinates(ctx);
        gameplay_state.resize_event(ctx, screen.w, screen.h);

        (gameplay_state, view_observer, human_controller)
    }

    fn piece_draw_param(&self, x: f32, y: f32) -> DrawParam {
        draw_param(x, y).scale([self.piece_scale, self.piece_scale])
    }

    fn set_dragged_piece_location(&mut self, mouse_x: f32, mouse_y: f32) {
        let x = mouse_x - self.piece_size * 0.5;
        let y = mouse_y - self.piece_size * 0.5;
        self.dragged_piece_location = Some((x, y))
    }

    fn get_mouse_field(&mut self, mouse_x: f32, mouse_y: f32)
            -> (usize, usize) {
        let file_f = (mouse_x - self.board_start_x) / self.field_width;
        let rank_f = (self.board_start_y - mouse_y) / self.field_height;

        let file = file_f.floor() as usize;
        let rank = rank_f.floor() as usize;

        (file, rank)
    }

    fn make_move(&mut self, mov: Move) {
        self.legal_moves = Vec::new();
        self.move_response_handle.take().unwrap().send_response(mov).unwrap();
    }
}

impl EventHandler for GameplayState {

    fn update(&mut self, _ctx: &mut Context) -> GameResult<()> {
        if let Some((game_state, response_handle)) =
                self.move_responder.recv() {
            self.legal_moves = movement::list_moves(game_state.position()).0;
            self.move_response_handle = Some(response_handle);
        }

        if let Ok(new_state) = self.move_receiver.try_recv() {
            self.game_state = new_state;
            self.turn = self.turn.opponent();
        }
        else if let Ok(outcome) = self.outcome_receiver.try_recv() {
            self.outcome = Some(outcome);
        }

        Ok(())
    }

    fn draw(&mut self, ctx: &mut Context) -> GameResult<()> {
        graphics::clear(ctx, BG_COLOR);

        let board = self.game_state.position().board();

        for rank in 0..board::BOARD_HEIGHT {
            let rank_y =
                self.board_start_y - (rank + 1) as f32 * self.field_height;

            for file in 0..board::BOARD_WIDTH {
                let file_x =
                    self.board_start_x + file as f32 * self.field_width;
                let color = if (rank + file) % 2 == 0 {
                    DARK_COLOR
                }
                else {
                    LIGHT_COLOR
                };
                let rect =
                    Rect::new(0.0, 0.0, self.field_width, self.field_height);
                let cell =
                    Mesh::new_rectangle(ctx, DrawMode::fill(), rect, color)?;
                let draw_param = draw_param(file_x, rank_y);

                graphics::draw(ctx, &cell, draw_param)?;

                if self.highlighted_squares.contains(&(file, rank)) {
                    let highlight =
                        Mesh::new_rectangle(ctx, DrawMode::fill(), rect,
                            HIGHLIGHT_COLOR)?;

                    graphics::draw(ctx, &highlight, draw_param)?;
                }

                if self.dragged_piece == Some((file, rank)) {
                    continue;
                }

                let location =
                    Location::from_file_and_rank(file, rank).unwrap();
                let piece = board.piece_at(location);

                if let Some(piece) = piece {
                    let player = board.player_at(location).unwrap();
                    let image_x = file_x + self.piece_offset_x;
                    let image_y = rank_y + self.piece_offset_y;
                    let draw_param = self.piece_draw_param(image_x, image_y);
                    let image = self.image_manager.piece_image(ctx, player, piece)?;

                    graphics::draw(ctx, image, draw_param)?;
                }
            }
        }

        if let Some((file, rank)) = self.dragged_piece {
            let location = Location::from_file_and_rank(file, rank).unwrap();
            let piece = board.piece_at(location);

            if let Some(piece) = piece {
                let player = board.player_at(location).unwrap();
                let (image_x, image_y) = self.dragged_piece_location.unwrap();
                let draw_param = self.piece_draw_param(image_x, image_y);
                let image = self.image_manager.piece_image(ctx, player, piece)?;

                graphics::draw(ctx, image, draw_param)?;
            }
        }

        Ok(())
    }

    fn mouse_button_down_event(&mut self, _ctx: &mut Context,
            button: MouseButton, x: f32, y: f32) {
        if button != MouseButton::Left || x < self.board_start_x ||
                y > self.board_start_y {
            return;
        }

        let (file, rank) = self.get_mouse_field(x, y);

        for m in &self.legal_moves {
            let src = m.source(self.game_state.position()).unwrap();
            let dest = m.destination(self.game_state.position()).unwrap();

            if src.file() == file && src.rank() == rank {
                self.highlighted_squares.insert((dest.file(), dest.rank()));
            }
        }

        if file < board::BOARD_WIDTH && rank < board::BOARD_HEIGHT {
            self.dragged_piece = Some((file, rank));
            self.set_dragged_piece_location(x, y);
        }
    }

    fn mouse_motion_event(&mut self, _ctx: &mut Context, x: f32, y: f32,
            _dx: f32, _dy: f32) {
        if self.dragged_piece_location.is_some() {
            self.set_dragged_piece_location(x, y);
        }
    }

    fn mouse_button_up_event(&mut self, _ctx: &mut Context,
            button: MouseButton, x: f32, y: f32) {
        if button != MouseButton::Left {
            return;
        }

        if x >= self.board_start_x && y <= self.board_start_y {
            if let Some((src_file, src_rank)) = self.dragged_piece {
                let (dest_file, dest_rank) = self.get_mouse_field(x, y);
                let moves = self.legal_moves.iter()
                    .filter(|m| {
                        let src = m.source(self.game_state.position())
                            .unwrap();
                        let dest = m.destination(self.game_state.position())
                            .unwrap();

                        src.file() == src_file && src.rank() == src_rank &&
                        dest.file() == dest_file && dest.rank() == dest_rank
                    })
                    .cloned()
                    .collect::<Vec<_>>();

                match moves.len() {
                    1 => {
                        self.make_move(moves.into_iter().next().unwrap());
                    },
                    2.. => {
                        self.awaiting_moves = Some(moves);
                    },
                    _ => { }
                }
            }
        }

        self.dragged_piece = None;
        self.dragged_piece_location = None;
        self.highlighted_squares.clear();
    }

    fn resize_event(&mut self, _ctx: &mut Context, width: f32, height: f32) {
        let board_size = width.min(height) * BOARD_FRACTION;
        self.board_start_x = (width - board_size) * 0.5;
        self.board_start_y = (height + board_size) * 0.5;

        self.field_width = board_size / board::BOARD_WIDTH as f32;
        self.field_height = board_size / board::BOARD_HEIGHT as f32;

        self.piece_size =
            self.field_width.min(self.field_height) * PIECE_FRACTION;
        self.piece_offset_x = (self.field_width - self.piece_size) * 0.5;
        self.piece_offset_y = (self.field_height - self.piece_size) * 0.5;
        self.piece_scale = self.piece_size / IMAGE_RESOLUTION;
    }
}

fn button_rect() -> Rect {
    Rect::new(0.0, 0.0, 128.0, 32.0)
}

impl GameState for GameplayState {

    fn transition(&mut self, _ctx: &mut Context) -> Transition {
        if let Some(awaiting_moves) = &self.awaiting_moves {
            let buttons: Vec<(Button, Action<GameplayState>)> = awaiting_moves.iter()
                .map(|m| {
                    let piece = match m {
                        Move::Promotion { promotion, .. } => *promotion,
                        _ => panic!("not a promotion")
                    };
                    let text = match piece {
                        Piece::Knight => "Knight",
                        Piece::Bishop => "Bishop",
                        Piece::Rook => "Rook",
                        Piece::Queen => "Queen",
                        _ => panic!("invalid promotion")
                    };

                    let button = Button::new(button_rect(), Color::WHITE, text.into(),
                        32.0); // TODO make size dynamic
                    let callback: Box<dyn FnMut(&mut GameplayState)> =
                        Box::new(move |this|
                            if let Some(awaiting_moves) =
                                    this.awaiting_moves.take() {
                                let mov = awaiting_moves.into_iter()
                                    .find(|m| match m {
                                        Move::Promotion { promotion, .. } =>
                                            *promotion == piece,
                                        _ => false
                                    });
                                
                                if let Some(mov) = mov {
                                    this.make_move(mov);
                                }
                            });

                    (button, callback)
                })
                .collect();

            Transition::change(move |ctx, this: GameplayState|
                DynGameState::new(
                    PopupState::new(ctx, this, "Select promotion", buttons)))
        }
        else if let Some(outcome) = self.outcome.take() {
            let text = match outcome {
                Outcome::Victory(Player::White) => "White won.",
                Outcome::Victory(Player::Black) => "Black won.",
                Outcome::Draw => "Draw."
            };
            let size = self.piece_size;
            let mut ok_button = Text::new("Ok");
            ok_button.set_bounds([size, size], Align::Center);
            let ok_button =
                Button::new(button_rect(), Color::WHITE, "Ok".into(), 32.0);
            let buttons: Vec<(Button, Action<GameplayState>)> =
                vec![(ok_button, Box::new(|_| { }))];

            Transition::change(move |ctx, this: GameplayState|
                DynGameState::new(
                    PopupState::new(ctx, this, text, buttons)))
        }
        else {
            Transition::None
        }
    }
}
