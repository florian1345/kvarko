//! This module defines the [Position] and [State] structs, which manage
//! information about the current game situation.

use crate::board::Board;
use crate::error::{FenError, FenResult};
use crate::piece::Piece;
use crate::player::{Player, PLAYER_COUNT, PLAYERS};
use crate::rules;

/// All information about the state of the game that does not relate to the
/// history of the game. That is, this contains the [Board], information
/// whether players may still castle, information about available en passant
/// moves, and whose turn it is. It does _not_ track the threefold repetition
/// or fifty move rules.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Position {
    board: Board,
    short_castles: [bool; PLAYER_COUNT],
    long_castles: [bool; PLAYER_COUNT],
    en_passant_file: usize,
    turn: Player
}

fn next_part<'a, I, S, F>(iter: &mut I, fen: &str, expected_cons: F)
    -> FenResult<&'a str>
where
    I: Iterator<Item = &'a str>,
    S: Into<String>,
    F: Fn() -> Vec<S>
{
    iter.next()
        .ok_or_else(|| FenError::WrongPartCount {
            fen: fen.to_owned(),
            expected: expected_cons().into_iter()
                .map(|s| s.into())
                .collect()
        })
}

fn next_position_part<'a, I>(iter: &mut I, fen: &str) -> FenResult<&'a str>
where
    I: Iterator<Item = &'a str>
{
    next_part(iter, fen, || vec![
        "board",
        "player to move",
        "castling rights",
        "en passant target"
    ])
}

fn next_state_part<'a, I>(iter: &mut I, fen: &str) -> FenResult<&'a str>
where
    I: Iterator<Item = &'a str>
{
    next_part(iter, fen, || vec![
        "board",
        "player to move",
        "castling rights",
        "en passant target",
        "half move clock",
        "full move clock"
    ])
}

fn parse_castling_rights(fen: &str)
        -> FenResult<([bool; PLAYER_COUNT], [bool; PLAYER_COUNT])> {
    let mut short_castles = [false, false];
    let mut long_castles = [false, false];

    if fen.is_empty() {
        Err(FenError::InvalidCastlingRight(fen.to_owned()))
    }
    else if fen == "-" {
        Ok((short_castles, long_castles))
    }
    else {
        for c in fen.chars() {
            let piece = Piece::from_fen_char(c)?;
            let player = Player::from_fen_piece_char(c);

            match piece {
                Piece::King => short_castles[player as usize] = true,
                Piece::Queen => long_castles[player as usize] = true,
                _ => return Err(FenError::InvalidCastlingRight(fen.to_owned()))
            }
        }

        Ok((short_castles, long_castles))
    }
}

fn parse_en_passant_file(fen: &str) -> FenResult<usize> {
    if fen.is_empty() {
        Err(FenError::InvalidEnPassantTarget(fen.to_owned()))
    }
    else if fen == "-" {
        Ok(usize::MAX)
    }
    else {
        let chars = fen.chars().collect::<Vec<_>>();

        if chars.len() != 2 {
            Err(FenError::InvalidEnPassantTarget(fen.to_owned()))
        }
        else {
            let file_char = chars[0];
            let rank_char = chars[1];

            if file_char < 'a' || file_char > 'h' || rank_char < '1' ||
                    rank_char > '8' {
                Err(FenError::InvalidEnPassantTarget(fen.to_owned()))
            }
            else {
                Ok(file_char as usize - '1' as usize)
            }
        }
    }
}

impl Position {

    /// Creates a new position in the initial configuration, i.e. with the
    /// [Board] described by [Board::initial], both players allowed to castle,
    /// no en passant opportunities, and white to move.
    ///
    /// # Returns
    ///
    /// A new position in the initial configuration.
    pub fn initial() -> Position {
        Position {
            board: Board::initial(),
            short_castles: [true, true],
            long_castles: [true, true],
            en_passant_file: usize::MAX,
            turn: Player::White
        }
    }

    fn from_fen_parts(board_fen: &str, turn_fen: &str,
            castling_rights_fen: &str, en_passant_fen: &str)
            -> FenResult<Position> {
        let board = Board::from_fen(board_fen)?;
        let turn = Player::from_fen_turn_specifier(turn_fen)?;
        let (short_castles, long_castles) =
            parse_castling_rights(castling_rights_fen)?;
        let en_passant_file = parse_en_passant_file(en_passant_fen)?;

        Ok(Position {
            board,
            short_castles,
            long_castles,
            en_passant_file,
            turn
        })
    }

    /// Parses FEN components which relate to the position, i.e. which do not
    /// relate to the history in any way. These are the first four components
    /// of a FEN: the board, player to move, castling rights, and en passant
    /// target square. The fifty-move state and move number are not included.
    ///
    /// # Arguments
    ///
    /// * `fen`: The parts of a FEN string which correspond to board, player to
    /// move, castling rights, and en passant target, separated by single
    /// spaces. Any more whitespace is not tolerated. May not contain any other
    /// parts than those specified.
    ///
    /// # Returns
    ///
    /// A new position constructed from the given FEN.
    ///
    /// # Errors
    ///
    /// Any [FenError] that can occur in the parts contained in a position,
    /// i.e. all except [FenError::ParseFiftyMoveClockError] and
    /// [FenError::ParseFullMoveClockError], as those relate to the move
    /// history.
    pub fn from_fen(fen: &str) -> FenResult<Position> {
        let mut parts = fen.split(' ');
        let parts = (0..4)
            .map(|_| next_position_part(&mut parts, fen))
            .collect::<Result<Vec<_>, _>>()?;

        Position::from_fen_parts(parts[0], parts[1], parts[2], parts[3])
    }

    /// Gets the current state of the [Board].
    ///
    /// # Returns
    ///
    /// An immutable reference to the current [Board].
    pub fn board(&self) -> &Board {
        &self.board
    }

    /// Indicates whether the given player may still castle short/kingside.
    /// Note this only refers to the state whether that is still generally
    /// allowed, not that it is a legal move given the current [Board]. As an
    /// example, at the start of the game this would always return `true`, as
    /// both players may generally still castle - if they move their pieces out
    /// of the way and all other conditions are met.
    ///
    /// # Arguments
    ///
    /// * `player`: The [Player] for which to determine whether they may still
    /// castle short.
    ///
    /// # Returns
    ///
    /// True, if and only if the given `player` may still castle short.
    pub fn may_short_castle(&self, player: Player) -> bool {
        self.short_castles[player as usize]
    }

    /// Indicates whether the given player may still castle long/queenside.
    /// Note this only refers to the state whether that is still generally
    /// allowed, not that it is a legal move given the current [Board]. As an
    /// example, at the start of the game this would always return `true`, as
    /// both players may generally still castle - if they move their pieces out
    /// of the way and all other conditions are met.
    ///
    /// # Arguments
    ///
    /// * `player`: The [Player] for which to determine whether they may still
    /// castle long.
    ///
    /// # Returns
    ///
    /// True, if and only if the given `player` may still castle long.
    pub fn may_long_castle(&self, player: Player) -> bool {
        self.long_castles[player as usize]
    }

    /// Gets the 0-based index of the file (A = 0, B = 1, ...) in which a pawn
    /// just moved two squares at once, if that is the case.
    ///
    /// # Returns
    ///
    /// `Some(file)` if a pawn just moved two squares at once in the given
    /// `file`, otherwise `None`.
    pub fn en_passant_file(&self) -> Option<usize> {
        if self.en_passant_file == usize::MAX {
            None
        }
        else {
            Some(self.en_passant_file)
        }
    }

    /// Gets the [Player] whose turn it currently is.
    ///
    /// # Returns
    ///
    /// The [Player] whose turn it currently is.
    pub fn turn(&self) -> Player {
        self.turn
    }

    /// Converts this position into FEN notation. To be precise, this only
    /// returns the part of the FEN notation which does not require knowledge
    /// about the history, as that is part of the [State] and not the position.
    /// That is, the first four parts (board, turn, castling rights, and en
    /// passant target) of the FEN are generated.
    ///
    /// # Returns
    ///
    /// A new [String] which contains the FEN for this position, where
    /// individual parts are separated by single spaces. There is no leading or
    /// trailing whitespace.
    pub fn to_fen(&self) -> String {
        let mut fen = self.board.to_fen();
        fen.push(' ');

        match self.turn {
            Player::White => fen.push('w'),
            Player::Black => fen.push('b')
        }

        fen.push(' ');
        let mut any_castle = false;

        for player in PLAYERS {
            if self.may_short_castle(player) {
                let c = Piece::King.to_fen_char();
                fen.push(player.convert_fen_piece_char(c));
                any_castle = true;
            }
            else if self.may_long_castle(player) {
                let c = Piece::Queen.to_fen_char();
                fen.push(player.convert_fen_piece_char(c));
                any_castle = true;
            }
        }

        if !any_castle {
            fen.push('-');
        }

        fen.push(' ');

        if self.en_passant_file == usize::MAX {
            fen.push('-');
        }
        else {
            fen.push(('a' as usize + self.en_passant_file) as u8 as char);

            match self.turn {
                Player::White => fen.push('6'),
                Player::Black => fen.push('3')
            }
        };

        fen
    }
}

/// The entire state of a match necessary to progress it. This tracks the
/// current [Position] as well as historical data to enforce the threefold
/// repetition and fifty move rules.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct State {
    position: Position,
    history: Vec<Position>,
    last_irreversible: usize,
    fifty_move_clock: usize
}

impl State {

    /// Creates a new state in the initial configuration, i.e. in the
    /// [Position] described by [Position::initial] and empty move history.
    ///
    /// # Returns
    ///
    /// A new state in the initial configuration.
    pub fn initial() -> State {
        State {
            position: Position::initial(),
            history: Vec::new(),
            last_irreversible: 0,
            fifty_move_clock: 0
        }
    }

    /// Parses a FEN string representing an entire state. The string must
    /// contain six components, separated by spaces: the [Board], player to
    /// move (`w`/`b`), castling rights (a list of `k`, `q`, `K`, `Q` where
    /// case decides which player may still castle and `k`/`q` indicates
    /// kingside/queenside respectively; `-` if no castles are allowed
    /// anymore), en passant target square (in algebraic notation; `-` if no en
    /// passant is available), half move clock (counting the half moves since
    /// the last pawn move or capture), and full move clock (stating the
    /// current 1-based move index).
    ///
    /// # Arguments
    ///
    /// * `fen`: A complete FEN string.
    ///
    /// # Returns
    ///
    /// A new state constructed from the given FEN.
    ///
    /// # Errors
    ///
    /// Any [FenError].
    ///
    /// # Example
    ///
    /// ```
    /// // The initial game state. Board is in the initial configuration, "w"
    /// // indicates white to move, "KQkq" means both white and black can still
    /// // castle both kingside and queenside, en passant target is "-" as no
    /// // en passant is available, half move clock is 0 and full move clock is
    /// // 1.
    ///
    /// let initial_state = State::from_fen(
    ///     "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1")
    ///     .unwrap();
    /// ```
    pub fn from_fen(fen: &str) -> FenResult<State> {
        let mut parts = fen.split(' ');
        let pos_parts = (0..4)
            .map(|_| next_state_part(&mut parts, fen))
            .collect::<Result<Vec<_>, _>>()?;
        let position = Position::from_fen_parts(
            pos_parts[0], pos_parts[1], pos_parts[2], pos_parts[3])?;
        let half_move_clock_fen = next_state_part(&mut parts, fen)?;
        let half_move_clock: usize = half_move_clock_fen.parse()
            .map_err(|error| FenError::ParseHalfMoveClockError {
                part: half_move_clock_fen.to_owned(),
                error
            })?;
        let full_move_clock_fen = next_state_part(&mut parts, fen)?;
        let full_move_clock: usize = full_move_clock_fen.parse()
            .map_err(|error| FenError::ParseFullMoveClockError {
                part: full_move_clock_fen.to_owned(),
                error
            })?;

        if half_move_clock > rules::DRAW_NO_PROGRESS_COUNT {
            return Err(FenError::HalfMoveClockOverflow(half_move_clock));
        }

        if full_move_clock == 0 {
            return Err(FenError::FullMoveClockZero);
        }

        let max_half_move_clock =
            full_move_clock * 2 + position.turn() as usize - 2;

        if half_move_clock > max_half_move_clock {
            return Err(FenError::HistoryTooShort {
                half_move_clock,
                full_move_clock,
                turn: position.turn()
            });
        }

        Ok(State {
            position,
            history: Vec::new(),
            last_irreversible: 0,
            fifty_move_clock: half_move_clock
        })
    }

    /// Gets the current [Position].
    ///
    /// # Returns
    ///
    /// An immutable reference to the current [Position].
    pub fn position(&self) -> &Position {
        &self.position
    }

    /// Gets a slice containing all previous positions, excluding the current
    /// one, in the order they happened. If this is empty, the current position
    /// represents the initial state.
    ///
    /// # Returns
    ///
    /// A slice of all previous positions, where the first entry is the initial
    /// position (unless the game is in its initial state), followed by the one
    /// after the first half-move etc. The last position in the slice preceded
    /// the current one. 
    pub fn history(&self) -> &[Position] {
        &self.history
    }

    /// Gets a slice containing all previous positions since the last
    /// irreversible move, that is, a pawn move, a capture, or castling. The
    /// position directly after the move is the first in the slice.
    ///
    /// # Returns
    ///
    /// A slice containing all previous positions since the last irreversible
    /// move.
    pub fn reversible_history(&self) -> &[Position] {
        &self.history[self.last_irreversible..]
    }

    /// Gets the current state of the fifty move clock, which counts the number
    /// of consecutive half moves that have not made progress in terms of the
    /// fifty move rule, i.e. which were not captures or pawn moves. If this
    /// number reaches [rules::DRAW_NO_PROGRESS_COUNT], the game ends in a
    /// draw.
    ///
    /// # Returns
    ///
    /// The current state of the fifty move clock.
    pub fn fifty_move_clock(&self) -> usize {
        self.fifty_move_clock
    }

    /// Converts the current state into a FEN string in the format defined in
    /// [State::from_fen].
    ///
    /// # Returns
    ///
    /// A new string containing the FEN for this state.
    pub fn to_fen(&self) -> String {
        let mut fen = self.position.to_fen();

        let half_move_clock = self.fifty_move_clock;
        let full_move_clock = self.history.len() / 2 + 1;

        fen.push(' ');
        fen.push_str(&half_move_clock.to_string());
        fen.push(' ');
        fen.push_str(&full_move_clock.to_string());

        fen
    }
}
