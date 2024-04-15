//! This module defines the [Position] and [State] structs, which manage
//! information about the current game situation.

use crate::board::{Board, Bitboard, Location};
use crate::error::{FenError, FenResult, AlgebraicResult};
use crate::hash::{PositionHasher, IdHasher};
use crate::movement::{Move, list_moves, LEFT_FILE, RIGHT_FILE};
use crate::piece::Piece;
use crate::player::{Black, Player, StaticPlayer, White, PLAYER_COUNT, PLAYERS};
use crate::rules;

use serde::{Deserialize, Serialize};

/// Returned by [Position::make_move] to allow reverting the move with
/// [Position::unmake_move].
#[derive(Clone, Debug)]
pub struct PositionRevertInfo {
    short_castles: [bool; PLAYER_COUNT],
    long_castles: [bool; PLAYER_COUNT],
    en_passant_file: usize
}

/// A unique ID for [Position]s that is smaller than positions in terms of
/// memory. It can therefore be used as keys for hash maps or similar.
#[derive(Clone, Debug, Deserialize, Eq, Hash, PartialEq, Serialize)]
pub struct PositionId {
    pub board_id: [Bitboard; 4],
    pub additional_data: u8 // TODO move this into the bitboards somehow
}

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
    if fen == "-" {
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

            if !('a'..='h').contains(&file_char) ||
                    !('1'..='8').contains(&rank_char) {
                Err(FenError::InvalidEnPassantTarget(fen.to_owned()))
            }
            else {
                Ok(file_char as usize - 'a' as usize)
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
    /// i.e. all except [FenError::ParseHalfMoveClockError] and
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

    /// Mutably sets whose player's turn it is. Note this may cause the
    /// position to be invalid.
    ///
    /// # Arguments
    ///
    /// * `turn`: The [Player] whose turn it shall be.
    pub fn set_turn(&mut self, turn: Player) {
        self.turn = turn;
        self.en_passant_file = usize::MAX;
    }

    /// Gets a unique ID for this position. This can be used as keys for hash
    /// maps or similar.
    ///
    /// # Returns
    ///
    /// A unique [PositionId] for this position.
    pub fn unique_id(&self) -> PositionId {
        let mut board_id = self.board.unique_id();

        board_id[0] ^= Bitboard(0u64.wrapping_sub(self.long_castles[0] as u64));
        board_id[1] ^= Bitboard(0u64.wrapping_sub(self.long_castles[1] as u64));
        board_id[2] ^= Bitboard(0u64.wrapping_sub(self.short_castles[0] as u64));
        board_id[3] ^= Bitboard(0u64.wrapping_sub(self.short_castles[1] as u64));

        let additional_data =
            (self.en_passant_file as u8) << 1 | self.turn as u8;

        PositionId {
            board_id,
            additional_data
        }
    }

    fn check_rook_capture<P, H>(&mut self, captured: Option<Piece>,
        delta_mask: Bitboard, hasher: &mut H)
    where
        P: StaticPlayer,
        H: PositionHasher
    {
        if captured == Some(Piece::Rook) {
            let opponent = self.turn.opponent();

            if !(delta_mask & P::Opponent::CLOSE_ROOK_SINGLETON).is_empty() {
                self.disable_short_castling(opponent, hasher);
            }

            if !(delta_mask & P::Opponent::FAR_ROOK_SINGLETON).is_empty() {
                self.disable_long_castling(opponent, hasher);
            }
        }
    }

    #[inline]
    fn disable_short_castling<H>(&mut self, player: Player, hasher: &mut H)
    where
        H: PositionHasher
    {
        let index = player as usize;

        if self.short_castles[index] {
            hasher.on_castling_right_lost(player, false);
        }

        self.short_castles[index] = false;
    }

    #[inline]
    fn disable_long_castling<H>(&mut self, player: Player, hasher: &mut H)
    where
        H: PositionHasher
    {
        let index = player as usize;

        if self.long_castles[index] {
            hasher.on_castling_right_lost(player, true);
        }

        self.long_castles[index] = false;
    }

    #[inline]
    fn src_dest(&self, delta_mask: Bitboard, player: Player)
            -> (Location, Location) {
        let of_turn = self.board().of_player(player);
        let src = (delta_mask & of_turn).min_unchecked();
        let dest = (delta_mask & !of_turn).min_unchecked();

        (src, dest)
    }

    #[inline]
    fn notify_movement<H>(&self, delta_mask: Bitboard, moved: Piece,
        captured: Option<Piece>, hasher: &mut H)
    where
        H: PositionHasher
    {
        let (src, dest) = self.src_dest(delta_mask, self.turn);

        hasher.on_piece_left(moved, self.turn, src);
        hasher.on_piece_entered(moved, self.turn, dest);

        if let Some(captured) = captured {
            hasher.on_piece_left(captured, self.turn.opponent(), dest);
        }
    }
    
    #[inline]
    fn is_en_passant_possible_after_move<P>(&self, moved: Piece, delta_mask: Bitboard) -> bool
    where
        P: StaticPlayer
    {
        if moved == Piece::Pawn && !(delta_mask & P::SECOND_RANK).is_empty() &&
                !(delta_mask & P::FOURTH_RANK).is_empty() {
            let target_singleton = delta_mask & P::FOURTH_RANK;
            let left_neighbor = (target_singleton - LEFT_FILE) >> 1;
            let right_neighbor = (target_singleton - RIGHT_FILE) << 1;
            let neighbors = left_neighbor | right_neighbor;
            let opponent_pawns = self.board.of_player_and_kind(self.turn.opponent(), Piece::Pawn);

            return !(neighbors & opponent_pawns).is_empty();
        }
        
        false
    }

    fn apply_ordinary_move<P, H>(&mut self, moved: Piece, captured: Option<Piece>,
        delta_mask: Bitboard, hasher: &mut H)
    where
        P: StaticPlayer,
        H: PositionHasher
    {
        self.notify_movement(delta_mask, moved, captured, hasher);

        if self.is_en_passant_possible_after_move::<P>(moved, delta_mask) {
            self.en_passant_file = delta_mask.min_unchecked().file();
            hasher.on_en_passant_enabled(self.en_passant_file);
            return;
        }

        self.en_passant_file = usize::MAX;

        if moved == Piece::King {
            self.disable_short_castling(self.turn, hasher);
            self.disable_long_castling(self.turn, hasher);
        }

        if moved == Piece::Rook {
            if !(delta_mask & P::CLOSE_ROOK_SINGLETON).is_empty() {
                self.disable_short_castling(self.turn, hasher);
            }

            if !(delta_mask & P::FAR_ROOK_SINGLETON).is_empty() {
                self.disable_long_castling(self.turn, hasher);
            }
        }

        self.check_rook_capture::<P, _>(captured, delta_mask, hasher);
    }

    /// Applies the given move made by the given player to this position, that
    /// is, moves/removes/promotes all necessary pieces on the underlying board
    /// and updates metadata, such as castling states and the turn.
    ///
    /// # Arguments
    ///
    /// * `mov`: The [Move] to apply.
    ///
    /// # Returns
    ///
    /// A [PositionRevertInfo] to be passed to [Position::unmake_move] in case
    /// the move should be reverted.
    pub fn make_move(&mut self, mov: &Move) -> PositionRevertInfo {
        self.make_move_with_hasher(mov, &mut IdHasher)
    }

    pub fn make_move_with_hasher<H>(&mut self, mov: &Move, hasher: &mut H) -> PositionRevertInfo
    where
        H: PositionHasher
    {
        let revert_info = PositionRevertInfo {
            short_castles: self.short_castles,
            long_castles: self.long_castles,
            en_passant_file: self.en_passant_file
        };

        if let Some(en_passant_file) = self.en_passant_file() {
            hasher.on_en_passant_disabled(en_passant_file);
        }

        match *mov {
            Move::Ordinary { moved, captured, delta_mask } => {
                match self.turn {
                    Player::White =>
                        self.apply_ordinary_move::<White, _>(
                            moved, captured, delta_mask, hasher),
                    Player::Black =>
                        self.apply_ordinary_move::<Black, _>(
                            moved, captured, delta_mask, hasher)
                }
            },
            Move::Castle { king_delta_mask, rook_delta_mask } => {
                self.notify_movement(king_delta_mask, Piece::King, None, hasher);
                self.notify_movement(rook_delta_mask, Piece::Rook, None, hasher);
                self.disable_short_castling(self.turn, hasher);
                self.disable_long_castling(self.turn, hasher);
                self.en_passant_file = usize::MAX;
            },
            Move::Promotion { captured, delta_mask, promotion } => {
                let (src, dest) = self.src_dest(delta_mask, self.turn);

                hasher.on_piece_left(Piece::Pawn, self.turn, src);
                hasher.on_piece_entered(promotion, self.turn, dest);

                if let Some(captured) = captured {
                    hasher.on_piece_left(captured, self.turn.opponent(), dest);
                }

                match self.turn {
                    Player::White =>
                        self.check_rook_capture::<White, _>(
                            captured, delta_mask, hasher),
                    Player::Black =>
                        self.check_rook_capture::<Black, _>(
                            captured, delta_mask, hasher)
                }

                self.en_passant_file = usize::MAX;
            },
            Move::EnPassant { delta_mask, target } => {
                let (src, dest) = self.src_dest(delta_mask, self.turn);
                let target = target.min_unchecked();

                hasher.on_piece_left(Piece::Pawn, self.turn, src);
                hasher.on_piece_entered(Piece::Pawn, self.turn, dest);
                hasher.on_piece_left(
                    Piece::Pawn, self.turn.opponent(), target);

                self.en_passant_file = usize::MAX;
            }
        }

        self.board.make_move(self.turn, mov);
        self.turn = self.turn.opponent();
        hasher.on_turn_changed(self.turn);

        revert_info
    }

    /// Reverts the given move made by the given player to this position, that
    /// is, moves all pieces back, puts back captured pieces, and reverts
    /// promotions. In addition, all metadata such as castling rights and the
    /// turn is reverted. This restores the position after a call to
    /// [Position::make_move] with the same move.
    ///
    /// # Arguments
    ///
    /// * `mov`: The [Move] to revert.
    /// * `revert_info`: The [PositionRevertInfo] returned by the call to
    /// [Position::make_move] to revert.
    pub fn unmake_move(&mut self, mov: &Move,
            revert_info: PositionRevertInfo) {
        self.short_castles = revert_info.short_castles;
        self.long_castles = revert_info.long_castles;
        self.en_passant_file = revert_info.en_passant_file;
        self.turn = self.turn.opponent();
        self.board.unmake_move(self.turn, mov);
    }

    #[inline]
    fn notify_inverse_movement<H>(&mut self, delta_mask: Bitboard,
        moved: Piece, captured: Option<Piece>, hasher: &mut H)
    where
        H: PositionHasher
    {
        let turn = self.turn.opponent();
        let (src, dest) = self.src_dest(delta_mask, turn);

        hasher.on_piece_left(moved, turn, src);
        hasher.on_piece_entered(moved, turn, dest);

        if let Some(captured) = captured {
            hasher.on_piece_entered(captured, turn.opponent(), src);
        }
    }

    #[inline]
    fn notify_restored_castling_rights<H>(&mut self, revert_info: &PositionRevertInfo, hasher: &mut H, player: Player)
    where
        H: PositionHasher
    {
        let idx = player as usize;

        if !self.short_castles[idx] && revert_info.short_castles[idx] {
            hasher.on_castling_right_gained(player, false);
        }

        if !self.long_castles[idx] && revert_info.long_castles[idx] {
            hasher.on_castling_right_gained(player, true);
        }
    }

    pub fn unmake_move_with_hasher<H>(&mut self, mov: &Move, revert_info: PositionRevertInfo, hasher: &mut H)
    where
        H: PositionHasher
    {
        let turn = self.turn.opponent();
        let opponent = self.turn;

        self.notify_restored_castling_rights(&revert_info, hasher, turn);
        self.notify_restored_castling_rights(&revert_info, hasher, opponent);

        if let Some(en_passant_file) = self.en_passant_file() {
            hasher.on_en_passant_disabled(en_passant_file);
        }

        if revert_info.en_passant_file != usize::MAX {
            hasher.on_en_passant_enabled(revert_info.en_passant_file);
        }

        match *mov {
            Move::Ordinary { moved, captured, delta_mask } => {
                self.notify_inverse_movement(
                    delta_mask, moved, captured, hasher);
            },
            Move::Castle { king_delta_mask, rook_delta_mask } => {
                self.notify_inverse_movement(
                    king_delta_mask, Piece::King, None, hasher);
                self.notify_inverse_movement(
                    rook_delta_mask, Piece::Rook, None, hasher);
            },
            Move::Promotion { captured, delta_mask, promotion } => {
                let (src, dest) = self.src_dest(delta_mask, turn);

                hasher.on_piece_left(promotion, turn, src);
                hasher.on_piece_entered(Piece::Pawn, turn, dest);

                if let Some(captured) = captured {
                    hasher.on_piece_entered(captured, opponent, src);
                }
            },
            Move::EnPassant { delta_mask, target } => {
                let (src, dest) = self.src_dest(delta_mask, turn);
                let target = target.min_unchecked();

                hasher.on_piece_left(Piece::Pawn, turn, src);
                hasher.on_piece_entered(Piece::Pawn, turn, dest);
                hasher.on_piece_entered(Piece::Pawn, opponent, target);
            }
        }

        hasher.on_turn_changed(turn);

        self.unmake_move(mov, revert_info);
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

            if self.may_long_castle(player) {
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

const LIGHT_SQUARES: Bitboard = Bitboard(0x55aa55aa55aa55aa);
const DARK_SQUARES: Bitboard = Bitboard(0xaa55aa55aa55aa55);

/// An enumeration of the different outcomes a game of Chess can have.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Outcome {

    /// The given [Player] won the game.
    Victory(Player),

    /// Any condition for a draw was met.
    Draw
}

/// Returned by [State::make_move] to allow reverting the move with
/// [State::unmake_move].
#[derive(Clone, Debug)]
pub struct StateRevertInfo {
    position_revert_info: PositionRevertInfo,
    last_irreversible: usize,
    fifty_move_clock: usize
}

/// The entire state of a match necessary to progress it. This tracks the
/// current [Position] as well as historical data to enforce the threefold
/// repetition and fifty move rules.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct State<H: PositionHasher> {
    position: Position,
    history: Vec<H::Hash>,
    last_irreversible: usize,
    fifty_move_clock: usize,
    hasher: H
}

impl<H: PositionHasher> State<H> {

    /// Creates a new state in the initial configuration, i.e. in the
    /// [Position] described by [Position::initial] and empty move history.
    ///
    /// # Returns
    ///
    /// A new state in the initial configuration.
    pub fn initial() -> State<H> {
        let position = Position::initial();
        let hasher = H::init(&position);

        State {
            position: Position::initial(),
            history: Vec::new(),
            last_irreversible: 0,
            fifty_move_clock: 0,
            hasher
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
    pub fn from_fen(fen: &str) -> FenResult<State<H>> {
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

        let hasher = H::init(&position);

        Ok(State {
            position,
            history: Vec::new(),
            last_irreversible: 0,
            fifty_move_clock: half_move_clock,
            hasher
        })
    }

    /// Generate a state by replaying a history of moves given in algebraic
    /// notation, such as "Nxe7". For more information, see
    /// [Move::parse_algebraic]. Before the first move, the state is put in the
    /// initial position.
    ///
    /// # Arguments
    ///
    /// * `history`: An [Iterator] over [str] referencing instances that
    /// contain algebraic notations for single moves. The moves are applied in
    /// the order they are provided by this iterator.
    ///
    /// # Returns
    ///
    /// A new [State] that arises when the moves specified in `history` are
    /// applied to the initial state.
    ///
    /// # Errors
    ///
    /// Any [AlgebraicError](crate::error::AlgebraicError) according to their
    /// respective documentations.
    pub fn from_algebraic_history<S, I>(history: I)
        -> AlgebraicResult<State<H>>
    where
        S: AsRef<str>,
        I: Iterator<Item = S>
    {
        let mut state = State::initial();

        for algebraic in history {
            let mov =
                Move::parse_algebraic(state.position(), algebraic.as_ref())?;
            state.make_move(&mov);
        }

        Ok(state)
    }

    pub fn from_uci_history<S, I>(history: I) -> Option<State<H>>
    where
        S: AsRef<str>,
        I: Iterator<Item = S>
    {
        // TODO reduce code duplication with from_algebraic_history
        let mut state = State::initial();

        for algebraic in history {
            let mov = Move::parse_uci(state.position(), algebraic.as_ref())?;
            state.make_move(&mov);
        }

        Some(state)
    }

    /// Gets the current [Position].
    ///
    /// # Returns
    ///
    /// An immutable reference to the current [Position].
    pub fn position(&self) -> &Position {
        &self.position
    }

    pub fn position_mut(&mut self) -> &mut Position {
        &mut self.position
    }

    /// Gets a slice containing all previous position hashes, excluding the
    /// current one, in the order they happened. If this is empty, the current
    /// position represents the initial state.
    ///
    /// # Returns
    ///
    /// A slice of all previous position hashes, where the first entry is the
    /// initial  position (unless the game is in its initial state), followed
    /// by the one after the first half-move etc. The last position hash in the
    /// slice preceded the current one. 
    pub fn history(&self) -> &[H::Hash] {
        &self.history
    }

    /// Gets a slice containing all previous position hashes since the last
    /// irreversible move, that is, a pawn move, a capture, or castling. The
    /// position directly after the move is the first in the slice.
    ///
    /// # Returns
    ///
    /// A slice containing all previous position hashes since the last
    /// irreversible move.
    pub fn reversible_history(&self) -> &[H::Hash] {
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

    pub fn position_hash(&self) -> H::Hash {
        self.hasher.hash(&self.position)
    }

    /// Applies the given move made by the given player to this state, that is,
    /// moves/removes/promotes all necessary pieces on the underlying board,
    /// updates metadata, such as castling states and the turn, and tracks the
    /// history of moves for the fifty-move rule and three-fold-repetition
    /// rule.
    ///
    /// # Arguments
    ///
    /// * `mov`: The [Move] to apply.
    ///
    /// # Returns
    ///
    /// A [StateRevertInfo] to be passed to [State::unmake_move] in case the
    /// move should be reverted.
    pub fn make_move(&mut self, mov: &Move) -> StateRevertInfo {
        let index = self.history.len();
        self.history.push(self.position_hash());

        let position_revert_info =
            self.position.make_move_with_hasher(mov, &mut self.hasher);
        let revert_info = StateRevertInfo {
            position_revert_info,
            last_irreversible: self.last_irreversible,
            fifty_move_clock: self.fifty_move_clock
        };

        match mov {
            &Move::Ordinary { moved, captured, .. } => {
                if moved == Piece::Pawn || captured.is_some() {
                    self.last_irreversible = index;
                    self.fifty_move_clock = 0;
                }
                else {
                    self.fifty_move_clock += 1;
                }
            },
            Move::EnPassant { .. } | Move::Promotion { .. } => {
                self.last_irreversible = index;
                self.fifty_move_clock = 0;
            },
            Move::Castle { .. } => {
                self.last_irreversible = index;
                self.fifty_move_clock += 1;
            }
        }

        revert_info
    }

    /// Reverts the given move made by the given player to this state, that is,
    /// moves all pieces back, puts back captured pieces, and reverts
    /// promotions. In addition, all metadata such as castling rights and the
    /// turn is reverted and the newest state is removed from the tracked
    /// history. This restores the position after a call to [State::make_move]
    /// with the same move.
    ///
    /// # Arguments
    ///
    /// * `mov`: The [Move] to revert.
    /// * `revert_info`: The [StateRevertInfo] returned by the call to
    /// [State::make_move] to revert.
    pub fn unmake_move(&mut self, mov: &Move, revert_info: StateRevertInfo) {
        self.history.pop();
        self.last_irreversible = revert_info.last_irreversible;
        self.fifty_move_clock = revert_info.fifty_move_clock;
        self.position.unmake_move_with_hasher(
            mov, revert_info.position_revert_info, &mut self.hasher);
    }

    /// Indicates whether this state is a draw according to the stateful checks
    /// that are part of he rules of chess. These are
    ///
    /// * Draw by repetition
    /// * Draw by fifty-move rule
    /// * Draw by insufficient material
    ///
    /// In particular, this does *not* check for draw by stalemate.
    ///
    /// # Returns
    ///
    /// True, if and only if this state is a draw by any stateful checks.
    pub fn is_stateful_draw(&self) -> bool {
        const MIN_LEN_FOR_REPETITION: usize =
            (rules::DRAW_REPETITION_COUNT - 1) * 4;

        if self.fifty_move_clock >= rules::DRAW_NO_PROGRESS_COUNT {
            // Draw by fifty-move rule

            return true;
        }

        let reversible_history = self.reversible_history();

        if reversible_history.len() >= MIN_LEN_FOR_REPETITION {
            let mut repetitions = 1;
            let position_hash = self.position_hash();
    
            for old_position_hash in reversible_history {
                if old_position_hash == &position_hash {
                    repetitions += 1;
    
                    if repetitions == rules::DRAW_REPETITION_COUNT {
                        // Draw by repetition
    
                        return true;
                    }
                }
            }
        }

        let board = self.position.board();

        if (board.of_kind(Piece::Pawn) | board.of_kind(Piece::Rook) |
                board.of_kind(Piece::Queen)).is_empty() {
            let knights = board.of_kind(Piece::Knight);
            let bishops = board.of_kind(Piece::Bishop);
            let insufficient_material =
                (knights.len() == 1 && bishops.is_empty()) ||
                (knights.is_empty() && (bishops.is_subset(LIGHT_SQUARES) ||
                    bishops.is_subset(DARK_SQUARES)));

            if insufficient_material {
                // Draw by insufficient material

                return true;
            }
        }

        false
    }

    /// Check whether this state constitutes an end state of the game and, if
    /// so, determines the outcome.
    ///
    /// # Returns
    ///
    /// `Some(outcome)` with the [Outcome] of the game that ended in this state
    /// and `None` if the game has not yet ended.
    pub fn compute_outcome(&self) -> Option<Outcome> {
        let (moves, check) = list_moves(&self.position);

        if moves.is_empty() {
            if check {
                return Some(Outcome::Victory(self.position.turn().opponent()));
            }
            else {
                // Draw by stalemate

                return Some(Outcome::Draw);
            }
        }

        if self.is_stateful_draw() {
            Some(Outcome::Draw)
        }
        else {
            None
        }
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

#[cfg(test)]
mod tests {

    use super::*;

    const UNSET: usize = 1337;

    fn test_move(fen: &str, mov: Move, assertions: impl Fn(&State<IdHasher>)) {
        let mut state = State::from_fen(fen).unwrap();
        // make last_irreversible testable
        state.last_irreversible = UNSET;
        let state_clone = state.clone();
        let revert_info = state.make_move(&mov);

        assertions(&state);

        state.unmake_move(&mov, revert_info);

        assert_eq!(state_clone, state);
    }

    #[test]
    fn normal_move() {
        // Board (white to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │ r │ n │ b │ q │ k │ b │ n │ r │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ p │ p │ p │ p │ p │ p │ p │ p │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ P │ P │ P │ P │ P │ P │ P │ P │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ R │ N │ B │ Q │ K │ B │ N │ R │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // White moves the knight to c3.

        let fen = "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1";
        let mov = Move::Ordinary {
            moved: Piece::Knight,
            captured: None,
            delta_mask: Bitboard(0x0000000000040002)
        };

        test_move(fen, mov, |state| {
            assert_eq!(Player::Black, state.position().turn());
            assert_eq!(1, state.fifty_move_clock());
            assert_eq!(UNSET, state.last_irreversible);
        });
    }

    #[test]
    fn pawn_move_resets_fifty_move_clock() {
        // Board (white to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │ r │   │ b │ q │ k │   │   │ r │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ p │ p │ p │ p │   │ p │ p │ p │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ n │   │   │ n │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ b │   │ p │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ B │   │ P │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ N │   │   │ N │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ P │ P │ P │ P │   │ P │ P │ P │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ R │   │ B │ Q │ K │   │   │ R │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // White plays pawn to d3, resetting the fifty-move-clock.

        let fen = "r1bqk2r/pppp1ppp/2n2n2/2b1p3/2B1P3/2N2N2/PPPP1PPP/R1BQK2R \
            w KQkq - 6 5";
        let mov = Move::Ordinary {
            moved: Piece::Pawn,
            captured: None,
            delta_mask: Bitboard(0x0000000000080800)
        };

        test_move(fen, mov, |state| {
            assert_eq!(0, state.fifty_move_clock());
            assert_eq!(0, state.last_irreversible);
        });
    }

    #[test]
    fn promotion_resets_fifty_move_clock() {
        // Board (white to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ k │ P │ K │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // White plays pawn to d8 and promotes to a queen, resetting the
        // fifty-move-clock.

        let fen = "8/2kPK3/8/8/8/8/8/8 w - - 12 45";
        let mov = Move::Promotion {
            promotion: Piece::Queen,
            captured: None,
            delta_mask: Bitboard(0x0808000000000000)
        };

        test_move(fen, mov, |state| {
            assert_eq!(0, state.fifty_move_clock());
            assert_eq!(0, state.last_irreversible);
        });
    }

    #[test]
    fn capture_resets_fifty_move_clock() {
        // Board (black to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │ r │   │ b │ q │ k │   │   │ r │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ p │ p │ p │   │   │ p │ p │ p │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ n │ p │   │ n │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ b │   │ p │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ B │   │ P │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ N │ P │ B │ N │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ P │ P │ P │   │   │ P │ P │ P │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ R │   │   │ Q │ K │   │   │ R │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // Black takes the bishop on e3, resetting the fifty-move-clock.

        let fen = "r1bqk2r/ppp2ppp/2np1n2/2b1p3/2B1P3/2NPBN2/PPP2PPP/R2QK2R b \
            KQkq - 1 8";
        let mov = Move::Ordinary {
            moved: Piece::Bishop,
            captured: Some(Piece::Bishop),
            delta_mask: Bitboard(0x0000000400100000)
        };

        test_move(fen, mov, |state| {
            assert_eq!(0, state.fifty_move_clock());
            assert_eq!(0, state.last_irreversible);
        });
    }

    #[test]
    fn castle_resets_reversible_history_but_not_fifty_move_clock() {
        // Board (white to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │ r │   │ b │ q │ k │   │   │ r │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ p │ p │ p │ p │   │ p │ p │ p │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ n │   │   │ n │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ b │   │ p │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ B │   │ P │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ N │   │   │ N │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ P │ P │ P │ P │   │ P │ P │ P │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ R │   │ B │ Q │ K │   │   │ R │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // White castles short, resetting reversible history (used internally)
        // but no the fifty-move-clock (which is a Chess rule that does not
        // consider castling as an irreversible move).

        let fen = "r1bqk2r/pppp1ppp/2n2n2/2b1p3/2B1P3/2N2N2/PPPP1PPP/R1BQK2R \
            w KQkq - 6 5";
        let mov = Move::Castle {
            king_delta_mask: Bitboard(0x0000000000000050),
            rook_delta_mask: Bitboard(0x00000000000000a0)
        };

        test_move(fen, mov, |state| {
            assert_eq!(7, state.fifty_move_clock());
            assert_eq!(0, state.last_irreversible);
        });
    }

    #[test]
    fn castle_sets_castling_state() {
        // Board (black to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │ r │   │ b │ q │ k │   │   │ r │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ p │ p │ p │ p │   │ p │ p │ p │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ n │   │   │ n │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ b │   │ p │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ B │   │ P │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ N │   │   │ N │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ P │ P │ P │ P │   │ P │ P │ P │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ R │   │ B │ Q │   │ R │ K │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // Black castles short and is therefore no longer allowed to castle in
        // the future.

        let fen = "r1bqk2r/pppp1ppp/2n2n2/2b1p3/2B1P3/2N2N2/PPPP1PPP/R1BQ1RK1 \
            b kq - 7 6";
        let mov = Move::Castle {
            king_delta_mask: Bitboard(0x5000000000000000),
            rook_delta_mask: Bitboard(0xa000000000000000)
        };

        test_move(fen, mov, |state| {
            assert!(!state.position().may_long_castle(Player::Black));
            assert!(!state.position().may_short_castle(Player::Black));
            assert!(!state.position().may_long_castle(Player::White));
            assert!(!state.position().may_short_castle(Player::White));
        });
    }

    #[test]
    fn rook_move_sets_its_castling_state() {
        // Board (white to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │ r │   │ b │ q │ k │   │   │ r │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ p │ p │ p │ p │   │ p │ p │ p │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ n │   │   │ n │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ b │   │ p │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ B │   │ P │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ N │   │   │ N │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ P │ P │ P │ P │   │ P │ P │ P │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ R │   │ B │ Q │ K │   │   │ R │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // White mouse-slips the rook to f1 and subsequently is no longer
        // allowed to castle short.

        let fen = "r1bqk2r/pppp1ppp/2n2n2/2b1p3/2B1P3/2N2N2/PPPP1PPP/R1BQK2R \
            w KQkq - 0 1";
        let mov = Move::Ordinary {
            moved: Piece::Rook,
            captured: None,
            delta_mask: Bitboard(0x00000000000000a0)
        };

        test_move(fen, mov, |state| {
            assert!(state.position().may_long_castle(Player::White));
            assert!(!state.position().may_short_castle(Player::White));
        });
    }

    #[test]
    fn rook_being_captured_sets_castling_state() {
        // Board (white to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │ r │   │   │   │ k │   │   │ r │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │ B │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │ K │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // White captures the rook on a8, which prevents black from castling
        // long in the future.

        let fen = "r3k2r/8/8/3B4/3K4/8/8/8 w kq - 0 1";
        let mov = Move::Ordinary {
            moved: Piece::Bishop,
            captured: Some(Piece::Rook),
            delta_mask: Bitboard(0x0100000800000000)
        };

        test_move(fen, mov, |state| {
            assert!(!state.position().may_long_castle(Player::Black));
            assert!(state.position().may_short_castle(Player::Black));
        });
    }

    #[test]
    fn promotion_capturing_rook_sets_castling_state() {
        // Board (black to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │ k │ b │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │ n │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │ Q │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │ p │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ R │   │   │   │ K │   │   │ R │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // Black captures the rook on h1 with the pawn, promoting to a knight.
        // Capturing the rook prevents white from castling short in the future.

        let fen = "8/8/3kb3/5n2/6Q1/8/1p6/R3K2R b KQ - 0 1";
        let mov = Move::Promotion {
            promotion: Piece::Knight,
            captured: Some(Piece::Rook),
            delta_mask: Bitboard(0x0000000000004080)
        };

        test_move(fen, mov, |state| {
            assert!(state.position().may_long_castle(Player::White));
            assert!(!state.position().may_short_castle(Player::White));
        });
    }

    #[test]
    fn king_move_sets_castling_state() {
        // Board (white to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │ r │   │ b │ q │ k │   │   │ r │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ p │ p │ p │ p │   │ p │ p │ p │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ n │   │   │ n │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ b │   │ p │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ B │   │ P │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ N │   │   │ N │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ P │ P │ P │ P │   │ P │ P │ P │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ R │   │ B │ Q │ K │   │   │ R │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // White mouse-slips the king to f1 and subsequently is no longer
        // allowed to castle.

        let fen = "r1bqk2r/pppp1ppp/2n2n2/2b1p3/2B1P3/2N2N2/PPPP1PPP/R1BQK2R \
            w KQkq - 0 1";
        let mov = Move::Ordinary {
            moved: Piece::King,
            captured: None,
            delta_mask: Bitboard(0x0000000000000030)
        };

        test_move(fen, mov, |state| {
            assert!(!state.position().may_long_castle(Player::White));
            assert!(!state.position().may_short_castle(Player::White));
        });
    }

    #[test]
    fn pawn_double_push_sets_en_passant_file() {
        // Board (white to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │ r │ n │ b │ q │ k │ b │ n │ r │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ p │ p │ p │ p │ p │ p │ p │ p │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ P │ P │ P │ P │ P │ P │ P │ P │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ R │ N │ B │ Q │ K │ B │ N │ R │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // White moves the pawn to d4.

        let fen = "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1";
        let mov = Move::Ordinary {
            moved: Piece::Pawn,
            captured: None,
            delta_mask: Bitboard(0x0000000008000800)
        };

        test_move(fen, mov, |state| {
            assert_eq!(Some(3), state.position().en_passant_file());
        });
    }

    #[test]
    fn any_move_resets_en_passant_file() {
        // Board (black to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │ r │ n │ b │ q │ k │ b │ n │ r │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ p │ p │ p │ p │ p │ p │ p │ p │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │ P │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ P │ P │ P │   │ P │ P │ P │ P │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ R │ N │ B │ Q │ K │ B │ N │ R │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // Black plays knight to f6, resetting the en passant state.

        let fen = "rnbqkbnr/pppppppp/8/8/3P4/8/PPP1PPPP/RNBQKBNR b KQkq - 0 1";
        let mov = Move::Ordinary {
            moved: Piece::Knight,
            captured: None,
            delta_mask: Bitboard(0x4000200000000000)
        };

        test_move(fen, mov, |state| {
            assert!(state.position().en_passant_file().is_none());
        });
    }

    #[test]
    fn checkmate() {
        // Board (white to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │ r │   │ b │ q │ k │ b │   │ r │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ p │ p │ p │ p │   │ p │ p │ p │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ n │   │   │ n │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │ p │   │   │ Q │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ B │   │ P │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ P │ P │ P │ P │   │ P │ P │ P │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ R │ N │ B │   │ K │   │ N │ R │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // White takes the pawn on f7 with the queen, which is checkmate.

        let fen = "r1bqkb1r/pppp1ppp/2n2n2/4p2Q/2B1P3/8/PPPP1PPP/RNB1K1NR w \
            KQkq - 0 1";
        let mov = Move::Ordinary {
            moved: Piece::Queen,
            captured: Some(Piece::Pawn),
            delta_mask: Bitboard(0x0020008000000000)
        };

        test_move(fen, mov, |state| {
            assert_eq!(Some(Outcome::Victory(Player::White)),
                state.compute_outcome());
        })
    }

    #[test]
    fn threefold_repetition() {
        // Board (black to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │ r │   │ b │ q │ k │ b │ n │ r │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ p │ p │ p │ p │ p │ p │ p │ p │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ n │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ P │ P │ P │ P │ P │ P │ P │ P │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ R │ N │ B │ Q │ K │ B │ N │ R │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // Where the history is as follows.
        //
        // 1. Na3 Na6
        // 2. Nb1 Nb8
        // 3. Na3 Na6
        // 4. Nb1
        //
        // Black now plays Nb8, which repeats the initial position for the
        // third time. This causes a draw by repetition.

        let mut state: State<IdHasher> = State::from_algebraic_history(
            "Na3 Na6 Nb1 Nb8 Na3 Na6 Nb1".split(' ')).unwrap();
        let mov = Move::Ordinary {
            moved: Piece::Knight,
            captured: None,
            delta_mask: Bitboard(0x0200010000000000)
        };
        
        assert_eq!(None, state.compute_outcome());

        state.make_move(&mov);

        assert_eq!(Some(Outcome::Draw), state.compute_outcome());
    }

    #[test]
    fn fifty_move_rule() {
        // Board (white to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ k │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │ p │   │ p │   │   │ p │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ p │   │   │ P │   │   │ P │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ P │   │ P │ K │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // Where 99 half-moves without progress have been made. White moves the
        // king to e3, triggering a draw by fifty-move-rule.

        let mut state: State<IdHasher> = State::from_fen(
            "8/8/2k5/1p1p2p1/p2P2P1/P1PK4/8/8 w - - 99 106").unwrap();
        let mov = Move::Ordinary {
            moved: Piece::King,
            captured: None,
            delta_mask: Bitboard(0x0000000000180000)
        };

        assert_eq!(None, state.compute_outcome());

        state.make_move(&mov);

        assert_eq!(Some(Outcome::Draw), state.compute_outcome());
    }

    #[test]
    fn insufficient_material_king_vs_king() {
        // Board (black to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ k │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │ K │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // As it is king vs king, the game is a draw by insufficient material.

        let state: State<IdHasher> = State::from_fen(
            "8/8/2k5/8/5K2/8/8/8 b - - 0 1").unwrap();

        assert_eq!(Some(Outcome::Draw), state.compute_outcome());
    }

    #[test]
    fn insufficient_material_knight_vs_king() {
        // Board (white to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ k │ N │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │ K │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // As it is knight and king vs king, the game is a draw by insufficient
        // material.

        let state: State<IdHasher> = State::from_fen(
            "8/8/2kN4/8/5K2/8/8/8 w - - 0 1").unwrap();

        assert_eq!(Some(Outcome::Draw), state.compute_outcome());
    }

    #[test]
    fn insufficient_material_bishop_vs_king() {
        // Board (black to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ k │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │ b │ K │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // As it is bishop and king vs king, the game is a draw by insufficient
        // material.

        let state: State<IdHasher> = State::from_fen(
            "8/8/2k5/8/4bK2/8/8/8 b - - 0 1").unwrap();

        assert_eq!(Some(Outcome::Draw), state.compute_outcome());
    }

    #[test]
    fn insufficient_material_equally_colored_bishops() {
        // Board (white to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ k │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │ B │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │ b │ K │ B │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // While there are three bishops on the board, they are all of the same
        // color. Hence, the game is a draw by insufficient material.

        let state: State<IdHasher> = State::from_fen(
            "8/8/2k5/7B/4bKB1/8/8/8 w - - 0 1").unwrap();

        assert_eq!(Some(Outcome::Draw), state.compute_outcome());
    }

    #[test]
    fn sufficient_material_opposite_colored_bishops() {
        // Board (black to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ k │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │ B │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │ b │ K │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // As the two remaining bishops on the board are of opposite colors,
        // the game is not a draw.

        let state: State<IdHasher> = State::from_fen(
            "8/8/2k5/6B1/4bKB1/8/8/8 b - - 0 1").unwrap();

        assert_eq!(None, state.compute_outcome());
    }

    #[test]
    fn sufficient_material_knight_vs_knight() {
        // Board (white to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │ k │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │ n │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │ N │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │ K │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // As there are still two knights on the board, the game is not a draw.

        let state: State<IdHasher> = State::from_fen(
            "8/8/3k4/6n1/6N1/3K4/8/8 w - - 0 1").unwrap();

        assert_eq!(None, state.compute_outcome());
    }

    #[test]
    fn sufficient_material_rook_vs_king() {
        // Board (black to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │ k │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │ r │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │ K │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // As there is still a rook on the board, the game is not a draw.

        let state: State<IdHasher> = State::from_fen(
            "8/8/3k4/8/6Q1/3K4/8/8 b - - 0 1").unwrap();

        assert_eq!(None, state.compute_outcome());
    }

    #[test]
    fn sufficient_material_queen_vs_king() {
        // Board (black to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │ k │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │ Q │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │ K │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // As there is still a queen on the board, the game is not a draw.

        let state: State<IdHasher> = State::from_fen(
            "8/8/3k4/8/6Q1/3K4/8/8 b - - 0 1").unwrap();

        assert_eq!(None, state.compute_outcome());
    }

    #[test]
    fn sufficient_material_pawn_vs_king() {
        // Board (white to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │ k │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │ P │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │ K │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // As there is still a pawn on the board, the game is not a draw.

        let state: State<IdHasher> = State::from_fen(
            "8/8/3k4/8/6P1/3K4/8/8 w - - 0 1").unwrap();

        assert_eq!(None, state.compute_outcome());
    }
}
