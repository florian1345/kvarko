//! This module defines the [Move] type which represents a single move a player
//! can make in a given position. It also contains a move generation algorithm
//! accessible through the function [list_moves].

use crate::board::{Bitboard, Location, Board};
use crate::piece::Piece;
use crate::player::{Black, CastleInfo, Player, StaticPlayer, White};
use crate::rules::PROMOTABLE;
use crate::state::Position;

kvarko_proc_macro::load_magics! { "kvarko-model/magics.json" }

const KNIGHT_ATTACK_MASKS: [Bitboard; 64] =
    kvarko_proc_macro::knight_attacks!();
const KING_ATTACK_MASKS: [Bitboard; 64] = kvarko_proc_macro::king_attacks!();

const LEFT_FILE: Bitboard = Bitboard(0x0101010101010101);
const RIGHT_FILE: Bitboard = Bitboard(0x8080808080808080);
const WHITE_EN_PASSANT_TARGET_RANK: usize = 5;
const BLACK_EN_PASSANT_TARGET_RANK: usize = 2;

fn get_slider_attack(occupancy: Bitboard, square: usize, magics: &[Magic; 64])
        -> Bitboard {
    let magic = &magics[square];
    let occupancy = magic.premask & occupancy;
    let shift = magic.magic >> 58;
    let index = (magic.magic.wrapping_mul(occupancy.0) >> shift) as usize;
    let index = index + magic.offset;

    attack_entry(index) & magic.postmask
}

fn get_pawn_push<D: StaticPlayer>(occupancy: Bitboard,
        square_singleton: Bitboard) -> Bitboard {
    let free = !occupancy;
    let progress = D::forward(square_singleton) & free;
    progress | D::forward(progress) & free & D::FOURTH_RANK
}

fn get_pawn_attack<D: StaticPlayer>(square_singleton: Bitboard) -> Bitboard {
    let straight = D::forward(square_singleton);
    let diagonal =
        ((straight << 1) & !RIGHT_FILE) | ((straight >> 1) & !LEFT_FILE);
    diagonal
}

fn get_bishop_attack(occupancy: Bitboard, square: Location) -> Bitboard {
    get_slider_attack(occupancy, square.0, &BISHOP_MAGICS)
}

fn get_rook_attack(occupancy: Bitboard, square: Location) -> Bitboard {
    get_slider_attack(occupancy, square.0, &ROOK_MAGICS)
}

fn get_queen_attack(occupancy: Bitboard, square: Location) -> Bitboard {
    get_bishop_attack(occupancy, square) | get_rook_attack(occupancy, square)
}

fn get_knight_attack(square: Location) -> Bitboard {
    KNIGHT_ATTACK_MASKS[square.0]
}

fn get_king_attack(square: Location) -> Bitboard {
    KING_ATTACK_MASKS[square.0]
}

/// Represents a move made by a single player. In technical Chess terminology,
/// this is referred to as a ply or half-move. The term "move" in this context
/// refers to the movement of a piece, i.e. a state change on the board.
///
/// Different kinds of moves are realized as different variants, although most
/// moves - including captures - are covered by [Move::Ordinary].
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Move {

    /// Any move made by one piece to one destination square which now holds
    /// the moved piece. This requires no other squares to be affected and the
    /// single moved piece not to change, but includes captures.
    Ordinary {

        /// The type of [Piece] that was moved.
        moved: Piece,

        /// [Option::Some] containing the type of [Piece] that was captured if
        /// the move is a capture, and [Option::None] otherwise. This is mainly
        /// used for revertability reasons.
        captured: Option<Piece>,

        /// A [Bitboard] which contains both the source and destination square
        /// of the moved piece. As only one of these squares can be occupied by
        /// the moving player, the current state of the board is sufficient to
        /// to determine which square is the source and which the destination.
        delta_mask: Bitboard
    },

    /// An en-passant capture, where a pawn moves just behind an enemy pawn
    /// that just progressed two squares in the last moves, capturing the enemy
    /// pawn. This is not [Move::Ordinary] as it influences a square other than
    /// the source and destination, namely the field occupied by the captured
    /// enemy pawn.
    EnPassant {
        delta_mask: Bitboard,

        // TODO find better name; this is not target, this is captured
        target: Bitboard
    },

    /// Any move that causes a pawn promotion, i.e. where a pawn arrives at the
    /// opponent's end of the board. This is not [Move::Ordinary] as the piece
    /// that arrives at the destination is different to the one that departed
    /// from the source.
    Promotion {
        promotion: Piece,
        captured: Option<Piece>,
        delta_mask: Bitboard,
    },

    /// A castle move, where the king moves by two squares horizontally and the
    /// rook in the associated corner simultaneously moves to the square right
    /// next to the king, but on the other side as previously. This is not
    /// [Move::Ordinary] as two pieces move simultaneously.
    Castle {
        king_delta_mask: Bitboard,
        rook_delta_mask: Bitboard
    }
}

struct CheckEvasionMasks {
    capture_mask: Bitboard,
    push_mask: Bitboard
}

impl CheckEvasionMasks {
    fn union(&self) -> Bitboard {
        self.capture_mask | self.push_mask
    }
}

fn compute_pawn_attack_mask<D: StaticPlayer>(board: &Board, player: Player) -> Bitboard {
    let mut attack = Bitboard::EMPTY;
    let pawns = board.of_player_and_kind(player, Piece::Pawn).singletons();

    for pawn in pawns {
        attack |= get_pawn_attack::<D>(pawn);
    }

    attack
}

fn compute_opponent_attack_mask(position: &Position) -> Bitboard {
    let turn = position.turn();
    let opponent = turn.opponent();
    let board = position.board();

    let turn_pieces_no_king =
        board.of_player(turn) - board.of_kind(Piece::King);
    let occupancy = turn_pieces_no_king | board.of_player(opponent);
    let mut attack = match opponent {
        Player::White =>
            compute_pawn_attack_mask::<White>(&board, opponent),
        Player::Black =>
            compute_pawn_attack_mask::<Black>(&board, opponent)
    };

    // TODO reduce duplication

    let bishops = board.of_player_and_kind(opponent, Piece::Bishop).locations();

    for bishop in bishops {
        attack |= get_bishop_attack(occupancy, bishop);
    }

    let rooks = board.of_player_and_kind(opponent, Piece::Rook).locations();

    for rook in rooks {
        attack |= get_rook_attack(occupancy, rook);
    }

    let queens = board.of_player_and_kind(opponent, Piece::Queen).locations();

    for queen in queens {
        attack |= get_queen_attack(occupancy, queen);
    }

    let knights = board.of_player_and_kind(opponent, Piece::Knight).locations();

    for knight in knights {
        attack |= get_knight_attack(knight);
    }

    let kings = board.of_player_and_kind(opponent, Piece::King).locations();

    for king in kings {
        attack |= get_king_attack(king);
    }

    attack
}

struct KingAttackers {
    all: Bitboard,
    orthogonal_sliders: Bitboard,
    diagonal_sliders: Bitboard
}

fn compute_king_attackers(board: &Board, player: Player) -> KingAttackers {
    // TODO avoid recomputation (was already done in list_moves)

    let king_singleton = board.of_player_and_kind(player, Piece::King);
    let opponent = player.opponent();
    let opponent_bitboard = board.of_player(opponent);
    let occupancy = opponent_bitboard | board.of_player(player);

    let opponent_pawns = opponent_bitboard & board.of_kind(Piece::Pawn);
    let mut hopper_attackers = match player {
        Player::White =>
            get_pawn_attack::<White>(king_singleton) &
                opponent_pawns,
        Player::Black =>
            get_pawn_attack::<Black>(king_singleton) &
                opponent_pawns
    };

    let location = king_singleton.locations().next().unwrap();
    let opponent_bishops = opponent_bitboard & board.of_kind(Piece::Bishop);
    let opponent_queens = opponent_bitboard & board.of_kind(Piece::Queen);
    let diagonal_slider_attackers = get_bishop_attack(occupancy, location) &
        (opponent_bishops | opponent_queens);

    let opponent_rooks = opponent_bitboard & board.of_kind(Piece::Rook);
    let orthogonal_slider_attackers = get_rook_attack(occupancy, location) &
        (opponent_rooks | opponent_queens);

    let opponent_knights = opponent_bitboard & board.of_kind(Piece::Knight);
    hopper_attackers |= get_knight_attack(location) & opponent_knights;

    // Kings can never attack opponent kings, so we are done

    KingAttackers {
        all: hopper_attackers | diagonal_slider_attackers |
            orthogonal_slider_attackers,
        orthogonal_sliders: orthogonal_slider_attackers,
        diagonal_sliders: diagonal_slider_attackers
    }
}

/// Calls `process` for every singleton in `targets`, which is given as the
/// second parameter. The first parameter is the piece which was captured, if
/// any.
fn process_targets<Proc>(board: &Board, player: Player, targets: Bitboard,
    mut process: Proc)
where
    Proc: FnMut(Option<Piece>, Bitboard)
{
    let opponent_pieces = board.of_player(player.opponent());

    for target_singleton in targets.singletons() {
        let captured = if (opponent_pieces & target_singleton).is_empty() {
            None
        }
        else {
            Some(board.kind_at(target_singleton))
        };

        process(captured, target_singleton);
    }
}

/// Generates moves from the given source to all fields in the given targets
/// bitboard. Requires information which piece kind was `moved` and of which
/// `player`.
fn generate_moves_from_targets(moves: &mut Vec<Move>, board: &Board,
        player: Player, source_singleton: Bitboard, targets: Bitboard,
        moved: Piece) {
    process_targets(board, player, targets, |captured, target_singleton| {
        moves.push(Move::Ordinary {
            moved,
            captured,
            delta_mask: source_singleton | target_singleton
        })
    })
}

/// Generates promotions to all promotable piece kinds rom the given source to
/// all fields in the given targets bitboard. Requires information about which
/// `player` moved the pawn.
fn generate_promotions_from_targets(moves: &mut Vec<Move>, board: &Board,
        player: Player, source_singleton: Bitboard, targets: Bitboard) {
    process_targets(board, player, targets, |captured, target_singleton| {
        for promotion in PROMOTABLE {
            moves.push(Move::Promotion {
                promotion,
                captured,
                delta_mask: source_singleton | target_singleton
            })
        }
    })
}

/// Generates moves of pinned pieces in a specific direction.
///
/// # Arguments
///
/// * `moves`: The vector of moves to fill with generated moves.
/// * `board`: The current board.
/// * `player`: The player for which to generate moves.
/// * `mask`: A bitboard which contains all valid target fields for additional
/// filtering. For pawn moves, this needs to be done manually by
/// `generate_pawn_moves`.
/// * `get_attack`: A function which receives as input the occupancy bitboard
/// and a location and outputs the attack bitboard for a slider which moves in
/// the direction for which to detect pins from the location given the
/// occupancy.
/// * `non_queen_slider`: The piece kind which moves in the direction for which
/// to detect pins, except queens.
/// * `generate_pawn_moves`: A function which receives as input the vector of
/// moves to fill with generated moves, a singleton bitboard for a pawn, and a
/// mask of valid target squares, which is guaranteed to be a line in the
/// direction for which to detect pins. Generates moves for a pawn at the given
/// location, but only in the direction of pins. As an example, for diagonal
/// pins, this does not need to consider push moves, only captures and en
/// passant.
fn generate_directional_pin_moves<GetAt, GenPawn>(moves: &mut Vec<Move>,
    board: &Board, player: Player, mask: Bitboard, get_attack: GetAt,
    non_queen_slider: Piece, generate_pawn_moves: GenPawn) -> Bitboard
where
    GetAt: Fn(Bitboard, Location) -> Bitboard,
    GenPawn: Fn(&mut Vec<Move>, Bitboard, Bitboard)
{
    // General strategy: We cast rays from the given player's king by acting as
    // if it was a bishop/rook and find all own pieces hit by the rays. We then
    // "remove" those pieces and check if any enemy sliders moving in the same
    // direction are hit by the extended beams. We then cast rays from those
    // sliders, intersect them with the rays originating from the king and add
    // the singleton bitboard of the slider itself to compute the set of valid
    // destinations for the pinned piece.

    // TODO avoid recomputation (was already done in compute_king_attackers)

    let king_singleton = board.of_player_and_kind(player, Piece::King);
    let king_location = king_singleton.min_unchecked();
    let occupancy =
        board.of_player(Player::White) | board.of_player(Player::Black);

    let mut pins = Bitboard::EMPTY;
    let king_rays = get_attack(occupancy, king_location);
    let potential_pins = king_rays & board.of_player(player);
    let removed_occupancy = occupancy - potential_pins;
    let king_xrays = get_attack(removed_occupancy, king_location);
    let potential_pinners = king_xrays &
        board.of_player(player.opponent()) &
        (board.of_kind(non_queen_slider) | board.of_kind(Piece::Queen));

    for pinner_singleton in potential_pinners.singletons() {
        let pinner_location = pinner_singleton.min_unchecked();
        let pinner_rays = get_attack(removed_occupancy, pinner_location);
        let pin_singleton = pinner_rays & potential_pins;

        if pin_singleton.is_empty() {
            continue;
        }

        pins |= pin_singleton;

        let pin_targets =
            ((pinner_rays & king_xrays) | pinner_singleton) - pin_singleton;
        let pin_targets = pin_targets & mask;

        if board.is_of_kind_any(Piece::Pawn, pin_singleton) {
            generate_pawn_moves(moves, pin_singleton, pin_targets);
        }
        else if board.is_of_kind_any(non_queen_slider, pin_singleton) {
            generate_moves_from_targets(moves, board, player, pin_singleton,
                pin_targets, non_queen_slider);
        }
        else if board.is_of_kind_any(Piece::Queen, pin_singleton) {
            generate_moves_from_targets(moves, board, player, pin_singleton,
                pin_targets, Piece::Queen);
        }
    }

    pins
}

/// Generates all moves of pinned pieces of the given player. Returns a
/// bitboard of all fields on which a pinned piece stands. These can be
/// excluded for future move generation.
fn generate_pin_moves(moves: &mut Vec<Move>, board: &Board,
        en_passant_target: Bitboard, player: Player, masks: &CheckEvasionMasks)
        -> Bitboard {
    let mask = masks.union();
    let orthogonal_pins = generate_directional_pin_moves(
        moves, board, player, mask, get_rook_attack, Piece::Rook,
        |moves, pawn_singleton, mask|
            generate_pawn_push_moves(
                moves, board, player, pawn_singleton, masks.push_mask & mask));
    let diagonal_pins = generate_directional_pin_moves(
        moves, board, player, mask, get_bishop_attack, Piece::Bishop,
            |moves, pawn_singleton, mask|
                generate_pawn_capture_moves(moves, board, player,
                    pawn_singleton, en_passant_target,
                    &CheckEvasionMasks {
                        capture_mask: masks.capture_mask & mask,
                        push_mask: masks.push_mask & mask
                    }));

    orthogonal_pins | diagonal_pins
}

fn generate_ordinary_king_moves(moves: &mut Vec<Move>, board: &Board,
        player: Player, opponent_attack: Bitboard) {
    // TODO avoid recomputation (was already done in compute_king_attackers)

    let king_singleton = board.of_player_and_kind(player, Piece::King);
    let king_location = king_singleton.locations().next().unwrap();
    let targets = get_king_attack(king_location) & !board.of_player(player) &
        !opponent_attack;

    generate_moves_from_targets(
        moves, board, player, king_singleton, targets, Piece::King);
}

fn generate_pawn_push_move_from_direction<D: StaticPlayer>(moves: &mut Vec<Move>, board: &Board,
    player: Player, source_singleton: Bitboard, mask: Bitboard)
{
    // TODO avoid recomputation of occupancy

    let occupancy =
        board.of_player(Player::White) | board.of_player(Player::Black);
    let targets = get_pawn_push::<D>(occupancy, source_singleton);
    let targets = targets & mask;

    if (targets & D::EIGHTH_RANK).is_empty() {
        generate_moves_from_targets(
            moves, board, player, source_singleton, targets, Piece::Pawn);
    }
    else {
        generate_promotions_from_targets(
            moves, board, player, source_singleton, targets);
    }
}

fn generate_pawn_push_moves(moves: &mut Vec<Move>, board: &Board,
        player: Player, source_singleton: Bitboard, mask: Bitboard) {
    match player {
        Player::White =>
            generate_pawn_push_move_from_direction::<White>(
                moves, board, player, source_singleton, mask),
        Player::Black =>
            generate_pawn_push_move_from_direction::<Black>(
                moves, board, player, source_singleton, mask)
    }
}

fn generate_pawn_capture_moves_from_direction<D: StaticPlayer>(
        moves: &mut Vec<Move>, board: &Board, player: Player,
        source_singleton: Bitboard, en_passant_target: Bitboard,
        masks: &CheckEvasionMasks) {
    // TODO avoid recomputation of masks.union()

    let opponent_pieces = board.of_player(player.opponent());
    let attack = get_pawn_attack::<D>(source_singleton);
    let capture_targets = attack & opponent_pieces & masks.capture_mask;

    if (capture_targets & D::EIGHTH_RANK).is_empty() {
        generate_moves_from_targets(moves, board, player, source_singleton,
            capture_targets, Piece::Pawn);
    }
    else {
        generate_promotions_from_targets(
            moves, board, player, source_singleton, capture_targets);
    }

    // en passant

    if !(attack & en_passant_target).is_empty() {
        let en_passant_captured = D::back(en_passant_target);

        if !(en_passant_captured & masks.capture_mask).is_empty() ||
                !(en_passant_target & masks.push_mask).is_empty() {
            // Check for horizontal pins of both pawns simultaneously.

            let own_pieces = board.of_player(player);
            let own_king_singleton = board.of_kind(Piece::King) & own_pieces;

            if !(own_king_singleton & D::FIFTH_RANK).is_empty() {
                let opponent_orthogonal_sliders = (board.of_kind(Piece::Rook) |
                    board.of_kind(Piece::Queen)) & opponent_pieces;
                let occupancy = (own_pieces | opponent_pieces) -
                    source_singleton - en_passant_captured;

                if !(opponent_orthogonal_sliders & D::FIFTH_RANK).is_empty() {
                    for opponent_orthogonal_slider in
                            opponent_orthogonal_sliders.locations() {
                        let attack = get_rook_attack(occupancy,
                            opponent_orthogonal_slider);

                        if !(attack & own_king_singleton).is_empty() {
                            return;
                        }
                    }
                }
            }

            moves.push(Move::EnPassant {
                delta_mask: source_singleton | en_passant_target,
                target: en_passant_captured
            });
        }
    }
}

fn generate_pawn_capture_moves(moves: &mut Vec<Move>, board: &Board,
        player: Player, source_singleton: Bitboard,
        en_passant_target: Bitboard, masks: &CheckEvasionMasks) {
    match player {
        Player::White =>
            generate_pawn_capture_moves_from_direction::<White>(
                moves, board, player, source_singleton, en_passant_target,
                masks),
        Player::Black =>
            generate_pawn_capture_moves_from_direction::<Black>(
                moves, board, player, source_singleton, en_passant_target,
                masks)
    }
}

fn generate_knight_moves(moves: &mut Vec<Move>, board: &Board, player: Player,
        mask: Bitboard, source: Location) {
    // TODO avoid recomputation of valid

    let valid = !board.of_player(player);
    let targets = get_knight_attack(source) & mask & valid;
    let source_singleton = Bitboard::singleton(source);

    generate_moves_from_targets(
        moves, board, player, source_singleton, targets, Piece::Knight);
}

fn generate_slider_moves<GetAt>(moves: &mut Vec<Move>, board: &Board,
    player: Player, mask: Bitboard, source: Location, get_attack: GetAt,
    piece: Piece)
where
    GetAt: Fn(Bitboard, Location) -> Bitboard
{
    // TODO avoid recomputation of occupancy and valid

    let occupancy =
        board.of_player(Player::White) | board.of_player(Player::Black);
    let valid = !board.of_player(player);
    let targets = get_attack(occupancy, source) & mask & valid;
    let source_singleton = Bitboard::singleton(source);

    generate_moves_from_targets(
        moves, board, player, source_singleton, targets, piece);
}

fn generate_bishop_moves(moves: &mut Vec<Move>, board: &Board, player: Player,
        mask: Bitboard, source: Location) {
    generate_slider_moves(
        moves, board, player, mask, source, get_bishop_attack, Piece::Bishop)
}

fn generate_rook_moves(moves: &mut Vec<Move>, board: &Board, player: Player,
        mask: Bitboard, source: Location) {
    generate_slider_moves(
        moves, board, player, mask, source, get_rook_attack, Piece::Rook)
}

fn generate_queen_moves(moves: &mut Vec<Move>, board: &Board, player: Player,
        mask: Bitboard, source: Location) {
    generate_slider_moves(
        moves, board, player, mask, source, get_queen_attack, Piece::Queen)
}

fn generate_castle_move(moves: &mut Vec<Move>, opponent_attack: Bitboard,
        occupancy: Bitboard, castle_info: &CastleInfo) {
    if (opponent_attack & castle_info.passed).is_empty() &&
            (occupancy & castle_info.intermediate).is_empty() {
        moves.push(Move::Castle {
            king_delta_mask: castle_info.king_delta_mask,
            rook_delta_mask: castle_info.rook_delta_mask
        });
    }
}

fn generate_castle_moves_for<P>(moves: &mut Vec<Move>, position: &Position,
    player: Player, opponent_attack: Bitboard)
where
    P: StaticPlayer
{
    // TODO avoid recomputation of occupancy

    let board = position.board();
    let occupancy =
        board.of_player(Player::White) | board.of_player(Player::Black);

    if position.may_short_castle(player) {
        generate_castle_move(
            moves, opponent_attack, occupancy, &P::SHORT_CASTLE_INFO);
    }

    if position.may_long_castle(player) {
        generate_castle_move(
            moves, opponent_attack, occupancy, &P::LONG_CASTLE_INFO);
    }
}

fn generate_castle_moves(moves: &mut Vec<Move>, position: &Position,
        player: Player, opponent_attack: Bitboard) {
    match player {
        Player::White =>
            generate_castle_moves_for::<White>(
                moves, position, player, opponent_attack),
        Player::Black =>
            generate_castle_moves_for::<Black>(
                moves, position, player, opponent_attack)
    }
}

/// Returns a list of all legal moves that are available in a given position,
/// according to all the rules of chess. The active player is taken from the
/// position.
///
/// # Arguments
///
/// * `position`: The [Position] from which to list all legal moves.
///
/// # Returns
///
/// A new [Vec] containing all legal [Move]s, in no particular order.
pub fn list_moves(position: &Position) -> Vec<Move> {
    let turn = position.turn();
    let board = position.board();
    let en_passant_target = if let Some(en_passant_file) =
            position.en_passant_file() {
        let en_passant_rank = match turn {
            Player::White => WHITE_EN_PASSANT_TARGET_RANK,
            Player::Black => BLACK_EN_PASSANT_TARGET_RANK
        };
        let en_passant_target_location =
            Location::from_file_and_rank(en_passant_file, en_passant_rank)
                .unwrap();

        Bitboard::singleton(en_passant_target_location)
    }
    else {
        Bitboard::EMPTY
    };
    let occupancy =
        board.of_player(Player::White) | board.of_player(Player::Black);
    let mut moves = Vec::new();

    let king_singleton = board.of_player_and_kind(turn, Piece::King);
    let king_location = king_singleton.locations().next().unwrap();
    let opponent_attack = compute_opponent_attack_mask(position);
    let king_attackers = compute_king_attackers(board, turn);

    generate_ordinary_king_moves(&mut moves, board, turn, opponent_attack);

    if king_attackers.all.len() > 1 {
        // Double check => only the king can move.

        return moves;
    }

    let mut capture_mask = Bitboard::FULL;
    let mut push_mask = Bitboard::FULL;

    if king_attackers.all.len() == 1 {
        // Single check => there are three kinds of legal moves:
        // 1. King moves, which we already generated
        // 2. Capture the attacker (i.e. limit captures to attacker)

        capture_mask = king_attackers.all;

        // 3. Block attack if slider (i.e. limit non-captures to blocks)

        if let Some(diagonal_attacker_location) =
                king_attackers.diagonal_sliders.min() {
            push_mask = get_bishop_attack(occupancy, king_location) &
                get_bishop_attack(occupancy, diagonal_attacker_location);
        }
        else if let Some(orthogonal_attacker_location) =
                king_attackers.orthogonal_sliders.min() {
            push_mask = get_rook_attack(occupancy, king_location) &
                get_rook_attack(occupancy, orthogonal_attacker_location);
        }
        else {
            // King attacker is not a slider => blocking impossible.

            push_mask = Bitboard::EMPTY;
        }
    }
    else {
        generate_castle_moves(&mut moves, position, turn, opponent_attack);
    }

    let masks = CheckEvasionMasks {
        capture_mask,
        push_mask
    };
    let mask = masks.union();

    let pinned =
        generate_pin_moves(&mut moves, board, en_passant_target, turn, &masks);

    let pawns = board.of_player_and_kind(turn, Piece::Pawn) - pinned;
    let knights = board.of_player_and_kind(turn, Piece::Knight) - pinned;
    let bishops = board.of_player_and_kind(turn, Piece::Bishop) - pinned;
    let rooks = board.of_player_and_kind(turn, Piece::Rook) - pinned;
    let queens = board.of_player_and_kind(turn, Piece::Queen) - pinned;

    for pawn_singleton in pawns.singletons() {
        generate_pawn_push_moves(
            &mut moves, board, turn, pawn_singleton, mask);
        generate_pawn_capture_moves(&mut moves, board, turn, pawn_singleton,
            en_passant_target, &masks);
    }

    for knight in knights.locations() {
        generate_knight_moves(&mut moves, board, turn, mask, knight);
    }

    for bishop in bishops.locations() {
        generate_bishop_moves(&mut moves, board, turn, mask, bishop);
    }

    for rook in rooks.locations() {
        generate_rook_moves(&mut moves, board, turn, mask, rook);
    }

    for queen in queens.locations() {
        generate_queen_moves(&mut moves, board, turn, mask, queen);
    }

    moves
}

#[cfg(test)]
mod tests {

    use std::fmt::Debug;

    use super::*;

    #[test]
    fn rook_attack_1() {
        // Board (R = rook, X = occupied):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │ X │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │ X │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │ X │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ X │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ X │ X │   │ X │   │ R │
        // └───┴───┴───┴───┴───┴───┴───┴───┘

        let occupancy = Bitboard(0x00001080080400ac);
        let attack = get_rook_attack(occupancy, Location(7));

        assert_eq!(Bitboard(0x0000008080808060), attack);
    }

    #[test]
    fn rook_attack_2() {
        // Board (R = rook, X = occupied):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │ X │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │ X │   │ R │   │   │ X │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │ X │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ X │   │   │ X │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │ X │   │   │ X │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │ X │   │   │   │ X │
        // └───┴───┴───┴───┴───┴───┴───┴───┘

        let occupancy = Bitboard(0x0000104a08244888);
        let attack = get_rook_attack(occupancy, Location(35));

        assert_eq!(Bitboard(0x0808087608000000), attack);
    }

    #[test]
    fn bishop_attack_1() {
        // Board (R = rook, X = occupied):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │   │   │   │   │   │   │   │ B │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │ X │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │ X │   │   │   │   │ X │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │ X │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ X │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │ X │
        // └───┴───┴───┴───┴───┴───┴───┴───┘

        let occupancy = Bitboard(0x8000104208040080);
        let attack = get_bishop_attack(occupancy, Location(63));

        assert_eq!(Bitboard(0x0040201008000000), attack);
    }

    #[test]
    fn bishop_attack_2() {
        // Board (R = rook, X = occupied):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │ X │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ X │   │ X │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │ X │   │   │ X │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │ X │ B │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ X │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ X │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │ X │
        // └───┴───┴───┴───┴───┴───┴───┴───┘

        let occupancy = Bitboard(0x0100844818040480);
        let attack = get_bishop_attack(occupancy, Location(28));

        assert_eq!(Bitboard(0x0080402800284480), attack);
    }

    #[test]
    fn initial_state_allows_20_moves() {
        let position = Position::initial();
        let moves = list_moves(&position);

        assert_eq!(20, moves.len());
    }

    #[test]
    fn advanced_position_allows_correct_number_of_moves() {
        // Board (black to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │ r │   │ b │ q │ r │   │ k │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ p │ p │ p │   │   │ p │ p │ p │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ n │ p │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ B │ P │ N │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │ N │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ P │ P │ P │   │   │   │ P │ P │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ R │   │   │ Q │   │ R │ K │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // Notice the pin of the f7 pawn.

        let fen = "r1bqr1k1/ppp2ppp/2np4/8/2BPN3/5N2/PPP3PP/R2Q1RK1 b - -";
        let position = Position::from_fen(fen).unwrap();
        let moves = list_moves(&position);

        assert_eq!(33, moves.len());
    }

    fn list_moves_from(position: &Position, from: Location) -> Vec<Move> {
        let moves = list_moves(&position);
        let mut moves_from = Vec::new();

        for mov in moves {
            let delta_mask = match &mov {
                Move::Ordinary { delta_mask, .. } => delta_mask,
                Move::EnPassant { delta_mask, .. } => delta_mask,
                Move::Promotion { delta_mask, .. } => delta_mask,
                Move::Castle { king_delta_mask: delta_mask, .. } => delta_mask
            };

            if (*delta_mask).contains(from) {
                moves_from.push(mov);
            }
        }

        moves_from
    }

    fn assert_set_equals<T: Debug + Eq>(v1: Vec<T>, mut v2: Vec<T>) {
        assert_eq!(v1.len(), v2.len());

        for t1 in v1 {
            let mut index = usize::MAX;
            
            for (i, t2) in v2.iter().enumerate() {
                if &t1 == t2 {
                    index = i;
                    break;
                }
            }

            if index == usize::MAX {
                panic!("RHS does not contain {:?} ; RHS = {:?}", t1, v2);
            }

            v2.remove(index);
        }
    }

    #[test]
    fn promotion_push() {
        // Board (white to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ k │   │ P │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │ n │   │ p │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │ p │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ p │   │   │   │   │ P │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ P │   │   │   │   │   │ K │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │ P │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │ R │   │   │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // Pawn on e7 can push and promote.

        let fen = "8/2k1P3/5n1p/6p1/p4P2/P5K1/6P1/4R3 w - -";
        let position = Position::from_fen(fen).unwrap();
        let moves_from_e7 = list_moves_from(&position, Location(52));
        let expected_moves = vec![
            Move::Promotion {
                promotion: Piece::Knight,
                captured: None,
                delta_mask: Bitboard(0x1010000000000000)
            },
            Move::Promotion {
                promotion: Piece::Bishop,
                captured: None,
                delta_mask: Bitboard(0x1010000000000000)
            },
            Move::Promotion {
                promotion: Piece::Rook,
                captured: None,
                delta_mask: Bitboard(0x1010000000000000)
            },
            Move::Promotion {
                promotion: Piece::Queen,
                captured: None,
                delta_mask: Bitboard(0x1010000000000000)
            }
        ];

        assert_set_equals(expected_moves, moves_from_e7);
    }

    #[test]
    fn promotion_capture() {
        // Board (white to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │   │   │   │ n │ k │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │ P │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │ p │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │ p │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ p │   │   │   │   │ P │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ P │   │   │   │   │   │ K │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │ P │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │ R │   │   │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // Pawn on e7 can capture the knight and promote.

        let fen = "3nk3/4P3/7p/6p1/p4P2/P5K1/6P1/4R3 w - -";
        let position = Position::from_fen(fen).unwrap();
        let moves_from_e7 = list_moves_from(&position, Location(52));
        let expected_moves = vec![
            Move::Promotion {
                promotion: Piece::Knight,
                captured: Some(Piece::Knight),
                delta_mask: Bitboard(0x0810000000000000)
            },
            Move::Promotion {
                promotion: Piece::Bishop,
                captured: Some(Piece::Knight),
                delta_mask: Bitboard(0x0810000000000000)
            },
            Move::Promotion {
                promotion: Piece::Rook,
                captured: Some(Piece::Knight),
                delta_mask: Bitboard(0x0810000000000000)
            },
            Move::Promotion {
                promotion: Piece::Queen,
                captured: Some(Piece::Knight),
                delta_mask: Bitboard(0x0810000000000000)
            }
        ];

        assert_set_equals(expected_moves, moves_from_e7);
    }

    #[test]
    fn promotion_push_and_captures() {
        // Board (white to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │   │   │   │ b │   │ q │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │ P │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ k │   │   │   │   │ p │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │ p │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ p │   │   │   │   │ P │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ P │   │   │   │   │   │ K │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │ P │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │ R │   │   │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // Pawn on e7 can capture the bishop, capture queen, or push and
        // promote.

        let fen = "3b1q2/4P3/2k4p/6p1/p4P2/P5K1/6P1/4R3 w - -";
        let position = Position::from_fen(fen).unwrap();
        let moves_from_e7 = list_moves_from(&position, Location(52));
        let expected_moves = vec![
            // 4 promotions to the left, taking the bishop

            Move::Promotion {
                promotion: Piece::Knight,
                captured: Some(Piece::Bishop),
                delta_mask: Bitboard(0x0810000000000000)
            },
            Move::Promotion {
                promotion: Piece::Bishop,
                captured: Some(Piece::Bishop),
                delta_mask: Bitboard(0x0810000000000000)
            },
            Move::Promotion {
                promotion: Piece::Rook,
                captured: Some(Piece::Bishop),
                delta_mask: Bitboard(0x0810000000000000)
            },
            Move::Promotion {
                promotion: Piece::Queen,
                captured: Some(Piece::Bishop),
                delta_mask: Bitboard(0x0810000000000000)
            },

            // 4 promotions to the right, capturing the queen

            Move::Promotion {
                promotion: Piece::Knight,
                captured: Some(Piece::Queen),
                delta_mask: Bitboard(0x2010000000000000)
            },
            Move::Promotion {
                promotion: Piece::Bishop,
                captured: Some(Piece::Queen),
                delta_mask: Bitboard(0x2010000000000000)
            },
            Move::Promotion {
                promotion: Piece::Rook,
                captured: Some(Piece::Queen),
                delta_mask: Bitboard(0x2010000000000000)
            },
            Move::Promotion {
                promotion: Piece::Queen,
                captured: Some(Piece::Queen),
                delta_mask: Bitboard(0x2010000000000000)
            },

            // 4 promotions in the center, capturing nothing

            Move::Promotion {
                promotion: Piece::Knight,
                captured: None,
                delta_mask: Bitboard(0x1010000000000000)
            },
            Move::Promotion {
                promotion: Piece::Bishop,
                captured: None,
                delta_mask: Bitboard(0x1010000000000000)
            },
            Move::Promotion {
                promotion: Piece::Rook,
                captured: None,
                delta_mask: Bitboard(0x1010000000000000)
            },
            Move::Promotion {
                promotion: Piece::Queen,
                captured: None,
                delta_mask: Bitboard(0x1010000000000000)
            }
        ];

        assert_set_equals(expected_moves, moves_from_e7);
    }

    #[test]
    fn pawn_blocked_on_second_rank_can_only_move_one_rank() {
        // Board (white to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │ r │ n │ b │ q │ k │ b │ n │ r │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ p │ p │ p │ p │   │ p │ p │ p │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ P │   │ p │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │ N │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ P │ P │   │ P │ P │ P │ P │ P │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ R │ N │ B │ Q │ K │ B │   │ R │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // Pawn on e1 can push only one square, second square is blocked.

        let fen = "rnbqkbnr/pppp1ppp/8/8/2P1p3/5N2/PP1PPPPP/RNBQKB1R w KQkq -";
        let position = Position::from_fen(fen).unwrap();
        let moves_from_e1 = list_moves_from(&position, Location(12));
        let expected_moves = vec![
            Move::Ordinary {
                moved: Piece::Pawn,
                captured: None,
                delta_mask: Bitboard(0x0000000000101000)
            }
        ];

        assert_set_equals(expected_moves, moves_from_e1);
    }

    #[test]
    fn blocking_evades_check() {
        // Board (black to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │ r │   │   │ k │   │   │   │ R │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │ n │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ p │ p │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │ b │   │ N │   │ B │   │ K │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │ P │   │   │   │   │   │ P │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ P │   │   │   │   │   │ r │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // Rook on h8 attacks the black king. No escape squares are available
        // and the rook cannot be taken. So, the only evading moves are
        // blocking with the rook on g3 or the bishop on b5.

        let fen = "r2k3R/1n6/pp6/1b1N1B1K/1P5P/P5r1/8/8 b - -";
        let position = Position::from_fen(fen).unwrap();
        let moves = list_moves(&position);
        let expected_moves = vec![
            Move::Ordinary {
                moved: Piece::Bishop,
                captured: None,
                delta_mask: Bitboard(0x1000000200000000)
            },
            Move::Ordinary {
                moved: Piece::Rook,
                captured: None,
                delta_mask: Bitboard(0x4000000000400000)
            }
        ];

        assert_set_equals(expected_moves, moves);
    }

    #[test]
    fn capturing_attacker_evades_check() {
        // Board (black to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │ r │   │   │ k │   │   │   │ R │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │ n │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ p │ p │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │ N │   │ B │   │ r │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │ P │   │ b │   │   │   │ P │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ P │   │   │   │   │   │ K │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // Rook on h8 attacks the black king. No escape squares or blocking
        // moves are available. So, the only evading moves are capturing the
        // rook with the bishop on d4 or the rook on h5.

        let fen = "r2k3R/1n6/pp6/3N1B1r/1P1b3P/P5K1/8/8 b - -";
        let position = Position::from_fen(fen).unwrap();
        let moves = list_moves(&position);
        let expected_moves = vec![
            Move::Ordinary {
                moved: Piece::Bishop,
                captured: Some(Piece::Rook),
                delta_mask: Bitboard(0x8000000008000000)
            },
            Move::Ordinary {
                moved: Piece::Rook,
                captured: Some(Piece::Rook),
                delta_mask: Bitboard(0x8000008000000000)
            }
        ];

        assert_set_equals(expected_moves, moves);
    }

    #[test]
    fn king_cannot_capture_covered_attacker() {
        // Board (black to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │ r │   │   │   │   │ R │ k │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │ b │   │ p │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │ p │   │   │   │ p │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ p │   │   │   │ p │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ P │   │   │   │ P │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ N │   │   │   │   │ P │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │ P │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │ R │ K │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // Rook on f8 attacks the black king. It is covered by the rook on f1,
        // so capturing it with the king is not allowed. The only valid king
        // move for black is to h7.

        let fen = "r4Rk1/4b1p1/3p3p/p3p3/P3P3/2N4P/6P1/5RK1 b - -";
        let position = Position::from_fen(fen).unwrap();
        let king_moves = list_moves_from(&position, Location(62));
        let expected_moves = vec![
            Move::Ordinary {
                moved: Piece::King,
                captured: None,
                delta_mask: Bitboard(0x4080000000000000)
            }
        ];

        assert_set_equals(expected_moves, king_moves);
    }

    #[test]
    fn king_can_capture_uncovered_attacker() {
        // Board (black to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │ r │   │   │   │   │ R │ k │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │ b │   │ p │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │ p │   │   │   │ p │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ p │   │   │   │ p │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ P │   │   │   │ P │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ N │   │   │   │   │ P │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │ P │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │ K │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // Same situation as in king_cannot_capture_covered_attacker, but the
        // rook giving check is not covered, so the king can take it.

        let fen = "r4Rk1/4b1p1/3p3p/p3p3/P3P3/2N4P/6P1/6K1 b - -";
        let position = Position::from_fen(fen).unwrap();
        let king_moves = list_moves_from(&position, Location(62));
        let expected_moves = vec![
            Move::Ordinary {
                moved: Piece::King,
                captured: None,
                delta_mask: Bitboard(0x4080000000000000)
            },
            Move::Ordinary {
                moved: Piece::King,
                captured: Some(Piece::Rook),
                delta_mask: Bitboard(0x6000000000000000)
            },
        ];

        assert_set_equals(expected_moves, king_moves);
    }

    #[test]
    fn moving_king_evades_check() {
        // Board (white to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │ k │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │ b │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ q │   │ K │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │ N │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │ Q │   │   │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // Queen on c4 gives check to white's king, who has to run to e3, e5,
        // or f5.

        let fen = "8/3k4/8/7b/2q1K3/3N4/8/4Q3 w - -";
        let position = Position::from_fen(fen).unwrap();
        let moves = list_moves(&position);
        let expected_moves = vec![
            Move::Ordinary {
                moved: Piece::King,
                captured: None,
                delta_mask: Bitboard(0x0000000010100000)
            },
            Move::Ordinary {
                moved: Piece::King,
                captured: None,
                delta_mask: Bitboard(0x0000001010000000)
            },
            Move::Ordinary {
                moved: Piece::King,
                captured: None,
                delta_mask: Bitboard(0x0000002010000000)
            }
        ];

        assert_set_equals(expected_moves, moves);
    }

    #[test]
    fn capturing_attacker_en_passant_evades_check() {
        // Board (black to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │   │   │ r │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ r │   │   │ b │ n │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ p │   │   │   │   │ k │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ P │   │   │ p │ P │   │   │ B │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │ B │   │   │   │ P │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │ P │ P │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │ R │   │ R │ K │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // Where en-passant is available to black, taking the pawn on e4. In
        // fact, this move is one of the available moves to evade the check by
        // white's pawn on e4.

        let fen = "2r5/2r2bn1/8/p4k2/P2pP2B/1B3P2/6PP/3R1RK1 b - e3";
        let position = Position::from_fen(fen).unwrap();
        let moves = list_moves(&position);
        let expected_moves = vec![
            Move::Ordinary {
                moved: Piece::King,
                captured: None,
                delta_mask: Bitboard(0x0000002020000000)
            },
            Move::Ordinary {
                moved: Piece::King,
                captured: None,
                delta_mask: Bitboard(0x0000003000000000)
            },
            Move::Ordinary {
                moved: Piece::King,
                captured: None,
                delta_mask: Bitboard(0x0000402000000000)
            },
            Move::EnPassant { 
                delta_mask: Bitboard(0x0000000008100000),
                target: Bitboard(0x0000000010000000)
            }
        ];

        assert_set_equals(expected_moves, moves);
    }

    #[test]
    fn blocking_with_en_passant_evades_check() {
        // Board (white to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │   │   │ b │   │   │   │   │ r │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │ p │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │ P │ p │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │ K │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │ B │   │   │   │   │ k │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │ R │   │   │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // Where en-passant is available to white, taking the pawn on e5. White
        // can only escape check by taking en-passant, which causes their own
        // pawn to be on e6, where it blocks the check by black's bishop on c8.
        //
        // Note that this position cannot be reached in ordinary play, as the
        // previous move must be a double pawn move. Hence, the slider must
        // give discovered check, which must be blockable by taking en-passant.
        // However, the destination square of en-passant must have already been
        // vacant before the double move, so the king would already have been
        // attacked previously, which cannot happen. Therefore, if a change
        // causes only this test case to fail, but has significant benefits
        // otherwise, such as performance improvements, it may be okay to
        // ignore this test.

        let fen = "2b4r/8/5p2/3Pp3/6K1/8/1B4k1/4R3 w - e6";
        let position = Position::from_fen(fen).unwrap();
        let moves = list_moves(&position);
        let expected_moves = vec![
            Move::EnPassant { 
                delta_mask: Bitboard(0x0000100800000000),
                target: Bitboard(0x0000001000000000)
            }
        ];

        assert_set_equals(expected_moves, moves);
    }

    #[test]
    fn orthogonally_pinned_bishop_cannot_move() {
        // Board (white to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │ k │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │ K │   │ B │   │ r │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // The white bishop on f4 is pinned to the king, so it has no legal
        // moves.

        let fen = "k7/8/8/8/3K1B1r/8/8/8 w - -";
        let position = Position::from_fen(fen).unwrap();
        let moves_from_f4 = list_moves_from(&position, Location(29));

        assert!(moves_from_f4.is_empty());
    }

    #[test]
    fn diagonally_pinned_bishop_can_only_move_along_pin_diagonal() {
        // Board (black to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │   │ Q │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │ b │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ P │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │ P │   │   │   │ k │ r │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │ p │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ K │   │   │   │   │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // The black bishop on d6 is pinned by the queen on b8 and thus can
        // only move on the anti-diagonal.

        let fen = "1Q6/8/3b4/P7/1P3kr1/6p1/8/2K5 b - -";
        let position = Position::from_fen(fen).unwrap();
        let moves_from_f4 = list_moves_from(&position, Location(43));
        let expected_moves = vec![
            Move::Ordinary {
                moved: Piece::Bishop,
                captured: Some(Piece::Queen),
                delta_mask: Bitboard(0x0200080000000000)
            },
            Move::Ordinary {
                moved: Piece::Bishop,
                captured: None,
                delta_mask: Bitboard(0x0004080000000000)
            },
            Move::Ordinary {
                moved: Piece::Bishop,
                captured: None,
                delta_mask: Bitboard(0x0000081000000000)
            }
        ];

        assert_set_equals(expected_moves, moves_from_f4);
    }

    #[test]
    fn vertically_pinned_rook_can_only_move_vertically() {
        // Board (white to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │ r │   │   │   │ k │ r │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ p │   │   │   │   │   │ p │ p │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │ p │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │ p │ B │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │ N │   │   │   │ P │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │ B │   │ b │   │ R │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ P │   │   │   │   │ K │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // The black rook on f8 pins the white rook on f3 to the king. Hence,
        // the white rook can only move vertically.

        let fen = "r3kr2/p5pp/1p6/3pB3/3N3P/1B1b1R2/P4K2/8 w q -";
        let position = Position::from_fen(fen).unwrap();
        let moves_from_f3 = list_moves_from(&position, Location(21));
        let expected_moves = vec![
            Move::Ordinary {
                moved: Piece::Rook,
                captured: Some(Piece::Rook),
                delta_mask: Bitboard(0x2000000000200000)
            },
            Move::Ordinary {
                moved: Piece::Rook,
                captured: None,
                delta_mask: Bitboard(0x0020000000200000)
            },
            Move::Ordinary {
                moved: Piece::Rook,
                captured: None,
                delta_mask: Bitboard(0x0000200000200000)
            },
            Move::Ordinary {
                moved: Piece::Rook,
                captured: None,
                delta_mask: Bitboard(0x0000002000200000)
            },
            Move::Ordinary {
                moved: Piece::Rook,
                captured: None,
                delta_mask: Bitboard(0x0000000020200000)
            }
        ];

        assert_set_equals(expected_moves, moves_from_f3);
    }

    #[test]
    fn horizontally_pinned_rook_can_only_move_horizontally() {
        // Board (white to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │ r │   │   │   │ k │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ p │   │   │   │   │   │ p │ p │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │ p │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │ p │ B │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │ N │   │   │   │ P │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │ B │   │ b │ K │ R │   │ r │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ P │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // The black rook on h3 pins the white rook on f3 to the king. Hence,
        // the white rook can only move horizontally.

        let fen = "r3k3/p5pp/1p6/3pB3/3N3P/1B1bKR1r/P7/8 w q -";
        let position = Position::from_fen(fen).unwrap();
        let moves_from_f3 = list_moves_from(&position, Location(21));
        let expected_moves = vec![
            Move::Ordinary {
                moved: Piece::Rook,
                captured: Some(Piece::Rook),
                delta_mask: Bitboard(0x0000000000a00000)
            },
            Move::Ordinary {
                moved: Piece::Rook,
                captured: None,
                delta_mask: Bitboard(0x0000000000600000)
            }
        ];

        assert_set_equals(expected_moves, moves_from_f3);
    }

    #[test]
    fn diagonally_pinned_rook_cannot_move() {
        // Board (black to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ k │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │ r │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │ p │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │ B │   │   │   │   │ B │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │ K │   │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // The white bishop on g3 pins the black rook on e5 to the king. Hence,
        // the rook cannot move.

        let fen = "8/2k5/8/4r3/6p1/1B4B1/8/5K2 b - -";
        let position = Position::from_fen(fen).unwrap();
        let moves_from_e5 = list_moves_from(&position, Location(36));

        assert!(moves_from_e5.is_empty());
    }

    #[test]
    fn vertically_pinned_pawn_can_only_push() {
        // Board (white to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ k │   │ r │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │ b │   │ p │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │ Q │   │   │ P │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │ K │   │   │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // The pawn on e2 is pinned to the king by the rook on e7. It can
        // therefore not capture the bishop on d3 or pawn on f3.

        let fen = "8/2k1r3/8/8/8/3b1p2/1Q2P3/4K3 w - -";
        let position = Position::from_fen(fen).unwrap();
        let moves_from_e2 = list_moves_from(&position, Location(12));
        let expected_moves = vec![
            Move::Ordinary {
                moved: Piece::Pawn,
                captured: None,
                delta_mask: Bitboard(0x0000000000101000)
            },
            Move::Ordinary {
                moved: Piece::Pawn,
                captured: None,
                delta_mask: Bitboard(0x0000000010001000)
            }
        ];

        assert_set_equals(expected_moves, moves_from_e2);
    }

    #[test]
    fn horizontally_pinned_pawn_cannot_move() {
        // Board (white to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ k │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │ b │   │ p │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │ Q │   │ K │ P │   │   │ r │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // The pawn on e2 is pinned to the king by the rook on h7. It can
        // therefore not move.

        let fen = "8/2k5/8/8/8/3b1p2/1Q1KP2r/8 w - -";
        let position = Position::from_fen(fen).unwrap();
        let moves_from_e2 = list_moves_from(&position, Location(12));

        assert!(moves_from_e2.is_empty());
    }

    #[test]
    fn diagonally_pinned_pawn_can_take_pinner() {
        // Board (black to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │ q │   │   │   │ k │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │ P │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │ p │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ B │   │ R │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ K │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // The pawn on d5 is pinned to the king by the bishop on c4. It can
        // therefore only move along the pin diagonal, which means take the
        // bishop.

        let fen = "8/1q3k2/5P2/3p4/2B1R3/8/2K5/8 b - -";
        let position = Position::from_fen(fen).unwrap();
        let moves_from_d5 = list_moves_from(&position, Location(35));
        let expected_moves = vec![
            Move::Ordinary {
                moved: Piece::Pawn,
                captured: Some(Piece::Bishop),
                delta_mask: Bitboard(0x0000000804000000)
            }
        ];

        assert_set_equals(expected_moves, moves_from_d5);
    }

    #[test]
    fn diagonally_pinned_pawn_can_take_en_passant_along_pin_diagonal() {
        // Board (black to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │ k │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │ P │ p │   │ b │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ B │   │   │ K │   │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // Where the pawn on e4 just progressed by two squares. The black pawn
        // on f4 is pinned to the king by the bishop on c1. Hence, it cannot
        // capture the knight, but it can capture the pawn on e4 en passant.

        let fen = "8/8/7k/8/4Pp1b/6N1/8/2B2K2 b - e3";
        let position = Position::from_fen(fen).unwrap();
        let moves_from_f4 = list_moves_from(&position, Location(29));
        let expected_moves = vec![
            Move::EnPassant {
                delta_mask: Bitboard(0x0000000020100000),
                target: Bitboard(0x0000000010000000)
            }
        ];

        assert_set_equals(expected_moves, moves_from_f4);
    }

    #[test]
    fn vertically_pinned_pawn_cannot_take_en_passant() {
        // Board (white to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │   │   │   │   │ r │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │ k │   │ p │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │ p │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │ P │ p │ n │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │ P │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ P │   │ P │   │   │ B │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │ R │ K │   │   │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // Where the pawn on f5 just moved two squares. As the white pawn on e5
        // is pinned to the king by the rook on e8, it cannot take the black
        // pawn en passant.

        let fen = "4r3/5k1p/6p1/4Ppn1/8/1P6/P1P2B2/3RK3 w - f6";
        let position = Position::from_fen(fen).unwrap();
        let moves_from_e5 = list_moves_from(&position, Location(36));
        let expected_moves = vec![
            Move::Ordinary {
                moved: Piece::Pawn,
                captured: None,
                delta_mask: Bitboard(0x0000101000000000)
            }
        ];

        assert_set_equals(expected_moves, moves_from_e5);
    }

    #[test]
    fn horizontally_pinned_pawn_cannot_take_en_passant() {
        // Board (white to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │   │   │ k │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ K │   │   │ p │ P │   │   │ r │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │ b │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // Where the pawn on d5 just moved two squares. Taking en passant is
        // not allowed here, as that would remove both pawns from the 5th rank
        // and put the white king in check from the rook on h5.

        let fen = "2k5/8/8/K2pP2r/8/8/6B1/8 w - d6 0 1";
        let position = Position::from_fen(fen).unwrap();
        let moves_from_e5 = list_moves_from(&position, Location(36));
        let expected_moves = vec![
            Move::Ordinary {
                moved: Piece::Pawn,
                captured: None,
                delta_mask: Bitboard(0x0000101000000000)
            }
        ];

        assert_set_equals(expected_moves, moves_from_e5);
    }

    #[test]
    fn horizontally_indirectly_pinned_pawn_cannot_take_en_passant() {
        // Board (white to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │   │   │ k │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ r │   │   │ p │ P │   │   │ K │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │ b │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // Same situation as previous test, but now the rook is behind the
        // black pawn.

        let fen = "2k5/8/8/r2pP2K/8/8/6B1/8 w - d6 0 1";
        let position = Position::from_fen(fen).unwrap();
        let moves_from_e5 = list_moves_from(&position, Location(36));
        let expected_moves = vec![
            Move::Ordinary {
                moved: Piece::Pawn,
                captured: None,
                delta_mask: Bitboard(0x0000101000000000)
            }
        ];

        assert_set_equals(expected_moves, moves_from_e5);
    }

    #[test]
    fn pinned_knight_cannot_move() {
        // Board (black to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │   │   │   │   │ r │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │ p │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ p │   │   │ k │   │   │ p │ p │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │ p │   │   │ n │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │ P │   │   │ P │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ P │   │ P │   │   │ P │ B │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │ K │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │ R │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // The black knight on e5 is pinned to the black king by the bishop on
        // g3 and therefore cannot move.

        let fen = "4r3/5p2/p2k2pp/1p2n3/1P2P3/P1P2PB1/4K3/6R1 b - - 0 1";
        let position = Position::from_fen(fen).unwrap();
        let moves_from_e5 = list_moves_from(&position, Location(36));

        assert!(moves_from_e5.is_empty());
    }

    #[test]
    fn checked_king_cannot_move_away_from_bishop() {
        // Board (white to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │ k │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │ b │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │ K │ P │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // The bishop on b6 is checking the white king. The king cannot move to
        // e3.

        let fen = "8/4k3/1b6/8/3KP3/8/8/8 w - - 0 1";
        let position = Position::from_fen(fen).unwrap();
        let moves_from_d4 = list_moves_from(&position, Location(27));
        let expected_moves = vec![
            Move::Ordinary {
                moved: Piece::King,
                captured: None,
                delta_mask: Bitboard(0x0000000008040000)
            },
            Move::Ordinary {
                moved: Piece::King,
                captured: None,
                delta_mask: Bitboard(0x000000000c000000)
            },
            Move::Ordinary {
                moved: Piece::King,
                captured: None,
                delta_mask: Bitboard(0x0000000008080000)
            },
            Move::Ordinary {
                moved: Piece::King,
                captured: None,
                delta_mask: Bitboard(0x0000000808000000)
            },
            Move::Ordinary {
                moved: Piece::King,
                captured: None,
                delta_mask: Bitboard(0x0000001008000000)
            }
        ];

        assert_set_equals(expected_moves, moves_from_d4);
    }

    #[test]
    fn checked_king_cannot_move_away_from_rook() {
        // Board (black to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │ k │   │   │   │ R │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ p │ p │ p │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │ K │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // The rook on h5 is checking the black king. The king cannot move to
        // c5.

        let fen = "8/8/8/3k3R/2ppp3/8/8/6K1 b - - 0 1";
        let position = Position::from_fen(fen).unwrap();
        let moves_from_d5 = list_moves_from(&position, Location(35));
        let expected_moves = vec![
            Move::Ordinary {
                moved: Piece::King,
                captured: None,
                delta_mask: Bitboard(0x0000040800000000)
            },
            Move::Ordinary {
                moved: Piece::King,
                captured: None,
                delta_mask: Bitboard(0x0000080800000000)
            },
            Move::Ordinary {
                moved: Piece::King,
                captured: None,
                delta_mask: Bitboard(0x0000100800000000)
            }
        ];

        assert_set_equals(expected_moves, moves_from_d5);
    }

    #[test]
    fn double_check_only_allows_king_moves() {
        // Board (white to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │   │   │   │ r │   │   │ k │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │ p │ p │ p │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │ Q │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │ P │ n │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ P │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │ K │   │   │   │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // The rook on d8 and the knight on c3 are giving check to the white
        // king, constituting double check. Hence, only king moves are
        // permitted.

        let fen = "3r2k1/5ppp/8/8/1Q6/1Pn5/P7/3K4 w - - 0 1";
        let position = Position::from_fen(fen).unwrap();
        let moves = list_moves(&position);
        let moves_from_d1 = list_moves_from(&position, Location(3));

        assert_set_equals(moves, moves_from_d1);
    }

    #[test]
    fn white_castle_short() {
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
        // White can castle short, but not long.

        let fen = "r1bqk2r/pppp1ppp/2n2n2/2b1p3/2B1P3/2N2N2/PPPP1PPP/R1BQK2R \
            w KQkq - 0 1";
        let position = Position::from_fen(fen).unwrap();
        let moves_from_e1 = list_moves_from(&position, Location(4));
        let expected_moves = vec![
            Move::Ordinary {
                moved: Piece::King,
                captured: None,
                delta_mask: Bitboard(0x0000000000000030)
            },
            Move::Ordinary {
                moved: Piece::King,
                captured: None,
                delta_mask: Bitboard(0x0000000000001010)
            },
            Move::Castle {
                king_delta_mask: Bitboard(0x0000000000000050),
                rook_delta_mask: Bitboard(0x00000000000000a0)
            }
        ];

        assert_set_equals(expected_moves, moves_from_e1);
    }

    #[test]
    fn white_castle_long() {
        // Board (white to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │ r │   │   │   │ k │   │ n │ r │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ p │ p │ p │ q │   │ p │ p │ p │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ n │ p │ b │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ b │   │ p │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ B │   │ P │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ N │ P │ B │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ P │ P │ P │ Q │   │ P │ P │ P │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ R │   │   │   │ K │   │ N │ R │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // White can castle long, but not short.

        let fen = "r3k1nr/pppq1ppp/2npb3/2b1p3/2B1P3/2NPB3/PPPQ1PPP/R3K1NR w \
            KQkq - 0 1";
        let position = Position::from_fen(fen).unwrap();
        let moves_from_e1 = list_moves_from(&position, Location(4));
        let expected_moves = vec![
            Move::Ordinary {
                moved: Piece::King,
                captured: None,
                delta_mask: Bitboard(0x0000000000000018)
            },
            Move::Ordinary {
                moved: Piece::King,
                captured: None,
                delta_mask: Bitboard(0x0000000000000030)
            },
            Move::Ordinary {
                moved: Piece::King,
                captured: None,
                delta_mask: Bitboard(0x0000000000001010)
            },
            Move::Castle {
                king_delta_mask: Bitboard(0x0000000000000014),
                rook_delta_mask: Bitboard(0x0000000000000009)
            }
        ];

        assert_set_equals(expected_moves, moves_from_e1);
    }

    #[test]
    fn white_castle_both() {
        // Board (white to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │ r │   │   │   │ k │   │   │ r │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ p │ p │ p │ q │   │ p │ p │ p │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ n │ p │ b │ n │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ b │   │ p │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ B │   │ P │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ N │ P │ B │ N │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ P │ P │ P │ Q │   │ P │ P │ P │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ R │   │   │   │ K │   │   │ R │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // White can castle both ways

        let fen = "r3k2r/pppq1ppp/2npbn2/2b1p3/2B1P3/2NPBN2/PPPQ1PPP/R3K2R w \
            KQkq - 0 1";
        let position = Position::from_fen(fen).unwrap();
        let moves_from_e1 = list_moves_from(&position, Location(4));
        let expected_moves = vec![
            Move::Ordinary {
                moved: Piece::King,
                captured: None,
                delta_mask: Bitboard(0x0000000000000018)
            },
            Move::Ordinary {
                moved: Piece::King,
                captured: None,
                delta_mask: Bitboard(0x0000000000000030)
            },
            Move::Ordinary {
                moved: Piece::King,
                captured: None,
                delta_mask: Bitboard(0x0000000000001010)
            },
            Move::Castle {
                king_delta_mask: Bitboard(0x0000000000000050),
                rook_delta_mask: Bitboard(0x00000000000000a0)
            },
            Move::Castle {
                king_delta_mask: Bitboard(0x0000000000000014),
                rook_delta_mask: Bitboard(0x0000000000000009)
            }
        ];

        assert_set_equals(expected_moves, moves_from_e1);
    }

    #[test]
    fn black_castle_short() {
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
        // │   │   │ N │ P │   │ N │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ P │ P │ P │   │   │ P │ P │ P │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ R │   │ B │ Q │ K │   │   │ R │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // Black can castle short, but not long.

        let fen = "r1bqk2r/pppp1ppp/2n2n2/2b1p3/2B1P3/2NP1N2/PPP2PPP/R1BQK2R \
            b KQkq - 0 1";
        let position = Position::from_fen(fen).unwrap();
        let moves_from_e8 = list_moves_from(&position, Location(60));
        let expected_moves = vec![
            Move::Ordinary {
                moved: Piece::King,
                captured: None,
                delta_mask: Bitboard(0x3000000000000000)
            },
            Move::Ordinary {
                moved: Piece::King,
                captured: None,
                delta_mask: Bitboard(0x1010000000000000)
            },
            Move::Castle {
                king_delta_mask: Bitboard(0x5000000000000000),
                rook_delta_mask: Bitboard(0xa000000000000000)
            }
        ];

        assert_set_equals(expected_moves, moves_from_e8);
    }

    #[test]
    fn black_castle_long() {
        // Board (black to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │ r │   │   │   │ k │   │ n │ r │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ p │ p │ p │ q │   │ p │ p │ p │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ n │ p │ b │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ b │   │ p │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ B │   │ P │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ N │ P │ B │ N │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ P │ P │ P │ Q │   │ P │ P │ P │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ R │   │   │   │ K │   │   │ R │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // Black can castle long, but not short.

        let fen = "r3k1nr/pppq1ppp/2npb3/2b1p3/2B1P3/2NPBN2/PPPQ1PPP/R3K2R b \
            KQkq - 0 1";
        let position = Position::from_fen(fen).unwrap();
        let moves_from_e8 = list_moves_from(&position, Location(60));
        let expected_moves = vec![
            Move::Ordinary {
                moved: Piece::King,
                captured: None,
                delta_mask: Bitboard(0x1800000000000000)
            },
            Move::Ordinary {
                moved: Piece::King,
                captured: None,
                delta_mask: Bitboard(0x3000000000000000)
            },
            Move::Ordinary {
                moved: Piece::King,
                captured: None,
                delta_mask: Bitboard(0x1010000000000000)
            },
            Move::Castle {
                king_delta_mask: Bitboard(0x1400000000000000),
                rook_delta_mask: Bitboard(0x0900000000000000)
            }
        ];

        assert_set_equals(expected_moves, moves_from_e8);
    }

    #[test]
    fn black_castle_both() {
        // Board (black to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │ r │   │   │   │ k │   │   │ r │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ p │ p │ p │ q │   │ p │ p │ p │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ n │ p │ b │ n │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ b │   │ p │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ B │   │ P │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ N │ P │ B │ N │   │ P │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ P │ P │ P │ Q │   │ P │ P │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ R │   │   │   │ K │   │   │ R │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // Black can castle both ways

        let fen = "r3k2r/pppq1ppp/2npbn2/2b1p3/2B1P3/2NPBN1P/PPPQ1PP1/R3K2R b \
            KQkq - 0 1";
        let position = Position::from_fen(fen).unwrap();
        let moves_from_e8 = list_moves_from(&position, Location(60));
        let expected_moves = vec![
            Move::Ordinary {
                moved: Piece::King,
                captured: None,
                delta_mask: Bitboard(0x1800000000000000)
            },
            Move::Ordinary {
                moved: Piece::King,
                captured: None,
                delta_mask: Bitboard(0x3000000000000000)
            },
            Move::Ordinary {
                moved: Piece::King,
                captured: None,
                delta_mask: Bitboard(0x1010000000000000)
            },
            Move::Castle {
                king_delta_mask: Bitboard(0x5000000000000000),
                rook_delta_mask: Bitboard(0xa000000000000000)
            },
            Move::Castle {
                king_delta_mask: Bitboard(0x1400000000000000),
                rook_delta_mask: Bitboard(0x0900000000000000)
            }
        ];

        assert_set_equals(expected_moves, moves_from_e8);
    }

    #[test]
    fn castling_in_check_not_allowed() {
        // Board (white to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │   │   │ k │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ b │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │ K │   │   │ R │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // Although white is allowed to castle short, the bishop on c3 is
        // giving check, so castling is illegal.

        let fen = "2k5/8/8/8/8/2b5/8/4K2R w K - 0 1";
        let position = Position::from_fen(fen).unwrap();
        let moves_from_e1 = list_moves_from(&position, Location(4));
        let expected_moves = vec![
            Move::Ordinary {
                moved: Piece::King,
                captured: None,
                delta_mask: Bitboard(0x0000000000000018)
            },
            Move::Ordinary {
                moved: Piece::King,
                captured: None,
                delta_mask: Bitboard(0x0000000000001010)
            },
            Move::Ordinary {
                moved: Piece::King,
                captured: None,
                delta_mask: Bitboard(0x0000000000002010)
            },
            Move::Ordinary {
                moved: Piece::King,
                captured: None,
                delta_mask: Bitboard(0x0000000000000030)
            }
        ];

        assert_set_equals(expected_moves, moves_from_e1);
    }

    #[test]
    fn castling_into_check_not_allowed() {
        // Board (black to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │ r │   │   │   │ k │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │ p │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │ N │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │ K │   │ R │   │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // Although black is allowed to castle long, the knight on b6 is
        // blocking the square on which the king would land, so castling is
        // illegal.

        let fen = "r3k3/4p3/1N6/8/8/8/8/3K1R2 b q - 0 1";
        let position = Position::from_fen(fen).unwrap();
        let moves_from_e8 = list_moves_from(&position, Location(60));
        let expected_moves = vec![
            Move::Ordinary {
                moved: Piece::King,
                captured: None,
                delta_mask: Bitboard(0x1800000000000000)
            }
        ];

        assert_set_equals(expected_moves, moves_from_e8);
    }

    #[test]
    fn castling_over_check_not_allowed() {
        // Board (white to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │   │ k │   │   │   │ r │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │ b │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │ P │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ R │   │   │   │ K │   │   │   │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // Although white is allowed to castle long, the bishop on g4 is
        // attacking d1, which the king would need to castle over, so castling
        // is illegal.

        let fen = "1k3r2/8/8/8/6b1/8/3P4/R3K3 w Q - 0 1";
        let position = Position::from_fen(fen).unwrap();
        let moves_from_e1 = list_moves_from(&position, Location(4));

        assert!(moves_from_e1.is_empty());
    }

    #[test]
    fn castling_not_allowed_if_state_says_so() {
        // Board (black to move):
        // ┌───┬───┬───┬───┬───┬───┬───┬───┐
        // │ r │   │   │   │ k │   │   │ r │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ p │ p │   │   │   │   │ p │ p │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │   │ p │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │   │ p │ P │ p │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ p │ P │   │ P │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │   │   │ P │   │   │   │   │   │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ P │ P │   │   │   │   │ P │ P │
        // ├───┼───┼───┼───┼───┼───┼───┼───┤
        // │ R │   │   │   │ K │   │   │ R │
        // └───┴───┴───┴───┴───┴───┴───┴───┘
        //
        // Although all conditions are met for black to castle both sides, the
        // position does not allow for black to castle short, so only castling
        // long is available.

        let fen = "r3k2r/pp4pp/4p3/3pPp2/2pP1P2/2P5/PP4PP/R3K2R b q - 0 1";
        let position = Position::from_fen(fen).unwrap();
        let moves_from_e8 = list_moves_from(&position, Location(60));
        let expected_moves = vec![
            Move::Ordinary {
                moved: Piece::King,
                captured: None,
                delta_mask: Bitboard(0x1800000000000000)
            },
            Move::Ordinary {
                moved: Piece::King,
                captured: None,
                delta_mask: Bitboard(0x3000000000000000)
            },
            Move::Ordinary {
                moved: Piece::King,
                captured: None,
                delta_mask: Bitboard(0x1008000000000000)
            },
            Move::Ordinary {
                moved: Piece::King,
                captured: None,
                delta_mask: Bitboard(0x1020000000000000)
            },
            Move::Ordinary {
                moved: Piece::King,
                captured: None,
                delta_mask: Bitboard(0x1010000000000000)
            },
            Move::Castle {
                king_delta_mask: Bitboard(0x1400000000000000),
                rook_delta_mask: Bitboard(0x0900000000000000)
            }
        ];

        assert_set_equals(expected_moves, moves_from_e8);
    }
}
