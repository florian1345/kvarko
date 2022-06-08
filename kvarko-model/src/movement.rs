use crate::board::Bitboard;

kvarko_proc_macro::load_magics! { "kvarko-model/magics.json" }

fn get_slider_attack(own_pieces: Bitboard, opponent_pieces: Bitboard,
        square: usize, magics: &[Magic; 64]) -> Bitboard {
    let magic = &magics[square];
    let occupancy = magic.premask & (own_pieces | opponent_pieces);
    let shift = magic.magic >> 58;
    let index = (magic.magic.wrapping_mul(occupancy.0) >> shift) as usize;
    attack_entry(index) & magic.postmask & !own_pieces
}

fn get_bishop_attack(own_pieces: Bitboard, opponent_pieces: Bitboard,
        square: usize) -> Bitboard {
    get_slider_attack(own_pieces, opponent_pieces, square, &BISHOP_MAGICS)
}

fn get_rook_attack(own_pieces: Bitboard, opponent_pieces: Bitboard,
        square: usize) -> Bitboard {
    get_slider_attack(own_pieces, opponent_pieces, square, &ROOK_MAGICS)
}
