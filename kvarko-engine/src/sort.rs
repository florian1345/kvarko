use std::convert::TryInto;
use std::iter;

use kvarko_model::board::Bitboard;
use kvarko_model::movement::Move;
use kvarko_model::piece::{PIECE_COUNT, Piece};
use kvarko_model::state::Position;

pub trait Presorter {

    fn pre_sort(&mut self, moves: &mut [Move], position: &Position);
}

trait Array<T> {

    fn as_slice(&self) -> &[T];

    fn as_mut_slice(&mut self) -> &mut [T];
}

impl<T, const N: usize> Array<T> for Box<[T; N]> {
    fn as_slice(&self) -> &[T] {
        self.as_ref()
    }

    fn as_mut_slice(&mut self) -> &mut [T] {
        self.as_mut()
    }
}

trait Countable : Clone + Copy {

    const COUNT: usize;
    const ZERO: Self;

    // TODO this should be replaced with [u8; MAX] as soon as issue 60551 is
    // resolved (https://github.com/rust-lang/rust/issues/60551)

    type IndexArray: Array<u8> + Sized;

    fn as_usize(self) -> usize;

    fn zero_index_array() -> Self::IndexArray;
}

const LEN_UPPER_BOUND: usize = 256;

#[derive(Clone, Debug)]
struct CounterSort<T: Countable> {
    counters: T::IndexArray,
    out: Box<[T; LEN_UPPER_BOUND]>
}

impl<T> CounterSort<T>
where
    T: Countable
{
    fn new() -> CounterSort<T> {
        CounterSort {
            counters: T::zero_index_array(),
            out: Box::new([T::ZERO; LEN_UPPER_BOUND])
        }
    }

    #[inline]
    fn reset_counters(&mut self) {
        self.counters.as_mut_slice().fill(0);
    }

    #[inline]
    fn fill_counters(&mut self, buf: &[T]) {
        for &value in &*buf {
            self.counters.as_mut_slice()[value.as_usize()] += 1;
        }

        let mut sum = 0;

        for i in 0..T::COUNT {
            let value = self.counters.as_slice()[i];
            self.counters.as_mut_slice()[i] = sum;
            sum += value;
        }
    }

    fn sort(&mut self, buf: &[T]) {
        self.reset_counters();
        self.fill_counters(buf);

        for &value in &*buf {
            let ctr_idx = value.as_usize();

            self.out[self.counters.as_slice()[ctr_idx] as usize] = value;
            self.counters.as_mut_slice()[ctr_idx] += 1;
        }
    }

    fn out(&self) -> &[T] {
        self.out.as_ref()
    }
}

const fn const_max(a: u8, b: u8) -> u8 {
    if a > b {
        a
    }
    else {
        b
    }
}

// These are not the ordinary piece values, but rather values which allow for
// easy comparison while keeping the numbers low.

const PAWN_CAPTURE_VALUE: u8 = 0;
const KNIGHT_BISHOP_CAPTURE_VALUE: u8 = 3;
const ROOK_CAPTURE_VALUE: u8 = 4;
const QUEEN_KING_CAPTURE_VALUE: u8 = 6;
const CAPTURE_VALUES: [u8; PIECE_COUNT] = [
    PAWN_CAPTURE_VALUE,
    KNIGHT_BISHOP_CAPTURE_VALUE,
    KNIGHT_BISHOP_CAPTURE_VALUE,
    ROOK_CAPTURE_VALUE,
    QUEEN_KING_CAPTURE_VALUE,
    QUEEN_KING_CAPTURE_VALUE
];
const MAX_PIECE_CAPTURE_VALUE: u8 = const_max(
    const_max(
        PAWN_CAPTURE_VALUE,
        KNIGHT_BISHOP_CAPTURE_VALUE),
    const_max(
        ROOK_CAPTURE_VALUE,
        QUEEN_KING_CAPTURE_VALUE));

const fn piece_capture_value(piece: Piece) -> u8 {
    CAPTURE_VALUES[piece as usize]
}

#[derive(Clone, Copy, Debug)]
struct CaptureValue(u8);

impl CaptureValue {

    #[inline]
    const fn ordinary() -> CaptureValue {
        CaptureValue(0)
    }

    #[inline]
    const fn capture(captured: Piece, moved: Piece) -> CaptureValue {
        CaptureValue(MAX_PIECE_CAPTURE_VALUE + 1 -
            piece_capture_value(moved) + piece_capture_value(captured))
    }

    #[inline]
    const fn promotion(promotion: Piece) -> CaptureValue {
        CaptureValue(piece_capture_value(promotion))
    }

    #[inline]
    const fn promotion_capture(promotion: Piece, captured: Piece) -> CaptureValue {
        CaptureValue(MAX_PIECE_CAPTURE_VALUE + 1 - PAWN_CAPTURE_VALUE +
            piece_capture_value(promotion) + piece_capture_value(captured))
    }

    fn from_move(mov: &Move) -> CaptureValue {
        match *mov {
            Move::Ordinary { moved, captured, .. } =>
                if let Some(captured) = captured {
                    CaptureValue::capture(captured, moved)
                }
                else {
                    CaptureValue::ordinary()
                },
            Move::EnPassant { .. } =>
                CaptureValue::capture(Piece::Pawn, Piece::Pawn),
            Move::Promotion { promotion, captured,.. } =>
                if let Some(captured) = captured {
                    CaptureValue::promotion_capture(promotion, captured)
                }
                else {
                    CaptureValue::promotion(promotion)
                },
            Move::Castle { .. } => CaptureValue::ordinary()
        }
    }
}

impl Countable for (CaptureValue, u8) {

    const COUNT: usize =
        CaptureValue::promotion_capture(Piece::Queen, Piece::Queen).0 as usize + 1;

    const ZERO: (CaptureValue, u8) = (CaptureValue(0), 0);

    type IndexArray = Box<[u8; Self::COUNT]>;

    #[inline]
    fn as_usize(self) -> usize {
        self.0.0 as usize
    }

    #[inline]
    fn zero_index_array() -> Box<[u8; Self::COUNT]> {
        Box::new([0; Self::COUNT])
    }
}

#[derive(Clone, Debug)]
pub struct CaptureValuePresorter {
    counter_sort: CounterSort<(CaptureValue, u8)>,
    in_buf: Box<[(CaptureValue, u8); LEN_UPPER_BOUND]>,
    move_buf: Box<[Move; LEN_UPPER_BOUND]>
}

impl CaptureValuePresorter {
    pub fn new() -> CaptureValuePresorter {
        CaptureValuePresorter {
            counter_sort: CounterSort::new(),
            in_buf: Box::new([(CaptureValue(0), 0); LEN_UPPER_BOUND]),
            move_buf: Box::new(iter::repeat_with(|| Move::Ordinary {
                    moved: Piece::Pawn,
                    captured: None,
                    delta_mask: Bitboard::EMPTY }
                )
                .take(LEN_UPPER_BOUND)
                .collect::<Vec<_>>()
                .try_into()
                .unwrap())
        }
    }
}

impl Presorter for CaptureValuePresorter {
    fn pre_sort(&mut self, moves: &mut [Move], _: &Position) {
        let len = moves.len();

        for i in 0..len {
            self.in_buf[i] = (CaptureValue::from_move(&moves[i]), i as u8);
        }

        self.counter_sort.sort(&self.in_buf[..len]);
        let out = &self.counter_sort.out()[..len];

        for (buf_idx, &(_, mov_idx)) in out.iter().enumerate() {
            // CounterSort sorts ascending, but we need descending
            // => invert index by taking len - mov_idx - 1

            let mov_idx = len - mov_idx as usize - 1;
            self.move_buf[buf_idx] = moves[mov_idx].clone();
        }

        moves.clone_from_slice(&self.move_buf[..len]);
    }
}
