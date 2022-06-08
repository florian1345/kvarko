use proc_macro::TokenStream;

use proc_macro2::Span;
use serde::Deserialize;

use std::fs::File;
use std::io::BufReader;

use syn::{
    Expr,
    ExprArray,
    ExprLit,
    ExprStruct,
    FieldValue,
    Ident,
    Lit,
    LitInt,
    LitStr,
    Path,
    PathSegment,
    PathArguments,
    Member, ExprPath, ExprCall
};
use syn::punctuated::Punctuated;
use syn::token::{Bracket, Brace, Colon, Paren};

const LEFT_BORDER: u64 = 0x0101010101010101;
const RIGHT_BORDER: u64 = 0x8080808080808080;
const BOTTOM_BORDER: u64 = 0x00000000000000ff;
const TOP_BORDER: u64 = 0xff00000000000000;

struct Slide {
    shift: u32,
    border: u64
}

impl Slide {
    const fn new(shift: u32, border: u64) -> Slide {
        Slide { shift, border }
    }
}

const BISHOP_DOWN_LEFT: Slide = Slide::new(55, LEFT_BORDER | BOTTOM_BORDER);
const BISHOP_DOWN_RIGHT: Slide = Slide::new(57, RIGHT_BORDER | BOTTOM_BORDER);
const BISHOP_UP_LEFT: Slide = Slide::new(7, LEFT_BORDER | TOP_BORDER);
const BISHOP_UP_RIGHT: Slide = Slide::new(9, RIGHT_BORDER | TOP_BORDER);
const BISHOP_SLIDES: [Slide; 4] = [
    BISHOP_DOWN_LEFT,
    BISHOP_DOWN_RIGHT,
    BISHOP_UP_LEFT,
    BISHOP_UP_RIGHT
];

const ROOK_DOWN: Slide = Slide::new(56, BOTTOM_BORDER);
const ROOK_LEFT: Slide = Slide::new(63, LEFT_BORDER);
const ROOK_RIGHT: Slide = Slide::new(1, RIGHT_BORDER);
const ROOK_UP: Slide = Slide::new(8, TOP_BORDER);
const ROOK_SLIDES: [Slide; 4] = [
    ROOK_DOWN,
    ROOK_LEFT,
    ROOK_RIGHT,
    ROOK_UP
];

struct Masks {
    premask: u64,
    postmask: u64
}

impl Masks {
    fn empty() -> Masks {
        Masks {
            premask: 0,
            postmask: 0
        }
    }
}

fn trace_mask_ray(start: u64, slide: &Slide, masks: &mut Masks) {
    if start & slide.border != 0 {
        return;
    }

    let mut target = start;

    loop {
        target = target.rotate_left(slide.shift);
        masks.postmask |= target;

        if target & slide.border != 0 {
            return;
        }

        masks.premask |= target;
    }
}

fn gen_masks(square: usize, slides: &[Slide]) -> Masks {
    let mut masks = Masks::empty();
    let start = 1u64 << square;

    for slide in slides {
        trace_mask_ray(start, slide, &mut masks);
    }

    masks
}

#[derive(Clone, Copy)]
enum SliderKind {
    Bishop,
    Rook
}

struct Requirement {
    kind: SliderKind,
    square: usize,
    occupancy: u64,
    postmask: u64,
    attack: u64
}

fn trace_attack_ray(start: u64, occupancy: u64, slide: &Slide,
        attack: &mut u64) {
    if start & slide.border != 0 {
        return;
    }

    let mut target = start;

    while target & slide.border == 0 && target & occupancy == 0 {
        target = target.rotate_left(slide.shift);
        *attack |= target;
    }
}

fn gen_attack(square: usize, occupancy: u64, slides: &[Slide]) -> u64 {
    let mut attack = 0;
    let start = 1u64 << square;

    for slide in slides {
        trace_attack_ray(start, occupancy, slide, &mut attack);
    }

    attack
}

fn gen_occupancies(premask: u64) -> Vec<u64> {
    let ones = premask.count_ones() as usize;
    let mut bits = Vec::with_capacity(ones);

    for i in 0..64u32 {
        let bit = 1u64 << i;

        if premask & bit != 0 {
            bits.push(bit);
        }
    }

    let mut occupancies = Vec::new();

    for bit_set in 0..(1u64 << ones) {
        let mut occupancy = 0;

        for bit_idx in 0..ones {
            if (1 << bit_idx) & bit_set != 0 {
                occupancy |= bits[bit_idx];
            }
        }

        occupancies.push(occupancy);
    }

    occupancies
}

fn gen_requirements_for(kind: SliderKind, square: usize,
        reqs: &mut Vec<Requirement>) {
    let slides = match kind {
        SliderKind::Bishop => &BISHOP_SLIDES,
        SliderKind::Rook => &ROOK_SLIDES
    };
    let masks = gen_masks(square, slides);

    for occupancy in gen_occupancies(masks.premask) {
        let attack = gen_attack(square, occupancy, slides);
        reqs.push(Requirement {
            kind,
            square,
            occupancy,
            postmask: masks.postmask,
            attack
        });
    }
}

fn gen_requirements() -> Vec<Requirement> {
    let mut reqs = Vec::new();

    for square in 0..64 {
        gen_requirements_for(SliderKind::Bishop, square, &mut reqs);
        gen_requirements_for(SliderKind::Rook, square, &mut reqs);
    }

    reqs
}

#[derive(Deserialize)]
struct Magic {
    offset: usize,
    premask: u64,
    postmask: u64,
    magic: u64
}

#[derive(Deserialize)]
struct Magics {
    size: usize,
    bishop: Vec<Magic>,
    rook: Vec<Magic>
}

impl Magics {
    fn compute_idx(&self, req: &Requirement) -> usize {
        let magic = match req.kind {
            SliderKind::Bishop => &self.bishop[req.square],
            SliderKind::Rook => &self.rook[req.square]
        };
        let shift = magic.magic >> 58;

        (req.occupancy.wrapping_mul(magic.magic) >> shift) as usize
            + magic.offset
    }
}

fn gen_table(magics: &Magics, reqs: &[Requirement]) -> Vec<u64> {
    let mut table = vec![0; magics.size];
    
    for req in reqs {
        let idx = magics.compute_idx(req);
        table[idx] |= req.attack;
    }

    table
}

fn verify_table(magics: &Magics, reqs: &[Requirement], table: &[u64]) -> bool {
    for req in reqs {
        let idx = magics.compute_idx(req);
        let attack = table[idx] & req.postmask;

        if attack != req.attack {
            return false;
        }
    }

    true
}

/// Loads the magics from the given file, constructs the table and verifies it.
/// If anything goes wrong, an `Err(_)` variant with a message is returned.
/// Otherwise, `Ok((magics, table))` is returned.
fn load_magics_from(file: String) -> Result<(Magics, Vec<u64>), String> {
    let file = File::open(file).map_err(|e| format!("{}", e))?;
    let reader = BufReader::new(file);
    let magics: Magics = serde_json::from_reader(reader)
        .map_err(|e| format!("{}", e))?;

    if magics.bishop.len() != 64 {
        return Err("expected 64 bishop magics".to_owned());
    }

    if magics.rook.len() != 64 {
        return Err("expected 64 rook magics".to_owned());
    }

    let reqs = gen_requirements();
    let table = gen_table(&magics, &reqs);

    if verify_table(&magics, &reqs, &table) {
        Ok((magics, table))
    }
    else {
        Err("magic numbers produce collision".to_owned())
    }
}

fn empty_array() -> ExprArray {
    ExprArray {
        attrs: Vec::new(),
        bracket_token: Bracket::default(),
        elems: Punctuated::new()
    }
}

fn int_lit(value: u64) -> Expr {
    Expr::Lit(ExprLit {
        attrs: Vec::new(),
        lit: Lit::Int(LitInt::new(&value.to_string(), Span::call_site()))
    })
}

fn bitboard_lit(value: u64) -> Expr {
    let bitboard_struct_path = simple_path("Bitboard");
    let mut args = Punctuated::new();
    args.push(int_lit(value));

    Expr::Call(ExprCall {
        attrs: Vec::new(),
        func: Box::new(Expr::Path(ExprPath {
            attrs: Vec::new(),
            qself: None,
            path: bitboard_struct_path
        })),
        paren_token: Paren::default(),
        args
    })
}

fn simple_path(name: &str) -> Path {
    let mut segments = Punctuated::new();
    segments.push(PathSegment {
        ident: Ident::new(name, Span::call_site()),
        arguments: PathArguments::None
    });

    Path {
        leading_colon: None,
        segments
    }
}

fn field(name: &str, value: u64, bitboard: bool) -> FieldValue {
    FieldValue {
        attrs: Vec::new(),
        member: Member::Named(Ident::new(name, Span::call_site())),
        colon_token: Some(Colon::default()),
        expr: if bitboard { bitboard_lit(value) } else { int_lit(value) }
    }
}

fn to_magics_array(magics: &[Magic]) -> ExprArray {
    let mut array = empty_array();
    let magic_struct_path = simple_path("Magic");

    for magic in magics {
        let mut magic_struct = ExprStruct {
            attrs: Vec::new(),
            path: magic_struct_path.clone(),
            brace_token: Brace::default(),
            fields: Punctuated::new(),
            dot2_token: None,
            rest: None
        };

        magic_struct.fields.push(field("offset", magic.offset as u64, false));
        magic_struct.fields.push(field("premask", magic.premask, true));
        magic_struct.fields.push(field("postmask", magic.postmask, true));
        magic_struct.fields.push(field("magic", magic.magic, false));

        array.elems.push(Expr::Struct(magic_struct));
    }

    array
}

fn to_table_array(table: &[u64]) -> ExprArray {
    let mut array = empty_array();

    for entry in table {
        array.elems.push(int_lit(*entry));
    }

    array
}

/// Receives as input a string literal containing the path to a file which
/// stores JSON defining a set of magic numbers for magic bitboard move
/// generation. The file must have the following schema:
///
/// ```norun
/// {
///   "size": usize,
///   "bishop": [Magic; 64],
///   "rook": [Magic; 64]
/// }
/// ```
///
/// Where `Magic` is defined as follows.
///
/// ```norun
/// {
///   "offset": usize,
///   "premask": u64,
///   "postmask": u64,
///   "magic": u64
/// }
/// ```
///
/// This macro generates code defining the `Magic` struct, which contains the
/// fields `offset`, `premask`, `postmask`, and `magic`. It also generates for
/// bishops and rooks a constant array of the 64 `Magic`s for that piece, one
/// per field, named `BISHOP_MAGICS` and `ROOK_MAGICS`. Finally, it computes
/// the lookup table which maps a hashed occupancy matrix to the attack
/// matrices. Access to the table is offered with the generated function
/// `attack_entry(index: usize) -> Bitboard`.
///
/// Note if one entry of the table is used by multiple squares, the attack
/// boards are combined via the OR-operation. To obtain the original attack
/// bitboard, the entry has to be masked with the postmask provided with the
/// magic. The bit shift is written in the first six bits of the magic number.
/// The table is verified after creation and an error is raised if appropriate.
///
/// All instances of `u64` that refer to a bit board are represented as the
/// type `Bitboard(u64)`. It is the responsibility of the caller to have such a
/// type in scope when this macro is called.
///
/// Invocation of this macro is very expensive and should only be done once per
/// project, if possible.
#[proc_macro]
pub fn load_magics(input: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(input as LitStr);

    match load_magics_from(input.value()) {
        Ok((magics, table)) => {
            let size = table.len();
            let bishop_magics = to_magics_array(&magics.bishop);
            let rook_magics = to_magics_array(&magics.rook);
            let table = to_table_array(&table);

            quote::quote! {
                struct Magic {
                    offset: usize,
                    premask: Bitboard,
                    postmask: Bitboard,
                    magic: u64
                }

                const BISHOP_MAGICS: [Magic; 64] = #bishop_magics;
                const ROOK_MAGICS: [Magic; 64] = #rook_magics;

                fn attack_entry(index: usize) -> Bitboard {
                    const ATTACK_TABLE: [u64; #size] = #table;

                    Bitboard(ATTACK_TABLE[index])
                }
            }.into()
        },
        Err(message) => {
            let span = Span::call_site();
            quote::quote_spanned!(span => compile_error! { #message }).into()
        }
    }
}
