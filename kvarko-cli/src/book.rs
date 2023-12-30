use kvarko_engine::book::OpeningBook;

use kvarko_model::error::{AlgebraicResult, AlgebraicError};
use kvarko_model::hash::IdHasher;
use kvarko_model::movement::Move;
use kvarko_model::player::Player;
use kvarko_model::state::State;

use pgn_reader::{
    Outcome,
    SanPlus,
    Color,
    Visitor,
    Skip,
    BufferedReader,
    RawHeader
};

use std::fs::File;
use std::io::{self, BufReader, BufWriter};
use std::str;
use kvarko_engine::eval::{Centipawns, Evaluation};

const MAX_VALUE_CENTIPAWNS: i32 = 500;

struct DatabaseTree {
    white_victories: u32,
    black_victories: u32,
    draws: u32,

    // A hash map has more efficient lookup, but memory is mostly the limiting
    // factor here.
    children: Vec<(SanPlus, DatabaseTree)>
}

impl DatabaseTree {
    fn new() -> DatabaseTree {
        DatabaseTree {
            white_victories: 0,
            black_victories: 0,
            draws: 0,
            children: Vec::new()
        }
    }

    fn register(&mut self, moves: &[SanPlus], outcome: Outcome) {
        match outcome {
            Outcome::Decisive { winner: Color::White } =>
                self.white_victories += 1,
            Outcome::Decisive { winner: Color::Black } =>
                self.black_victories += 1,
            Outcome::Draw => self.draws += 1
        }

        if !moves.is_empty() {
            let entry =
                self.children.iter_mut().find(|(key, _)| key == &moves[0]);
            let child = 
                if let Some((_, child)) = entry {
                    child
                }
                else {
                    let child = DatabaseTree {
                        white_victories: 0,
                        black_victories: 0,
                        draws: 0,
                        children: Vec::new()
                    };

                    if self.children.capacity() == 0 {
                        // This ensures only a small portion of memory is
                        // allocated for the first entry. While this causes
                        // more reallocations, it massively improves memory
                        // efficiency, as many paths in the tree are unique.

                        self.children.reserve_exact(1);
                    }

                    self.children.push((moves[0].clone(), child));

                    &mut self.children.last_mut().unwrap().1
                };
    
            child.register(&moves[1..], outcome);
        }
    }

    fn occurrences(&self) -> u32 {
        self.white_victories + self.black_victories + self.draws
    }

    fn value(&self, player: Player) -> Evaluation {
        // TODO factor in amount of occurrences?

        let advantage = match player {
            Player::White =>
                self.white_victories as i32 - self.black_victories as i32,
            Player::Black =>
                self.black_victories as i32 - self.white_victories as i32
        };
        let centipawns = advantage * MAX_VALUE_CENTIPAWNS / self.occurrences() as i32;

        Evaluation::from_centipawns(centipawns as Centipawns).unwrap()
    }

    fn enter_in_book(&self, min_occurrences: u32, state: &mut State<IdHasher>,
            book: &mut OpeningBook) -> AlgebraicResult<()> {
        if self.occurrences() < min_occurrences || self.children.is_empty() {
            return Ok(());
        }

        let player = state.position().turn();
        let value = self.value(player);
        let best_move = self.children.iter()
            .max_by_key(|(_, child)| child.value(player))
            .unwrap().0.clone();
        let best_move = &format!("{}", best_move);
        let best_move = Move::parse_algebraic(state.position(), best_move)?;

        book.add_entry(&*state, value, best_move);

        for (san_plus, child) in self.children.iter() {
            let algebraic = &format!("{}", san_plus);
            let mov = Move::parse_algebraic(state.position(), algebraic)?;
            let revert_info = state.make_move(&mov);
            child.enter_in_book(min_occurrences, state, book)?;
            state.unmake_move(&mov, revert_info);
        }

        Ok(())
    }

    fn to_book(&self, min_occurrences: u32) -> AlgebraicResult<OpeningBook> {
        let mut book = OpeningBook::empty();
        let mut state = State::initial();

        self.enter_in_book(min_occurrences, &mut state, &mut book)?;

        Ok(book)
    }
}

struct GameCollector {
    moves: Vec<SanPlus>,
    outcome: Option<Outcome>,
    skip: bool
}

impl GameCollector {
    fn new() -> GameCollector {
        GameCollector {
            moves: Vec::new(),
            outcome: None,
            skip: false
        }
    }
}

impl Visitor for GameCollector {
    type Result = (Vec<SanPlus>, Option<Outcome>);

    fn begin_variation(&mut self) -> Skip {
        Skip(true)
    }

    fn begin_game(&mut self) {
        self.skip = false;
    }

    fn end_game(&mut self) -> (Vec<SanPlus>, Option<Outcome>) {
        let mut moves = Vec::new();

        std::mem::swap(&mut self.moves, &mut moves);

        (moves, self.outcome.take())
    }

    fn san(&mut self, san_plus: SanPlus) {
        self.moves.push(san_plus);
    }

    fn outcome(&mut self, outcome: Option<Outcome>) {
        self.outcome = outcome;
    }

    fn header(&mut self, key: &[u8], value: RawHeader<'_>) {
        if let Ok(key) = str::from_utf8(key) {
            // We should only have to check "SetUp", but some DBs are buggy

            if key == "SetUp" || key == "Setup" || key == "setup" {
                if let Ok(value) = str::from_utf8(value.0) {
                    if value == "1" {
                        self.skip = true;
                    }
                }
            }
            else if key == "FEN" || key == "Fen" || key == "fen" {
                self.skip = true;
            }
        }
    }

    fn end_headers(&mut self) -> Skip {
        Skip(self.skip)
    }
}

#[derive(Debug)]
pub enum MakeBookError {
    Io(io::Error),
    Algebraic(AlgebraicError),
    Bincode(bincode::Error)
}

impl From<io::Error> for MakeBookError {
    fn from(e: io::Error) -> MakeBookError {
        MakeBookError::Io(e)
    }
}

impl From<AlgebraicError> for MakeBookError {
    fn from(e: AlgebraicError) -> MakeBookError {
        MakeBookError::Algebraic(e)
    }
}

impl From<bincode::Error> for MakeBookError {
    fn from(e: bincode::Error) -> MakeBookError {
        MakeBookError::Bincode(e)
    }
}

pub fn make_book(in_path: String, out_path: String, min_occurrences: u32,
        max_depth: usize) -> Result<usize, MakeBookError> {
    let mut collector = GameCollector::new();
    let mut tree = DatabaseTree::new();
    let in_file = BufReader::new(File::open(in_path)?);
    let mut reader = BufferedReader::new(in_file);

    while let Some((moves, outcome)) = reader.read_game(&mut collector)? {
        if let Some(outcome) = outcome {
            let moves = &moves[..max_depth.min(moves.len())];
            tree.register(moves, outcome);
        }
    }

    let book = tree.to_book(min_occurrences)?;
    let mut out_file = BufWriter::new(File::create(out_path)?);

    book.save(&mut out_file)?;

    Ok(book.len())
}
