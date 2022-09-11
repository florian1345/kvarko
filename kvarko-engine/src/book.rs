use kvarko_model::hash::PositionHasher;
use kvarko_model::movement::Move;
use kvarko_model::state::{PositionId, State};

use serde::{Deserialize, Serialize};

use std::collections::HashMap;
use std::io::{Read, Write};

#[derive(Clone, Deserialize, Serialize)]
struct OpeningBookEntry {
    value: f32,
    best_move: Move,
    at_ply: usize
}

/// An opening book stores the values and best moves for various common opening
/// positions in a game. Internally, this is realized as a hash map associating
/// values and moves with each [PositionId] in the book. It is further checked
/// that the position is reached at the correct point in time to avoid causing
/// draws by repetition.
#[derive(Clone, Deserialize, Serialize)]
pub struct OpeningBook {
    map: HashMap<PositionId, OpeningBookEntry>
}

impl OpeningBook {

    /// Loads an opening book from the data provided by a reader. This may be a
    /// kvarko opening book file (`.kob`) or any other serialized form. This
    /// method uses the same format provided by [OpeningBook::save].
    ///
    /// # Arguments
    ///
    /// * `reader`: The [Read]er providing binary data that constitutes an
    /// opening book.
    ///
    /// # Returns
    ///
    /// A new opening book constructed from the data provided by the given
    /// reader.
    ///
    /// # Errors
    ///
    /// Any [bincode::Error] if reading or parsing fails.
    pub fn load<R>(reader: &mut R) -> bincode::Result<OpeningBook>
    where
        R: Read
    {
        bincode::deserialize_from(reader)
    }

    /// Saves an opening book to the data stream provided by a writer. This may
    /// be a kvarko opening book file (`.kob`) or any other serialized form.
    /// This method provides a format that can be read by [OpeningBook::load].
    ///
    /// # Arguments
    ///
    /// * `writer`: The [Write]r consuming binary data that constitutes this
    /// opening book.
    ///
    /// # Errors
    ///
    /// Any [bincode::Error] if serializing or writing fails.
    pub fn save<W>(&self, writer: &mut W) -> bincode::Result<()>
    where
        W: Write
    {
        bincode::serialize_into(writer, self)
    }

    /// Creates a new, empty opening book.
    ///
    /// # Returns
    ///
    /// A new opening book without any entries.
    pub fn empty() -> OpeningBook {
        OpeningBook {
            map: HashMap::new()
        }
    }

    fn get_entry<H>(&self, state: &State<H>) -> Option<&OpeningBookEntry>
    where
        H: PositionHasher
    {
        if let Some(entry) = self.map.get(&state.position().unique_id()) {
            if entry.at_ply == state.history().len() {
                return Some(entry);
            }
        }

        None
    }

    /// Gets the value of a given `state` from the perspective of the player
    /// whose turn it is, or `None` if the state is not contained in this
    /// opening book.
    pub fn get_value<H>(&self, state: &State<H>) -> Option<f32>
    where
        H: PositionHasher
    {
        self.get_entry(state).map(|e| e.value)
    }

    /// Gets the recommended move in a given `state` for the player whose turn
    /// it is, or `None` if the state is not contained in this opening book.
    pub fn get_best_move<H>(&self, state: &State<H>) -> Option<&Move>
    where
        H: PositionHasher
    {
        self.get_entry(state).map(|e| &e.best_move)
    }

    /// Adds a new entry for a given state to this opening book.
    ///
    /// # Arguments
    ///
    /// * `state`: The [State] for which the created entry provides
    /// information.
    /// * `value`: The evaluation from the player's perspective whose turn it
    /// is.
    /// * `best_move`: The recommended [Move] for the player whose turn it is.
    pub fn add_entry<H>(&mut self, state: &State<H>, value: f32,
        best_move: Move)
    where
        H: PositionHasher
    {
        let id = state.position().unique_id();
        let at_ply = state.history().len();

        self.map.insert(id, OpeningBookEntry {
            value,
            best_move,
            at_ply
        });
    }

    /// Gets the number of entries contained in this opening book.
    pub fn len(&self) -> usize {
        self.map.len()
    }
}
