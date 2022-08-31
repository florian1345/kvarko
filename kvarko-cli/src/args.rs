use clap::{Parser, Subcommand};

#[derive(Debug, Subcommand)]
pub(crate) enum Command {

    /// Runs perft-search on a specific position with a given depth. That is,
    /// returns the number of paths with a certain length that exist in the
    /// game tree.
    Perft {

        /// The FEN describing the initial position/root node of the search
        /// tree.
        #[clap(long, default_value =
            "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1")]
        fen: String,

        /// The depth to which paths are searched.
        #[clap(long)]
        depth: usize
    },

    Eval {
        #[clap(long, default_value = "")]
        history: String,

        #[clap(long)]
        depth: u32
    }
}

#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
pub(crate) struct Args {

    #[clap(subcommand)]
    pub(crate) command: Command
}
