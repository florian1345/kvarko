use std::num::{NonZeroUsize, ParseIntError};
use std::time::Duration;

use clap::Parser;

#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
pub(crate) struct Args {

    /// The number of threads to use for parallel evaluation of different openings. Engines still
    /// evaluate single-threaded.
    #[clap(short, long)]
    pub(crate) threads: Option<NonZeroUsize>,

    /// If search at some depth is finished within this duration, a search of a depth one higher is
    /// started. The new search is always awaited, so this is not an upper bound in any way. The
    /// bound is applied to both engines equally. Given in milliseconds.
    #[clap(short, long, value_parser = parse_duration)]
    pub(crate) deepen_for: Duration
}

fn parse_duration(arg: &str) -> Result<Duration, ParseIntError> {
    let milliseconds = arg.parse()?;

    Ok(Duration::from_millis(milliseconds))
}
