//! This module contains constants for all [Location]s on the Chess board for convenience.

use crate::board::{File, Location, Rank};

macro_rules! declare_square {
    ($file:ident, $rank:literal) => {
        paste::paste! {
            #[doc = "The location of the " $file $rank "-square."]
            pub const [<$file $rank>]: Location =
                Location::from_file_and_rank(File::$file, Rank::[<R $rank>]);
        }
    };
}

macro_rules! declare_file {
    ($file:ident) => {
        declare_square!($file, 1);
        declare_square!($file, 2);
        declare_square!($file, 3);
        declare_square!($file, 4);
        declare_square!($file, 5);
        declare_square!($file, 6);
        declare_square!($file, 7);
        declare_square!($file, 8);
    };
}

declare_file!(A);
declare_file!(B);
declare_file!(C);
declare_file!(D);
declare_file!(E);
declare_file!(F);
declare_file!(G);
declare_file!(H);
