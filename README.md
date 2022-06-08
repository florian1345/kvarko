# kvarko

The Kvarko Chess engine, written in Rust.
At the moment it is in early development and not really usable.

# Project structure

The project is separated into five crates.
Note that currently not everything specified here is actually implemented.

* `kvarko-model` implements the rules of Chess as well as move generation.
It also provides a framework to write controllers that can be registered to play a full game of Chess.
* `kvarko-engine` is the heart of the project and contains the actual Chess engine.
It is implemented as a controller for the `kvarko-model`.
* `kvarko-cli` is an application which gives CLI access to the Kvarko engine.
* `kvarko-view` is an application which gives UI access to the Kvarko engine.
* `kvarko-proc-macro` defines auxiliary macros used in some of the other crates.

# Magic numbers

A part of this project is a set of numbers used for generating [Magic Bitboards](https://www.chessprogramming.org/Magic_Bitboards).
They enable fancy magic bitboards with attack sharing and incorporation of the shift.
The set can be found in `kvarko/kvarko-model/magics.json`.
If the schema is not obvious enough, refer to the implementation of the `load_magics!` macro in `kvarko-proc-macro`.
Otherwise, the numbers were freshly generated for this project, so you can use them under the same license as the entire project.
