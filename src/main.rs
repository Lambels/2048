#![deny(rust_2018_idioms)]

use std::io;

use game::{Game, GameExit};
use parser::Parser;

mod game;
mod parser;

fn main() -> Result<(), GameExit> {
    let parser = Parser::new(io::stdin());
    Game::new(parser).game_loop().map(|v| {
        println!("{v}");
        ()
    })
}
