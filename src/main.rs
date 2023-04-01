#![deny(rust_2018_idioms)]

use std::io;

use game::Game;
use parser::Parser;

mod game;
mod parser;

fn main() -> Result<(), parser::ParsingError> {
    let parser = Parser::new(io::stdin());
    Game::new(parser).game_loop()
}
