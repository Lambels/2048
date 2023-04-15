#![deny(rust_2018_idioms)]

use game::{Game, GameExit};

mod game;

fn main() -> Result<(), GameExit> {
    crossterm::terminal::enable_raw_mode().unwrap();

    Game::new().game_loop().map(|v| {
        println!("{v}");
        ()
    })
}
