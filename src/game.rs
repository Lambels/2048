use std::io::Read;

use crate::parser::{Command, Parser, ParsingError};

struct Columns<'a> {
    inner: &'a mut [u32; 16],
    wrap: usize,
}

impl Columns<'_> {
    fn new(inner: &mut [u32; 16], wrap: usize) -> Columns<'_> {
        Columns { inner, wrap }
    }
}

impl<'a> Iterator for Columns<'a> {
    type Item = &'a mut [u32];

    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

impl<'a> DoubleEndedIterator for Columns<'a> {
    fn next_back(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

#[derive(Default)]
struct GameState {
    game: [u32; 16],
}

// impl Default for GameState {
//     fn default() -> Self {
//         Self { game: [0; 16] }
//     }
// }

impl GameState {
    fn shift(&mut self, direction: Command) -> u32 {
        let stack_emitter: Box<dyn DoubleEndedIterator<Item = _>> = match direction {
            Command::MoveUp | Command::MoveDown => Box::new(Columns::new(&mut self.game, 4)),
            Command::MoveLeft | Command::MoveRight => Box::new(self.game.chunks_exact_mut(4)),
            _ => unreachable!(),
        };

        stack_emitter
            .map(|v| GameState::calculate_stack(v, direction))
            .sum()
    }

    fn reset(&mut self) {}

    fn calculate_stack(stack: &mut [u32], direction: Command) -> u32 {
        todo!()
    }
}

pub struct Game<R> {
    parser: Parser<R>,

    game: GameState,
}

impl<R> Game<R> {
    pub fn new(parser: Parser<R>) -> Game<R> {
        Game {
            parser,
            game: GameState::default(),
        }
    }
}

impl<R: Read> Game<R> {
    pub fn game_loop(mut self) -> Result<(), ParsingError> {
        loop {
            match self.parser.parse_command()? {
                Command::Quit => return Ok(()),
                x @ (Command::MoveLeft
                | Command::MoveRight
                | Command::MoveUp
                | Command::MoveDown) => {
                    self.game.shift(x);
                }
                Command::Restart => self.game.reset(),
            };
        }
    }
}
