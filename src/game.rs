use std::{io::Read, mem};

use crate::parser::{Command, Parser, ParsingError};

const EMPTY_BOX: u32 = 0;

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
    type Item = &'a mut u32;

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
struct GameState([u32; 16]);

impl GameState {
    fn shift(&mut self, direction: Command) -> u32 {
        let stack_emitter: Box<dyn DoubleEndedIterator<Item = _>> = match direction {
            Command::MoveUp | Command::MoveDown => Box::new(Columns::new(&mut self.0, 4)),
            Command::MoveLeft | Command::MoveRight => {
                Box::new(self.0.iter_mut())
            }
            _ => unreachable!(),
        };

        // apply mask for inverted iterators.
        match direction {
            Command::MoveLeft | Command::MoveDown => {
                stack_emitter = Box::new(stack_emitter.rev());
            }
            _ => {}
        }

        let mut count = 0;
        let mut total = 0;
        
        // set compare (ideal) reference to the top element of the stack.
        let mut comp_ref: Option<&mut u32> = Some(stack_emitter.next().expect("The board must have 16 entries"));
        // free ref is reference to an element on the stack which is always free.
        let mut free_ref: Option<&mut u32> = None;
        while let Some(current_ref) = stack_emitter.next() {
            count += 1;
            if count % 4 == 0 {
                comp_ref = Some(current_ref);
                continue;
            }

            if *current_ref == EMPTY_BOX && free_ref.is_none() {
                free_ref = Some(current_ref);
                continue;
            }

            GameState::swap_with_fallback(current_ref, comp_ref, free_ref);
        }
        
        total
    }

    fn swap_with_fallback(v: &mut u32, ideal: Option<&mut u32>, fallback: Option<&mut u32>) -> u32 {
        if let Some(ideal) = ideal {
            if *v == *ideal {
                *ideal = *v * 2;
                v
            } else if let Some(fallback) = fallback {
                            
            } else {
    
            }
        } else if let Some(v) = fallback {

        }  
    }

    #[inline]
    fn reset(&mut self) {
        self.0.fill(EMPTY_BOX);
    }

    fn over(&self) -> bool {
        false
    }

    fn populate(&mut self) {}
}

pub struct Game<R> {
    parser: Parser<R>,

    game: GameState,
    score: u32,
}

impl<R> Game<R> {
    pub fn new(parser: Parser<R>) -> Game<R> {
        Game {
            parser,
            game: GameState::default(),
            score: 0,
        }
    }
}

pub enum GameExit {
    ParseError(ParsingError),
    Quit,
}

impl From<ParsingError> for GameExit {
    fn from(value: ParsingError) -> Self {
        GameExit::ParseError(value)
    }
}

impl<R: Read> Game<R> {
    pub fn game_loop(mut self) -> Result<u32, GameExit> {
        loop {
            if self.game.over() {
                return Ok(self.score);
            }
            self.game.populate();

            match self.parser.parse_command()? {
                Command::Quit => return Err(GameExit::Quit),
                x @ (Command::MoveLeft
                | Command::MoveRight
                | Command::MoveUp
                | Command::MoveDown) => {
                    self.score += self.game.shift(x);
                }
                Command::Restart => self.game.reset(),
            };
        }
    }
}
