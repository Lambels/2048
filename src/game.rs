use std::{io::Read, mem, ops::Index, usize};
use core::{array, slice};

use crate::parser::{Command, Parser, ParsingError};

const EMPTY_BOX: usize = 0;
const BOARD_SIZE: usize = 16;
const BOARD_WIDTH: usize = 4;

/// sdgfsg
struct Columns {
    dirty: [u32; BOARD_SIZE],
    dirty_x: usize,
    clean_x: usize,
    wrap: usize,
}

enum WrapStep {
    Stepped(usize),
    Wrapped,
}

impl Columns {
    fn new(dirty: [u32; BOARD_SIZE]) {

    }

    // dont return a wraps step because clean pointer will always be behind dirty pointer.
    fn step_clean(&mut self) -> usize {
        
    }

    fn step_dirty(&mut self) -> (WrapStep, WrapStep) {}
}

impl Iterator for Columns {
    type Item = (usize, (u32, u32));

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let step = self.step_clean();
        let (dirty1, dirty2) = self.step_dirty();

        match (dirty1, dirty2) {
            (WrapStep::Wrapped, _) => Some(step, (EMPTY_BOX, EMPTY_BOX)),
            (WrapStep::Stepped(x), WrapStep::Wrapped) => Some(step, (x/2, x/2)),
            (WrapStep::Stepped(x), WrapStep::Stepped(y) => Some(step, (x, y)),
        }
    }
}

impl DoubleEndedIterator for Columns {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back()
    }
}

struct Rows();

#[derive(Default)]
struct GameState([u32; BOARD_SIZE]);

impl GameState {
    fn shift(&mut self, direction: Command) -> u32 {
        let mut stack_emitter: Box<dyn DoubleEndedIterator<Item = _>> = match direction {
            Command::MoveUp | Command::MoveDown => Box::new(Columns::new()),
            Command::MoveLeft | Command::MoveRight => Box::new(Rows::new()),
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
        let mut comp_ref = Some(stack_emitter.next().expect("The board must have 16 entries"));
        // free ref is reference to an element on the stack which is always free.
        let mut free_ref = None;
        comp_ref = comp_ref.and_then(|v| {
            if *v == EMPTY_BOX {
                free_ref = Some(v);
                None
            } else {
                Some(v)
            }
        });

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

            total += GameState::swap_with_fallback(current_ref, &mut comp_ref, &mut free_ref);
        }
        
        total
    }

    fn swap_with_fallback<'a>(v: &'a mut u32, ideal: &'a mut Option<&'a mut u32>, fallback: &'a mut Option<&'a mut u32>) -> u32 {
        if let Some(ref mut ideal_ptr) = *ideal {
            if *v == **ideal_ptr {
                let new_val = *v * 2;
                **ideal_ptr = new_val;
                *v = EMPTY_BOX;
                if fallback.is_none() {
                    *fallback = Some(v);
                }
                return new_val / 2;
            } else if let Some(ref mut fallback) = *fallback {
                mem::swap(*fallback, v);
                *ideal = Some(fallback);
                return 0;
            }
        } else if let Some(ref mut fallback_ptr) = *fallback {
            mem::swap(*fallback_ptr, v);
            *ideal = fallback.take();
            return 0;
        }

        unreachable!()
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

#[derive(Debug)]
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
