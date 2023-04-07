use std::{collections::VecDeque, io::Read};

use crate::parser::{Command, Parser, ParsingError};

/// The empty value of a box in the 2048 game data model.
const EMPTY_BOX: u32 = 0;
/// The standard board size. 4x4
const BOARD_SIZE: usize = 16;
/// The standard board width.
const BOARD_WIDTH: usize = 4;

type WrapIter<T> = dyn DoubleEndedIterator<Item = WrapStep<T>>;

/// SkipWrap is an extension to an iterator which yields WrapSteps of usize which can be indexed in
/// an array.
///
/// The purpose of this trait is to blanket the implementation for skipping the EMPTY_BOX value for
/// the current column / row in an array provided the wrapping of the indexes.
trait SkipWrap: DoubleEndedIterator<Item = WrapStep<usize>> {
    /// wrap_skip_zero will walk the underlaying interator until it wraps. Before wrapping, if it
    /// encounters any zero values it skips them, advancing the iterator and returns the first non
    /// zero value BEFORE WRAPPING. If no non zero value is found before wrapping, the first
    /// wrapped value will be returned.
    fn wrap_skip_zero<T: Copy + PartialEq + Eq>(
        &mut self,
        source: &[T],
        zero: T,
    ) -> Option<WrapStep<T>> {
        loop {
            match self.next()? {
                WrapStep::Stepped(index) if source[index] != zero => {
                    return Some(WrapStep::Stepped(source[index]))
                }
                WrapStep::Stepped(_) => {}
                WrapStep::Wrapped(index) => return Some(WrapStep::Wrapped(source[index])),
            }
        }
    }
}

/// WrapStep represents a step taken in an iterator which might have wrapped.
#[derive(Debug, PartialEq, Eq)]
enum WrapStep<T> {
    /// Represents a step taken by the iterator which hasnt yet wrapped.
    Stepped(T),
    /// Represents the first step which wrapped.
    Wrapped(T),
}

/// *_pointer keeps row representation.
/// *_index keeps col representation.
struct ColumnWrap {
    front_pointer: usize,
    prev_front_index: usize,

    back_pointer: usize,
    prev_back_index: usize,

    wrap: usize,
}

impl ColumnWrap {
    fn new(size: usize, wrap: usize) -> Self {
        assert_eq!(size % wrap, 0);
        Self {
            front_pointer: 0,
            prev_front_index: 0,
            back_pointer: size - 1,
            prev_back_index: size - 1,
            wrap,
        }
    }
}

impl Iterator for ColumnWrap {
    type Item = WrapStep<usize>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.front_pointer > self.back_pointer {
            return None;
        } else if self.front_pointer == 0 {
            self.front_pointer += 1;
            return Some(WrapStep::Stepped(0));
        }

        let edge = self.front_pointer % self.wrap;
        self.front_pointer += 1;
        if edge == 0 {
            // we wrapped.
            self.prev_front_index = (self.prev_front_index % self.wrap) + 1;
            Some(WrapStep::Wrapped(self.prev_front_index))
        } else {
            // we didnt wrap.
            self.prev_front_index += self.wrap;
            Some(WrapStep::Stepped(self.prev_front_index))
        }
    }
}

impl DoubleEndedIterator for ColumnWrap {
    fn next_back(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

struct RowWrap {}

impl RowWrap {
    fn new(size: usize, wrap: usize) -> Self {
        todo!()
    }
}

impl Iterator for RowWrap {
    type Item = WrapStep<usize>;

    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

impl DoubleEndedIterator for RowWrap {
    fn next_back(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

#[derive(Default, PartialEq, Eq)]
struct GameState([u32; BOARD_SIZE]);

impl GameState {
    fn shift(&mut self, direction: Command) -> u32 {
        let (mut clean_iter, mut dirty_iter): (Box<WrapIter<_>>, Box<WrapIter<_>>) = match direction {
            Command::MoveUp | Command::MoveDown => (
                Box::new(ColumnWrap::new(BOARD_SIZE, BOARD_WIDTH)),
                Box::new(ColumnWrap::new(BOARD_SIZE, BOARD_WIDTH)),
            ),
            Command::MoveLeft | Command::MoveRight => (
                Box::new(RowWrap::new(BOARD_SIZE, BOARD_WIDTH)),
                Box::new(RowWrap::new(BOARD_SIZE, BOARD_WIDTH)),
            ),
            _ => unreachable!(),
        };

        // apply mask for inverted iterators.
        match direction {
            Command::MoveLeft | Command::MoveDown => {
                clean_iter = Box::new(clean_iter.rev());
                dirty_iter = Box::new(dirty_iter.rev());
            }
            _ => {}
        }

        todo!()
    }

    #[inline]
    fn reset(&mut self) {
        self.0.fill(EMPTY_BOX);
    }

    fn over(&self) -> bool {
        todo!()
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn column_wrap() {
        let mut column_iter = ColumnWrap::new(9, 3);

        assert_eq!(Some(WrapStep::Stepped(0)), column_iter.next());
        assert_eq!(Some(WrapStep::Stepped(3)), column_iter.next());
        assert_eq!(Some(WrapStep::Stepped(6)), column_iter.next());
        assert_eq!(Some(WrapStep::Wrapped(1)), column_iter.next());
        assert_eq!(Some(WrapStep::Stepped(4)), column_iter.next());
        assert_eq!(Some(WrapStep::Stepped(7)), column_iter.next());
        assert_eq!(Some(WrapStep::Wrapped(2)), column_iter.next());
        assert_eq!(Some(WrapStep::Stepped(5)), column_iter.next());
        assert_eq!(Some(WrapStep::Stepped(8)), column_iter.next());
        assert_eq!(None, column_iter.next());
    }
}
