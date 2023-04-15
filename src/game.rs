use std::{
    fmt::{Debug, Display},
    slice::SliceIndex,
};

use colored::{Color, ColoredString, Colorize};
use crossterm::event::{self, Event, KeyCode, KeyEvent};
use rand::Rng;

/// The empty value of a box in the 2048 game data model.
const EMPTY_BOX: u32 = 0;
/// The standard board size. 4x4
const BOARD_SIZE: usize = 16;
/// The standard board width.
const BOARD_WIDTH: usize = 4;

const CLEAR_BOARD: &'static str = "\x1B[2J\x1B[1;1H";

type WrapIter<T> = dyn DoubleEndedIterator<Item = WrapStep<T>>;

/// SkipWrap is an extension to an iterator which yields WrapSteps of usize which can be indexed in
/// an array.
///
/// The purpose of this trait is to blanket the implementation for skipping the EMPTY_BOX value for
/// the current column / row in an array provided the wrapping of the indexes.
trait SkipWrap<I>: DoubleEndedIterator<Item = WrapStep<I>> {
    /// wrap_skip_zero will walk the underlaying interator until it wraps. Before wrapping, if it
    /// encounters any zero values it skips them, advancing the iterator and returns the first non
    /// zero value BEFORE WRAPPING. If no non zero value is found before wrapping, the first
    /// wrapped value will be returned.
    fn wrap_skip_zero<'a, T>(
        &mut self,
        source: &'a [T],
        zero: &T,
    ) -> Option<WrapStep<&'a <I as SliceIndex<[T]>>::Output>>
    where
        I: SliceIndex<[T]> + Clone,
        <I as SliceIndex<[T]>>::Output: PartialEq<T> + Eq,
    {
        for index in self {
            let value = index.index_into(source);
            match value {
                WrapStep::Stepped(value) if value == zero => {}
                WrapStep::Stepped(value) => return Some(WrapStep::Stepped(value)),
                WrapStep::Wrapped(value) => return Some(WrapStep::Wrapped(value)),
            }
        }

        None
    }
}

impl<I, T> SkipWrap<I> for T where T: DoubleEndedIterator<Item = WrapStep<I>> {}

/// WrapStep represents a step taken in an iterator which might have wrapped.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum WrapStep<T> {
    /// Represents a step taken by the iterator which hasnt yet wrapped.
    Stepped(T),
    /// Represents the first step which wrapped.
    Wrapped(T),
}

impl<T> WrapStep<T> {
    fn is_wrapped(&self) -> bool {
        match self {
            WrapStep::Wrapped(_) => true,
            _ => false,
        }
    }
}

impl<I: Clone> WrapStep<I> {
    /// index_into turns a WrapStep which can index into a slice to a WrapStep corresponding to the
    /// Index opperation.
    fn index_into<'a, T>(&self, source: &'a [T]) -> WrapStep<&'a I::Output>
    where
        I: SliceIndex<[T]>,
    {
        match self {
            WrapStep::Stepped(index) => WrapStep::Stepped(&source[index.clone()]),
            WrapStep::Wrapped(index) => WrapStep::Wrapped(&source[index.clone()]),
        }
    }
}

impl<T: Clone> WrapStep<&T> {
    // cloned maps a WrapStep<&T> to a WrapStep<T> by cloning the T.
    fn cloned(&self) -> WrapStep<T> {
        match self {
            WrapStep::Stepped(value) => WrapStep::Stepped(T::clone(value)),
            WrapStep::Wrapped(value) => WrapStep::Wrapped(T::clone(value)),
        }
    }
}

impl<T> AsRef<T> for WrapStep<T> {
    // as_ref unwraps the &WrapStep<T> wrapper to reveal the &T.
    fn as_ref(&self) -> &T {
        match self {
            WrapStep::Stepped(v) => v,
            WrapStep::Wrapped(v) => v,
        }
    }
}

/// ColumnWrap is an iterator which yields indexes pointing in a row majour matrix. The indexes are
/// wrapped in the WrapStep enum indicating when the iterator wraps.
///
/// *_pointer keeps row representation.
/// *_index keeps col representation.
struct ColumnWrap {
    front_pointer: usize,
    prev_front_index: usize,

    back_pointer: usize,
    prev_back_index: usize,
    curr_back_head: usize,

    wrap: usize,
    size: usize,
}

impl ColumnWrap {
    /// new creates a new column iterator. wrap describes the width of each column.
    ///
    /// # Panics:
    /// new panics if size % wrap != 0
    fn new(size: usize, wrap: usize) -> Self {
        assert_eq!(size % wrap, 0);
        Self {
            front_pointer: 0,
            prev_front_index: 0,
            back_pointer: size,
            prev_back_index: size - 1,
            curr_back_head: size - 1,
            wrap,
            size,
        }
    }
}

impl Iterator for ColumnWrap {
    type Item = WrapStep<usize>;

    /// next yields the next index into row majour matrix.
    /// next returns None when the iterator finished all the possible indexes or intersects with
    /// indexes yielded by the next_back method.
    fn next(&mut self) -> Option<Self::Item> {
        if self.front_pointer >= self.back_pointer {
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
        if self.back_pointer <= self.front_pointer {
            return None;
        } else if self.back_pointer == self.size {
            self.back_pointer -= 1;
            return Some(WrapStep::Stepped(self.back_pointer));
        }

        let edge = self.back_pointer % self.wrap;
        self.back_pointer -= 1;
        if edge == 0 {
            // we wrapped, decrement the current head.
            self.curr_back_head -= 1;
            self.prev_back_index = self.curr_back_head;
            Some(WrapStep::Wrapped(self.curr_back_head))
        } else {
            // we didnt wrap.
            self.prev_back_index -= self.wrap;
            Some(WrapStep::Stepped(self.prev_back_index))
        }
    }
}

struct RowWrap {
    front_pointer: usize,
    back_pointer: usize,

    wrap: usize,
    size: usize,
}

impl RowWrap {
    fn new(size: usize, wrap: usize) -> Self {
        assert_eq!(size % wrap, 0);
        Self {
            front_pointer: 0,
            back_pointer: size,
            wrap,
            size,
        }
    }
}

impl Iterator for RowWrap {
    type Item = WrapStep<usize>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.front_pointer >= self.back_pointer {
            return None;
        } else if self.front_pointer == 0 {
            self.front_pointer += 1;
            return Some(WrapStep::Stepped(0));
        }

        let edge = self.front_pointer % self.wrap;
        self.front_pointer += 1;
        if edge == 0 {
            Some(WrapStep::Wrapped(self.front_pointer - 1))
        } else {
            Some(WrapStep::Stepped(self.front_pointer - 1))
        }
    }
}

impl DoubleEndedIterator for RowWrap {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.back_pointer <= self.front_pointer {
            return None;
        } else if self.back_pointer == self.size {
            self.back_pointer -= 1;
            return Some(WrapStep::Stepped(self.back_pointer));
        }

        let edge = self.back_pointer % self.wrap;
        self.back_pointer -= 1;
        if edge == 0 {
            Some(WrapStep::Wrapped(self.back_pointer))
        } else {
            Some(WrapStep::Stepped(self.back_pointer))
        }
    }
}

/// GameState is a state machine modeling the state of the game board of 2048.
#[derive(Default, PartialEq, Eq)]
struct GameState([u32; BOARD_SIZE]);

impl Debug for GameState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let digits = self.get_max_digits();

        let mut write_row = |row: &[u32]| -> std::fmt::Result {
            let mut iter = row.into_iter();
            let value = iter.next().unwrap();
            write!(f, "| {value:^digits$}")?;

            for value in iter {
                write!(f, " | {value:^digits$}")?;
            }
            write!(f, " |\n\r")
        };

        for row in self.0.chunks(BOARD_WIDTH) {
            write_row(row)?;
        }

        Ok(())
    }
}

impl Display for GameState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fn render_row(
            f: &mut std::fmt::Formatter<'_>,
            row: &[ColoredString],
            padding: usize,
        ) -> std::fmt::Result {
            let mut iter = row.into_iter();

            if let Some(value) = iter.next() {
                write!(f, "| {value:^padding$}")?;

                for value in iter {
                    write!(f, " | {value:^padding$}")?;
                }

                write!(f, " |")?;
            }

            Ok(())
        }

        fn map_to_color(value: u32) -> ColoredString {
            if value == EMPTY_BOX {
                return ColoredString::default();
            }

            let color = match value {
                x if x == 2 => Color::Green,
                x if x == 4 => Color::BrightGreen,
                x if x == 8 => Color::BrightCyan,
                x if x == 16 => Color::Cyan,
                x if x == 32 => Color::BrightBlue,
                x if x == 64 => Color::Blue,
                x if x == 128 => Color::BrightMagenta,
                x if x == 256 => Color::Magenta,
                x if x == 512 => Color::Yellow,
                x if x == 1024 => Color::BrightYellow,
                x if x == 2048 => Color::BrightRed,
                _ => unreachable!(),
            };

            value.to_string().color(color)
        }

        let digits = self.get_max_digits();
        let binding = self.0.map(map_to_color);
        let iterator = binding.chunks(BOARD_WIDTH);
        let bottom_border = "-".repeat(BOARD_WIDTH * (digits + BOARD_WIDTH) - 3);
        let top_border = "_".repeat(BOARD_WIDTH * (digits + BOARD_WIDTH) - 3);

        write!(f, "{top_border}\n\r")?;
        for row in iterator {
            render_row(f, row, digits)?;
            write!(f, "\n\r")?;
        }
        write!(f, "{bottom_border}\n\r")?;

        Ok(())
    }
}

impl GameState {
    fn get_max_digits(&self) -> usize {
        let max_value = self
            .0
            .iter()
            .copied()
            .max()
            .expect("expected at least one value");

        // | 2    |
        // | 2048 |

        f32::floor(f32::log10(max_value as f32)) as usize + 1
    }

    /// shift applies a Command wise shift. It returns the points gained after the move.
    ///
    /// # Panics:
    /// shift expects only Move* enum variants to be passed in.
    fn shift(&mut self, direction: KeyCode) -> u32 {
        let (mut clean_iter, mut dirty_iter): (Box<WrapIter<_>>, Box<WrapIter<_>>) = match direction
        {
            KeyCode::Up | KeyCode::Down => (
                Box::new(ColumnWrap::new(BOARD_SIZE, BOARD_WIDTH)),
                Box::new(ColumnWrap::new(BOARD_SIZE, BOARD_WIDTH)),
            ),
            KeyCode::Left | KeyCode::Right => (
                Box::new(RowWrap::new(BOARD_SIZE, BOARD_WIDTH)),
                Box::new(RowWrap::new(BOARD_SIZE, BOARD_WIDTH)),
            ),
            _ => unreachable!(),
        };

        // apply mask for inverted iterators.
        match direction {
            KeyCode::Right | KeyCode::Down => {
                clean_iter = Box::new(clean_iter.rev());
                dirty_iter = Box::new(dirty_iter.rev());
            }
            _ => {}
        }

        let mut previous_value = Some(
            dirty_iter
                .wrap_skip_zero(&self.0, &EMPTY_BOX)
                .expect("expected some value")
                .cloned(),
        );
        let mut total = 0;
        for index in clean_iter {
            match previous_value {
                Some(WrapStep::Stepped(value)) => {
                    // we need to get a new value to compare to the previous.
                    // if we get a match we replace with their sum, else just replace with the
                    // previous value and set the new value to the previous value.

                    let next_value = dirty_iter.wrap_skip_zero(&self.0, &EMPTY_BOX);
                    let (new_value, sum) = self.compare_and_swap(
                        *index.as_ref(),
                        value,
                        next_value.map(|v| v.cloned()),
                    );
                    previous_value = new_value;
                    total += sum;
                }
                Some(WrapStep::Wrapped(mut value)) => {
                    // we need to nullate the current wrap or do a swap.
                    // value will always point infront of the current index, so we nullate untill
                    // we get a synchronisation needed for the compare_and_swap opperation.

                    match index {
                        WrapStep::Stepped(index) => self.0[index] = EMPTY_BOX,
                        WrapStep::Wrapped(index) => {
                            // we are sync ed.

                            if value == EMPTY_BOX {
                                value = match dirty_iter.wrap_skip_zero(&self.0, &EMPTY_BOX) {
                                    None => EMPTY_BOX,
                                    Some(WrapStep::Wrapped(value)) => {
                                        previous_value = Some(WrapStep::Wrapped(*value));
                                        continue;
                                    }
                                    Some(WrapStep::Stepped(value)) => *value,
                                }
                            }

                            let next_value = dirty_iter.wrap_skip_zero(&self.0, &EMPTY_BOX);
                            let (new_value, sum) =
                                self.compare_and_swap(index, value, next_value.map(|v| v.cloned()));
                            previous_value = new_value;
                            total += sum;
                        }
                    }
                }
                None => {
                    // we either need to get 2 new items or nullate the current position.

                    let current_value = dirty_iter
                        .wrap_skip_zero(&self.0, &EMPTY_BOX)
                        .map(|v| v.cloned());
                    let next_value = match current_value {
                        None => {
                            self.0[*index.as_ref()] = EMPTY_BOX;
                            continue;
                        }
                        Some(value) if value.is_wrapped() => {
                            self.0[*index.as_ref()] = EMPTY_BOX;
                            previous_value = current_value;
                            continue;
                        }
                        Some(_) => dirty_iter.wrap_skip_zero(&self.0, &EMPTY_BOX),
                    };

                    let (new_value, sum) = self.compare_and_swap(
                        *index.as_ref(),
                        *current_value.unwrap().as_ref(),
                        next_value.map(|v| v.cloned()),
                    );
                    previous_value = new_value;
                    total += sum;
                }
            }
        }

        total
    }

    fn compare_and_swap(
        &mut self,
        index: usize,
        primary: u32,
        secondary: Option<WrapStep<u32>>,
    ) -> (Option<WrapStep<u32>>, u32) {
        match secondary {
            Some(WrapStep::Stepped(value)) if value == primary => {
                self.0[index] = value * 2;
                (None, value)
            }
            _ => {
                self.0[index] = primary;
                (secondary, 0)
            }
        }
    }

    /// reset resets the board state.
    #[inline]
    fn reset(&mut self) {
        self.0.fill(EMPTY_BOX);
    }

    /// is_over indicates wether there are any moves left to play.
    fn is_over(&self) -> bool {
        false
    }

    /// populate pseudo randomly adds a 2 or 4 box inside the game state at a random, valid location.
    ///
    /// 90% - 2
    /// 10% - 4
    fn populate(&mut self) {
        let mut rng_core = rand::thread_rng();
        let mut possible_values = self.0.iter_mut().filter(|&&mut v| v == EMPTY_BOX).collect::<Vec<_>>();
        let index = rng_core.gen_range(0..possible_values.len());

        if rng_core.gen_bool(0.9) {
            *possible_values[index] = 2;
        } else {
            *possible_values[index] = 4;
        }     
    }
}

/// Game represents all the global state the 2048 game should hold and IO capabilities by wrapping
/// the Parser type.
pub struct Game {
    game: GameState,
    score: u32,
}

impl Game {
    pub fn new() -> Game {
        Game {
            game: GameState::default(),
            score: 0,
        }
    }
}

/// GameExit represents any possible errors from the states of the game, either from the IO:
/// ParseError or the game itself: Quit ... .
#[derive(Debug)]
pub enum GameExit {
    /// ParseError represents any error from the parsing in the game loop.
    IOError(std::io::Error),
    /// Quit represents an exit signal from the user.
    Quit,
}

impl From<std::io::Error> for GameExit {
    fn from(value: std::io::Error) -> Self {
        GameExit::IOError(value)
    }
}

impl Game {
    /// game_loop starts the game loop for the game, this is the main entry point in the game. It
    /// handles IO by wrapping the command parser and outputing the games state. It also handles
    /// the actuall game by aplying the correct combination of moves and exiting when there are no
    /// more moves left.
    ///
    /// Ok(u32) represents that the game ended (no more moves where left) and returns the score the
    /// user accumulated during the game loop.
    ///
    /// Err(GameExit) represents an error which happened throughout the game_loop, either from the
    /// game itself or the IO process.
    pub fn game_loop(mut self) -> Result<u32, GameExit> {
        loop {
            print!("{}", CLEAR_BOARD);
            if self.game.is_over() {
                return Ok(self.score);
            }
            self.game.populate();
            print!("{}\n\r", self.game);

            loop {
                if let Event::Key(key_pressed) = event::read()? {
                    match key_pressed {
                        KeyEvent {
                            code:
                                value @ (KeyCode::Up | KeyCode::Down | KeyCode::Left | KeyCode::Right),
                            ..
                        } => self.score += self.game.shift(value),
                        KeyEvent {
                            code: KeyCode::Char('q'),
                            ..
                        } => return Err(GameExit::Quit),
                        KeyEvent {
                            code: KeyCode::Char('r'),
                            ..
                        } => self.game.reset(),
                        _ => continue,
                    }

                    break;
                }
            }
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

    #[test]
    fn column_wrap_rev() {
        let mut column_iter = ColumnWrap::new(9, 3);

        assert_eq!(Some(WrapStep::Stepped(8)), column_iter.next_back());
        assert_eq!(Some(WrapStep::Stepped(5)), column_iter.next_back());
        assert_eq!(Some(WrapStep::Stepped(2)), column_iter.next_back());
        assert_eq!(Some(WrapStep::Wrapped(7)), column_iter.next_back());
        assert_eq!(Some(WrapStep::Stepped(4)), column_iter.next_back());
        assert_eq!(Some(WrapStep::Stepped(1)), column_iter.next_back());
        assert_eq!(Some(WrapStep::Wrapped(6)), column_iter.next_back());
        assert_eq!(Some(WrapStep::Stepped(3)), column_iter.next_back());
        println!("Good till here");
        assert_eq!(Some(WrapStep::Stepped(0)), column_iter.next_back());
        println!("GOOOD");
        assert_eq!(None, column_iter.next_back());
        println!("WTF");
    }

    #[test]
    fn row_wrap() {
        let mut row_iter = RowWrap::new(9, 3);

        assert_eq!(Some(WrapStep::Stepped(0)), row_iter.next());
        assert_eq!(Some(WrapStep::Stepped(1)), row_iter.next());
        assert_eq!(Some(WrapStep::Stepped(2)), row_iter.next());
        assert_eq!(Some(WrapStep::Wrapped(3)), row_iter.next());
        assert_eq!(Some(WrapStep::Stepped(4)), row_iter.next());
        assert_eq!(Some(WrapStep::Stepped(5)), row_iter.next());
        assert_eq!(Some(WrapStep::Wrapped(6)), row_iter.next());
        assert_eq!(Some(WrapStep::Stepped(7)), row_iter.next());
        assert_eq!(Some(WrapStep::Stepped(8)), row_iter.next());
        assert_eq!(None, row_iter.next());
    }

    #[test]
    fn row_wrap_rev() {
        let mut row_iter = RowWrap::new(9, 3);

        assert_eq!(Some(WrapStep::Stepped(8)), row_iter.next_back());
        assert_eq!(Some(WrapStep::Stepped(7)), row_iter.next_back());
        assert_eq!(Some(WrapStep::Stepped(6)), row_iter.next_back());
        assert_eq!(Some(WrapStep::Wrapped(5)), row_iter.next_back());
        assert_eq!(Some(WrapStep::Stepped(4)), row_iter.next_back());
        assert_eq!(Some(WrapStep::Stepped(3)), row_iter.next_back());
        assert_eq!(Some(WrapStep::Wrapped(2)), row_iter.next_back());
        assert_eq!(Some(WrapStep::Stepped(1)), row_iter.next_back());
        assert_eq!(Some(WrapStep::Stepped(0)), row_iter.next_back());
        assert_eq!(None, row_iter.next());
    }

    #[test]
    fn shift_up() {
        let mut state = GameState([2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]);
        println!("{state:?}");

        let score = state.shift(KeyCode::Up);
        assert_eq!(score, 16);
        println!("{state:?}");
    }

    #[test]
    fn shift_up_with_zeros() {
        let mut state = GameState([2, 0, 0, 2, 0, 0, 4, 4, 2, 2, 2, 4, 2, 2, 2, 2]);
        println!("{state:?}");

        let score = state.shift(KeyCode::Up);
        println!("{state:?}");
    }

    #[test]
    fn shift_up_simple() {
        let mut state = GameState([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2]);
        println!("{state:?}");

        let score = state.shift(KeyCode::Up);
        assert_eq!(score, 0);
        println!("{state:?}");
    }

    #[test]
    fn shift_up_random1() {
        let mut state = GameState([0, 4, 2, 0, 4, 2, 8, 8, 8, 8, 8, 4, 2, 8, 2, 0]);
        println!("{state:?}");

        let score = state.shift(KeyCode::Up);
        assert_eq!(score, 16);
        println!("{state:?}");
    }

    #[test]
    fn display_board() {
        let mut state = GameState([
            0, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 0, 0, 0, 0,
        ]);

        println!("{state}");
        state.shift(KeyCode::Left);
        println!("{state}");
    }
} // FIRST 500 LINES OF RUST!
