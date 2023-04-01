use std::io::Read;

#[derive(Debug, Clone, Copy)]
pub enum Command {
    MoveLeft,
    MoveRight,
    MoveUp,
    MoveDown,
    Quit,
    Restart,
}

#[derive(Debug)]
pub enum ParsingError {}

pub struct Parser<R> {
    reader: R,
}

impl<R> Parser<R> {
    pub fn new(reader: R) -> Parser<R> {
        Parser { reader }
    }
}

impl<R: Read> Parser<R> {
    pub fn parse_command(&mut self) -> Result<Command, ParsingError> {
        todo!()
    }
}
