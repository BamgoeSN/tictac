use std::{
    fmt::Display,
    io::{self, Write},
};

fn main() {
    let stdin = io::stdin();
    let mut stdout = io::stdout();
    let (_dp, strat) = preprocess();

    let mut game = Game::default();
    println!("Let's play Tic Tac Toe!");

    let mut my_turn = Cell::E;
    print!("Do you want to go first, or second? (O/X) ");
    stdout.flush().expect("Couldn't flush output into stdout");
    let mut buf = String::new();
    while my_turn == Cell::E {
        stdin.read_line(&mut buf).expect("Couldn't read from stdin");
        let s = buf.trim();
        match s {
            "o" | "O" => {
                my_turn = Cell::X;
            }
            "x" | "X" => {
                my_turn = Cell::O;
            }
            _ => {
                print!("Please enter a valid input. ");
                buf.clear();
                stdout.flush().expect("Couldn't flush output into stdout");
            }
        }
    }

    println!("{}", game);
    let mut turn = Cell::O;
    while game.who_won() == Some(None) {
        let pos = if turn == my_turn {
            let state: usize = (&game).into();
            strat[state].expect("Invalid state access while finding the strategy")
        } else {
            let mut pos = (4, 4);
            print!("Enter the row/col index (e.g. 0 2) ");
            stdout.flush().expect("Couldn't flush output into stdout");

            let mut buf = String::new();
            while pos == (4, 4) {
                stdin.read_line(&mut buf).expect("Couldn't read from stdin");
                let s = buf.trim();

                let arr: Vec<Option<usize>> =
                    s.split_whitespace().map(|x| x.parse().ok()).collect();
                if arr.len() != 2 || arr.iter().any(|x| x.is_none()) {
                    print!("Please enter a valid input. ");
                    buf.clear();
                    stdout.flush().expect("Couldn't flush output into stdout");
                } else {
                    let (r, c) = (arr[0].unwrap(), arr[1].unwrap());
                    if r >= 3 || c >= 3 {
                        print!("The position is out of bounds. ");
                        buf.clear();
                        stdout.flush().expect("Couldn't flush output into stdout");
                    } else if !game.board[r][c].is_empty() {
                        print!("The selected cell is already filled. ");
                        buf.clear();
                        stdout.flush().expect("Couldn't flush output into stdout");
                    } else {
                        pos = (r, c);
                    }
                }
            }

            pos
        };
        game.board[pos.0][pos.1] = turn;
        turn = turn.reverse();
        println!("{}", game);
        stdout.flush().expect("Couldn't flush output into stdout");
    }

    match game.who_won() {
        Some(won) => match won {
            Some(won) => match won {
                Win::Tie => {
                    println!("Tied!");
                }
                Win::O | Win::X => {
                    if won == my_turn.into() {
                        println!("You lost!");
                    } else {
                        println!("You won!");
                    }
                }
            },
            None => {
                panic!("Game finished prematurely");
            }
        },
        None => {
            panic!("Reached invalid state");
        }
    }
}

#[derive(Clone, Copy, Default, Debug, PartialEq, Eq)]
enum Cell {
    #[default]
    E,
    X,
    O,
}

impl From<Cell> for usize {
    fn from(c: Cell) -> Self {
        match c {
            Cell::E => 0,
            Cell::X => 1,
            Cell::O => 2,
        }
    }
}

impl From<usize> for Cell {
    fn from(x: usize) -> Self {
        let x = x % 3;
        if x == 0 {
            Self::E
        } else if x == 1 {
            Self::X
        } else {
            Self::O
        }
    }
}

impl Cell {
    fn is_empty(self) -> bool {
        self == Cell::E
    }

    fn reverse(self) -> Self {
        match self {
            Cell::E => Cell::E,
            Cell::X => Cell::O,
            Cell::O => Cell::X,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Win {
    X,
    O,
    Tie,
}

impl From<Win> for Cell {
    fn from(w: Win) -> Self {
        match w {
            Win::X => Cell::X,
            Win::O => Cell::O,
            Win::Tie => Cell::E,
        }
    }
}

impl From<Cell> for Win {
    fn from(c: Cell) -> Self {
        match c {
            Cell::E => Win::Tie,
            Cell::X => Win::X,
            Cell::O => Win::O,
        }
    }
}

impl Win {
    fn reverse(self) -> Self {
        match self {
            Win::X => Win::O,
            Win::O => Win::X,
            Win::Tie => Win::Tie,
        }
    }
}

#[derive(Clone, Default, Debug, PartialEq, Eq)]
struct Game {
    board: [[Cell; 3]; 3],
}

impl Display for Game {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for row in self.board.iter() {
            for &elm in row.iter() {
                match elm {
                    Cell::E => write!(f, ".")?,
                    Cell::X => write!(f, "X")?,
                    Cell::O => write!(f, "O")?,
                }
            }
            writeln!(f)?;
        }
        Ok(())
    }
}

impl From<&Game> for usize {
    fn from(g: &Game) -> Self {
        g.board
            .iter()
            .map(|r| r.iter())
            .flatten()
            .fold(0, |acc, &x| {
                let d: usize = x.into();
                acc * 3 + d
            })
    }
}

impl From<usize> for Game {
    fn from(n: usize) -> Game {
        let mut arr = vec![];
        let mut x = n;
        while x != 0 {
            arr.push(x % 3);
            x /= 3;
        }
        let mut ptr: usize = 9;
        let mut board = [[Cell::E; 3]; 3];
        for d in arr {
            ptr -= 1;
            let (r, c) = (ptr / 3, ptr % 3);
            board[r][c] = d.into();
        }
        Game { board }
    }
}

impl Game {
    /// Returns a vector of available next states, and position to add to move on to the state.
    /// Returns None if turn == Cell::E.
    fn gen_reachable(&self, turn: Cell) -> Option<Vec<(usize, (usize, usize))>> {
        if turn == Cell::E {
            return None;
        }
        let mut reachable = vec![];
        let mut state = self.clone();
        for r in 0..3 {
            for c in 0..3 {
                if state.board[r][c].is_empty() {
                    state.board[r][c] = turn;
                    reachable.push(((&state).into(), (r, c)));
                    state.board[r][c] = Cell::E;
                }
            }
        }
        Some(reachable)
    }

    /// Returns None if the given state is it appears that the both
    /// players have won. Returns Some(None) if no one has won.
    fn who_won(&self) -> Option<Option<Win>> {
        let mut x_win = false;
        let mut o_win = false;

        // Horizontal
        for row in self.board.iter() {
            if row.iter().all(|&x| x == Cell::X) {
                x_win = true;
            }
            if row.iter().all(|&x| x == Cell::O) {
                o_win = true;
            }
        }

        // Vertical
        for c in 0..3 {
            if (0..3).map(|r| self.board[r][c]).all(|x| x == Cell::X) {
                x_win = true;
            }
            if (0..3).map(|r| self.board[r][c]).all(|x| x == Cell::O) {
                o_win = true;
            }
        }

        // Diagonal
        if (0..3).map(|i| self.board[i][i]).all(|x| x == Cell::X) {
            x_win = true;
        }
        if (0..3).map(|i| self.board[i][i]).all(|x| x == Cell::O) {
            o_win = true;
        }
        if (0..3).map(|i| self.board[i][2 - i]).all(|x| x == Cell::X) {
            x_win = true;
        }
        if (0..3).map(|i| self.board[i][2 - i]).all(|x| x == Cell::O) {
            o_win = true;
        }

        match (x_win, o_win) {
            (true, true) => None,
            (true, false) => Some(Some(Win::X)),
            (false, true) => Some(Some(Win::O)),
            (false, false) => {
                if self
                    .board
                    .iter()
                    .map(|r| r.iter())
                    .flatten()
                    .filter(|x| x.is_empty())
                    .count()
                    == 0
                {
                    Some(Some(Win::Tie))
                } else {
                    Some(None)
                }
            }
        }
    }
}

fn preprocess() -> (Vec<Option<Win>>, Vec<Option<(usize, usize)>>) {
    let mut dp: Vec<Option<Win>> = vec![None; 3usize.pow(9)];
    let mut strat: Vec<Option<(usize, usize)>> = vec![None; 3usize.pow(9)];
    let mut winrate: Vec<Option<f64>> = vec![None; 3usize.pow(9)];

    for (state, p) in dp.iter_mut().enumerate() {
        let game: Game = state.into();
        if let Some(v) = game.who_won() {
            *p = v;
        }
    }

    preproc_recur(0, Cell::O, &mut dp, &mut strat, &mut winrate);
    (dp, strat)
}

/// Panics if turn == Cell::E.
fn preproc_recur(
    curr: usize,
    turn: Cell,
    dp: &mut [Option<Win>],
    strat: &mut [Option<(usize, usize)>],
    winrate: &mut [Option<f64>],
) -> (Win, f64) {
    if let Some(x) = dp[curr] {
        return if x == turn.into() { (x, 1.) } else { (x, 0.) };
    }

    let ifiwin: Win = turn.into();
    let ifilose = ifiwin.reverse();

    let game: Game = curr.into();
    debug_assert_eq!(game.who_won(), Some(None));

    let reachable = game
        .gen_reachable(turn)
        .expect("turn should be either Cell::X or Cell::O");
    let available: Vec<(Win, f64)> = reachable
        .iter()
        .map(|&next| {
            let val = preproc_recur(next.0, turn.reverse(), dp, strat, winrate);
            (val.0, 1. - val.1)
        })
        .collect();

    let to_win = (0..available.len())
        .find(|&i| available[i].0 == ifiwin)
        .map(|i| reachable[i].1);
    let to_tie = (0..available.len())
        .filter(|&i| available[i].0 != ifilose)
        .max_by(|&i, &j| available[i].1.total_cmp(&available[j].1))
        .map(|i| reachable[i].1);

    if let Some(pos) = to_win {
        strat[curr] = Some(pos);
        dp[curr] = Some(ifiwin);
        winrate[curr] = Some(1.);
        (ifiwin, 1.)
    } else if let Some(pos) = to_tie {
        strat[curr] = Some(pos);
        dp[curr] = Some(Win::Tie);
        let ratesum: f64 = available.iter().map(|&x| x.1).sum();
        let rate = ratesum / available.len() as f64;
        winrate[curr] = Some(rate);
        (Win::Tie, rate)
    } else {
        strat[curr] = Some(reachable[0].1);
        dp[curr] = Some(ifilose);
        (ifilose, 0.)
    }
}

#[cfg(test)]
mod test {
    use crate::*;

    #[test]
    fn game_usize_conversion() {
        let val: usize = 12859;
        let game: Game = val.into();
        let x: usize = (&game).into();
        let recover: Game = x.into();
        assert_eq!(val, x);
        assert_eq!(game, recover);
    }
}
