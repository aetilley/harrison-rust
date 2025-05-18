use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::fs;
use std::ops::RangeInclusive;
use std::path::Path;

use crate::formula::{Formula, FormulaSet};
use crate::propositional_logic::Prop;

use itertools::iproduct;

const BOARD_SIZE: usize = 9;
const SUBBOARD_SIZE: usize = 3;
const RANGE: RangeInclusive<usize> = 1..=BOARD_SIZE;
// Note, paths are relative to top level package dir.
const PATH: &str = "./data/sudoku.txt";
const NUM_BOARDS: usize = 95;
const FILE_LEN_CHARS: usize = NUM_BOARDS * (BOARD_SIZE * BOARD_SIZE + 1); //(board size plus newline)

pub type Board = BTreeMap<(usize, usize), Option<u32>>;

fn _parse_board(input: &str) -> Board {
    // Returns a 1-indexed board.
    assert_eq!(input.len(), BOARD_SIZE.pow(2));
    let mut flat: Vec<Option<u32>> = Vec::new();
    for c in input.chars() {
        flat.push(c.to_digit(10));
    }
    let mut data = BTreeMap::new();
    for (i, item) in flat.into_iter().enumerate().take(BOARD_SIZE.pow(2)) {
        let row = i / BOARD_SIZE;
        let col = i % BOARD_SIZE;
        // 1-indexed
        data.insert((row + 1, col + 1), item);
    }
    data
}

pub fn parse_sudoku_dataset(path: &Path, maybe_limit: Option<usize>) -> Vec<Board> {
    // Read from PATH and return the first `limit`-many parsed boards

    let file_string = fs::read_to_string(path).unwrap();
    let lines: Vec<&str> = file_string.lines().collect();
    let limit = maybe_limit.unwrap_or(lines.len());
    let mut boards: Vec<Board> = Vec::new();
    for line in &lines[..limit] {
        let board = _parse_board(line);
        boards.push(board);
    }
    boards
}

pub fn _exactly_one_prop(props: &[Prop]) -> FormulaSet<Prop> {
    // Stating that exactly one of a collection of proposotions is true is
    // naturally expressed in CNF form.
    let at_least_one: BTreeSet<Formula<Prop>> = props.iter().map(Formula::atom).collect();
    let mut clauses = BTreeSet::from([at_least_one]);
    for i in 0..props.len() - 1 {
        for j in i + 1..props.len() {
            let not_i = Formula::not(&Formula::atom(&props[i]));
            let not_j = Formula::not(&Formula::atom(&props[j]));
            let not_both = BTreeSet::from([not_i, not_j]);
            clauses.insert(not_both);
        }
    }
    clauses
}

type AllProps = BTreeMap<(usize, usize, usize), Prop>;

fn get_all_props(board_size: usize) -> AllProps {
    // For each square and each number RANGE we have the
    // prop signifying that that square is that number
    let range: RangeInclusive<usize> = 1..=board_size;
    let mut props = BTreeMap::<(usize, usize, usize), Prop>::new();
    for row in range.clone() {
        for col in range.clone() {
            for val in range.clone() {
                let name = format!("{row}_{col}_{val}");
                let prop = Prop::new(&name);
                props.insert((row, col, val), prop);
            }
        }
    }
    props
}

fn get_row_constraints(props: &AllProps, board_size: usize) -> FormulaSet<Prop> {
    let range: RangeInclusive<usize> = 1..=board_size;
    let mut row_constraints: HashSet<FormulaSet<Prop>> = HashSet::new();
    for row in range.clone() {
        for val in range.clone() {
            // State that "exactly one column has the 1, exactly
            // one column has the 2, etc."
            let props: Vec<Prop> = range
                .clone()
                .map(|col| props[&(row, col, val)].clone())
                .collect();
            let constraint: FormulaSet<Prop> = _exactly_one_prop(&props);
            row_constraints.insert(constraint);
        }
    }
    // Take union
    row_constraints
        .into_iter()
        .fold(FormulaSet::new(), |x, y| &x | &y)
}

fn get_col_constraints(props: &AllProps, board_size: usize) -> FormulaSet<Prop> {
    let range: RangeInclusive<usize> = 1..=board_size;
    let mut col_constraints: HashSet<FormulaSet<Prop>> = HashSet::new();
    for col in range.clone() {
        for val in range.clone() {
            // State that "exactly one row has the 1, exactly
            // one row has the 2, etc."
            let props: Vec<Prop> = range
                .clone()
                .map(|row| props[&(row, col, val)].clone())
                .collect();
            let constraint: FormulaSet<Prop> = _exactly_one_prop(&props);
            col_constraints.insert(constraint);
        }
    }
    // Take union
    col_constraints
        .into_iter()
        .fold(FormulaSet::new(), |x, y| &x | &y)
}

type CoordSet = HashSet<(usize, usize)>;

fn _get_subboard_indices_and_offsets(
    board_size: usize,
    subboard_size: usize,
) -> (CoordSet, CoordSet) {
    let subrange: RangeInclusive<usize> = 1..=subboard_size;
    let first_subboard_indices: CoordSet = iproduct!(subrange.clone(), subrange).collect();

    assert_eq!(board_size % subboard_size, 0);
    let width_in_subboards = board_size / subboard_size;
    let offsets_1d = (0..width_in_subboards).map(|n| n * subboard_size);
    let subboard_offsets: CoordSet = iproduct!(offsets_1d.clone(), offsets_1d).collect();

    (first_subboard_indices, subboard_offsets)
}

fn get_subboard_constraints(
    props: &AllProps,
    board_size: usize,
    subboard_size: usize,
) -> FormulaSet<Prop> {
    let range: RangeInclusive<usize> = 1..=board_size;
    let (first_subboard_indices, subboard_offsets) =
        _get_subboard_indices_and_offsets(board_size, subboard_size);
    let mut subboard_constraints: HashSet<FormulaSet<Prop>> = HashSet::new();
    for (row_offset, col_offset) in subboard_offsets {
        for val in range.clone() {
            // State that "exactly one square has the 1, exactly
            // one square has the 2, etc."
            let props: Vec<Prop> = first_subboard_indices
                .iter()
                .map(|(row, col)| props[&(row + row_offset, col + col_offset, val)].clone())
                .collect();
            let constraint: FormulaSet<Prop> = _exactly_one_prop(&props);
            subboard_constraints.insert(constraint);
        }
    }
    // Take union
    subboard_constraints
        .into_iter()
        .fold(FormulaSet::new(), |x, y| &x | &y)
}

fn get_numerical_constraints(props: &AllProps, board_size: usize) -> FormulaSet<Prop> {
    // Constraints that exactly one value holds at any given square.
    let range: RangeInclusive<usize> = 1..=board_size;
    let mut numerical_constraints: HashSet<FormulaSet<Prop>> = HashSet::new();
    for row in range.clone() {
        for col in range.clone() {
            let props: Vec<Prop> = range
                .clone()
                .map(|val| props[&(row, col, val)].clone())
                .collect();
            let constraint: FormulaSet<Prop> = _exactly_one_prop(&props);
            numerical_constraints.insert(constraint);
        }
    }
    // Take union
    numerical_constraints
        .into_iter()
        .fold(FormulaSet::new(), |x, y| &x | &y)
}

fn get_start_constraints(props: &AllProps, board_size: usize, board: &Board) -> FormulaSet<Prop> {
    // Props for squares that have values to start must match those values.
    let range: RangeInclusive<usize> = 1..=board_size;
    let mut start_props: HashSet<Prop> = HashSet::new();
    for row in range.clone() {
        for col in range.clone() {
            if let Some(val) = board[&(row, col)] {
                start_props.insert(props[&(row, col, val as usize)].clone());
            }
        }
    }
    let start_constraint: FormulaSet<Prop> = start_props
        .into_iter()
        .map(|atom| BTreeSet::from([Formula::atom(&atom)]))
        .collect();
    start_constraint
}

pub fn get_board_formulas(
    boards: &[Board],
    board_size: usize,
    subboard_size: usize,
) -> Vec<FormulaSet<Prop>> {
    // FormulaSets are in CNF
    let props = get_all_props(board_size);

    let constant_constraints: FormulaSet<Prop> = [
        get_row_constraints(&props, board_size),
        get_col_constraints(&props, board_size),
        get_subboard_constraints(&props, board_size, subboard_size),
        get_numerical_constraints(&props, board_size),
    ]
    .iter()
    .fold(FormulaSet::new(), |x, y| &x | y);

    boards
        .iter()
        .map(|board| &constant_constraints | &get_start_constraints(&props, board_size, board))
        .collect()
}

#[cfg(test)]
mod sudoku_tests {

    use super::*;
    use crate::formula::{DPLBSolver, DPLISolver};
    use crate::utils::run_repeatedly_and_average;

    #[test]
    fn test_exactly_one() {
        let props: Vec<Prop> = (1..=3).map(|n| Prop::new(&format!("P{n}"))).collect();
        let result = _exactly_one_prop(&props);
        let desired = BTreeSet::from([
            BTreeSet::from([
                Formula::atom(&Prop::new("P1")),
                Formula::atom(&Prop::new("P2")),
                Formula::atom(&Prop::new("P3")),
            ]),
            BTreeSet::from([
                Formula::not(&Formula::atom(&Prop::new("P1"))),
                Formula::not(&Formula::atom(&Prop::new("P2"))),
            ]),
            BTreeSet::from([
                Formula::not(&Formula::atom(&Prop::new("P1"))),
                Formula::not(&Formula::atom(&Prop::new("P3"))),
            ]),
            BTreeSet::from([
                Formula::not(&Formula::atom(&Prop::new("P2"))),
                Formula::not(&Formula::atom(&Prop::new("P3"))),
            ]),
        ]);
        assert_eq!(result, desired);

        // Trivial case
        let props: Vec<Prop> = vec![Prop::new("P1")];
        let result = _exactly_one_prop(&props);
        let desired = BTreeSet::from([BTreeSet::from([Formula::atom(&Prop::new("P1"))])]);
        assert_eq!(result, desired);
    }

    #[test]
    fn test_get_start_constraints() {
        let s = "4.....8.5.3..........7......2.....6.....8.4......1.......6.3.7.5..2.....1.4......";
        let board: Board = _parse_board(s);
        let board_size = 9;
        let props = get_all_props(board_size);
        let result = get_start_constraints(&props, board_size, &board);
        let desired = BTreeSet::from([
            BTreeSet::from([Formula::atom(&Prop::new("1_1_4"))]),
            BTreeSet::from([Formula::atom(&Prop::new("1_7_8"))]),
            BTreeSet::from([Formula::atom(&Prop::new("1_9_5"))]),
            BTreeSet::from([Formula::atom(&Prop::new("2_2_3"))]),
            BTreeSet::from([Formula::atom(&Prop::new("3_4_7"))]),
            BTreeSet::from([Formula::atom(&Prop::new("4_2_2"))]),
            BTreeSet::from([Formula::atom(&Prop::new("4_8_6"))]),
            BTreeSet::from([Formula::atom(&Prop::new("5_5_8"))]),
            BTreeSet::from([Formula::atom(&Prop::new("5_7_4"))]),
            BTreeSet::from([Formula::atom(&Prop::new("6_5_1"))]),
            BTreeSet::from([Formula::atom(&Prop::new("7_4_6"))]),
            BTreeSet::from([Formula::atom(&Prop::new("7_6_3"))]),
            BTreeSet::from([Formula::atom(&Prop::new("7_8_7"))]),
            BTreeSet::from([Formula::atom(&Prop::new("8_1_5"))]),
            BTreeSet::from([Formula::atom(&Prop::new("8_4_2"))]),
            BTreeSet::from([Formula::atom(&Prop::new("9_1_1"))]),
            BTreeSet::from([Formula::atom(&Prop::new("9_3_4"))]),
        ]);
        assert_eq!(result, desired);
    }

    #[test]
    fn test_get_row_constraints() {
        let board_size = 2;
        let props = get_all_props(board_size);
        let result = get_row_constraints(&props, board_size);
        let desired = BTreeSet::from([
            BTreeSet::from([
                Formula::atom(&Prop::new("1_1_1")),
                Formula::atom(&Prop::new("1_2_1")),
            ]),
            BTreeSet::from([
                Formula::atom(&Prop::new("1_1_2")),
                Formula::atom(&Prop::new("1_2_2")),
            ]),
            BTreeSet::from([
                Formula::atom(&Prop::new("2_1_1")),
                Formula::atom(&Prop::new("2_2_1")),
            ]),
            BTreeSet::from([
                Formula::atom(&Prop::new("2_1_2")),
                Formula::atom(&Prop::new("2_2_2")),
            ]),
            BTreeSet::from([
                Formula::not(&Formula::atom(&Prop::new("1_1_1"))),
                Formula::not(&Formula::atom(&Prop::new("1_2_1"))),
            ]),
            BTreeSet::from([
                Formula::not(&Formula::atom(&Prop::new("1_1_2"))),
                Formula::not(&Formula::atom(&Prop::new("1_2_2"))),
            ]),
            BTreeSet::from([
                Formula::not(&Formula::atom(&Prop::new("2_1_1"))),
                Formula::not(&Formula::atom(&Prop::new("2_2_1"))),
            ]),
            BTreeSet::from([
                Formula::not(&Formula::atom(&Prop::new("2_1_2"))),
                Formula::not(&Formula::atom(&Prop::new("2_2_2"))),
            ]),
        ]);
        assert_eq!(result, desired);
    }

    #[test]
    fn test_get_col_constraints() {
        let board_size = 2;
        let props = get_all_props(board_size);
        let result = get_col_constraints(&props, board_size);
        let desired = BTreeSet::from([
            BTreeSet::from([
                Formula::atom(&Prop::new("1_1_1")),
                Formula::atom(&Prop::new("2_1_1")),
            ]),
            BTreeSet::from([
                Formula::atom(&Prop::new("1_1_2")),
                Formula::atom(&Prop::new("2_1_2")),
            ]),
            BTreeSet::from([
                Formula::atom(&Prop::new("1_2_1")),
                Formula::atom(&Prop::new("2_2_1")),
            ]),
            BTreeSet::from([
                Formula::atom(&Prop::new("1_2_2")),
                Formula::atom(&Prop::new("2_2_2")),
            ]),
            BTreeSet::from([
                Formula::not(&Formula::atom(&Prop::new("1_1_1"))),
                Formula::not(&Formula::atom(&Prop::new("2_1_1"))),
            ]),
            BTreeSet::from([
                Formula::not(&Formula::atom(&Prop::new("1_1_2"))),
                Formula::not(&Formula::atom(&Prop::new("2_1_2"))),
            ]),
            BTreeSet::from([
                Formula::not(&Formula::atom(&Prop::new("1_2_1"))),
                Formula::not(&Formula::atom(&Prop::new("2_2_1"))),
            ]),
            BTreeSet::from([
                Formula::not(&Formula::atom(&Prop::new("1_2_2"))),
                Formula::not(&Formula::atom(&Prop::new("2_2_2"))),
            ]),
        ]);
        assert_eq!(result, desired);
    }

    #[test]
    fn test_get_subboard_indices_and_offsets() {
        let board_size = 9;
        let subboard_size = 3;
        let (result_first_board, result_offsets) =
            _get_subboard_indices_and_offsets(board_size, subboard_size);
        let desired_first_board = HashSet::from([
            (1, 1),
            (1, 2),
            (1, 3),
            (2, 1),
            (2, 2),
            (2, 3),
            (3, 1),
            (3, 2),
            (3, 3),
        ]);
        let desired_offsets = HashSet::from([
            (0, 0),
            (0, 3),
            (0, 6),
            (3, 0),
            (3, 3),
            (3, 6),
            (6, 0),
            (6, 3),
            (6, 6),
        ]);
        assert_eq!(result_first_board, desired_first_board);
        assert_eq!(result_offsets, desired_offsets);

        let board_size = 3;
        let subboard_size = 1;
        let (result_first_board, result_offsets) =
            _get_subboard_indices_and_offsets(board_size, subboard_size);
        let desired_first_board = HashSet::from([(1, 1)]);

        let desired_offsets = HashSet::from([
            (0, 0),
            (0, 1),
            (0, 2),
            (1, 0),
            (1, 1),
            (1, 2),
            (2, 0),
            (2, 1),
            (2, 2),
        ]);
        assert_eq!(result_first_board, desired_first_board);
        assert_eq!(result_offsets, desired_offsets);
    }

    #[test]
    fn test_get_subboard_constraints() {
        let board_size = 2;
        let subboard_size = 1;

        let props = get_all_props(board_size);

        let result = get_subboard_constraints(&props, board_size, subboard_size);

        let desired = BTreeSet::from([
            BTreeSet::from([Formula::atom(&Prop::new("1_1_1"))]),
            BTreeSet::from([Formula::atom(&Prop::new("1_1_2"))]),
            BTreeSet::from([Formula::atom(&Prop::new("1_2_1"))]),
            BTreeSet::from([Formula::atom(&Prop::new("1_2_2"))]),
            BTreeSet::from([Formula::atom(&Prop::new("2_1_1"))]),
            BTreeSet::from([Formula::atom(&Prop::new("2_1_2"))]),
            BTreeSet::from([Formula::atom(&Prop::new("2_2_1"))]),
            BTreeSet::from([Formula::atom(&Prop::new("2_2_2"))]),
        ]);

        assert_eq!(result, desired);
    }

    #[test]
    fn test_get_numerical_constraints() {
        let board_size = 2;
        let props = get_all_props(board_size);
        let result = get_numerical_constraints(&props, board_size);
        let desired = BTreeSet::from([
            BTreeSet::from([
                Formula::atom(&Prop::new("1_1_1")),
                Formula::atom(&Prop::new("1_1_2")),
            ]),
            BTreeSet::from([
                Formula::atom(&Prop::new("1_2_1")),
                Formula::atom(&Prop::new("1_2_2")),
            ]),
            BTreeSet::from([
                Formula::atom(&Prop::new("2_1_1")),
                Formula::atom(&Prop::new("2_1_2")),
            ]),
            BTreeSet::from([
                Formula::atom(&Prop::new("2_2_1")),
                Formula::atom(&Prop::new("2_2_2")),
            ]),
            BTreeSet::from([
                Formula::not(&Formula::atom(&Prop::new("1_1_1"))),
                Formula::not(&Formula::atom(&Prop::new("1_1_2"))),
            ]),
            BTreeSet::from([
                Formula::not(&Formula::atom(&Prop::new("1_2_1"))),
                Formula::not(&Formula::atom(&Prop::new("1_2_2"))),
            ]),
            BTreeSet::from([
                Formula::not(&Formula::atom(&Prop::new("2_1_1"))),
                Formula::not(&Formula::atom(&Prop::new("2_1_2"))),
            ]),
            BTreeSet::from([
                Formula::not(&Formula::atom(&Prop::new("2_2_1"))),
                Formula::not(&Formula::atom(&Prop::new("2_2_2"))),
            ]),
        ]);
        assert_eq!(result, desired);
    }

    #[test]
    fn test_parse_file_and_get_some_formulas() {
        let limit = 5;
        let path: &Path = Path::new(PATH);
        let boards: Vec<Board> = parse_sudoku_dataset(path, Some(limit));
        assert_eq!(boards.len(), limit);

        let all_formulas = get_board_formulas(&boards, BOARD_SIZE, SUBBOARD_SIZE);
        assert_eq!(all_formulas.len(), limit);
    }

    // #[test] //Slow.
    fn test_parse_whole_file() {
        let path: &Path = Path::new(PATH);
        let boards: Vec<Board> = parse_sudoku_dataset(path, None);
        assert_eq!(boards.len(), NUM_BOARDS);
    }

    // #[test] //SLOWWW...
    fn solve_test_dpli_solver() {
        let path: &Path = Path::new(PATH);
        let boards: Vec<Board> = parse_sudoku_dataset(path, Some(2));
        let start_clauses = get_board_formulas(&boards, BOARD_SIZE, SUBBOARD_SIZE)[0].clone();
        let mut solver = DPLISolver::new(&start_clauses);
        let is_sat = solver.solve();
        assert!(is_sat);
        let formula = Formula::formulaset_to_cnf(start_clauses);
        assert!(formula.eval(&solver.get_valuation().unwrap()));
    }

    // Should probably be run in release mode.
    // #[test] //SLOWWW...
    fn solve_test_dplb_solver() {
        let path: &Path = Path::new(PATH);
        let boards: Vec<Board> = parse_sudoku_dataset(path, Some(2));
        let start_clauses = get_board_formulas(&boards, BOARD_SIZE, SUBBOARD_SIZE)[1].clone();
        let mut solver = DPLBSolver::new(&start_clauses);
        let is_sat = solver.solve();
        assert!(is_sat);
        let formula = Formula::formulaset_to_cnf(start_clauses);
        assert!(formula.eval(&solver.get_valuation().unwrap()));
        run_repeatedly_and_average(
            || {
                solver.solve();
            },
            10,
        );
    }
}
