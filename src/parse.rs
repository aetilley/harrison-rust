// General parsing utilities independent of particular logic.

use log::debug;
use std::fmt::Debug;

use crate::token::lex;

pub type ErrInner = &'static str;

// Most parsing functions below take the form of parsing a piece
// off the front of a [String], returning the parsed piece and the
// remaining input.
pub type PartialParseResult<'a, AST> = (AST, &'a [String]);
pub type MaybePartialParseResult<'a, AST> = Result<PartialParseResult<'a, AST>, ErrInner>;
pub type PartialParseListResult<'a, AST> = (Vec<AST>, &'a [String]);

// We use these wrappers for closures when passing to a recursive function
// like parse_general_infix to avoid trying to instantiate an unbounded number
// of function instances.  See https://github.com/rust-lang/rust/issues/43520
pub type SubparserFuncType<'c, T> = &'c dyn for<'b> Fn(&'b [String]) -> PartialParseResult<'b, T>;
pub type MaybeSubparserFuncType<'c, T> =
    &'c dyn for<'b> Fn(&'b [String]) -> MaybePartialParseResult<'b, T>;
pub type SubparserFuncListType<'c, T> =
    &'c dyn for<'b> Fn(&'b [String]) -> PartialParseListResult<'b, T>;

pub struct Subparser<'a, AST> {
    pub fun: SubparserFuncType<'a, AST>,
}
impl<'a, AST> Subparser<'a, AST> {
    fn call<'b>(&self, ast: &'b [String]) -> PartialParseResult<'b, AST> {
        (self.fun)(ast)
    }
}

pub struct MaybeSubparser<'a, AST> {
    pub fun: MaybeSubparserFuncType<'a, AST>,
}
impl<'a, AST> MaybeSubparser<'a, AST> {
    fn call<'b>(&self, ast: &'b [String]) -> MaybePartialParseResult<'b, AST> {
        (self.fun)(ast)
    }
}

pub struct ListSubparser<'a, AST> {
    pub fun: SubparserFuncListType<'a, AST>,
}
impl<'a, AST> ListSubparser<'a, AST> {
    fn call<'b>(&self, ast: &'b [String]) -> PartialParseListResult<'b, AST> {
        (self.fun)(ast)
    }
}
// Agg and AggList functions close over aggregates and combine
// newly parsed items with that aggregate.
// (Compare Harrison's "sof" functions.)
type AggFuncType<'a, AST> = &'a dyn Fn(AST) -> AST;
struct Agg<'a, AST> {
    fun: AggFuncType<'a, AST>,
}
impl<'a, AST> Agg<'a, AST> {
    fn call(&self, ast: AST) -> AST {
        (self.fun)(ast)
    }
}

type AggListFuncType<'a, AST> = &'a dyn Fn(AST) -> Vec<AST>;
struct AggList<'a, AST> {
    fun: AggListFuncType<'a, AST>,
}
impl<'a, AST> AggList<'a, AST> {
    fn call(&self, ast: AST) -> Vec<AST> {
        (self.fun)(ast)
    }
}

// The OpUpdate and OpUpdateList functions evolve the Agg
// and AggList accumulators by having them store
// larger ASTs.

type OpUpdateFuncType<'a, AST> = &'a dyn Fn(AggFuncType<AST>, AST, AST) -> AST;
#[derive(Clone)]
struct OpUpdate<'a, AST> {
    fun: OpUpdateFuncType<'a, AST>,
}
impl<'a, AST> OpUpdate<'a, AST> {
    fn call(&self, f: &impl Fn(AST) -> AST, ast1: AST, ast2: AST) -> AST {
        (self.fun)(f, ast1, ast2)
    }
}

type OpUpdateListFuncType<'a, AST> = &'a dyn Fn(AggListFuncType<AST>, AST, AST) -> Vec<AST>;
#[derive(Clone)]
struct OpUpdateList<'a, AST> {
    fun: OpUpdateListFuncType<'a, AST>,
}
impl<'a, AST> OpUpdateList<'a, AST> {
    fn call(&self, f: &impl Fn(AST) -> Vec<AST>, ast1: AST, ast2: AST) -> Vec<AST> {
        (self.fun)(f, ast1, ast2)
    }
}

// ### Abstract parser builders

fn parse_general_infix<'a, AST: Clone>(
    op_symbol: &str,
    op_update: OpUpdate<AST>,
    agg: Agg<AST>,
    subparser: Subparser<AST>,
    input: &'a [String],
) -> PartialParseResult<'a, AST> {
    // Parser buider that parses a piece off the front of the `input` and either adds
    // it to the accumulator in `Agg` or, if a select infix operation `op_symbol` follows, evolves
    // the aggregator via `op_update`.
    // `op_update` and `agg` will depend on whether the operation is left or right
    // associative.
    let (ast1, rest1) = subparser.call(input);
    match rest1 {
        [head, rest2 @ ..] if head == op_symbol => {
            let op_update_clone = op_update.clone();
            let new_agg: Agg<AST> = Agg {
                fun: &|ast| op_update_clone.call(&|ast1| agg.call(ast1), ast1.clone(), ast),
            };
            parse_general_infix(op_symbol, op_update, new_agg, subparser, rest2)
        }
        _ => (agg.call(ast1), rest1),
    }
}

pub fn parse_right_infix<'a, AST: Clone>(
    op_symbol: &str,
    op_constructor: fn(AST, AST) -> AST,
    subparser: Subparser<AST>,
    input: &'a [String],
) -> PartialParseResult<'a, AST> {
    // Parser builder for handling right-associative infix operations.
    // op_constructor should be a constructor for ASTs of type corresponding
    // to `op_symbol`.
    let op_update = OpUpdate {
        fun: &|f, ast1, ast2| f(op_constructor(ast1, ast2)),
    };
    let agg = Agg { fun: &|ast| ast };
    parse_general_infix(op_symbol, op_update, agg, subparser, input)
}

pub fn parse_left_infix<'a, AST: Clone>(
    op_symbol: &str,
    op_constructor: fn(AST, AST) -> AST,
    subparser: Subparser<AST>,
    input: &'a [String],
) -> PartialParseResult<'a, AST> {
    // Parser builder for handling left-associative infix operations.
    // op_constructor should be a constructor for ASTs of type corresponding
    // to `op_symbol`.
    let op_update = OpUpdate {
        fun: &|f, ast1, ast2| op_constructor(f(ast1), ast2),
    };
    let agg = Agg { fun: &|ast| ast };
    parse_general_infix(op_symbol, op_update, agg, subparser, input)
}

fn parse_general_list<'a, AST: Clone>(
    op_symbol: &str,
    op_update: OpUpdateList<AST>,
    agg: AggList<AST>,
    subparser: Subparser<AST>,
    input: &'a [String],
) -> PartialParseListResult<'a, AST> {
    // Parse one element of the list type and check if a
    // list delimiter follows (usually a comma).  If so continue
    // parsing with an updated Agg function that stores a copy of the
    // first value.
    let (ast1, rest1) = subparser.call(input);
    match rest1 {
        [head, rest2 @ ..] if head == op_symbol => {
            let op_update_clone = op_update.clone();
            let new_agg_fun = |ast| op_update_clone.call(&|ast| agg.call(ast), ast1.clone(), ast);
            let new_agg: AggList<AST> = AggList { fun: &new_agg_fun };
            parse_general_list(op_symbol, op_update, new_agg, subparser, rest2)
        }
        _ => (agg.call(ast1), rest1),
    }
}

pub fn parse_list<'a, AST: Clone>(
    op_symbol: &str,
    subparser: Subparser<AST>,
    input: &'a [String],
) -> PartialParseListResult<'a, AST> {
    debug!("parse_list called on op_symbol {op_symbol:?}, input {input:?}");
    // Evolves a Agg function to one that appends an element (`ast2`) onto
    // a previously existing list (the result of calling the previous
    // agg on `ast1`).
    let op_update = OpUpdateList {
        fun: &|f, ast1, ast2| -> Vec<AST> {
            let mut v = f(ast1);
            v.push(ast2);
            v
        },
    };
    // First agg just puts a single list item into
    // a singleton vector.
    let agg = AggList {
        fun: &|ast: AST| -> Vec<AST> { vec![ast] },
    };
    parse_general_list(op_symbol, op_update, agg, subparser, input)
}

pub fn parse_bracketed<'a, AST: Clone + Debug>(
    subparser: Subparser<AST>,
    input: &'a [String],
) -> PartialParseResult<'a, AST> {
    // To be called after an opening bracket has been read.
    // The `subparser` should be able to parse all the way
    // to the closing bracket and otherwise we panic.
    debug!("parse_bracketed called on input {input:?}");
    let (ast, rest) = subparser.call(input);

    match rest {
        [head, tail @ ..] if head == ")" => (ast, tail),
        _ => {
            panic!("Closing bracket expected. Found {rest:?}");
        }
    }
}

pub fn maybe_parse_bracketed<'a, AST: Clone + Debug>(
    subparser: MaybeSubparser<AST>,
    input: &'a [String],
) -> Result<PartialParseResult<'a, AST>, ErrInner> {
    // To be called after an opening bracket has been read.
    // The subparser may fail, but if it succees to parse
    // any piece then it should parse all the way
    // to the closing bracket otherwise return Result::Err.
    debug!("parse_bracketed called on input {input:?}");
    let (ast, rest) = subparser.call(input)?;

    match rest {
        [head, tail @ ..] if head == ")" => Ok((ast, tail)),
        _ => {
            panic!("Closing bracket expected. Found {rest:?}");
        }
    }
}

pub fn parse_bracketed_list<'a, AST: Clone + Debug>(
    subparser: ListSubparser<AST>,
    input: &'a [String],
) -> PartialParseListResult<'a, AST> {
    // Same as parse_bracketed but subparser is of
    // ListSubparser type, and this function can handle empty
    // lists (first character ")").
    debug!("parse_bracketed_list called on input {input:?}");
    if let [head, rest @ ..] = input {
        if head == ")" {
            return (vec![], rest);
        }
    }

    let (ast, rest) = subparser.call(input);

    match rest {
        [head, tail @ ..] if head == ")" => (ast, tail),
        _ => {
            panic!("Closing bracket expected. Found {rest:?}");
        }
    }
}

pub fn generic_parser<AST>(inner: fn(&[String]) -> (AST, &[String]), input: &str) -> AST {
    // Tokenize and call parser on result.
    // (Compare Harrison's `make_parser`.)
    let lexed = lex(input);
    let (expr, rest) = inner(&lexed[..]);
    if !rest.is_empty() {
        panic!("Unparsed input {rest:?}");
    }
    expr
}

#[cfg(test)]
mod generic_parsing_tests {
    use super::*;
    // We use Formula for convenience in these tests, but this parent module (`parse`) should
    // not depend on `formula`.
    use crate::formula::Formula;
    use crate::utils::to_vec_of_owned;

    fn init() {
        let _ = env_logger::builder().is_test(true).try_init();
    }

    // Begin parsing tests
    fn _parse_conjunction(input: &[String]) -> (Formula<String>, &[String]) {
        parse_right_infix("&", Formula::and, Subparser { fun: &_parse_unit }, input)
    }

    fn _parse_unit(input: &[String]) -> (Formula<String>, &[String]) {
        match input {
            [head, rest @ ..] if head == "(" => parse_bracketed(
                Subparser {
                    fun: &_parse_conjunction,
                },
                rest,
            ),
            [head, rest @ ..] => (Formula::atom(head.to_string()), rest),
            _ => {
                panic!("got empty input");
            }
        }
    }

    #[test]
    fn test_parse_right_infix_two_conjuncts() {
        let input_vect: Vec<String> = to_vec_of_owned(vec!["P", "&", "Q"]);
        let input = &input_vect[..];
        let result = parse_right_infix("&", Formula::and, Subparser { fun: &_parse_unit }, input);
        let empty: &[String] = &[];
        let desired = (
            Formula::and(
                Formula::atom(String::from("P")),
                Formula::atom(String::from("Q")),
            ),
            empty,
        );
        assert_eq!(result, desired);
    }

    #[test]
    fn test_parse_right_infix_three_conjuncts() {
        let input_vect: Vec<String> = to_vec_of_owned(vec!["P", "&", "Q", "&", "S"]);
        let input = &input_vect[..];
        let result = parse_right_infix("&", Formula::and, Subparser { fun: &_parse_unit }, input);
        let empty: &[String] = &[];
        let desired = (
            Formula::and(
                Formula::atom(String::from("P")),
                Formula::and(
                    Formula::atom(String::from("Q")),
                    Formula::atom(String::from("S")),
                ),
            ),
            empty,
        );
        assert_eq!(result, desired);
    }
    #[test]
    fn test_parse_left_infix_two_conjuncts() {
        let input_vect: Vec<String> = to_vec_of_owned(vec!["P", "&", "Q"]);
        let input = &input_vect[..];
        let result = parse_left_infix("&", Formula::and, Subparser { fun: &_parse_unit }, input);
        let empty: &[String] = &[];
        let desired = (
            Formula::and(
                Formula::atom(String::from("P")),
                Formula::atom(String::from("Q")),
            ),
            empty,
        );
        assert_eq!(result, desired);
    }

    #[test]
    fn test_parse_left_infix_three_conjuncts() {
        let input_vect: Vec<String> = to_vec_of_owned(vec!["P", "&", "Q", "&", "S"]);
        let input = &input_vect[..];
        let result = parse_left_infix("&", Formula::and, Subparser { fun: &_parse_unit }, input);
        let empty: &[String] = &[];
        let desired = (
            Formula::and(
                Formula::and(
                    Formula::atom(String::from("P")),
                    Formula::atom(String::from("Q")),
                ),
                Formula::atom(String::from("S")),
            ),
            empty,
        );
        assert_eq!(result, desired);
    }

    #[test]
    fn test_parse_bracketed() {
        init();
        let input_vect: Vec<String> = to_vec_of_owned(vec![
            "P", "&", "(", "Q", "&", "(", "S", "&", "T", ")", "&", "U", ")", ")",
        ]);
        let input = &input_vect[..];
        let result = parse_bracketed(
            Subparser {
                fun: &_parse_conjunction,
            },
            input,
        );
        let empty: &[String] = &[];
        let desired = (
            (Formula::and(
                Formula::atom(String::from("P")),
                Formula::and(
                    Formula::atom(String::from("Q")),
                    Formula::and(
                        Formula::and(
                            Formula::atom(String::from("S")),
                            Formula::atom(String::from("T")),
                        ),
                        Formula::atom(String::from("U")),
                    ),
                ),
            )),
            empty,
        );
        assert_eq!(result, desired);
    }

    #[test]
    fn test_parse_list() {
        init();
        let input_vect: Vec<String> = to_vec_of_owned(vec!["A", ",", "B", ",", "C", "REST"]);
        let input = &input_vect[..];
        let result = parse_list(",", Subparser { fun: &_parse_unit }, input);
        let desired_list = vec![
            Formula::atom(String::from("A")),
            Formula::atom(String::from("B")),
            Formula::atom(String::from("C")),
        ];
        let desired = (desired_list, &[String::from("REST")][..]);
        assert_eq!(result, desired);
    }

    #[test]
    fn test_parse_bracketed_list() {
        init();
        let input_vect: Vec<String> = to_vec_of_owned(vec!["A", ",", "B", ")", "REST"]);
        let input = &input_vect[..];
        let list_subparser: SubparserFuncListType<Formula<String>> =
            &|input| parse_list(",", Subparser { fun: &_parse_unit }, input);
        let result = parse_bracketed_list(
            ListSubparser {
                fun: list_subparser,
            },
            input,
        );
        let desired_list = vec![
            Formula::atom(String::from("A")),
            Formula::atom(String::from("B")),
        ];
        let desired = (desired_list, &[String::from("REST")][..]);
        assert_eq!(result, desired);
    }

    #[test]
    fn test_parse_bracketed_empty_list() {
        init();
        let input_vect: Vec<String> = to_vec_of_owned(vec![")", "REST"]);
        let input = &input_vect[..];
        let list_subparser: SubparserFuncListType<Formula<String>> =
            &|input| parse_list(",", Subparser { fun: &_parse_unit }, input);
        let result = parse_bracketed_list(
            ListSubparser {
                fun: list_subparser,
            },
            input,
        );
        let desired = (vec![], &[String::from("REST")][..]);
        assert_eq!(result, desired);
    }
}
