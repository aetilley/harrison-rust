// General parsing utilities independent of particular logic.

use crate::token::lex;

use log::debug;
use std::fmt::Debug;

pub type PartialParseResult<'a, AST> = (AST, &'a [String]);
pub type PartialParseListResult<'a, AST> = (Vec<AST>, &'a [String]);

// We use these wrappers for closures when passing to a recursive function
// like parse_general_infix to avoid trying to instantiate an unbounded number
// of function instances.  See https://github.com/rust-lang/rust/issues/43520
#[derive(Clone)]
struct OpUpdate<'a, AST> {
    fun: &'a dyn Fn(&dyn Fn(AST) -> AST, AST, AST) -> AST,
}

impl<'a, AST> OpUpdate<'a, AST> {
    fn call(&self, f: &impl Fn(AST) -> AST, ast1: AST, ast2: AST) -> AST {
        (self.fun)(f, ast1, ast2)
    }
}

struct Sof<'a, AST> {
    fun: &'a dyn Fn(AST) -> AST,
}

impl<'a, AST> Sof<'a, AST> {
    fn call(&self, ast: AST) -> AST {
        (self.fun)(ast)
    }
}

pub type SubparserFuncType<'c, T> = &'c dyn for<'b> Fn(&'b [String]) -> PartialParseResult<'b, T>;
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

pub struct ListSubparser<'a, AST> {
    pub fun: SubparserFuncListType<'a, AST>,
}

impl<'a, AST> ListSubparser<'a, AST> {
    fn call<'b>(&self, ast: &'b [String]) -> PartialParseListResult<'b, AST> {
        (self.fun)(ast)
    }
}

#[derive(Clone)]
struct OpUpdateList<'a, AST> {
    fun: &'a dyn Fn(&dyn Fn(AST) -> Vec<AST>, AST, AST) -> Vec<AST>,
}

impl<'a, AST> OpUpdateList<'a, AST> {
    fn call(&self, f: &impl Fn(AST) -> Vec<AST>, ast1: AST, ast2: AST) -> Vec<AST> {
        (self.fun)(f, ast1, ast2)
    }
}

struct SofList<'a, AST> {
    fun: &'a dyn Fn(AST) -> Vec<AST>,
}

impl<'a, AST> SofList<'a, AST> {
    fn call(&self, ast: AST) -> Vec<AST> {
        (self.fun)(ast)
    }
}

fn parse_general_infix<'a, AST: Clone>(
    op_symbol: &str,
    op_update: OpUpdate<AST>,
    sof: Sof<AST>,
    subparser: Subparser<AST>,
    input: &'a [String],
) -> PartialParseResult<'a, AST> {
    let (ast1, rest1) = subparser.call(input);
    match rest1 {
        [head, rest2 @ ..] if head == op_symbol => {
            let op_update_clone = op_update.clone();
            let new_sof_fun = |ast| op_update_clone.call(&|ast1| sof.call(ast1), ast1.clone(), ast);
            let new_sof: Sof<AST> = Sof { fun: &new_sof_fun };
            parse_general_infix(op_symbol, op_update, new_sof, subparser, rest2)
        }
        _ => (sof.call(ast1), rest1),
    }
}

pub fn parse_right_infix<'a, AST: Clone>(
    op_symbol: &str,
    op_constructor: fn(AST, AST) -> AST,
    subparser: Subparser<AST>,
    input: &'a [String],
) -> PartialParseResult<'a, AST> {
    let op_update = OpUpdate {
        fun: &|f, ast1, ast2| f(op_constructor(ast1, ast2)),
    };
    let sof = Sof { fun: &|x| x };
    parse_general_infix(op_symbol, op_update, sof, subparser, input)
}

pub fn parse_left_infix<'a, AST: Clone>(
    op_symbol: &str,
    op_constructor: fn(AST, AST) -> AST,
    subparser: Subparser<AST>,
    input: &'a [String],
) -> PartialParseResult<'a, AST> {
    let op_update = OpUpdate {
        fun: &|f, ast1, ast2| op_constructor(f(ast1), ast2),
    };
    let sof = Sof { fun: &|ast| ast };
    parse_general_infix(op_symbol, op_update, sof, subparser, input)
}

fn parse_general_list<'a, AST: Clone>(
    op_symbol: &str,
    op_update: OpUpdateList<AST>,
    sof: SofList<AST>,
    subparser: Subparser<AST>,
    input: &'a [String],
) -> PartialParseListResult<'a, AST> {
    // TODO(arthur) COMMENT
    // op_symbol will be the list delimiter, usually a comma.
    let (ast1, rest1) = subparser.call(input);
    match rest1 {
        [head, rest2 @ ..] if head == op_symbol => {
            let op_update_clone = op_update.clone();
            let new_sof_fun = |ast| op_update_clone.call(&|ast1| sof.call(ast1), ast1.clone(), ast);
            let new_sof: SofList<AST> = SofList { fun: &new_sof_fun };
            parse_general_list(op_symbol, op_update, new_sof, subparser, rest2)
        }
        _ => (sof.call(ast1), rest1),
    }
}

pub fn parse_list<'a, AST: Clone>(
    op_symbol: &str,
    subparser: Subparser<AST>,
    input: &'a [String],
) -> PartialParseListResult<'a, AST> {
    let op_update = OpUpdateList {
        fun: &|f, ast1, ast2| -> Vec<AST> {
            let mut v = f(ast1);
            v.push(ast2);
            v
        },
    };
    let sof = SofList {
        fun: &|ast: AST| -> Vec<AST> { vec![ast] },
    };
    parse_general_list(op_symbol, op_update, sof, subparser, input)
}

pub fn parse_bracketed<'a, AST: Clone + Debug>(
    subparser: Subparser<AST>,
    input: &'a [String],
) -> PartialParseResult<'a, AST> {
    debug!("parse_bracketed called with input {:?}", input);
    let (ast, rest) = subparser.call(input);

    match rest {
        [head, tail @ ..] if head == ")" => (ast, tail),
        _ => {
            panic!("Closing bracket expected. Found {:?}", rest);
        }
    }
}

pub fn parse_bracketed_list<'a, AST: Clone + Debug>(
    subparser: ListSubparser<AST>,
    input: &'a [String],
) -> PartialParseListResult<'a, AST> {
    debug!("parse_bracketed_list called with input {:?}", input);
    if let [head, rest @ ..] = input {
        if head == ")" {
            return (vec![], rest);
        }
    }

    let (ast, rest) = subparser.call(input);

    match rest {
        [head, tail @ ..] if head == ")" => (ast, tail),
        _ => {
            panic!("Closing bracket expected. Found {:?}", rest);
        }
    }
}

pub fn generic_parser<AST>(inner: fn(&[String]) -> (AST, &[String]), input: &str) -> AST {
    // This is Harrison's `make_parser`.
    let lexed = lex(input);
    let (expr, rest) = inner(&lexed[..]);
    if rest.len() != 0 {
        panic!("Unparsed input {:?}", rest);
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
