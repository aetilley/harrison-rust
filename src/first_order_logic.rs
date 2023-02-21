// ### First
// Order Logic ###
// AST specific parsing/printing functions for first-order (aka predicate) logic.

use std::collections::{BTreeSet, HashMap, HashSet};
use std::fmt::Debug;
use std::hash::Hash;
use std::io::Write;
// use std::rc::Rc;

use crate::formula::{close_box, open_box, parse_formula, print_break, write, Formula, Valuation};
use crate::parse::{
    generic_parser, parse_bracketed, parse_bracketed_list, parse_left_infix, parse_list,
    parse_right_infix, ErrInner, ListSubparser, PartialParseResult, Subparser,
    SubparserFuncListType, SubparserFuncType,
};
use crate::token::{is_const_name, INFIX_RELATION_SYMBOLS};

use log::debug;

// Term
#[derive(Debug, PartialEq, Clone, Hash, Eq, PartialOrd, Ord)]
pub enum Term {
    Var(String),
    Fun(String, Vec<Term>),
}

impl Term {
    fn var(name: &str) -> Term {
        Term::Var(String::from(name))
    }

    fn fun(name: &str, terms: &[Term]) -> Term {
        Term::Fun(String::from(name), terms.to_owned())
    }

    fn constant(name: &str) -> Term {
        Term::fun(name, &[])
    }

    #[allow(clippy::should_implement_trait)]
    pub fn add(t1: &Term, t2: &Term) -> Term {
        Term::Fun(String::from("+"), vec![t1.to_owned(), t2.to_owned()])
    }

    pub fn unary_minus(t: &Term) -> Term {
        Term::Fun(String::from("-"), vec![t.to_owned()])
    }

    #[allow(clippy::should_implement_trait)]
    pub fn sub(t1: &Term, t2: &Term) -> Term {
        Term::Fun(String::from("-"), vec![t1.to_owned(), t2.to_owned()])
    }

    #[allow(clippy::should_implement_trait)]
    pub fn mul(t1: &Term, t2: &Term) -> Term {
        Term::Fun(String::from("*"), vec![t1.to_owned(), t2.to_owned()])
    }

    #[allow(clippy::should_implement_trait)]
    pub fn div(t1: &Term, t2: &Term) -> Term {
        Term::Fun(String::from("/"), vec![t1.to_owned(), t2.to_owned()])
    }

    pub fn exp(t1: &Term, t2: &Term) -> Term {
        Term::Fun(String::from("^"), vec![t1.to_owned(), t2.to_owned()])
    }
    // The inclusion of infix list constructor is a bit
    // surprising and seems to imply that domains will often
    // be closed under cartesian products.
    pub fn cons(t1: &Term, t2: &Term) -> Term {
        Term::Fun(String::from("::"), vec![t1.to_owned(), t2.to_owned()])
    }
}

#[cfg(test)]
mod term_basic_tests {

    use super::*;

    #[test]
    fn test_term_eq() {
        let t1 = Term::var("a");
        let t2 = Term::var("b");
        let t3 = Term::var("b");
        let t4 = Term::fun("c", &[Term::var("f"), Term::fun("a", &[Term::var("d")])]);
        let t5 = Term::fun("c", &[Term::var("f"), Term::fun("a", &[Term::var("d")])]);
        let t6 = Term::fun("c", &[Term::var("f"), Term::fun("a", &[Term::var("e")])]);

        assert_ne!(t1, t2);
        assert_eq!(t2, t3);
        assert_eq!(t4, t5);
        assert_ne!(t5, t6);
    }
}

// TERM PARSING
impl Term {
    fn parse_atomic_term<'a>(
        variables: &[String],
        input: &'a [String],
    ) -> PartialParseResult<'a, Term> {
        debug!(
            "parse_atomic_term called on variables {:?}, input {:?}",
            variables, input
        );
        let minus = "-";
        match input {
            [] => panic!("Term expected."),
            [head, rest @ ..] if head == "(" => parse_bracketed(
                Subparser {
                    fun: &|input| Term::parse_term(variables, input),
                },
                rest,
            ),
            [f, rest @ ..] if f == minus => {
                let (term, newrest) = Term::parse_atomic_term(variables, rest);
                (Term::Fun(String::from(minus), vec![term]), newrest)
            }
            [f, x, rest @ ..] if x == "(" => {
                let term_subparser: SubparserFuncType<Term> =
                    &|input| Term::parse_term(variables, input);
                let list_subparser: SubparserFuncListType<Term> = &|input| {
                    parse_list(
                        ",",
                        Subparser {
                            fun: term_subparser,
                        },
                        input,
                    )
                };
                let (terms, newrest) = parse_bracketed_list(
                    ListSubparser {
                        fun: list_subparser,
                    },
                    rest,
                );
                (Term::Fun(f.clone(), terms), newrest)
            }
            [a, rest @ ..] => {
                if is_const_name(a) && !variables.contains(a) {
                    (Term::Fun(a.clone(), vec![]), rest)
                } else {
                    (Term::Var(a.clone()), rest)
                }
            }
        }
    }

    fn parse_term<'a>(variables: &[String], input: &'a [String]) -> PartialParseResult<'a, Term> {
        debug!(
            "parse_term called on variables {:?}, input {:?}",
            variables, input
        );
        let atomic_subparser: SubparserFuncType<Term> =
            &|input| Term::parse_atomic_term(variables, input);
        let exp_subparser: SubparserFuncType<Term> = &|input| {
            parse_left_infix(
                "^",
                Term::exp,
                Subparser {
                    fun: atomic_subparser,
                },
                input,
            )
        };
        let div_subparser: SubparserFuncType<Term> =
            &|input| parse_left_infix("/", Term::div, Subparser { fun: exp_subparser }, input);
        let mul_subparser: SubparserFuncType<Term> =
            &|input| parse_right_infix("*", Term::mul, Subparser { fun: div_subparser }, input);
        let sub_subparser: SubparserFuncType<Term> =
            &|input| parse_left_infix("-", Term::sub, Subparser { fun: mul_subparser }, input);
        let add_subparser: SubparserFuncType<Term> =
            &|input| parse_right_infix("+", Term::add, Subparser { fun: sub_subparser }, input);
        let cons_subparser: SubparserFuncType<Term> =
            &|input| parse_right_infix("::", Term::cons, Subparser { fun: add_subparser }, input);
        let parser = cons_subparser;
        parser(input)
    }

    fn parse_term_inner(input: &[String]) -> PartialParseResult<'_, Term> {
        Term::parse_term(&[], input)
    }

    pub fn parset(input: &str) -> Term {
        generic_parser(Term::parse_term_inner, input)
    }
}

#[cfg(test)]
mod term_parse_tests {

    use super::*;
    use crate::utils::slice_to_vec_of_owned;

    #[test]
    fn test_parse_term_simple_1() {
        let input: Vec<String> = slice_to_vec_of_owned(&["(", "13", "+", "x", ")", "/", "A"]);

        let result: PartialParseResult<Term> = Term::parse_term(&[], &input);

        let desired_rest: &[String] = &[];
        let desired = (
            Term::div(
                &Term::add(&Term::constant("13"), &Term::var("x")),
                &Term::var("A"),
            ),
            desired_rest,
        );
        assert_eq!(result, desired);
    }

    #[test]
    fn test_parse_term_simple_2() {
        let input: Vec<String> = slice_to_vec_of_owned(&["apples", "*", "-", "oranges", "-", "42"]);

        let result: PartialParseResult<Term> = Term::parse_term(&[], &input);

        let desired_rest: &[String] = &[];
        let desired = (
            Term::sub(
                &Term::mul(
                    &Term::var("apples"),
                    &Term::unary_minus(&Term::var("oranges")),
                ),
                &Term::constant("42"),
            ),
            desired_rest,
        );
        assert_eq!(result, desired);
    }

    #[test]
    fn test_parse_term_simple_3() {
        let input: Vec<String> = slice_to_vec_of_owned(&[
            "F", "(", "V", ",", "apples", "::", "oranges", "::", "42", ",", "19", ")",
        ]);

        let result: PartialParseResult<Term> = Term::parse_term(&[], &input);

        let desired_rest: &[String] = &[];
        let desired = (
            Term::fun(
                "F",
                &[
                    Term::var("V"),
                    Term::fun(
                        "::",
                        &[
                            Term::var("apples"),
                            Term::fun("::", &[Term::var("oranges"), Term::constant("42")]),
                        ],
                    ),
                    Term::constant("19"),
                ],
            ),
            desired_rest,
        );
        assert_eq!(result, desired);
    }

    #[test]
    fn test_parset_0() {
        let result = Term::parset("foo(X, the_meaning(), Z)");
        let desired = Term::fun(
            "foo",
            &[
                Term::var("X"),
                Term::fun("the_meaning", &[]),
                Term::var("Z"),
            ],
        );
        assert_eq!(result, desired);
    }

    fn test_parset_1() {
        let result = Term::parset("bar(B, baz(C))");
        let desired = Term::fun(
            "bar",
            &[Term::var("B"), Term::fun("baz", &[Term::var("C")])],
        );
        assert_eq!(result, desired);
    }
}

// TERM PRINTING
impl Term {
    fn print_term<W: Write>(dest: &mut W, prec: u32, term: &Term) {
        match term {
            Term::Var(x) => {
                write(dest, x);
            }
            Term::Fun(op, args) if op == "^" && args.len() == 2 => {
                Term::print_infix_term(dest, true, prec, 24, "^", &args[0], &args[1])
            }
            Term::Fun(op, args) if op == "/" && args.len() == 2 => {
                Term::print_infix_term(dest, true, prec, 22, " / ", &args[0], &args[1])
            }
            Term::Fun(op, args) if op == "*" && args.len() == 2 => {
                Term::print_infix_term(dest, false, prec, 20, " * ", &args[0], &args[1])
            }
            Term::Fun(op, args) if op == "-" && args.len() == 2 => {
                Term::print_infix_term(dest, true, prec, 18, " - ", &args[0], &args[1])
            }
            Term::Fun(op, args) if op == "+" && args.len() == 2 => {
                Term::print_infix_term(dest, false, prec, 16, " + ", &args[0], &args[1])
            }
            Term::Fun(op, args) if op == "::" && args.len() == 2 => {
                Term::print_infix_term(dest, false, prec, 14, "::", &args[0], &args[1])
            }
            Term::Fun(f, args) => Term::print_fargs(dest, f, args),
        }
    }

    fn print_fargs<W: Write>(dest: &mut W, f: &str, args: &[Term]) {
        // Print a prefix predicate/function application e.g. R(x, y, ...), or f(u, v, ...)
        write(dest, f);
        match &args {
            [] => {}
            // Dont' print parens for constants and propositions
            [head, rest @ ..] => {
                write(dest, "(");
                open_box(0);
                Term::print_term(dest, 0, head);
                for term in rest {
                    write(dest, ",");
                    print_break(dest, 0, 0);
                    Term::print_term(dest, 0, term);
                }
                close_box();
                write(dest, ")");
            }
        }
    }

    fn print_infix_term<W: Write>(
        dest: &mut W,
        is_left: bool,
        old_prec: u32,
        new_prec: u32,
        symbol: &str,
        term1: &Term,
        term2: &Term,
    ) {
        if old_prec > new_prec {
            write(dest, "(");
            open_box(0);
        }
        Term::print_term(dest, if is_left { new_prec } else { new_prec + 1 }, term1);
        // print_break(0,0)
        write(dest, symbol);
        // print_break(
        //     dest,
        //     if symbol.chars().nth(0).unwrap() == ' ' {
        //         1
        //     } else {
        //         0
        //     },
        //     0,
        // );
        Term::print_term(dest, if is_left { new_prec + 1 } else { new_prec }, term2);
        if old_prec > new_prec {
            write(dest, ")");
            open_box(0);
        }
    }

    fn pprint<W: Write>(&self, dest: &mut W) {
        open_box(0);
        write(dest, "<<|");
        open_box(0);
        Term::print_term(dest, 0, self);
        close_box();
        write(dest, "|>>");
        close_box();
    }
}

#[cfg(test)]
mod term_print_tests {

    use super::*;

    #[test]
    fn test_print_term_simple_1() {
        let term = Term::div(
            &Term::add(&Term::constant("13"), &Term::var("x")),
            &Term::var("A"),
        );

        let mut output = Vec::new();

        term.pprint(&mut output);
        let output = String::from_utf8(output).expect("Not UTF-8");

        let desired = "<<|(13 + x) / A|>>";

        assert_eq!(output, desired);
    }

    #[test]
    fn test_print_term_simple_2() {
        let term = Term::sub(
            &Term::mul(
                &Term::var("apples"),
                &Term::unary_minus(&Term::var("oranges")),
            ),
            &Term::constant("42"),
        );
        let mut output = Vec::new();

        term.pprint(&mut output);
        let output = String::from_utf8(output).expect("Not UTF-8");
        let desired = "<<|apples * -(oranges) - 42|>>";
        assert_eq!(output, desired);
    }

    #[test]
    fn test_print_term_simple_3() {
        let term = Term::fun(
            "F",
            &[
                Term::var("V"),
                Term::fun(
                    "::",
                    &[
                        Term::var("apples"),
                        Term::fun("::", &[Term::var("oranges"), Term::constant("42")]),
                    ],
                ),
                Term::constant("19"),
            ],
        );
        let mut output = Vec::new();

        term.pprint(&mut output);
        let output = String::from_utf8(output).expect("Not UTF-8");
        let desired = "<<|F(V, apples::oranges::42, 19)|>>";
        assert_eq!(output, desired);
    }
}

// A Relation / n-ary Predicate
#[derive(Debug, PartialEq, Clone, Hash, Eq, PartialOrd, Ord)]
pub struct Pred {
    name: String,
    terms: Vec<Term>,
}

impl Pred {
    pub fn new(name: &str, terms: &[Term]) -> Pred {
        // Convenience constructor for `Pred`s.
        Pred {
            name: String::from(name),
            terms: terms.to_owned(),
        }
    }

    fn print_pred<W: Write>(dest: &mut W, _prec: u32, Pred { name, terms }: &Pred) {
        if INFIX_RELATION_SYMBOLS.contains(&name.as_str()) && terms.len() == 2 {
            Term::print_infix_term(
                dest,
                false,
                12,
                12,
                &format!(" {name} "),
                &terms[0],
                &terms[1],
            );
        } else {
            Term::print_fargs(dest, name, terms);
        }
    }
}

#[cfg(test)]
mod pred_print_tests {

    use super::*;

    #[test]
    fn print_pred_test_prefix() {
        let pred = Pred::new(
            "R",
            &[
                Term::var("V"),
                Term::fun(
                    "::",
                    &[
                        Term::var("apples"),
                        Term::fun("::", &[Term::var("oranges"), Term::constant("42")]),
                    ],
                ),
                Term::constant("19"),
            ],
        );
        let mut output = Vec::new();
        Pred::print_pred(&mut output, 0, &pred);
        let output = String::from_utf8(output).expect("Not UTF-8");
        let desired = "R(V, apples::oranges::42, 19)";
        assert_eq!(output, desired);
    }

    #[test]
    fn print_pred_test_infix() {
        let pred = Pred::new(
            "<=",
            &[
                Term::fun(
                    "::",
                    &[
                        Term::var("apples"),
                        Term::fun("::", &[Term::var("oranges"), Term::constant("42")]),
                    ],
                ),
                Term::constant("19"),
            ],
        );
        let mut output = Vec::new();
        Pred::print_pred(&mut output, 0, &pred);
        let output = String::from_utf8(output).expect("Not UTF-8");
        let desired = "apples::oranges::42 <= 19";
        assert_eq!(output, desired);
    }
}

// Formula Parsing

impl Formula<Pred> {
    fn _infix_parser<'a>(
        variables: &[String],
        input: &'a [String],
    ) -> Result<PartialParseResult<'a, Formula<Pred>>, ErrInner> {
        debug!(
            "(pred) _infix_parser called on variables {:?}, input {:?}",
            variables, input
        );
        let (term1, rest) = Term::parse_term(variables, input);
        if rest.is_empty() || !INFIX_RELATION_SYMBOLS.contains(&rest[0].as_str()) {
            return Err("Not infix.");
        }
        let (term2, newrest) = Term::parse_term(variables, &rest[1..]);
        Ok((
            Formula::atom(&Pred::new(&rest[0], &[term1, term2])),
            newrest,
        ))
    }

    fn _atom_parser<'a>(
        variables: &[String],
        input: &'a [String],
    ) -> PartialParseResult<'a, Formula<Pred>> {
        debug!(
            "(pred) _atom_parser called on variables {:?}, input {:?}",
            variables, input
        );
        if let Ok(parse_result) = Formula::_infix_parser(variables, input) {
            return parse_result;
        };
        // Else not infix atom.
        match input {
            [p, x, rest @ ..] if x == "(" => {
                let term_subparser: SubparserFuncType<Term> =
                    &|input| Term::parse_term(variables, input);
                let list_subparser: SubparserFuncListType<Term> = &|input| {
                    parse_list(
                        ",",
                        Subparser {
                            fun: term_subparser,
                        },
                        input,
                    )
                };
                let (terms, newrest) = parse_bracketed_list(
                    ListSubparser {
                        fun: list_subparser,
                    },
                    rest,
                );
                (Formula::atom(&Pred::new(p, &terms)), newrest)
            }
            [p, rest @ ..] if p != "(" => (Formula::atom(&Pred::new(p, &[])), rest),
            _ => panic!("parse_atom"),
        }
    }

    fn _parse_pred_formula_inner(input: &[String]) -> PartialParseResult<'_, Formula<Pred>> {
        parse_formula(
            Formula::_infix_parser,
            Formula::_atom_parser,
            &[], // Bound Variables
            input,
        )
    }

    pub fn parse(input: &str) -> Formula<Pred> {
        generic_parser(Formula::_parse_pred_formula_inner, input)
    }
}

#[cfg(test)]
mod parse_pred_formula_tests {

    use super::*;

    #[test]
    fn test_parse_pred_basics() {
        let result = Formula::<Pred>::parse("bar(X, Z)");
        let pred = Pred::new("bar", &[Term::var("X"), Term::var("Z")]);
        let desired = Formula::atom(&pred);
        assert_eq!(result, desired);
    }

    #[test]
    fn test_parse_pred_formula_variables() {
        let input = "F(x) /\\ G(d(y)) ==> p(13, w)";

        let result = Formula::<Pred>::parse(input);

        let desired = Formula::imp(
            &Formula::and(
                &Formula::atom(&Pred::new("F", &[Term::var("x")])),
                &Formula::atom(&Pred::new("G", &[Term::fun("d", &[Term::var("y")])])),
            ),
            &Formula::atom(&Pred::new("p", &[Term::constant("13"), Term::var("w")])),
        );
        assert_eq!(result, desired);
    }

    #[test]
    fn test_parse_pred_formula_variables_2() {
        let input = "(R(Y, X) /\\ false)";

        let result = Formula::<Pred>::parse(input);

        let desired = Formula::and(
            &Formula::atom(&Pred::new("R", &[Term::var("Y"), Term::var("X")])),
            &Formula::False,
        );
        assert_eq!(result, desired);
    }

    #[test]
    fn test_parse_pred_formula_variables_3() {
        let input = "(Y = X)";
        let result = Formula::<Pred>::parse(input);
        let desired = Formula::atom(&Pred::new("=", &[Term::var("Y"), Term::var("X")]));
        assert_eq!(result, desired);
    }

    #[test]
    fn test_parse_pred_formula_variables_4() {
        let _ = env_logger::builder().is_test(true).try_init();
        let input = "Y = X \\/ false";

        let result = Formula::<Pred>::parse(input);

        let desired = Formula::or(
            &Formula::atom(&Pred::new("=", &[Term::var("Y"), Term::var("X")])),
            &Formula::False,
        );
        assert_eq!(result, desired);
    }

    #[test]
    fn test_parse_pred_formula_variables_5() {
        let _ = env_logger::builder().is_test(true).try_init();
        let input = "(Y = X \\/ false)";

        let result = Formula::<Pred>::parse(input);

        let desired = Formula::or(
            &Formula::atom(&Pred::new("=", &[Term::var("Y"), Term::var("X")])),
            &Formula::False,
        );
        assert_eq!(result, desired);
    }

    #[test]
    fn test_parse_pred_formula_quantifiers() {
        // Remember that quantifiers bind looser than any connective.
        let input = "forall y w. F(RED) /\\ exists RED BLUE. G(d(y))";

        let result = Formula::<Pred>::parse(input);

        let desired = Formula::forall(
            "y",
            &Formula::forall(
                "w",
                &Formula::and(
                    &Formula::atom(&Pred::new("F", &[Term::var("RED")])),
                    &Formula::exists(
                        "RED",
                        &Formula::exists(
                            "BLUE",
                            &Formula::atom(&Pred::new("G", &[Term::fun("d", &[Term::var("y")])])),
                        ),
                    ),
                ),
            ),
        );

        assert_eq!(result, desired);
    }

    #[test]
    fn test_parse_ea_quantified() {
        let result = Formula::<Pred>::parse("exists X. forall Y. bar(X, Y)");
        let desired = Formula::exists(
            "X",
            &Formula::forall(
                "Y",
                &Formula::atom(&Pred::new("bar", &[Term::var("X"), Term::var("Y")])),
            ),
        );

        assert_eq!(result, desired);
    }

    #[test]
    fn test_simple_infix() {
        let input = "~(x = y)";
        let result = Formula::<Pred>::parse(input);
        let desired = Formula::not(&Formula::atom(&Pred::new(
            "=",
            &[Term::var("x"), Term::var("y")],
        )));
        assert_eq!(result, desired);
    }

    #[test]
    fn test_more_quantifiers() {
        let input = "forall x. ~(x = 0) ==> exists y. x * y = 1";

        let desired = Formula::forall(
            "x",
            &Formula::imp(
                &Formula::not(&Formula::atom(&Pred::new(
                    "=",
                    &[Term::var("x"), Term::fun("0", &[])],
                ))),
                &Formula::exists(
                    "y",
                    &Formula::atom(&Pred::new(
                        "=",
                        &[
                            Term::fun("*", &[Term::var("x"), Term::var("y")]),
                            Term::fun("1", &[]),
                        ],
                    )),
                ),
            ),
        );

        let result = Formula::<Pred>::parse(input);
        assert_eq!(result, desired);
    }

    #[test]
    fn test_more_quantifiers_2() {
        let result = Formula::<Pred>::parse("exists X. exists Y. foo(X, Y, Z) = W");
        let desired = Formula::exists(
            "X",
            &Formula::exists(
                "Y",
                &Formula::atom(&Pred::new(
                    "=",
                    &[
                        Term::fun("foo", &[Term::var("X"), Term::var("Y"), Term::var("Z")]),
                        Term::var("W"),
                    ],
                )),
            ),
        );
        assert_eq!(result, desired);
    }
}

// Formula Printing
impl Formula<Pred> {
    pub fn pprint<W: Write>(&self, dest: &mut W) {
        let pfn: fn(&mut W, u32, &Pred) -> () = Pred::print_pred;
        self.pprint_general(dest, &pfn);
        write(dest, "\n");
    }
}

#[cfg(test)]
mod test_print_pred_formula {
    use super::*;

    #[test]
    fn test_print_pred_formula_variables() {
        let input = Formula::imp(
            &Formula::and(
                &Formula::atom(&Pred::new("F", &[Term::var("x")])),
                &Formula::atom(&Pred::new("G", &[Term::fun("d", &[Term::var("y")])])),
            ),
            &Formula::atom(&Pred::new("p", &[Term::constant("13"), Term::var("w")])),
        );

        let mut output = Vec::new();
        input.pprint(&mut output);
        let output = String::from_utf8(output).expect("Not UTF-8");
        let desired = "<<F(x) /\\ G(d(y)) ==> p(13, w)>>\n";
        assert_eq!(output, desired);
    }

    #[test]
    fn test_print_pred_formula_quantifiers() {
        let input = Formula::forall(
            "y",
            &Formula::forall(
                "w",
                &Formula::and(
                    &Formula::atom(&Pred::new("F", &[Term::var("RED")])),
                    &Formula::exists(
                        "RED",
                        &Formula::exists(
                            "BLUE",
                            &Formula::atom(&Pred::new("G", &[Term::fun("d", &[Term::var("y")])])),
                        ),
                    ),
                ),
            ),
        );
        let mut output = Vec::new();
        input.pprint(&mut output);
        let output = String::from_utf8(output).expect("Not UTF-8");
        let desired = "<<forall y w. F(RED) /\\ (exists RED BLUE. G(d(y)))>>\n";
        assert_eq!(output, desired);
    }
}

#[derive(Clone)]
// Eval
pub struct Language {
    pub func: HashMap<String, usize>,
    pub rel: HashMap<String, usize>,
}

type FuncType<DomainType> = dyn Fn(&[DomainType]) -> DomainType;
type RelType<DomainType> = dyn Fn(&[DomainType]) -> bool;

pub struct Interpretation<DomainType: Hash + Clone + Eq + Debug + 'static> {
    // Need a lifetime parameter due to the trait bounds in func/rel.
    lang: Language,
    domain: HashSet<DomainType>,
    func: HashMap<String, Box<FuncType<DomainType>>>,
    rel: HashMap<String, Box<RelType<DomainType>>>,
}

impl<DomainType: Hash + Clone + Eq + Debug> Interpretation<DomainType> {
    pub fn new(
        lang: &Language,
        domain: HashSet<DomainType>,
        funcs: HashMap<String, Box<FuncType<DomainType>>>,
        rels: HashMap<String, Box<RelType<DomainType>>>,
    ) -> Interpretation<DomainType> {
        // Notice:  Takes ownership of some parameters.
        // Wrap each function in a check for the correct arity.
        // Note that this does not check, e.g. that the domain is closed under
        // operations in funcs.
        let mut safe_funcs = HashMap::<String, Box<FuncType<DomainType>>>::new();
        for (name, f) in funcs {
            let name_clone = name.clone();
            let domain_clone = domain.clone();
            let arity = lang.func[&name];
            let safe_f = move |input: &[DomainType]| -> DomainType {
                assert_eq!(
                    input.len(),
                    arity,
                    "Function {} has arity {} but was passed {} arguments",
                    name_clone,
                    arity,
                    input.len()
                );
                for arg in input {
                    assert!(
                        domain_clone.contains(arg),
                        "In evaluating function {}, Value {:?} is not in domain",
                        name_clone,
                        &arg
                    );
                }
                f(input)
            };
            safe_funcs.insert(name.clone(), Box::new(safe_f));
        }
        let mut safe_rels = HashMap::<String, Box<RelType<DomainType>>>::new();
        for (name, r) in rels {
            let name_clone = name.clone();
            let domain_clone = domain.clone();
            let arity = lang.rel[&name];
            let safe_r = move |input: &[DomainType]| -> bool {
                assert_eq!(
                    input.len(),
                    arity,
                    "Relation {} has arity {} but was passed {} arguments",
                    name_clone,
                    arity,
                    input.len()
                );
                for arg in input {
                    assert!(
                        domain_clone.contains(arg),
                        "In evaluating relation {}
                        Value {:?} is not in domain",
                        name_clone,
                        &arg
                    );
                }
                r(input)
            };
            safe_rels.insert(name.clone(), Box::new(safe_r));
        }

        Interpretation {
            lang: lang.clone(),
            domain,
            func: safe_funcs,
            rel: safe_rels,
        }
    }
}

mod test_utils {

    use super::*;

    pub type DomainType = u32;

    pub fn get_test_interpretation() -> Interpretation<DomainType> {
        fn _foo(input: &[DomainType]) -> DomainType {
            std::cmp::min(input[0] + input[1] + input[2], 60)
        }

        fn _bar(input: &[DomainType]) -> bool {
            (input[0] + input[1]) % 2 == 0
        }

        fn _equals(input: &[DomainType]) -> bool {
            input[0] == input[1]
        }

        fn _the_meaning(_input: &[DomainType]) -> DomainType {
            42
        }

        let lang: Language = Language {
            func: HashMap::from([(String::from("foo"), 3), (String::from("the_meaning"), 0)]),
            rel: HashMap::from([(String::from("bar"), 2), (String::from("="), 2)]),
        };

        let domain: HashSet<DomainType> = (1..=60).collect();
        let funcs: HashMap<String, Box<FuncType<DomainType>>> = HashMap::from([
            (
                String::from("foo"),
                Box::new(_foo) as Box<FuncType<DomainType>>,
            ),
            (
                String::from("the_meaning"),
                Box::new(_the_meaning) as Box<FuncType<DomainType>>,
            ),
        ]);
        let rels: HashMap<String, Box<RelType<DomainType>>> = HashMap::from([
            (
                String::from("bar"),
                Box::new(_bar) as Box<RelType<DomainType>>,
            ),
            (
                String::from("="),
                Box::new(_equals) as Box<RelType<DomainType>>,
            ),
        ]);

        Interpretation::new(&lang, domain, funcs, rels)
    }
}

#[cfg(test)]
mod interpretation_tests {

    use super::*;

    #[test]
    fn test_new_basic() {
        let m = test_utils::get_test_interpretation();
        assert_eq!(m.func["foo"](&[1, 3, 3]), 7);
        assert!(m.rel["bar"](&[3, 21]));
    }

    #[test]
    #[should_panic]
    fn test_new_panic_1() {
        // Should panic since foo is ternary.
        let m = test_utils::get_test_interpretation();
        m.func["foo"](&[1, 3]);
    }

    #[test]
    #[should_panic]
    fn test_new_panic_2() {
        // Should panic since foo is ternary.
        let m = test_utils::get_test_interpretation();
        m.func["foo"](&[1, 3, 3, 21]);
    }

    #[test]
    #[should_panic]
    fn test_new_panic_3() {
        // Should panic since 61 is not in the domain.
        let m = test_utils::get_test_interpretation();
        m.func["foo"](&[1, 61, 4]);
    }
}

// Partial Map from variable names to domain elements
// implemented as linked frames to allow for less
// copying.
pub struct FOValuation<'a, DomainType: Hash + Clone + Eq + Debug> {
    // Any new assignments for this frame
    frame: HashMap<String, DomainType>,
    // Pointer to the next frame
    next: Option<&'a FOValuation<'a, DomainType>>,
}

impl<'a, DomainType: Hash + Clone + Eq + Debug> FOValuation<'a, DomainType> {
    // Maybe implement this later.
    #[allow(clippy::new_without_default)]
    pub fn new() -> FOValuation<'a, DomainType> {
        FOValuation {
            frame: HashMap::new(),
            next: None,
        }
    }

    pub fn from(data: &HashMap<String, DomainType>) -> FOValuation<'a, DomainType> {
        // Todo, implement coming from general iter.
        FOValuation {
            frame: data.clone(),
            next: None,
        }
    }

    fn set(&self, name: String, val: DomainType) -> FOValuation<'_, DomainType> {
        let frame = HashMap::from([(name, val)]);
        let next = Some(self);
        FOValuation { frame, next }
    }

    fn get(&self, name: &str) -> Option<DomainType> {
        // First try local frame, and failing that, defer
        // to `next` FOValuation (if any).
        if let Some(value) = self.frame.get(name) {
            let cloned: DomainType = value.clone();
            return Some(cloned);
        }
        match self.next {
            Some(valuation) => valuation.get(name),
            None => None,
        }
    }
}

// ### Term Evaluation ###
impl Term {
    pub fn eval<DomainType: Hash + Clone + Eq + Debug>(
        &self,
        m: &Interpretation<DomainType>,
        v: &FOValuation<DomainType>,
    ) -> DomainType {
        match self {
            Term::Var(name) => match v.get(&name.to_string()) {
                Some(val) => val,
                None => panic!("FOValuation not defined on variable {name:?}."),
            },
            Term::Fun(name, args) => {
                let func_box: &FuncType<DomainType> = &m.func[&name.to_string()];
                let vals: Vec<DomainType> = args.iter().map(|term| term.eval(m, v)).collect();
                (*func_box)(&vals)
            }
        }
    }
}

#[cfg(test)]
mod test_term_eval {
    use super::*;

    #[test]
    fn test_term_eval_simple() {
        let m = test_utils::get_test_interpretation();

        let map = HashMap::from([
            ("X".to_string(), 14),
            ("Y".to_string(), 1),
            ("Z".to_string(), 2),
        ]);
        let v = FOValuation::from(&map);

        let var_x = Term::var("X");
        let var_z = Term::var("Z");

        assert_eq!(var_x.eval(&m, &v), 14);
        assert_eq!(var_z.eval(&m, &v), 2);

        let t = Term::parset("foo(X, the_meaning(), Z)");
        assert_eq!(t.eval(&m, &v), 58);
    }
}

impl Pred {
    pub fn eval<DomainType: Hash + Clone + Eq + Debug>(
        &self,
        m: &Interpretation<DomainType>,
        v: &FOValuation<DomainType>,
    ) -> bool {
        let rel_box: &RelType<DomainType> = &m.rel[&self.name];
        let vals: Vec<DomainType> = self.terms.iter().map(|term| term.eval(m, v)).collect();
        (*rel_box)(&vals)
    }
}

#[cfg(test)]
mod test_pred_eval {

    use super::*;

    #[test]
    fn test_pred_eval_simple() {
        let m = test_utils::get_test_interpretation();

        let map = HashMap::from([
            ("X".to_string(), 14),
            ("Y".to_string(), 1),
            ("Z".to_string(), 2),
            ("W".to_string(), 14),
        ]);
        let v = FOValuation::from(&map);

        let t = Term::parset("foo(X, the_meaning(), Z)");

        let pred_1 = Pred::new("bar", &[t.clone(), Term::var("Y")]);
        assert!(!pred_1.eval(&m, &v)); // 58 + 1 % 2 = 0 is false
        let pred_2 = Pred::new("bar", &[t, Term::var("X")]);
        assert!(pred_2.eval(&m, &v)); // 58 + 14 % 2 == 0 is true
        let pred_3 = Pred::new("=", &[Term::var("Y"), Term::var("X")]);
        assert!(!pred_3.eval(&m, &v)); // 1 == 14 is false
        let pred_4 = Pred::new("=", &[Term::var("W"), Term::var("X")]);
        assert!(pred_4.eval(&m, &v)); // 14 == 14 is true
    }
}

// ### Formula Evaluation ###
impl Formula<Pred> {
    pub fn eval<DomainType: Hash + Clone + Eq + Debug>(
        &self,
        m: &Interpretation<DomainType>,
        v: &FOValuation<DomainType>,
    ) -> bool {
        let pred_atom_eval = |pred: &Pred| -> bool { pred.eval(m, v) };

        // TODO the clone inside of the for loops of the quantifiers could get expensive.
        // Find a better way. Partial functions like Z3 arrays?

        let forall_eval = |var: &str, subformula: &Formula<Pred>| -> bool {
            for val in &m.domain {
                let v_ext = v.set(var.to_string(), val.clone()); // (var |-> val)v
                if !subformula.eval(m, &v_ext) {
                    return false;
                }
            }
            true
        };

        let exists_eval = |var: &str, subformula: &Formula<Pred>| -> bool {
            for val in &m.domain {
                let v_ext = v.set(var.to_string(), val.clone()); // (var |-> val)v
                if subformula.eval(m, &v_ext) {
                    return true;
                }
            }
            false
        };

        self.eval_core(&pred_atom_eval, &forall_eval, &exists_eval)
    }
}

#[cfg(test)]
mod test_formula_eval {

    use super::*;

    #[test]
    fn test_formula_eval_simple() {
        let m = test_utils::get_test_interpretation();

        let map = HashMap::from([
            ("X".to_string(), 14),
            ("Y".to_string(), 1),
            ("Z".to_string(), 2),
        ]);
        let v = FOValuation::from(&map);

        let formula_1 = Formula::<Pred>::parse("bar(X, Z)");
        assert!(formula_1.eval(&m, &v));
    }

    #[test]
    fn test_formula_eval_quantified_1() {
        let m = test_utils::get_test_interpretation();

        let map = HashMap::from([("Z".to_string(), 2)]);
        let v = FOValuation::from(&map);

        let formula_1 = Formula::<Pred>::parse("exists X. bar(X, Z)");

        assert!(formula_1.eval(&m, &v));
    }

    #[test]
    fn test_formula_eval_quantified_2() {
        let m = test_utils::get_test_interpretation();

        let map = HashMap::from([
            ("U".to_string(), 43),
            ("Z".to_string(), 42),
            ("W".to_string(), 58),
        ]);
        let v = FOValuation::from(&map);

        let formula_1 = Formula::<Pred>::parse("exists X. exists Y. foo(X, Y, Z) = W");

        // A Solution exists.
        assert!(formula_1.eval(&m, &v));

        let formula_2 = Formula::<Pred>::parse("exists X. exists Y. foo(X, Y, Z) = U");
        // No Solution exists in (1..=60)
        assert!(!formula_2.eval(&m, &v));
    }

    #[test]
    fn test_formula_eval_quantified_3() {
        let m = test_utils::get_test_interpretation();
        let v = FOValuation::new();

        let formula_ae = Formula::<Pred>::parse("forall X. exists Y. bar(X, Y)");
        assert!(formula_ae.eval(&m, &v));
        let formula_ea = Formula::<Pred>::parse("exists X. forall Y. bar(X, Y)");
        assert!(!formula_ea.eval(&m, &v));
    }
}

// Term Variables
type Instantiation = HashMap<String, Term>;

impl Term {
    fn get_variables_for_termlist(terms: &[Term]) -> HashSet<String> {
        terms
            .iter()
            .fold(HashSet::new(), |acc, term| &acc | &term.variables())
    }

    fn variables(&self) -> HashSet<String> {
        // Theorem (Harrison 3.1)
        // if `t: Term` and if `v, v': FOValuation` such that
        // for all x in t.variables() we have v(x) == v'(x), then
        // t.eval(M, v) == t.eval(M, v') for any `M: Interpretation`.
        match self {
            Term::Var(name) => HashSet::from([name.clone()]),
            Term::Fun(_name, terms) => Term::get_variables_for_termlist(terms),
        }
    }

    fn functions(&self) -> HashSet<(String, usize)> {
        // Return functions with arities.
        match self {
            Term::Var(_) => HashSet::new(),
            Term::Fun(name, args) => args
                .iter()
                .fold(HashSet::from([(name.clone(), args.len())]), |acc, arg| {
                    &acc | &arg.functions()
                }),
        }
    }

    pub fn subst(&self, inst: &Instantiation) -> Term {
        // Substitute Terms for Vars throughout according to `inst`.
        //
        // Lemma (Harrison 3.5)
        // For any `t: Term`, `inst: Instatiation`, `M: Interpretation`
        // `v: FOValuation`, we have
        // t.subst(inst).eval(M, v) = t.eval(M, {x |-> inst(x).eval(M, v)})
        match self {
            Term::Var(x) => inst.get(x).unwrap_or(&Term::var(x)).clone(),
            Term::Fun(name, args) => {
                let new_args: Vec<Term> = args.iter().map(|term| term.subst(inst)).collect();
                Term::fun(name, &new_args)
            }
        }
    }

    pub fn variant(var: &str, vars: &HashSet<String>) -> String {
        // Add primes ("'") to `var` until the result is not in `vars`.
        if vars.contains(var) {
            let guess = format!("{var}'");
            Term::variant(&guess, vars)
        } else {
            var.to_owned()
        }
    }
}

#[cfg(test)]
mod test_term_variables {

    use crate::utils::{slice_to_set_of_owned, slice_to_vec_of_owned};

    use super::*;

    #[test]
    fn tet_get_variables_for_termlist() {
        let term1 = Term::parset("foo(A)");
        let term2 = Term::parset("B");
        let term3 = Term::parset("bar(B, baz(C))");
        let input = vec![term1, term2, term3];

        let result = Term::get_variables_for_termlist(&input);
        assert_eq!(result, slice_to_set_of_owned(&["A", "B", "C"]),);
    }

    #[test]
    fn test_variables() {
        let input = Term::parset("F1(foo(A), B, bar(B, baz(C)))");
        let result = input.variables();
        assert_eq!(result, slice_to_set_of_owned(&["A", "B", "C"]),);
    }

    #[test]
    fn test_functions() {
        let input = Term::parset("F1(foo(A), B, bar(13, baz(C)))");
        let result = input.functions();
        let desired_names = slice_to_vec_of_owned(&["F1", "foo", "bar", "baz", "13"]);
        let desired_arities = vec![3, 1, 2, 1, 0];
        let desired: HashSet<(String, usize)> = desired_names
            .into_iter()
            .zip(desired_arities.into_iter())
            .collect();
        assert_eq!(result, desired);
    }

    #[test]
    fn test_subst() {
        let input = Term::parset("F1(foo(A), B, bar(B, baz(C)))");
        let t1 = Term::var("S");
        let t2 = Term::fun("B", &[Term::var("v")]);
        let inst = Instantiation::from([("B".to_string(), t1), ("C".to_string(), t2)]);
        let result = input.subst(&inst);
        let desired = Term::parset("F1(foo(A), S, bar(S, baz(B(v))))");
        assert_eq!(result, desired);
    }

    #[test]
    fn test_variant() {
        let existing: HashSet<String> = slice_to_set_of_owned(&["a", "b", "b'"]);

        let var = "c";
        let result = Term::variant(var, &existing);
        assert_eq!(result, "c");

        let var = "a";
        let result = Term::variant(var, &existing);
        assert_eq!(result, "a'");

        let var = "b";
        let result = Term::variant(var, &existing);
        assert_eq!(result, "b''");
    }
}

impl Pred {
    fn variables(&self) -> HashSet<String> {
        Term::get_variables_for_termlist(&self.terms)
    }

    fn functions(&self) -> HashSet<(String, usize)> {
        self.terms
            .iter()
            .fold(HashSet::new(), |acc, term| &acc | &term.functions())
    }
}

// ### Variables ###
impl Formula<Pred> {
    fn variables(&self) -> HashSet<String> {
        match self {
            Formula::True | Formula::False => HashSet::new(),
            Formula::Atom(pred) => pred.variables(),
            Formula::Not(box p) => p.variables(),
            Formula::And(box p, box q)
            | Formula::Or(box p, box q)
            | Formula::Imp(box p, box q)
            | Formula::Iff(box p, box q) => &p.variables() | &q.variables(),
            Formula::Forall(var, box p) | Formula::Exists(var, box p) => {
                let mut vars = p.variables();
                vars.insert(var.clone());
                vars
            }
        }
    }

    pub fn free_variables(&self) -> HashSet<String> {
        // Theorem (Harrison 3.2)
        // If `p: Formula<Pred>` and if `v, v': FOValuation` such that
        // for all x in p.free_variables()  we have v(x) == v'(x), then
        // p.eval(M, v) == p.eval(M, v') for any `M: Interpretation.
        //
        // Corollary (Harrision 3.3)
        // If `p: Formula<Pred>` and p.free_variables() == {}, then
        // p.eval(M, v) == p.eval(M, v') for any `M: Interpretation`
        // and any `v, v': FOValuation`.
        match self {
            Formula::True | Formula::False => HashSet::new(),
            Formula::Atom(pred) => pred.variables(),
            Formula::Not(box p) => p.free_variables(),
            Formula::And(box p, box q)
            | Formula::Or(box p, box q)
            | Formula::Imp(box p, box q)
            | Formula::Iff(box p, box q) => &p.free_variables() | &q.free_variables(),
            Formula::Forall(var, box p) | Formula::Exists(var, box p) => {
                let mut vars = p.free_variables();
                vars.remove(var);
                vars
            }
        }
    }

    fn functions(&self) -> HashSet<(String, usize)> {
        let combine = |pred: &Pred, agg: HashSet<(String, usize)>| -> HashSet<(String, usize)> {
            &pred.functions() | &agg
        };
        self.over_atoms(&combine, HashSet::new())
    }

    fn generalize(&self) -> Formula<Pred> {
        // The universal closure of `formula`.

        let mut sorted: Vec<String> = self.free_variables().iter().cloned().collect();
        sorted.sort();
        sorted
            .into_iter()
            .fold(self.clone(), |formula, var| Formula::forall(&var, &formula))
    }

    fn _subst_quant(
        inst: &Instantiation,
        quant_const: &QuantConstructor,
        var: &String,
        formula: &Formula<Pred>,
    ) -> Formula<Pred> {
        // Helper function for `subst`.  Does substitution in `formula` according to `inst`
        // and re-attaches the quantifier for `quant_const`, making sure to change the
        // variable of quantification (if necessary) to one not occuring free in the resulting
        // formula (substitution result).
        let mut other_vars = formula.free_variables();
        other_vars.remove(var);
        let mut would_be_captured = false;
        for free_var in other_vars {
            // Try apply?
            let image_free_variables = inst
                .get(&free_var)
                .unwrap_or(&Term::var(&free_var))
                .variables();
            if image_free_variables.contains(var) {
                would_be_captured = true;
                break;
            }
        }
        let new_var = if would_be_captured {
            let mut tmp_inst = inst.clone();
            tmp_inst.remove(var);
            let free_variables = formula.subst(&tmp_inst).free_variables();
            Term::variant(var, &free_variables)
        } else {
            var.clone()
        };

        let mut new_inst = inst.clone();
        new_inst.insert(var.clone(), Term::var(&new_var));
        quant_const(&new_var, &formula.subst(&new_inst))
    }

    pub fn subst(&self, inst: &Instantiation) -> Formula<Pred> {
        // Substitute Terms for Vars throughout according to `inst`, swapping in
        // fresh variables of quantification when necessary to avoid unwanted
        // capture.
        //
        // Theorem (Harrision 3.7)
        // For any `p: Formula<Pred>`, `inst: Instatiation`, `M: Interpretation`
        // `v: FOValuation`, we have
        // p.subst(inst).eval(M, v) = p.eval(M, {x |-> inst(x).eval(M, v)})
        //
        // Corollary (Harrison 3.8)
        // If a formula is valid, then so is any substitution instance.
        match self {
            Formula::False | Formula::True => self.clone(),
            Formula::Atom(Pred { name, terms }) => {
                let new_args: Vec<Term> = terms.iter().map(|term| term.subst(inst)).collect();
                Formula::atom(&Pred::new(name, &new_args))
            }
            Formula::Not(box p) => Formula::not(&p.subst(inst)),
            Formula::And(box p, box q) => Formula::and(&p.subst(inst), &q.subst(inst)),
            Formula::Or(box p, box q) => Formula::or(&p.subst(inst), &q.subst(inst)),
            Formula::Imp(box p, box q) => Formula::imp(&p.subst(inst), &q.subst(inst)),
            Formula::Iff(box p, box q) => Formula::iff(&p.subst(inst), &q.subst(inst)),
            Formula::Forall(x, box p) => Formula::_subst_quant(inst, &Formula::forall, x, p),
            Formula::Exists(x, box p) => Formula::_subst_quant(inst, &Formula::exists, x, p),
        }
    }
}

#[cfg(test)]
mod test_formula_variables {

    use super::*;
    use crate::utils::slice_to_set_of_owned;
    use crate::utils::slice_to_vec_of_owned;

    #[test]
    fn test_formula_variables() {
        let formula = Formula::<Pred>::parse("forall X. X = W ==> exists W. foo(X, W, Z) = U");
        let result_all = formula.variables();
        let desired_all = slice_to_set_of_owned(&["U", "W", "X", "Z"]);
        assert_eq!(result_all, desired_all);
    }

    #[test]
    fn test_formula_free_variables() {
        let formula = Formula::<Pred>::parse("forall X. X = W ==> exists W. foo(X, W, Z) = U");
        let result_free = formula.free_variables();
        let desired_free = slice_to_set_of_owned(&["U", "W", "Z"]);
        assert_eq!(result_free, desired_free);
    }

    #[test]
    fn test_formula_functions() {
        let formula =
            Formula::<Pred>::parse("forall X. f(X) = W ==> exists W. foo(X, bar(13), Z) = U");
        let result = formula.functions();
        let desired_names = slice_to_vec_of_owned(&["f", "foo", "bar", "13"]);
        let desired_arities = vec![1, 3, 1, 0];
        let desired: HashSet<(String, usize)> = desired_names
            .into_iter()
            .zip(desired_arities.into_iter())
            .collect();
        assert_eq!(result, desired);
    }

    #[test]
    fn test_formula_functions_2() {
        let formula_string = "R(F(y, r)) \\/ (exists x. P(f_w(x))) /\\ exists n. forall r. forall y. exists w. M(G(y, w)) \\/ exists z. ~M(F(z, w))";
        let formula = Formula::<Pred>::parse(formula_string);
        let result = formula.functions();
        let desired_names = slice_to_vec_of_owned(&["F", "f_w", "G"]);
        let desired_arities = vec![2, 1, 2];
        let desired: HashSet<(String, usize)> = desired_names
            .into_iter()
            .zip(desired_arities.into_iter())
            .collect();
        assert_eq!(result, desired);
    }

    #[test]
    fn test_generalize() {
        let formula = Formula::<Pred>::parse("forall X. X = W ==> exists W. foo(X, W) = U");
        let result = formula.generalize();
        let desired = Formula::<Pred>::parse("forall W U X. X = W ==> exists W. foo(X, W) = U");
        assert_eq!(result, desired);
    }

    #[test]
    fn test_subst() {
        let formula = Formula::<Pred>::parse("R(foo(X, W, Z), U)");
        let inst = Instantiation::from([
            ("W".to_string(), Term::parset("Z")),
            ("Z".to_string(), Term::parset("U")),
        ]);
        let result = formula.subst(&inst);
        let desired = Formula::<Pred>::parse("R(foo(X, Z, U), U)");
        assert_eq!(result, desired);

        let formula = Formula::<Pred>::parse("forall X. X = W ==> exists W. foo(X, W, Z) = U");
        let inst = Instantiation::from([("W".to_string(), Term::parset("bar(X, R)"))]);
        let result = formula.subst(&inst);
        let desired =
            Formula::<Pred>::parse("forall X'. X' = bar(X, R) ==> exists W. foo(X', W, Z) = U");
        assert_eq!(result, desired);

        let formula = Formula::<Pred>::parse("forall X. X = W ==> exists W. foo(X, W, Z) = U");
        let inst = Instantiation::from([("X".to_string(), Term::parset("W"))]);
        let result = formula.subst(&inst);
        let desired = formula;
        assert_eq!(result, desired);
    }
}

type QuantConstructor = dyn Fn(&str, &Formula<Pred>) -> Formula<Pred>;
type BinopConstructor = dyn Fn(&Formula<Pred>, &Formula<Pred>) -> Formula<Pred>;
// Normal Forms
impl Formula<Pred> {
    fn fo_simplify_step(formula: &Formula<Pred>) -> Formula<Pred> {
        // In addition to core simplifications, removes quantifiers `Qx` in
        // formulas `Qx.p` when quantified formulas `p` do not contain
        // free occurences of `x`.
        match formula {
            Formula::Forall(x, box p) | Formula::Exists(x, box p) => {
                if p.free_variables().contains(x) {
                    formula.clone()
                } else {
                    p.clone()
                }
            }
            _ => Formula::psimplify_step(formula),
        }
    }

    pub fn simplify(self: &Formula<Pred>) -> Formula<Pred> {
        self.simplify_recursive(&Formula::fo_simplify_step)
    }

    fn nnf(&self) -> Formula<Pred> {
        // Negation normal form
        // NOTE:  Harrison actually doesn't simplify first (but makes
        // sure to simplify in the final definition of prenex form.
        self.simplify().raw_nnf()
    }

    fn pull_quantifiers(formula: &Formula<Pred>) -> Formula<Pred> {
        // Assumes that `formula` is of the form `<binop>(p, q)` where `p, q` are
        // already in prenex form.
        // Recursively pulls out all quantifiers leading `p` and `q` to result in
        // a prenex formula.
        match formula {
            Formula::And(box Formula::Forall(x, box p), box Formula::Forall(y, box q)) => {
                Formula::pullq(
                    true,
                    true,
                    formula,
                    &Formula::forall,
                    &Formula::and,
                    x,
                    y,
                    p,
                    q,
                )
            }
            Formula::Or(box Formula::Exists(x, box p), box Formula::Exists(y, box q)) => {
                Formula::pullq(
                    true,
                    true,
                    formula,
                    &Formula::exists,
                    &Formula::or,
                    x,
                    y,
                    p,
                    q,
                )
            }
            Formula::And(box Formula::Forall(x, box p), q) => Formula::pullq(
                true,
                false,
                formula,
                &Formula::forall,
                &Formula::and,
                x,
                x,
                p,
                q,
            ),
            Formula::And(p, box Formula::Forall(y, box q)) => Formula::pullq(
                false,
                true,
                formula,
                &Formula::forall,
                &Formula::and,
                y,
                y,
                p,
                q,
            ),
            Formula::Or(box Formula::Forall(x, box p), q) => Formula::pullq(
                true,
                false,
                formula,
                &Formula::forall,
                &Formula::or,
                x,
                x,
                p,
                q,
            ),
            Formula::Or(p, box Formula::Forall(y, box q)) => Formula::pullq(
                false,
                true,
                formula,
                &Formula::forall,
                &Formula::or,
                y,
                y,
                p,
                q,
            ),
            Formula::And(box Formula::Exists(x, box p), q) => Formula::pullq(
                true,
                false,
                formula,
                &Formula::exists,
                &Formula::and,
                x,
                x,
                p,
                q,
            ),
            Formula::And(p, box Formula::Exists(y, box q)) => Formula::pullq(
                false,
                true,
                formula,
                &Formula::exists,
                &Formula::and,
                y,
                y,
                p,
                q,
            ),
            Formula::Or(box Formula::Exists(x, box p), q) => Formula::pullq(
                true,
                false,
                formula,
                &Formula::exists,
                &Formula::or,
                x,
                x,
                p,
                q,
            ),
            Formula::Or(p, box Formula::Exists(y, box q)) => Formula::pullq(
                false,
                true,
                formula,
                &Formula::exists,
                &Formula::or,
                y,
                y,
                p,
                q,
            ),
            _ => formula.clone(),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn pullq(
        sub_left: bool,
        sub_right: bool,
        formula: &Formula<Pred>,
        quant_const: &QuantConstructor,
        binop_const: &BinopConstructor,
        x: &str,
        y: &str,
        p: &Formula<Pred>,
        q: &Formula<Pred>,
    ) -> Formula<Pred> {
        // Helper function mutually recursive with `pull_quantifiers`.  Handles
        // the move of a single quantifier (of type corresponding to `quant_const`)
        // occuring at the heads of one or both  sides of a binary operation
        // (corresponding to (binop_const)).  `formula` is the entire formula.
        // Which side(s) the quantifiers are from is represented by `sub_left`/`sub_right`
        // `x`/`y` are the corresponding variables (if applicable) for the
        // left/right sides, and `p, q` are the corresponding
        // quantified formulas (if applicable)
        // for the left/right sides.
        let z = Term::variant(x, &formula.free_variables());
        let p_new = if sub_left {
            let inst = Instantiation::from([(x.to_owned(), Term::Var(z.clone()))]);
            p.subst(&inst)
        } else {
            p.clone()
        };
        let q_new = if sub_right {
            let inst = Instantiation::from([(y.to_owned(), Term::Var(z.clone()))]);
            q.subst(&inst)
        } else {
            q.clone()
        };
        quant_const(&z, &Formula::pull_quantifiers(&binop_const(&p_new, &q_new)))
    }

    fn raw_prenex(&self) -> Formula<Pred> {
        // Assumes `formula` is in NNF.
        match self {
            Formula::Forall(x, box p) => Formula::forall(x, &p.raw_prenex()),
            Formula::Exists(x, box p) => Formula::exists(x, &p.raw_prenex()),
            Formula::And(box p, box q) => {
                Formula::pull_quantifiers(&Formula::and(&p.raw_prenex(), &q.raw_prenex()))
            }
            Formula::Or(box p, box q) => {
                Formula::pull_quantifiers(&Formula::or(&p.raw_prenex(), &q.raw_prenex()))
            }
            _ => self.clone(),
        }
    }

    pub fn pnf(&self) -> Formula<Pred> {
        // Result should be of the form `Q_1 x_1 ... Q_n x_n. p`
        // where `p` is a quantifier-free formula in negation normal form.
        self.simplify().nnf().raw_prenex()
    }
}

#[cfg(test)]
mod normal_form_tests {

    use super::*;

    #[test]
    fn test_simplify_step() {
        let formula_string = "exists w. forall z. G(z)";
        let formula = Formula::<Pred>::parse(formula_string);
        let result = Formula::fo_simplify_step(&formula);
        let desired_string = "forall z. G(z)";
        let desired = Formula::<Pred>::parse(desired_string);
        assert_eq!(result, desired);
    }

    #[test]
    fn test_simplify() {
        let formula_string = "Y = X /\\ false \\/ (false ==> R(Z))";
        let formula = Formula::<Pred>::parse(formula_string);
        let desired = Formula::True;
        assert_eq!(formula.simplify(), desired);

        let formula_string =
            "forall x. (true ==> (R(x) <=> false)) ==> exists z exists y. ~(K(y) \\/ false)";
        let formula = Formula::<Pred>::parse(formula_string);
        let desired_string = "forall x. (~R(x) ==> exists y. ~K(y))";
        let desired = Formula::<Pred>::parse(desired_string);
        assert_eq!(formula.simplify(), desired);

        let formula_string = "exists w. forall z. G(z)";
        let formula = Formula::<Pred>::parse(formula_string);
        let desired_string = "forall z. G(z)";
        let desired = Formula::<Pred>::parse(desired_string);
        assert_eq!(formula.simplify(), desired);
    }

    #[test]
    fn test_raw_prenex() {
        let formula_string = "F(x) /\\ forall y. exists w. (G(y, z) \\/ exists z. ~F(z))";
        let formula = Formula::<Pred>::parse(formula_string);
        let result = formula.raw_prenex();
        let desired_string = "forall y. exists w. exists z'. F(x) /\\ (G(y, z) \\/ ~F(z'))";
        let desired = Formula::<Pred>::parse(desired_string);
        assert_eq!(result, desired);

        // let formula_string = "(exists x. F(x, z)) ==> (exists w forall z. ~G(z, x))";
        let formula_string = "(forall x. ~F(x, z)) \\/ (forall z. ~G(z, x))";
        let formula = Formula::<Pred>::parse(formula_string);
        let result = formula.raw_prenex();
        let desired_string = "forall x'. forall z'. ~F(x', z) \\/ ~G(z', x)";
        let desired = Formula::<Pred>::parse(desired_string);
        assert_eq!(result, desired);
    }

    #[test]
    fn test_pnf() {
        let formula_string = "(exists x. F(x, z)) ==> (exists w. forall z. ~G(z, x))";
        let formula = Formula::<Pred>::parse(formula_string);
        let result = formula.pnf();
        let desired_string = "forall x'. forall z'. ~F(x', z) \\/ ~G(z', x)";
        let desired = Formula::<Pred>::parse(desired_string);
        assert_eq!(result, desired);
    }
}

// Skolemization

impl Formula<Pred> {
    fn _skolem(
        formula: &Formula<Pred>,
        functions: &HashSet<String>,
    ) -> (Formula<Pred>, HashSet<String>) {
        match formula {
            Formula::Exists(y, box p) => {
                let free = formula.free_variables();
                let func_name_candidate = if free.is_empty() {
                    format!("c_{y}")
                } else {
                    format!("f_{y}")
                };
                let func_name = Term::variant(&func_name_candidate, functions);
                let mut new_functions = functions.clone();
                new_functions.insert(func_name.clone());
                let mut sorted = Vec::from_iter(free);
                sorted.sort();
                let vars: Vec<Term> = sorted.iter().map(|name| Term::var(name)).collect();
                let function_term = Term::fun(&func_name, &vars);
                let substituted = p.subst(&Instantiation::from([(y.to_owned(), function_term)]));
                Formula::_skolem(&substituted, &new_functions)
            }
            Formula::Forall(y, box p) => {
                let (inner, new_functions) = Formula::_skolem(p, functions);
                (Formula::forall(y, &inner), new_functions)
            }
            Formula::And(box p, box q) => Formula::_skolem_2(&Formula::and, p, q, functions),
            Formula::Or(box p, box q) => Formula::_skolem_2(&Formula::or, p, q, functions),
            _ => (formula.clone(), functions.clone()),
        }
    }

    fn _skolem_2(
        op: &BinopConstructor,
        p: &Formula<Pred>,
        q: &Formula<Pred>,
        functions_0: &HashSet<String>,
    ) -> (Formula<Pred>, HashSet<String>) {
        let (p_new, functions_1) = Formula::_skolem(p, functions_0);
        let (q_new, functions_2) = Formula::_skolem(q, &functions_1);
        (op(&p_new, &q_new), functions_2)
    }

    fn askolemize(&self) -> Formula<Pred> {
        // Harrison actually keeps the arities since he allows for distinct
        // functions of the same name (but different arities).
        // I'm going to see how far we can get w/o this since I think allowing
        // disctinct functions of the same name is pretty rare.
        let functions: HashSet<String> = self.functions().into_iter().map(|pair| pair.0).collect();

        Formula::_skolem(&self.simplify().nnf(), &functions).0
    }

    fn specialize(&self) -> Formula<Pred> {
        match self {
            Formula::Forall(_, box p) => p.specialize(),
            _ => self.clone(),
        }
    }

    pub fn skolemize(&self) -> Formula<Pred> {
        self.askolemize().pnf().specialize()
    }
}

#[cfg(test)]
mod skolemize_tests {

    use super::*;
    use crate::utils::slice_to_set_of_owned;

    #[test]
    fn test_skolem() {
        let formula_string = "R(F(n)) \\/ (exists x. P(f_w(x))) /\\ exists n. forall r. forall y. exists w. M(G(y, w)) \\/ exists z. ~M(F(z, w))";
        let formula = Formula::<Pred>::parse(formula_string);
        let result = Formula::_skolem(&formula, &slice_to_set_of_owned(&["f_w", "F", "G"]));
        let desired_formula_string =
            "R(F(n)) \\/ P(f_w(c_x())) /\\ forall r. forall y. (M(G(y, f_w'(y))) \\/ ~M(F(f_z(y), f_w'(y))))";
        let desired_formula = Formula::<Pred>::parse(desired_formula_string);
        // Note that "c_n" is added to the functions even though it appears zero times
        // in the result.  This is because `n` does not appear in within the scope of
        // the quantifier `exists n`.
        let desired_functions =
            slice_to_set_of_owned(&["c_x", "f_w", "G", "F", "f_w'", "f_z", "c_n"]);
        assert_eq!(result, (desired_formula, desired_functions));
    }

    #[test]
    fn test_skolemize() {
        let formula_string = "R(F(y)) \\/ (exists x. P(f_w(x))) /\\ exists n. forall r. forall y. exists w. M(G(y, w)) \\/ exists z. ~M(F(z, w))";
        let formula = Formula::<Pred>::parse(formula_string);
        let result = formula.skolemize();
        let desired_formula_string =
            "R(F(y)) \\/ P(f_w(c_x())) /\\ (M(G(y', f_w'(y'))) \\/ ~M(F(f_z(y'), f_w'(y'))))";
        let desired_formula = Formula::<Pred>::parse(desired_formula_string);
        assert_eq!(result, desired_formula);
    }
}

// Canonical Models
//

impl Formula<Pred> {
    pub fn peval(&self, d: &Valuation<Pred>) -> bool {
        // For evaluating quantifier free formulas without evaluating Predicates
        // but just looking up predicate instances in a table (FOValuation<Pred>).
        //
        // TODO (test)
        let pred_atom_eval = |pred: &Pred| -> bool {
            d.get(pred)
                .expect("Pred {pred:?} not found in Valuation {d:?}")
                .to_owned()
        };

        let forall_eval = |_var: &str, _subformula: &Formula<Pred>| -> bool {
            panic!("peval recieved quantifier");
        };
        let exists_eval = |_var: &str, _subformula: &Formula<Pred>| -> bool {
            panic!("peval recieved quantifier");
        };
        self.eval_core(&pred_atom_eval, &forall_eval, &exists_eval)
    }
}

// Herbrand methods
//
type GroundInstancesAugmenter =
    dyn Fn(&FormulaSet<Pred>, &Instantiation, &FormulaSet<Pred>) -> FormulaSet<Pred>;
type SatTester = dyn Fn(&FormulaSet<Pred>) -> bool;

use crate::formula::FormulaSet;

impl Formula<Pred> {
    #[allow(clippy::type_complexity)]
    fn _herbrand_functions(
        formula: &Formula<Pred>,
    ) -> (HashSet<(String, usize)>, HashSet<(String, usize)>) {
        let (mut constants, functions): (HashSet<(String, usize)>, HashSet<(String, usize)>) =
            formula
                .functions()
                .into_iter()
                .partition(|pair| pair.1 == 0);

        if constants.is_empty() {
            constants = HashSet::from([("c".to_string(), 0)]);
        }
        (constants, functions)
    }
    fn _ground_terms(
        constants: &HashSet<(String, usize)>,
        functions: &HashSet<(String, usize)>,
        level: usize,
    ) -> HashSet<Term> {
        if level == 0 {
            return constants
                .iter()
                .map(|(name, _arity)| Term::fun(name, &[]))
                .collect();
        }
        functions
            .iter()
            .map(|(name, arity)| {
                // Get set of all applications of this function to args of the
                // apprpriate level and length.
                Formula::_ground_tuples(constants, functions, level - 1, arity.to_owned())
                    .iter()
                    .map(|tuple| Term::fun(name, tuple))
                    .collect::<HashSet<Term>>()
            })
            .fold(HashSet::new(), |x, y| &x | &y)
    }

    fn _get_all_appends(
        vectors: &BTreeSet<Vec<Term>>,
        elements: &HashSet<Term>,
    ) -> BTreeSet<Vec<Term>> {
        // Return all vectors that result in prepending an element from `elements`
        // to a vector from `vectors`.
        elements
            .iter()
            .map(|element| {
                vectors
                    .iter()
                    .map(|vector| {
                        let mut clone = vector.clone();
                        clone.push(element.clone());
                        clone
                    })
                    .collect::<BTreeSet<Vec<Term>>>()
            })
            .fold(BTreeSet::new(), |x, y| &x | &y)
    }

    fn _ground_tuples(
        constants: &HashSet<(String, usize)>,
        functions: &HashSet<(String, usize)>,
        level: usize,
        size: usize,
    ) -> BTreeSet<Vec<Term>> {
        if size == 0 {
            return if level == 0 {
                BTreeSet::from([Vec::new()])
            } else {
                BTreeSet::from([])
            };
        }
        (0..=level)
            .map(|k| {
                let last_element_options = Formula::_ground_terms(constants, functions, k);
                let up_to_last_element_options =
                    Formula::_ground_tuples(constants, functions, level - k, size - 1);
                // Note we append instead of prepend since it seems cheaper.
                Formula::_get_all_appends(&up_to_last_element_options, &last_element_options)
            })
            .fold(BTreeSet::new(), |x, y| &x | &y)
    }

    fn make_instantiation(free_variables: &[String], terms: &[Term]) -> Instantiation {
        // Map corresponding `free_variables` to `terms`.
        assert_eq!(free_variables.len(), terms.len());
        free_variables
            .iter()
            .enumerate()
            .map(|(idx, var)| (var.to_owned(), terms[idx].clone()))
            .collect()
    }

    #[allow(clippy::too_many_arguments)]
    fn _herbloop(
        // NOTE could put the first 6 of these parameters into a struct `HerbloopContext`
        // since they don't change...
        augment_ground_instances: &GroundInstancesAugmenter,
        sat_test: &SatTester,
        formula: &FormulaSet<Pred>,
        constants: &HashSet<(String, usize)>,
        functions: &HashSet<(String, usize)>,
        free_variables: &Vec<String>,
        next_level: usize,
        ground_instances_so_far: &FormulaSet<Pred>,
        mut tuples_tried: HashSet<Vec<Term>>,
        mut tuples_left_at_level: BTreeSet<Vec<Term>>,
    ) -> HashSet<Vec<Term>> {
        // `augment_ground_instances`:  Updates ground_instances_so_far for a given tuple
        // of ground terms. Note that this will depend on whether a FormulaSet<Pred> is a
        // DNF vs CNF representation.
        //
        // `sat_test`: test for whether a `FormulaSet<Pred>` is satisfiable. Note that this will
        // depend on whether a FormulaSet<Pred> is a DNF vs CNF representation.
        //
        // `formula`: A `FormulaSet<Pred>` representation of the target formula to be tested for
        // satisfiability.
        //
        // `constants`/`functions`; all constants/functions in the Herbrand universe for
        // `formula`.
        //
        // `free_variables`: all free variables in `formula`.
        //
        // `next_level`: the next level of ground tuples to consider
        // after `tuples_left_at_level` is depleated.
        //
        // `ground_instances_so_far`:   A FormulaSet<Pred> representation of the set of
        // all ground instances that we are checking for joint satisfiability.
        //
        // `tuple_tried`: Tuples of terms that we have so far converted to ground instances
        // (`FormulaSet<Pred>`s specifically) and added to the `ground_instances_so_far`.
        //
        // `tuples_left_at_level`: Remaining tuples for the last `next_level` computed
        // which we have yet to convert and incorporate into `ground_instances_so_far`.
        println!("Ground instances tried: {}", tuples_tried.len());
        println!(
            "Size of the Ground instance FormulaSet: {}",
            ground_instances_so_far.len()
        );
        println!();

        if tuples_left_at_level.is_empty() {
            let new_tuples =
                Formula::_ground_tuples(constants, functions, next_level, free_variables.len());
            Formula::_herbloop(
                augment_ground_instances,
                sat_test,
                formula,
                constants,
                functions,
                free_variables,
                next_level + 1,
                ground_instances_so_far,
                tuples_tried,
                new_tuples,
            )
        } else {
            let next_tuple: Vec<Term> = tuples_left_at_level.pop_first().unwrap();
            let instantiation: Instantiation =
                Formula::make_instantiation(free_variables, &next_tuple);
            // NOTE could have this function take ownership of `ground_instances_so_far`
            // and mutate it.
            let augmented_instances =
                augment_ground_instances(formula, &instantiation, ground_instances_so_far);
            tuples_tried.insert(next_tuple);
            if !sat_test(&augmented_instances) {
                tuples_tried
            } else {
                Formula::_herbloop(
                    augment_ground_instances,
                    sat_test,
                    formula,
                    constants,
                    functions,
                    free_variables,
                    next_level,
                    &augmented_instances,
                    tuples_tried,
                    tuples_left_at_level,
                )
            }
        }
    }

    fn _subst_in_formulaset(
        formula: &FormulaSet<Pred>,
        instantiation: &Instantiation,
    ) -> FormulaSet<Pred> {
        formula
            .iter()
            .map(|clause| {
                clause
                    .iter()
                    .map(|literal| literal.subst(instantiation))
                    .collect()
            })
            .collect()
    }

    fn augement_dnf_formulaset(
        template_formula: &FormulaSet<Pred>,
        instantiation: &Instantiation,
        ground_instances_so_far: &FormulaSet<Pred>,
    ) -> FormulaSet<Pred> {
        // First substitute in the ground instances for `instantiation`.
        let subst_result: FormulaSet<Pred> =
            Formula::_subst_in_formulaset(template_formula, instantiation);

        // Combine with existing ground instances
        let aggregate = Formula::_set_distrib_and_over_or(&subst_result, ground_instances_so_far);

        Formula::_strip_contradictory(&aggregate)
    }

    #[allow(clippy::too_many_arguments)]
    fn gilmore_loop(
        formula: &FormulaSet<Pred>,
        constants: &HashSet<(String, usize)>,
        functions: &HashSet<(String, usize)>,
        free_variables: &Vec<String>,
        next_level: usize,
        ground_instances_so_far: &FormulaSet<Pred>,
        tuples_tried: HashSet<Vec<Term>>,
        tuples_left_at_level: BTreeSet<Vec<Term>>,
    ) -> HashSet<Vec<Term>> {
        // USES DNF FormulaSet representations throughout.
        //
        fn sat_test(formula: &FormulaSet<Pred>) -> bool {
            !formula.is_empty()
        }

        Formula::_herbloop(
            &Formula::augement_dnf_formulaset,
            &|formula| !formula.is_empty(),
            formula,
            constants,
            functions,
            free_variables,
            next_level,
            ground_instances_so_far,
            tuples_tried,
            tuples_left_at_level,
        )
    }

    pub fn gilmore(formula: &Formula<Pred>) -> usize {
        // Tautology test by checking whether the negation is unsatisfiable.
        // USES DNF FormulaSet representations throughout.
        let negation_skolemized = formula.generalize().negate().skolemize();
        let (constants, functions) = Formula::_herbrand_functions(&negation_skolemized);
        let mut free_variables = Vec::from_iter(negation_skolemized.free_variables());
        free_variables.sort();
        let dnf_formula = negation_skolemized.dnf_formulaset();
        let result = Formula::gilmore_loop(
            &dnf_formula,
            &constants,
            &functions,
            &free_variables,
            0,
            &FormulaSet::from([BTreeSet::new()]),
            HashSet::new(),
            BTreeSet::new(),
        );
        println!("Formula is valid.");
        result.len()
    }

    // Davis-Putnam approach
    //
    fn augment_cnf_formulaset(
        template_formula: &FormulaSet<Pred>,
        instantiation: &Instantiation,
        ground_instances_so_far: &FormulaSet<Pred>,
    ) -> FormulaSet<Pred> {
        // First substitute in the ground instances for `instantiation`.
        let subst_result: FormulaSet<Pred> =
            Formula::_subst_in_formulaset(template_formula, instantiation);

        // Combine with existing ground instances
        &subst_result | ground_instances_so_far
    }

    #[allow(clippy::too_many_arguments)]
    fn dp_loop(
        formula: &FormulaSet<Pred>,
        constants: &HashSet<(String, usize)>,
        functions: &HashSet<(String, usize)>,
        free_variables: &Vec<String>,
        next_level: usize,
        ground_instances_so_far: &FormulaSet<Pred>,
        tuples_tried: HashSet<Vec<Term>>,
        tuples_left_at_level: BTreeSet<Vec<Term>>,
    ) -> HashSet<Vec<Term>> {
        // USES CNF FormulaSet representations throughout.

        Formula::_herbloop(
            &Formula::augment_cnf_formulaset,
            &Formula::dpll,
            formula,
            constants,
            functions,
            free_variables,
            next_level,
            ground_instances_so_far,
            tuples_tried,
            tuples_left_at_level,
        )
    }

    fn _get_dp_unsat_core(
        formula: &FormulaSet<Pred>,
        free_variables: &Vec<String>,
        mut unknown: BTreeSet<Vec<Term>>,
        mut needed: BTreeSet<Vec<Term>>,
    ) -> HashSet<Vec<Term>> {
        // Find a minimal subset of tuples whose corresponding set of formulas are
        // inconsistent.
        // Note the following recursive invariant: The set of formulas corresponding to
        // `unknown U needed` is unsat.
        //
        if unknown.is_empty() {
            return HashSet::from_iter(needed);
        }
        let next = unknown.pop_first().unwrap();
        // If formulas for unknown U needed are still inconsistent, discard `next`,
        // and else add next to needed.

        // NOTE: Could pass this as an additional parameter to keep from having to build
        // it from scratch each time.
        let new_union = needed
            .union(&unknown)
            .map(|tuple| Formula::make_instantiation(free_variables, tuple))
            .fold(FormulaSet::new(), |acc, inst| {
                Formula::augment_cnf_formulaset(formula, &inst, &acc)
            });

        if Formula::dpll(&new_union) {
            needed.insert(next);
        }
        Formula::_get_dp_unsat_core(formula, free_variables, unknown, needed)
    }

    pub fn davis_putnam(formula: &Formula<Pred>, get_unsat_core: bool) -> usize {
        // Tautology test by checking whether the negation is unsatisfiable.
        // USES CNF FormulaSet representations throughout.
        let negation_skolemized = formula.generalize().negate().skolemize();
        let (constants, functions) = Formula::_herbrand_functions(&negation_skolemized);
        let mut free_variables = Vec::from_iter(negation_skolemized.free_variables());
        free_variables.sort();
        let cnf_formula = negation_skolemized.cnf_formulaset();
        let mut result = Formula::dp_loop(
            &cnf_formula,
            &constants,
            &functions,
            &free_variables,
            0,
            &FormulaSet::new(),
            HashSet::new(),
            BTreeSet::new(),
        );
        if get_unsat_core {
            result = Formula::_get_dp_unsat_core(
                &cnf_formula,
                &free_variables,
                BTreeSet::from_iter(result),
                BTreeSet::new(),
            )
        }
        println!(
            "Found {} inconsistent tuples of skolemized negation: {:?}",
            result.len(),
            result
        );
        println!("Formula is valid.");
        result.len()
    }
}

#[cfg(test)]
mod herbrand_tests {

    use super::*;

    #[test]
    fn test_herbrand_functions() {
        let formula = Formula::<Pred>::parse("P(g(f(42, x)))");
        let result = Formula::_herbrand_functions(&formula);
        let desired_constants = HashSet::from([(String::from("42"), 0)]);
        let desired_functions = HashSet::from([(String::from("f"), 2), (String::from("g"), 1)]);
        assert_eq!(result, (desired_constants, desired_functions));

        let formula = Formula::<Pred>::parse("P(f(x))");
        let result = Formula::_herbrand_functions(&formula);
        let desired_constants = HashSet::from([(String::from("c"), 0)]);
        let desired_functions = HashSet::from([(String::from("f"), 1)]);
        assert_eq!(result, (desired_constants, desired_functions));
    }

    #[test]
    fn test_ground_terms() {
        let constants = HashSet::from([(String::from("42"), 0)]);
        let functions = HashSet::from([(String::from("f"), 2), (String::from("g"), 1)]);

        let level = 0;
        let result = Formula::_ground_terms(&constants, &functions, level);
        let desired = HashSet::from([Term::constant("42")]);
        assert_eq!(result, desired);

        let level = 1;
        let result = Formula::_ground_terms(&constants, &functions, level);
        let desired = HashSet::from([Term::parset("g(42)"), Term::parset("f(42, 42)")]);
        assert_eq!(result, desired);

        let level = 2;
        let result = Formula::_ground_terms(&constants, &functions, level);
        let desired = HashSet::from([
            Term::parset("g(g(42))"),
            Term::parset("g(f(42, 42))"),
            Term::parset("f(g(42), 42)"),
            Term::parset("f(42, g(42))"),
            Term::parset("f(f(42, 42), 42)"),
            Term::parset("f(42, f(42, 42))"),
        ]);

        assert_eq!(result, desired);
    }

    #[test]
    fn test_get_all_appends() {
        let vectors: BTreeSet<Vec<Term>> = BTreeSet::from([
            vec![Term::parset("A"), Term::parset("B")],
            vec![Term::parset("C"), Term::parset("D")],
        ]);
        let elements: HashSet<Term> = HashSet::from([Term::parset("X"), Term::parset("Y")]);

        let result = Formula::_get_all_appends(&vectors, &elements);

        let desired: BTreeSet<Vec<Term>> = BTreeSet::from([
            vec![Term::parset("A"), Term::parset("B"), Term::parset("X")],
            vec![Term::parset("C"), Term::parset("D"), Term::parset("X")],
            vec![Term::parset("A"), Term::parset("B"), Term::parset("Y")],
            vec![Term::parset("C"), Term::parset("D"), Term::parset("Y")],
        ]);

        assert_eq!(result, desired);
    }

    #[test]
    fn test_ground_tuples() {
        let constants = HashSet::from([(String::from("42"), 0)]);
        let functions = HashSet::from([(String::from("f"), 2), (String::from("g"), 1)]);

        let level = 0;
        let size = 0;
        let result: BTreeSet<Vec<Term>> =
            Formula::_ground_tuples(&constants, &functions, level, size);
        let desired = BTreeSet::from([Vec::new()]);
        assert_eq!(result, desired);

        let level = 1;
        let size = 0;
        let result: BTreeSet<Vec<Term>> =
            Formula::_ground_tuples(&constants, &functions, level, size);
        let desired = BTreeSet::from([]);
        assert_eq!(result, desired);

        let level = 0;
        let size = 2;
        let result: BTreeSet<Vec<Term>> =
            Formula::_ground_tuples(&constants, &functions, level, size);
        let desired = BTreeSet::from([vec![Term::parset("42"), Term::parset("42")]]);
        assert_eq!(result, desired);

        let level = 2;
        let size = 1;
        let result: BTreeSet<Vec<Term>> =
            Formula::_ground_tuples(&constants, &functions, level, size);
        let desired = BTreeSet::from([
            vec![Term::parset("f(g(42), 42)")],
            vec![Term::parset("f(42, g(42))")],
            vec![Term::parset("g(g(42))")],
            vec![Term::parset("g(f(42, 42))")],
            vec![Term::parset("f(f(42, 42), 42)")],
            vec![Term::parset("f(42, f(42, 42))")],
        ]);
        assert_eq!(result, desired);

        let level = 1;
        let size = 2;
        let result: BTreeSet<Vec<Term>> =
            Formula::_ground_tuples(&constants, &functions, level, size);
        let desired = BTreeSet::from([
            vec![Term::parset("42"), Term::parset("g(42)")],
            vec![Term::parset("g(42)"), Term::parset("42")],
            vec![Term::parset("42"), Term::parset("f(42, 42)")],
            vec![Term::parset("f(42, 42)"), Term::parset("42")],
        ]);
        assert_eq!(result, desired);

        let level = 2;
        let size = 2;
        let result: BTreeSet<Vec<Term>> =
            Formula::_ground_tuples(&constants, &functions, level, size);
        let desired = BTreeSet::from([
            // 0 and 2
            vec![Term::parset("42"), Term::parset("f(g(42), 42)")],
            vec![Term::parset("42"), Term::parset("f(42, g(42))")],
            vec![Term::parset("42"), Term::parset("g(g(42))")],
            vec![Term::parset("42"), Term::parset("g(f(42, 42))")],
            vec![Term::parset("42"), Term::parset("f(f(42, 42), 42)")],
            vec![Term::parset("42"), Term::parset("f(42, f(42, 42))")],
            // 1 and 1
            vec![Term::parset("g(42)"), Term::parset("g(42)")],
            vec![Term::parset("f(42, 42)"), Term::parset("f(42, 42)")],
            vec![Term::parset("g(42)"), Term::parset("f(42, 42)")],
            vec![Term::parset("f(42, 42)"), Term::parset("g(42)")],
            // 2 and 0
            vec![Term::parset("f(g(42), 42)"), Term::parset("42")],
            vec![Term::parset("f(42, g(42))"), Term::parset("42")],
            vec![Term::parset("g(g(42))"), Term::parset("42")],
            vec![Term::parset("g(f(42, 42))"), Term::parset("42")],
            vec![Term::parset("f(f(42, 42), 42)"), Term::parset("42")],
            vec![Term::parset("f(42, f(42, 42))"), Term::parset("42")],
        ]);
        assert_eq!(result, desired);
    }

    #[test]
    fn test_herbloop() {
        fn augment_ground_instances(
            template: &FormulaSet<Pred>,
            instantiation: &Instantiation,
            accum: &FormulaSet<Pred>,
        ) -> FormulaSet<Pred> {
            // Just add the new substituted clauses to the ground instances so far.
            accum | &Formula::_subst_in_formulaset(template, instantiation)
        }

        fn sat_test(formula: &FormulaSet<Pred>) -> bool {
            // Just check for a random singleton clause.
            let target_clause = Formula::<Pred>::parse("~P(g(f(42, 42))) \\/  F(g(42))")
                .cnf_formulaset()
                .pop_first()
                .unwrap();
            !formula.contains(&target_clause)
        }

        // We will use CNF formulaset representations.
        let formula = Formula::<Pred>::parse("~P(g(x)) \\/ F(y)").cnf_formulaset();

        let constants = HashSet::from([("42".to_string(), 0)]);
        let functions = HashSet::from([("f".to_string(), 2), ("g".to_string(), 1)]);

        let free_variables = vec!["x".to_string(), "y".to_string()];
        let next_level = 0;
        // CNF representation of True
        let ground_instances_so_far: FormulaSet<Pred> = BTreeSet::new();
        let tuples_tried: HashSet<Vec<Term>> = HashSet::new();
        let tuples_left_at_level: BTreeSet<Vec<Term>> = BTreeSet::new();

        let result = Formula::_herbloop(
            &augment_ground_instances,
            &sat_test,
            &formula,
            &constants,
            &functions,
            &free_variables,
            next_level,
            &ground_instances_so_far,
            tuples_tried.clone(),
            tuples_left_at_level.clone(),
        );

        let level_0_size_2 =
            HashSet::from_iter(Formula::_ground_tuples(&constants, &functions, 0, 2));
        let level_1_size_2 =
            HashSet::from_iter(Formula::_ground_tuples(&constants, &functions, 1, 2));
        let level_2_size_2 =
            HashSet::from_iter(Formula::_ground_tuples(&constants, &functions, 2, 2));
        let all_size_2 = &(&level_0_size_2 | &level_1_size_2) | &level_2_size_2;

        assert!(result.is_subset(&all_size_2));
        assert!(level_0_size_2.is_subset(&result));
        assert!(level_1_size_2.is_subset(&result));

        // Start at level 2:
        let result_2 = Formula::_herbloop(
            &augment_ground_instances,
            &sat_test,
            &formula,
            &constants,
            &functions,
            &free_variables,
            2,
            &ground_instances_so_far,
            tuples_tried,
            tuples_left_at_level,
        );

        assert!(result_2.is_subset(&level_2_size_2));
    }

    #[test]
    fn test_gilmore_loop() {
        // We will use DNF formulaset representations.
        let formula = Formula::<Pred>::parse("~P(g(x)) /\\ P(y)").dnf_formulaset();

        let constants = HashSet::from([("42".to_string(), 0)]);
        let functions = HashSet::from([("f".to_string(), 2), ("g".to_string(), 1)]);

        let free_variables = vec!["x".to_string(), "y".to_string()];
        let next_level = 0;
        // DNF representation of True
        let ground_instances_so_far: FormulaSet<Pred> = BTreeSet::from([BTreeSet::new()]);
        let tuples_tried: HashSet<Vec<Term>> = HashSet::new();
        let tuples_left_at_level: BTreeSet<Vec<Term>> = BTreeSet::new();

        let result = Formula::gilmore_loop(
            &formula,
            &constants,
            &functions,
            &free_variables,
            next_level,
            &ground_instances_so_far,
            tuples_tried,
            tuples_left_at_level,
        );
        assert!(result.contains(&vec![Term::parset("42"), Term::parset("g(42)")]));
    }

    #[test]
    fn test_gilmore() {
        // We will use DNF formulaset representations.
        let formula = Formula::<Pred>::parse("exists x. forall y. P(x) ==> P(y)");
        let result = Formula::gilmore(&formula);
        assert!((2..=3).contains(&result));
    }

    #[test]
    fn test_dp_loop() {
        // We will use DNF formulaset representations.
        let formula = Formula::<Pred>::parse("~P(g(x)) /\\ P(y)").cnf_formulaset();

        let constants = HashSet::from([("42".to_string(), 0)]);
        let functions = HashSet::from([("f".to_string(), 2), ("g".to_string(), 1)]);

        let free_variables = vec!["x".to_string(), "y".to_string()];
        let next_level = 0;
        // CNF representation of True
        let ground_instances_so_far: FormulaSet<Pred> = BTreeSet::new();
        let tuples_tried: HashSet<Vec<Term>> = HashSet::new();
        let tuples_left_at_level: BTreeSet<Vec<Term>> = BTreeSet::new();

        let result = Formula::dp_loop(
            &formula,
            &constants,
            &functions,
            &free_variables,
            next_level,
            &ground_instances_so_far,
            tuples_tried,
            tuples_left_at_level,
        );
        assert!(result.contains(&vec![Term::parset("42"), Term::parset("g(42)")]));
    }

    #[test]
    fn test_get_dp_unsat_core() {
        let formula = Formula::<Pred>::parse("P(x) /\\ ~P(f_y(x))").cnf_formulaset();
        let free_variables = vec!["x".to_string()];
        let unknown = BTreeSet::from([
            vec![Term::parset("f_y(c)")],
            vec![Term::parset("g(f_y(c))")],
            vec![Term::parset("g(c)")],
            vec![Term::parset("(c)")],
            vec![Term::parset("d")],
        ]);
        let needed = BTreeSet::new();

        let result: HashSet<Vec<Term>> =
            Formula::_get_dp_unsat_core(&formula, &free_variables, unknown, needed);

        let desired = HashSet::from([vec![Term::parset("f_y(c)")], vec![Term::parset("c")]]);

        assert_eq!(result, desired);
    }

    #[test]
    fn test_davis_putnam_simple() {
        // We will use DNF formulaset representations.
        let formula = Formula::<Pred>::parse("exists x. forall y. P(x) ==> P(y)");
        let result = Formula::davis_putnam(&formula, false);
        assert!((2..=3).contains(&result));
    }

    #[test]
    fn test_davis_putnam_longer() {
        // We will use DNF formulaset representations.
        let string = "(forall x y. exists z. forall w. P(x) /\\ Q(y) ==> R(z) /\\ U(w)) ==> 
            (exists x y. P(x) /\\ Q(y)) ==> (exists z. R(z))";
        let formula = Formula::<Pred>::parse(string);
        let result = Formula::davis_putnam(&formula, false);
        println!("result: {result}");
    }

    #[test]
    fn test_davis_putnam_longer_unsat_core() {
        // We will use DNF formulaset representations.
        let string = "(forall x y. exists z. forall w. P(x) /\\ Q(y) ==> R(z) /\\ U(w)) ==> 
            (exists x y. P(x) /\\ Q(y)) ==> (exists z. R(z))";
        let formula = Formula::<Pred>::parse(string);
        let result = Formula::davis_putnam(&formula, true);
        assert_eq!(result, 2);
    }
}
