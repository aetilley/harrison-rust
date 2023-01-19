// ### First
// Order Logic ###
// AST specific parsing/printing functions for first-order (aka predicate) logic.

use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::hash::Hash;
use std::io::Write;
// use std::rc::Rc;

use crate::formula::{close_box, open_box, parse_formula, print_break, write, Formula};
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
    // Convenience builders for Terms.
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
    pub fn add(t1: Term, t2: Term) -> Term {
        Term::Fun(String::from("+"), vec![t1, t2])
    }

    pub fn unary_minus(t: Term) -> Term {
        Term::Fun(String::from("-"), vec![t])
    }

    #[allow(clippy::should_implement_trait)]
    pub fn sub(t1: Term, t2: Term) -> Term {
        Term::Fun(String::from("-"), vec![t1, t2])
    }

    #[allow(clippy::should_implement_trait)]
    pub fn mul(t1: Term, t2: Term) -> Term {
        Term::Fun(String::from("*"), vec![t1, t2])
    }

    #[allow(clippy::should_implement_trait)]
    pub fn div(t1: Term, t2: Term) -> Term {
        Term::Fun(String::from("/"), vec![t1, t2])
    }

    pub fn exp(t1: Term, t2: Term) -> Term {
        Term::Fun(String::from("^"), vec![t1, t2])
    }
    // The inclusion of infix list constructor is a bit
    // surprising and seems to imply that domains will often
    // be closed under cartesian products.
    pub fn cons(t1: Term, t2: Term) -> Term {
        Term::Fun(String::from("::"), vec![t1, t2])
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
                Term::add(Term::constant("13"), Term::var("x")),
                Term::var("A"),
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
                Term::mul(Term::var("apples"), Term::unary_minus(Term::var("oranges"))),
                Term::constant("42"),
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
            Term::add(Term::constant("13"), Term::var("x")),
            Term::var("A"),
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
            Term::mul(Term::var("apples"), Term::unary_minus(Term::var("oranges"))),
            Term::constant("42"),
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
        Ok((Formula::atom(Pred::new(&rest[0], &[term1, term2])), newrest))
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
                (Formula::atom(Pred::new(p, &terms)), newrest)
            }
            [p, rest @ ..] if p != "(" => (Formula::atom(Pred::new(p, &[])), rest),
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
        let desired = Formula::atom(pred);
        assert_eq!(result, desired);
    }

    #[test]
    fn test_parse_pred_formula_variables() {
        let input = "F(x) /\\ G(d(y)) ==> p(13, w)";

        let result = Formula::<Pred>::parse(input);

        let desired = Formula::imp(
            Formula::and(
                Formula::atom(Pred::new("F", &[Term::var("x")])),
                Formula::atom(Pred::new("G", &[Term::fun("d", &[Term::var("y")])])),
            ),
            Formula::atom(Pred::new("p", &[Term::constant("13"), Term::var("w")])),
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
            Formula::forall(
                "w",
                Formula::and(
                    Formula::atom(Pred::new("F", &[Term::var("RED")])),
                    Formula::exists(
                        "RED",
                        Formula::exists(
                            "BLUE",
                            Formula::atom(Pred::new("G", &[Term::fun("d", &[Term::var("y")])])),
                        ),
                    ),
                ),
            ),
        );

        assert_eq!(result, desired);
    }

    #[test]
    fn test_parse_ea_quantified() {
        let desired = Formula::exists(
            "X",
            Formula::forall(
                "Y",
                Formula::atom(Pred::new("bar", &[Term::var("X"), Term::var("Y")])),
            ),
        );

        let result = Formula::<Pred>::parse("exists X. forall Y. bar(X, Y)");
        assert_eq!(result, desired);
    }

    #[test]
    fn test_simple_infix() {
        env_logger::init();
        let input = "~(x = y)";
        let desired = Formula::not(Formula::atom(Pred::new(
            "=",
            &[Term::var("x"), Term::var("y")],
        )));
        let result = Formula::<Pred>::parse(input);
        assert_eq!(result, desired);
    }

    #[test]
    fn test_more_quantifiers() {
        let input = "forall x. ~(x = 0) ==> exists y. x * y = 1";

        let desired = Formula::forall(
            "x",
            Formula::imp(
                Formula::not(Formula::atom(Pred::new(
                    "=",
                    &[Term::var("x"), Term::fun("0", &[])],
                ))),
                Formula::exists(
                    "y",
                    Formula::atom(Pred::new(
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
            Formula::exists(
                "Y",
                Formula::atom(Pred::new(
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
            Formula::and(
                Formula::atom(Pred::new("F", &[Term::var("x")])),
                Formula::atom(Pred::new("G", &[Term::fun("d", &[Term::var("y")])])),
            ),
            Formula::atom(Pred::new("p", &[Term::constant("13"), Term::var("w")])),
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
            Formula::forall(
                "w",
                Formula::and(
                    Formula::atom(Pred::new("F", &[Term::var("RED")])),
                    Formula::exists(
                        "RED",
                        Formula::exists(
                            "BLUE",
                            Formula::atom(Pred::new("G", &[Term::fun("d", &[Term::var("y")])])),
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
pub struct Valuation<'a, DomainType: Hash + Clone + Eq + Debug> {
    // Any new assignments for this frame
    frame: HashMap<String, DomainType>,
    // Pointer to the next frame
    next: Option<&'a Valuation<'a, DomainType>>,
}

impl<'a, DomainType: Hash + Clone + Eq + Debug> Valuation<'a, DomainType> {
    // Maybe implement this later.
    #[allow(clippy::new_without_default)]
    pub fn new() -> Valuation<'a, DomainType> {
        Valuation {
            frame: HashMap::new(),
            next: None,
        }
    }

    pub fn from(data: &HashMap<String, DomainType>) -> Valuation<'a, DomainType> {
        // Todo, implement coming from general iter.
        Valuation {
            frame: data.clone(),
            next: None,
        }
    }

    fn set(&self, name: String, val: DomainType) -> Valuation<'_, DomainType> {
        let frame = HashMap::from([(name, val)]);
        let next = Some(self);
        Valuation { frame, next }
    }

    fn get(&self, name: &str) -> Option<DomainType> {
        // First try local frame, and failing that, defer
        // to `next` Valuation (if any).
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
        v: &Valuation<DomainType>,
    ) -> DomainType {
        match self {
            Term::Var(name) => match v.get(&name.to_string()) {
                Some(val) => val,
                None => panic!("Valuation not defined on variable {name:?}."),
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
        let v = Valuation::from(&map);

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
        v: &Valuation<DomainType>,
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
        let v = Valuation::from(&map);

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
        v: &Valuation<DomainType>,
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
        let v = Valuation::from(&map);

        // let pred = Pred::new("bar", &vec![Term::var("X"), Term::var("Z")]); // 14 + 2 % 2 = 0
        // let formula_1 = Formula::atom(pred);

        let formula_1 = Formula::<Pred>::parse("bar(X, Z)");
        assert!(formula_1.eval(&m, &v));
    }

    #[test]
    fn test_formula_eval_quantified_1() {
        let m = test_utils::get_test_interpretation();

        let map = HashMap::from([("Z".to_string(), 2)]);
        let v = Valuation::from(&map);

        // exists X. X + 2 % 2 == 0
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
        let v = Valuation::from(&map);

        // exists X Y. X + Y + 42 == 58
        let formula_1 = Formula::<Pred>::parse("exists X. exists Y. foo(X, Y, Z) = W");

        // A Solution exists.
        assert!(formula_1.eval(&m, &v));

        // exists X Y. X + Y + 42 == 43
        let formula_2 = Formula::<Pred>::parse("exists X. exists Y. foo(X, Y, Z) = U");
        // No Solution exists in (1..=60)
        assert!(!formula_2.eval(&m, &v));
    }

    #[test]
    fn test_formula_eval_quantified_3() {
        let m = test_utils::get_test_interpretation();
        let v = Valuation::new();

        let formula_ae = Formula::<Pred>::parse("forall X. exists Y. bar(X, Y)");
        assert!(formula_ae.eval(&m, &v));
        let formula_ea = Formula::<Pred>::parse("exists X. forall Y. bar(X, Y)");
        assert!(!formula_ea.eval(&m, &v));
    }
}

impl Term {
    fn get_variables_for_termlist(terms: &[Term]) -> HashSet<String> {
        terms
            .iter()
            .fold(HashSet::new(), |acc, term| &acc | &term.variables())
    }

    fn variables(&self) -> HashSet<String> {
        match self {
            Term::Var(name) => HashSet::from([name.clone()]),
            Term::Fun(_name, terms) => Term::get_variables_for_termlist(terms),
        }
    }
}

#[cfg(test)]
mod test_term_variables {

    use super::*;

    #[test]
    fn tet_get_variables_for_termlist() {
        let term1 = Term::parset("foo(A)");
        let term2 = Term::parset("B");
        let term3 = Term::parset("bar(B, baz(C))");
        let input = vec![term1, term2, term3];

        let result = Term::get_variables_for_termlist(&input);
        assert_eq!(
            result,
            HashSet::from(["A".to_string(), "B".to_string(), "C".to_string()])
        );
    }
}

impl Pred {
    fn variables(&self) -> HashSet<String> {
        Term::get_variables_for_termlist(&self.terms)
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

    fn free_variables(&self) -> HashSet<String> {
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
}

#[cfg(test)]
mod test_formula_variables {

    use super::*;
    use crate::utils::slice_to_set_of_owned;

    #[test]
    fn test_formula_variables() {
        let formula = Formula::<Pred>::parse("forall X. X = W ==> exists W. foo(X, W, Z) = U");
        let result_all = formula.variables();
        let desired_all = slice_to_set_of_owned(&["U", "W", "X", "Z"]);
        assert_eq!(result_all, desired_all);
        let result_free = formula.free_variables();
        let desired_free = slice_to_set_of_owned(&["U", "W", "Z"]);
        assert_eq!(result_free, desired_free);
    }
}
