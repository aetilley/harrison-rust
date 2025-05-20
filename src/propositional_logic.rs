// PROPOSITIONAL LOGIC
//
// parsing, printing, eval, and sat functions for
// propositional (aka sentential) logic.

use std::cmp;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt::Debug;

use crate::formula::{Formula, Valuation};
use crate::propositional_logic_grammar::PropFormulaParser;
use crate::token::{Lexer, LexicalError, Token};

use lalrpop_util::ParseError;
use regex::Regex;

// A propositional variable.
#[derive(Debug, PartialEq, Clone, Hash, Eq, PartialOrd, Ord)]
pub struct Prop {
    name: String,
}

impl Prop {
    pub fn new(name: &str) -> Prop {
        // Convenience constructor for `Prop`s.
        Prop {
            name: String::from(name),
        }
    }

    fn get_propvar(_prec: u32, atom: &Prop) -> String {
        // Our atom printer for propositional logic.  Note that the precedence argument is
        // simply ignored.

        atom.name.clone()
    }
}

#[cfg(test)]
mod prop_basic_tests {
    use super::*;

    fn init() {
        let _ = env_logger::builder().is_test(true).try_init();
    }

    #[test]
    fn test_print_propvar() {
        let prop = Prop::new("SomeProp");
        let output = Prop::get_propvar(0, &prop);
        assert_eq!(output, "SomeProp");

        let output2 = Prop::get_propvar(42, &prop);
        assert_eq!(output2, "SomeProp");
    }
}

// PARSING

impl Formula<Prop> {
    pub fn parse(input: &str) -> Result<Formula<Prop>, ParseError<usize, Token, LexicalError>> {
        let lexer = Lexer::new(input);
        let parser = PropFormulaParser::new();
        parser.parse(lexer)
    }
}

#[cfg(test)]
mod prop_parse_tests {
    use super::*;

    fn init() {
        let _ = env_logger::builder().is_test(true).try_init();
    }

    // Convenience to save us some typing.
    fn prop(name: &str) -> Prop {
        Prop::new(name)
    }

    #[test]
    fn test_parse_true() {
        let result = Formula::<Prop>::parse("true").unwrap();
        let desired = Formula::True;
        assert_eq!(result, desired);
    }

    #[test]
    fn test_parse_false() {
        let result = Formula::<Prop>::parse("false").unwrap();
        let desired = Formula::False;
        assert_eq!(result, desired);
    }

    #[test]
    fn test_parse_or() {
        let result = Formula::<Prop>::parse("A \\/ B").unwrap();
        let desired = Formula::or(&Formula::atom(&prop("A")), &Formula::atom(&prop("B")));
        assert_eq!(result, desired);
    }

    #[test]
    fn test_parse_or2() {
        let result = Formula::<Prop>::parse("A \\/ ~A").unwrap();
        let desired = Formula::or(
            &Formula::atom(&prop("A")),
            &Formula::not(&Formula::atom(&prop("A"))),
        );
        assert_eq!(result, desired);
    }

    #[test]
    fn test_parse_and() {
        let result = Formula::<Prop>::parse("(A /\\ ~A)").unwrap();
        let desired = Formula::and(
            &Formula::atom(&prop("A")),
            &Formula::not(&Formula::atom(&prop("A"))),
        );
        assert_eq!(result, desired);
    }

    #[test]
    fn test_parse_and_assoc() {
        let result = Formula::<Prop>::parse("p /\\ q /\\ p /\\ q").unwrap();
        let desired = Formula::and(
            &Formula::atom(&prop("p")),
            &Formula::and(
                &Formula::atom(&prop("q")),
                &Formula::and(&Formula::atom(&prop("p")), &Formula::atom(&prop("q"))),
            ),
        );
        assert_eq!(result, desired);
    }

    #[test]
    fn test_parse_comp() {
        let result = Formula::<Prop>::parse("a <=> (b /\\ c)").unwrap();
        let desired = Formula::iff(
            &Formula::atom(&Prop::new("a")),
            &Formula::and(
                &Formula::atom(&Prop::new("b")),
                &Formula::atom(&Prop::new("c")),
            ),
        );
        assert_eq!(result, desired);
    }

    #[test]
    fn test_parse_comp2() {
        let result = Formula::<Prop>::parse("(a /\\ false) \\/ (false ==> d)").unwrap();
        let desired = Formula::or(
            &Formula::and(&Formula::atom(&Prop::new("a")), &Formula::False),
            &Formula::imp(&Formula::False, &Formula::atom(&Prop::new("d"))),
        );
        assert_eq!(result, desired);
    }

    #[test]
    fn test_parse_comp3() {
        let result = Formula::<Prop>::parse("(p /\\ q) /\\ q ==> (p /\\ q) /\\ q").unwrap();
        let desired = Formula::imp(
            &Formula::and(
                &Formula::and(&Formula::atom(&prop("p")), &Formula::atom(&prop("q"))),
                &Formula::atom(&prop("q")),
            ),
            &Formula::and(
                &Formula::and(&Formula::atom(&prop("p")), &Formula::atom(&prop("q"))),
                &Formula::atom(&prop("q")),
            ),
        );
        assert_eq!(result, desired);
    }

    #[test]
    fn test_parse_comp4() {
        let result = Formula::<Prop>::parse("a /\\ ~b \\/ (~c \\/ d)").unwrap();
        let desired = Formula::or(
            &Formula::and(
                &Formula::atom(&prop("a")),
                &Formula::not(&Formula::atom(&prop("b"))),
            ),
            &Formula::or(
                &Formula::not(&Formula::atom(&prop("c"))),
                &Formula::atom(&prop("d")),
            ),
        );
        assert_eq!(result, desired);
    }

    #[test]
    fn test_parse_comp6() {
        let result = Formula::<Prop>::parse("A /\\ (false \\/ B)").unwrap();
        let desired = Formula::and(
            &Formula::atom(&prop("A")),
            &Formula::or(&Formula::False, &Formula::atom(&prop("B"))),
        );
        assert_eq!(result, desired);
    }

    #[test]
    fn test_parse_comp7() {
        let result = Formula::<Prop>::parse("~(A ==> (B <=> C))").unwrap();
        let desired = Formula::not(&Formula::imp(
            &Formula::atom(&prop("A")),
            &Formula::iff(&Formula::atom(&prop("B")), &Formula::atom(&prop("C"))),
        ));
        assert_eq!(result, desired);
    }

    #[test]
    fn test_parse_quantifier() {
        let result = Formula::<Prop>::parse("forall x y. (A /\\ (false \\/ B))").unwrap();
        let desired = Formula::forall(
            "x",
            &Formula::forall(
                "y",
                &Formula::and(
                    &Formula::atom(&prop("A")),
                    &Formula::or(&Formula::False, &Formula::atom(&prop("B"))),
                ),
            ),
        );
        assert_eq!(result, desired);
    }

    #[test]
    fn test_parse_quantifier_2() {
        let result = Formula::<Prop>::parse("A /\\ exists z. (false \\/ B)").unwrap();
        let desired = Formula::and(
            &Formula::atom(&prop("A")),
            &Formula::exists(
                "z",
                &Formula::or(&Formula::False, &Formula::atom(&prop("B"))),
            ),
        );
        assert_eq!(result, desired);
    }

    #[test]
    fn test_parse_double_neg_parens() {
        let result = Formula::<Prop>::parse("~(~A)").unwrap();
        let desired = Formula::not(&Formula::not(&Formula::atom(&prop("A"))));
        assert_eq!(result, desired);
    }

    #[test]
    fn test_double_neg_no_parens() {
        let result = Formula::<Prop>::parse("~~A").unwrap();
        let desired = Formula::not(&Formula::not(&Formula::atom(&prop("A"))));
        assert_eq!(result, desired);
    }
}

// PRINTING

impl Formula<Prop> {
    pub fn pretty(&self) -> String {
        let pfn: fn(u32, &Prop) -> String = Prop::get_propvar;
        self.pretty_general(&pfn)
    }

    pub fn pprint(&self) {
        println!("{}\n", self.pretty())
    }
}

#[cfg(test)]
mod prop_formula_print_tests {
    use super::*;

    fn init() {
        let _ = env_logger::builder().is_test(true).try_init();
    }

    #[test]
    fn test_pretty() {
        let formula = Formula::and(
            &Formula::atom(&Prop::new("Prop5")),
            &Formula::iff(
                &Formula::atom(&Prop::new("Prop2")),
                &Formula::imp(
                    &Formula::or(
                        &Formula::atom(&Prop::new("Prop3")),
                        &Formula::atom(&Prop::new("Prop4")),
                    ),
                    &Formula::atom(&Prop::new("Prop1")),
                ),
            ),
        );
        let result = formula.pretty();
        assert_eq!(result, "Prop5 /\\ (Prop2 <=> Prop3 \\/ Prop4 ==> Prop1)");
    }
}

// Propositional Eval

impl Prop {
    fn eval(&self, val: &Valuation<Prop>) -> bool {
        match val.get(self) {
            Some(b) => b.to_owned(),
            None => panic!("Valuation is not defined on prop {:?}", &self),
        }
    }
}

// Propositional Formula Eval
impl Formula<Prop> {
    pub fn eval(&self, val: &Valuation<Prop>) -> bool {
        // Theorem (Harrison 2.2):
        // For any `p: Formula<Prop>` if `v, v': Valuation<Prop>`,
        // such that v(x) ==  v'(x) for all x in p.atoms(),
        // then p.eval(v) == p.eval(v').
        let prop_atom_eval = |prop: &Prop| prop.eval(val);

        fn qempty(_: &str, _: &Formula<Prop>) -> bool {
            panic!("Did not expect to find quantifiers in propositional evaluation.");
        }

        self.eval_core(&prop_atom_eval, &qempty, &qempty)
    }
}

#[cfg(test)]
mod eval_tests {
    use super::*;

    // Convenience to save us some typing.
    fn prop(name: &str) -> Prop {
        Prop::new(name)
    }

    #[test]
    fn test_eval() {
        let mut formula;
        let val = Valuation::from([(prop("A"), true), (prop("B"), false), (prop("C"), true)]);

        formula = Formula::<Prop>::parse("A").unwrap();
        assert!(formula.eval(&val));

        formula = Formula::<Prop>::parse("B").unwrap();
        assert!(!formula.eval(&val));

        formula = Formula::<Prop>::parse("C <=> A /\\ B").unwrap();
        assert!(!formula.eval(&val));
    }
}

// ### Core SAT definitions (ie. brute-force algorithms).

impl Formula<Prop> {
    fn get_all_valuations(atoms: &HashSet<Prop>) -> Vec<Valuation<Prop>> {
        // Initialize result to the singleton with the empty valuation.
        // WARNING, running time/space is Exp(|atoms|))

        let mut sorted: Vec<Prop> = atoms.iter().cloned().collect();
        sorted.sort();
        let mut result = vec![BTreeMap::new()];
        for atom in sorted {
            let mut new_result = Vec::new();
            for val in result {
                let mut positive = val.clone();
                positive.insert(atom.clone(), true);
                new_result.push(positive);
                let mut negative = val.clone();
                negative.insert(atom.clone(), false);
                new_result.push(negative)
            }
            result = new_result;
        }
        result
    }

    pub fn get_truthtable(&self) -> String {
        let atoms = self.atoms();
        let mut sorted_atoms = Vec::from_iter(&atoms);
        sorted_atoms.sort();
        let column_width = 1 + cmp::max(5, atoms.iter().map(|x| x.name.len()).max().unwrap());
        // Pad String `s` with enough spaces to be `column_width`.
        let pad = |s: String| {
            format!(
                "{}{}",
                s,
                String::from_iter(vec![' '; column_width - s.len()])
            )
        };
        let truth_string = |value: bool| {
            if value {
                String::from("true")
            } else {
                String::from("false")
            }
        };
        let make_row = |val: &Valuation<Prop>| {
            let input_string = String::from_iter(
                sorted_atoms
                    .iter()
                    .map(|x| val[x])
                    .map(truth_string)
                    .map(pad),
            );
            let result = self.eval(val);
            let output_string = truth_string(result);
            format!("{input_string}| {output_string}\n")
        };
        let body = String::from_iter(Formula::get_all_valuations(&atoms).iter().map(make_row));

        let header_lhs = String::from_iter(sorted_atoms.iter().map(|p| p.name.clone()).map(pad));
        let header = format!("{header_lhs}| formula");
        let separator = String::from_iter(vec!['-'; header.len()]);
        format!("{header}\n{separator}\n{body}{separator}\n")
    }

    pub fn brute_tautology(&self) -> bool {
        // NOTE:  SLOW, USE OTHER VERSIONS.
        // Note that the set of valuations should never be empty
        // (Event `True` has the empty valuation.)
        Formula::get_all_valuations(&self.atoms())
            .iter()
            .all(|x| self.eval(x))
    }

    pub fn brute_equivalent(&self, formula: &Formula<Prop>) -> bool {
        // NOTE:  SLOW, USE OTHER VERSIONS.
        let target = Formula::iff(self, formula);
        target.brute_tautology()
    }

    pub fn brute_unsatisfiable(&self) -> bool {
        // NOTE:  SLOW, USE OTHER VERSIONS.
        Formula::not(self).brute_tautology()
    }

    pub fn brute_satisfiable(&self) -> bool {
        // NOTE:  SLOW, USE OTHER VERSIONS.
        !self.brute_unsatisfiable()
    }
}

#[cfg(test)]
mod core_sat_definitions_tests {
    use super::*;

    // Convenience to save us some typing.
    fn prop(name: &str) -> Prop {
        Prop::new(name)
    }

    #[test]
    fn test_get_all_valuations() {
        let atoms = HashSet::from([prop("A"), prop("B"), prop("C")]);
        let result = Formula::get_all_valuations(&atoms);
        let desired_result = vec![
            BTreeMap::from([(prop("A"), true), (prop("B"), true), (prop("C"), true)]),
            BTreeMap::from([(prop("A"), true), (prop("B"), true), (prop("C"), false)]),
            BTreeMap::from([(prop("A"), true), (prop("B"), false), (prop("C"), true)]),
            BTreeMap::from([(prop("A"), true), (prop("B"), false), (prop("C"), false)]),
            BTreeMap::from([(prop("A"), false), (prop("B"), true), (prop("C"), true)]),
            BTreeMap::from([(prop("A"), false), (prop("B"), true), (prop("C"), false)]),
            BTreeMap::from([(prop("A"), false), (prop("B"), false), (prop("C"), true)]),
            BTreeMap::from([(prop("A"), false), (prop("B"), false), (prop("C"), false)]),
        ];
        assert_eq!(result, desired_result);
    }

    #[test]
    fn test_print_truthtable() {
        let formula = Formula::<Prop>::parse("C <=> A /\\ B").unwrap();
        let output = formula.get_truthtable();
        let desired_output = "\
A     B     C     | formula
---------------------------
true  true  true  | true
true  true  false | false
true  false true  | false
true  false false | true
false true  true  | false
false true  false | true
false false true  | false
false false false | true
---------------------------
";

        assert_eq!(output, desired_output);
    }

    #[test]
    fn test_brute_tautology_and_satisfiable() {
        let form1 = Formula::<Prop>::parse("true").unwrap();
        assert!(form1.brute_tautology());
        assert!(!form1.brute_unsatisfiable());
        assert!(form1.brute_satisfiable());

        let form2 = Formula::<Prop>::parse("A \\/ B").unwrap();
        assert!(!form2.brute_tautology());
        assert!(!form2.brute_unsatisfiable());
        assert!(form2.brute_satisfiable());

        let form3 = Formula::<Prop>::parse("A \\/ ~A").unwrap();
        assert!(form3.brute_tautology());
        assert!(!form3.brute_unsatisfiable());
        assert!(form3.brute_satisfiable());

        let form4 = Formula::<Prop>::parse("A /\\ ~A").unwrap();
        assert!(!form4.brute_tautology());
        assert!(form4.brute_unsatisfiable());
        assert!(!form4.brute_satisfiable());
    }
}

// ### Normal Forms

// Set representations of Formulas in disjunctive or conjunctive normal form
// (we need to specify in order to have a unique meaning)..
// Note we could replace the inner `Formula<Prop>` by an indicator
// function on `Prop` (or just a set of type Valuation<Prop>), which would prevent
// non-literals from going in there.
// In the meantime, we use a BTreeSet here so that we can order the items
// by Prop.name.
pub type FormulaSet = BTreeSet<BTreeSet<Formula<Prop>>>;

impl Formula<Prop> {
    fn psubst(&self, subfn: &HashMap<Prop, Formula<Prop>>) -> Formula<Prop> {
        // Replace each Atom(prop) with a subformula given by `subfn[prop]`.
        //
        // Theorem (Harrison 2.3)
        // For any `p: Prop`, and `p, q: Formula<Prop>` and any `v: Valuation<Prop>`,
        // we have p.psubst({x |=> q}).eval(v) == p.eval((x |=> q.eval(v))v).
        //
        // Corollary (Harrison 2.4)
        // If `p: Formula<Prop>` is a tautology, `x: Prop`, and `q: Formula<Prop>`
        // then p.psubst({x |=> q}) is also a tautology.
        //
        // Theorem (Harrison 2.5)
        // For `v: Valuation<Prop>` and `p,q: Formula<Prop>` such that p.eval(v) == q.eval(v).
        // Then for any x: Prop and r: Formula<Prop> we have
        // r.psubst({x|=>p}).eval(v) == r.psubst({x|=>q}).eval(v)
        //
        // Corollary (Harrision 2.6)
        // If `p, q: Formula<Prop>` are logically equivalent, then
        // for all `v: Valuation<Prop>` we have
        // r.psubst({x|=>p}).eval(v) == r.psubst({x|=>q}).eval(v)
        // In particular r.psubst({x|=>p}) is a tautology iff r.psubst({x|=>q}) is.
        let map = |p: &Prop| subfn.get(p).unwrap_or(&Formula::atom(p)).clone();
        self.on_atoms(&map)
    }

    pub fn simplify(&self) -> Formula<Prop> {
        self.simplify_recursive(&Formula::psimplify_step)
    }

    fn dual(&self) -> Formula<Prop> {
        // Theorem (Harrison 2.7)
        // For `p: Formula<Prop>` and `v: Valuation<Prop>`
        // and letting !v denote the map of (prop: !val) for
        // (prop, val) in v,  we have
        // p.dual().eval(v) == !p.eval(!v).
        //
        // Corollary (Harrision 2.8) If `p, q: Formula<Prop>` are equivalent
        // (e.g. p.brute_equivalent(&q) below),
        // then so are `p.dual()` and `q.dual()`.
        // If `p` is a tautology then so is `Formula::not(p.dual()).
        match self {
            Formula::False => Formula::True,
            Formula::True => Formula::False,
            Formula::Atom(_) => self.clone(),
            Formula::Not(p) => Formula::not(&p.dual()),
            Formula::And(p, q) => Formula::or(&p.dual(), &q.dual()),
            Formula::Or(p, q) => Formula::and(&p.dual(), &q.dual()),
            _ => panic!("Formula involves connectives '==>' or '<=>'"),
        }
    }

    fn nnf(&self) -> Formula<Prop> {
        // Negation normal form
        self.simplify().raw_nnf()
    }

    fn nenf(&self) -> Formula<Prop> {
        // Negation and normal form also allowing equivalences (iff).
        self.simplify().raw_nenf()
    }
}

#[cfg(test)]
mod normal_form_tests {
    use super::*;

    // Convenience to save us some typing.
    fn prop(name: &str) -> Prop {
        Prop::new(name)
    }

    #[test]
    fn test_psubst() {
        let map = HashMap::from([(prop("p"), Formula::<Prop>::parse("p /\\ q").unwrap())]);
        let formula = Formula::<Prop>::parse("p /\\ q ==> p /\\ q").unwrap();
        let result = formula.psubst(&map);
        let desired = Formula::<Prop>::parse("(p /\\ q) /\\ q ==> (p /\\ q) /\\ q").unwrap();
        assert_eq!(result, desired)
    }

    #[test]
    fn test_dual() {
        let formula = Formula::<Prop>::parse("(a /\\ ~b) \\/ (~c \\/ d)").unwrap();
        let desired = Formula::<Prop>::parse("(a \\/ ~b ) /\\ (~c /\\ d)").unwrap();
        assert_eq!(formula.dual(), desired);
    }
    #[test]
    fn test_nnf() {
        let formula = Formula::<Prop>::parse("~(~A) /\\ (false \\/ B)").unwrap();
        let desired = Formula::<Prop>::parse("A /\\ B").unwrap();
        assert_eq!(formula.nnf(), desired);
    }

    #[test]
    fn test_nenf() {
        let formula = Formula::<Prop>::parse("~(~A) /\\ (false \\/ B)").unwrap();
        let desired = Formula::<Prop>::parse("A /\\ B").unwrap();
        assert_eq!(formula.nnf(), desired);
    }
}

// ### Definitional CNF

type Triple = (Formula<Prop>, Defs, usize);
type BinOp = fn(&Formula<Prop>, &Formula<Prop>) -> Formula<Prop>;
type Defs = HashMap<Formula<Prop>, (Formula<Prop>, Formula<Prop>)>;

impl Formula<Prop> {
    // Note that when _maincnf recieves such a triple, the formula could be anything
    // But when such a triple is returned by defstep (and so by this function),
    // the formula is always an atom and so the value returned here is always
    // a literal.
    /* Definitional CNF */
    fn _main_def_cnf(formula: &Formula<Prop>, defs: &Defs, n: usize) -> Triple {
        let triple: Triple = (formula.clone(), defs.clone(), n);
        match formula {
            Formula::And(p, q) => Formula::_defstep(Formula::and, (*p.clone(), *q.clone()), triple),
            Formula::Or(p, q) => Formula::_defstep(Formula::or, (*p.clone(), *q.clone()), triple),
            Formula::Iff(p, q) => Formula::_defstep(Formula::iff, (*p.clone(), *q.clone()), triple),
            // Literals:
            _ => triple,
        }
    }

    const DEF_CNF_PREFIX: &'static str = "p_";
    fn _mkprop_name(idx: usize) -> String {
        format!("{}{}", Formula::DEF_CNF_PREFIX, idx)
    }
    fn _mkprop(idx: usize) -> Prop {
        Prop::new(&Formula::_mkprop_name(idx))
    }

    fn _defstep(bin_op: BinOp, operands: (Formula<Prop>, Formula<Prop>), params: Triple) -> Triple {
        // Takes owned operands and params.
        let (_current_formula, defs0, n0) = params;
        let (literal1, defs1, n1) = Formula::_main_def_cnf(&operands.0, &defs0, n0);
        let (literal2, mut defs2, n2) = Formula::_main_def_cnf(&operands.1, &defs1, n1);
        let operation = bin_op(&literal1, &literal2);
        if defs2.contains_key(&operation) {
            return (defs2[&operation].0.clone(), defs2, n2);
        }

        let atom = Formula::atom(&Self::_mkprop(n2));
        defs2.insert(
            operation.clone(),
            (atom.clone(), Formula::iff(&atom, &operation)),
        );

        (atom, defs2, n2 + 1)
    }

    fn _max_taken_index(formula: &Formula<Prop>) -> usize {
        // Walk the formula with a running maximum index
        // such thatthere is an atom with Prop name <DEF_CNF_PREFIX><numeric>
        fn max(prop: &Prop, max_so_far: usize) -> usize {
            // Is it of the form <DEF_CNF_PREFIX><numeric>;
            let re = Regex::new(&format!(
                "^{}(?P<index>[[:digit:]]*)$",
                Formula::DEF_CNF_PREFIX
            ))
            .unwrap();
            match re.captures(&prop.name) {
                Some(value) => {
                    let idx = value
                        .name("index")
                        .unwrap()
                        .as_str()
                        .parse::<usize>()
                        .unwrap();
                    std::cmp::max(idx, max_so_far)
                }
                // If the prop name doesn't match, we return the max so far.
                None => max_so_far,
            }
        }

        formula.over_atoms(&max, 0)
    }

    fn def_cnf<F>(&self, reducer: &F) -> Formula<Prop>
    where
        F: Fn(&Formula<Prop>, &Defs, usize) -> Triple,
    {
        // WARNING, this function may not have redundant (subsumed) conjuncts
        // removed  at the very last stage since this step is expensive on large formulas.
        let nenf = self.nenf();
        let n = Formula::_max_taken_index(&nenf);
        let (formula, defs, _) = reducer(&nenf, &HashMap::new(), n);
        let atom_cnf_formulaset: FormulaSet = formula.cnf_formulaset();
        let def_formulaset: FormulaSet = defs
            .iter()
            .map(|value| value.1 .1.clone())
            .map(|formula| formula.cnf_formulaset())
            .fold(FormulaSet::new(), |x, y| &x | &y);
        let result_formulaset: FormulaSet = &atom_cnf_formulaset | &def_formulaset;
        let cleaned = Formula::_strip_contradictory(&result_formulaset);
        // Note that we do not call `_strip_redundant` here because on
        // long formulas it would be slow. (`_strip_contradictory` is Theta(|formula|).)
        Formula::formulaset_to_cnf(cleaned)
    }

    fn def_cnf_full(&self) -> Formula<Prop> {
        // Apply full traversal that collects defs for every node
        // of the tree.
        // Compare to `def_cnf_opt` (optimized) below.
        self.def_cnf(&Formula::_main_def_cnf)
    }

    fn _apply_to_children<F>(
        f: F,
        bin_op: BinOp,
        operands: (Formula<Prop>, Formula<Prop>),
        params: Triple,
    ) -> Triple
    where
        F: Fn(&Formula<Prop>, &Defs, usize) -> Triple,
    {
        let (_, defs0, n0) = params;
        /* Apply `f` to both children accumulating defs as we go */
        let (formula1, defs1, n1) = f(&operands.0, &defs0, n0);
        let (formula2, defs2, n2) = f(&operands.1, &defs1, n1);
        (bin_op(&formula1, &formula2), defs2, n2)
    }

    // TODO make the triple functions consume an actual triple?
    fn _def_cnf_opt_outer_disjunctions(formula: &Formula<Prop>, defs: &Defs, idx: usize) -> Triple {
        match formula {
            Formula::Or(p, q) => Formula::_apply_to_children(
                Formula::_def_cnf_opt_outer_conjunctions,
                Formula::or,
                (*p.clone(), *q.clone()),
                (formula.clone(), defs.clone(), idx),
            ),
            _ => Formula::_main_def_cnf(formula, defs, idx),
        }
    }

    fn _def_cnf_opt_outer_conjunctions(formula: &Formula<Prop>, defs: &Defs, idx: usize) -> Triple {
        match formula {
            Formula::And(p, q) => Formula::_apply_to_children(
                Formula::_def_cnf_opt_outer_conjunctions,
                Formula::and,
                (*p.clone(), *q.clone()),
                (formula.clone(), defs.clone(), idx),
            ),
            _ => Formula::_def_cnf_opt_outer_disjunctions(formula, defs, idx),
        }
    }

    // Optimized Definitional CNF
    fn def_cnf_opt(&self) -> Formula<Prop> {
        self.def_cnf(&Formula::_def_cnf_opt_outer_conjunctions)
    }
}

#[cfg(test)]
mod def_cnf_tests {
    use super::*;

    // Convenience to save us some typing.
    fn prop(name: &str) -> Prop {
        Prop::new(name)
    }

    #[test]
    fn test_max_taken_index() {
        // Only valid taken indices are 3 and 5.
        let sentence = format!(
            "
        ((oranges /\\ (true \\/ {})) /\\ (B ==> apples)) /\\
        ((~A \\/ (false <=> {})) \\/ (D /\\ A11))
        ",
            Formula::_mkprop_name(3),
            Formula::_mkprop_name(5)
        );

        let formula = Formula::<Prop>::parse(&sentence).unwrap();
        let result = Formula::_max_taken_index(&formula);
        assert_eq!(result, 5);
    }

    #[test]
    fn test_def_cnf_full_trivial() {
        let formula = Formula::<Prop>::parse("A").unwrap();
        let result = formula.def_cnf_full();
        assert_eq!(result, formula);
    }

    #[test]
    fn test_def_cnf_opt_trivial() {
        let formula = Formula::<Prop>::parse("A").unwrap();
        let result = formula.def_cnf_opt();
        assert_eq!(result, formula);
    }

    #[test]
    fn test_def_cnf_full_nontrivial() {
        let formula = Formula::<Prop>::parse("A /\\ B").unwrap();
        let result = formula.def_cnf_full();
        let p = Formula::_mkprop_name(0);
        let desired_equiv_str = format!("{p} /\\ ({p} <=> A /\\ B)");
        let desired_equiv = Formula::<Prop>::parse(&desired_equiv_str).unwrap();
        // Since we know that `desired_equiv` is equisatisfiable with the input `formula`
        // the following shows that the result is equisatisfiable with the input `formula`.
        assert!(result.brute_equivalent(&desired_equiv));
        assert!(result.is_cnf());
    }

    #[test]
    fn test_def_cnf_opt_nontrivial() {
        let formula = Formula::<Prop>::parse("A /\\ B").unwrap();
        let result = formula.def_cnf_opt();
        assert_eq!(result, formula);
    }

    #[test]
    fn test_def_cnf_full_lesstrivial() {
        let formula = Formula::<Prop>::parse("(A ==> B) \\/ (C /\\ D)").unwrap();
        let result = formula.def_cnf_full();
        let mp0 = Formula::_mkprop_name(0);
        let mp1 = Formula::_mkprop_name(1);
        let mp2 = Formula::_mkprop_name(2);

        let desired_equiv_sentence = format!(
            "((({mp0} <=> (~A \\/ B)) /\\
        ({mp1} <=> (C /\\ D))) /\\
        ({mp2} <=> ({mp0} \\/ {mp1}))) /\\
        {mp2}",
        );

        let desired_equiv = Formula::<Prop>::parse(&desired_equiv_sentence).unwrap();

        // Since we know that `desired_equiv` is equisatisfiable with the input `formula`
        // the following shows that the result is equisatisfiable with the input `formula`.
        assert!(result.brute_equivalent(&desired_equiv));
        // Check already in cnf form
        assert!(result.is_cnf());
    }

    #[test]
    fn test_def_cnf_opt_lesstrivial() {
        let formula = Formula::<Prop>::parse("A \\/ B /\\ C").unwrap();
        let result = formula.def_cnf_opt();
        // Note the top nodes of the tree are preserved.
        let desired = Formula::<Prop>::parse("(A \\/ B) /\\ (A \\/ C)").unwrap();
        assert_eq!(result, desired);
    }
}
