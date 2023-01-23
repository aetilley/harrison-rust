// PROPOSITIONAL LOGIC
//
// parsing, printing, eval, and sat functions for
// propositional (aka sentential) logic.

use std::cmp;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt::Debug;
use std::io::Write;

use crate::formula::{parse_formula, write, Formula};
use crate::parse::{generic_parser, ErrInner, PartialParseResult};

use log::debug;
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

    fn print_propvar<W: Write>(dest: &mut W, _prec: u32, atom: &Prop) {
        // Our atom printer for propositional logic.  Note that the precedence argument is
        // simply ignored.
        write(dest, &atom.name);
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
        let mut output = Vec::new();
        let prop = Prop::new("SomeProp");
        Prop::print_propvar(&mut output, 0, &prop);
        let output = String::from_utf8(output).expect("Not UTF-8");
        assert_eq!(output, "SomeProp");

        let mut output2 = Vec::new();
        Prop::print_propvar(&mut output2, 42, &prop);
        let output2 = String::from_utf8(output2).expect("Not UTF-8");
        assert_eq!(output2, "SomeProp");
    }
}

// PARSING

impl Formula<Prop> {
    fn _atom_parser<'a>(
        variables: &[String],
        input: &'a [String],
    ) -> PartialParseResult<'a, Formula<Prop>> {
        debug!(
            "(prop)_atom_parser called on variables {:?}, input {:?}",
            variables, input
        );
        match input {
            // The conditional here seems unnecessary given how this is used in parse_formula.
            [p, rest @ ..] if p != "(" => (Formula::atom(Prop::new(p)), rest),
            _ => panic!("Failed to parse propvar."),
        }
    }

    fn _infix_parser<'a>(
        variables: &[String],
        input: &'a [String],
    ) -> Result<PartialParseResult<'a, Formula<Prop>>, ErrInner> {
        debug!(
            "(prop)_infix_parser called on variables {:?}, input {:?}",
            variables, input
        );
        Err("Infix operations not supported.")
    }

    fn _parse_prop_formula_inner(input: &[String]) -> PartialParseResult<'_, Formula<Prop>> {
        parse_formula(
            Formula::_infix_parser,
            Formula::_atom_parser,
            &[], // Bound Variables
            input,
        )
    }

    pub fn parse(input: &str) -> Formula<Prop> {
        generic_parser(Formula::_parse_prop_formula_inner, input)
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
    fn test_parse() {
        let result = Formula::<Prop>::parse("true");
        let desired = Formula::True;
        assert_eq!(result, desired);

        let result = Formula::<Prop>::parse("false");
        let desired = Formula::False;
        assert_eq!(result, desired);

        let result = Formula::<Prop>::parse("A \\/ B");
        let desired = Formula::or(Formula::atom(prop("A")), Formula::atom(prop("B")));
        assert_eq!(result, desired);

        let result = Formula::<Prop>::parse("A \\/ ~A");
        let desired = Formula::or(
            Formula::atom(prop("A")),
            Formula::not(Formula::atom(prop("A"))),
        );
        assert_eq!(result, desired);

        let result = Formula::<Prop>::parse("(A /\\ ~A)");
        let desired = Formula::and(
            Formula::atom(prop("A")),
            Formula::not(Formula::atom(prop("A"))),
        );
        assert_eq!(result, desired);

        let result = Formula::<Prop>::parse("p /\\ q /\\ p /\\ q");
        let desired = Formula::and(
            Formula::atom(prop("p")),
            Formula::and(
                Formula::atom(prop("q")),
                Formula::and(Formula::atom(prop("p")), Formula::atom(prop("q"))),
            ),
        );
        assert_eq!(result, desired);

        let result = Formula::<Prop>::parse("a <=> (b /\\ c)");
        let desired = Formula::iff(
            Formula::atom(Prop::new("a")),
            Formula::and(Formula::atom(Prop::new("b")), Formula::atom(Prop::new("c"))),
        );
        assert_eq!(result, desired);

        let result = Formula::<Prop>::parse("(p /\\ q) /\\ q ==> (p /\\ q) /\\ q");
        let desired = Formula::imp(
            Formula::and(
                Formula::and(Formula::atom(prop("p")), Formula::atom(prop("q"))),
                Formula::atom(prop("q")),
            ),
            Formula::and(
                Formula::and(Formula::atom(prop("p")), Formula::atom(prop("q"))),
                Formula::atom(prop("q")),
            ),
        );
        assert_eq!(result, desired);

        let result = Formula::<Prop>::parse("a /\\ ~b \\/ (~c \\/ d)");
        let desired = Formula::or(
            Formula::and(
                Formula::atom(prop("a")),
                Formula::not(Formula::atom(prop("b"))),
            ),
            Formula::or(
                Formula::not(Formula::atom(prop("c"))),
                Formula::atom(prop("d")),
            ),
        );
        assert_eq!(result, desired);

        let result = Formula::<Prop>::parse("~(~A)");
        let desired = Formula::not(Formula::not(Formula::atom(prop("A"))));
        assert_eq!(result, desired);

        let result = Formula::<Prop>::parse("A /\\ (false \\/ B)");
        let desired = Formula::and(
            Formula::atom(prop("A")),
            Formula::or(Formula::False, Formula::atom(prop("B"))),
        );
        assert_eq!(result, desired);

        let result = Formula::<Prop>::parse("~(A ==> (B <=> C))");
        let desired = Formula::not(Formula::imp(
            Formula::atom(prop("A")),
            Formula::iff(Formula::atom(prop("B")), Formula::atom(prop("C"))),
        ));
        assert_eq!(result, desired);
    }

    // TODO Currently can't handle double (consecutive w/o parens) negation
    // since tokenizer groups "~~" as one token.
    // #[test]
    // fn double_neg() {
    //     env_logger::init();
    //     let result = Formula::<Prop>::parse("~~A");
    //     let desired = Formula::not(Formula::not(Formula::atom(prop("A"))));
    //     assert_eq!(result, desired);
    // }
}

// PRINTING

impl Formula<Prop> {
    pub fn pprint<W: Write>(&self, dest: &mut W) {
        let pfn: fn(&mut W, u32, &Prop) -> () = Prop::print_propvar;
        self.pprint_general(dest, &pfn);
        write(dest, "\n");
    }
}

#[cfg(test)]
mod prop_formula_print_tests {
    use super::*;

    fn init() {
        let _ = env_logger::builder().is_test(true).try_init();
    }

    #[test]
    fn test_pprint() {
        let formula = Formula::and(
            Formula::atom(Prop::new("Prop5")),
            Formula::iff(
                Formula::atom(Prop::new("Prop2")),
                Formula::imp(
                    Formula::or(
                        Formula::atom(Prop::new("Prop3")),
                        Formula::atom(Prop::new("Prop4")),
                    ),
                    Formula::atom(Prop::new("Prop1")),
                ),
            ),
        );
        let mut output = Vec::new();
        formula.pprint(&mut output);
        let output = String::from_utf8(output).expect("Not UTF-8");
        assert_eq!(
            output,
            "<<Prop5 /\\ (Prop2 <=> Prop3 \\/ Prop4 ==> Prop1)>>\n"
        );
    }
}

// Propositional Eval

// We use a BTreeMap here so that we can order the items by Prop.name
// (mostly for being able to test truthtable output).
type Valuation = BTreeMap<Prop, bool>;

impl Prop {
    fn eval(&self, val: &Valuation) -> bool {
        match val.get(self) {
            Some(b) => b.to_owned(),
            None => panic!("Valuation is not defined on prop {:?}", &self),
        }
    }
}

// Propositional Formula Eval
impl Formula<Prop> {
    fn eval(&self, val: &Valuation) -> bool {
        // NOTE:  We could just as well give trivial definitions for when a propositional
        // formula is quantified, but for now we'll just panic.
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

        formula = Formula::<Prop>::parse("A");
        assert!(formula.eval(&val));

        formula = Formula::<Prop>::parse("B");
        assert!(!formula.eval(&val));

        formula = Formula::<Prop>::parse("C <=> A /\\ B");
        assert!(!formula.eval(&val));
    }
}

// ### Core SAT definitions (ie. brute-force algorithms).

impl Formula<Prop> {
    fn get_all_valuations(atoms: &HashSet<Prop>) -> Vec<Valuation> {
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

    pub fn print_truthtable(&self, dest: &mut impl Write) {
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
        let make_row = |val: &Valuation| {
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
        let result = format!("{header}\n{separator}\n{body}{separator}\n");
        write(dest, &result);
    }

    // TODO prefix the below with, e.g., "naive_" or "brute_force_" in order to
    // discourage use.
    pub fn tautology(&self) -> bool {
        // NOTE:  SLOW, USE OTHER VERSIONS.
        // Note that the set of valuations should never be empty
        // (Event `True` has the empty valuation.)
        Formula::get_all_valuations(&self.atoms())
            .iter()
            .map(|x| self.eval(x))
            .all(|y| y)
    }

    pub fn equivalent(&self, formula: &Formula<Prop>) -> bool {
        // NOTE:  SLOW, USE OTHER VERSIONS.
        let target = Formula::iff(self.clone(), formula.clone());
        target.tautology()
    }

    pub fn unsatisfiable(&self) -> bool {
        // NOTE:  SLOW, USE OTHER VERSIONS.
        Formula::not(self.clone()).tautology()
    }

    pub fn satisfiable(&self) -> bool {
        // NOTE:  SLOW, USE OTHER VERSIONS.
        !self.unsatisfiable()
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
        let formula = Formula::<Prop>::parse("C <=> A /\\ B");
        let mut output = Vec::new();
        formula.print_truthtable(&mut output);
        let output = String::from_utf8(output).expect("Not UTF-8");
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
    fn test_tautology_and_satisfiable() {
        let form1 = Formula::<Prop>::parse("true");
        assert!(form1.tautology());
        assert!(!form1.unsatisfiable());
        assert!(form1.satisfiable());

        let form2 = Formula::<Prop>::parse("A \\/ B");
        assert!(!form2.tautology());
        assert!(!form2.unsatisfiable());
        assert!(form2.satisfiable());

        let form3 = Formula::<Prop>::parse("A \\/ ~A");
        assert!(form3.tautology());
        assert!(!form3.unsatisfiable());
        assert!(form3.satisfiable());

        let form4 = Formula::<Prop>::parse("A /\\ ~A");
        assert!(!form4.tautology());
        assert!(form4.unsatisfiable());
        assert!(!form4.satisfiable());
    }
}

// ### Normal Forms

// Set representations of Formulas in disjunctive or conjunctive normal form
// (we need to specify in order to have a unique meaning)..
// Note we could replace the inner `Formula<Prop>` by an indicator
// function on `Prop` (or just a set of type Valuation), which would prevent
// non-literals from going in there.
// In the meantime, we use a BTreeSet here so that we can order the items
// by Prop.name.
pub type FormulaSet = BTreeSet<BTreeSet<Formula<Prop>>>;

impl Formula<Prop> {
    fn psubst(&self, subfn: &HashMap<Prop, Formula<Prop>>) -> Formula<Prop> {
        // Replace each Atom(prop) with a subformula given by `subfn(prop)`.
        let map = |p: &Prop| subfn.get(p).unwrap_or(&Formula::atom(p.clone())).clone();
        self.on_atoms(&map)
    }

    fn dual(&self) -> Formula<Prop> {
        match self {
            Formula::False => Formula::True,
            Formula::True => Formula::False,
            Formula::Atom(_) => self.clone(),
            Formula::Not(p) => Formula::not(p.dual()),
            Formula::And(p, q) => Formula::or(p.dual(), q.dual()),
            Formula::Or(p, q) => Formula::and(p.dual(), q.dual()),
            _ => panic!("Formula involves connectives '==>' or '<=>'"),
        }
    }

    fn nnf(&self) -> Formula<Prop> {
        // Negation normal form
        let simplified = self.psimplify();

        match simplified {
            Formula::And(box p, box q) => Formula::and(p.nnf(), q.nnf()),
            Formula::Or(box p, box q) => Formula::or(p.nnf(), q.nnf()),
            Formula::Imp(box p, box q) => Formula::or(Formula::not(p).nnf(), q.nnf()),
            Formula::Iff(box p, box q) => Formula::and(
                Formula::or(Formula::not(p.clone()).nnf(), q.nnf()),
                Formula::or(Formula::not(q).nnf(), p.nnf()),
            ),
            Formula::Not(box Formula::Not(box p)) => p.nnf(),
            Formula::Not(box Formula::And(box p, box q)) => {
                Formula::or(Formula::not(p).nnf(), Formula::not(q).nnf())
            }
            Formula::Not(box Formula::Or(box p, box q)) => {
                Formula::and(Formula::not(p).nnf(), Formula::not(q).nnf())
            }
            Formula::Not(box Formula::Imp(box p, box q)) => {
                Formula::and(p.nnf(), Formula::not(q).nnf())
            }
            Formula::Not(box Formula::Iff(box p, box q)) => Formula::or(
                Formula::and(p.nnf(), Formula::not(q.clone()).nnf()),
                Formula::and(Formula::not(p).nnf(), q.nnf()),
            ),
            _ => simplified,
        }
    }

    fn nenf(&self) -> Formula<Prop> {
        // Negation and normal form also allowing equivalences (iff).
        let simplified = self.psimplify();

        match simplified {
            Formula::And(box p, box q) => Formula::and(p.nenf(), q.nenf()),
            Formula::Or(box p, box q) => Formula::or(p.nenf(), q.nenf()),
            Formula::Imp(box p, box q) => Formula::or(Formula::not(p).nenf(), q.nenf()),
            Formula::Iff(box p, box q) => Formula::iff(p.nenf(), q.nenf()),
            Formula::Not(box Formula::Not(box p)) => p.nenf(),
            Formula::Not(box Formula::And(box p, box q)) => {
                Formula::or(Formula::not(p).nenf(), Formula::not(q).nenf())
            }
            Formula::Not(box Formula::Or(box p, box q)) => {
                Formula::and(Formula::not(p).nenf(), Formula::not(q).nenf())
            }
            Formula::Not(box Formula::Imp(box p, box q)) => {
                Formula::and(p.nenf(), Formula::not(q).nenf())
            }
            Formula::Not(box Formula::Iff(box p, box q)) => Formula::iff(p, Formula::not(q)),
            _ => simplified,
        }
    }

    fn _set_distrib_and_over_or(formula1: &FormulaSet, formula2: &FormulaSet) -> FormulaSet {
        // FIX do this w/ maps?
        let mut result = FormulaSet::new();
        for conj1 in formula1 {
            for conj2 in formula2 {
                result.insert(conj1 | conj2);
            }
        }
        result
    }

    fn _purednf(&self) -> FormulaSet {
        // WARNING, assumes self is already in NNF!
        // DNF by converting formulas to set of sets representation.
        let nnf = self.nnf();
        match nnf {
            Formula::False => FormulaSet::new(),
            Formula::True => BTreeSet::from([BTreeSet::new()]),
            Formula::Atom(_) | Formula::Not(_) => BTreeSet::from([BTreeSet::from([nnf.clone()])]),
            Formula::And(box p, box q) => {
                Formula::_set_distrib_and_over_or(&p._purednf(), &q._purednf())
            }
            Formula::Or(box p, box q) => &p._purednf() | &q._purednf(),
            _ => panic!("Unrecognized formula type {nnf:?} for _puredfn."),
        }
    }

    fn _purecnf(&self) -> FormulaSet {
        // WARNING, assumes self is already in NNF!
        // DNF by converting formulas to set of sets representation.
        // NOTE that representation of the result is not the same as the representation of
        // intermediate results.
        let negation_in_purednf: FormulaSet = Formula::not(self.clone())._purednf();
        // distribute matching negation from outside (and assuming dual representation).
        let result: FormulaSet = negation_in_purednf
            .iter()
            .map(|conjunction| conjunction.iter().map(|lit| lit.negate()).collect())
            .collect();
        result
    }

    fn _negative(formula: &Formula<Prop>) -> bool {
        matches!(formula, Formula::Not(_))
    }

    fn _positive(formula: &Formula<Prop>) -> bool {
        // NOTE: that the way _negative and _positive are defined,
        // every non-literal will count as `_positive`.
        !Formula::_negative(formula)
    }

    fn _contradictory_lits(lits: &BTreeSet<Formula<Prop>>) -> bool {
        // Whether `lits` contains two literals of the form `p` and `~p`.
        let pos: BTreeSet<Formula<Prop>> = lits
            .iter()
            .filter(|x| Formula::_positive(x))
            .cloned()
            .collect();

        let neg: BTreeSet<Formula<Prop>> = lits
            .iter()
            .filter(|x| Formula::_negative(x))
            .map(|lit| lit.negate())
            .collect();

        pos.intersection(&neg).count() != 0
    }

    fn _strip_supersets(formula: &FormulaSet) -> FormulaSet {
        // Remove all inner sets that contain other inner sets.
        let mut result = FormulaSet::new();
        for conj1 in formula {
            let mut keep = true;
            for conj2 in formula {
                if conj2 == conj1 {
                    continue;
                } else if conj1.is_superset(conj2) {
                    // This must be proper containment.
                    keep = false;
                    break;
                } else {
                }
            }
            if keep {
                result.insert(conj1.clone());
            }
        }
        result
    }

    fn _strip_contradictory(formula_set: &FormulaSet) -> FormulaSet {
        // filter by non contradictory_lits
        formula_set
            .iter()
            .filter(|x| !Formula::_contradictory_lits(x))
            .cloned()
            .collect()
    }

    fn _formulaset_to_dnf(formula_set: FormulaSet) -> Formula<Prop> {
        let partial: Vec<Formula<Prop>> = formula_set
            .into_iter()
            .map(Vec::from_iter)
            .map(|conj| Formula::list_conj(&conj))
            .collect();
        Formula::list_disj(&partial)
    }

    fn _formulaset_to_cnf(formula_set: FormulaSet) -> Formula<Prop> {
        let partial: Vec<Formula<Prop>> = formula_set
            .into_iter()
            .map(Vec::from_iter)
            .map(|conj| Formula::list_disj(&conj))
            .collect();
        Formula::list_conj(&partial)
    }

    fn _is_disjunction_of_literals(&self) -> bool {
        match self {
            Formula::Atom(_) | Formula::Not(box Formula::Atom(_)) => true,
            Formula::Or(box p, box q) => {
                p._is_disjunction_of_literals() && q._is_disjunction_of_literals()
            }
            _ => false,
        }
    }

    fn is_cnf(&self) -> bool {
        if Formula::_is_disjunction_of_literals(self) {
            return true;
        }
        match self {
            Formula::And(box p, box q) => p.is_cnf() && q.is_cnf(),
            _ => false,
        }
    }

    fn _dnf_formulaset(&self) -> FormulaSet {
        // Note that a formula is a non-satisfiable iff this function returns Formula::False
        // (the empty disjunction).
        let formula_set = self._purednf();
        Formula::_strip_contradictory(&Formula::_strip_supersets(&formula_set))
    }

    fn _cnf_formulaset(&self) -> FormulaSet {
        // Note that a formula is a tautology iff this function returns Formula::True
        // (the empty conjunction)
        let formula_set = self._purecnf();
        Formula::_strip_contradictory(&Formula::_strip_supersets(&formula_set))
    }

    pub fn cnf(&self) -> Formula<Prop> {
        // Note that a formula is a tautology iff this function returns Formula::True
        // (the empty conjunction)
        let formula_set = self._cnf_formulaset();
        Formula::_formulaset_to_cnf(formula_set)
    }

    pub fn dnf(&self) -> Formula<Prop> {
        // Note that a formula is a non-satisfiable iff this function returns Formula::False
        // (the empty disjunction).
        let formula_set = self._dnf_formulaset();
        Formula::_formulaset_to_dnf(formula_set)
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
        let map = HashMap::from([(prop("p"), Formula::<Prop>::parse("p /\\ q"))]);
        let formula = Formula::<Prop>::parse("p /\\ q ==> p /\\ q");
        let result = formula.psubst(&map);
        let desired = Formula::<Prop>::parse("(p /\\ q) /\\ q ==> (p /\\ q) /\\ q");
        assert_eq!(result, desired)
    }

    #[test]
    fn test_dual() {
        let formula = Formula::<Prop>::parse("(a /\\ ~b) \\/ (~c \\/ d)");
        let desired = Formula::<Prop>::parse("(a \\/ ~b ) /\\ (~c /\\ d)");
        assert_eq!(formula.dual(), desired);
    }
    #[test]
    fn test_nnf() {
        let formula = Formula::<Prop>::parse("~(~A) /\\ (false \\/ B)");
        let desired = Formula::<Prop>::parse("A /\\ B");
        assert_eq!(formula.nnf(), desired);

        let formula = Formula::<Prop>::parse("~(A /\\ (B \\/ C))");
        let desired = Formula::<Prop>::parse("~A \\/ (~B /\\ ~C)");

        assert_eq!(formula.nnf(), desired);

        let formula = Formula::<Prop>::parse("~(A ==> (B <=> C))");
        let desired = Formula::<Prop>::parse("A /\\ (B /\\ ~C \\/ ~B /\\ C)");
        assert_eq!(formula.nnf(), desired);
    }

    #[test]
    fn test_nenf() {
        let formula = Formula::<Prop>::parse("~(A /\\ (B \\/ C))");
        let desired = Formula::<Prop>::parse("~A \\/ (~B /\\ ~C)");
        assert_eq!(formula.nenf(), desired);

        let formula = Formula::<Prop>::parse("~(A ==> (B <=> C))");
        let desired = Formula::<Prop>::parse("A /\\ (B <=> ~C)");
        assert_eq!(formula.nenf(), desired);
    }

    #[test]
    fn test_set_distrib_and_over_or() {
        let formula1 = BTreeSet::from([
            BTreeSet::from([Formula::atom(prop("A")), Formula::atom(prop("B"))]),
            BTreeSet::from([Formula::atom(prop("B")), Formula::atom(prop("C"))]),
        ]);
        let formula2 = BTreeSet::from([
            BTreeSet::from([Formula::atom(prop("A"))]),
            BTreeSet::from([Formula::atom(prop("D")), Formula::atom(prop("C"))]),
        ]);

        let desired = BTreeSet::from([
            BTreeSet::from([Formula::atom(prop("A")), Formula::atom(prop("B"))]),
            BTreeSet::from([
                Formula::atom(prop("A")),
                Formula::atom(prop("B")),
                Formula::atom(prop("D")),
                Formula::atom(prop("C")),
            ]),
            BTreeSet::from([
                Formula::atom(prop("B")),
                Formula::atom(prop("C")),
                Formula::atom(prop("A")),
            ]),
            BTreeSet::from([
                Formula::atom(prop("B")),
                Formula::atom(prop("C")),
                Formula::atom(prop("D")),
            ]),
        ]);
        let result = Formula::_set_distrib_and_over_or(&formula1, &formula2);
        assert_eq!(result, desired);
    }

    #[test]
    fn test_purednf() {
        let formula = Formula::<Prop>::parse(
            "false \\/ (((A /\\ true) \\/ (B /\\ C)) /\\ (A \\/ (D /\\ C)))",
        );
        let result = formula._purednf();
        let desired = BTreeSet::from([
            BTreeSet::from([Formula::atom(prop("A"))]),
            BTreeSet::from([
                Formula::atom(prop("A")),
                Formula::atom(prop("D")),
                Formula::atom(prop("C")),
            ]),
            BTreeSet::from([
                Formula::atom(prop("B")),
                Formula::atom(prop("C")),
                Formula::atom(prop("A")),
            ]),
            BTreeSet::from([
                Formula::atom(prop("B")),
                Formula::atom(prop("C")),
                Formula::atom(prop("D")),
            ]),
        ]);
        assert_eq!(result, desired);

        // Trivial:
        let result_true = (Formula::True)._purednf();
        let result_false = (Formula::False)._purednf();
        assert_eq!(result_true, BTreeSet::from([BTreeSet::from([])]));
        assert_eq!(result_false, BTreeSet::from([]));
    }

    #[test]
    fn test_purecnf() {
        let sentence = "
            ((A /\\ (true \\/ E)) \\/ (B /\\ C)) /\\
            ((~A \\/ (false /\\ F)) \\/ (D /\\ C))
            ";
        let formula = Formula::<Prop>::parse(sentence);
        let desired = BTreeSet::from([
            BTreeSet::from([Formula::atom(prop("A")), Formula::atom(prop("B"))]),
            BTreeSet::from([Formula::atom(prop("A")), Formula::atom(prop("C"))]),
            BTreeSet::from([
                Formula::not(Formula::atom(prop("A"))),
                Formula::atom(prop("D")),
            ]),
            BTreeSet::from([
                Formula::not(Formula::atom(prop("A"))),
                Formula::atom(prop("C")),
            ]),
        ]);
        assert_eq!(formula._purecnf(), desired);

        let result_true = (Formula::True)._purecnf();
        let result_false = (Formula::False)._purecnf();
        assert_eq!(result_false, BTreeSet::from([BTreeSet::from([])]));
        assert_eq!(result_true, BTreeSet::from([]));
    }
    #[test]
    fn test_contradictory_lits() {
        let lits1 = BTreeSet::from([Formula::atom(prop("A")), Formula::atom(prop("B"))]);
        let lits2 = BTreeSet::from([
            Formula::atom(prop("A")),
            Formula::atom(prop("B")),
            Formula::not(Formula::atom(prop("A"))),
        ]);

        assert!(!Formula::_contradictory_lits(&lits1));
        assert!(Formula::_contradictory_lits(&lits2));
    }

    #[test]
    fn test_strip_supersets() {
        let formula = BTreeSet::from([
            BTreeSet::from([
                Formula::atom(prop("A")),
                Formula::atom(prop("B")),
                Formula::atom(prop("D")),
                Formula::atom(prop("C")),
            ]),
            BTreeSet::from([
                Formula::atom(prop("B")),
                Formula::atom(prop("C")),
                Formula::atom(prop("A")),
            ]),
            BTreeSet::from([
                Formula::atom(prop("A")),
                Formula::atom(prop("B")),
                Formula::atom(prop("D")),
                Formula::atom(prop("C")),
                Formula::atom(prop("E")),
            ]),
            BTreeSet::from([
                Formula::atom(prop("B")),
                Formula::atom(prop("C")),
                Formula::atom(prop("E")),
            ]),
        ]);

        let desired = BTreeSet::from([
            BTreeSet::from([
                Formula::atom(prop("B")),
                Formula::atom(prop("C")),
                Formula::atom(prop("A")),
            ]),
            BTreeSet::from([
                Formula::atom(prop("B")),
                Formula::atom(prop("C")),
                Formula::atom(prop("E")),
            ]),
        ]);
        let result = Formula::_strip_supersets(&formula);
        assert_eq!(result, desired);
    }

    #[test]
    fn test_dnf() {
        let formula = Formula::<Prop>::parse("((A /\\ true) \\/ (B /\\ ~B)) /\\ (B \\/ (D /\\ C))");
        let result = formula.dnf();
        let desired = Formula::<Prop>::parse("(A /\\ B) \\/ ((A /\\ C) /\\ D)");

        assert_eq!(result, desired);
    }

    #[test]
    fn test_dnf_unsatisfiable() {
        // Should be False on contradictions.
        let formula = Formula::<Prop>::parse("P /\\ ~P");
        assert_eq!(formula.dnf(), Formula::False);
    }

    #[test]
    fn test_cnf_tautology() {
        // Should be True on tautologies.
        let formula = Formula::<Prop>::parse("P \\/ ~P");
        assert_eq!(formula.cnf(), Formula::True);
    }

    #[test]
    fn test_cnf() {
        let sentence = "
            ((A /\\ (true \\/ E)) \\/ (B /\\ C)) /\\
            ((~A \\/ (false /\\ F)) \\/ (D /\\ C))
            ";
        let formula = Formula::<Prop>::parse(sentence);

        let desired_sentence = "(((A \\/ B) /\\ (A \\/C)) /\\ (C \\/ ~A)) /\\ (D \\/ ~A)";
        let desired = Formula::<Prop>::parse(desired_sentence);
        assert_eq!(formula.cnf(), desired);
    }

    #[test]
    fn test_is_cnf() {
        // YES
        let formula = Formula::<Prop>::parse("~A /\\ B");
        assert!(formula.is_cnf());
        // YES
        let formula = Formula::<Prop>::parse("~A \\/ B");
        assert!(formula.is_cnf());
        // No
        let formula = Formula::<Prop>::parse("(A /\\ C) \\/ B");
        assert!(!formula.is_cnf());
        // YES
        let formula = Formula::<Prop>::parse("((D \\/ A) \\/ C) /\\ B");
        assert!(formula.is_cnf());
    }
}

// ### Definitional CNF

type Triple = (Formula<Prop>, Defs, usize);
type BinOp = fn(Formula<Prop>, Formula<Prop>) -> Formula<Prop>;
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
            Formula::And(box p, box q) => {
                Formula::_defstep(Formula::and, (p.clone(), q.clone()), triple)
            }
            Formula::Or(box p, box q) => {
                Formula::_defstep(Formula::or, (p.clone(), q.clone()), triple)
            }
            Formula::Iff(box p, box q) => {
                Formula::_defstep(Formula::iff, (p.clone(), q.clone()), triple)
            }
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
        let operation = bin_op(literal1, literal2);
        if defs2.contains_key(&operation) {
            return (defs2[&operation].0.clone(), defs2, n2);
        }

        let atom = Formula::atom(Self::_mkprop(n2));
        defs2.insert(
            operation.clone(),
            (atom.clone(), Formula::iff(atom.clone(), operation)),
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
        let atom_cnf_formulaset: FormulaSet = formula._cnf_formulaset();
        let def_formulaset: FormulaSet = defs
            .iter()
            .map(|value| value.1 .1.clone())
            .map(|formula| formula._cnf_formulaset())
            .fold(FormulaSet::new(), |x, y| &x | &y);
        let result_formulaset: FormulaSet = &atom_cnf_formulaset | &def_formulaset;
        let cleaned = Formula::_strip_contradictory(&result_formulaset);
        // Note that we do not call `_strip_redundant` here because on
        // long formulas it would be slow. (`_strip_contradictory` is Theta(|formula|).)
        Formula::_formulaset_to_cnf(cleaned)
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
        (bin_op(formula1, formula2), defs2, n2)
    }

    // TODO make the triple functions consume an actual triple?
    fn _def_cnf_opt_outer_disjunctions(formula: &Formula<Prop>, defs: &Defs, idx: usize) -> Triple {
        match formula {
            Formula::Or(box p, box q) => Formula::_apply_to_children(
                Formula::_def_cnf_opt_outer_conjunctions,
                Formula::or,
                (p.clone(), q.clone()),
                (formula.clone(), defs.clone(), idx),
            ),
            _ => Formula::_main_def_cnf(formula, defs, idx),
        }
    }

    fn _def_cnf_opt_outer_conjunctions(formula: &Formula<Prop>, defs: &Defs, idx: usize) -> Triple {
        match formula {
            Formula::And(box p, box q) => Formula::_apply_to_children(
                Formula::_def_cnf_opt_outer_conjunctions,
                Formula::and,
                (p.clone(), q.clone()),
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
        ((~A \\/ (false <=> {})) \\/ (D /\\ 11))
        ",
            Formula::_mkprop_name(3),
            Formula::_mkprop_name(5)
        );

        let formula = Formula::<Prop>::parse(&sentence);
        let result = Formula::_max_taken_index(&formula);
        assert_eq!(result, 5);
    }

    #[test]
    fn test_def_cnf_full_trivial() {
        let formula = Formula::<Prop>::parse("A");
        let result = formula.def_cnf_full();
        assert_eq!(result, formula);
    }

    #[test]
    fn test_def_cnf_opt_trivial() {
        let formula = Formula::<Prop>::parse("A");
        let result = formula.def_cnf_opt();
        assert_eq!(result, formula);
    }

    #[test]
    fn test_def_cnf_full_nontrivial() {
        let formula = Formula::<Prop>::parse("A /\\ B");
        let result = formula.def_cnf_full();
        let p = Formula::_mkprop_name(0);
        let desired_equiv_str = format!("{p} /\\ ({p} <=> A /\\ B)");
        let desired_equiv = Formula::<Prop>::parse(&desired_equiv_str);
        // Since we know that `desired_equiv` is equisatisfiable with the input `formula`
        // the following shows that the result is equisatisfiable with the input `formula`.
        assert!(result.equivalent(&desired_equiv));
        assert!(result.is_cnf());
    }

    #[test]
    fn test_def_cnf_opt_nontrivial() {
        let formula = Formula::<Prop>::parse("A /\\ B");
        let result = formula.def_cnf_opt();
        assert_eq!(result, formula);
    }

    #[test]
    fn test_def_cnf_full_lesstrivial() {
        let formula = Formula::<Prop>::parse("(A ==> B) \\/ (C /\\ D)");
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

        let desired_equiv = Formula::<Prop>::parse(&desired_equiv_sentence);

        // Since we know that `desired_equiv` is equisatisfiable with the input `formula`
        // the following shows that the result is equisatisfiable with the input `formula`.
        assert!(result.equivalent(&desired_equiv));
        // Check already in cnf form
        assert!(result.is_cnf());
    }

    #[test]
    fn test_def_cnf_opt_lesstrivial() {
        let formula = Formula::<Prop>::parse("A \\/ B /\\ C");
        let result = formula.def_cnf_opt();
        // Note the top nodes of the tree are preserved.
        let desired = Formula::<Prop>::parse("(A \\/ B) /\\ (A \\/ C)");
        assert_eq!(result, desired);
    }
}

// ### Davis-Putnam (DP)
impl Formula<Prop> {
    fn _one_literal_rule(clauses: &FormulaSet) -> Result<FormulaSet, ErrInner> {
        for clause in clauses {
            if clause.len() == 1 {
                let clause_vec: Vec<Formula<Prop>> = Vec::from_iter(clause.clone());
                let literal = clause_vec[0].clone();
                let negation = literal.negate();
                let result: FormulaSet = clauses
                    .iter()
                    .filter(|c| !c.contains(&literal))
                    .cloned()
                    .collect();
                let result: FormulaSet = result
                    .iter()
                    // FIX:  image instead of map?
                    .map(|clause| {
                        clause
                            .difference(&BTreeSet::from([negation.clone()]))
                            .cloned()
                            .collect()
                    })
                    .collect();
                return Ok(result);
            }
        }
        Err("No unit clauses found.")
    }

    fn _affirmative_negative_rule(clauses: &FormulaSet) -> Result<FormulaSet, ErrInner> {
        // Remove all clauses that contain literals that occur either all positively or
        // all negatively.
        let all_literals: BTreeSet<Formula<Prop>> =
            clauses.iter().fold(BTreeSet::new(), |x, y| &x | y);
        let (negative, positive): (BTreeSet<Formula<Prop>>, BTreeSet<Formula<Prop>>) =
            all_literals.into_iter().partition(Formula::negative);
        let unnegated: BTreeSet<Formula<Prop>> = negative
            .into_iter()
            .map(|neg| Formula::negate(&neg))
            .collect();
        let positive_only: BTreeSet<Formula<Prop>> =
            positive.difference(&unnegated).cloned().collect();
        let negative_only: BTreeSet<Formula<Prop>> =
            unnegated.difference(&positive).cloned().collect();
        let renegated: BTreeSet<Formula<Prop>> = negative_only
            .into_iter()
            .map(|neg| Formula::negate(&neg))
            .collect();
        let pure: BTreeSet<Formula<Prop>> = &positive_only | &renegated;

        if pure.is_empty() {
            Err("No strictly positively or strictly negatively occurring literals.")
        } else {
            let value: FormulaSet = clauses
                .iter()
                .filter(|clause| {
                    clause
                        .intersection(&pure)
                        .collect::<BTreeSet<_>>()
                        .is_empty()
                })
                .cloned()
                .collect();
            Ok(value)
        }
    }

    // For _resolution_rule (DP only).
    fn _resolve_atom(clauses: &FormulaSet, literal: &Formula<Prop>) -> FormulaSet {
        let clauses = Formula::_strip_contradictory(clauses);
        let (contains_literal, doesnt_contain_literal): (FormulaSet, FormulaSet) = clauses
            .into_iter()
            .partition(|clause| clause.contains(literal));
        let negated = &Formula::negate(literal);
        // We'll come back to `contains_neither` at the end.
        let (contains_negation, contains_neither): (FormulaSet, FormulaSet) =
            doesnt_contain_literal
                .into_iter()
                .partition(|clause| clause.contains(negated));

        // Now get copies of the clauses with p and ~p removed.
        let literal_complements: FormulaSet = contains_literal
            .iter()
            .map(|clause| {
                clause
                    .difference(&BTreeSet::from([literal.clone()]))
                    .cloned()
                    .collect()
            })
            .collect();
        let negation_complements: FormulaSet = contains_negation
            .iter()
            .map(|clause| {
                clause
                    .difference(&BTreeSet::from([negated.clone()]))
                    .cloned()
                    .collect()
            })
            .collect();
        let mut result = FormulaSet::new();
        for literal_comp in literal_complements.iter() {
            for negation_comp in negation_complements.iter() {
                result.insert(literal_comp | negation_comp);
            }
        }
        &Formula::_strip_contradictory(&result) | &contains_neither
    }

    fn _counts_containing_literal_and_negation(
        clauses: &FormulaSet,
        literal: &Formula<Prop>,
    ) -> (isize, isize) {
        let num_containing_lit = clauses
            .iter()
            .filter(|clause| clause.contains(literal))
            .count() as isize;
        let negated = &Formula::negate(literal);
        let num_containing_neg = clauses
            .iter()
            .filter(|clause| clause.contains(negated))
            .count() as isize;
        (num_containing_lit, num_containing_neg)
    }

    fn _atom_resolution_cost(clauses: &FormulaSet, literal: &Formula<Prop>) -> isize {
        let (num_containing_lit, num_containing_neg) =
            Formula::_counts_containing_literal_and_negation(clauses, literal);

        num_containing_lit * num_containing_neg - (num_containing_lit + num_containing_neg)
    }

    fn _find_min<F>(obj: &F, domain: &BTreeSet<Formula<Prop>>) -> Option<Formula<Prop>>
    where
        F: Fn(&Formula<Prop>) -> isize,
    {
        // Returns the input that minimizes `obj` */
        if domain.is_empty() {
            return None;
        }
        let mut minimizing_input: Formula<Prop> = Vec::from_iter(domain)[0].clone();
        let mut min_value = obj(&minimizing_input);
        for atom in domain {
            let atom_value = obj(atom);
            if atom_value < min_value {
                minimizing_input = atom.clone();
                min_value = atom_value;
            }
        }
        Some(minimizing_input)
    }

    fn _resolution_rule(clauses: &FormulaSet) -> FormulaSet {
        // Resolve whichever atom is cheapest.
        let positive_literals: BTreeSet<Formula<Prop>> = clauses
            .iter()
            .fold(BTreeSet::new(), |x, y| &x | y)
            .into_iter()
            .filter(|literal| !Formula::negative(literal))
            .collect();
        let obj = |literal: &Formula<Prop>| Formula::_atom_resolution_cost(clauses, literal);
        let literal = Formula::_find_min(&obj, &positive_literals)
            .expect("positive_literals should be non-empty");
        Formula::_resolve_atom(clauses, &literal)
    }

    pub fn dp(clauses: &FormulaSet) -> bool {
        // The Davis-Putnam (1960) procedure.
        // Intended to be run on a FormulaSet representing a CNF formula.
        if clauses.is_empty() {
            return true;
        }
        if clauses.contains(&BTreeSet::new()) {
            return false;
        }
        if let Ok(next) = Formula::_one_literal_rule(clauses) {
            return Formula::dp(&next);
        }
        if let Ok(next) = Formula::_affirmative_negative_rule(clauses) {
            return Formula::dp(&next);
        }
        let next = Formula::_resolution_rule(clauses);
        Formula::dp(&next)
    }

    pub fn dp_sat(&self) -> bool {
        Formula::dp(&Formula::_cnf_formulaset(self))
    }
    pub fn dp_taut(&self) -> bool {
        !Formula::dp_sat(&Formula::not(self.clone()))
    }
}

#[cfg(test)]
mod dp_tests {
    use super::*;

    // Convenience to save us some typing.
    fn prop(name: &str) -> Prop {
        Prop::new(name)
    }
    #[test]
    fn test_one_literal_rule() {
        let formula_set = BTreeSet::from([
            BTreeSet::from([Formula::atom(prop("A"))]),
            BTreeSet::from([Formula::atom(prop("B")), Formula::atom(prop("C"))]),
            BTreeSet::from([Formula::atom(prop("A")), Formula::atom(prop("C"))]),
            BTreeSet::from([
                Formula::not(Formula::atom(prop("A"))),
                Formula::atom(prop("C")),
            ]),
        ]);
        let desired = BTreeSet::from([
            BTreeSet::from([Formula::atom(prop("B")), Formula::atom(prop("C"))]),
            BTreeSet::from([Formula::atom(prop("C"))]),
        ]);

        let result = Formula::_one_literal_rule(&formula_set);
        assert_eq!(result, Ok(desired));

        let formula_set_no_unit = BTreeSet::from([
            BTreeSet::from([Formula::atom(prop("B")), Formula::atom(prop("C"))]),
            BTreeSet::from([Formula::atom(prop("A")), Formula::atom(prop("C"))]),
            BTreeSet::from([
                Formula::not(Formula::atom(prop("A"))),
                Formula::atom(prop("C")),
            ]),
        ]);
        let result = Formula::_one_literal_rule(&formula_set_no_unit);
        assert_eq!(result, Err("No unit clauses found."))
    }

    #[test]
    fn test_one_literal_rule_single_atom() {
        let formula_set = BTreeSet::from([BTreeSet::from([Formula::atom(prop("A"))])]);
        let result = Formula::_one_literal_rule(&formula_set);
        let desired = BTreeSet::new();
        assert_eq!(result, Ok(desired))
    }

    #[test]
    fn test_one_literal_rule_single_negated() {
        let formula_set =
            BTreeSet::from([BTreeSet::from([Formula::not(Formula::atom(prop("A")))])]);
        let result = Formula::_one_literal_rule(&formula_set);
        let desired = BTreeSet::new();
        assert_eq!(result, Ok(desired))
    }

    #[test]
    fn test_affirmative_negative_rule_1() {
        let formula_set = BTreeSet::from([
            BTreeSet::from([Formula::atom(prop("A"))]),
            BTreeSet::from([Formula::atom(prop("A")), Formula::atom(prop("C"))]),
            BTreeSet::from([
                Formula::not(Formula::atom(prop("A"))),
                Formula::atom(prop("D")),
            ]),
        ]);
        let desired = BTreeSet::from([BTreeSet::from([Formula::atom(prop("A"))])]);
        let result = Formula::_affirmative_negative_rule(&formula_set);
        assert_eq!(result, Ok(desired))
    }

    #[test]
    fn test_affirmative_negative_rule_2() {
        let formula_set = BTreeSet::from([
            BTreeSet::from([
                Formula::atom(prop("A")),
                Formula::not(Formula::atom(prop("C"))),
            ]),
            BTreeSet::from([
                Formula::not(Formula::atom(prop("A"))),
                Formula::atom(prop("B")),
            ]),
            BTreeSet::from([
                Formula::not(Formula::atom(prop("B"))),
                Formula::atom(prop("C")),
            ]),
        ]);
        let result = Formula::_affirmative_negative_rule(&formula_set);
        let desired = Err("No strictly positively or strictly negatively occurring literals.");
        assert_eq!(result, desired);
    }

    #[test]
    fn test_affirmative_negative_rule_3() {
        let formula_set =
            BTreeSet::from([BTreeSet::from([Formula::not(Formula::atom(prop("A")))])]);
        let result = Formula::_affirmative_negative_rule(&formula_set);

        assert_eq!(result, Ok(BTreeSet::new()))
    }
    #[test]
    fn test_resolve_atom() {
        let formula_set = BTreeSet::from([
            BTreeSet::from([Formula::atom(prop("A")), Formula::atom(prop("E"))]),
            BTreeSet::from([
                Formula::atom(prop("A")),
                Formula::not(Formula::atom(prop("C"))),
            ]),
            BTreeSet::from([
                Formula::not(Formula::atom(prop("A"))),
                Formula::atom(prop("B")),
                Formula::atom(prop("D")),
            ]),
            BTreeSet::from([
                Formula::not(Formula::atom(prop("B"))),
                Formula::atom(prop("C")),
            ]),
        ]);
        let atom: Formula<Prop> = Formula::atom(prop("A"));
        let result = Formula::_resolve_atom(&formula_set, &atom);
        // {{E}, {~C}} X  {{B, D}}
        let desired_product: FormulaSet = BTreeSet::from([
            BTreeSet::from([
                Formula::atom(prop("E")),
                Formula::atom(prop("B")),
                Formula::atom(prop("D")),
            ]),
            BTreeSet::from([
                Formula::not(Formula::atom(prop("C"))),
                Formula::atom(prop("B")),
                Formula::atom(prop("D")),
            ]),
        ]);
        let desired_rest: FormulaSet = BTreeSet::from([BTreeSet::from([
            Formula::not(Formula::atom(prop("B"))),
            Formula::atom(prop("C")),
        ])]);
        let desired = &desired_product | &desired_rest;
        assert_eq!(result, desired)
    }

    #[test]
    fn test_find_min() {
        // Just use the (negative of the) length of the formula for a test optimum.
        let opt = |formula: &Formula<Prop>| -(format!("{formula:?}").len() as isize);
        let domain = BTreeSet::from([
            Formula::True,
            Formula::atom(prop("A")),
            Formula::or(Formula::atom(prop("A")), Formula::False),
        ]);
        let result = Formula::_find_min(&opt, &domain).unwrap();
        let desired = Formula::or(Formula::atom(prop("A")), Formula::False);
        assert_eq!(result, desired);
    }

    #[test]
    fn test_counts_containing_literal_and_negation() {
        let formula_set = BTreeSet::from([
            BTreeSet::from([Formula::atom(prop("A")), Formula::atom(prop("E"))]),
            BTreeSet::from([
                Formula::atom(prop("A")),
                Formula::not(Formula::atom(prop("C"))),
            ]),
            BTreeSet::from([
                Formula::not(Formula::atom(prop("A"))),
                Formula::atom(prop("B")),
                Formula::atom(prop("D")),
            ]),
            BTreeSet::from([
                Formula::not(Formula::atom(prop("B"))),
                Formula::atom(prop("C")),
            ]),
        ]);
        let result = Formula::_counts_containing_literal_and_negation(
            &formula_set,
            &Formula::atom(prop("A")),
        );
        // (2 * 1) - 2 - 1 = -1
        let desired: (isize, isize) = (2, 1);
        assert_eq!(result, desired);
    }

    #[test]
    fn test_resolution_rule() {
        let formula_set = BTreeSet::from([
            BTreeSet::from([
                Formula::atom(prop("A")),
                Formula::not(Formula::atom(prop("C"))),
            ]),
            BTreeSet::from([
                Formula::not(Formula::atom(prop("D"))),
                Formula::atom(prop("C")),
            ]),
            BTreeSet::from([
                Formula::not(Formula::atom(prop("A"))),
                Formula::atom(prop("D")),
            ]),
            BTreeSet::from([Formula::atom(prop("A")), Formula::atom(prop("C"))]),
            BTreeSet::from([
                Formula::not(Formula::atom(prop("A"))),
                Formula::not(Formula::atom(prop("C"))),
            ]),
        ]);

        let result = Formula::_resolution_rule(&formula_set);
        // Check different cost values
        // cost picking:
        // A: 2 * 1 - 2 - 1 = 0
        // C: 2 * 1 - 2 - 1 = 0
        // D  1 * 1 - 1 - 1 = -1

        let desired_atom: Formula<Prop> = Formula::atom(prop("D"));
        let desired = Formula::_resolve_atom(&formula_set, &desired_atom);

        assert_eq!(result, desired)
    }

    #[test]
    fn test_dp() {
        let formula_set = BTreeSet::from([
            BTreeSet::from([
                Formula::atom(prop("A")),
                Formula::not(Formula::atom(prop("C"))),
            ]),
            BTreeSet::from([
                Formula::not(Formula::atom(prop("D"))),
                Formula::atom(prop("C")),
            ]),
            BTreeSet::from([
                Formula::not(Formula::atom(prop("A"))),
                Formula::atom(prop("D")),
            ]),
            BTreeSet::from([Formula::atom(prop("A")), Formula::atom(prop("C"))]),
            BTreeSet::from([
                Formula::not(Formula::atom(prop("A"))),
                Formula::not(Formula::atom(prop("C"))),
            ]),
        ]);

        let result = Formula::dp(&formula_set);
        let desired = false;
        assert_eq!(result, desired);
    }

    #[test]
    fn test_dp_simple() {
        let formula_set = BTreeSet::from([BTreeSet::from([Formula::atom(prop("A"))])]);
        assert!(Formula::dp(&formula_set));
    }

    #[test]
    fn test_dp_sat_taut_sanity() {
        assert!(Formula::dp_sat(&Formula::True));
        assert!(Formula::dp_taut(&Formula::True));
        assert!(!Formula::dp_sat(&Formula::False));
        assert!(!Formula::dp_taut(&Formula::False));
        assert!(Formula::dp_sat(&Formula::atom(prop("A"))));
        assert!(!Formula::dp_taut(&Formula::atom(prop("A"))));
    }
}

// DPLL
impl Formula<Prop> {
    fn _posneg_count(clauses: &FormulaSet, literal: &Formula<Prop>) -> isize {
        // splitting creates *two* formulae for DPLL of sizes
        // N + 1 each, but the next call to DPLL will call the unit clause rule
        // which will reduce each by
        // 1) removing the whole *clauses* where `literal` appears positively, and
        // 2) removing all occurences of the negation of literal.
        // NOTE that Harrison seems to count both of (1) and (2) equally, but
        // it doesn't seem that much harder to count up the sizes of the
        // clauses removed in 1).
        let (num_containing_lit, num_containing_neg) =
            Formula::_counts_containing_literal_and_negation(clauses, literal);
        num_containing_lit + num_containing_neg
    }

    pub fn dpll(clauses: &FormulaSet) -> bool {
        // The Davis-Putnam-Logemann-Loveland (1962) procedure.
        if clauses.is_empty() {
            return true;
        }
        if clauses.contains(&BTreeSet::new()) {
            return false;
        }
        if let Ok(formula) = Formula::_one_literal_rule(clauses) {
            return Formula::dpll(&formula);
        }
        if let Ok(formula) = Formula::_affirmative_negative_rule(clauses) {
            return Formula::dpll(&formula);
        }
        // Split.
        let positive_literals: BTreeSet<Formula<Prop>> = clauses
            .iter()
            .fold(BTreeSet::new(), |x, y| &x | y)
            .into_iter()
            .filter(|literal| !Formula::negative(literal))
            .collect();
        let atom = Formula::_find_min(
            &|atom| -Formula::_posneg_count(clauses, atom),
            &positive_literals,
        )
        .expect("Positive literals should not be empty");
        let negated = Formula::negate(&atom);
        let mut with_atom = clauses.clone();
        with_atom.insert(BTreeSet::from([atom]));
        let mut with_negated = clauses.clone();
        with_negated.insert(BTreeSet::from([negated]));
        Formula::dpll(&with_atom) || Formula::dpll(&with_negated)
    }

    pub fn dpll_sat(&self) -> bool {
        Formula::dpll(&Formula::_cnf_formulaset(self))
    }
    pub fn dpll_taut(&self) -> bool {
        !Formula::dpll_sat(&Formula::not(self.clone()))
    }
}

#[cfg(test)]
mod dpll_tests {
    use super::*;

    // Convenience to save us some typing.
    fn prop(name: &str) -> Prop {
        Prop::new(name)
    }

    #[test]
    fn test_dpll() {
        let formula_set = BTreeSet::from([
            BTreeSet::from([
                Formula::atom(prop("A")),
                Formula::not(Formula::atom(prop("C"))),
            ]),
            BTreeSet::from([
                Formula::not(Formula::atom(prop("D"))),
                Formula::atom(prop("C")),
            ]),
            BTreeSet::from([
                Formula::not(Formula::atom(prop("A"))),
                Formula::atom(prop("D")),
            ]),
            BTreeSet::from([Formula::atom(prop("A")), Formula::atom(prop("C"))]),
            BTreeSet::from([
                Formula::not(Formula::atom(prop("A"))),
                Formula::not(Formula::atom(prop("C"))),
            ]),
        ]);

        let result = Formula::dpll(&formula_set);
        let desired = false;
        assert_eq!(result, desired);
    }

    #[test]
    fn test_dpll_sat_taut_sanity() {
        assert!(Formula::dpll_sat(&Formula::True));
        assert!(Formula::dpll_taut(&Formula::True));
        assert!(!Formula::dpll_sat(&Formula::False));
        assert!(!Formula::dpll_taut(&Formula::False));
        assert!(Formula::dpll_sat(&Formula::atom(prop("A"))));
        assert!(!Formula::dpll_taut(&Formula::atom(prop("A"))));
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Mix {
    Guessed,
    Deduced,
}

// Unlike Harrison, we will push to / pop from the back.
pub type Trail = Vec<(Formula<Prop>, Mix)>;

// Iterative DPLL
impl Formula<Prop> {
    fn unit_propagate(clauses: &FormulaSet, trail: Trail) -> (FormulaSet, Trail) {
        // Kick of recursive unit_subpropagation with a `trail_set` matching the incoming `trail`.
        let trail_set: HashSet<Formula<Prop>> = trail.iter().map(|pair| pair.0.clone()).collect();
        let (reduced_clauses, _, new_trail) = Formula::unit_subpropagate(clauses, trail_set, trail);
        (reduced_clauses, new_trail)
    }

    fn unit_subpropagate(
        clauses: &FormulaSet,
        mut trail_set: HashSet<Formula<Prop>>,
        mut trail: Trail,
    ) -> (FormulaSet, HashSet<Formula<Prop>>, Trail) {
        // Filter out disjuncts that disagree with `trail_set`
        // from clauses.  If there are any new resulting unit clauses
        // add these to `trail` and `trail_set` and repeat.
        let reduced_clauses: FormulaSet = clauses
            .clone()
            .into_iter()
            .map(|clause| {
                clause
                    .into_iter()
                    .filter(|disjunct| !trail_set.contains(&Formula::negate(disjunct)))
                    .collect()
            })
            .collect();
        let new_units: HashSet<Formula<Prop>> = reduced_clauses
            .iter()
            .filter(|clause| clause.len() == 1 && !trail_set.contains(clause.first().unwrap()))
            .map(|clause| clause.first().unwrap().clone())
            .collect();
        if new_units.is_empty() {
            (reduced_clauses, trail_set, trail)
        } else {
            for unit in new_units.into_iter() {
                trail.push((unit.clone(), Mix::Deduced));
                trail_set.insert(unit);
            }
            Formula::unit_subpropagate(&reduced_clauses, trail_set, trail)
        }
    }

    fn _lit_abs(lit: &Formula<Prop>) -> Formula<Prop> {
        let result = match lit {
            Formula::Not(box p) => p,
            _ => lit,
        };
        result.clone()
    }

    fn get_unassigned_props(clauses: &FormulaSet, trail: &Trail) -> BTreeSet<Formula<Prop>> {
        // All Props that occur in `clauses` but not in `trail`.

        let clause_props: BTreeSet<_> = clauses
            .iter()
            .fold(BTreeSet::new(), |x, y| &x | y)
            .iter()
            .map(Formula::_lit_abs)
            .collect();

        let trail_props: BTreeSet<_> = trail
            .iter()
            .map(|(lit, _)| Formula::_lit_abs(lit))
            .collect();
        clause_props.difference(&trail_props).cloned().collect()
    }

    fn backtrack(trail: &mut Trail) {
        // Pop until we get to a Guessed value or the empty trail.
        if let Some((_, Mix::Deduced)) = trail.last() {
            trail.pop();
            Formula::backtrack(trail)
        }
    }

    fn functional_backtrack(trail: &Trail) -> Trail {
        // Pop until we get to a Guessed value or the empty trail.
        let mut copy = trail.clone();
        Formula::backtrack(&mut copy);
        copy
    }

    pub fn _dpli(clauses: &FormulaSet, trail: &mut Trail) -> bool {
        // Start by unit propagating.  If this results in a contradiction, backtrack.
        let (simplified_clauses, mut extended_trail) =
            Formula::unit_propagate(clauses, trail.to_owned());

        if simplified_clauses.contains(&BTreeSet::new()) {
            // Reach a contradiction.  Must backtrack.
            Formula::backtrack(trail);
            let last = trail.last();
            // Unfortunately cloning/to_owned-ing a Option<&T> gives the same type.
            // So we use "map" here as a kludge.
            let copy = last.map(|inner| inner.to_owned());
            match copy {
                // Switch parity of our last guess.  Marking as Deduced this time.
                Some((lit, Mix::Guessed)) => {
                    trail.pop();
                    trail.push((Formula::negate(&lit), Mix::Deduced));
                    Formula::_dpli(clauses, trail)
                }
                // If there were no more Guesses, the clauses are not satisfiable.
                _ => false,
            }
        } else {
            // Above propagation was consistent.  Choose another variable to guess.
            let unassigned = Formula::get_unassigned_props(clauses, &extended_trail);
            if unassigned.is_empty() {
                true
            } else {
                let optimum = Formula::_find_min(
                    &|lit| -Formula::_posneg_count(&simplified_clauses, lit),
                    &unassigned,
                )
                .unwrap();
                extended_trail.push((optimum, Mix::Guessed));
                Formula::_dpli(clauses, &mut extended_trail)
            }
        }
    }

    pub fn dpli(clauses: &FormulaSet) -> bool {
        Formula::_dpli(clauses, &mut vec![])
    }
}

#[cfg(test)]
mod dpli_tests {

    use super::*;

    #[test]
    fn test_backtrack() {
        let mut trail = vec![
            (Formula::atom(Prop::new("E")), Mix::Deduced),
            (Formula::atom(Prop::new("D")), Mix::Guessed),
            (Formula::atom(Prop::new("C")), Mix::Deduced),
            (Formula::atom(Prop::new("B")), Mix::Deduced),
            (Formula::atom(Prop::new("A")), Mix::Guessed),
        ];

        Formula::backtrack(&mut trail);
        assert_eq!(
            trail.last(),
            Some(&(Formula::atom(Prop::new("A")), Mix::Guessed))
        );
        let desired_trail = vec![
            (Formula::atom(Prop::new("E")), Mix::Deduced),
            (Formula::atom(Prop::new("D")), Mix::Guessed),
            (Formula::atom(Prop::new("C")), Mix::Deduced),
            (Formula::atom(Prop::new("B")), Mix::Deduced),
            (Formula::atom(Prop::new("A")), Mix::Guessed),
        ];
        assert_eq!(trail, desired_trail);

        trail.pop();
        Formula::backtrack(&mut trail);
        assert_eq!(
            trail.last(),
            Some(&(Formula::atom(Prop::new("D")), Mix::Guessed))
        );
        let desired_trail = vec![
            (Formula::atom(Prop::new("E")), Mix::Deduced),
            (Formula::atom(Prop::new("D")), Mix::Guessed),
        ];
        assert_eq!(trail, desired_trail);

        trail.pop();
        Formula::backtrack(&mut trail);
        assert_eq!(trail.last(), None);
        let desired_trail = vec![];
        assert_eq!(trail, desired_trail);
    }

    #[test]
    fn test_unassigned() {
        let trail: Trail = vec![
            (Formula::atom(Prop::new("E")), Mix::Deduced),
            (Formula::not(Formula::atom(Prop::new("D"))), Mix::Guessed),
            (Formula::atom(Prop::new("B")), Mix::Deduced),
            (Formula::not(Formula::atom(Prop::new("C"))), Mix::Guessed),
        ];

        let clauses: FormulaSet = BTreeSet::from([
            BTreeSet::from([Formula::atom(Prop::new("Z")), Formula::atom(Prop::new("D"))]),
            BTreeSet::from([
                Formula::atom(Prop::new("C")),
                Formula::not(Formula::atom(Prop::new("X"))),
            ]),
        ]);
        let result: BTreeSet<Formula<Prop>> = Formula::get_unassigned_props(&clauses, &trail);
        let desired =
            BTreeSet::from([Formula::atom(Prop::new("Z")), Formula::atom(Prop::new("X"))]);
        assert_eq!(result, desired);
    }

    #[test]
    fn test_unit_propagate() {
        let clauses: FormulaSet = BTreeSet::from([
            BTreeSet::from([
                Formula::not(Formula::atom(Prop::new("A"))),
                Formula::atom(Prop::new("B")),
            ]),
            BTreeSet::from([
                Formula::not(Formula::atom(Prop::new("B"))),
                Formula::not(Formula::atom(Prop::new("A"))),
                Formula::not(Formula::atom(Prop::new("D"))),
            ]),
            BTreeSet::from([
                Formula::not(Formula::atom(Prop::new("B"))),
                Formula::atom(Prop::new("E")),
                Formula::atom(Prop::new("D")),
                Formula::not(Formula::atom(Prop::new("C"))),
            ]),
        ]);
        let trail: Trail = Vec::from([
            (Formula::atom(Prop::new("A")), Mix::Guessed),
            (Formula::atom(Prop::new("Z")), Mix::Deduced),
        ]);
        let (result_clauses, result_trail) = Formula::unit_propagate(&clauses, trail);
        let desired_clauses: FormulaSet = BTreeSet::from([
            BTreeSet::from([Formula::atom(Prop::new("B"))]),
            BTreeSet::from([Formula::not(Formula::atom(Prop::new("D")))]),
            BTreeSet::from([
                Formula::atom(Prop::new("E")),
                Formula::not(Formula::atom(Prop::new("C"))),
            ]),
        ]);
        let desired_trail: Trail = Vec::from([
            (Formula::atom(Prop::new("A")), Mix::Guessed),
            (Formula::atom(Prop::new("Z")), Mix::Deduced),
            (Formula::atom(Prop::new("B")), Mix::Deduced),
            (Formula::not(Formula::atom(Prop::new("D"))), Mix::Deduced),
        ]);
        assert_eq!(result_clauses, desired_clauses);
        assert_eq!(result_trail, desired_trail);
    }

    #[test]
    fn test_dpli() {
        let formula_set = BTreeSet::from([
            BTreeSet::from([
                Formula::atom(Prop::new("A")),
                Formula::not(Formula::atom(Prop::new("C"))),
            ]),
            BTreeSet::from([
                Formula::not(Formula::atom(Prop::new("D"))),
                Formula::atom(Prop::new("C")),
            ]),
            BTreeSet::from([
                Formula::not(Formula::atom(Prop::new("A"))),
                Formula::atom(Prop::new("D")),
            ]),
            BTreeSet::from([Formula::atom(Prop::new("A")), Formula::atom(Prop::new("C"))]),
            BTreeSet::from([
                Formula::not(Formula::atom(Prop::new("A"))),
                Formula::not(Formula::atom(Prop::new("C"))),
            ]),
        ]);

        let result = Formula::dpli(&formula_set);
        let desired = false;
        assert_eq!(result, desired);

        let formula_set = BTreeSet::from([
            BTreeSet::from([
                Formula::atom(Prop::new("A")),
                Formula::not(Formula::atom(Prop::new("C"))),
            ]),
            BTreeSet::from([
                Formula::not(Formula::atom(Prop::new("D"))),
                Formula::atom(Prop::new("C")),
            ]),
            BTreeSet::from([
                Formula::not(Formula::atom(Prop::new("A"))),
                Formula::atom(Prop::new("D")),
            ]),
            BTreeSet::from([Formula::atom(Prop::new("A")), Formula::atom(Prop::new("C"))]),
            BTreeSet::from([
                Formula::not(Formula::atom(Prop::new("A"))),
                Formula::atom(Prop::new("C")),
            ]),
        ]);

        let result = Formula::dpli(&formula_set);
        let desired = true;
        assert_eq!(result, desired);
    }
}

// Backjumping
impl Formula<Prop> {
    fn backjump(clauses: &FormulaSet, p: &Formula<Prop>, trail: &Trail) -> Trail {
        // To be called when `p` is inconsistent with `trail`.
        let mut new_trail = Formula::functional_backtrack(trail);
        if let Some((_, Mix::Guessed)) = new_trail.last() {
            new_trail.pop();
            new_trail.push((p.clone(), Mix::Guessed));
            let (reduced_clauses, _) = Formula::unit_propagate(clauses, new_trail.clone());
            if reduced_clauses.contains(&BTreeSet::new()) {
                new_trail.pop();
                return Formula::backjump(clauses, p, &new_trail);
            }
        }
        trail.clone()
    }

    pub fn _dplb(clauses: &FormulaSet, trail: &mut Trail) -> bool {
        // Start by unit propagating.  If this results in a contradiction, backtrack.
        let (simplified_clauses, mut extended_trail) =
            Formula::unit_propagate(clauses, trail.to_owned());

        if simplified_clauses.contains(&BTreeSet::new()) {
            // Reach a contradiction.  Must backtrack.
            Formula::backtrack(trail);
            match trail.last() {
                // Switch parity of our last guess.  Marking as Deduced this time.
                Some((lit, Mix::Guessed)) => {
                    let mut bj_trail = Formula::backjump(clauses, lit, trail);
                    // A clause of the negations of all guesses up till but not including
                    // p.  Note that those guesses are jointly consistent (were one to conjoin them),
                    // but not if we were to add `val`.
                    let mut constraint: BTreeSet<Formula<Prop>> = bj_trail
                        .iter()
                        .filter(|(_, mix)| mix == &Mix::Guessed)
                        .map(|(val, _)| Formula::negate(val))
                        .collect();
                    constraint.insert(Formula::negate(lit));
                    // TODO: use mutable variable instead?
                    let mut new_clauses = clauses.clone();
                    new_clauses.insert(constraint);
                    trail.push((Formula::negate(lit), Mix::Deduced));
                    Formula::_dplb(&new_clauses, &mut bj_trail)
                }

                _ => false,
            }
        } else {
            // Above propagation was consistent.  Choose another variable to guess.
            let unassigned = Formula::get_unassigned_props(clauses, &extended_trail);
            if unassigned.is_empty() {
                true
            } else {
                let optimum = Formula::_find_min(
                    &|lit| -Formula::_posneg_count(&simplified_clauses, lit),
                    &unassigned,
                )
                .unwrap();
                extended_trail.push((optimum, Mix::Guessed));
                Formula::_dpli(clauses, &mut extended_trail)
            }
        }
    }

    pub fn dplb(clauses: &FormulaSet) -> bool {
        Formula::_dplb(clauses, &mut vec![])
    }
}

#[cfg(test)]
mod dplb_tests {

    use super::*;

    #[test]
    fn test_backjump() {
        let clauses: FormulaSet = BTreeSet::from([
            BTreeSet::from([
                Formula::not(Formula::atom(Prop::new("A"))),
                Formula::atom(Prop::new("B")),
            ]),
            BTreeSet::from([
                Formula::not(Formula::atom(Prop::new("B"))),
                Formula::not(Formula::atom(Prop::new("A"))),
                Formula::not(Formula::atom(Prop::new("D"))),
            ]),
            BTreeSet::from([
                Formula::atom(Prop::new("D")),
                Formula::not(Formula::atom(Prop::new("Z"))),
            ]),
            BTreeSet::from([
                Formula::not(Formula::atom(Prop::new("M"))),
                Formula::not(Formula::atom(Prop::new("Y"))),
            ]),
        ]);

        let p = Formula::atom(Prop::new("A"));
        let trail: Trail = Vec::from([
            (Formula::atom(Prop::new("N")), Mix::Deduced),
            (Formula::not(Formula::atom(Prop::new("M"))), Mix::Guessed),
            (Formula::atom(Prop::new("Z")), Mix::Guessed),
            (Formula::atom(Prop::new("F")), Mix::Guessed),
            (Formula::atom(Prop::new("R")), Mix::Deduced),
        ]);

        let result = Formula::backjump(&clauses, &p, &trail);

        let desired: Trail = Vec::from([
            (Formula::atom(Prop::new("N")), Mix::Deduced),
            (Formula::not(Formula::atom(Prop::new("M"))), Mix::Guessed),
            (Formula::atom(Prop::new("Z")), Mix::Guessed),
        ]);
        assert_eq!(result, desired);
    }

    #[test]
    fn test_dplb() {
        let formula_set = BTreeSet::from([
            BTreeSet::from([
                Formula::atom(Prop::new("A")),
                Formula::not(Formula::atom(Prop::new("C"))),
            ]),
            BTreeSet::from([
                Formula::not(Formula::atom(Prop::new("D"))),
                Formula::atom(Prop::new("C")),
            ]),
            BTreeSet::from([
                Formula::not(Formula::atom(Prop::new("A"))),
                Formula::atom(Prop::new("D")),
            ]),
            BTreeSet::from([Formula::atom(Prop::new("A")), Formula::atom(Prop::new("C"))]),
            BTreeSet::from([
                Formula::not(Formula::atom(Prop::new("A"))),
                Formula::not(Formula::atom(Prop::new("C"))),
            ]),
        ]);

        let result = Formula::dplb(&formula_set);
        let desired = false;
        assert_eq!(result, desired);

        let formula_set = BTreeSet::from([
            BTreeSet::from([
                Formula::atom(Prop::new("A")),
                Formula::not(Formula::atom(Prop::new("C"))),
            ]),
            BTreeSet::from([
                Formula::not(Formula::atom(Prop::new("D"))),
                Formula::atom(Prop::new("C")),
            ]),
            BTreeSet::from([
                Formula::not(Formula::atom(Prop::new("A"))),
                Formula::atom(Prop::new("D")),
            ]),
            BTreeSet::from([Formula::atom(Prop::new("A")), Formula::atom(Prop::new("C"))]),
            BTreeSet::from([
                Formula::not(Formula::atom(Prop::new("A"))),
                Formula::atom(Prop::new("C")),
            ]),
        ]);

        let result = Formula::dpli(&formula_set);
        let desired = true;
        assert_eq!(result, desired);
    }
}
