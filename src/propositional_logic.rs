// ### PROPOSITIONAL LOGIC ###
// AST specific parsing/printing functions for propositional (aka sentential) logic.

// TODO(arthur) Maybe encapsulate printing/parsing each into their own (inner) modules
// so that testing can import just them?
//
use std::cmp;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt::Debug;
use std::io::Write;

use crate::parse::{generic_parser, PartialParseResult};

pub use crate::formula::{write, ErrInner, Formula};

use regex::Regex;

// A propositional variable.  Basically just a wrapper around a name.
#[derive(Debug, PartialEq, Clone, Hash, Eq, PartialOrd, Ord)]
pub struct Prop {
    name: String,
}

pub fn prop(name: &str) -> Prop {
    // Convenience constructor for `Prop`s.
    Prop {
        name: String::from(name),
    }
}

impl Formula<Prop> {
    fn _parse_propvar<'a>(
        _variables: &Vec<String>,
        input: &'a [String],
    ) -> PartialParseResult<'a, Formula<Prop>> {
        match input {
            // The conditional here seems unnecessary given how this is used in parse_formula.
            [p, rest @ ..] if p != "(" => (Formula::atom(prop(p)), rest),
            _ => panic!("Failed to parse propvar."),
        }
    }

    fn _parse_prop_formula_inner<'a>(input: &'a [String]) -> PartialParseResult<'a, Formula<Prop>> {
        Formula::parse_general(
            |_, _| Err("Infix operations not supported."),
            Formula::_parse_propvar,
            &vec![],
            input,
        )
    }

    pub fn parse(input: &str) -> Formula<Prop> {
        generic_parser(Formula::_parse_prop_formula_inner, input)
    }
}

type Triple = (Formula<Prop>, Defs, usize);
type BinOp = fn(Formula<Prop>, Formula<Prop>) -> Formula<Prop>;
type Defs = HashMap<Formula<Prop>, (Formula<Prop>, Formula<Prop>)>;

#[cfg(test)]
mod prop_parse_tests {
    use super::*;

    fn init() {
        let _ = env_logger::builder().is_test(true).try_init();
    }

    #[test]
    fn test_parse() {
        let input = "a <=> (b /\\ c)";
        let result = Formula::parse(input);

        let desired = Formula::iff(
            Formula::atom(prop("a")),
            Formula::and(Formula::atom(prop("b")), Formula::atom(prop("c"))),
        );
        assert_eq!(result, desired);
    }
}

// ### PRINTING ###

impl Formula<Prop> {
    fn _print_propvar<W: Write>(dest: &mut W, _prec: u32, atom: &Prop) -> () {
        // Our atom printer for propositional logic.  Note that the precedence argument is
        // simply ignored.
        write(dest, &atom.name);
    }

    pub fn pprint<W: Write>(&self, dest: &mut W) -> () {
        let pfn: fn(&mut W, u32, &Prop) -> () = Formula::_print_propvar;
        self.pprint_general(dest, &pfn);
        write(dest, "\n");
    }
}

#[cfg(test)]
mod prop_print_tests {
    use super::*;

    fn init() {
        let _ = env_logger::builder().is_test(true).try_init();
    }

    #[test]
    fn test_print_propvar() {
        let mut output = Vec::new();
        let prop = prop("SomeProp");
        Formula::_print_propvar(&mut output, 0, &prop);
        let output = String::from_utf8(output).expect("Not UTF-8");
        assert_eq!(output, "SomeProp");

        let mut output2 = Vec::new();
        Formula::_print_propvar(&mut output2, 42, &prop);
        let output2 = String::from_utf8(output2).expect("Not UTF-8");
        assert_eq!(output2, "SomeProp");
    }

    #[test]
    fn test_pprint() {
        let formula = Formula::and(
            Formula::atom(prop("Prop5")),
            Formula::iff(
                Formula::atom(prop("Prop2")),
                Formula::imp(
                    Formula::or(Formula::atom(prop("Prop3")), Formula::atom(prop("Prop4"))),
                    Formula::atom(prop("Prop1")),
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

// ### Eval / Manipulation ###

// We use a BTreeMap here so that we can order the items by Prop.name.
type Valuation = BTreeMap<Prop, bool>;

// Set representations of Formulas in disjunctive or conjunctive normal form 
// (we need to specify in order to have a unique meaning)..
// Note we could replace the inner `Formula<Prop>` by an indicator
// function on `Prop`. Which would prevent non-literals from going in there.
// We use a BTreeSet here so that we can order the items by Prop.name.
type FormulaSet = BTreeSet<BTreeSet<Formula<Prop>>>;

impl Formula<Prop> {
    fn eval(&self, val: &Valuation) -> bool {
        // NOTE:  We could just as well give trivial definitions for when a propositional
        // formula is quantified, but for now we'll just panic.
        match self {
            Formula::True => true,
            Formula::False => false,
            Formula::Atom(x) => val
                .get(x)
                .expect("Valuation should be defined on all atoms occurring in formula")
                .clone(),
            Formula::Not(box p) => !p.eval(val),
            Formula::And(box p, box q) => p.eval(val) && q.eval(val),
            Formula::Or(box p, box q) => p.eval(val) || q.eval(val),
            Formula::Imp(box p, box q) => !p.eval(val) || q.eval(val),
            Formula::Iff(box p, box q) => p.eval(val) == q.eval(val),
            _ => panic!("Unsupported formula type for {:?}", self),
        }
    }

    fn get_all_valuations(atoms: &BTreeSet<Prop>) -> Vec<Valuation> {
        // Initialize result to the singleton with the empty valuation.
        // WARNING, running time/space is Theta(exp(|atoms|))

        let mut result = vec![BTreeMap::new()];
        for atom in atoms {
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

    pub fn print_truthtable(&self, dest: &mut impl Write) -> () {
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
            let result = self.eval(&val);
            let output_string = truth_string(result);
            format!("{}| {}\n", input_string, output_string)
        };
        let body = String::from_iter(Formula::get_all_valuations(&atoms).iter().map(make_row));

        let header_lhs = String::from_iter(sorted_atoms.iter().map(|p| p.name.clone()).map(pad));
        let header = format!("{}| formula", header_lhs);
        let separator = String::from_iter(vec!['-'; header.len()]);
        let result = format!("{}\n{}\n{}{}\n", header, separator, body, separator);
        write(dest, &result);
    }

    pub fn tautology(&self) -> bool {
        // NOTE:  SLOW, USE OTHER VERSIONS.
        // Note that the set of valuations should never be empty
        // (Event `True` has the empty valuation.)
        Formula::get_all_valuations(&self.atoms())
            .iter()
            .map(|x| self.eval(x))
            .fold(true, |x, y| x && y)
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

    fn psubst(&self, subfn: &HashMap<Prop, Formula<Prop>>) -> Formula<Prop> {
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

    // fn make_lits(items: &Vec<Formula<Prop>>, valuation: &Valuation) -> Formula<Prop> {
    //     // Despite the name `items` can be any formulas and we compute the conjunction of
    //     // the formulas in `items` xor their negations according to which is satisfied by
    //     // `valuation`.
    //     let items = items.clone();
    //     let map = |item: Formula<Prop>| {
    //         if item.eval(valuation) {
    //             item
    //         } else {
    //             Formula::not(item)
    //         }
    //     };
    //     Formula::list_conj(&items.into_iter().map(&map).collect())
    // }

    // fn all_sat_valuations(&self) -> Vec<Valuation> {
    //     // All valuations satisfying `self`.
    //     Formula::get_all_valuations(&self.atoms())
    //         .into_iter()
    //         .filter(|val| self.eval(val))
    //         .collect()
    // }

    // fn naive_dnf(&self) -> Formula<Prop> {
    //     // Disjunction Normal Form via gathering all satisfying valuations.

    //     let mut atom_vec = Vec::from_iter(self.atoms());
    //     atom_vec.sort();

    //     let atom_formulas: Vec<Formula<Prop>> = atom_vec
    //         .into_iter()
    //         .map(|inner| Formula::atom(inner))
    //         .collect();

    //     Formula::list_disj(
    //         &self
    //             .all_sat_valuations()
    //             .iter()
    //             .map(|val| Formula::make_lits(&atom_formulas, &val))
    //             .collect(),
    //     )
    // }

    // fn _distrib_and_over_or(formula: &Formula<Prop>) -> Formula<Prop> {
    //     match formula {
    //         Formula::And(box p, box Formula::Or(box q, box r)) => Formula::or(
    //             Formula::_distrib_and_over_or(&Formula::and(p.clone(), q.clone())),
    //             Formula::_distrib_and_over_or(&Formula::and(p.clone(), r.clone())),
    //         ),
    //         Formula::And(box Formula::Or(box p, box q), box r) => Formula::or(
    //             Formula::_distrib_and_over_or(&Formula::and(p.clone(), r.clone())),
    //             Formula::_distrib_and_over_or(&Formula::and(q.clone(), r.clone())),
    //         ),
    //         _ => formula.clone(),
    //     }
    // }

    // fn raw_dnf(&self) -> Formula<Prop> {
    //     // Disjunctive Normal Form via repeated distributions of And over Or.
    //     match self.nnf() {
    //         Formula::And(box p, box q) => {
    //             Formula::_distrib_and_over_or(&Formula::and(p.raw_dnf(), q.raw_dnf()))
    //         }
    //         Formula::Or(box p, box q) => Formula::or(p.raw_dnf(), q.raw_dnf()),
    //         x => x,
    //     }
    // }

    fn _set_distrib_and_over_or(formula1: &FormulaSet, formula2: &FormulaSet) -> FormulaSet {
        // FIX do this w/ maps?
        let mut result = FormulaSet::new();
        for conj1 in formula1 {
            for conj2 in formula2 {
                let union: BTreeSet<Formula<Prop>> = conj1.union(conj2).cloned().collect();
                result.insert(union);
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
            Formula::Or(box p, box q) => p._purednf().union(&q._purednf()).cloned().collect(),
            _ => panic!("Unrecognized formula type for puredfn{:?}.  In nnf:", nnf),
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
        match formula {
            Formula::Not(_) => true,
            _ => false,
        }
    }

    fn _positive(formula: &Formula<Prop>) -> bool {
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
                } else if conj1.is_superset(&conj2) {
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
            .map(|set| Vec::from_iter(set))
            .map(|conj| Formula::list_conj(&conj))
            .collect();
        Formula::list_disj(&partial)
    }

    fn _formulaset_to_cnf(formula_set: FormulaSet) -> Formula<Prop> {
        let partial: Vec<Formula<Prop>> = formula_set
            .into_iter()
            .map(|set| Vec::from_iter(set))
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
        if Formula::_is_disjunction_of_literals(&self) {
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

    // Note that when _maincnf recieves such a triple, the formula could be anything
    // But when such a triple is returned by defstep (and so by this function),
    // the formula is always an atom and so the value returned here is always
    // a literal.
    /* Definitional CNF */
    fn _main_def_cnf(formula: &Formula<Prop>, defs: &Defs, n: usize) -> Triple {
        let triple: Triple = (formula.clone(), defs.clone(), n);
        match formula {
            Formula::And(box p, box q) => {
                Formula::_defstep(Formula::and, (p.clone(), q.clone()), triple.clone())
            }
            Formula::Or(box p, box q) => {
                Formula::_defstep(Formula::or, (p.clone(), q.clone()), triple.clone())
            }
            Formula::Iff(box p, box q) => {
                Formula::_defstep(Formula::iff, (p.clone(), q.clone()), triple.clone())
            }
            // Literals:
            _ => triple.clone(),
        }
    }

    const DEF_CNF_PREFIX: &'static str = "p_";
    fn _mkprop(idx: usize) -> Prop {
        prop(&format!("{}{}", Formula::DEF_CNF_PREFIX, idx))
    }

    fn _defstep(bin_op: BinOp, operands: (Formula<Prop>, Formula<Prop>), params: Triple) -> Triple {
        // Takes owned operands and params.
        let (_current_formula, defs0, n0) = params;
        let (literal1, defs1, n1) = Formula::_main_def_cnf(&operands.0, &defs0, n0);
        let (literal2, defs2, n2) = Formula::_main_def_cnf(&operands.1, &defs1, n1);
        let operation = bin_op(literal1, literal2);
        if defs2.contains_key(&operation) {
            return (defs2[&operation].0.clone(), defs2, n2);
        }

        let atom = Formula::atom(Self::_mkprop(n2));
        let mut new_defs = defs2.clone();
        new_defs.insert(
            operation.clone(),
            (atom.clone(), Formula::iff(atom.clone(), operation)),
        );

        (atom, new_defs, n2 + 1)
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
            .fold(FormulaSet::new(), |x, y| x.union(&y).cloned().collect());
        let result_formulaset: FormulaSet = atom_cnf_formulaset
            .union(&def_formulaset)
            .cloned()
            .collect();
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

    fn _one_literal_rule(clauses: &FormulaSet) -> Result<FormulaSet, ErrInner> {
        for clause in clauses {
            if clause.len() == 1 {
                let clause_vec: Vec<Formula<Prop>> = Vec::from_iter(clause.clone());
                let literal = clause_vec[0].clone();
                let negation = literal.negate();
                let result: FormulaSet = clauses
                    .into_iter()
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
        let all_literals: BTreeSet<Formula<Prop>> = clauses
            .iter()
            .fold(BTreeSet::new(), |x, y| x.union(&y).cloned().collect());
        let (negative, positive): (BTreeSet<Formula<Prop>>, BTreeSet<Formula<Prop>>) =
            all_literals.into_iter().partition(Formula::negative);
        let unnegated: BTreeSet<Formula<Prop>> = negative
            .into_iter()
            .map(|neg| Formula::negate(&neg))
            .collect();
        let positive_only: BTreeSet<Formula<Prop>> = positive.difference(&unnegated).cloned().collect();
        let negative_only: BTreeSet<Formula<Prop>> = unnegated.difference(&positive).cloned().collect();
        let renegated: BTreeSet<Formula<Prop>> = negative_only
            .into_iter()
            .map(|neg| Formula::negate(&neg))
            .collect();
        let pure: BTreeSet<Formula<Prop>> = positive_only.union(&renegated).cloned().collect();

        if pure.len() == 0 {
            Err("No strictly positively or strictly negatively occurring literals.")
        } else {
            let value: FormulaSet = clauses
                .iter()
                .filter(|clause| clause.intersection(&pure).collect::<BTreeSet<_>>().len() == 0)
                .cloned()
                .collect();
            Ok(value)
        }
    }

    // For _resolution_rule (DP only).
    fn _resolve_atom(clauses: &FormulaSet, literal: &Formula<Prop>) -> FormulaSet {
        let clauses = Formula::_strip_contradictory(&clauses);
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
                result.insert(literal_comp.union(&negation_comp).cloned().collect());
            }
        }
        let result = Formula::_strip_contradictory(&result)
            .union(&contains_neither)
            .cloned()
            .collect();
        result
    }

    fn _counts_containing_literal_and_negation(
        clauses: &FormulaSet,
        literal: &Formula<Prop>,
    ) -> (isize, isize) {
        let num_containing_lit = clauses
            .iter()
            .filter(|clause| clause.contains(&literal))
            .count() as isize;
        let negated = &Formula::negate(&literal);
        let num_containing_neg = clauses
            .iter()
            .filter(|clause| clause.contains(&negated))
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
        // Returns the T that minimizes F */
        if domain.len() == 0 {
            return None;
        }
        let mut minimizing_input: Formula<Prop> = Vec::from_iter(domain)[0].clone();
        let mut min_value = obj(&minimizing_input);
        for atom in domain {
            let atom_value = obj(&atom);
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
            .fold(BTreeSet::new(), |x, y| x.union(&y).cloned().collect())
            .into_iter()
            .filter(|literal| !Formula::negative(literal))
            .collect();
        println!("POS {:?}", positive_literals);
        let obj = |literal: &Formula<Prop>| Formula::_atom_resolution_cost(&clauses, literal);
        let literal = Formula::_find_min(&obj, &positive_literals)
            .expect("positive_literals should be non-empty");
        Formula::_resolve_atom(clauses, &literal)
    }

    pub fn dp(clauses: &FormulaSet) -> bool {
        // The Davis-Putnam (1960) procedure.
        // Intended to be run on a FormulaSet representing a CNF formula.
        if clauses.len() == 0 {
            return true;
        }
        if clauses.contains(&BTreeSet::new()) {
            return false;
        }
        if let Ok(formula) = Formula::_one_literal_rule(&clauses) {
            return Formula::dp(&formula);
        }
        if let Ok(formula) = Formula::_affirmative_negative_rule(&clauses) {
            return Formula::dp(&formula);
        }
        let next = Formula::_resolution_rule(&clauses);
        Formula::dp(&next)
    }

    pub fn dp_sat(&self) -> bool {
        Formula::dp(&Formula::_cnf_formulaset(&self))
    }
    pub fn dp_taut(&self) -> bool {
        !Formula::dp_sat(&Formula::not(self.clone()))
    }

    fn _posneg_count(clauses: &FormulaSet, literal: &Formula<Prop>) -> isize {
        // splitting creates *two* formulae for DPLL of sizes
        // N + 1 each, but the next call to DPLL will call the unit clause rule
        // which will reduce each by
        // 1) removing the whole *clauses* where `literal` appears positively, and
        // 2) removing all occurences of the negation of literal.
        // NOTE that Harrison seesm to count both of (1) and (2) equally, but
        // it doesn't seem that much harder to count up the sizes of the
        // clauses removed in 1).
        let (num_containing_lit, num_containing_neg) =
            Formula::_counts_containing_literal_and_negation(&clauses, &literal);
        num_containing_lit + num_containing_neg
    }

    pub fn dpll(clauses: &FormulaSet) -> bool {
        
        // The Davis-Putnam-Logemann-Loveland (1962) procedure.
        if clauses.len() == 0 {
            return true;
        }
        if clauses.contains(&BTreeSet::new()) {
            return false;
        }
        if let Ok(formula) = Formula::_one_literal_rule(&clauses) {
            return Formula::dpll(&formula);
        }
        if let Ok(formula) = Formula::_affirmative_negative_rule(&clauses) {
            return Formula::dpll(&formula);
        }
        // Split.
        let positive_literals: BTreeSet<Formula<Prop>> = clauses
            .iter()
            .fold(BTreeSet::new(), |x, y| x.union(&y).cloned().collect())
            .into_iter()
            .filter(|literal| !Formula::negative(literal))
            .collect();
        let atom = Formula::_find_min(
            &|atom| -Formula::_posneg_count(&clauses, atom),
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
        Formula::dpll(&Formula::_cnf_formulaset(&self))
    }
    pub fn dpll_taut(&self) -> bool {
        !Formula::dpll_sat(&Formula::not(self.clone()))
    }
}

// END

#[cfg(test)]
mod eval_tests {
    use super::*;

    #[test]
    fn test_eval() {
        let empty = &Valuation::new();
        let mut formula;

        formula = Formula::True;
        assert_eq!(formula.eval(empty), true);

        formula = Formula::False;
        assert_eq!(formula.eval(empty), false);

        formula = Formula::not(Formula::False);
        assert_eq!(formula.eval(empty), true);

        formula = Formula::not(Formula::True);
        assert_eq!(formula.eval(empty), false);

        formula = Formula::and(Formula::True, Formula::True);
        assert_eq!(formula.eval(empty), true);

        formula = Formula::and(Formula::False, Formula::True);
        assert_eq!(formula.eval(empty), false);

        formula = Formula::and(Formula::True, Formula::False);
        assert_eq!(formula.eval(empty), false);

        formula = Formula::and(Formula::False, Formula::False);
        assert_eq!(formula.eval(empty), false);

        formula = Formula::or(Formula::True, Formula::True);
        assert_eq!(formula.eval(empty), true);

        formula = Formula::or(Formula::False, Formula::True);
        assert_eq!(formula.eval(empty), true);

        formula = Formula::or(Formula::True, Formula::False);
        assert_eq!(formula.eval(empty), true);

        formula = Formula::or(Formula::False, Formula::False);
        assert_eq!(formula.eval(empty), false);

        formula = Formula::imp(Formula::True, Formula::True);
        assert_eq!(formula.eval(empty), true);

        formula = Formula::imp(Formula::False, Formula::True);
        assert_eq!(formula.eval(empty), true);

        formula = Formula::imp(Formula::True, Formula::False);
        assert_eq!(formula.eval(empty), false);

        formula = Formula::imp(Formula::False, Formula::False);
        assert_eq!(formula.eval(empty), true);

        formula = Formula::iff(Formula::True, Formula::True);
        assert_eq!(formula.eval(empty), true);

        formula = Formula::iff(Formula::False, Formula::True);
        assert_eq!(formula.eval(empty), false);

        formula = Formula::iff(Formula::True, Formula::False);
        assert_eq!(formula.eval(empty), false);

        formula = Formula::iff(Formula::False, Formula::False);
        assert_eq!(formula.eval(empty), true);

        let val = Valuation::from([(prop("A"), true), (prop("B"), false), (prop("C"), true)]);

        formula = Formula::atom(prop("A"));
        assert_eq!(formula.eval(&val), true);

        formula = Formula::atom(prop("B"));
        assert_eq!(formula.eval(&val), false);

        formula = Formula::iff(
            Formula::atom(prop("C")),
            Formula::and(Formula::atom(prop("A")), Formula::atom(prop("B"))),
        );
        assert_eq!(formula.eval(&val), false);
    }

    #[test]
    fn test_get_all_valuations() {
        let atoms = BTreeSet::from([prop("A"), prop("B"), prop("C")]);
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
        let formula = Formula::iff(
            Formula::atom(prop("C")),
            Formula::and(Formula::atom(prop("A")), Formula::atom(prop("B"))),
        );
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
        let form1 = Formula::True;
        assert!(form1.tautology());
        assert!(!form1.unsatisfiable());
        assert!(form1.satisfiable());

        let form2 = Formula::or(Formula::atom(prop("A")), Formula::atom(prop("B")));
        assert!(!form2.tautology());
        assert!(!form2.unsatisfiable());
        assert!(form2.satisfiable());

        let form3 = Formula::or(
            Formula::atom(prop("A")),
            Formula::not(Formula::atom(prop("A"))),
        );
        assert!(form3.tautology());
        assert!(!form3.unsatisfiable());
        assert!(form3.satisfiable());

        let form4 = Formula::and(
            Formula::atom(prop("A")),
            Formula::not(Formula::atom(prop("A"))),
        );
        assert!(!form4.tautology());
        assert!(form4.unsatisfiable());
        assert!(!form4.satisfiable());
    }

    #[test]
    fn test_psubst() {
        let map = HashMap::from([(
            prop("p"),
            Formula::and(Formula::atom(prop("p")), Formula::atom(prop("q"))),
        )]);
        let formula = Formula::and(
            Formula::atom(prop("p")),
            Formula::and(
                Formula::atom(prop("q")),
                Formula::and(Formula::atom(prop("p")), Formula::atom(prop("q"))),
            ),
        );
        let desired = Formula::and(
            Formula::and(Formula::atom(prop("p")), Formula::atom(prop("q"))),
            Formula::and(
                Formula::atom(prop("q")),
                Formula::and(
                    Formula::and(Formula::atom(prop("p")), Formula::atom(prop("q"))),
                    Formula::atom(prop("q")),
                ),
            ),
        );
        let result = formula.psubst(&map);
        assert_eq!(result, desired)
    }

    #[test]
    fn test_dual() {
        let formula = Formula::or(
            Formula::and(
                Formula::atom(prop("a")),
                Formula::not(Formula::atom(prop("b"))),
            ),
            Formula::or(
                Formula::not(Formula::atom(prop("c"))),
                Formula::atom(prop("d")),
            ),
        );
        let desired = Formula::and(
            Formula::or(
                Formula::atom(prop("a")),
                Formula::not(Formula::atom(prop("b"))),
            ),
            Formula::and(
                Formula::not(Formula::atom(prop("c"))),
                Formula::atom(prop("d")),
            ),
        );
        assert_eq!(formula.dual(), desired);
    }
    #[test]
    fn test_nnf() {
        let formula = Formula::and(
            Formula::not(Formula::not(Formula::atom(prop("A")))),
            Formula::or(Formula::False, Formula::atom(prop("B"))),
        );

        let desired = Formula::and(Formula::atom(prop("A")), Formula::atom(prop("B")));
        assert_eq!(formula.nnf(), desired);

        let formula = Formula::not(Formula::and(
            Formula::atom(prop("A")),
            Formula::or(Formula::atom(prop("B")), Formula::atom(prop("C"))),
        ));
        let desired = Formula::or(
            Formula::not(Formula::atom(prop("A"))),
            Formula::and(
                Formula::not(Formula::atom(prop("B"))),
                Formula::not(Formula::atom(prop("C"))),
            ),
        );
        assert_eq!(formula.nnf(), desired);

        let formula = Formula::not(Formula::imp(
            Formula::atom(prop("A")),
            Formula::iff(Formula::atom(prop("B")), Formula::atom(prop("C"))),
        ));
        let desired = Formula::and(
            Formula::atom(prop("A")),
            Formula::or(
                Formula::and(
                    Formula::atom(prop("B")),
                    Formula::not(Formula::atom(prop("C"))),
                ),
                Formula::and(
                    Formula::not(Formula::atom(prop("B"))),
                    Formula::atom(prop("C")),
                ),
            ),
        );
        assert_eq!(formula.nnf(), desired);
    }

    #[test]
    fn test_nenf() {
        let formula = Formula::not(Formula::and(
            Formula::atom(prop("A")),
            Formula::or(Formula::atom(prop("B")), Formula::atom(prop("C"))),
        ));
        let desired = Formula::or(
            Formula::not(Formula::atom(prop("A"))),
            Formula::and(
                Formula::not(Formula::atom(prop("B"))),
                Formula::not(Formula::atom(prop("C"))),
            ),
        );
        assert_eq!(formula.nenf(), desired);

        let formula = Formula::not(Formula::imp(
            Formula::atom(prop("A")),
            Formula::iff(Formula::atom(prop("B")), Formula::atom(prop("C"))),
        ));
        let desired = Formula::and(
            Formula::atom(prop("A")),
            Formula::iff(
                Formula::atom(prop("B")),
                Formula::not(Formula::atom(prop("C"))),
            ),
        );
        assert_eq!(formula.nenf(), desired);
    }

    // #[test]
    // fn test_make_lits() {
    //     let valuation = BTreeMap::from([(prop("A"), false), (prop("B"), false), (prop("C"), true)]);
    //     let items = vec![
    //         Formula::atom(prop("A")),
    //         Formula::and(Formula::atom(prop("B")), Formula::atom(prop("C"))),
    //         Formula::atom(prop("C")),
    //     ];
    //     let result = Formula::make_lits(&items, &valuation);
    //     let desired = Formula::and(
    //         Formula::and(
    //             Formula::not(Formula::atom(prop("A"))),
    //             Formula::not(Formula::and(
    //                 Formula::atom(prop("B")),
    //                 Formula::atom(prop("C")),
    //             )),
    //         ),
    //         Formula::atom(prop("C")),
    //     );
    //     assert_eq!(result, desired);
    // }

    // #[test]
    // fn test_all_sat_valuations() {
    //     let formula = Formula::or(
    //         Formula::and(Formula::atom(prop("A")), Formula::atom(prop("B"))),
    //         Formula::atom(prop("C")),
    //     );

    //     let result = formula.all_sat_valuations();
    //     let desired = vec![
    //         BTreeMap::from([(prop("A"), true), (prop("B"), true), (prop("C"), true)]),
    //         BTreeMap::from([(prop("A"), true), (prop("B"), true), (prop("C"), false)]),
    //         BTreeMap::from([(prop("A"), true), (prop("B"), false), (prop("C"), true)]),
    //         BTreeMap::from([(prop("A"), false), (prop("B"), true), (prop("C"), true)]),
    //         BTreeMap::from([(prop("A"), false), (prop("B"), false), (prop("C"), true)]),
    //     ];

    //     assert_eq!(result, desired);
    // }

    // #[test]
    // fn test_naive_dnf() {
    //     let formula = Formula::or(
    //         Formula::and(Formula::atom(prop("A")), Formula::atom(prop("B"))),
    //         Formula::atom(prop("C")),
    //     );
    //     let desired = Formula::list_disj(&vec![
    //         Formula::and(
    //             Formula::and(Formula::atom(prop("A")), Formula::atom(prop("B"))),
    //             Formula::atom(prop("C")),
    //         ),
    //         Formula::and(
    //             Formula::and(Formula::atom(prop("A")), Formula::atom(prop("B"))),
    //             Formula::not(Formula::atom(prop("C"))),
    //         ),
    //         Formula::and(
    //             Formula::and(
    //                 Formula::atom(prop("A")),
    //                 Formula::not(Formula::atom(prop("B"))),
    //             ),
    //             Formula::atom(prop("C")),
    //         ),
    //         Formula::and(
    //             Formula::and(
    //                 Formula::not(Formula::atom(prop("A"))),
    //                 Formula::atom(prop("B")),
    //             ),
    //             Formula::atom(prop("C")),
    //         ),
    //         Formula::and(
    //             Formula::and(
    //                 Formula::not(Formula::atom(prop("A"))),
    //                 Formula::not(Formula::atom(prop("B"))),
    //             ),
    //             Formula::atom(prop("C")),
    //         ),
    //     ]);
    //     assert_eq!(formula.naive_dnf(), desired);
    // }

    // #[test]
    // fn test_raw_dnf() {
    //     let formula = Formula::and(
    //         Formula::or(
    //             Formula::not(Formula::atom(prop("A"))),
    //             Formula::and(
    //                 Formula::atom(prop("B")),
    //                 Formula::or(Formula::atom(prop("C")), Formula::atom(prop("D"))),
    //             ),
    //         ),
    //         Formula::atom(prop("E")),
    //     );

    //     let desired = Formula::or(
    //         Formula::and(
    //             Formula::not(Formula::atom(prop("A"))),
    //             Formula::atom(prop("E")),
    //         ),
    //         Formula::or(
    //             Formula::and(
    //                 Formula::and(Formula::atom(prop("B")), Formula::atom(prop("C"))),
    //                 Formula::atom(prop("E")),
    //             ),
    //             Formula::and(
    //                 Formula::and(Formula::atom(prop("B")), Formula::atom(prop("D"))),
    //                 Formula::atom(prop("E")),
    //             ),
    //         ),
    //     );

    //     assert_eq!(formula.raw_dnf(), desired);
    // }

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
        let formula = Formula::or(
            Formula::False,
            // After distrib:  [ (A & True & A) V (A & True & D & C) V (B & C & A) V (B & C & D) ]
            Formula::and(
                Formula::or(
                    Formula::and(Formula::atom(prop("A")), Formula::True),
                    Formula::and(Formula::atom(prop("B")), Formula::atom(prop("C"))),
                ),
                Formula::or(
                    Formula::atom(prop("A")),
                    Formula::and(Formula::atom(prop("D")), Formula::atom(prop("C"))),
                ),
            ),
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
        let formula = Formula::and(
            Formula::or(
                Formula::and(
                    Formula::atom(prop("A")),
                    Formula::or(Formula::True, Formula::atom(prop("E"))),
                ),
                Formula::and(Formula::atom(prop("B")), Formula::atom(prop("C"))),
            ),
            Formula::or(
                Formula::or(
                    Formula::not(Formula::atom(prop("A"))),
                    Formula::and(Formula::False, Formula::atom(prop("F"))),
                ),
                Formula::and(Formula::atom(prop("D")), Formula::atom(prop("C"))),
            ),
        );
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
        let formula = Formula::and(
            Formula::or(
                Formula::and(Formula::atom(prop("A")), Formula::True),
                Formula::and(
                    Formula::atom(prop("B")),
                    Formula::not(Formula::atom(prop("B"))),
                ),
            ),
            Formula::or(
                Formula::atom(prop("B")),
                Formula::and(Formula::atom(prop("D")), Formula::atom(prop("C"))),
            ),
        );
        let result = formula.dnf();
        let desired = Formula::or(
            Formula::and(Formula::atom(prop("A")), Formula::atom(prop("B"))),
            Formula::and(
                Formula::and(Formula::atom(prop("A")), Formula::atom(prop("C"))),
                Formula::atom(prop("D")),
            ),
        );
        assert_eq!(result, desired);
    }

    #[test]
    fn test_dnf_unsatisfiable() {
        // Should be False on contradictions.
        let formula = Formula::and(
            Formula::atom(prop("P")),
            Formula::not(Formula::atom(prop("P"))),
        );
        assert_eq!(formula.dnf(), Formula::False);
    }

    #[test]
    fn test_cnf_tautology() {
        // Should be True on tautologies.
        let formula = Formula::or(
            Formula::atom(prop("P")),
            Formula::not(Formula::atom(prop("P"))),
        );
        assert_eq!(formula.cnf(), Formula::True);
    }

    #[test]
    fn test_cnf() {
        let formula = Formula::and(
            Formula::or(
                Formula::and(
                    Formula::atom(prop("A")),
                    Formula::or(Formula::True, Formula::atom(prop("E"))),
                ),
                Formula::and(Formula::atom(prop("B")), Formula::atom(prop("C"))),
            ),
            Formula::or(
                Formula::or(
                    Formula::not(Formula::atom(prop("A"))),
                    Formula::and(Formula::False, Formula::atom(prop("F"))),
                ),
                Formula::and(Formula::atom(prop("D")), Formula::atom(prop("C"))),
            ),
        );

        let desired = Formula::list_conj(&vec![
            Formula::or(Formula::atom(prop("A")), Formula::atom(prop("B"))),
            Formula::or(Formula::atom(prop("A")), Formula::atom(prop("C"))),
            Formula::or(
                Formula::atom(prop("C")),
                Formula::not(Formula::atom(prop("A"))),
            ),
            Formula::or(
                Formula::atom(prop("D")),
                Formula::not(Formula::atom(prop("A"))),
            ),
        ]);
        assert_eq!(formula.cnf(), desired);
    }

    #[test]
    fn test_max_taken_index() {
        // Only valid taken indices are 3 and 5.
        let formula = Formula::and(
            Formula::and(
                Formula::and(
                    Formula::atom(prop("oranges")),
                    Formula::or(Formula::True, Formula::atom(Formula::_mkprop(3))),
                ),
                Formula::imp(Formula::atom(prop("B")), Formula::atom(prop("apples"))),
            ),
            Formula::or(
                Formula::or(
                    Formula::not(Formula::atom(prop("A"))),
                    Formula::iff(Formula::False, Formula::atom(Formula::_mkprop(5))),
                ),
                Formula::and(Formula::atom(prop("D")), Formula::atom(prop("11"))),
            ),
        );
        let result = Formula::_max_taken_index(&formula);
        assert_eq!(result, 5);
    }

    #[test]
    fn test_is_cnf() {
        // YES
        let formula = Formula::and(
            Formula::not(Formula::atom(prop("A"))),
            Formula::atom(prop("B")),
        );
        assert!(formula.is_cnf());
        // YES
        let formula = Formula::or(
            Formula::not(Formula::atom(prop("A"))),
            Formula::atom(prop("B")),
        );
        assert!(formula.is_cnf());
        // No
        let formula = Formula::or(
            Formula::and(Formula::atom(prop("A")), Formula::atom(prop("C"))),
            Formula::atom(prop("B")),
        );
        assert!(!formula.is_cnf());
        // YES
        let formula = Formula::and(
            Formula::or(
                Formula::or(Formula::atom(prop("D")), Formula::atom(prop("A"))),
                Formula::atom(prop("C")),
            ),
            Formula::atom(prop("B")),
        );
        assert!(formula.is_cnf());
    }

    #[test]
    fn test_def_cnf_full_trivial() {
        let formula = Formula::atom(prop("A"));
        let result = formula.def_cnf_full();
        assert_eq!(result, formula);
    }

    #[test]
    fn test_def_cnf_opt_trivial() {
        let formula = Formula::atom(prop("A"));
        let result = formula.def_cnf_opt();
        assert_eq!(result, formula);
    }

    #[test]
    fn test_def_cnf_full_nontrivial() {
        let formula = Formula::and(Formula::atom(prop("A")), Formula::atom(prop("B")));
        let result = formula.def_cnf_full();
        let p = Formula::_mkprop(0);
        let desired_equiv = Formula::and(
            Formula::atom(p.clone()),
            Formula::iff(
                Formula::atom(p),
                Formula::and(Formula::atom(prop("A")), Formula::atom(prop("B"))),
            ),
        );

        // Since we know that `desired_equiv` is equisatisfiable with the input `formula`
        // the following shows that the result is equisatisfiable with the input `formula`.
        assert!(result.equivalent(&desired_equiv));
        assert!(result.is_cnf());
    }

    #[test]
    fn test_def_cnf_opt_nontrivial() {
        let formula = Formula::and(Formula::atom(prop("A")), Formula::atom(prop("B")));
        let result = formula.def_cnf_opt();
        assert_eq!(result, formula);
    }

    #[test]
    fn test_def_cnf_full_lesstrivial() {
        let formula = Formula::or(
            Formula::imp(Formula::atom(prop("A")), Formula::atom(prop("B"))),
            Formula::and(Formula::atom(prop("C")), Formula::atom(prop("D"))),
        );
        let result = formula.def_cnf_full();
        let desired_equiv = Formula::list_conj(&vec![
            // _mkprop(0)
            Formula::iff(
                Formula::atom(Formula::_mkprop(0)),
                Formula::or(
                    Formula::not(Formula::atom(prop("A"))),
                    Formula::atom(prop("B")),
                ),
            ),
            // _mkprop(1)
            Formula::iff(
                Formula::atom(Formula::_mkprop(1)),
                Formula::and(Formula::atom(prop("C")), Formula::atom(prop("D"))),
            ),
            // _mkprop(2)
            Formula::iff(
                Formula::atom(Formula::_mkprop(2)),
                Formula::or(
                    Formula::atom(Formula::_mkprop(0)),
                    Formula::atom(Formula::_mkprop(1)),
                ),
            ),
            Formula::atom(Formula::_mkprop(2)),
        ]);

        // Since we know that `desired_equiv` is equisatisfiable with the input `formula`
        // the following shows that the result is equisatisfiable with the input `formula`.
        assert!(result.equivalent(&desired_equiv));
        // Check already in cnf form
        assert!(result.is_cnf());
    }

    #[test]
    fn test_def_cnf_opt_lesstrivial() {
        let formula = Formula::or(
            Formula::atom(prop("A")),
            Formula::and(Formula::atom(prop("B")), Formula::atom(prop("C"))),
        );
        let result = formula.def_cnf_opt();
        // Note the top nodes of the tree are preserved.
        let desired = Formula::and(
            Formula::or(Formula::atom(prop("A")), Formula::atom(prop("B"))),
            Formula::or(Formula::atom(prop("A")), Formula::atom(prop("C"))),
        );
        assert_eq!(result, desired);
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
        let formula_set = BTreeSet::from([
            BTreeSet::from([Formula::not(Formula::atom(prop("A")))]),
        ]);
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
        let desired = desired_product.union(&desired_rest).cloned().collect();
        assert_eq!(result, desired)
    }

    #[test]
    fn test_find_min() {
        // Just use the (negative of the) length of the formula for a test optimum.
        let opt = |formula: &Formula<Prop>| -(format!("{:?}", formula).len() as isize);
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

    // #[test]
    // fn test_dp() {
    //     let formula_set = BTreeSet::from([
    //         BTreeSet::from([
    //             Formula::atom(prop("A")),
    //             Formula::not(Formula::atom(prop("C"))),
    //         ]),
    //         BTreeSet::from([
    //             Formula::not(Formula::atom(prop("D"))),
    //             Formula::atom(prop("C")),
    //         ]),
    //         BTreeSet::from([
    //             Formula::not(Formula::atom(prop("A"))),
    //             Formula::atom(prop("D")),
    //         ]),
    //         BTreeSet::from([Formula::atom(prop("A")), Formula::atom(prop("C"))]),
    //         BTreeSet::from([
    //             Formula::not(Formula::atom(prop("A"))),
    //             Formula::not(Formula::atom(prop("C"))),
    //         ]),
    //     ]);

    //     let result = Formula::dp(&formula_set);
    //     let desired = false;
    //     assert_eq!(result, desired);
    // }

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

// END TESTS
//
// Applications

// Ramsey Theory
// Given x, y, Compute a predicate for n > R(x, y).
// (That is, for any graph of size n,
// there exists either a subgraph of size x that is fully connected or
// a subgraph of size y that is fully disconnected (the antigraph is fully connected).
// "Any graph of size n" here is will be n^2 propositional atoms ranging over logical space.
// contrained by formulas representing the contraint about subsets.
//
// fn ramsey(x: u32, y: u32, n: u32) -> Formula<Prop> {
//     // A function outputing proposition names for propositions representing
//     // that two nodes a and b are connected by an edge.
//     fn label(a: u32, b: u32) -> String {
//         format!("CON_{a}_{b}", a, b);
//     }
//
//     //Subsets of size x:
//
//     //some subgraph of size x is fully connected);
//     let con = Formula::list_dist();
//
//     //Subsets of size y:
//     // ...
//     //some subgraph of size y is fully connected);
//     let dis = Formula::list_dist();
//
//     Formula::or(con, dis)
//
// Adder
//

fn adder(
    x: &Formula<Prop>,
    y: &Formula<Prop>,
    z: &Formula<Prop>,
    s: &Formula<Prop>,
    c: &Formula<Prop>,
) -> Formula<Prop> {
    // Exactly one or exactly three.
    let sum = Formula::iff(
        Formula::iff(x.clone(), Formula::not(y.clone())),
        Formula::not(z.clone()),
    );
    // Equiv to at least two
    let carry = Formula::list_disj(&vec![
        Formula::and(x.clone(), y.clone()),
        Formula::and(x.clone(), z.clone()),
        Formula::and(y.clone(), z.clone()),
    ]);
    let result = Formula::and(Formula::iff(s.clone(), sum), Formula::iff(c.clone(), carry));
    result.psimplify()
}

pub fn ripplecarry(
    x: &Vec<Formula<Prop>>,
    y: &Vec<Formula<Prop>>,
    carry: &Vec<Formula<Prop>>,
    out: &Vec<Formula<Prop>>,
    n: usize,
) -> Formula<Prop> {
    /* Assumes that bits with greater indices in  x, y, etc correspond to
     * more significant digits
     */

    assert_eq!(x.len(), n);
    assert_eq!(y.len(), n);
    assert_eq!(carry.len(), n);
    assert_eq!(out.len(), n + 1);

    // Set initial carry bit to zero.
    let mut carry = carry.clone();
    carry.insert(0, Formula::False);

    // conjoin that out[n] <==> carry[n]
    let adders = Formula::list_conj(
        &(0..n)
            .map(|idx| adder(&x[idx], &y[idx], &carry[idx], &out[idx], &carry[idx + 1]))
            .collect(),
    );
    let final_carry_is_final_out = Formula::iff(out[n].clone(), carry[n].clone());
    let result = Formula::and(adders, final_carry_is_final_out);
    result.psimplify()
}

#[cfg(test)]
mod adder_tests {
    use super::*;

    #[test]
    fn test_adder_standard_tautologies() {
        assert_eq!(
            adder(
                &Formula::True,
                &Formula::True,
                &Formula::True,
                &Formula::True,
                &Formula::True,
            ),
            Formula::True
        );

        assert_eq!(
            adder(
                &Formula::True,
                &Formula::True,
                &Formula::False,
                &Formula::False,
                &Formula::True,
            ),
            Formula::True
        );

        assert_eq!(
            adder(
                &Formula::True,
                &Formula::False,
                &Formula::True,
                &Formula::False,
                &Formula::True,
            ),
            Formula::True
        );

        assert_eq!(
            adder(
                &Formula::True,
                &Formula::False,
                &Formula::False,
                &Formula::True,
                &Formula::False,
            ),
            Formula::True
        );

        assert_eq!(
            adder(
                &Formula::False,
                &Formula::True,
                &Formula::True,
                &Formula::False,
                &Formula::True,
            ),
            Formula::True
        );

        assert_eq!(
            adder(
                &Formula::False,
                &Formula::True,
                &Formula::False,
                &Formula::True,
                &Formula::False,
            ),
            Formula::True
        );

        assert_eq!(
            adder(
                &Formula::False,
                &Formula::False,
                &Formula::True,
                &Formula::True,
                &Formula::False,
            ),
            Formula::True
        );

        assert_eq!(
            adder(
                &Formula::False,
                &Formula::False,
                &Formula::False,
                &Formula::False,
                &Formula::False,
            ),
            Formula::True
        );
    }

    #[test]
    fn test_adder_some_more() {
        assert_eq!(
            adder(
                &Formula::True,
                &Formula::True,
                &Formula::False,
                &Formula::True,
                &Formula::True,
            ),
            Formula::False
        );

        assert_eq!(
            adder(
                &Formula::True,
                &Formula::True,
                &Formula::False,
                &Formula::False,
                &Formula::True,
            ),
            Formula::True
        );
    }

    #[test]
    fn test_adder_prop_variables() {
        let formula = adder(
            &Formula::True,
            &Formula::atom(prop("Y")),
            &Formula::True,
            &Formula::atom(prop("Sum")),
            &Formula::atom(prop("Carry")),
        );
        assert!(!formula.tautology());
        assert!(formula.satisfiable());
    }

    #[test]
    fn test_ripplecarry() {
        let n = 3;
        //
        // Greater indices should correspond to more significant digits so e.g.
        // 3 = (bin) [1 1 0] =
        let x = vec![Formula::True, Formula::True, Formula::False];
        // 5 = (bin) [1 0 1] =
        let y = vec![Formula::True, Formula::False, Formula::True];
        let symbolic_carry = vec![
            Formula::atom(prop("C1")),
            Formula::atom(prop("C2")),
            Formula::atom(prop("C3")),
        ];
        let out_correct = vec![
            Formula::False,
            Formula::False,
            Formula::False,
            Formula::True,
        ]; // 0 0 0 1 (8)
        let formula = ripplecarry(&x, &y, &symbolic_carry, &out_correct, n);
        // It is possible to find carries that satisfy the Formula.
        assert!(formula.dpll_sat());
        assert!(!formula.dpll_taut());

        let out_false = vec![
            Formula::False,
            Formula::False,
            Formula::True,
            Formula::False,
        ]; // 0 0 1 0 (4)
        let formula = ripplecarry(&x, &y, &symbolic_carry, &out_false, n);
        let mut output = std::io::stdout();
        formula.pprint(&mut output);
        // It is *not* possible to find carries that satisfy the Formula.
        assert!(!formula.dpll_sat());
    }
}
