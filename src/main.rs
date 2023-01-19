#![feature(box_patterns)]

use harrison_rust::applications_propositional::ripplecarry;
use harrison_rust::first_order_logic::{Interpretation, Language, Pred, Valuation};
use harrison_rust::formula::Formula;
use harrison_rust::propositional_logic::Prop;

use std::collections::{HashMap, HashSet};

use std::io::stdout;

fn main() {
    let mut stdout = stdout();

    // ### PROPOSITIONAL LOGIC ###

    // Example 1:  Simple formula.
    println!("\nExample 1: Simple formula");
    let formula = Formula::<Prop>::parse("C \\/ D <=> (~A /\\ B)");
    formula.pprint(&mut stdout);
    formula.print_truthtable(&mut stdout);
    let cnf = Formula::cnf(&formula);
    cnf.pprint(&mut stdout);
    // Satisfiable
    assert!(formula.dpll_sat());
    // Not a tautology
    assert!(!formula.dpll_taut());
    //
    // Example 2:  A tautology
    println!("\nExample 2: Simple formula");
    let formula = Formula::<Prop>::parse("A \\/ ~A");
    formula.pprint(&mut stdout);
    formula.print_truthtable(&mut stdout);
    let cnf = Formula::cnf(&formula);
    cnf.pprint(&mut stdout);
    // A tautology
    assert!(formula.dpll_taut());

    // Example 3:  A contradiction
    println!("\nExample 3: Simple formula");
    let formula = Formula::<Prop>::parse("~A /\\ A");
    formula.pprint(&mut stdout);
    formula.print_truthtable(&mut stdout);
    let dnf = Formula::dnf(&formula);
    dnf.pprint(&mut stdout);
    // A contradiction.
    assert!(!formula.dpll_sat());
    // ...this means, it's negation is a tautology.
    let negation = Formula::not(formula);
    assert!(negation.dpll_taut());

    // Example 4: Simplification
    println!("\nExample 4: Formula simplification");
    let formula = Formula::<Prop>::parse("((true ==> (x <=> false)) ==> ~(y \\/ (false /\\ z)))");
    let simplified = formula.psimplify();
    simplified.pprint(&mut stdout);

    // Example 5:
    println!("\nExample 5: Ripple Carry");
    // The function `ripplecarry` below defines an array of `num_bits`-many full-adders
    // interconnected as usual.
    let num_bits = 3;
    // Greater indices should correspond to more significant digits so e.g.
    // 3 = (bin) [1 1 0] =
    let x = vec![Formula::True, Formula::True, Formula::False];
    // 5 = (bin) [1 0 1] =
    let y = vec![Formula::True, Formula::False, Formula::True];
    let symbolic_carry = vec![
        Formula::atom(Prop::new("C1")),
        Formula::atom(Prop::new("C2")),
        Formula::atom(Prop::new("C3")),
    ];
    let out = vec![
        Formula::False,
        Formula::False,
        Formula::False,
        Formula::True,
    ]; // 0 0 0 1 (8)
    let formula = ripplecarry(&x, &y, &symbolic_carry, &out, num_bits);

    // This is accurate, but our formula simplfier could use some improvement.
    formula.pprint(&mut stdout);

    // (DPLL method for computing Sat).
    assert!(formula.dpll_sat());
    assert!(!formula.dpll_taut());
    println!("\n");

    // ### PREDICATE LOGIC ###

    // ### Arithmetic mod n (n >= 2) ###
    println!("Example 6: Arithmetic mod n (n >= 2)\n");

    fn integers_mod_n(n: u32) -> Interpretation<u32> {
        assert!(n > 1);

        type FuncType = dyn Fn(&[u32]) -> u32;
        type RelType = dyn Fn(&[u32]) -> bool;

        let lang = Language {
            func: HashMap::from([
                ("+".to_string(), 2),
                ("*".to_string(), 2),
                ("0".to_string(), 0),
                ("1".to_string(), 0),
            ]),
            rel: HashMap::from([("=".to_string(), 2)]),
        };

        let domain: HashSet<u32> = HashSet::from_iter(0..n);

        let addition = move |inputs: &[u32]| -> u32 { (inputs[0] + inputs[1]) % n };
        let multiplication = move |inputs: &[u32]| -> u32 { (inputs[0] * inputs[1]) % n };
        let zero = |_inputs: &[u32]| -> u32 { 0 };
        let one = |_inputs: &[u32]| -> u32 { 1 };

        fn equality(inputs: &[u32]) -> bool {
            inputs[0] == inputs[1]
        }

        let funcs: HashMap<String, Box<FuncType>> = HashMap::from([
            ("+".to_string(), Box::new(addition) as Box<FuncType>),
            ("*".to_string(), Box::new(multiplication) as Box<FuncType>),
            ("0".to_string(), Box::new(zero) as Box<FuncType>),
            ("1".to_string(), Box::new(one) as Box<FuncType>),
        ]);
        let rels: HashMap<String, Box<RelType>> =
            HashMap::from([("=".to_string(), Box::new(equality) as Box<RelType>)]);

        Interpretation::new(&lang, domain, funcs, rels)
    }

    // Let's verify (for n < 20) that the integers mod n form a field
    // (have multiplicative inverses) if and only if n is prime.
    let mult_inverse = "forall x. ~(x = 0) ==> exists y. x * y = 1";
    let mult_inverse_formula = Formula::<Pred>::parse(mult_inverse);
    let empty_valuation = Valuation::new();
    println!("Model:         |  Is a field?");
    for n in 2..20 {
        let interpretation = integers_mod_n(n);
        let sat = mult_inverse_formula.eval(&interpretation, &empty_valuation);
        println!("Integers mod {n}:  {sat}");
    }
}
