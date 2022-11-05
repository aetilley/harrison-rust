#![feature(box_patterns)]

use harrison_rust::formula::Formula;
use harrison_rust::propositional_logic::{prop, ripplecarry};

use std::io::stdout;

fn main() {
    let mut stdout = stdout();
	
	// Example 1:  Simple formula.
    println!("\nExample 1: Simple formula");
    let formula = Formula::parse("C \\/ D <=> (~A /\\ B)"); 
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
    let formula = Formula::parse("A \\/ ~A"); 
    formula.pprint(&mut stdout);
    formula.print_truthtable(&mut stdout);
	let cnf = Formula::cnf(&formula);
    cnf.pprint(&mut stdout);
    // A tautology
    assert!(formula.dpll_taut());

	// Example 3:  A contradiction 
    println!("\nExample 3: Simple formula");
    let formula = Formula::parse("~A /\\ A"); 
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
    let formula = Formula::parse("((true ==> (x <=> false)) ==> ~(y \\/ (false /\\ z)))"); 
    let simplified = formula.psimplify();
    simplified.pprint(&mut stdout);



    // Example 0:  
    println!("\nRipple Carry");
    // The function `ripplecarry` below defines an array of `num_bits`-many full-adders
    // interconnected as usual.
    let num_bits = 3;
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
    let out = vec![
        Formula::False,
        Formula::False,
        Formula::False,
        Formula::True,
    ]; // 0 0 0 1 (8)
    let formula = ripplecarry(&x, &y, &symbolic_carry, &out, num_bits);
    formula.pprint(&mut stdout);

	// (DPLL method for computing Sat).
    assert!(formula.dpll_sat());
    assert!(!formula.dpll_taut());
}
