A Rust library for SAT solving and automated theorem proving highly informed by 
John Harrison's text on Automated Theorem Proving.

(Harrison, J. (2009). Handbook of Practical Logic and Automated Reasoning. Cambridge: Cambridge University Press)

This package is still in its nascent stages, but the following are supported:

For propositional logic:
1) datatypes/parsing/printing operations
1) `eval`
1) standard DNF/CNF algorithms,
1) Definitional CNF (preserving equisatisfiability)
1) the DP and DPLL algorithms for testing satisfiability

For predicate (first-order) logic:
1) datatypes/parsing/printing operations

Example Usage:

```
#![feature(box_patterns)]

use harrison_rust::formula::Formula;
use harrison_rust::propositional_applications::ripplecarry;
use harrison_rust::propositional_logic::Prop;

use std::io::stdout;

fn main() {
    let mut stdout = stdout();

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
        Formula::atom(Prop::prop("C1")),
        Formula::atom(Prop::prop("C2")),
        Formula::atom(Prop::prop("C3")),
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

```

```
% cargo run
   Compiling harrison_rust v0.1.0 (/Users/arthurtilley/Dropbox/PersonalDrop/DropDev/harrison-rust)
    Finished dev [unoptimized + debuginfo] target(s) in 0.22s
     Running `...`

Example 1: Simple formula
<<C \/ D <=> ~A /\ B>>
A     B     C     D     | formula
---------------------------------
true  true  true  true  | false
true  true  true  false | false
true  true  false true  | false
true  true  false false | true
true  false true  true  | false
true  false true  false | false
true  false false true  | false
true  false false false | true
false true  true  true  | true
false true  true  false | true
false true  false true  | true
false true  false false | false
false false true  true  | false
false false true  false | false
false false false true  | false
false false false false | true
---------------------------------
<<((((((A \/ C) \/ D) \/ ~B) /\ (B \/ ~C)) /\ (B \/ ~D)) /\ (~A \/ ~C)) /\ (~A \/ ~D)>>

Example 2: Simple formula
<<A \/ ~A>>
A     | formula
---------------
true  | true
false | true
---------------
<<true>>

Example 3: Simple formula
<<~A /\ A>>
A     | formula
---------------
true  | false
false | false
---------------
<<false>>

Example 4: Formula simplification
<<~x ==> ~y>>

Ripple Carry
<<((C1 /\ C1 /\ (C2 <=> C1)) /\ C2 /\ (C3 <=> C2)) /\ C3>>
```

NOTE:  Currently this project RELIES ON NIGHTLY RUST, for exactly one feature `box_patterns`.
For more info, see
https://doc.rust-lang.org/beta/unstable-book/language-features/box-patterns.html

There is lots of room for improvement.  More to come.

For suggestions or questions please contact tilley@fastmail.com


