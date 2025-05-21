pub mod applications_propositional;
pub mod first_order_logic;
pub mod formula;
pub mod propositional_logic;
pub mod sudoku;
mod token;
pub mod utils;

use lalrpop_util::lalrpop_mod;
lalrpop_mod!(
    #[allow(unused_imports)]
    #[allow(unused_parens)]
    propositional_logic_grammar
);

lalrpop_mod!(
    #[allow(unused_imports)]
    #[allow(unused_parens)]
    first_order_logic_grammar
);
