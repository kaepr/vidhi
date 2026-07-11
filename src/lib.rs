use std::collections::HashMap;

/// Represents a concrete value.
#[derive(Debug, PartialEq, Clone)]
pub enum Atom {
    String(String),
    Number(isize),
}

/// Represents a variable.
#[derive(Debug, Clone, PartialEq, Hash)]
pub struct Variable {
    pub name: String,
}

/// Represents either a variable or a concrete value.
#[derive(Debug, PartialEq, Clone)]
pub enum Term {
    Literal(Atom),
    Variable(Variable),
}

/// Represents the facts in our database.
#[derive(Debug, PartialEq, Clone)]
pub struct Fact {
    pub entity: Atom,
    pub attribute: Atom,
    pub value: Atom,
}

/// A pattern to create rules.
#[derive(Debug, PartialEq, Clone)]
pub struct Pattern {
    pub entity: Term,
    pub attribute: Term,
    pub value: Term,
}

/// Binds a variable to a concrete value.
pub type Bindings = HashMap<Variable, Atom>;

pub fn unify(pattern: &Pattern, fact: &Fact, bindings: &Bindings) -> Option<Bindings> {
    todo!()
}

#[cfg(test)]
mod tests {
    use super::*;
    use test_that::prelude::*;

    #[test_that::test]
    fn test_fact() {
        let fact = Fact {
            entity: Atom::String("player".to_string()),
            attribute: Atom::String("health".to_string()),
            value: Atom::Number(10),
        };

        expect_that!(fact.value, eq(Atom::Number(10)));
    }
}
