use std::collections::HashMap;

/// Represents a concrete value.
#[derive(Debug, PartialEq, Clone)]
pub enum Atom {
    String(String),
    Number(isize),
}

impl From<isize> for Atom {
    fn from(value: isize) -> Self {
        Atom::Number(value)
    }
}

impl From<&str> for Atom {
    fn from(value: &str) -> Self {
        Atom::String(value.to_string())
    }
}

/// Represents a variable.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Variable {
    pub name: String,
}

impl From<&str> for Variable {
    fn from(value: &str) -> Self {
        Variable {
            name: value.to_string(),
        }
    }
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

/// Tries to unify a pattern to a fact, and returns updated bindings if found.
pub fn unify(pattern: &Pattern, fact: &Fact, bindings: &Bindings) -> Option<Bindings> {
    let mut bindings = bindings.clone();
    unify_slot(&pattern.entity, &fact.entity, &mut bindings)?;
    unify_slot(&pattern.attribute, &fact.attribute, &mut bindings)?;
    unify_slot(&pattern.value, &fact.value, &mut bindings)?;
    Some(bindings)
}

fn unify_slot(term: &Term, atom: &Atom, bindings: &mut Bindings) -> Option<()> {
    match term {
        Term::Literal(l) => (l == atom).then_some(()),
        Term::Variable(v) => match bindings.get(v) {
            Some(l) => (l == atom).then_some(()),
            None => {
                bindings.insert(v.clone(), atom.clone());
                Some(())
            }
        },
    }
}

/// Find's all possible bindings for given database and conditions.
pub fn match_rule(conditions: &[Pattern], facts: &[Fact], bindings: &Bindings) -> Vec<Bindings> {
    match conditions.split_first() {
        Some((first, rest)) => {
            let mut results = Vec::new();
            for fact in facts {
                if let Some(new_bindings) = unify(first, fact, bindings) {
                    results.extend(match_rule(rest, facts, &new_bindings));
                }
            }
            results
        }
        None => vec![bindings.clone()],
    }
}

#[macro_export]
macro_rules! atom {
    ($lit:literal) => {
        Atom::from($lit)
    };
    ($name:ident) => {
        Atom::from(stringify!($name))
    };
}

#[macro_export]
macro_rules! variable {
    ($name:ident) => {
        Variable::from(stringify!($name))
    };
}

#[macro_export]
macro_rules! fact {
    ($e: tt, $a: tt, $v: tt) => {
        Fact {
            entity: atom!($e),
            attribute: atom!($a),
            value: atom!($v),
        }
    };
}

#[macro_export]
macro_rules! pattern {
    (? $e:ident, $($rest:tt)*) => {
        pattern!(@attr Term::Variable(variable!($e)), $($rest)*)
    };
    ($e:tt, $($rest:tt)*) => {
        pattern!(@attr Term::Literal(atom!($e)), $($rest)*)
    };
    (@attr $entity:expr, ? $a:ident, $($rest:tt)*) => {
        pattern!(@val $entity, Term::Variable(variable!($a)), $($rest)*)
    };
    (@attr $entity:expr, $a:tt, $($rest:tt)*) => {
        pattern!(@val $entity, Term::Literal(atom!($a)), $($rest)*)
    };
    (@val $entity:expr, $attribute:expr, ? $v:ident) => {
        Pattern {
            entity: $entity,
            attribute: $attribute,
            value: Term::Variable(variable!($v))
        }
    };
    (@val $entity:expr, $attribute:expr, $v:tt) => {
        Pattern {
            entity: $entity,
            attribute: $attribute,
            value: Term::Literal(atom!($v))
        }
    };
}

#[cfg(test)]
mod tests {
    use super::*;
    use test_that::prelude::*;

    #[test_that::test]
    fn test_atom() {
        let atom = atom!(10);
        expect_that!(atom, eq(Atom::Number(10)));

        let atom = atom!(player);
        expect_that!(atom, eq(Atom::String("player".to_string())));
    }

    #[test_that::test]
    fn test_fact() {
        let fact = fact!(player, health, 10);

        expect_that!(
            fact,
            eq(Fact {
                entity: Atom::String("player".to_string()),
                attribute: Atom::String("health".to_string()),
                value: Atom::Number(10),
            })
        );
    }

    #[test_that::test]
    fn test_variable() {
        let variable = variable!(e);
        expect_that!(variable, eq(Variable::from("e")));
    }

    #[test_that::test]
    fn test_pattern() {
        let pattern = pattern!(?e, health, 10);
        expect_that!(
            pattern,
            eq(Pattern {
                entity: Term::Variable("e".into()),
                attribute: Term::Literal("health".into()),
                value: Term::Literal(10.into()),
            })
        );
        let pattern = pattern!(?e, ?a, ?v);
        expect_that!(
            pattern,
            eq(Pattern {
                entity: Term::Variable("e".into()),
                attribute: Term::Variable("a".into()),
                value: Term::Variable("v".into()),
            })
        );
    }

    #[test_that::test]
    fn test_unify() {
        // new variables
        let bindings = Bindings::new();
        let result = unify(&pattern!(?e, age, ?a), &fact!(alice, age, 30), &bindings);
        let expected = Bindings::from([
            (variable!(e), Atom::from("alice")),
            (variable!(a), Atom::from(30)),
        ]);
        expect_that!(result, some(eq(expected)));

        // conflicts
        let bindings = Bindings::from([(variable!(e), Atom::from("alice"))]);
        let result = unify(
            &pattern!(?e, likes, pizza),
            &fact!(bob, likes, pizza),
            &bindings,
        );
        expect_that!(result, none());
    }

    #[test_that::test]
    fn test_match_rule() {
        let facts = [
            fact!(alice, likes, pizza),
            fact!(alice, age, 30),
            fact!(bob, likes, pasta),
            fact!(bob, age, 25),
        ];
        // single fact found
        let conditions = [pattern!(?e, age, ?a), pattern!(?e, likes, pizza)];
        let bindings = Bindings::new();

        let result = match_rule(&conditions, &facts, &bindings);

        let expected = Bindings::from([
            (variable!(e), Atom::from("alice")),
            (variable!(a), Atom::from(30)),
        ]);
        expect_that!(result, contains_exactly!(eq(expected)));

        // multiple bindings found
        let conditions = [pattern!(?e, age, ?a)];
        let bindings = Bindings::new();

        let result = match_rule(&conditions, &facts, &bindings);

        let expected_alice = Bindings::from([
            (variable!(e), Atom::from("alice")),
            (variable!(a), Atom::from(30)),
        ]);
        let expected_bob = Bindings::from([
            (variable!(e), Atom::from("bob")),
            (variable!(a), Atom::from(25)),
        ]);
        expect_that!(
            result,
            contains_exactly!(eq(expected_alice), eq(expected_bob))
        );

        // no patterns matched
        let conditions = [pattern!(?e, likes, dosa)];
        let bindings = Bindings::new();

        let result = match_rule(&conditions, &facts, &bindings);

        expect_that!(result, empty());

        // existing bindings returned
        let bindings = Bindings::from([(variable!(e), Atom::from("alice"))]);

        let result = match_rule(&[], &facts, &bindings);

        expect_that!(result, contains_exactly!(eq(bindings)));
    }
}
