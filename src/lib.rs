use std::collections::{BTreeMap, HashMap, HashSet};
use std::mem;

use thiserror::Error;

/// Represents a concrete value.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
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

impl Term {
    pub fn as_variable(&self) -> Option<&Variable> {
        match self {
            Term::Variable(v) => Some(v),
            Term::Literal(_) => None,
        }
    }
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

impl Pattern {
    /// Returns all variables from this given pattern.
    fn variables(&self) -> impl Iterator<Item = &Variable> + '_ {
        [&self.entity, &self.attribute, &self.value]
            .into_iter()
            .filter_map(Term::as_variable)
    }
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
pub fn match_rule<'a, F>(conditions: &[Pattern], facts: F, bindings: &Bindings) -> Vec<Bindings>
where
    F: IntoIterator<Item = &'a Fact> + Clone,
{
    match conditions.split_first() {
        Some((first, rest)) => {
            let mut results = Vec::new();
            for fact in facts.clone() {
                if let Some(new_bindings) = unify(first, fact, bindings) {
                    results.extend(match_rule(rest, facts.clone(), &new_bindings));
                }
            }
            results
        }
        None => vec![bindings.clone()],
    }
}

/// Represents the working memory, comprised of facts.
///
/// # Invariant
///
/// - For a given (entity, attribute), only a single value can exist.
#[derive(Default)]
pub struct WorkingMemory {
    /// Maps a (entity, attribute) -> (entity, attribute, value)
    memory: BTreeMap<(Atom, Atom), Fact>,
}

/// Represents the change in working memory after an insert operation.
#[derive(Debug, PartialEq)]
pub enum InsertResult {
    /// A fresh fact was added.
    Added,
    /// An existing fact was updated. The old value is returned.
    Updated(Fact),
    /// No facts were changed.
    Unchanged,
}

impl WorkingMemory {
    pub fn insert(&mut self, fact: Fact) -> InsertResult {
        use std::collections::btree_map::Entry;

        match self
            .memory
            .entry((fact.entity.clone(), fact.attribute.clone()))
        {
            Entry::Vacant(e) => {
                e.insert(fact);
                InsertResult::Added
            }
            Entry::Occupied(mut e) => {
                if e.get().value == fact.value {
                    InsertResult::Unchanged
                } else {
                    InsertResult::Updated(e.insert(fact))
                }
            }
        }
    }

    pub fn retract(&mut self, entity: Atom, attribute: Atom) -> Option<Fact> {
        self.memory.remove(&(entity, attribute))
    }

    pub fn facts(&self) -> impl Iterator<Item = &Fact> + Clone {
        self.memory.values()
    }
}

/// Valid operations supported in a guard.
#[derive(Debug, Copy, Clone, PartialEq)]
pub enum Op {
    LessThan,
    LessThanEqual,
    GreaterThan,
    GreaterThanEqual,
    Equal,
    NotEqual,
}

/// Guards a rule.
#[derive(Debug, Clone, PartialEq)]
pub struct Guard {
    pub left: Term,
    pub op: Op,
    pub right: Term,
}

impl Guard {
    /// Returns all variables from this given pattern.
    fn variables(&self) -> impl Iterator<Item = &Variable> + '_ {
        [&self.left, &self.right]
            .into_iter()
            .filter_map(Term::as_variable)
    }
}

/// Action taken after a rule is matched.
#[derive(Debug, Clone)]
pub enum Action {
    Insert(Pattern),
}

impl Action {
    fn variables(&self) -> impl Iterator<Item = &Variable> + '_ {
        match self {
            Action::Insert(pattern) => pattern.variables(),
        }
    }
}

/// Represents a rule.
#[derive(Debug, Clone)]
pub struct Rule {
    pub name: String,
    pub conditions: Vec<Pattern>,
    pub guards: Vec<Guard>,
    pub actions: Vec<Action>,
}

impl Rule {
    pub fn new(
        name: impl AsRef<str>,
        conditions: Vec<Pattern>,
        guards: Vec<Guard>,
        actions: Vec<Action>,
    ) -> Result<Rule, RuleError> {
        let bounded: HashSet<&Variable> = conditions.iter().flat_map(Pattern::variables).collect();

        // finds first of possibly many unbounded variables
        let unbounded = guards
            .iter()
            .flat_map(Guard::variables)
            .chain(actions.iter().flat_map(Action::variables))
            .find(|&v| !bounded.contains(v));

        if let Some(v) = unbounded {
            return Err(RuleError::UnboundVariable(v.clone()));
        }

        Ok(Rule {
            name: name.as_ref().to_owned(),
            conditions,
            guards,
            actions,
        })
    }
}

/// Resolves a term to an atom.
pub fn resolve(term: &Term, bindings: &Bindings) -> Option<Atom> {
    match term {
        Term::Literal(atom) => Some(atom.clone()),
        Term::Variable(variable) => bindings.get(variable).cloned(),
    }
}

#[derive(Error, Debug, PartialEq)]
pub enum GuardError {
    #[error("unbound variable {}", .0.name)]
    UnboundVariable(Variable),
    #[error("type mismatch: cannot compare {left:?} with {right:?}")]
    TypeMismatch { left: Atom, right: Atom },
}

#[derive(Error, Debug)]
pub enum RuleError {
    #[error("unbound variable {0:?}")]
    UnboundVariable(Variable),
}

/// Resolves to an atom, or returns an error with the unbound variable.
fn resolve_or_err(term: &Term, bindings: &Bindings) -> Result<Atom, GuardError> {
    match term {
        Term::Literal(atom) => Ok(atom.clone()),
        Term::Variable(var) => bindings
            .get(var)
            .cloned()
            .ok_or_else(|| GuardError::UnboundVariable(var.clone())),
    }
}

/// Evaluates a guard given bindings.
///
/// # Errors
///
/// - Returns [GuardError::TypeMismatch] when incompatible types are compared.
/// - Returns [GuardError::UnboundVariable] when guard contains an unbound variable.
pub fn eval(guard: &Guard, bindings: &Bindings) -> Result<bool, GuardError> {
    let left = resolve_or_err(&guard.left, bindings)?;
    let right = resolve_or_err(&guard.right, bindings)?;

    if mem::discriminant(&left) != mem::discriminant(&right) {
        return Err(GuardError::TypeMismatch { left, right });
    }

    let result = match guard.op {
        Op::LessThan => left < right,
        Op::LessThanEqual => left <= right,
        Op::GreaterThan => left > right,
        Op::GreaterThanEqual => left >= right,
        Op::Equal => left == right,
        Op::NotEqual => left != right,
    };

    Ok(result)
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

#[macro_export]
macro_rules! guard {
    (@right $left:expr, $op:expr, ? $r:ident) => {
        Guard { left: $left, op: $op, right: Term::Variable(variable!($r)) }
    };
    (@right $left:expr, $op:expr, $r:tt) => {
        Guard { left: $left, op: $op, right: Term::Literal(atom!($r)) }
    };
    (@op $left:expr, <  $($rest:tt)*) => {
        guard!(@right $left, Op::LessThan,         $($rest)*)
    };
    (@op $left:expr, <= $($rest:tt)*) => {
        guard!(@right $left, Op::LessThanEqual,    $($rest)*)
    };
    (@op $left:expr, >  $($rest:tt)*) => {
         guard!(@right $left, Op::GreaterThan,      $($rest)*)
    };
    (@op $left:expr, >= $($rest:tt)*) => {
        guard!(@right $left, Op::GreaterThanEqual, $($rest)*)
    };
    (@op $left:expr, == $($rest:tt)*) => {
        guard!(@right $left, Op::Equal,            $($rest)*)
    };
    (@op $left:expr, != $($rest:tt)*) => {
        guard!(@right $left, Op::NotEqual,         $($rest)*)
    };
    (? $l:ident $($rest:tt)*) => {
        guard!(@op Term::Variable(variable!($l)), $($rest)*)
    };
    ($l:tt $($rest:tt)*)      => {
        guard!(@op Term::Literal(atom!($l)), $($rest)*)
    };
}

#[cfg(test)]
mod tests {
    use super::*;
    use test_that::prelude::*;

    fn guard(left: Term, op: Op, right: Term) -> Guard {
        Guard { left, op, right }
    }

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

    #[test_that::test]
    fn test_working_memory() {
        let mut wm = WorkingMemory::default();

        let result = wm.insert(fact!(player, health, 10));
        expect_that!(result, eq(InsertResult::Added));

        let result = wm.insert(fact!(player, health, 8));
        expect_that!(result, eq(InsertResult::Updated(fact!(player, health, 10))));
        let facts: Vec<Fact> = wm.facts().cloned().collect();
        expect_that!(facts, contains_exactly!(eq(fact!(player, health, 8))));

        let result = wm.retract("player".into(), "health".into());
        let facts: Vec<Fact> = wm.facts().cloned().collect();
        expect_that!(facts.len(), eq(0));
        expect_that!(result, some(eq(fact!(player, health, 8))));
    }

    #[test_that::test]
    fn test_eval() {
        let bindings = Bindings::from([
            (variable!(h), Atom::from(8)),
            (variable!(name), Atom::from("alice")),
        ]);

        // numeric smoke test
        let g = guard(
            Term::Variable(variable!(h)),
            Op::LessThan,
            Term::Literal(atom!(10)),
        );
        expect_that!(eval(&g, &bindings), eq(Ok(true)));

        // type mismatch
        let g = guard(
            Term::Variable(variable!(h)),
            Op::LessThan,
            Term::Literal(atom!(bob)),
        );
        expect_that!(
            eval(&g, &bindings),
            eq(Err(GuardError::TypeMismatch {
                left: Atom::from(8),
                right: Atom::from("bob")
            }))
        );

        // unbound variable
        let g = guard(
            Term::Variable(variable!(what)),
            Op::LessThan,
            Term::Literal(atom!(bob)),
        );
        expect_that!(
            eval(&g, &bindings),
            eq(Err(GuardError::UnboundVariable(variable!(what))))
        );
    }

    #[test_that::test]
    fn test_guard() {
        let g = guard!(?h < 10);
        expect_that!(
            g,
            eq(Guard {
                left: Term::Variable(variable!(h)),
                op: Op::LessThan,
                right: Term::Literal(atom!(10))
            })
        );

        let g = guard!(alice != ?name);
        expect_that!(
            g,
            eq(Guard {
                left: Term::Literal(atom!(alice)),
                op: Op::NotEqual,
                right: Term::Variable(variable!(name)),
            })
        );
    }
}
