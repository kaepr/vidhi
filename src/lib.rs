use std::collections::{BTreeMap, HashSet, VecDeque};
use std::iter::{self, IntoIterator, Iterator};
use std::mem;

use thiserror::Error;

/// Represents a concrete value.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
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
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
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

#[derive(Debug, Clone, PartialEq)]
pub struct Condition {
    pub pattern: Pattern,
    /// Triggers the rule for matching changes iff true.
    pub then: bool,
}

impl Condition {
    pub fn support(pattern: Pattern) -> Condition {
        Condition {
            pattern,
            then: false,
        }
    }
}

impl From<Pattern> for Condition {
    fn from(pattern: Pattern) -> Self {
        Condition {
            pattern,
            then: true,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Term(Term),
    Add(Term, Term),
}

impl Expr {
    fn variables(&self) -> impl Iterator<Item = &Variable> + '_ {
        let (x, xs) = match self {
            Expr::Term(t) => (t, None),
            Expr::Add(l, r) => (l, Some(r)),
        };

        iter::once(x).chain(xs).filter_map(Term::as_variable)
    }
}

/// Allows computation for the [Pattern::value] slot.
#[derive(Debug, Clone, PartialEq)]
pub struct ActionPattern {
    pub entity: Term,
    pub attribute: Term,
    pub value: Expr,
}

impl ActionPattern {
    fn variables(&self) -> impl Iterator<Item = &Variable> + '_ {
        [&self.entity, &self.attribute]
            .into_iter()
            .filter_map(Term::as_variable)
            .chain(self.value.variables())
    }
}

impl From<Pattern> for ActionPattern {
    fn from(p: Pattern) -> Self {
        ActionPattern {
            entity: p.entity,
            attribute: p.attribute,
            value: Expr::Term(p.value),
        }
    }
}

/// Binds a variable to a concrete value.
pub type Bindings = BTreeMap<Variable, Atom>;

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

#[derive(Debug, Clone, PartialEq)]
pub enum Change {
    Added(Fact),
    Updated { old: Fact, new: Fact },
    Retracted(Fact),
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
    Insert(ActionPattern),
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
    pub conditions: Vec<Condition>,
    pub guards: Vec<Guard>,
    pub actions: Vec<Action>,
}

impl Rule {
    pub fn new<C>(
        name: impl AsRef<str>,
        conditions: Vec<C>,
        guards: Vec<Guard>,
        actions: Vec<Action>,
    ) -> Result<Rule, RuleError>
    where
        C: Into<Condition>,
    {
        let conditions: Vec<Condition> = conditions.into_iter().map(Into::into).collect();
        let bounded: HashSet<&Variable> = conditions
            .iter()
            .flat_map(|c| c.pattern.variables())
            .collect();

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
pub enum EvalError {
    #[error("unbound variable {}", .0.name)]
    UnboundVariable(Variable),
    #[error("type mismatch: cannot compare {left:?} with {right:?}")]
    TypeMismatch { left: Atom, right: Atom },
    #[error("cannot add {left:?} and {right:?}")]
    Arithmetic { left: Atom, right: Atom },
}

fn eval_expr(expr: &Expr, bindings: &Bindings) -> Result<Atom, EvalError> {
    match expr {
        Expr::Term(term) => resolve_or_err(term, bindings),
        Expr::Add(l, r) => {
            let left = resolve_or_err(l, bindings)?;
            let right = resolve_or_err(r, bindings)?;
            match (left, right) {
                (Atom::Number(a), Atom::Number(b)) => Ok(Atom::Number(a + b)),
                (left, right) => Err(EvalError::Arithmetic { left, right }),
            }
        }
    }
}

#[derive(Error, Debug)]
pub enum RuleError {
    #[error("unbound variable {0:?}")]
    UnboundVariable(Variable),
}

/// Resolves to an atom, or returns an error with the unbound variable.
fn resolve_or_err(term: &Term, bindings: &Bindings) -> Result<Atom, EvalError> {
    match term {
        Term::Literal(atom) => Ok(atom.clone()),
        Term::Variable(var) => bindings
            .get(var)
            .cloned()
            .ok_or_else(|| EvalError::UnboundVariable(var.clone())),
    }
}

/// Evaluates a guard given bindings.
///
/// # Errors
///
/// - Returns [GuardError::TypeMismatch] when incompatible types are compared.
/// - Returns [GuardError::UnboundVariable] when guard contains an unbound variable.
pub fn eval(guard: &Guard, bindings: &Bindings) -> Result<bool, EvalError> {
    let left = resolve_or_err(&guard.left, bindings)?;
    let right = resolve_or_err(&guard.right, bindings)?;

    if mem::discriminant(&left) != mem::discriminant(&right) {
        return Err(EvalError::TypeMismatch { left, right });
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

#[derive(Debug, Clone, PartialEq)]
pub struct Firing {
    pub rule: String,
    pub bindings: Bindings,
    pub inserted: Vec<Fact>,
}

#[derive(Debug)]
pub struct Run {
    pub firings: Vec<Firing>,
    /// No change in facts.
    pub is_stable: bool,
}

#[derive(Error, Debug)]
pub enum EngineError {
    #[error("guard failed in rule {rule}")]
    Guard { rule: String, source: EvalError },
    #[error("action failed in rule {rule}")]
    Action { rule: String, source: EvalError },
}

/// Instantiates the pattern to a concrete fact.
///
/// Resolves each term to it's value.
fn instantiate(pattern: &ActionPattern, bindings: &Bindings) -> Result<Fact, EvalError> {
    Ok(Fact {
        entity: resolve_or_err(&pattern.entity, bindings)?,
        attribute: resolve_or_err(&pattern.attribute, bindings)?,
        value: eval_expr(&pattern.value, bindings)?,
    })
}

#[derive(Default)]
pub struct Engine {
    rules: Vec<Rule>,
    wm: WorkingMemory,
    queue: VecDeque<Change>,
}

impl Engine {
    pub fn add_rule(&mut self, rule: Rule) {
        self.rules.push(rule);
    }

    pub fn insert(&mut self, fact: Fact) -> InsertResult {
        Self::track_insert(&mut self.wm, &mut self.queue, fact)
    }

    pub fn retract(&mut self, entity: Atom, attribute: Atom) -> Option<Fact> {
        let fact = self.wm.retract(entity, attribute)?;
        self.queue.push_back(Change::Retracted(fact.clone()));
        Some(fact)
    }

    fn track_insert(
        wm: &mut WorkingMemory,
        queue: &mut VecDeque<Change>,
        fact: Fact,
    ) -> InsertResult {
        match wm.insert(fact.clone()) {
            InsertResult::Added => {
                queue.push_back(Change::Added(fact));
                InsertResult::Added
            }
            InsertResult::Updated(old) => {
                queue.push_back(Change::Updated {
                    old: old.clone(),
                    new: fact,
                });
                InsertResult::Updated(old)
            }
            InsertResult::Unchanged => InsertResult::Unchanged,
        }
    }

    pub fn facts(&self) -> impl Iterator<Item = &Fact> + Clone {
        self.wm.facts()
    }

    pub fn run(&mut self, max_firings: usize) -> Result<Run, EngineError> {
        let mut firings = Vec::new();

        while let Some(change) = self.queue.pop_front() {
            if firings.len() >= max_firings {
                self.queue.push_front(change);
                return Ok(Run {
                    firings,
                    is_stable: false,
                });
            }

            let fact = match &change {
                Change::Added(fact) => fact,
                Change::Updated { new, .. } => new,
                Change::Retracted(_) => continue,
            };

            let key = (fact.entity.clone(), fact.attribute.clone());
            if self.wm.memory.get(&key) != Some(fact) {
                continue;
            }

            let mut agenda: Vec<(&Rule, Bindings)> = Vec::new();
            for rule in &self.rules {
                let mut seen: Vec<Bindings> = Vec::new();
                for (seat, condition) in rule.conditions.iter().enumerate() {
                    if !condition.then {
                        continue;
                    }

                    let Some(seed) = unify(&condition.pattern, fact, &Bindings::new()) else {
                        continue;
                    };

                    let rest: Vec<Pattern> = rule
                        .conditions
                        .iter()
                        .enumerate()
                        .filter(|(i, _)| *i != seat)
                        .map(|(_, c)| c.pattern.clone())
                        .collect();

                    'candidates: for bindings in match_rule(&rest, self.wm.facts(), &seed) {
                        if seen.contains(&bindings) {
                            continue;
                        }

                        for g in &rule.guards {
                            match eval(g, &bindings) {
                                Ok(true) => {}
                                Ok(false) => continue 'candidates,
                                Err(source) => {
                                    return Err(EngineError::Guard {
                                        rule: rule.name.clone(),
                                        source,
                                    });
                                }
                            }
                        }
                        seen.push(bindings.clone());
                        agenda.push((rule, bindings));
                    }
                }
            }

            for (rule, bindings) in agenda {
                let mut inserted = Vec::new();
                for action in &rule.actions {
                    match action {
                        Action::Insert(pattern) => {
                            let fact = instantiate(pattern, &bindings).map_err(|source| {
                                EngineError::Action {
                                    rule: rule.name.clone(),
                                    source,
                                }
                            })?;

                            Self::track_insert(&mut self.wm, &mut self.queue, fact.clone());
                            inserted.push(fact);
                        }
                    }
                }

                firings.push(Firing {
                    rule: rule.name.clone(),
                    bindings,
                    inserted,
                });
            }
        }

        Ok(Run {
            firings,
            is_stable: true,
        })
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
            eq(Err(EvalError::TypeMismatch {
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
            eq(Err(EvalError::UnboundVariable(variable!(what))))
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

    #[test_that::test]
    fn test_engine_run() {
        let mut engine = Engine::default();
        engine.insert(fact!(player, health, 3));

        let low_health = Rule::new(
            "low-health",
            vec![pattern!(?e, health, ?h)],
            vec![guard!(?h < 5)],
            vec![Action::Insert(pattern!(?e, status, danger).into())],
        )
        .unwrap();
        let panic_rule = Rule::new(
            "panic",
            vec![pattern!(?e, status, danger)],
            vec![],
            vec![Action::Insert(pattern!(?e, action, flee).into())],
        )
        .unwrap();
        engine.add_rule(low_health);
        engine.add_rule(panic_rule);

        let run = engine.run(10).unwrap();

        // low-health fires, then its change causes panic to fire (cascade!).
        expect_that!(run.is_stable, eq(true));
        expect_that!(run.firings.len(), eq(2));
        expect_that!(run.firings[0].rule, eq("low-health".to_string()));
        expect_that!(run.firings[1].rule, eq("panic".to_string()));

        let facts: Vec<Fact> = engine.facts().cloned().collect();
        expect_that!(
            facts,
            contains_exactly!(
                eq(fact!(player, health, 3)),
                eq(fact!(player, status, danger)),
                eq(fact!(player, action, flee)),
            )
        );

        // No new changes means there is nothing to trigger the rules again.
        let run = engine.run(10).unwrap();
        expect_that!(run.firings, empty());
        expect_that!(run.is_stable, eq(true));
    }

    #[test_that::test]
    fn test_move_player() {
        let mut engine = Engine::default();
        engine.insert(fact!(player, position, 0));

        let move_player = Rule::new(
            "move-player",
            vec![pattern!(?p, position, ?pos)],
            vec![],
            vec![Action::Insert(ActionPattern {
                entity: Term::Variable(variable!(p)),
                attribute: Term::Literal(atom!(position)),
                value: Expr::Add(Term::Variable(variable!(pos)), Term::Literal(atom!(1))),
            })],
        )
        .unwrap();
        engine.add_rule(move_player);

        let run = engine.run(10).unwrap();

        // Each position update triggers the rule again. Only max_firings stops the loop.
        expect_that!(run.is_stable, eq(false));
        expect_that!(run.firings.len(), eq(10));
        let facts: Vec<Fact> = engine.facts().cloned().collect();
        expect_that!(facts, contains_exactly!(eq(fact!(player, position, 10))));
    }

    #[test_that::test]
    fn test_move_player_changes() {
        let mut engine = Engine::default();
        engine.insert(fact!(player, position, 0));

        let move_player = Rule::new(
            "move-player",
            vec![
                Condition::from(pattern!(global, dt, ?dt)),
                Condition::support(pattern!(?p, position, ?pos)),
            ],
            vec![],
            vec![Action::Insert(ActionPattern {
                entity: Term::Variable(variable!(p)),
                attribute: Term::Literal(atom!(position)),
                value: Expr::Add(
                    Term::Variable(variable!(pos)),
                    Term::Variable(variable!(dt)),
                ),
            })],
        )
        .unwrap();

        engine.add_rule(move_player);

        engine.insert(fact!(global, dt, 16));
        let run = engine.run(100).unwrap();

        expect_that!(run.is_stable, eq(true));
        expect_that!(run.firings.len(), eq(1));

        engine.insert(fact!(global, dt, 16));
        let run = engine.run(100).unwrap();
        expect_that!(run.firings, empty());

        engine.insert(fact!(global, dt, 17));
        let run = engine.run(100).unwrap();
        expect_that!(run.firings.len(), eq(1));

        let facts: Vec<Fact> = engine.facts().cloned().collect();
        expect_that!(
            facts,
            contains_exactly!(eq(fact!(global, dt, 17)), eq(fact!(player, position, 33)))
        );
    }

    #[test_that::test]
    fn run_ignores_changes_superseded_before_firing() {
        let mut engine = Engine::default();
        let observe_health = Rule::new(
            "observe-health",
            vec![pattern!(player, health, ?health)],
            vec![],
            vec![Action::Insert(pattern!(observer, health, ?health).into())],
        )
        .unwrap();
        engine.add_rule(observe_health);

        engine.insert(fact!(player, health, 10));
        engine.insert(fact!(player, health, 5));

        let run = engine.run(100).unwrap();

        expect_that!(run.firings.len(), eq(1));
        expect_that!(
            run.firings[0].bindings,
            eq(Bindings::from([(variable!(health), Atom::from(5))]))
        );
    }

    #[test_that::test]
    fn run_does_not_fire_a_fact_retracted_before_firing() {
        let mut engine = Engine::default();
        let observe_health = Rule::new(
            "observe-health",
            vec![pattern!(player, health, ?health)],
            vec![],
            vec![Action::Insert(pattern!(observer, health, ?health).into())],
        )
        .unwrap();
        engine.add_rule(observe_health);

        engine.insert(fact!(player, health, 10));
        let retracted = engine.retract(atom!(player), atom!(health));

        expect_that!(retracted, some(eq(fact!(player, health, 10))));
        expect_that!(engine.run(100).unwrap().firings, empty());
        expect_that!(engine.facts().count(), eq(0));
    }
}
