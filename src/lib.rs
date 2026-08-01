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
    pub changes: Vec<Change>,
}

#[derive(Debug)]
pub struct Run {
    pub firings: Vec<Firing>,
    pub status: RunStatus,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum RunStatus {
    /// No changes or activations remain to be processed.
    Quiescence,
    /// Changes or activations remain after the firing budget was consumed.
    FiringLimitReached,
}

#[derive(Error, Debug)]
pub enum EngineError {
    #[error("guard failed in rule {rule}")]
    Guard { rule: String, source: EvalError },
    #[error("action failed in rule {rule}")]
    Action { rule: String, source: EvalError },
}

#[derive(Error, Debug)]
#[error("{source}")]
pub struct RunError {
    #[source]
    pub source: EngineError,
    pub firings: Vec<Firing>,
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

fn guards_match(rule: &Rule, bindings: &Bindings) -> Result<bool, EngineError> {
    for guard in &rule.guards {
        match eval(guard, bindings) {
            Ok(true) => {}
            Ok(false) => return Ok(false),
            Err(source) => {
                return Err(EngineError::Guard {
                    rule: rule.name.clone(),
                    source,
                });
            }
        }
    }

    Ok(true)
}

#[derive(Debug)]
struct Activation {
    rule: usize,
    bindings: Bindings,
}

#[derive(Error, Debug, PartialEq, Eq)]
pub enum AddRuleError {
    #[error("rule {name:?} already exists")]
    DuplicateName { name: String },
}

#[derive(Default)]
pub struct Engine {
    rules: Vec<Rule>,
    wm: WorkingMemory,
    queue: VecDeque<Change>,
    added_rules: VecDeque<usize>,
    agenda: VecDeque<Activation>,
}

impl Engine {
    pub fn add_rule(&mut self, rule: Rule) -> Result<(), AddRuleError> {
        if self.rules.iter().any(|existing| existing.name == rule.name) {
            return Err(AddRuleError::DuplicateName { name: rule.name });
        }

        self.rules.push(rule);
        self.added_rules.push_back(self.rules.len() - 1);
        Ok(())
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

    /// Runs rules in deterministic order until no work remains or the firing limit is reached.
    ///
    /// Changes are considered in FIFO order. Matching then follows rule registration order,
    /// condition declaration order, and working-memory fact order. Actions execute in their
    /// declaration order. When multiple actions write the same fact key, the last write in this
    /// order determines the final value.
    pub fn run(&mut self, max_firings: usize) -> Result<Run, RunError> {
        let mut firings = Vec::new();

        while firings.len() < max_firings {
            if self.agenda.is_empty() {
                let mut scheduled = HashSet::new();
                while let Some(change) = self.queue.pop_front() {
                    let fact = match &change {
                        Change::Added(fact) => fact,
                        Change::Updated { new, .. } => new,
                        Change::Retracted(_) => continue,
                    };

                    let key = (fact.entity.clone(), fact.attribute.clone());
                    if self.wm.memory.get(&key) != Some(fact) {
                        continue;
                    }

                    for (rule_index, rule) in self.rules.iter().enumerate() {
                        for (seat, condition) in rule.conditions.iter().enumerate() {
                            if !condition.then {
                                continue;
                            }

                            let Some(seed) = unify(&condition.pattern, fact, &Bindings::new())
                            else {
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
                                if scheduled.contains(&(rule_index, bindings.clone())) {
                                    continue;
                                }

                                let matches = match guards_match(rule, &bindings) {
                                    Ok(matches) => matches,
                                    Err(source) => return Err(RunError { source, firings }),
                                };
                                if !matches {
                                    continue 'candidates;
                                }

                                scheduled.insert((rule_index, bindings.clone()));
                                self.agenda.push_back(Activation {
                                    rule: rule_index,
                                    bindings,
                                });
                            }
                        }
                    }
                }

                while let Some(rule_index) = self.added_rules.pop_front() {
                    let rule = &self.rules[rule_index];
                    if !rule.conditions.iter().any(|condition| condition.then) {
                        continue;
                    }

                    let patterns: Vec<Pattern> = rule
                        .conditions
                        .iter()
                        .map(|condition| condition.pattern.clone())
                        .collect();

                    'candidates: for bindings in
                        match_rule(&patterns, self.wm.facts(), &Bindings::new())
                    {
                        if scheduled.contains(&(rule_index, bindings.clone())) {
                            continue;
                        }

                        let matches = match guards_match(rule, &bindings) {
                            Ok(matches) => matches,
                            Err(source) => return Err(RunError { source, firings }),
                        };
                        if !matches {
                            continue 'candidates;
                        }

                        scheduled.insert((rule_index, bindings.clone()));
                        self.agenda.push_back(Activation {
                            rule: rule_index,
                            bindings,
                        });
                    }
                }
            }

            let Some(activation) = self.agenda.pop_front() else {
                break;
            };

            let rule = &self.rules[activation.rule];
            let rule_name = rule.name.clone();
            let actions = rule.actions.clone();
            let mut produced = Vec::new();
            for action in &actions {
                match action {
                    Action::Insert(pattern) => {
                        let fact = match instantiate(pattern, &activation.bindings) {
                            Ok(fact) => fact,
                            Err(source) => {
                                return Err(RunError {
                                    source: EngineError::Action {
                                        rule: rule_name.clone(),
                                        source,
                                    },
                                    firings,
                                });
                            }
                        };
                        produced.push(fact);
                    }
                }
            }

            let mut changes = Vec::new();
            for fact in produced {
                match Self::track_insert(&mut self.wm, &mut self.queue, fact.clone()) {
                    InsertResult::Added => changes.push(Change::Added(fact)),
                    InsertResult::Updated(old) => changes.push(Change::Updated { old, new: fact }),
                    InsertResult::Unchanged => {}
                }
            }

            firings.push(Firing {
                rule: rule_name,
                bindings: activation.bindings,
                changes,
            });
        }

        let status =
            if self.queue.is_empty() && self.added_rules.is_empty() && self.agenda.is_empty() {
                RunStatus::Quiescence
            } else {
                RunStatus::FiringLimitReached
            };

        Ok(Run { firings, status })
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
    use std::error::Error;

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
    fn test_engine_run() -> Result<(), Box<dyn Error>> {
        let mut engine = Engine::default();
        engine.insert(fact!(player, health, 3));

        let low_health = Rule::new(
            "low-health",
            vec![pattern!(?e, health, ?h)],
            vec![guard!(?h < 5)],
            vec![Action::Insert(pattern!(?e, status, danger).into())],
        )?;
        let panic_rule = Rule::new(
            "panic",
            vec![pattern!(?e, status, danger)],
            vec![],
            vec![Action::Insert(pattern!(?e, action, flee).into())],
        )?;
        engine.add_rule(low_health)?;
        engine.add_rule(panic_rule)?;

        let run = engine.run(10)?;

        // low-health fires, then its change causes panic to fire (cascade!).
        expect_that!(run.status, eq(RunStatus::Quiescence));
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
        let run = engine.run(10)?;
        expect_that!(run.firings, empty());
        expect_that!(run.status, eq(RunStatus::Quiescence));

        Ok(())
    }

    #[test_that::test]
    fn test_move_player() -> Result<(), Box<dyn Error>> {
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
        )?;
        engine.add_rule(move_player)?;

        let run = engine.run(10)?;

        // Each position update triggers the rule again. Only max_firings stops the loop.
        expect_that!(run.status, eq(RunStatus::FiringLimitReached));
        expect_that!(run.firings.len(), eq(10));
        let facts: Vec<Fact> = engine.facts().cloned().collect();
        expect_that!(facts, contains_exactly!(eq(fact!(player, position, 10))));

        Ok(())
    }

    #[test_that::test]
    fn test_move_player_changes() -> Result<(), Box<dyn Error>> {
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
        )?;

        engine.add_rule(move_player)?;

        engine.insert(fact!(global, dt, 16));
        let run = engine.run(100)?;

        expect_that!(run.status, eq(RunStatus::Quiescence));
        expect_that!(run.firings.len(), eq(1));

        engine.insert(fact!(global, dt, 16));
        let run = engine.run(100)?;
        expect_that!(run.firings, empty());

        engine.insert(fact!(global, dt, 17));
        let run = engine.run(100)?;
        expect_that!(run.firings.len(), eq(1));

        let facts: Vec<Fact> = engine.facts().cloned().collect();
        expect_that!(
            facts,
            contains_exactly!(eq(fact!(global, dt, 17)), eq(fact!(player, position, 33)))
        );

        Ok(())
    }

    #[test_that::test]
    fn run_ignores_changes_superseded_before_firing() -> Result<(), Box<dyn Error>> {
        let mut engine = Engine::default();
        let observe_health = Rule::new(
            "observe-health",
            vec![pattern!(player, health, ?health)],
            vec![],
            vec![Action::Insert(pattern!(observer, health, ?health).into())],
        )?;
        engine.add_rule(observe_health)?;

        engine.insert(fact!(player, health, 10));
        engine.insert(fact!(player, health, 5));

        let run = engine.run(100)?;

        expect_that!(run.firings.len(), eq(1));
        expect_that!(
            run.firings[0].bindings,
            eq(Bindings::from([(variable!(health), Atom::from(5))]))
        );

        Ok(())
    }

    #[test_that::test]
    fn run_does_not_fire_a_fact_retracted_before_firing() -> Result<(), Box<dyn Error>> {
        let mut engine = Engine::default();
        let observe_health = Rule::new(
            "observe-health",
            vec![pattern!(player, health, ?health)],
            vec![],
            vec![Action::Insert(pattern!(observer, health, ?health).into())],
        )?;
        engine.add_rule(observe_health)?;

        engine.insert(fact!(player, health, 10));
        let retracted = engine.retract(atom!(player), atom!(health));

        expect_that!(retracted, some(eq(fact!(player, health, 10))));
        expect_that!(engine.run(100)?.firings, empty());
        expect_that!(engine.facts().count(), eq(0));

        Ok(())
    }

    #[test_that::test]
    fn run_preserves_activations_beyond_the_firing_limit() -> Result<(), Box<dyn Error>> {
        let mut engine = Engine::default();
        engine.add_rule(Rule::new(
            "first-observer",
            vec![pattern!(player, health, ?health)],
            vec![],
            vec![],
        )?)?;
        engine.add_rule(Rule::new(
            "second-observer",
            vec![pattern!(player, health, ?health)],
            vec![],
            vec![],
        )?)?;
        engine.insert(fact!(player, health, 10));

        let first_run = engine.run(1)?;
        expect_that!(first_run.firings.len(), eq(1));
        expect_that!(first_run.firings[0].rule, eq("first-observer".to_string()));
        expect_that!(first_run.status, eq(RunStatus::FiringLimitReached));

        let second_run = engine.run(1)?;
        expect_that!(second_run.firings.len(), eq(1));
        expect_that!(
            second_run.firings[0].rule,
            eq("second-observer".to_string())
        );
        expect_that!(second_run.status, eq(RunStatus::Quiescence));

        Ok(())
    }

    #[test_that::test]
    fn run_schedules_an_activation_once_per_change_batch() -> Result<(), Box<dyn Error>> {
        let mut engine = Engine::default();
        engine.add_rule(Rule::new(
            "observe-living-player",
            vec![
                pattern!(?player, health, ?health),
                pattern!(?player, status, alive),
            ],
            vec![],
            vec![],
        )?)?;

        engine.insert(fact!(alice, health, 10));
        engine.insert(fact!(alice, status, alive));

        let run = engine.run(100)?;

        expect_that!(run.firings.len(), eq(1));
        expect_that!(run.firings[0].rule, eq("observe-living-player".to_string()));

        Ok(())
    }

    #[test_that::test]
    fn run_fires_every_activation_captured_for_a_batch() -> Result<(), Box<dyn Error>> {
        let mut engine = Engine::default();
        engine.add_rule(Rule::new(
            "change-blue-to-green",
            vec![pattern!(player, color, blue)],
            vec![],
            vec![Action::Insert(pattern!(player, color, green).into())],
        )?)?;
        engine.add_rule(Rule::new(
            "observe-blue",
            vec![pattern!(player, color, blue)],
            vec![],
            vec![Action::Insert(pattern!(observer, saw, blue).into())],
        )?)?;
        engine.insert(fact!(player, color, blue));

        let run = engine.run(100)?;

        expect_that!(run.firings.len(), eq(2));
        expect_that!(run.firings[0].rule, eq("change-blue-to-green".to_string()));
        expect_that!(run.firings[1].rule, eq("observe-blue".to_string()));
        expect_that!(
            engine.facts().cloned().collect::<Vec<_>>(),
            contains_exactly!(
                eq(fact!(player, color, green)),
                eq(fact!(observer, saw, blue)),
            )
        );

        Ok(())
    }

    #[test_that::test]
    fn engine_rejects_duplicate_rule_names() -> Result<(), Box<dyn Error>> {
        let mut engine = Engine::default();
        let first = Rule::new(
            "observe-health",
            vec![pattern!(alice, health, ?health)],
            vec![],
            vec![],
        )?;
        let duplicate = Rule::new(
            "observe-health",
            vec![pattern!(bob, health, ?health)],
            vec![],
            vec![],
        )?;

        engine.add_rule(first)?;
        expect_that!(
            engine.add_rule(duplicate),
            eq(Err(AddRuleError::DuplicateName {
                name: "observe-health".to_string(),
            }))
        );

        engine.insert(fact!(alice, health, 10));
        engine.insert(fact!(bob, health, 10));
        expect_that!(engine.run(100)?.firings.len(), eq(1));

        Ok(())
    }

    #[test_that::test]
    fn run_uses_rule_registration_and_fact_order() -> Result<(), Box<dyn Error>> {
        let mut engine = Engine::default();
        let conditions = || {
            vec![
                Condition::from(pattern!(global, dt, ?dt)),
                Condition::support(pattern!(?player, position, ?position)),
            ]
        };
        engine.add_rule(Rule::new("first-rule", conditions(), vec![], vec![])?)?;
        engine.add_rule(Rule::new("second-rule", conditions(), vec![], vec![])?)?;

        // Facts are deliberately inserted in reverse entity order.
        engine.insert(fact!(bob, position, 0));
        engine.insert(fact!(alice, position, 0));
        engine.insert(fact!(global, dt, 16));

        let run = engine.run(100)?;
        let player = variable!(player);

        expect_that!(run.firings.len(), eq(4));
        expect_that!(run.firings[0].rule, eq("first-rule".to_string()));
        expect_that!(
            run.firings[0].bindings.get(&player),
            some(eq(&atom!(alice)))
        );
        expect_that!(run.firings[1].rule, eq("first-rule".to_string()));
        expect_that!(run.firings[1].bindings.get(&player), some(eq(&atom!(bob))));
        expect_that!(run.firings[2].rule, eq("second-rule".to_string()));
        expect_that!(
            run.firings[2].bindings.get(&player),
            some(eq(&atom!(alice)))
        );
        expect_that!(run.firings[3].rule, eq("second-rule".to_string()));
        expect_that!(run.firings[3].bindings.get(&player), some(eq(&atom!(bob))));

        Ok(())
    }

    #[test_that::test]
    fn firing_does_not_apply_actions_when_evaluation_fails() -> Result<(), Box<dyn Error>> {
        let mut engine = Engine::default();
        engine.add_rule(Rule::new(
            "invalid-second-action",
            vec![pattern!(player, status, ready)],
            vec![],
            vec![
                Action::Insert(pattern!(observer, status, started).into()),
                Action::Insert(ActionPattern {
                    entity: Term::Literal(atom!(observer)),
                    attribute: Term::Literal(atom!(total)),
                    value: Expr::Add(Term::Literal(atom!(invalid)), Term::Literal(atom!(1))),
                }),
            ],
        )?)?;
        engine.insert(fact!(player, status, ready));

        expect_that!(engine.run(100), err(anything()));
        expect_that!(
            engine.facts().cloned().collect::<Vec<_>>(),
            contains_exactly!(eq(fact!(player, status, ready)))
        );

        Ok(())
    }

    #[test_that::test]
    fn firing_reports_only_facts_that_changed() -> Result<(), Box<dyn Error>> {
        let mut engine = Engine::default();
        engine.add_rule(Rule::new(
            "observe-tick",
            vec![pattern!(global, tick, ?tick)],
            vec![],
            vec![Action::Insert(pattern!(observer, status, ready).into())],
        )?)?;
        engine.insert(fact!(global, tick, 1));

        let first_run = engine.run(100)?;

        expect_that!(first_run.firings.len(), eq(1));
        expect_that!(
            first_run.firings[0].changes,
            contains_exactly!(eq(Change::Added(fact!(observer, status, ready))))
        );

        engine.insert(fact!(global, tick, 2));
        let second_run = engine.run(100)?;

        expect_that!(second_run.firings.len(), eq(1));
        expect_that!(second_run.firings[0].changes, empty());

        Ok(())
    }

    #[test_that::test]
    fn adding_a_rule_evaluates_existing_facts_once() -> Result<(), Box<dyn Error>> {
        let observe_health = || {
            Rule::new(
                "observe-health",
                vec![pattern!(?player, health, ?health)],
                vec![],
                vec![],
            )
        };

        let mut settled_engine = Engine::default();
        settled_engine.insert(fact!(alice, health, 10));
        settled_engine.run(100)?;
        settled_engine.add_rule(observe_health()?)?;
        expect_that!(settled_engine.run(100)?.firings.len(), eq(1));

        settled_engine.add_rule(Rule::new(
            "support-only",
            vec![Condition::support(pattern!(?player, health, ?health))],
            vec![],
            vec![],
        )?)?;
        expect_that!(settled_engine.run(100)?.firings, empty());

        let mut pending_engine = Engine::default();
        pending_engine.insert(fact!(alice, health, 10));
        pending_engine.add_rule(observe_health()?)?;
        expect_that!(pending_engine.run(100)?.firings.len(), eq(1));

        Ok(())
    }

    #[test_that::test]
    fn run_error_reports_completed_firings_and_preserves_later_activations(
    ) -> Result<(), Box<dyn Error>> {
        let mut engine = Engine::default();
        engine.add_rule(Rule::new(
            "first-rule",
            vec![pattern!(player, status, ready)],
            vec![],
            vec![Action::Insert(pattern!(observer, first, complete).into())],
        )?)?;
        engine.add_rule(Rule::new(
            "failing-rule",
            vec![pattern!(player, status, ready)],
            vec![],
            vec![Action::Insert(ActionPattern {
                entity: Term::Literal(atom!(observer)),
                attribute: Term::Literal(atom!(invalid)),
                value: Expr::Add(Term::Literal(atom!(invalid)), Term::Literal(atom!(1))),
            })],
        )?)?;
        engine.add_rule(Rule::new(
            "last-rule",
            vec![pattern!(player, status, ready)],
            vec![],
            vec![Action::Insert(pattern!(observer, last, complete).into())],
        )?)?;
        engine.insert(fact!(player, status, ready));

        let failure = engine.run(100).err().ok_or("expected the run to fail")?;

        expect_that!(failure.firings.len(), eq(1));
        expect_that!(failure.firings[0].rule, eq("first-rule".to_string()));
        expect_that!(
            engine.facts().cloned().collect::<Vec<_>>(),
            contains_exactly!(
                eq(fact!(player, status, ready)),
                eq(fact!(observer, first, complete)),
            )
        );

        let resumed = engine.run(100)?;
        expect_that!(resumed.firings.len(), eq(1));
        expect_that!(resumed.firings[0].rule, eq("last-rule".to_string()));

        Ok(())
    }

    #[test_that::test]
    fn later_firings_win_when_writing_the_same_fact() -> Result<(), Box<dyn Error>> {
        let mut engine = Engine::default();
        engine.add_rule(Rule::new(
            "set-happy",
            vec![pattern!(global, tick, 1)],
            vec![],
            vec![Action::Insert(pattern!(player, mood, happy).into())],
        )?)?;
        engine.add_rule(Rule::new(
            "set-sad",
            vec![pattern!(global, tick, 1)],
            vec![],
            vec![Action::Insert(pattern!(player, mood, sad).into())],
        )?)?;
        engine.insert(fact!(global, tick, 1));

        let run = engine.run(100)?;

        expect_that!(run.firings.len(), eq(2));
        expect_that!(
            run.firings[0].changes,
            contains_exactly!(eq(Change::Added(fact!(player, mood, happy))))
        );
        expect_that!(
            run.firings[1].changes,
            contains_exactly!(eq(Change::Updated {
                old: fact!(player, mood, happy),
                new: fact!(player, mood, sad),
            }))
        );
        expect_that!(
            engine.facts().cloned().collect::<Vec<_>>(),
            contains_exactly!(eq(fact!(global, tick, 1)), eq(fact!(player, mood, sad)),)
        );

        Ok(())
    }
}
