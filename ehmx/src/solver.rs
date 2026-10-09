//! A concrete solver for the REPL's built-in Eq and Show predicates.
//! Existential witnesses are eliminated only within their own scope.
//! Other quantified handler constraints remain symbolic.

use crate::core::{BaseTy, ClassPred, Constraint, Effect, Id, Ty};
use crate::infer::Output;
use std::collections::{BTreeMap, BTreeSet};

type C = Constraint<ClassPred>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SolveError {
    TypeMismatch,
    OccursCheck,
    EffectMismatch,
    LacksViolation,
    NoInstance(ClassPred),
}

#[derive(Default)]
struct Solver {
    types: BTreeMap<Id, Ty>,
    effects: BTreeMap<Id, Effect>,
    fixed_types: BTreeSet<Id>,
    fixed_effects: BTreeSet<Id>,
}

impl Solver {
    fn ty(&self, ty: &Ty) -> Ty {
        match ty {
            Ty::Var(i) => self.types.get(i).map_or_else(|| ty.clone(), |t| self.ty(t)),
            Ty::Base(_) => ty.clone(),
            Ty::Arr(a, e, b) => Ty::Arr(Box::new(self.ty(a)), self.effect(e), Box::new(self.ty(b))),
        }
    }

    fn effect(&self, effect: &Effect) -> Effect {
        effect.vars.iter().fold(
            Effect {
                labels: effect.labels.clone(),
                vars: Default::default(),
            },
            |acc, i| match self.effects.get(i) {
                Some(bound) => acc.union(&self.effect(bound)),
                None => acc.union(&Effect::var(*i)),
            },
        )
    }

    fn pred(&self, pred: &ClassPred) -> ClassPred {
        match pred {
            ClassPred::Eq(t) => ClassPred::Eq(self.ty(t)),
            ClassPred::Show(t) => ClassPred::Show(self.ty(t)),
        }
    }

    fn unify(
        &mut self,
        equations: &mut Vec<(Ty, Ty)>,
        effects: &mut Vec<C>,
    ) -> Result<(), SolveError> {
        while let Some((left, right)) = equations.pop() {
            let left = self.ty(&left);
            let right = self.ty(&right);
            if left == right {
                continue;
            }
            match (left, right) {
                (Ty::Var(i), t) if !self.fixed_types.contains(&i) => {
                    if t.fv_types().contains(&i) {
                        return Err(SolveError::OccursCheck);
                    }
                    self.types.insert(i, t);
                }
                (t, Ty::Var(i)) if !self.fixed_types.contains(&i) => {
                    if t.fv_types().contains(&i) {
                        return Err(SolveError::OccursCheck);
                    }
                    self.types.insert(i, t);
                }
                (Ty::Base(_), Ty::Base(_))
                | (Ty::Base(_), Ty::Arr(_, _, _))
                | (Ty::Arr(_, _, _), Ty::Base(_)) => {
                    return Err(SolveError::TypeMismatch);
                }
                (Ty::Arr(a, e, b), Ty::Arr(a2, e2, b2)) => {
                    equations.push((*a, *a2));
                    equations.push((*b, *b2));
                    effects.push(C::EffectLe(e.clone(), e2.clone()));
                    effects.push(C::EffectLe(e2, e));
                }
                (a, b) => effects.push(C::TypeEq(a, b)),
            }
        }
        Ok(())
    }

    fn bind_empty_effects(&mut self, atoms: &[C]) -> Result<bool, SolveError> {
        let mut changed = false;
        for atom in atoms {
            if let C::EffectLe(left, right) = atom {
                let left = self.effect(left);
                let right = self.effect(right);
                if right.vars.is_empty() {
                    if !left.labels.is_subset(&right.labels) {
                        return Err(SolveError::EffectMismatch);
                    }
                    for i in left.vars {
                        let excluded: std::collections::BTreeSet<_> = atoms
                            .iter()
                            .filter_map(|atom| match atom {
                                C::Lacks(op, effect) => {
                                    let effect = self.effect(effect);
                                    (!effect.labels.contains(op) && effect.vars.contains(&i))
                                        .then_some(*op)
                                }
                                _ => None,
                            })
                            .collect();
                        if !self.fixed_effects.contains(&i)
                            && right.labels.is_subset(&excluded)
                            && self.effects.insert(i, Effect::default()).is_none()
                        {
                            changed = true;
                        }
                    }
                }
            }
        }
        Ok(changed)
    }

    fn bind_equal_effects(&mut self, atoms: &[C]) -> bool {
        let pairs: Vec<_> = atoms
            .iter()
            .filter_map(|atom| match atom {
                C::EffectLe(left, right) => Some((self.effect(left), self.effect(right))),
                _ => None,
            })
            .collect();
        for (left, right) in &pairs {
            let (Some(&a), Some(&b)) = (left.vars.iter().next(), right.vars.iter().next()) else {
                continue;
            };
            if a == b
                || left.vars.len() != 1
                || right.vars.len() != 1
                || !left.labels.is_empty()
                || !right.labels.is_empty()
                || !pairs.iter().any(|(x, y)| x == right && y == left)
                || (self.fixed_effects.contains(&a) && self.fixed_effects.contains(&b))
            {
                continue;
            }
            let (from, to) = if self.fixed_effects.contains(&a) {
                (b, a)
            } else if self.fixed_effects.contains(&b) || a > b {
                (a, b)
            } else {
                (b, a)
            };
            self.effects.insert(from, Effect::var(to));
            return true;
        }
        false
    }

    fn atom(&self, atom: C, assumptions: &[ClassPred]) -> Result<C, SolveError> {
        Ok(match atom {
            C::Top => C::Top,
            C::TypeEq(a, b) => {
                let a = self.ty(&a);
                let b = self.ty(&b);
                if a == b {
                    C::Top
                } else if matches!((&a, &b), (Ty::Base(_), Ty::Base(_))) {
                    return Err(SolveError::TypeMismatch);
                } else {
                    C::TypeEq(a, b)
                }
            }
            C::EffectLe(a, b) => {
                let a = self.effect(&a);
                let b = self.effect(&b);
                if a.labels.is_subset(&b.labels) && a.vars.is_subset(&b.vars) {
                    C::Top
                } else if b.vars.is_empty() && a.vars.is_empty() {
                    return Err(SolveError::EffectMismatch);
                } else {
                    C::EffectLe(a, b)
                }
            }
            C::Lacks(op, e) => {
                let e = self.effect(&e);
                if e.labels.contains(&op) {
                    return Err(SolveError::LacksViolation);
                }
                if e.vars.is_empty() {
                    C::Top
                } else {
                    C::Lacks(op, e)
                }
            }
            C::Pred(p) => {
                let p = self.pred(&p);
                if assumptions.iter().any(|a| self.pred(a) == p) {
                    C::Top
                } else {
                    let t = match &p {
                        ClassPred::Eq(t) | ClassPred::Show(t) => t,
                    };
                    match t {
                        Ty::Base(BaseTy::Int | BaseTy::Bool) => C::Top,
                        _ if t.fv_types().is_empty() && t.fv_effects().is_empty() => {
                            return Err(SolveError::NoInstance(p));
                        }
                        _ => C::Pred(p),
                    }
                }
            }
            C::And(a, b) => C::and(self.atom(*a, assumptions)?, self.atom(*b, assumptions)?),
            C::AllTy(i, c) => C::AllTy(i, Box::new(self.atom(*c, assumptions)?)),
            C::AllEff(i, c) => C::AllEff(i, Box::new(self.atom(*c, assumptions)?)),
            C::ExTy(i, c) => C::ExTy(i, Box::new(self.atom(*c, assumptions)?)),
            C::ExEff(i, c) => C::ExEff(i, Box::new(self.atom(*c, assumptions)?)),
        })
    }
}

fn collect_top(c: C, equations: &mut Vec<(Ty, Ty)>, atoms: &mut Vec<C>) {
    match c {
        C::And(a, b) => {
            collect_top(*a, equations, atoms);
            collect_top(*b, equations, atoms);
        }
        C::TypeEq(a, b) => equations.push((a, b)),
        C::Top => {}
        other => atoms.push(other),
    }
}

fn conjunction(atoms: impl IntoIterator<Item = C>) -> C {
    atoms
        .into_iter()
        .fold(C::Top, |acc, atom| match (acc, atom) {
            (C::Top, other) | (other, C::Top) => other,
            (a, b) => C::and(a, b),
        })
}

fn flatten_and(c: C, atoms: &mut Vec<C>) {
    match c {
        C::And(a, b) => {
            flatten_and(*a, atoms);
            flatten_and(*b, atoms);
        }
        C::Top => {}
        other => atoms.push(other),
    }
}

fn type_witness(i: Id, body: &C, atoms: &[C]) -> Option<(usize, Ty)> {
    atoms.iter().enumerate().find_map(|(index, atom)| {
        let term = match atom {
            C::TypeEq(Ty::Var(j), t) | C::TypeEq(t, Ty::Var(j)) if *j == i => t,
            _ => return None,
        };
        (term.fv_types().is_disjoint(&body.bound_types())
            && term.fv_effects().is_disjoint(&body.bound_effects())
            && !term.fv_types().contains(&i))
        .then(|| (index, term.clone()))
    })
}

fn effect_witness(i: Id, body: &C, atoms: &[C]) -> Option<(usize, usize, Effect)> {
    let variable = Effect::var(i);
    atoms.iter().enumerate().find_map(|(left_index, atom)| {
        let C::EffectLe(left, term) = atom else {
            return None;
        };
        if *left != variable
            || term.vars.contains(&i)
            || !term.vars.is_disjoint(&body.bound_effects())
        {
            return None;
        }
        atoms.iter().enumerate().find_map(|(right_index, other)| {
            (left_index != right_index
                && matches!(other, C::EffectLe(a, b) if a == term && *b == variable))
            .then(|| (left_index, right_index, term.clone()))
        })
    })
}

fn forced_empty_effect(i: Id, atoms: &[C]) -> bool {
    atoms.iter().any(|atom| {
        let C::EffectLe(left, right) = atom else {
            return false;
        };
        if !left.vars.contains(&i) || !right.vars.is_empty() {
            return false;
        }
        right.labels.iter().all(|op| {
            atoms.iter().any(|atom| {
                matches!(atom, C::Lacks(lacked, effect)
                    if lacked == op && effect.vars.contains(&i) && !effect.labels.contains(op))
            })
        })
    })
}

fn sole_effect_bound(i: Id, atoms: &[C]) -> Option<usize> {
    atoms.iter().enumerate().find_map(|(index, atom)| {
        let can_choose = match atom {
            C::EffectLe(left, right) if *right == Effect::var(i) => !left.vars.contains(&i),
            C::EffectLe(left, _) if *left == Effect::var(i) => true,
            _ => false,
        };
        (can_choose
            && atoms
                .iter()
                .enumerate()
                .all(|(other, atom)| other == index || !atom.fv_effects().contains(&i)))
        .then_some(index)
    })
}

fn replace_type_in_ty(ty: Ty, i: Id, witness: &Ty) -> Ty {
    match ty {
        Ty::Var(j) if i == j => witness.clone(),
        Ty::Arr(a, effect, b) => Ty::Arr(
            Box::new(replace_type_in_ty(*a, i, witness)),
            effect,
            Box::new(replace_type_in_ty(*b, i, witness)),
        ),
        other => other,
    }
}

fn replace_effect_in_effect(mut effect: Effect, i: Id, witness: &Effect) -> Effect {
    if effect.vars.remove(&i) {
        effect.union(witness)
    } else {
        effect
    }
}

fn replace_effect_in_ty(ty: Ty, i: Id, witness: &Effect) -> Ty {
    match ty {
        Ty::Arr(a, effect, b) => Ty::Arr(
            Box::new(replace_effect_in_ty(*a, i, witness)),
            replace_effect_in_effect(effect, i, witness),
            Box::new(replace_effect_in_ty(*b, i, witness)),
        ),
        other => other,
    }
}

fn map_pred_ty(pred: ClassPred, f: impl FnOnce(Ty) -> Ty) -> ClassPred {
    match pred {
        ClassPred::Eq(ty) => ClassPred::Eq(f(ty)),
        ClassPred::Show(ty) => ClassPred::Show(f(ty)),
    }
}

fn replace_type(c: C, i: Id, witness: &Ty) -> C {
    match c {
        C::And(a, b) => C::and(replace_type(*a, i, witness), replace_type(*b, i, witness)),
        C::TypeEq(a, b) => C::TypeEq(
            replace_type_in_ty(a, i, witness),
            replace_type_in_ty(b, i, witness),
        ),
        C::Pred(p) => C::Pred(map_pred_ty(p, |t| replace_type_in_ty(t, i, witness))),
        C::AllTy(j, body) if j == i => C::AllTy(j, body),
        C::ExTy(j, body) if j == i => C::ExTy(j, body),
        C::AllTy(j, body) => C::AllTy(j, Box::new(replace_type(*body, i, witness))),
        C::ExTy(j, body) => C::ExTy(j, Box::new(replace_type(*body, i, witness))),
        C::AllEff(j, body) => C::AllEff(j, Box::new(replace_type(*body, i, witness))),
        C::ExEff(j, body) => C::ExEff(j, Box::new(replace_type(*body, i, witness))),
        other => other,
    }
}

fn replace_effect(c: C, i: Id, witness: &Effect) -> C {
    match c {
        C::And(a, b) => C::and(
            replace_effect(*a, i, witness),
            replace_effect(*b, i, witness),
        ),
        C::TypeEq(a, b) => C::TypeEq(
            replace_effect_in_ty(a, i, witness),
            replace_effect_in_ty(b, i, witness),
        ),
        C::EffectLe(a, b) => C::EffectLe(
            replace_effect_in_effect(a, i, witness),
            replace_effect_in_effect(b, i, witness),
        ),
        C::Lacks(op, effect) => C::Lacks(op, replace_effect_in_effect(effect, i, witness)),
        C::Pred(p) => C::Pred(map_pred_ty(p, |t| replace_effect_in_ty(t, i, witness))),
        C::AllEff(j, body) if j == i => C::AllEff(j, body),
        C::ExEff(j, body) if j == i => C::ExEff(j, body),
        C::AllTy(j, body) => C::AllTy(j, Box::new(replace_effect(*body, i, witness))),
        C::ExTy(j, body) => C::ExTy(j, Box::new(replace_effect(*body, i, witness))),
        C::AllEff(j, body) => C::AllEff(j, Box::new(replace_effect(*body, i, witness))),
        C::ExEff(j, body) => C::ExEff(j, Box::new(replace_effect(*body, i, witness))),
        other => other,
    }
}

fn reduce_quantified(c: C, assumptions: &[ClassPred]) -> Result<C, SolveError> {
    Ok(match c {
        C::And(a, b) => conjunction([
            reduce_quantified(*a, assumptions)?,
            reduce_quantified(*b, assumptions)?,
        ]),
        C::TypeEq(Ty::Arr(a, effect, b), Ty::Arr(a2, effect2, b2)) => reduce_quantified(
            conjunction([
                C::TypeEq(*a, *a2),
                C::TypeEq(*b, *b2),
                C::EffectLe(effect.clone(), effect2.clone()),
                C::EffectLe(effect2, effect),
            ]),
            assumptions,
        )?,
        C::AllTy(i, body) => {
            let body = reduce_quantified(*body, assumptions)?;
            if body.fv_types().contains(&i) {
                C::AllTy(i, Box::new(body))
            } else {
                body
            }
        }
        C::AllEff(i, body) => {
            let body = reduce_quantified(*body, assumptions)?;
            if body.fv_effects().contains(&i) {
                C::AllEff(i, Box::new(body))
            } else {
                body
            }
        }
        C::ExTy(i, body) => {
            let body = reduce_quantified(*body, assumptions)?;
            let mut atoms = Vec::new();
            flatten_and(body.clone(), &mut atoms);
            if let Some((index, witness)) = type_witness(i, &body, &atoms) {
                atoms.remove(index);
                reduce_quantified(
                    conjunction(atoms.into_iter().map(|c| replace_type(c, i, &witness))),
                    assumptions,
                )?
            } else if body.fv_types().contains(&i) {
                C::ExTy(i, Box::new(body))
            } else {
                body
            }
        }
        C::ExEff(i, body) => {
            let body = reduce_quantified(*body, assumptions)?;
            let mut atoms = Vec::new();
            flatten_and(body.clone(), &mut atoms);
            if let Some((left, right, witness)) = effect_witness(i, &body, &atoms) {
                atoms.remove(left.max(right));
                atoms.remove(left.min(right));
                reduce_quantified(
                    conjunction(atoms.into_iter().map(|c| replace_effect(c, i, &witness))),
                    assumptions,
                )?
            } else if forced_empty_effect(i, &atoms) {
                reduce_quantified(replace_effect(body, i, &Effect::default()), assumptions)?
            } else if let Some(index) = sole_effect_bound(i, &atoms) {
                atoms.remove(index);
                reduce_quantified(conjunction(atoms), assumptions)?
            } else if body.fv_effects().contains(&i) {
                C::ExEff(i, Box::new(body))
            } else {
                body
            }
        }
        atom => Solver::default().atom(atom, assumptions)?,
    })
}

/// Solve free type equalities, forced-empty effects, built-in class instances,
/// and local existential witnesses. Other quantified constraints remain.
pub fn solve_with_fixed(
    output: Output<ClassPred>,
    assumptions: &[ClassPred],
    fixed_types: &BTreeSet<Id>,
    fixed_effects: &BTreeSet<Id>,
) -> Result<Output<ClassPred>, SolveError> {
    let mut solver = Solver {
        fixed_types: fixed_types.clone(),
        fixed_effects: fixed_effects.clone(),
        ..Solver::default()
    };
    let mut constraints = output.constraints;
    loop {
        let previous = constraints.clone();
        let mut equations = Vec::new();
        let mut atoms = Vec::new();
        collect_top(
            reduce_quantified(constraints, assumptions)?,
            &mut equations,
            &mut atoms,
        );
        solver.unify(&mut equations, &mut atoms)?;
        loop {
            let emptied = solver.bind_empty_effects(&atoms)?;
            let equated = solver.bind_equal_effects(&atoms);
            if !emptied && !equated {
                break;
            }
        }
        constraints = reduce_quantified(
            conjunction(
                atoms
                    .into_iter()
                    .map(|atom| solver.atom(atom, assumptions))
                    .collect::<Result<Vec<_>, _>>()?,
            ),
            assumptions,
        )?;
        if constraints == previous {
            break;
        }
    }
    Ok(Output {
        ty: solver.ty(&output.ty),
        effect: solver.effect(&output.effect),
        constraints,
        next: output.next,
    })
}

pub fn solve(
    output: Output<ClassPred>,
    assumptions: &[ClassPred],
) -> Result<Output<ClassPred>, SolveError> {
    solve_with_fixed(output, assumptions, &BTreeSet::new(), &BTreeSet::new())
}
