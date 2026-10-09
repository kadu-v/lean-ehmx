//! A concrete solver for the REPL's built-in Eq and Show predicates.
//! Quantified handler constraints remain symbolic unless an atom is already
//! ground; solving them by free-variable unification would be unsound.

use crate::core::{BaseTy, ClassPred, Constraint, Effect, Id, Ty};
use crate::infer::Output;
use std::collections::BTreeMap;

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
                Some(bound) => acc.union(bound),
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
                (Ty::Var(i), t) | (t, Ty::Var(i)) => {
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
                        if right.labels.is_subset(&excluded)
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

/// Solve free type equalities, forced-empty effects, and the built-in class
/// instances. All remaining constraints are returned, including quantified
/// constraints that require a stronger solver.
pub fn solve(
    output: Output<ClassPred>,
    assumptions: &[ClassPred],
) -> Result<Output<ClassPred>, SolveError> {
    let mut equations = Vec::new();
    let mut atoms = Vec::new();
    collect_top(output.constraints, &mut equations, &mut atoms);
    let mut solver = Solver::default();
    solver.unify(&mut equations, &mut atoms)?;
    while solver.bind_empty_effects(&atoms)? {}
    let constraints = conjunction(
        atoms
            .into_iter()
            .map(|atom| solver.atom(atom, assumptions))
            .collect::<Result<Vec<_>, _>>()?,
    );
    Ok(Output {
        ty: solver.ty(&output.ty),
        effect: solver.effect(&output.effect),
        constraints,
        next: output.next,
    })
}
