use crate::core::*;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Copy, Debug, Default)]
pub struct Supply {
    pub types: Id,
    pub effects: Id,
}
fn seed_supply<P: Predicate>(
    sig: &BTreeMap<Id, OpDecl>,
    ctx: &[Scheme<P>],
    ps: &[P],
    mut s: Supply,
) -> Supply {
    let mut types = BTreeSet::new();
    let mut effects = BTreeSet::new();
    for scheme in ctx {
        types.extend(&scheme.type_vars);
        types.extend(scheme.result.fv_types());
        types.extend(scheme.predicates.fv_types());
        types.extend(scheme.predicates.bound_types());
        effects.extend(&scheme.effect_vars);
        effects.extend(scheme.result.fv_effects());
        effects.extend(scheme.predicates.fv_effects());
        effects.extend(scheme.predicates.bound_effects());
    }
    for decl in sig.values() {
        types.extend(&decl.type_vars);
        types.extend(decl.input.fv_types());
        types.extend(decl.output.fv_types());
        effects.extend(&decl.effect_vars);
        effects.extend(decl.input.fv_effects());
        effects.extend(decl.output.fv_effects());
    }
    for p in ps {
        types.extend(p.fv_types());
        effects.extend(p.fv_effects());
    }
    if let Some(i) = types.last() {
        s.types = s.types.max(i + 1);
    }
    if let Some(i) = effects.last() {
        s.effects = s.effects.max(i + 1);
    }
    s
}

#[derive(Clone, Debug)]
pub struct Output<P: Predicate> {
    pub ty: Ty,
    pub effect: Effect,
    pub constraints: Constraint<P>,
    pub next: Supply,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InferError {
    UnknownVariable(Id),
    UnknownOperation(Id),
    HandlerScope,
    SchemeCapture,
    OccursCheck,
    TypeMismatch,
    EffectMismatch,
    LacksViolation,
    RigidTypeMismatch,
}

/// Generate a constraint in the selected full constraint system. The
/// compatibility API uses the predicate-backed system supplied by `core`.
pub fn generate<P: Predicate>(
    sig: &BTreeMap<Id, OpDecl>,
    ctx: &[Scheme<P>],
    e: &Expr,
    s: Supply,
) -> Result<Output<P>, InferError> {
    generate_via_system(sig, ctx, e, s)
}

fn occurs_bad(a: &Ty, b: &Ty) -> bool {
    match (a, b) {
        (Ty::Var(i), t) | (t, Ty::Var(i)) => t.fv_types().contains(i),
        _ => false,
    }
}

pub fn simplify_atom<P: Predicate>(c: Constraint<P>) -> Result<Constraint<P>, InferError> {
    use Constraint as C;
    match c {
        C::TypeEq(Ty::Arr(a, e, b), Ty::Arr(a2, e2, b2)) => Ok(C::and(
            C::TypeEq(*a, *a2),
            C::and(
                C::TypeEq(*b, *b2),
                C::and(C::EffectLe(e.clone(), e2.clone()), C::EffectLe(e2, e)),
            ),
        )),
        C::TypeEq(Ty::Base(a), Ty::Base(b)) => {
            if a == b {
                Ok(C::Top)
            } else {
                Err(InferError::TypeMismatch)
            }
        }
        C::TypeEq(Ty::Base(_), Ty::Arr(_, _, _)) | C::TypeEq(Ty::Arr(_, _, _), Ty::Base(_)) => {
            Err(InferError::TypeMismatch)
        }
        C::TypeEq(a, b) => {
            if a == b {
                Ok(C::Top)
            } else if occurs_bad(&a, &b) {
                Err(InferError::OccursCheck)
            } else {
                Ok(C::TypeEq(a, b))
            }
        }
        C::EffectLe(a, b) if a.vars.is_empty() && b.vars.is_empty() => {
            if a.labels.is_subset(&b.labels) {
                Ok(C::Top)
            } else {
                Err(InferError::EffectMismatch)
            }
        }
        C::Lacks(op, e) if e.vars.is_empty() => {
            if !e.labels.contains(&op) {
                Ok(C::Top)
            } else {
                Err(InferError::LacksViolation)
            }
        }
        other => Ok(other),
    }
}
pub fn simplify<P: Predicate>(c: Constraint<P>) -> Result<Constraint<P>, InferError> {
    if rigid_var_equality(&c, &BTreeSet::new(), &BTreeMap::new()) {
        return Err(InferError::RigidTypeMismatch);
    }
    match c {
        Constraint::And(a, b) => Ok(Constraint::and(simplify(*a)?, simplify(*b)?)),
        atom => simplify_atom(atom),
    }
}

fn rigid_var_equality<P: Predicate>(
    c: &Constraint<P>,
    bound: &BTreeSet<Id>,
    witnesses: &BTreeMap<Id, BTreeSet<Id>>,
) -> bool {
    // A universally quantified type variable cannot equal a distinct fixed
    // variable for every instantiation.
    match c {
        Constraint::And(a, b) => {
            rigid_var_equality(a, bound, witnesses) || rigid_var_equality(b, bound, witnesses)
        }
        Constraint::AllTy(i, inner) => {
            let mut bound = bound.clone();
            bound.insert(*i);
            rigid_var_equality(inner, &bound, witnesses)
        }
        Constraint::AllEff(_, inner) | Constraint::ExEff(_, inner) => {
            rigid_var_equality(inner, bound, witnesses)
        }
        Constraint::ExTy(i, inner) => {
            let mut witnesses = witnesses.clone();
            witnesses.insert(*i, bound.clone());
            rigid_var_equality(inner, bound, &witnesses)
        }
        Constraint::TypeEq(Ty::Var(a), Ty::Var(b)) => {
            a != b
                && ((bound.contains(a) && !witnesses.get(b).is_some_and(|deps| deps.contains(a)))
                    || (bound.contains(b)
                        && !witnesses.get(a).is_some_and(|deps| deps.contains(b))))
        }
        _ => false,
    }
}
pub fn assumptions<P: Predicate>(ps: &[P]) -> Constraint<P> {
    ps.iter().rev().fold(Constraint::Top, |c, p| {
        Constraint::and(Constraint::Pred(p.clone()), c)
    })
}
pub fn resolve_x<P: Predicate>(ps: &[P], c: Constraint<P>) -> Constraint<P> {
    match c {
        Constraint::And(a, b) => Constraint::and(resolve_x(ps, *a), resolve_x(ps, *b)),
        Constraint::Pred(p) if ps.contains(&p) => Constraint::Top,
        other => other,
    }
}
pub fn infer_qualified<P: Predicate>(
    sig: &BTreeMap<Id, OpDecl>,
    ctx: &[Scheme<P>],
    e: &Expr,
    s: Supply,
    ps: &[P],
) -> Result<Output<P>, InferError> {
    let mut r = generate_via_system(sig, ctx, e, seed_supply(sig, ctx, ps, s))?;
    let c = simplify(r.constraints)?;
    r.constraints = Constraint::and(assumptions(ps), resolve_x(ps, c));
    Ok(r)
}

/// Preserve the complete qualified constraint, including contradictions.
/// The REPL-facing `infer_qualified` may report an obvious contradiction early.
pub fn infer_symbolic<P: Predicate>(
    sig: &BTreeMap<Id, OpDecl>,
    ctx: &[Scheme<P>],
    e: &Expr,
    s: Supply,
    ps: &[P],
) -> Result<Output<P>, InferError> {
    let mut r = generate_via_system(sig, ctx, e, seed_supply(sig, ctx, ps, s))?;
    r.constraints = Constraint::and(assumptions(ps), resolve_x(ps, r.constraints));
    Ok(r)
}

fn generate_via_system<P: Predicate>(
    sig: &BTreeMap<Id, OpDecl>,
    ctx: &[Scheme<P>],
    e: &Expr,
    s: Supply,
) -> Result<Output<P>, InferError> {
    let system = crate::system::PredicateSystem::<P>::new();
    let qualified: Vec<_> = ctx.iter().cloned().map(Into::into).collect();
    let r = crate::system::generate(&system, sig, &qualified, e, s)?;
    Ok(Output {
        ty: r.ty,
        effect: r.effect,
        constraints: r.condition,
        next: r.next,
    })
}
