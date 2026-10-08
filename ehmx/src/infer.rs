use crate::core::*;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Copy, Debug, Default)]
pub struct Supply {
    pub types: Id,
    pub effects: Id,
}
impl Supply {
    fn advance(self, ts: &BTreeSet<Id>, es: &BTreeSet<Id>) -> Self {
        Self {
            types: self.types + ts.last().copied().unwrap_or(0) + 2,
            effects: self.effects + es.last().copied().unwrap_or(0) + 2,
        }
    }
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
    OccursCheck,
    TypeMismatch,
    EffectMismatch,
    LacksViolation,
}

fn scope_ok<P: Predicate>(
    d: &OpDecl,
    ctx: &[Scheme<P>],
    ti: &Ty,
    a: &Ty,
    ei: &Effect,
    er: &Effect,
    delta: &Effect,
    chi: &Effect,
) -> bool {
    let mut ft: BTreeSet<_> = ctx.iter().flat_map(|s| s.fv_types()).collect();
    ft.extend(ti.fv_types());
    ft.extend(a.fv_types());
    let mut fe: BTreeSet<_> = ctx.iter().flat_map(|s| s.fv_effects()).collect();
    fe.extend(ti.fv_effects());
    fe.extend(a.fv_effects());
    for e in [ei, er, delta, chi] {
        fe.extend(&e.vars);
    }
    d.type_vars.is_disjoint(&ft) && d.effect_vars.is_disjoint(&fe)
}

pub fn generate<P: Predicate>(
    sig: &BTreeMap<Id, OpDecl>,
    ctx: &[Scheme<P>],
    e: &Expr,
    s: Supply,
) -> Result<Output<P>, InferError> {
    use Constraint as C;
    match e {
        Expr::Var(i) => {
            let scheme = ctx.get(*i).ok_or(InferError::UnknownVariable(*i))?;
            let (ty, constraints) = scheme.instantiate(s.types, s.effects);
            Ok(Output {
                ty,
                effect: Effect::default(),
                constraints,
                next: s.advance(&scheme.type_vars, &scheme.effect_vars),
            })
        }
        Expr::Int(_) => Ok(Output {
            ty: Ty::Base(BaseTy::Int),
            effect: Effect::default(),
            constraints: C::Top,
            next: s,
        }),
        Expr::Bool(_) => Ok(Output {
            ty: Ty::Base(BaseTy::Bool),
            effect: Effect::default(),
            constraints: C::Top,
            next: s,
        }),
        Expr::Lam(body) => {
            let a = Ty::Var(s.types);
            let mut inner = vec![Scheme::mono(a.clone())];
            inner.extend_from_slice(ctx);
            let r = generate(
                sig,
                &inner,
                body,
                Supply {
                    types: s.types + 1,
                    ..s
                },
            )?;
            Ok(Output {
                ty: Ty::Arr(Box::new(a), r.effect, Box::new(r.ty)),
                effect: Effect::default(),
                constraints: r.constraints,
                next: r.next,
            })
        }
        Expr::App(f, x) => {
            let rf = generate(sig, ctx, f, s)?;
            let rx = generate(sig, ctx, x, rf.next)?;
            let b = Ty::Var(rx.next.types);
            let eta = Effect::var(rx.next.effects);
            let constraints = C::and(
                C::and(rf.constraints, rx.constraints),
                C::TypeEq(
                    rf.ty,
                    Ty::Arr(Box::new(rx.ty), eta.clone(), Box::new(b.clone())),
                ),
            );
            Ok(Output {
                ty: b,
                effect: rf.effect.union(&rx.effect).union(&eta),
                constraints,
                next: Supply {
                    types: rx.next.types + 1,
                    effects: rx.next.effects + 1,
                },
            })
        }
        Expr::Let(e1, e2) => {
            let r1 = generate(sig, ctx, e1, s)?;
            if e1.is_value() {
                let scheme = Scheme::generalize(ctx, r1.constraints, r1.ty);
                let mut inner = vec![scheme];
                inner.extend_from_slice(ctx);
                generate(sig, &inner, e2, r1.next)
            } else {
                let mut inner = vec![Scheme::mono(r1.ty)];
                inner.extend_from_slice(ctx);
                let r2 = generate(sig, &inner, e2, r1.next)?;
                Ok(Output {
                    ty: r2.ty,
                    effect: r1.effect.union(&r2.effect),
                    constraints: C::and(r1.constraints, r2.constraints),
                    next: r2.next,
                })
            }
        }
        Expr::Perform(op, arg) => {
            let d = sig.get(op).ok_or(InferError::UnknownOperation(*op))?;
            let tf = |i| {
                if d.type_vars.contains(&i) {
                    s.types + i + 1
                } else {
                    i
                }
            };
            let ef = |i| {
                if d.effect_vars.contains(&i) {
                    s.effects + i + 1
                } else {
                    i
                }
            };
            let r = generate(sig, ctx, arg, s.advance(&d.type_vars, &d.effect_vars))?;
            Ok(Output {
                ty: d.output.rename(&tf, &ef),
                effect: Effect::singleton(*op).union(&r.effect),
                constraints: C::and(r.constraints, C::TypeEq(r.ty, d.input.rename(&tf, &ef))),
                next: r.next,
            })
        }
        Expr::Handle(body, op, ret, clause) => {
            let d = sig.get(op).ok_or(InferError::UnknownOperation(*op))?;
            let rb = generate(sig, ctx, body, s)?;
            let a = Ty::Var(rb.next.types);
            let delta = Effect::var(rb.next.effects);
            let chi = Effect::var(rb.next.effects + 1);
            let sr = Supply {
                types: rb.next.types + 1,
                effects: rb.next.effects + 2,
            };
            let mut ret_ctx = vec![Scheme::mono(rb.ty.clone())];
            ret_ctx.extend_from_slice(ctx);
            let rr = generate(sig, &ret_ctx, ret, sr)?;
            let mut clause_ctx = vec![
                Scheme::mono(Ty::Arr(
                    Box::new(d.output.clone()),
                    chi.clone(),
                    Box::new(a.clone()),
                )),
                Scheme::mono(d.input.clone()),
            ];
            clause_ctx.extend_from_slice(ctx);
            let rc = generate(sig, &clause_ctx, clause, rr.next)?;
            if !scope_ok(d, ctx, &rb.ty, &a, &rb.effect, &rr.effect, &delta, &chi) {
                return Err(InferError::HandlerScope);
            }
            let clause_c = C::close(
                &d.type_vars,
                &d.effect_vars,
                C::and(
                    rc.constraints,
                    C::and(
                        C::TypeEq(rc.ty, a.clone()),
                        C::EffectLe(rc.effect, chi.clone()),
                    ),
                ),
            );
            let constraints = C::and(
                C::and(rb.constraints, rr.constraints),
                C::and(
                    C::TypeEq(rr.ty, a.clone()),
                    C::and(
                        clause_c,
                        C::and(
                            C::split(*op, rb.effect, delta.clone()),
                            C::and(
                                C::EffectLe(delta, chi.clone()),
                                C::EffectLe(rr.effect, chi.clone()),
                            ),
                        ),
                    ),
                ),
            );
            Ok(Output {
                ty: a,
                effect: chi,
                constraints,
                next: rc.next,
            })
        }
    }
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
    match c {
        Constraint::And(a, b) => Ok(Constraint::and(simplify(*a)?, simplify(*b)?)),
        atom => simplify_atom(atom),
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
    let mut r = generate(sig, ctx, e, s)?;
    let c = simplify(r.constraints)?;
    r.constraints = Constraint::and(assumptions(ps), resolve_x(ps, c));
    Ok(r)
}
