//! HM(X)-style constraint-system interface used by syntax-directed generation.
//! A system owns complete formulas, including equalities and effect constraints.
//! The handler operation discharges its rigid operation parameters; it does not
//! require a general universal-quantifier constructor in the base interface.

use crate::core::*;
use crate::infer::{InferError, Supply};
use std::collections::{BTreeMap, BTreeSet};

pub trait ConstraintSystem {
    type Formula: Clone + std::fmt::Debug;

    fn top(&self) -> Self::Formula;
    fn meet(&self, left: Self::Formula, right: Self::Formula) -> Self::Formula;
    fn type_eq(&self, left: Ty, right: Ty) -> Self::Formula;
    fn effect_le(&self, left: Effect, right: Effect) -> Self::Formula;
    fn lacks(&self, op: Id, effect: Effect) -> Self::Formula;
    fn hide_type(&self, name: Id, formula: Self::Formula) -> Self::Formula;
    fn hide_effect(&self, name: Id, formula: Self::Formula) -> Self::Formula;
    fn rename(
        &self,
        formula: &Self::Formula,
        types: &impl Fn(Id) -> Id,
        effects: &impl Fn(Id) -> Id,
    ) -> Self::Formula;
    fn free_types(&self, formula: &Self::Formula) -> BTreeSet<Id>;
    fn free_effects(&self, formula: &Self::Formula) -> BTreeSet<Id>;
    fn bound_types(&self, formula: &Self::Formula) -> BTreeSet<Id>;
    fn bound_effects(&self, formula: &Self::Formula) -> BTreeSet<Id>;

    fn project(
        &self,
        types: &BTreeSet<Id>,
        effects: &BTreeSet<Id>,
        mut formula: Self::Formula,
    ) -> Self::Formula {
        for i in effects.iter().rev() {
            formula = self.hide_effect(*i, formula);
        }
        for i in types.iter().rev() {
            formula = self.hide_type(*i, formula);
        }
        formula
    }

    fn split(&self, op: Id, input: Effect, rest: Effect) -> Self::Formula {
        self.meet(
            self.effect_le(rest.clone(), input.clone()),
            self.meet(
                self.effect_le(input, Effect::singleton(op).union(&rest)),
                self.lacks(op, rest),
            ),
        )
    }

    /// The result means: for every instantiation of `rigid_*`, there exist
    /// values for `local_*` that satisfy `formula`. A domain may retain this
    /// obligation symbolically and later check it using fresh rigid names.
    fn handler_clause(
        &self,
        rigid_types: &BTreeSet<Id>,
        rigid_effects: &BTreeSet<Id>,
        local_types: &BTreeSet<Id>,
        local_effects: &BTreeSet<Id>,
        formula: Self::Formula,
    ) -> Self::Formula;
}

#[derive(Clone, Copy, Debug, Default)]
pub struct PredicateSystem<P: Predicate>(std::marker::PhantomData<P>);

pub type ClassSystem = PredicateSystem<ClassPred>;
pub type EmptySystem = PredicateSystem<EmptyPred>;

impl<P: Predicate> PredicateSystem<P> {
    pub fn new() -> Self {
        Self(std::marker::PhantomData)
    }
}

impl<P: Predicate> ConstraintSystem for PredicateSystem<P> {
    type Formula = Constraint<P>;
    fn top(&self) -> Self::Formula {
        Constraint::Top
    }
    fn meet(&self, a: Self::Formula, b: Self::Formula) -> Self::Formula {
        Constraint::and(a, b)
    }
    fn type_eq(&self, a: Ty, b: Ty) -> Self::Formula {
        Constraint::TypeEq(a, b)
    }
    fn effect_le(&self, a: Effect, b: Effect) -> Self::Formula {
        Constraint::EffectLe(a, b)
    }
    fn lacks(&self, op: Id, e: Effect) -> Self::Formula {
        Constraint::Lacks(op, e)
    }
    fn hide_type(&self, i: Id, c: Self::Formula) -> Self::Formula {
        Constraint::ExTy(i, Box::new(c))
    }
    fn hide_effect(&self, i: Id, c: Self::Formula) -> Self::Formula {
        Constraint::ExEff(i, Box::new(c))
    }
    fn rename(
        &self,
        c: &Self::Formula,
        tf: &impl Fn(Id) -> Id,
        ef: &impl Fn(Id) -> Id,
    ) -> Self::Formula {
        c.rename(tf, ef)
    }
    fn free_types(&self, c: &Self::Formula) -> BTreeSet<Id> {
        c.fv_types()
    }
    fn free_effects(&self, c: &Self::Formula) -> BTreeSet<Id> {
        c.fv_effects()
    }
    fn bound_types(&self, c: &Self::Formula) -> BTreeSet<Id> {
        c.bound_types()
    }
    fn bound_effects(&self, c: &Self::Formula) -> BTreeSet<Id> {
        c.bound_effects()
    }
    fn handler_clause(
        &self,
        rt: &BTreeSet<Id>,
        re: &BTreeSet<Id>,
        lt: &BTreeSet<Id>,
        le: &BTreeSet<Id>,
        c: Self::Formula,
    ) -> Self::Formula {
        Constraint::close(rt, re, Constraint::project(lt, le, c))
    }
}

#[derive(Clone, Debug)]
pub struct QualifiedScheme<F> {
    pub type_vars: BTreeSet<Id>,
    pub effect_vars: BTreeSet<Id>,
    pub condition: F,
    pub result: Ty,
}

impl<F: Clone> QualifiedScheme<F> {
    pub fn mono<X: ConstraintSystem<Formula = F>>(x: &X, result: Ty) -> Self {
        Self {
            type_vars: BTreeSet::new(),
            effect_vars: BTreeSet::new(),
            condition: x.top(),
            result,
        }
    }
    pub fn fv_types<X: ConstraintSystem<Formula = F>>(&self, x: &X) -> BTreeSet<Id> {
        self.result
            .fv_types()
            .union(&x.free_types(&self.condition))
            .copied()
            .filter(|i| !self.type_vars.contains(i))
            .collect()
    }
    pub fn fv_effects<X: ConstraintSystem<Formula = F>>(&self, x: &X) -> BTreeSet<Id> {
        self.result
            .fv_effects()
            .union(&x.free_effects(&self.condition))
            .copied()
            .filter(|i| !self.effect_vars.contains(i))
            .collect()
    }
    pub fn generalize<X: ConstraintSystem<Formula = F>>(
        x: &X,
        ctx: &[Self],
        condition: F,
        result: Ty,
    ) -> Self {
        let ct: BTreeSet<_> = ctx.iter().flat_map(|s| s.fv_types(x)).collect();
        let ce: BTreeSet<_> = ctx.iter().flat_map(|s| s.fv_effects(x)).collect();
        Self {
            type_vars: result
                .fv_types()
                .union(&x.free_types(&condition))
                .copied()
                .filter(|i| !ct.contains(i))
                .collect(),
            effect_vars: result
                .fv_effects()
                .union(&x.free_effects(&condition))
                .copied()
                .filter(|i| !ce.contains(i))
                .collect(),
            condition,
            result,
        }
    }
    pub fn instantiate<X: ConstraintSystem<Formula = F>>(
        &self,
        x: &X,
        s: Supply,
    ) -> Result<(Ty, F), InferError> {
        let tf = |i| {
            if self.type_vars.contains(&i) {
                s.types + i + 1
            } else {
                i
            }
        };
        let ef = |i| {
            if self.effect_vars.contains(&i) {
                s.effects + i + 1
            } else {
                i
            }
        };
        let new_t: BTreeSet<_> = self.type_vars.iter().map(|i| tf(*i)).collect();
        let new_e: BTreeSet<_> = self.effect_vars.iter().map(|i| ef(*i)).collect();
        let mut used_t = self.fv_types(x);
        used_t.extend(x.bound_types(&self.condition));
        let mut used_e = self.fv_effects(x);
        used_e.extend(x.bound_effects(&self.condition));
        if new_t.len() != self.type_vars.len()
            || new_e.len() != self.effect_vars.len()
            || !new_t.is_disjoint(&used_t)
            || !new_e.is_disjoint(&used_e)
        {
            return Err(InferError::SchemeCapture);
        }
        Ok((
            self.result.rename(&tf, &ef),
            x.rename(&self.condition, &tf, &ef),
        ))
    }
}

impl<P: Predicate> From<Scheme<P>> for QualifiedScheme<Constraint<P>> {
    fn from(s: Scheme<P>) -> Self {
        Self {
            type_vars: s.type_vars,
            effect_vars: s.effect_vars,
            condition: s.predicates,
            result: s.result,
        }
    }
}

#[derive(Clone, Debug)]
pub struct QualifiedOutput<F> {
    pub ty: Ty,
    pub effect: Effect,
    pub condition: F,
    pub next: Supply,
}

fn advance(s: Supply, ts: &BTreeSet<Id>, es: &BTreeSet<Id>) -> Supply {
    Supply {
        types: s.types + ts.last().copied().unwrap_or(0) + 2,
        effects: s.effects + es.last().copied().unwrap_or(0) + 2,
    }
}

fn scope_ok<X: ConstraintSystem>(
    x: &X,
    d: &OpDecl,
    ctx: &[QualifiedScheme<X::Formula>],
    ty_in: &Ty,
    result: &Ty,
    effects: [&Effect; 4],
) -> bool {
    let mut ft: BTreeSet<_> = ctx.iter().flat_map(|s| s.fv_types(x)).collect();
    ft.extend(ty_in.fv_types());
    ft.extend(result.fv_types());
    let mut fe: BTreeSet<_> = ctx.iter().flat_map(|s| s.fv_effects(x)).collect();
    fe.extend(ty_in.fv_effects());
    fe.extend(result.fv_effects());
    for e in effects {
        fe.extend(&e.vars);
    }
    d.type_vars.is_disjoint(&ft) && d.effect_vars.is_disjoint(&fe)
}

pub fn generate<X: ConstraintSystem>(
    x: &X,
    sig: &BTreeMap<Id, OpDecl>,
    ctx: &[QualifiedScheme<X::Formula>],
    e: &Expr,
    s: Supply,
) -> Result<QualifiedOutput<X::Formula>, InferError> {
    match e {
        Expr::Var(i) => {
            let scheme = ctx.get(*i).ok_or(InferError::UnknownVariable(*i))?;
            let (ty, condition) = scheme.instantiate(x, s)?;
            Ok(QualifiedOutput {
                ty,
                effect: Effect::default(),
                condition,
                next: advance(s, &scheme.type_vars, &scheme.effect_vars),
            })
        }
        Expr::Int(_) | Expr::Bool(_) => Ok(QualifiedOutput {
            ty: Ty::Base(if matches!(e, Expr::Int(_)) {
                BaseTy::Int
            } else {
                BaseTy::Bool
            }),
            effect: Effect::default(),
            condition: x.top(),
            next: s,
        }),
        Expr::Lam(body) => {
            let a = Ty::Var(s.types);
            let mut inner = vec![QualifiedScheme::mono(x, a.clone())];
            inner.extend_from_slice(ctx);
            let r = generate(
                x,
                sig,
                &inner,
                body,
                Supply {
                    types: s.types + 1,
                    ..s
                },
            )?;
            Ok(QualifiedOutput {
                ty: Ty::Arr(Box::new(a), r.effect, Box::new(r.ty)),
                effect: Effect::default(),
                condition: r.condition,
                next: r.next,
            })
        }
        Expr::App(f, arg) => {
            let rf = generate(x, sig, ctx, f, s)?;
            let ra = generate(x, sig, ctx, arg, rf.next)?;
            let b = Ty::Var(ra.next.types);
            let eta = Effect::var(ra.next.effects);
            Ok(QualifiedOutput {
                ty: b.clone(),
                effect: rf.effect.union(&ra.effect).union(&eta),
                condition: x.meet(
                    x.meet(rf.condition, ra.condition),
                    x.type_eq(rf.ty, Ty::Arr(Box::new(ra.ty), eta, Box::new(b))),
                ),
                next: Supply {
                    types: ra.next.types + 1,
                    effects: ra.next.effects + 1,
                },
            })
        }
        Expr::Let(bound, body) => {
            let r1 = generate(x, sig, ctx, bound, s)?;
            if bound.is_value() {
                let scheme = QualifiedScheme::generalize(x, ctx, r1.condition.clone(), r1.ty);
                let residual = x.project(&scheme.type_vars, &scheme.effect_vars, r1.condition);
                let mut inner = vec![scheme];
                inner.extend_from_slice(ctx);
                let mut r2 = generate(x, sig, &inner, body, r1.next)?;
                r2.condition = x.meet(residual, r2.condition);
                Ok(r2)
            } else {
                let mut inner = vec![QualifiedScheme::mono(x, r1.ty)];
                inner.extend_from_slice(ctx);
                let r2 = generate(x, sig, &inner, body, r1.next)?;
                Ok(QualifiedOutput {
                    ty: r2.ty,
                    effect: r1.effect.union(&r2.effect),
                    condition: x.meet(r1.condition, r2.condition),
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
            let r = generate(x, sig, ctx, arg, advance(s, &d.type_vars, &d.effect_vars))?;
            Ok(QualifiedOutput {
                ty: d.output.rename(&tf, &ef),
                effect: Effect::singleton(*op).union(&r.effect),
                condition: x.meet(r.condition, x.type_eq(r.ty, d.input.rename(&tf, &ef))),
                next: r.next,
            })
        }
        Expr::Handle(body, op, ret, clause) => {
            let raw = sig.get(op).ok_or(InferError::UnknownOperation(*op))?;
            let rb = generate(x, sig, ctx, body, s)?;
            let tf = |i| {
                if raw.type_vars.contains(&i) {
                    rb.next.types + i + 1
                } else {
                    i
                }
            };
            let ef = |i| {
                if raw.effect_vars.contains(&i) {
                    rb.next.effects + i + 1
                } else {
                    i
                }
            };
            let d = raw.alpha_rename(&tf, &ef);
            if !raw.alpha_safe(&d) {
                return Err(InferError::HandlerScope);
            }
            let sb = advance(rb.next, &raw.type_vars, &raw.effect_vars);
            let a = Ty::Var(sb.types);
            let delta = Effect::var(sb.effects);
            let chi = Effect::var(sb.effects + 1);
            let sr = Supply {
                types: sb.types + 1,
                effects: sb.effects + 2,
            };
            let mut ret_ctx = vec![QualifiedScheme::mono(x, rb.ty.clone())];
            ret_ctx.extend_from_slice(ctx);
            let rr = generate(x, sig, &ret_ctx, ret, sr)?;
            let mut clause_ctx = vec![
                QualifiedScheme::mono(
                    x,
                    Ty::Arr(Box::new(d.output.clone()), chi.clone(), Box::new(a.clone())),
                ),
                QualifiedScheme::mono(x, d.input.clone()),
            ];
            clause_ctx.extend_from_slice(ctx);
            let rc = generate(x, sig, &clause_ctx, clause, rr.next)?;
            let lt: BTreeSet<_> = (rr.next.types..rc.next.types).collect();
            let le: BTreeSet<_> = (rr.next.effects..rc.next.effects).collect();
            if !scope_ok(
                x,
                &d,
                ctx,
                &rb.ty,
                &a,
                [&rb.effect, &rr.effect, &delta, &chi],
            ) {
                return Err(InferError::HandlerScope);
            }
            let clause_condition = x.handler_clause(
                &d.type_vars,
                &d.effect_vars,
                &lt,
                &le,
                x.meet(
                    rc.condition,
                    x.meet(
                        x.type_eq(rc.ty, a.clone()),
                        x.effect_le(rc.effect, chi.clone()),
                    ),
                ),
            );
            let condition = x.meet(
                x.meet(rb.condition, rr.condition),
                x.meet(
                    x.type_eq(rr.ty, a.clone()),
                    x.meet(
                        clause_condition,
                        x.meet(
                            x.split(*op, rb.effect, delta.clone()),
                            x.meet(
                                x.effect_le(delta, chi.clone()),
                                x.effect_le(rr.effect, chi.clone()),
                            ),
                        ),
                    ),
                ),
            );
            let outer_t = x.free_types(&condition);
            let outer_e = x.free_effects(&condition);
            if !d.type_vars.is_disjoint(&outer_t) || !d.effect_vars.is_disjoint(&outer_e) {
                return Err(InferError::HandlerScope);
            }
            let mut scope_t: BTreeSet<_> = ctx.iter().flat_map(|s| s.fv_types(x)).collect();
            scope_t.extend(outer_t);
            scope_t.extend(rb.ty.fv_types());
            scope_t.extend(a.fv_types());
            scope_t.extend(&d.type_vars);
            scope_t.extend(d.input.fv_types());
            scope_t.extend(d.output.fv_types());
            let mut scope_e: BTreeSet<_> = ctx.iter().flat_map(|s| s.fv_effects(x)).collect();
            scope_e.extend(outer_e);
            scope_e.extend(rb.ty.fv_effects());
            scope_e.extend(a.fv_effects());
            scope_e.extend(&d.effect_vars);
            scope_e.extend(d.input.fv_effects());
            scope_e.extend(d.output.fv_effects());
            if !lt.is_disjoint(&scope_t) || !le.is_disjoint(&scope_e) {
                return Err(InferError::HandlerScope);
            }
            Ok(QualifiedOutput {
                ty: a,
                effect: chi,
                condition,
                next: rc.next,
            })
        }
    }
}
