use std::collections::BTreeSet;

pub type Id = usize;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum BaseTy {
    Int,
    Bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ty {
    Var(Id),
    Base(BaseTy),
    Arr(Box<Ty>, Effect, Box<Ty>),
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Effect {
    pub labels: BTreeSet<Id>,
    pub vars: BTreeSet<Id>,
}

impl Effect {
    pub fn singleton(op: Id) -> Self {
        Self {
            labels: [op].into(),
            vars: BTreeSet::new(),
        }
    }
    pub fn var(id: Id) -> Self {
        Self {
            labels: BTreeSet::new(),
            vars: [id].into(),
        }
    }
    pub fn union(&self, other: &Self) -> Self {
        Self {
            labels: self.labels.union(&other.labels).copied().collect(),
            vars: self.vars.union(&other.vars).copied().collect(),
        }
    }
    pub fn rename(&self, f: &impl Fn(Id) -> Id) -> Self {
        Self {
            labels: self.labels.clone(),
            vars: self.vars.iter().map(|v| f(*v)).collect(),
        }
    }
}

impl Ty {
    pub fn rename(&self, tf: &impl Fn(Id) -> Id, ef: &impl Fn(Id) -> Id) -> Self {
        match self {
            Self::Var(i) => Self::Var(tf(*i)),
            Self::Base(b) => Self::Base(*b),
            Self::Arr(a, e, b) => Self::Arr(
                Box::new(a.rename(tf, ef)),
                e.rename(ef),
                Box::new(b.rename(tf, ef)),
            ),
        }
    }
    pub fn fv_types(&self) -> BTreeSet<Id> {
        match self {
            Self::Var(i) => [*i].into(),
            Self::Base(_) => BTreeSet::new(),
            Self::Arr(a, _, b) => a.fv_types().union(&b.fv_types()).copied().collect(),
        }
    }
    pub fn fv_effects(&self) -> BTreeSet<Id> {
        match self {
            Self::Var(_) | Self::Base(_) => BTreeSet::new(),
            Self::Arr(a, e, b) => a
                .fv_effects()
                .union(&e.vars)
                .copied()
                .collect::<BTreeSet<_>>()
                .union(&b.fv_effects())
                .copied()
                .collect(),
        }
    }
}

pub trait Predicate: Clone + Eq + std::fmt::Debug {
    fn rename(&self, tf: &impl Fn(Id) -> Id, ef: &impl Fn(Id) -> Id) -> Self;
    fn fv_types(&self) -> BTreeSet<Id>;
    fn fv_effects(&self) -> BTreeSet<Id>;
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ClassPred {
    Eq(Ty),
    Show(Ty),
}

impl Predicate for ClassPred {
    fn rename(&self, tf: &impl Fn(Id) -> Id, ef: &impl Fn(Id) -> Id) -> Self {
        match self {
            Self::Eq(t) => Self::Eq(t.rename(tf, ef)),
            Self::Show(t) => Self::Show(t.rename(tf, ef)),
        }
    }
    fn fv_types(&self) -> BTreeSet<Id> {
        match self {
            Self::Eq(t) | Self::Show(t) => t.fv_types(),
        }
    }
    fn fv_effects(&self) -> BTreeSet<Id> {
        match self {
            Self::Eq(t) | Self::Show(t) => t.fv_effects(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Constraint<P: Predicate> {
    Top,
    And(Box<Self>, Box<Self>),
    TypeEq(Ty, Ty),
    EffectLe(Effect, Effect),
    Lacks(Id, Effect),
    Pred(P),
    AllTy(Id, Box<Self>),
    AllEff(Id, Box<Self>),
    ExTy(Id, Box<Self>),
    ExEff(Id, Box<Self>),
}

impl<P: Predicate> Constraint<P> {
    pub fn and(a: Self, b: Self) -> Self {
        Self::And(Box::new(a), Box::new(b))
    }
    pub fn rename(&self, tf: &impl Fn(Id) -> Id, ef: &impl Fn(Id) -> Id) -> Self {
        match self {
            Self::Top => Self::Top,
            Self::And(a, b) => Self::and(a.rename(tf, ef), b.rename(tf, ef)),
            Self::TypeEq(a, b) => Self::TypeEq(a.rename(tf, ef), b.rename(tf, ef)),
            Self::EffectLe(a, b) => Self::EffectLe(a.rename(ef), b.rename(ef)),
            Self::Lacks(op, e) => Self::Lacks(*op, e.rename(ef)),
            Self::Pred(p) => Self::Pred(p.rename(tf, ef)),
            Self::AllTy(i, c) => Self::AllTy(tf(*i), Box::new(c.rename(tf, ef))),
            Self::AllEff(i, c) => Self::AllEff(ef(*i), Box::new(c.rename(tf, ef))),
            Self::ExTy(i, c) => Self::ExTy(tf(*i), Box::new(c.rename(tf, ef))),
            Self::ExEff(i, c) => Self::ExEff(ef(*i), Box::new(c.rename(tf, ef))),
        }
    }
    pub fn fv_types(&self) -> BTreeSet<Id> {
        match self {
            Self::Top | Self::EffectLe(_, _) | Self::Lacks(_, _) => BTreeSet::new(),
            Self::And(a, b) => a.fv_types().union(&b.fv_types()).copied().collect(),
            Self::TypeEq(a, b) => a.fv_types().union(&b.fv_types()).copied().collect(),
            Self::Pred(p) => p.fv_types(),
            Self::AllTy(i, c) | Self::ExTy(i, c) => {
                let mut x = c.fv_types();
                x.remove(i);
                x
            }
            Self::AllEff(_, c) | Self::ExEff(_, c) => c.fv_types(),
        }
    }
    pub fn fv_effects(&self) -> BTreeSet<Id> {
        match self {
            Self::Top => BTreeSet::new(),
            Self::And(a, b) => a.fv_effects().union(&b.fv_effects()).copied().collect(),
            Self::TypeEq(a, b) => a.fv_effects().union(&b.fv_effects()).copied().collect(),
            Self::EffectLe(a, b) => a.vars.union(&b.vars).copied().collect(),
            Self::Lacks(_, e) => e.vars.clone(),
            Self::Pred(p) => p.fv_effects(),
            Self::AllTy(_, c) | Self::ExTy(_, c) => c.fv_effects(),
            Self::AllEff(i, c) | Self::ExEff(i, c) => {
                let mut x = c.fv_effects();
                x.remove(i);
                x
            }
        }
    }
    pub fn bound_types(&self) -> BTreeSet<Id> {
        match self {
            Self::And(a, b) => a.bound_types().union(&b.bound_types()).copied().collect(),
            Self::AllTy(i, c) | Self::ExTy(i, c) => {
                let mut vars = c.bound_types();
                vars.insert(*i);
                vars
            }
            Self::AllEff(_, c) | Self::ExEff(_, c) => c.bound_types(),
            _ => BTreeSet::new(),
        }
    }
    pub fn bound_effects(&self) -> BTreeSet<Id> {
        match self {
            Self::And(a, b) => a
                .bound_effects()
                .union(&b.bound_effects())
                .copied()
                .collect(),
            Self::AllEff(i, c) | Self::ExEff(i, c) => {
                let mut vars = c.bound_effects();
                vars.insert(*i);
                vars
            }
            Self::AllTy(_, c) | Self::ExTy(_, c) => c.bound_effects(),
            _ => BTreeSet::new(),
        }
    }
    pub fn split(op: Id, input: Effect, rest: Effect) -> Self {
        Self::and(
            Self::EffectLe(rest.clone(), input.clone()),
            Self::and(
                Self::EffectLe(input, Effect::singleton(op).union(&rest)),
                Self::Lacks(op, rest),
            ),
        )
    }
    pub fn close(type_vars: &BTreeSet<Id>, effect_vars: &BTreeSet<Id>, mut c: Self) -> Self {
        for i in effect_vars.iter().rev() {
            c = Self::AllEff(*i, Box::new(c));
        }
        for i in type_vars.iter().rev() {
            c = Self::AllTy(*i, Box::new(c));
        }
        c
    }
    pub fn project(type_vars: &BTreeSet<Id>, effect_vars: &BTreeSet<Id>, mut c: Self) -> Self {
        for i in effect_vars.iter().rev() {
            c = Self::ExEff(*i, Box::new(c));
        }
        for i in type_vars.iter().rev() {
            c = Self::ExTy(*i, Box::new(c));
        }
        c
    }
}

#[derive(Clone, Debug)]
pub struct Scheme<P: Predicate> {
    pub type_vars: BTreeSet<Id>,
    pub effect_vars: BTreeSet<Id>,
    pub predicates: Constraint<P>,
    pub result: Ty,
}

impl<P: Predicate> Scheme<P> {
    pub fn mono(result: Ty) -> Self {
        Self {
            type_vars: BTreeSet::new(),
            effect_vars: BTreeSet::new(),
            predicates: Constraint::Top,
            result,
        }
    }
    pub fn fv_types(&self) -> BTreeSet<Id> {
        self.result
            .fv_types()
            .union(&self.predicates.fv_types())
            .copied()
            .filter(|i| !self.type_vars.contains(i))
            .collect()
    }
    pub fn fv_effects(&self) -> BTreeSet<Id> {
        self.result
            .fv_effects()
            .union(&self.predicates.fv_effects())
            .copied()
            .filter(|i| !self.effect_vars.contains(i))
            .collect()
    }
    pub fn safe_instantiate(&self, type_base: Id, effect_base: Id) -> bool {
        let renamed_types: BTreeSet<_> = self.type_vars.iter().map(|i| type_base + i + 1).collect();
        let renamed_effects: BTreeSet<_> = self
            .effect_vars
            .iter()
            .map(|i| effect_base + i + 1)
            .collect();
        let mut used_types = self.fv_types();
        used_types.extend(self.predicates.bound_types());
        let mut used_effects = self.fv_effects();
        used_effects.extend(self.predicates.bound_effects());
        renamed_types.len() == self.type_vars.len()
            && renamed_effects.len() == self.effect_vars.len()
            && renamed_types.is_disjoint(&used_types)
            && renamed_effects.is_disjoint(&used_effects)
    }
    pub fn generalize(ctx: &[Self], c: Constraint<P>, result: Ty) -> Self {
        let ctx_t: BTreeSet<_> = ctx.iter().flat_map(|s| s.fv_types()).collect();
        let ctx_e: BTreeSet<_> = ctx.iter().flat_map(|s| s.fv_effects()).collect();
        Self {
            type_vars: result
                .fv_types()
                .union(&c.fv_types())
                .copied()
                .filter(|i| !ctx_t.contains(i))
                .collect(),
            effect_vars: result
                .fv_effects()
                .union(&c.fv_effects())
                .copied()
                .filter(|i| !ctx_e.contains(i))
                .collect(),
            predicates: c,
            result,
        }
    }
    pub fn instantiate(&self, type_base: Id, effect_base: Id) -> (Ty, Constraint<P>) {
        let tf = |i| {
            if self.type_vars.contains(&i) {
                type_base + i + 1
            } else {
                i
            }
        };
        let ef = |i| {
            if self.effect_vars.contains(&i) {
                effect_base + i + 1
            } else {
                i
            }
        };
        (
            self.result.rename(&tf, &ef),
            self.predicates.rename(&tf, &ef),
        )
    }
}

#[derive(Clone, Debug)]
pub struct OpDecl {
    pub type_vars: BTreeSet<Id>,
    pub effect_vars: BTreeSet<Id>,
    pub input: Ty,
    pub output: Ty,
}

impl OpDecl {
    pub fn alpha_rename(&self, tf: &impl Fn(Id) -> Id, ef: &impl Fn(Id) -> Id) -> Self {
        Self {
            type_vars: self.type_vars.iter().map(|i| tf(*i)).collect(),
            effect_vars: self.effect_vars.iter().map(|i| ef(*i)).collect(),
            input: self.input.rename(tf, ef),
            output: self.output.rename(tf, ef),
        }
    }
    pub fn alpha_safe(&self, renamed: &Self) -> bool {
        let free_types: BTreeSet<_> = self
            .input
            .fv_types()
            .union(&self.output.fv_types())
            .copied()
            .filter(|i| !self.type_vars.contains(i))
            .collect();
        let free_effects: BTreeSet<_> = self
            .input
            .fv_effects()
            .union(&self.output.fv_effects())
            .copied()
            .filter(|i| !self.effect_vars.contains(i))
            .collect();
        renamed.type_vars.len() == self.type_vars.len()
            && renamed.effect_vars.len() == self.effect_vars.len()
            && renamed.type_vars.is_disjoint(&free_types)
            && renamed.effect_vars.is_disjoint(&free_effects)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr {
    Var(Id),
    Int(String),
    Bool(bool),
    Lam(Box<Self>),
    App(Box<Self>, Box<Self>),
    Let(Box<Self>, Box<Self>),
    Perform(Id, Box<Self>),
    Handle(Box<Self>, Id, Box<Self>, Box<Self>),
}
impl Expr {
    pub fn is_value(&self) -> bool {
        matches!(
            self,
            Self::Var(_) | Self::Int(_) | Self::Bool(_) | Self::Lam(_)
        )
    }
}
