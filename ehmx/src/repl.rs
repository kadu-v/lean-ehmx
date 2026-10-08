use crate::core::*;
use crate::infer::{self, Supply};
use crate::parse::{NamedExpr, NamedTy, OpAst, Parser, SchemeAst};
use std::collections::BTreeMap;

#[derive(Clone)]
pub struct Session {
    ops: BTreeMap<String, Id>,
    op_names: BTreeMap<Id, String>,
    sig: BTreeMap<Id, OpDecl>,
    bindings: Vec<(String, Scheme<ClassPred>)>,
    assumptions: Vec<ClassPred>,
    free_types: BTreeMap<String, Id>,
    free_effects: BTreeMap<String, Id>,
    next_ty: Id,
    next_eff: Id,
    next_op: Id,
}
impl Default for Session {
    fn default() -> Self {
        let mut ops = BTreeMap::new();
        ops.insert("ping".into(), 0);
        let mut op_names = BTreeMap::new();
        op_names.insert(0, "ping".into());
        let mut sig = BTreeMap::new();
        sig.insert(
            0,
            OpDecl {
                type_vars: [0].into_iter().collect(),
                effect_vars: Default::default(),
                input: Ty::Var(0),
                output: Ty::Var(0),
            },
        );
        Self {
            ops,
            op_names,
            sig,
            bindings: vec![],
            assumptions: vec![],
            free_types: BTreeMap::new(),
            free_effects: BTreeMap::new(),
            next_ty: 1,
            next_eff: 0,
            next_op: 1,
        }
    }
}
impl Session {
    pub fn new() -> Self {
        Self::default()
    }
    fn type_id(
        &mut self,
        name: &str,
        local: &BTreeMap<String, Id>,
        allow_free: bool,
    ) -> Result<Id, String> {
        if let Some(i) = local.get(name) {
            return Ok(*i);
        }
        if !allow_free {
            return Err(format!(
                "unbound type variable '{name}' in operation signature"
            ));
        }
        if let Some(i) = self.free_types.get(name) {
            return Ok(*i);
        }
        let i = self.next_ty;
        self.next_ty += 1;
        self.free_types.insert(name.into(), i);
        Ok(i)
    }
    fn effect_id(
        &mut self,
        name: &str,
        local: &BTreeMap<String, Id>,
        allow_free: bool,
    ) -> Result<Id, String> {
        if let Some(i) = local.get(name) {
            return Ok(*i);
        }
        if !allow_free {
            return Err(format!(
                "unbound effect variable '{name}' in operation signature"
            ));
        }
        if let Some(i) = self.free_effects.get(name) {
            return Ok(*i);
        }
        let i = self.next_eff;
        self.next_eff += 1;
        self.free_effects.insert(name.into(), i);
        Ok(i)
    }
    fn lower_ty(
        &mut self,
        t: &NamedTy,
        tv: &BTreeMap<String, Id>,
        ev: &BTreeMap<String, Id>,
        allow_free: bool,
    ) -> Result<Ty, String> {
        Ok(match t {
            NamedTy::Int => Ty::Base(BaseTy::Int),
            NamedTy::Bool => Ty::Base(BaseTy::Bool),
            NamedTy::Var(n) => {
                if n.starts_with('?') {
                    return Err("effect variable used as a type".into());
                }
                Ty::Var(self.type_id(n, tv, allow_free)?)
            }
            NamedTy::Arr(a, items, b) => {
                let left = self.lower_ty(a, tv, ev, allow_free)?;
                let mut effect = Effect::default();
                for item in items {
                    if item.starts_with('?') {
                        effect.vars.insert(self.effect_id(item, ev, allow_free)?);
                    } else {
                        effect.labels.insert(
                            *self
                                .ops
                                .get(item)
                                .ok_or_else(|| format!("unknown operation '{item}'"))?,
                        );
                    }
                }
                Ty::Arr(
                    Box::new(left),
                    effect,
                    Box::new(self.lower_ty(b, tv, ev, allow_free)?),
                )
            }
        })
    }
    fn bound_ids(
        &mut self,
        bound: &[String],
    ) -> Result<(BTreeMap<String, Id>, BTreeMap<String, Id>), String> {
        let mut tv = BTreeMap::new();
        let mut ev = BTreeMap::new();
        for n in bound {
            if n.starts_with('?') {
                if ev.contains_key(n) {
                    return Err(format!("duplicate binder '{n}'"));
                }
                ev.insert(n.clone(), self.next_eff);
                self.next_eff += 1;
            } else {
                if tv.contains_key(n) || n == "Int" || n == "Bool" {
                    return Err(format!("invalid or duplicate binder '{n}'"));
                }
                tv.insert(n.clone(), self.next_ty);
                self.next_ty += 1;
            }
        }
        Ok((tv, ev))
    }
    fn lower_pred(
        &mut self,
        p: &(String, NamedTy),
        tv: &BTreeMap<String, Id>,
        ev: &BTreeMap<String, Id>,
        allow_free: bool,
    ) -> Result<ClassPred, String> {
        let ty = self.lower_ty(&p.1, tv, ev, allow_free)?;
        match p.0.as_str() {
            "Eq" => Ok(ClassPred::Eq(ty)),
            "Show" => Ok(ClassPred::Show(ty)),
            _ => Err(format!("unknown class '{}'", p.0)),
        }
    }
    fn lower_scheme(&mut self, a: SchemeAst) -> Result<Scheme<ClassPred>, String> {
        let (tv, ev) = self.bound_ids(&a.bound)?;
        let mut c = Constraint::Top;
        for p in &a.preds {
            c = Constraint::and(c, Constraint::Pred(self.lower_pred(p, &tv, &ev, true)?));
        }
        let result = self.lower_ty(&a.ty, &tv, &ev, true)?;
        Ok(Scheme {
            type_vars: tv.values().copied().collect(),
            effect_vars: ev.values().copied().collect(),
            predicates: c,
            result,
        })
    }
    fn lower_op(&mut self, a: OpAst) -> Result<OpDecl, String> {
        let (tv, ev) = self.bound_ids(&a.bound)?;
        let input = self.lower_ty(&a.input, &tv, &ev, false)?;
        let output = self.lower_ty(&a.output, &tv, &ev, false)?;
        Ok(OpDecl {
            type_vars: tv.values().copied().collect(),
            effect_vars: ev.values().copied().collect(),
            input,
            output,
        })
    }
    fn lower_expr(&self, e: &NamedExpr, names: &[String]) -> Result<Expr, String> {
        Ok(match e {
            NamedExpr::Var(n) => Expr::Var(
                names
                    .iter()
                    .position(|x| x == n)
                    .ok_or_else(|| format!("unbound variable '{n}'"))?,
            ),
            NamedExpr::Int(n) => Expr::Int(n.clone()),
            NamedExpr::Bool(b) => Expr::Bool(*b),
            NamedExpr::Lam(x, body) => {
                let mut ns = vec![x.clone()];
                ns.extend_from_slice(names);
                Expr::Lam(Box::new(self.lower_expr(body, &ns)?))
            }
            NamedExpr::App(f, x) => Expr::App(
                Box::new(self.lower_expr(f, names)?),
                Box::new(self.lower_expr(x, names)?),
            ),
            NamedExpr::Let(x, e1, e2) => {
                let mut ns = vec![x.clone()];
                ns.extend_from_slice(names);
                Expr::Let(
                    Box::new(self.lower_expr(e1, names)?),
                    Box::new(self.lower_expr(e2, &ns)?),
                )
            }
            NamedExpr::Perform(op, arg) => Expr::Perform(
                *self
                    .ops
                    .get(op)
                    .ok_or_else(|| format!("unknown operation '{op}'"))?,
                Box::new(self.lower_expr(arg, names)?),
            ),
            NamedExpr::Handle(body, op, r, ret, x, k, clause) => {
                let id = *self
                    .ops
                    .get(op)
                    .ok_or_else(|| format!("unknown operation '{op}'"))?;
                let mut rn = vec![r.clone()];
                rn.extend_from_slice(names);
                let mut cn = vec![k.clone(), x.clone()];
                cn.extend_from_slice(names);
                Expr::Handle(
                    Box::new(self.lower_expr(body, names)?),
                    id,
                    Box::new(self.lower_expr(ret, &rn)?),
                    Box::new(self.lower_expr(clause, &cn)?),
                )
            }
        })
    }
    pub fn process(&mut self, line: &str) -> Result<String, String> {
        let mut copy = self.clone();
        let result = copy.process_inner(line)?;
        *self = copy;
        Ok(result)
    }
    fn process_inner(&mut self, line: &str) -> Result<String, String> {
        let line = line.trim();
        if line.is_empty() {
            return Ok(String::new());
        }
        match line {
            ":quit"|":q"=>return Ok("quit".into()),
            ":help"=>return Ok("expr | :infer expr | :op name : forall a. a -> a | :bind name : forall a. Eq a => a -{}-> a | :assume Eq Int | :env | :reset | :quit\nBuilt-in operation: ping : forall a. a -> a\nEffect variables begin with ?, e.g. forall a ?e. a -{?e}-> a\n↑/↓: input history; Ctrl-C: clear input; Ctrl-D: exit".into()),
            ":reset"=>{*self=Self::new();return Ok("environment reset".into())},
            ":env"=>return Ok(self.environment()),
            _=>{}
        }
        if let Some(rest) = line.strip_prefix(":op ") {
            let (name, sig) = rest
                .split_once(':')
                .ok_or("expected :op name : signature")?;
            let name = name.trim();
            if !valid_decl_name(name) {
                return Err("invalid operation name".into());
            }
            if self.ops.contains_key(name) {
                return Err(format!("operation '{name}' already declared"));
            }
            let mut parser = Parser::new(sig)?;
            let ast = parser.parse_op()?;
            parser.finish()?;
            let decl = self.lower_op(ast)?;
            let id = self.next_op;
            self.next_op += 1;
            self.ops.insert(name.into(), id);
            self.op_names.insert(id, name.into());
            self.sig.insert(id, decl);
            return Ok(format!("declared operation {name}"));
        }
        if let Some(rest) = line.strip_prefix(":bind ") {
            let (name, sig) = rest.split_once(':').ok_or("expected :bind name : scheme")?;
            let name = name.trim();
            if !valid_decl_name(name) {
                return Err("invalid binding name".into());
            }
            let mut parser = Parser::new(sig)?;
            let ast = parser.parse_scheme()?;
            parser.finish()?;
            let scheme = self.lower_scheme(ast)?;
            self.bindings.insert(0, (name.into(), scheme));
            return Ok(format!("bound {name}"));
        }
        if let Some(rest) = line.strip_prefix(":assume ") {
            let mut parser = Parser::new(rest)?;
            let ast = parser.parse_predicate()?;
            parser.finish()?;
            let pred = self.lower_pred(&ast, &BTreeMap::new(), &BTreeMap::new(), true)?;
            self.assumptions.insert(0, pred);
            return Ok("assumption added".into());
        }
        let src = line.strip_prefix(":infer ").unwrap_or(line);
        let mut parser = Parser::new(src)?;
        let ast = parser.parse_expr()?;
        parser.finish()?;
        let names: Vec<_> = self.bindings.iter().map(|(n, _)| n.clone()).collect();
        let e = self.lower_expr(&ast, &names)?;
        let ctx: Vec<_> = self.bindings.iter().map(|(_, s)| s.clone()).collect();
        let supply = Supply {
            types: self.next_ty + 1,
            effects: self.next_eff + 1,
        };
        let r = infer::infer_qualified(&self.sig, &ctx, &e, supply, &self.assumptions)
            .map_err(|e| format!("inference failed: {e:?}"))?;
        Ok(format!(
            "type: {}\neffect: {}\nconstraints: {}",
            self.show_ty(&r.ty),
            self.show_effect(&r.effect),
            self.show_constraint(&r.constraints)
        ))
    }
    fn environment(&self) -> String {
        let mut lines = Vec::new();
        for (n, d) in &self.ops {
            let op = &self.sig[d];
            lines.push(format!(
                "op {n}: {} -> {}",
                self.show_ty(&op.input),
                self.show_ty(&op.output)
            ));
        }
        for (n, s) in &self.bindings {
            lines.push(format!("{n}: {}", self.show_ty(&s.result)));
        }
        for p in &self.assumptions {
            lines.push(format!("assume {}", self.show_pred(p)));
        }
        if lines.is_empty() {
            "empty environment".into()
        } else {
            lines.join("\n")
        }
    }
    fn show_ty(&self, t: &Ty) -> String {
        match t {
            Ty::Var(i) => format!("α{i}"),
            Ty::Base(BaseTy::Int) => "Int".into(),
            Ty::Base(BaseTy::Bool) => "Bool".into(),
            Ty::Arr(a, e, b) => format!(
                "({} -{}-> {})",
                self.show_ty(a),
                self.show_effect(e),
                self.show_ty(b)
            ),
        }
    }
    fn show_effect(&self, e: &Effect) -> String {
        let mut xs: Vec<_> = e
            .labels
            .iter()
            .map(|i| {
                self.op_names
                    .get(i)
                    .cloned()
                    .unwrap_or_else(|| format!("op{i}"))
            })
            .collect();
        xs.extend(e.vars.iter().map(|i| format!("μ{i}")));
        if xs.is_empty() {
            "{}".into()
        } else {
            format!("{{{}}}", xs.join(", "))
        }
    }
    fn show_pred(&self, p: &ClassPred) -> String {
        match p {
            ClassPred::Eq(t) => format!("Eq {}", self.show_ty(t)),
            ClassPred::Show(t) => format!("Show {}", self.show_ty(t)),
        }
    }
    fn show_constraint(&self, c: &Constraint<ClassPred>) -> String {
        use Constraint as C;
        match c {
            C::Top => "true".into(),
            C::And(a, b) => {
                let a = self.show_constraint(a);
                let b = self.show_constraint(b);
                match (a.as_str(), b.as_str()) {
                    ("true", _) => b,
                    (_, "true") => a,
                    _ => format!("({a} ∧ {b})"),
                }
            }
            C::TypeEq(a, b) => format!("{} = {}", self.show_ty(a), self.show_ty(b)),
            C::EffectLe(a, b) => format!("{} ⊆ {}", self.show_effect(a), self.show_effect(b)),
            C::Lacks(op, e) => format!(
                "{} ∉ {}",
                self.op_names.get(op).map(String::as_str).unwrap_or("?"),
                self.show_effect(e)
            ),
            C::Pred(p) => self.show_pred(p),
            C::AllTy(i, c) => format!("∀α{i}. {}", self.show_constraint(c)),
            C::AllEff(i, c) => format!("∀μ{i}. {}", self.show_constraint(c)),
        }
    }
}
fn valid_decl_name(s: &str) -> bool {
    let mut chars = s.chars();
    matches!(chars.next(),Some(c) if c.is_ascii_alphabetic() || c=='_')
        && chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
        && !matches!(
            s,
            "let" | "in" | "with" | "return" | "handle" | "perform" | "true" | "false"
        )
}
