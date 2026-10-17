import HMX.LocallyNameless.Semantics
import HMX.Typing

namespace HMX.LN

def JudgmentWF (S : Signature) (C : Constraint) (Γ : Env) (t : Expr) (s : Scheme) : Prop :=
  C.WF S [] 0 ∧ Γ.WF S ∧ t.LCAt 0 ∧ s.WF S [] 0 ∧
  C.fpi = ∅ ∧ Γ.fpi = ∅ ∧ s.fpi = ∅

/-- Figure 10-7 with cofinite opening of term binders. No freshness property is
assumed globally: each binder rule supplies a finite exclusion set. -/
inductive Derivation (S : Signature) (M : Model) :
    Constraint → Env → Expr → Scheme → Shape → Prop where
  | var : JudgmentWF S C Γ (.ident (.free x)) s → lookup Γ x = some s →
      Entails S M C s.exists_ → Derivation S M C Γ (.ident (.free x)) s (.node 0 [])
  | abs (L : Finset Nat) : JudgmentWF S C Γ (.lam t) (.mono (.arrow T U)) →
      (∀ z, z ∉ L → Derivation S M C (Γ ++ [(.var z, .mono T)])
        (Expr.openAt 0 (.ident (.free (.var z))) t) (.mono U) d) →
      Derivation S M C Γ (.lam t) (.mono (.arrow T U)) (.node 1 [d])
  | app : JudgmentWF S C Γ (.app t u) (.mono U) →
      Derivation S M C Γ t (.mono (.arrow T U)) d → Derivation S M C Γ u (.mono T) e →
      Derivation S M C Γ (.app t u) (.mono U) (.node 2 [d,e])
  | letE (L : Finset Nat) : JudgmentWF S C Γ (.letE t u) (.mono T) → Derivation S M C Γ t s d →
      (∀ z, z ∉ L → Derivation S M C (Γ ++ [(.var z, s)])
        (Expr.openAt 0 (.ident (.free (.var z))) u) (.mono T) e) →
      Derivation S M C Γ (.letE t u) (.mono T) (.node 3 [d,e])
  | gen : JudgmentWF S (.conj C (D.existsNames xs)) Γ t (Scheme.generalize xs D T) →
      xs.Nodup → Disjoint xs.toFinset (C.fv ∪ Γ.fv) →
      Derivation S M (.conj C D) Γ t (.mono T) d →
      Derivation S M (.conj C (D.existsNames xs)) Γ t (Scheme.generalize xs D T) (.node 4 [d])
  | inst : JudgmentWF S (.conj C D) Γ t (.mono T) → xs.Nodup →
      Derivation S M C Γ t (Scheme.generalize xs D T) d →
      Derivation S M (.conj C D) Γ t (.mono T) (.node 5 [d])
  | sub : JudgmentWF S C Γ t (.mono U) → Derivation S M C Γ t (.mono T) d →
      Entails S M C (.le 0 T U) → Derivation S M C Γ t (.mono U) (.node 6 [d])
  | exists_ : JudgmentWF S (C.existsNames xs) Γ t s → xs.Nodup →
      (∀ X ∈ xs, X.1 ∈ S.kinds) → Disjoint xs.toFinset (Γ.fv ∪ s.fv) →
      Derivation S M C Γ t s d → Derivation S M (C.existsNames xs) Γ t s (.node 7 [d])
  | convert : JudgmentWF S D Δ t r → Derivation S M C Γ t s d →
      Equivalent S M C D → Γ.BinderEq Δ → s.BinderEq r → Derivation S M D Δ t r d

def Typing (S : Signature) (M : Model) (C : Constraint) (Γ : Env) (t : Expr) (s : Scheme) : Prop :=
  ∃ d, Derivation S M C Γ t s d

/-- Figure 10-8, using the same cofinite convention as Derivation. -/
inductive AlternateTyping (S : Signature) (M : Model) : Constraint → Env → Expr → Ty → Prop where
  | varInst : JudgmentWF S (.conj C D) Γ (.ident (.free x)) (.mono T) →
      xs.Nodup → lookup Γ x = some (Scheme.generalize xs D T) →
      AlternateTyping S M (.conj C D) Γ (.ident (.free x)) T
  | abs (L : Finset Nat) : JudgmentWF S C Γ (.lam t) (.mono (.arrow T U)) →
      (∀ z, z ∉ L → AlternateTyping S M C (Γ ++ [(.var z, .mono T)])
        (Expr.openAt 0 (.ident (.free (.var z))) t) U) →
      AlternateTyping S M C Γ (.lam t) (.arrow T U)
  | app : JudgmentWF S C Γ (.app t u) (.mono U) →
      AlternateTyping S M C Γ t (.arrow T U) → AlternateTyping S M C Γ u T →
      AlternateTyping S M C Γ (.app t u) U
  | letGen (L : Finset Nat) : JudgmentWF S (.conj C (D.existsNames xs)) Γ (.letE t u) (.mono U) →
      xs.Nodup → Disjoint xs.toFinset (C.fv ∪ Γ.fv) →
      AlternateTyping S M (.conj C D) Γ t T →
      (∀ z, z ∉ L → AlternateTyping S M (.conj C (D.existsNames xs))
        (Γ ++ [(.var z, Scheme.generalize xs D T)]) (Expr.openAt 0 (.ident (.free (.var z))) u) U) →
      AlternateTyping S M (.conj C (D.existsNames xs)) Γ (.letE t u) U
  | sub : JudgmentWF S C Γ t (.mono U) → AlternateTyping S M C Γ t T →
      Entails S M C (.le 0 T U) → AlternateTyping S M C Γ t U
  | exists_ : JudgmentWF S (C.existsNames xs) Γ t (.mono T) → xs.Nodup →
      (∀ X ∈ xs, X.1 ∈ S.kinds) → Disjoint xs.toFinset (Γ.fv ∪ T.fv) →
      AlternateTyping S M C Γ t T → AlternateTyping S M (C.existsNames xs) Γ t T
  | convert : JudgmentWF S D Δ t (.mono T) → AlternateTyping S M C Γ t T →
      Equivalent S M C D → Γ.BinderEq Δ → AlternateTyping S M D Δ t T

end HMX.LN
