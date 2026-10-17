import HMX.Semantics
import HMX.Binding

namespace HMX

/-- p.410: a context may have zero, one, or several holes. -/
inductive Context where
  | hole
  | fixed : Constraint → Context
  | conj : Context → Context → Context
  | exists_ : Vars → Context → Context
  | define : Id → Vars → Context → Ty → Context → Context

def Context.plug (C : Constraint) : Context → Constraint
  | .hole => C
  | .fixed D => D
  | .conj K L => .conj (K.plug C) (L.plug C)
  | .exists_ A K => .exists_ A (K.plug C)
  | .define x A K T L => .def_ x (.all A (K.plug C) T) (L.plug C)

def Context.hasHole : Context → Bool
  | .hole => true
  | .fixed _ => false
  | .conj K L | .define _ _ K _ L => K.hasHole || L.hasHole
  | .exists_ _ K => K.hasHole

def Context.dtv : Context → Vars
  | .hole | .fixed _ => ∅
  | .conj K L => K.dtv ∪ L.dtv
  | .exists_ A K => K.dtv ∪ if K.hasHole then A else ∅
  | .define _ A K _ L => K.dtv ∪ L.dtv ∪ if K.hasHole then A else ∅

def Context.dpi : Context → Finset Id
  | .hole | .fixed _ => ∅
  | .conj K L => K.dpi ∪ L.dpi
  | .exists_ _ K => K.dpi
  | .define x _ K _ L => K.dpi ∪ L.dpi ∪ if L.hasHole then {x} else ∅

/-- The grammar in use after p.420 replaces primitive def by derived let. -/
inductive LetContext where
  | hole
  | fixed : Constraint → LetContext
  | conj : LetContext → LetContext → LetContext
  | exists_ : Vars → LetContext → LetContext
  | let_ : Id → Vars → LetContext → Ty → LetContext → LetContext

def LetContext.plug (C : Constraint) : LetContext → Constraint
  | .hole => C
  | .fixed D => D
  | .conj K L => .conj (K.plug C) (L.plug C)
  | .exists_ A K => .exists_ A (K.plug C)
  | .let_ x A K T L => .let_ x (.all A (K.plug C) T) (L.plug C)

def theorem10_2_13_congruence (S : Signature) (M : Model) : Prop :=
  M.Requirements S → ∀ (K : Context) C D,
    C.WF S → D.WF S → (K.plug C).WF S → (K.plug D).WF S →
    Entails S M C D → Entails S M (K.plug C) (K.plug D)

/-- Common implicit kind-correctness of the two sides of a printed law. -/
def EquationLaw (S : Signature) (M : Model) (C D : Constraint) : Prop :=
  C.WF S → D.WF S → Equivalent S M C D

abbrev Equations := List (TVar × Ty)
def Equations.dom (es : Equations) : Vars := (es.map Prod.fst).toFinset
def Equations.range (es : Equations) : Vars := (es.map (fun p => p.2.fv)).foldr (· ∪ ·) ∅
def Equations.WF (S : Signature) (es : Equations) : Prop :=
  (es.map Prod.fst).Nodup ∧ ∀ p ∈ es, p.2.HasKind S p.1.1

def Equations.constraint (es : Equations) : Constraint :=
  es.foldr (fun p C => .conj (.eq p.1.1 (.var p.1) p.2) C) .truth

def Equations.substitution (es : Equations) : Subst :=
  fun X => match es.find? (fun p => p.1 == X) with
    | some p => p.2
    | none => .var X

/-- Figure 10-6: separate declarations retain every printed side condition. -/
def cAnd (S : Signature) (M : Model) : Prop :=
  ∀ C D, EquationLaw S M (.conj C D) (.conj D C)
def cAndAnd (S : Signature) (M : Model) : Prop :=
  ∀ C D E, EquationLaw S M (.conj (.conj C D) E) (.conj C (.conj D E))
def cDup (S : Signature) (M : Model) : Prop :=
  ∀ C D, Entails S M C D → EquationLaw S M (.conj C D) C
def cExEx (S : Signature) (M : Model) : Prop :=
  ∀ A B C, EquationLaw S M (.exists_ A (.exists_ B C)) (.exists_ (A ∪ B) C)
def cExStar (S : Signature) (M : Model) : Prop :=
  ∀ A (C : Constraint), Disjoint A C.fv → EquationLaw S M (.exists_ A C) C
def cExAnd (S : Signature) (M : Model) : Prop :=
  ∀ A C (D : Constraint), Disjoint A D.fv →
    EquationLaw S M (.conj (.exists_ A C) D) (.exists_ A (.conj C D))
def cExTrans (S : Signature) (M : Model) : Prop :=
  ∀ (s : Scheme) Z T, Z.1 = 0 → Z ∉ s.fv ∪ T.fv →
    s.InstanceFresh (.var Z) → s.InstanceFresh T →
    EquationLaw S M (.exists_ {Z} (.conj (s.instanceConstraint (.var Z)) (.le 0 (.var Z) T)))
      (s.instanceConstraint T)
def cInId (S : Signature) (M : Model) : Prop :=
  ∀ (K : Context) x (s : Scheme) T, x ∉ K.dpi → Disjoint K.dtv s.fv →
    Disjoint ({x} ∪ K.dpi) s.fpi → s.InstanceFresh T →
    EquationLaw S M (.let_ x s (K.plug (.inst x T))) (.let_ x s (K.plug (s.instanceConstraint T)))
def cInStar (S : Signature) (M : Model) : Prop :=
  ∀ (Γ : Env) (C : Constraint), Disjoint Γ.dpi C.fpi →
    EquationLaw S M (Γ.letIn C) (.conj Γ.exists_ C)
def cInAnd (S : Signature) (M : Model) : Prop :=
  ∀ (Γ : Env) C D, EquationLaw S M (Γ.letIn (.conj C D)) (.conj (Γ.letIn C) (Γ.letIn D))
def cInAndStar (S : Signature) (M : Model) : Prop :=
  ∀ (Γ : Env) C (D : Constraint), Disjoint Γ.dpi D.fpi →
    EquationLaw S M (Γ.letIn (.conj C D)) (.conj (Γ.letIn C) D)
def cInEx (S : Signature) (M : Model) : Prop :=
  ∀ (Γ : Env) A C, Disjoint A Γ.fv → EquationLaw S M (Γ.letIn (.exists_ A C)) (.exists_ A (Γ.letIn C))
def cLetLet (S : Signature) (M : Model) : Prop :=
  ∀ (Γ Δ : Env) C, Disjoint Γ.dpi Δ.dpi → Disjoint Δ.dpi Γ.fpi → Disjoint Γ.dpi Δ.fpi →
    EquationLaw S M ((Γ ++ Δ).letIn C) ((Δ ++ Γ).letIn C)
def cLetAnd (S : Signature) (M : Model) : Prop :=
  ∀ x A (C : Constraint) D T E, Disjoint A C.fv →
    EquationLaw S M (.let_ x (.all A (.conj C D) T) E) (.conj C (.let_ x (.all A D T) E))
def cLetDup (S : Signature) (M : Model) : Prop :=
  ∀ (Γ : Env) x A C T D, Disjoint A Γ.fv → Disjoint Γ.dpi Γ.fpi →
    EquationLaw S M ((Γ ++ [(x, Scheme.all A C T)]).letIn D)
      ((Γ ++ [(x, Scheme.all A (Γ.letIn C) T)]).letIn D)
def cLetEx (S : Signature) (M : Model) : Prop :=
  ∀ x A B C (T : Ty) D, Disjoint B T.fv →
    EquationLaw S M (.let_ x (.all A (.exists_ B C) T) D) (.let_ x (.all (A ∪ B) C T) D)
def cLetAll (S : Signature) (M : Model) : Prop :=
  ∀ x A B C T (D : Constraint), Disjoint B D.fv → Determines S M (.exists_ A C) B →
    EquationLaw S M (.let_ x (.all (A ∪ B) C T) D) (.exists_ B (.let_ x (.all A C T) D))
def cLetSub (S : Signature) (M : Model) : Prop :=
  ∀ X x (T : Ty) (C : Constraint), X.1 = 0 → X ∉ T.fv ∪ C.fv →
    EquationLaw S M (.exists_ {X} (.conj (.le 0 T (.var X)) (.let_ x (.mono (.var X)) C)))
      (.let_ x (.mono T) C)
def cEq (S : Signature) (M : Model) : Prop :=
  ∀ (es : Equations) C D, es.WF S → C.Substitutes es.substitution D →
    EquationLaw S M (.conj es.constraint D) (.conj es.constraint C)
def cName (S : Signature) (M : Model) : Prop :=
  ∀ es : Equations, es.WF S → Disjoint es.dom es.range →
    EquationLaw S M .truth (.exists_ es.dom es.constraint)
def cNameEq (S : Signature) (M : Model) : Prop :=
  ∀ (es : Equations) C D, es.WF S → Disjoint es.dom es.range →
    C.Substitutes es.substitution D → EquationLaw S M D (.exists_ es.dom (.conj es.constraint C))

def theorem10_2_15 (S : Signature) (M : Model) : Prop :=
  M.Requirements S →
  cAnd S M ∧ cAndAnd S M ∧ cDup S M ∧ cExEx S M ∧ cExStar S M ∧ cExAnd S M ∧
  cExTrans S M ∧ cInId S M ∧ cInStar S M ∧ cInAnd S M ∧ cInAndStar S M ∧ cInEx S M ∧
  cLetLet S M ∧ cLetAnd S M ∧ cLetDup S M ∧ cLetEx S M ∧ cLetAll S M ∧ cLetSub S M ∧
  cEq S M ∧ cName S M ∧ cNameEq S M

/-- Lemma 10.2.17, literally quantified over the printed context convention.
The zero-hole case is NOT silently removed: see audit ambiguity A-03. -/
def lemma10_2_17 (S : Signature) (M : Model) : Prop :=
  M.Requirements S → ∀ K : LetContext, EquationLaw S M (K.plug .falsity) .falsity

end HMX
