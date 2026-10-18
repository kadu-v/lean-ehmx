import EHMX.Syntax

/-! 抽象 X における制約の意味。全称制約は kind を満たすすべての割当てを走る。
Scheme の意味はインスタンスの上方閉集合であり、全称制約とは異なる。 -/
namespace EHMX

structure Model where
  Carrier : Type
  default : Carrier
  kind : Carrier → Kind
  constructor : Symbol → List Carrier → Carrier
  predicate : Nat → List Carrier → Prop
  below : Kind → Carrier → Carrier → Prop
  effects : Carrier → Set Op

abbrev Assignment (M : Model) := TVar → M.Carrier
def Assignment.Valid (S : Signature) (M : Model) (ρ : Assignment M) : Prop :=
  ∀ X, X.1 ∈ S.kinds → M.kind (ρ X) = X.1
def KindValues (M : Model) (ks : List Kind) (vs : List M.Carrier) : Prop :=
  List.Forall₂ (fun v k => M.kind v = k) vs ks

structure GroundEnv (M : Model) where
  free : Nat → Set M.Carrier
  bound : List (Set M.Carrier)
def GroundEnv.lookup (ι : GroundEnv M) : PVar → Set M.Carrier
  | .free x => ι.free x
  | .bound i => ι.bound[i]?.getD ∅
def GroundEnv.push (ι : GroundEnv M) (s : Set M.Carrier) : GroundEnv M :=
  { ι with bound := s :: ι.bound }
def GroundEnv.bind (ι : GroundEnv M) (x : Nat) (s : Set M.Carrier) : GroundEnv M :=
  { ι with free := fun y => if y = x then s else ι.free y }
def UpperSet (M : Model) (s : Set M.Carrier) : Prop :=
  (∀ a ∈ s, M.kind a = 0) ∧
  ∀ a ∈ s, ∀ b, M.kind b = 0 → M.below 0 a b → b ∈ s
def GroundEnv.Valid (ι : GroundEnv M) : Prop :=
  (∀ x, UpperSet M (ι.free x)) ∧ ∀ s ∈ ι.bound, UpperSet M s

def Ty.eval (M : Model) (ρ : Assignment M) (bs : List M.Carrier) : Ty → M.Carrier
  | .free X => ρ X
  | .bound i => bs[i]?.getD M.default
  | .con f ts => M.constructor f (ts.map (Ty.eval M ρ bs))

def Predicate.eval (M : Model) : Predicate → List M.Carrier → Prop
  | .equal k, [a,b] => M.kind a = k ∧ M.kind b = k ∧ a = b
  | .sub k, [a,b] => M.kind a = k ∧ M.kind b = k ∧ M.below k a b
  | .other p, vs => M.predicate p vs
  | _, _ => False

mutual
def Constraint.Holds (M : Model) (ρ : Assignment M) (bs : List M.Carrier)
    (ι : GroundEnv M) : Constraint → Prop
  | .truth => True
  | .falsity => False
  | .atom p ts => p.eval M (ts.map (Ty.eval M ρ bs))
  | .conj C D => C.Holds M ρ bs ι ∧ D.Holds M ρ bs ι
  | .implies P D => (P.Holds M ρ bs ι → D.Holds M ρ bs ι)
  | .exists_ ks C => ∃ vs, KindValues M ks vs ∧ C.Holds M ρ (vs ++ bs) ι
  | .forall_ ks C => ∀ vs, KindValues M ks vs → C.Holds M ρ (vs ++ bs) ι
  | .def_ s C => C.Holds M ρ bs (ι.push (s.denote M ρ bs ι))
  | .defFree x s C => C.Holds M ρ bs (ι.bind x (s.denote M ρ bs ι))
  | .inst x T => T.eval M ρ bs ∈ ι.lookup x
def Scheme.denote (M : Model) (ρ : Assignment M) (bs : List M.Carrier)
    (ι : GroundEnv M) : Scheme → Set M.Carrier
  | .all ks C T => {v | M.kind v = 0 ∧ ∃ vs, KindValues M ks vs ∧
      C.Holds M ρ (vs ++ bs) ι ∧ M.below 0 (T.eval M ρ (vs ++ bs)) v}
end

def Entails (S : Signature) (M : Model) (Δ : List Kind) (C D : Constraint) : Prop :=
  ∀ ρ bs ι, Assignment.Valid S M ρ → KindValues M Δ bs → ι.Valid →
    C.Holds M ρ bs ι → D.Holds M ρ bs ι
def Equivalent (S : Signature) (M : Model) (Δ : List Kind) (C D : Constraint) : Prop :=
  Entails S M Δ C D ∧ Entails S M Δ D C
def Satisfiable (S : Signature) (M : Model) (Δ : List Kind) (C : Constraint) : Prop :=
  C.WF S Δ 0 ∧ ∃ ρ bs ι, Assignment.Valid S M ρ ∧ KindValues M Δ bs ∧
    ι.Valid ∧ C.Holds M ρ bs ι

/-- Algebraic assumptions only: no typing, generation, or safety theorem is a field. -/
structure EffectFramework (S : Signature) (M : Model) : Prop where
  signature : S.WF
  inhabited : ∀ k ∈ S.kinds, ∃ v, M.kind v = k
  constructorKind : ∀ f, f.Declared S → ∀ vs, KindValues M (f.parameters S) vs →
    M.kind (M.constructor f vs) = f.result S
  belowRefl : ∀ k ∈ S.kinds, ∀ a, M.kind a = k → M.below k a a
  belowTrans : ∀ k ∈ S.kinds, ∀ a b c,
    M.kind a = k → M.kind b = k → M.kind c = k →
    M.below k a b → M.below k b c → M.below k a c
  belowAntisymm : ∀ k ∈ S.kinds, ∀ a b,
    M.kind a = k → M.kind b = k → M.below k a b → M.below k b a → a = b
  effectOrder : ∀ a b, M.kind a = 1 → M.kind b = 1 →
    (M.below 1 a b ↔ M.effects a ⊆ M.effects b)
  effectsFinite : ∀ a, M.kind a = 1 → (M.effects a).Finite
  emptyEffect : M.effects (M.constructor .empty []) = ∅
  singletonEffect : ∀ op, M.effects (M.constructor (.operation op) []) = {op}
  unionEffect : ∀ a b, M.kind a = 1 → M.kind b = 1 →
    M.effects (M.constructor .union [a,b]) = M.effects a ∪ M.effects b
  arrowOrder : ∀ a ε b a' ε' b',
    M.kind a = 0 → M.kind ε = 1 → M.kind b = 0 →
    M.kind a' = 0 → M.kind ε' = 1 → M.kind b' = 0 →
    (M.below 0 (M.constructor .arrow [a,ε,b]) (M.constructor .arrow [a',ε',b']) ↔
      M.below 0 a' a ∧ M.below 1 ε ε' ∧ M.below 0 b b')

/-- Constraint safety requires excluding a non-function constructor below an arrow. -/
def ArrowSeparated (S : Signature) (M : Model) : Prop :=
  ∀ f ∈ S.constructors, S.result f = 0 → ∀ vs a ε b,
    KindValues M (S.parameters f) vs → M.kind a = 0 → M.kind ε = 1 → M.kind b = 0 →
    ¬ M.below 0 (M.constructor (.other f) vs) (M.constructor .arrow [a,ε,b])

def Scheme.instanceConstraint (s : Scheme) (U : Ty) : Constraint :=
  match s with
  | .all ks C T => .exists_ ks (.conj C (.le 0 T (U.shift ks.length 0)))

end EHMX
