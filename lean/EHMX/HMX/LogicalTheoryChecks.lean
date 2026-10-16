import EHMX.HMX.LogicalNormalization

namespace EHMX.HMX.LogicalChecks

/-- A free type algebra with variables and arrows, but no nullary constructor. -/
inductive Ty where
  | var : Nat → Ty
  | arrow : Ty → Effect → Ty → Ty

def Ty.support : Ty → Names
  | .var i => ⟨{i}, ∅⟩
  | .arrow a e b => ⟨a.support.types ∪ b.support.types,
      a.support.effects ∪ e.vars ∪ b.support.effects⟩

def Ty.subst (f : Nat → Ty) (g : Nat → Effect) : Ty → Ty
  | .var i => f i
  | .arrow a e b => .arrow (a.subst f g) (e.subst g) (b.subst f g)

private def noConstructors : TypeSignature := ⟨Empty, Empty.elim, Empty.elim⟩

private def Ty.toTerm : Ty → TypeTerm noConstructors
  | .var i => .var i
  | .arrow a e b => .arrow a.toTerm e b.toTerm

private def Ty.fromTerm : TypeTerm noConstructors → Ty
  | .var i => .var i
  | .arrow a e b => .arrow (fromTerm a) e (fromTerm b)
  | .con k _ _ => Empty.elim k

private def representation : Ty ≃ TypeTerm noConstructors where
  toFun := Ty.toTerm
  invFun := Ty.fromTerm
  left_inv := by
    intro t
    induction t with
    | var i => rfl
    | arrow a e b ha hb => simp [Ty.toTerm, Ty.fromTerm, ha, hb]
  right_inv := by
    intro t
    induction t with
    | var i => rfl
    | arrow a e b ha hb => simp [Ty.toTerm, Ty.fromTerm, ha, hb]
    | con k _ _ _ => exact Empty.elim k

def variableArrowSyntax : TypeSyntax where
  signature := noConstructors
  representation := representation
  representation_var := by intros; rfl
  representation_arrow := by intros; rfl
  representation_subst := by
    intro f g t
    change (t.subst f g).toTerm = t.toTerm.subst (fun i => (f i).toTerm) g
    induction t with
    | var i => rfl
    | arrow a e b ha hb => simp [Ty.subst, Ty.toTerm, TypeTerm.subst, ha, hb]
  representation_support := by
    intro t
    change t.support = t.toTerm.support
    induction t with
    | var i => rfl
    | arrow a e b ha hb => simp [Ty.support, Ty.toTerm, TypeTerm.support, ha, hb]
  Term := Ty
  var := Ty.var
  arrow := Ty.arrow
  subst := Ty.subst
  subst_var := by intros; rfl
  subst_arrow := by intros; rfl
  support := Ty.support
  support_var := by intros; rfl
  support_arrow := by intros; rfl
  support_subst_types := by
    intro f g t
    induction t with
    | var i => simp [Ty.subst, Ty.support]
    | arrow a e b ha hb => simp [Ty.subst, Ty.support, ha, hb, Finset.union_biUnion]
  support_subst_effects := by
    intro f g t
    induction t with
    | var i => simp [Ty.subst, Ty.support]
    | arrow a e b ha hb =>
      simp [Ty.subst, Ty.support, ha, hb, Effect.subst, Finset.union_biUnion,
        Finset.union_assoc, Finset.union_left_comm, Finset.union_comm]
  subst_eq_self := by
    intro f g t ht he
    induction t with
    | var i => exact ht i (by simp [Ty.support])
    | arrow a e b ha hb =>
      have ea := ha (fun i hi => ht i (Finset.mem_union_left _ hi))
        (fun i hi => he i (Finset.mem_union_left _ (Finset.mem_union_left _ hi)))
      have eb := hb (fun i hi => ht i (Finset.mem_union_right _ hi))
        (fun i hi => he i (Finset.mem_union_right _ hi))
      have ee := Effect.subst_eq_self e g
        (fun i hi => he i (Finset.mem_union_left _ (Finset.mem_union_right _ hi)))
      simp [Ty.subst, ea, eb, ee]
  subst_compose := by
    intro f g f' g' t
    induction t with
    | var i => rfl
    | arrow a e b ha hb => simp only [Ty.subst, ha, hb, Effect.subst_compose]

theorem no_closed_type (t : variableArrowSyntax.Term) :
    variableArrowSyntax.support t ≠ Names.empty := by
  have nonempty : t.support.types.Nonempty := by
    induction t with
    | var i => exact ⟨i, Finset.mem_singleton_self i⟩
    | arrow a e b ha _ => exact ha.mono Finset.subset_union_left
  intro h
  have : t.support.types = ∅ := congrArg Names.types h
  exact Finset.nonempty_iff_ne_empty.mp nonempty this

/-- The storage bound can contain a name even for the identity map. -/
theorem identity_bound_is_not_domain {T : TypeSyntax} (i : Nat) :
    (FiniteSubstitution.singleType T i (T.var i)).supportBound ≠ Names.empty ∧
    (FiniteSubstitution.singleType T i (T.var i)).changedNames = Names.empty := by
  constructor
  · intro h
    have := congrArg Names.types h
    simp [FiniteSubstitution.singleType, Names.empty] at this
  · rw [FiniteSubstitution.changedNames_ext
      (σ := FiniteSubstitution.singleType T i (T.var i))
      (θ := FiniteSubstitution.identity T)
      (by intro j; by_cases h : j = i <;> simp [FiniteSubstitution.singleType, FiniteSubstitution.identity, h])
      (by intro j; rfl), FiniteSubstitution.changedNames_identity]

end EHMX.HMX.LogicalChecks
