import HMX.LocallyNameless.Proofs.NamedTypingSupport

namespace HMX.Proofs

/-- A global kind-preserving permutation also renames the binder declarations. -/
def namedTyRename (p : TVar ≃ TVar) : Ty → Ty
  | .var X => .var (p X)
  | .con f ts => .con f (ts.map (namedTyRename p))

mutual
def namedConstraintRename (p : TVar ≃ TVar) : Constraint → Constraint
  | .truth => .truth
  | .falsity => .falsity
  | .atom q ts => .atom q (ts.map (namedTyRename p))
  | .conj C D => .conj (namedConstraintRename p C) (namedConstraintRename p D)
  | .exists_ A C => .exists_ (A.image p) (namedConstraintRename p C)
  | .def_ x s C => .def_ x (namedSchemeRename p s) (namedConstraintRename p C)
  | .inst x T => .inst x (namedTyRename p T)
def namedSchemeRename (p : TVar ≃ TVar) : Scheme → Scheme
  | .all A C T => .all (A.image p) (namedConstraintRename p C) (namedTyRename p T)
end

def renamedBinding (r : TVar → TVar → Prop) (p : TVar ≃ TVar) (A : Vars)
    (X Y : TVar) : Prop :=
  (X ∈ A ∧ Y = p X) ∨ (X ∉ A ∧ Y ∉ A.image p ∧ r X Y)

theorem renamedBindingBinds (p : TVar ≃ TVar) (hk : ∀ X, (p X).1 = X.1)
    (r : TVar → TVar → Prop) (A : Vars) : Binds r (renamedBinding r p A) A (A.image p) := by
  refine ⟨?_,?_,?_⟩
  · intro X hx
    refine ⟨p X,⟨Finset.mem_image.mpr ⟨X,hx,rfl⟩,(hk X).symm,Or.inl ⟨hx,rfl⟩⟩,?_⟩
    intro Y h
    rcases h.2.2 with ⟨_,h⟩ | ⟨hn,_,_⟩
    · exact h
    · exact (hn hx).elim
  · intro Y hy
    obtain ⟨X,hx,rfl⟩ := Finset.mem_image.mp hy
    refine ⟨X,⟨hx,(hk X).symm,Or.inl ⟨hx,rfl⟩⟩,?_⟩
    intro Z h
    rcases h.2.2 with ⟨_,he⟩ | ⟨hn,_,_⟩
    · exact p.injective he.symm
    · exact (hn h.1).elim
  · intro X Y
    constructor
    · rintro (⟨hx,rfl⟩ | h)
      · exact Or.inl ⟨hx,Finset.mem_image.mpr ⟨X,hx,rfl⟩,(hk X).symm,Or.inl ⟨hx,rfl⟩⟩
      · exact Or.inr h
    · rintro (⟨_,_,_,h⟩ | h)
      · exact h
      · exact Or.inr h

theorem renamedBindingOnBody (p : TVar ≃ TVar) (r : TVar → TVar → Prop) (A F : Vars)
    (h : ∀ X ∈ F \ A, r X (p X)) : ∀ X ∈ F, renamedBinding r p A X (p X) := by
  intro X hx
  by_cases ha : X ∈ A
  · exact Or.inl ⟨ha,rfl⟩
  · exact Or.inr ⟨ha,by simpa using ha,h X (Finset.mem_sdiff.mpr ⟨hx,ha⟩)⟩

theorem namedTyRenameRelated (p : TVar ≃ TVar) (T : Ty) (r : TVar → TVar → Prop)
    (h : ∀ X ∈ T.fv, r X (p X)) : Ty.Related r T (namedTyRename p T) := by
  cases T with
  | var X =>
    simp only [namedTyRename]
    exact .var (h X (by simp [Ty.fv]))
  | con f ts =>
    simp only [Ty.fv] at h
    simp only [namedTyRename]
    apply Ty.Related.con
    apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    intro U hu
    exact namedTyRenameRelated p U r (fun X hx => h X
      ((LN.Proofs.memUnionFold Ty.fv ts X).mpr ⟨U,hu,hx⟩))
termination_by sizeOf T

mutual
theorem namedConstraintRenameRelated (p : TVar ≃ TVar) (hk : ∀ X, (p X).1 = X.1)
    (C : Constraint) (r : TVar → TVar → Prop) (q : Id → Id → Prop)
    (hr : ∀ X ∈ C.fv, r X (p X)) (hq : ∀ x ∈ C.fpi, q x x) :
    Constraint.Related r q C (namedConstraintRename p C) := by
  cases C with
  | truth => exact .truth
  | falsity => exact .falsity
  | atom a ts =>
    apply Constraint.Related.atom
    apply List.forall₂_map_right_iff.mpr
    exact List.forall₂_same.mpr (fun U hu => namedTyRenameRelated p U r (fun X hx =>
      hr X ((LN.Proofs.memUnionFold Ty.fv ts X).mpr ⟨U,hu,hx⟩)))
  | conj C D =>
    exact .conj
      (namedConstraintRenameRelated p hk C r q
        (fun X hx => hr X (Finset.mem_union_left _ hx))
        (fun x hx => hq x (Finset.mem_union_left _ hx)))
      (namedConstraintRenameRelated p hk D r q
        (fun X hx => hr X (Finset.mem_union_right _ hx))
        (fun x hx => hq x (Finset.mem_union_right _ hx)))
  | exists_ A C =>
    exact .exists_ (renamedBindingBinds p hk r A)
      (namedConstraintRenameRelated p hk C _ q (renamedBindingOnBody p r A C.fv hr) hq)
  | def_ x s C =>
    apply Constraint.Related.def_ (Or.inl rfl)
      (namedSchemeRenameRelated p hk s r q
        (fun X hx => hr X (Finset.mem_union_left _ hx))
        (fun y hy => hq y (Finset.mem_union_left _ hy)))
    apply namedConstraintRenameRelated p hk C r (bindId q x x)
      (fun X hx => hr X (Finset.mem_union_right _ hx))
    intro y hy
    by_cases he : y = x
    · exact Or.inl ⟨he,he⟩
    · exact Or.inr ⟨he,he,hq y (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨he,hy⟩))⟩
  | inst x T => exact .inst (hq x (by simp [Constraint.fpi])) (namedTyRenameRelated p T r hr)
theorem namedSchemeRenameRelated (p : TVar ≃ TVar) (hk : ∀ X, (p X).1 = X.1)
    (s : Scheme) (r : TVar → TVar → Prop) (q : Id → Id → Prop)
    (hr : ∀ X ∈ s.fv, r X (p X)) (hq : ∀ x ∈ s.fpi, q x x) :
    Scheme.Related r q s (namedSchemeRename p s) := by
  cases s with
  | all A C T =>
    have hb := renamedBindingOnBody p r A (C.fv ∪ T.fv) hr
    exact .all (renamedBindingBinds p hk r A)
      (namedConstraintRenameRelated p hk C _ q (fun X hx => hb X (Finset.mem_union_left _ hx)) hq)
      (namedTyRenameRelated p T _ (fun X hx => hb X (Finset.mem_union_right _ hx)))
end

theorem namedSchemeRenameAlpha (p : TVar ≃ TVar) (hk : ∀ X, (p X).1 = X.1)
    (s : Scheme) (hf : ∀ X ∈ s.fv, p X = X) : s.Alpha (namedSchemeRename p s) :=
  namedSchemeRenameRelated p hk s Eq Eq (fun X hx => (hf X hx).symm) (fun _ _ => rfl)

theorem namedTyRenameKind (p : TVar ≃ TVar) (hk : ∀ X, (p X).1 = X.1)
    (h : Ty.HasKind S T k) : (namedTyRename p T).HasKind S k := by
  cases h with
  | var X hX => simpa only [namedTyRename,hk] using Ty.HasKind.var (p X) (by simpa [hk] using hX)
  | con f ts hf ht =>
    simp only [namedTyRename]
    apply Ty.HasKind.con _ _ hf
    apply List.forall₂_map_left_iff.mpr
    exact LN.Proofs.forall₂ImplMem ht (fun U _ k hk' => namedTyRenameKind p hk hk')
termination_by sizeOf T

mutual
theorem namedConstraintRenameWF (p : TVar ≃ TVar) (hk : ∀ X, (p X).1 = X.1)
    (C : Constraint) (h : C.WF S) : (namedConstraintRename p C).WF S := by
  cases C with
  | truth | falsity => trivial
  | atom q ts => exact ⟨h.1,List.forall₂_map_left_iff.mpr (h.2.imp (fun _ _ ht => namedTyRenameKind p hk ht))⟩
  | conj C D => exact ⟨namedConstraintRenameWF p hk C h.1,namedConstraintRenameWF p hk D h.2⟩
  | exists_ A C =>
    refine ⟨?_,namedConstraintRenameWF p hk C h.2⟩
    intro X hx
    obtain ⟨Y,hy,rfl⟩ := Finset.mem_image.mp hx
    simpa only [hk] using h.1 Y hy
  | def_ x s C => exact ⟨namedSchemeRenameWF p hk s h.1,namedConstraintRenameWF p hk C h.2⟩
  | inst x T => exact namedTyRenameKind p hk h
theorem namedSchemeRenameWF (p : TVar ≃ TVar) (hk : ∀ X, (p X).1 = X.1)
    (s : Scheme) (h : s.WF S) : (namedSchemeRename p s).WF S := by
  cases s with
  | all A C T =>
    refine ⟨?_,namedConstraintRenameWF p hk C h.2.1,namedTyRenameKind p hk h.2.2⟩
    intro X hx
    obtain ⟨Y,hy,rfl⟩ := Finset.mem_image.mp hx
    simpa only [hk] using h.1 Y hy
end

mutual
theorem namedConstraintRenameFpi (p : TVar ≃ TVar) (C : Constraint) :
    (namedConstraintRename p C).fpi = C.fpi := by
  cases C with
  | truth | falsity | atom _ _ | inst _ _ => rfl
  | conj C D => exact congrArg₂ (· ∪ ·) (namedConstraintRenameFpi p C) (namedConstraintRenameFpi p D)
  | exists_ A C => exact namedConstraintRenameFpi p C
  | def_ x s C =>
    exact congrArg₂ (· ∪ ·) (namedSchemeRenameFpi p s)
      (congrArg (fun F => F.erase x) (namedConstraintRenameFpi p C))
theorem namedSchemeRenameFpi (p : TVar ≃ TVar) (s : Scheme) :
    (namedSchemeRename p s).fpi = s.fpi := by
  cases s with
  | all A C T => exact namedConstraintRenameFpi p C
end

end HMX.Proofs
