import EHMX.HMX.ConstraintSyntax

namespace EHMX.HMX

/-- Definition 7 over a presented constraint language. Substitution is
constructed on predicate arguments and syntax; it is not an independently
chosen semantic action. No ground interpretation is selected. -/
structure TermConstraintTheory (T : TypeSyntax) extends ConstraintTheory where
  language : ConstraintPresentation T toConstraintTheory
  represents : ∀ c, toConstraintTheory.Equivalent (language.denote (language.encode c)) c
  representation_support : ∀ c, (language.encode c).support.Subset (support c)
  diagonal_refl : ∀ i, Entails top (language.atom (.typeEq (T.var i) (T.var i)))
  diagonal_symm : ∀ i j, Entails (language.atom (.typeEq (T.var i) (T.var j)))
    (language.atom (.typeEq (T.var j) (T.var i)))
  diagonal_trans : ∀ i j k, Entails
    (and (language.atom (.typeEq (T.var i) (T.var j)))
      (language.atom (.typeEq (T.var j) (T.var k))))
    (language.atom (.typeEq (T.var i) (T.var k)))
  /-- The distinct-variable convention in D4 is explicit. Without it, setting
  i=j would collapse existential projection to the identity. -/
  diagonal_elim : ∀ i j c, i ≠ j → Entails
    (and (language.atom (.typeEq (T.var i) (T.var j)))
      (existsNames ⟨{i}, ∅⟩ (and c (language.atom (.typeEq (T.var i) (T.var j)))))) c
  congr : ∀ i a b t, Entails (language.atom (.typeEq a b))
    (language.atom (.typeEq ((FiniteSubstitution.singleType T i a).apply t)
      ((FiniteSubstitution.singleType T i b).apply t)))
  /-- D6 is imposed on predicates, not postulated for arbitrary formulas. -/
  predicate_project : ∀ i t (p : ConstraintAtom T language.predicates),
    i ∉ (T.support t).types → toConstraintTheory.Equivalent
      (language.atom (p.subst (FiniteSubstitution.singleType T i t)))
      (existsNames ⟨{i}, ∅⟩ (and (language.atom p) (language.atom (.typeEq (T.var i) t))))

namespace TermConstraintTheory
variable {T : TypeSyntax} (X : TermConstraintTheory T)
abbrev eq (a b : T.Term) := X.language.atom (.typeEq a b)
abbrev subst (s : FiniteSubstitution T) := X.language.subst s

/-- Derived substitution laws are future proof obligations, not extra fields
of the constraint theory or premises of the four reconstruction statements. -/
def SubstitutionRespectsEquivalence : Prop :=
  ∀ s c d, X.toConstraintTheory.Equivalent c d →
    X.toConstraintTheory.Equivalent (X.subst s c) (X.subst s d)
def SubstitutionPreservesEntailment : Prop :=
  ∀ s c d, X.Entails c d → X.Entails (X.subst s c) (X.subst s d)
def SubstitutionPresentationIndependent : Prop :=
  ∀ s c, X.toConstraintTheory.Equivalent
    (X.subst s (X.language.denote c)) (X.language.denote (c.subst s))
end TermConstraintTheory
end EHMX.HMX
