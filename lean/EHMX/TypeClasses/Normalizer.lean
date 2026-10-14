import EHMX.TypeClasses.Projection

namespace EHMX.TypeClasses
open HMX

theorem clause_empty {K} (E : ClassEnv K) (a c v) :
    Formula.Holds E (.clause a Names.empty c) v ↔
      ∀ w, w.AgreeOutside v a → Formula.Holds E c w := by
  rw [holds_clause]
  apply forall_congr'
  intro w
  apply imp_congr_right
  intro _
  exact (holds_ex E Names.empty c w).symm.trans
    (by simpa [smartEx] using (smartEx_correct E Names.empty c w).symm)

/-- Scoped projection is performed inside the universal binder. No exchange
of universal and existential quantifiers is used. -/
def normalize {K} (E : ClassEnv K) : Formula K E.count → Formula K E.count
  | .and a b => smartAnd (normalize E a) (normalize E b)
  | .ex a c => (project E a (normalize E c)).val
  | .clause a b c => smartClause a Names.empty (project E b (normalize E c)).val
  | .subst s c => simplify E (push E s (normalize E c))
  | c => simplify E c

theorem normalize_correct {K} (E : ClassEnv K) (c v) :
    Formula.Holds E (normalize E c) v ↔ Formula.Holds E c v := by
  induction c generalizing v with
  | and a b ha hb => simp only [normalize, smartAnd_correct, ha, hb, holds_and]
  | ex a c ih =>
    exact ((project E a (normalize E c)).property v).trans
      (by simp only [holds_ex, ih])
  | clause a b c ih =>
    rw [normalize, smartClause_correct, clause_empty, holds_clause]
    apply forall_congr'
    intro w
    apply imp_congr_right
    intro _
    exact ((project E b (normalize E c)).property w).trans (by simp only [holds_ex, ih])
  | subst s c ih => simp only [normalize, simplify_correct, push_correct, holds_subst, ih]
  | top => exact simplify_correct E .top v
  | bot => exact simplify_correct E .bot v
  | eq a b => exact simplify_correct E (.eq a b) v
  | pred c t => exact simplify_correct E (.pred c t) v
  | effectLe a b => exact simplify_correct E (.effectLe a b) v
  | lacks op a => exact simplify_correct E (.lacks op a) v

def normalizer {K} (E : ClassEnv K) : (constraints E).Simplifier where
  run := normalize E
  equivalent := fun c => ⟨fun v => (normalize_correct E c v).mp, fun v => (normalize_correct E c v).mpr⟩

end EHMX.TypeClasses
