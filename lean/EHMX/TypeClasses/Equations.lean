import EHMX.TypeClasses.Reduction

namespace EHMX.TypeClasses

def equations {K n} : Ty K → Ty K → Formula K n
  | .arr a e b, .arr c f d =>
    .and (equations a c) (.and (equations b d) (.and (.effectLe e f) (.effectLe f e)))
  | .con k args, .con l bs =>
    if h : k = l then
      Formula.all ((List.finRange (K.arity k)).map (fun i => equations (args i) ((h ▸ bs) i)))
    else .bot
  | .base a, .base b => if a = b then .top else .bot
  | .var i, .var j => if i = j then .top else .eq (.var i) (.var j)
  | .var i, t => .eq (.var i) t
  | t, .var i => .eq t (.var i)
  | _, _ => .bot
termination_by structural a _ => a

theorem equations_correct {K} (E : ClassEnv K) (a b : Ty K) (v) :
    Formula.Holds E (equations a b) v ↔ a.eval v = b.eval v := by
  induction a generalizing b with
  | var i =>
    cases b with
    | var j => simp only [equations]; split <;> simp_all [Ty.eval]
    | _ => simp [equations]
  | base x =>
    cases b with
    | base y => simp only [equations]; split <;> simp_all [Ty.eval]
    | _ => simp [equations, Ty.eval]
  | arr a e c ha hc =>
    cases b with
    | arr d f q =>
      simp only [equations, holds_and, holds_effectLe, ha, hc, Ty.eval, Ground.arr.injEq]
      constructor
      · rintro ⟨h₁, h₂, h₃, h₄⟩
        exact ⟨h₁, Finset.Subset.antisymm h₃ h₄, h₂⟩
      · rintro ⟨h₁, h₂, h₃⟩
        exact ⟨h₁, h₃, h₂ ▸ Finset.Subset.refl _, h₂ ▸ Finset.Subset.refl _⟩
    | _ => simp [equations, Ty.eval]
  | con k args ih =>
    cases b with
    | con l bs =>
      by_cases h : k = l
      · subst l
        simp [equations, holds_all, Ty.eval, Ground.con.injEq, funext_iff, ih]
      · simp [equations, h, Ty.eval, Ground.con.injEq]
    | _ => simp [equations, Ty.eval]

end EHMX.TypeClasses
