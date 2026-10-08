import SystemFXi.EHMX.Classes

namespace SystemFXi.EHMX

example (sig : Signature) (X : Domain) (Γ : Context X) (s : Supply)
    (n : Int) :
    infer sig X Γ (.int n) s =
      some ⟨.base .int, ∅, .top, s⟩ := by
  rfl

example (sig : Signature) (X : Domain) (Γ : Context X) (s : Supply)
    (b : Bool) :
    infer sig X Γ (.bool b) s =
      some ⟨.base .bool, ∅, .top, s⟩ := by
  rfl

example (X : Domain) :
    simplifyAtom (X := X) (.typeEq (.base .int) (.base .bool)) = none := by
  rfl

example (I : ClassEnv) :
    (infer (fun _ => none) (classDomain I) []
      (.app (.lam (.var 0)) (.int 1)) ⟨1, 1⟩).map
        (fun r => (r.ty, r.effect.vars)) =
      some (.var 4, {3}) := by
  rfl

end SystemFXi.EHMX
