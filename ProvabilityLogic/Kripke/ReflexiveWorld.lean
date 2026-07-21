module

public import ProvabilityLogic.Kripke.Basic

@[expose]
public section

open scoped Formula

universe u v

variable {α : Type u} [DecidableEq α]

namespace Model.World

variable {κ : Type v} [Nonempty κ] {M : Model κ α}

/--
  A world `x` is `X`-reflexive (KK23, "`Σ`-reflexive") if `□A → A` is forced at `x` for every
  `□A ∈ X`.
-/
def IsReflexiveOf (X : FormulaFinset α) (x : M.World) : Prop :=
  ∀ {A}, □A ∈ X → x ⊩ (□A 🡒 A)

omit [DecidableEq α] in
/-- `IsReflexiveOf` is antitone in `X`: reflexivity for a larger set implies reflexivity for
any of its subsets. -/
lemma IsReflexiveOf.anti {X X' : FormulaFinset α} {x : M.World}
  (hx : x.IsReflexiveOf X') (hXX' : X ⊆ X') : x.IsReflexiveOf X :=
  fun hA => hx (hXX' hA)

end Model.World

variable {κ : Type v} [Nonempty κ] {M : Model κ α}

/-- The `Subtype` of worlds of `M` that are `X`-reflexive. -/
abbrev Model.ReflexiveWorldOf (M : Model κ α) (X : FormulaFinset α) := {x : M.World // x.IsReflexiveOf X}

namespace Model.ReflexiveWorldOf

variable {X : FormulaFinset α}

instance : CoeOut (M.ReflexiveWorldOf X) M.World := ⟨Subtype.val⟩

end Model.ReflexiveWorldOf

end
