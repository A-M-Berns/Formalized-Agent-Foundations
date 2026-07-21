module

public import ProvabilityLogic.Kripke.Basic

@[expose]
public section

variable [Nonempty κ]

abbrev Model.Root (M : Model κ α) := { r : M.World // ∀ x, x ≠ r → r ≺ x }

structure RootedModel (κ) [Nonempty κ] (α) extends Model κ α where
  root : toModel.Root

namespace RootedModel

/-- A world of `M` other than its root. Bundling the non-root proof into a subtype lets
lemmas and instances about cone removal take a single argument `a : M.NonRoot` instead of
threading an explicit `a : M.World` together with a proof `a ≠ M.root.1`. -/
abbrev NonRoot (M : RootedModel κ α) := { a : M.World // a ≠ M.root.1 }

variable {M : RootedModel κ α} {s : Formula.Substitution α α}

/-- Rooted model obtained by composing the valuation with a substitution `s`
(the frame and the root are unchanged). -/
abbrev substModel (M : RootedModel κ α) (s : Formula.Substitution α α) : RootedModel κ α where
  toModel := M.toModel.substModel s
  root := M.root

end RootedModel

end
