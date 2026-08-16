import CartesianFrames.API

namespace APITests.CartesianFrames

open CategoryTheory
open _root_.CartesianFrames
open scoped _root_.CartesianFrames.Frame

/-- A tiny client frame, independent of the paper's worked-example fixtures. -/
abbrev bitFrame : Frame Bool where
  Agent := Bool
  Env := PUnit
  outcome a _ := a

def bitIdentity : bitFrame ⟶ bitFrame where
  agent := id
  env := id
  adjoint _ _ := rfl

example : bitIdentity ≫ bitIdentity = bitIdentity := by
  apply Frame.Hom.ext <;> rfl

example (B : Set bitFrame.Agent) (b : B) (e : bitFrame.Env) :
    (bitFrame.commit B).outcome b e = bitFrame.outcome b.val e := by simp

/-- Operation facts compose with unrelated subagent facts. -/
example {W : Type} (C D : Frame W) (s : Setoid C.Agent) (h : C ◁ D) :
    C.external s ◁ D :=
  (C.external_multSubagent s).subagent.trans h

/-- The ordinary subagent relation now has the same direct equivalence transport as its
additive and multiplicative refinements. -/
example {W : Type} {C C' D D' : Frame W} (h : C ◁ D)
    (hC : C ≃ᵇ C') (hD : D ≃ᵇ D') : C' ◁ D' :=
  h.congr hC hD

example {W : Type} {C D : Frame W} (h : C ◁ₓ D) :
    Frame.MultSubagentCategorical C D :=
  Frame.multSubagent_iff_multSubagentCategorical.mp h

/-- Claim 35's supported half is consumed honestly at canonical-isomorphism strength. -/
example {W : Type} (C : Frame W) (B : Set C.Agent) :
    C.commit B ≃ᵇ (C.commit B).commit (Subtype.val ⁻¹' B) :=
  Frame.biextEquiv_of_nonempty_iso ⟨(C.commit_commit_self B).symm⟩

end APITests.CartesianFrames
