import CartesianFrames.Biextensional
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi

/-!
# Worked examples and non-vacuity witnesses

The paper's two unnumbered worked matrices, as concrete `Frame ℕ`s, together with the
witnesses that the §2.2 equivalence layer says something: the definitions are neither
vacuous nor degenerate, and the separations the paper asserts informally really hold in
this encoding.

* §2.1's driver matrix (seaside vs. highway against rain/cloud/sun) is `driver`.
* §2.2's duplicate-row pair — the paper's "not isomorphic, but biextensionally
  equivalent (consider deleting `b₃`)" — is `dedup` and `dup`.

What the witnesses rule out:

* biextensional/homotopy equivalence is **strictly weaker** than isomorphism
  (`biextEquiv_strictly_weaker_than_iso`), so `BiextEquiv` is not a re-spelling of `≅`;
* `Homotopic` is **not equality** (`homotopic_ne_eq`) and **not the total relation**
  (`not_homotopic_of_row_col`), so `Definition 36` is not degenerate in either
  direction;
* `BiextEquiv` is **not the total relation** (`not_biextEquiv_dedup_driver`), so
  `Definition 7` does not identify everything;
* the collapse genuinely deletes (`nonempty_iso_dup_collapse_dedup`,
  `not_nonempty_iso_dup_collapse`), so `Definition 6` is not the identity in disguise.

None of these statements is a paper claim, so none carries a paper-node annotation; the
matrices they are built from are the paper's own worked examples, cited above in prose.
Every lemma here is a non-vacuity witness (kind `N±`) with no hypotheses: each is
discharged by `decide` over concrete finite carriers, or composed from the §2.2 layer
(provenance `(a)`).  The concrete frames are `abbrev`s rather than `def`s so that
`decide` and instance search can see through to their carriers.
-/

namespace CartesianFrames

namespace Examples

open CategoryTheory Frame

/-! ## The driver of §2.1 -/

/-- The paper's opening matrix (§2.1): a driver choosing the seaside route (`0`) or the
highway (`1`) against rainy / cloudy / sunny weather (`0`, `1`, `2`), with worlds the
numbers measuring how much she likes each outcome.

```
      e_r  e_c  e_s
a_s    1    5    7
a_h    5    5    5
```
-/
abbrev driver : Frame ℕ where
  Agent := Fin 2
  Env := Fin 3
  outcome := ![![1, 5, 7], ![5, 5, 5]]

/- The matrix is read off as printed, and `Frame.dual` is transposition on it. -/
example : driver.outcome 0 2 = 7 := rfl
example (e : Fin 3) (a : Fin 2) : driver.dual.outcome e a = driver.outcome a e := rfl

/-- The driver matrix has no duplicate rows or columns: `Definition 4` has a
non-degenerate inhabitant with more than one agent choice and more than one
environment state. -/
lemma driver_biextensional : driver.Biextensional := by
  constructor
  · intro a b h; revert h; revert a b; decide
  · intro a b h; revert h; revert a b; decide

/-- `7` is realized by a choice/state pair and `2` is not: `Frame.image` is a proper,
inhabited subset of the worlds here. -/
lemma seven_mem_driver_image : (7 : ℕ) ∈ driver.image := ⟨0, 2, rfl⟩

lemma two_not_mem_driver_image : (2 : ℕ) ∉ driver.image := by
  rintro ⟨a, e, h⟩; revert h; revert a e; decide

/-! ## The duplicate-row pair of §2.2

The paper's example of two frames that "are not isomorphic, but they are
biextensionally equivalent (consider deleting `b₃`)".  The paper writes the entries as
abstract worlds `w₁ … w₆`; here they are the numerals `1 … 6`, whose only relevant
property — pairwise distinctness — is the same. -/

/-- The left frame of §2.2: rows `a₁, a₂`, columns `e₁, e₂, e₃`. -/
abbrev dedup : Frame ℕ where
  Agent := Fin 2
  Env := Fin 3
  outcome := ![![1, 2, 3], ![4, 5, 6]]

/-- The right frame of §2.2: rows `b₁, b₂, b₃`, columns `f₁, f₂, f₃`, with `b₃` a
duplicate of `b₂`. -/
abbrev dup : Frame ℕ where
  Agent := Fin 3
  Env := Fin 3
  outcome := ![![1, 2, 3], ![4, 5, 6], ![4, 5, 6]]

lemma dedup_biextensional : dedup.Biextensional := by
  constructor
  · intro a b h; revert h; revert a b; decide
  · intro a b h; revert h; revert a b; decide

/-- `dup` is not biextensional: rows `b₂` and `b₃` coincide.  So `Definition 4` is a
real restriction, and Claim 38's hypotheses are not automatic. -/
lemma not_dup_biextensional : ¬ dup.Biextensional := by
  intro h
  have : (1 : Fin 3) = 2 := h.agent_ext (by decide)
  exact absurd this (by decide)

/-- The paper's `(g, h)` mapping corresponding subscripts forward. -/
def toDup : dedup ⟶ dup where
  agent := ![0, 1]
  env := _root_.id
  adjoint := by decide

/-- The backward map, which sends the duplicate row `b₃` back to `a₂`. -/
def toDedup : dup ⟶ dedup where
  agent := ![0, 1, 1]
  env := _root_.id
  adjoint := by decide

/-- The §2.2 pair is homotopy equivalent (`Definition 37`). -/
lemma homotopyEquiv_dedup_dup : HomotopyEquiv dedup dup := by
  refine ⟨toDup, toDedup, ?_, ?_⟩
  · intro a e; revert a e; decide
  · intro a e; revert a e; decide

/-- …but the pair is not isomorphic: the agent carriers have different cardinalities,
so no component map can be a bijection. -/
lemma not_nonempty_iso_dedup_dup : ¬ Nonempty (dedup ≅ dup) := by
  intro h
  obtain ⟨f, hf⟩ := nonempty_iso_iff_exists_isIsomorphism.mp h
  have hs : Function.Surjective (show Fin 2 → Fin 3 from f.agent) := hf.1.2
  have := Fintype.card_le_of_surjective _ hs
  simp at this

/-- Homotopy equivalence is **strictly** weaker than isomorphism: the §2.2 pair
witnesses the gap that Claim 38 closes only under biextensionality. -/
lemma homotopyEquiv_strictly_weaker_than_iso :
    HomotopyEquiv dedup dup ∧ ¬ Nonempty (dedup ≅ dup) :=
  ⟨homotopyEquiv_dedup_dup, not_nonempty_iso_dedup_dup⟩

/-- The paper's headline for §2.2: non-isomorphic frames can be biextensionally
equivalent.  So `Definition 7` is strictly coarser than `Definition 3`. -/
lemma biextEquiv_strictly_weaker_than_iso :
    (dedup ≃ᵇ dup) ∧ ¬ Nonempty (dedup ≅ dup) :=
  ⟨biextEquiv_iff_homotopyEquiv.mpr homotopyEquiv_dedup_dup, not_nonempty_iso_dedup_dup⟩

/-! ## `Homotopic` is neither equality nor the total relation -/

/-- The endomorphism of `dup` that collapses the duplicate row `b₃` onto `b₂`. -/
def dupLoop : dup ⟶ dup where
  agent := ![0, 1, 1]
  env := _root_.id
  adjoint := by decide

/-- `dupLoop` is homotopic to the identity without being equal to it: `Definition 36`
is strictly coarser than equality of morphisms. -/
lemma homotopic_ne_eq : Homotopic dupLoop (𝟙 dup) ∧ dupLoop ≠ 𝟙 dup := by
  refine ⟨?_, ?_⟩
  · intro a e; revert a e; decide
  · intro h
    have hag : (show Fin 3 → Fin 3 from dupLoop.agent) = _root_.id := congrArg Hom.agent h
    exact absurd (congrFun hag 2) (by decide)

/-- A one-row frame. -/
abbrev row : Frame ℕ where
  Agent := Fin 1
  Env := Fin 2
  outcome := ![![0, 1]]

/-- A one-column frame. -/
abbrev col : Frame ℕ where
  Agent := Fin 2
  Env := Fin 1
  outcome := ![![0], ![1]]

def rowToCol₀ : row ⟶ col where
  agent := ![0]
  env := ![0]
  adjoint := by decide

def rowToCol₁ : row ⟶ col where
  agent := ![1]
  env := ![1]
  adjoint := by decide

/-- Two parallel morphisms that are *not* homotopic: `Definition 36` is not the total
relation on a hom-set. -/
lemma not_homotopic_of_row_col : ¬ Homotopic rowToCol₀ rowToCol₁ := by
  intro h
  exact absurd (h 0 0) (by decide)

/-! ## `BiextEquiv` is not the total relation -/

/-- There is no morphism at all from `dedup` to `driver`: the two frames' outcome
entries cannot be matched up under the adjointness condition. -/
lemma not_nonempty_hom_dedup_driver : ¬ Nonempty (dedup ⟶ driver) := by
  rintro ⟨f⟩
  have key : ∀ (g : Fin 2 → Fin 2) (h : Fin 3 → Fin 3),
      ¬ (∀ a e, dedup.outcome a (h e) = driver.outcome (g a) e) := by decide
  exact key f.agent f.env f.adjoint

lemma not_homotopyEquiv_dedup_driver : ¬ HomotopyEquiv dedup driver := by
  rintro ⟨φ, -, -, -⟩
  exact not_nonempty_hom_dedup_driver ⟨φ⟩

/-- `Definition 7` does not identify everything: the §2.2 frame and the §2.1 driver
are not biextensionally equivalent. -/
lemma not_biextEquiv_dedup_driver : ¬ (dedup ≃ᵇ driver) := fun h =>
  not_homotopyEquiv_dedup_driver (biextEquiv_iff_homotopyEquiv.mp h)

/-! ## The collapse genuinely deletes -/

/-- Deleting the duplicate row is exactly what the collapse does: `dup`'s collapse is
isomorphic to the deduplicated frame the paper obtains by hand. -/
lemma nonempty_iso_dup_collapse_dedup : Nonempty (dup.collapse ≅ dedup) := by
  have h₀ : Nonempty (dedup.collapse ≅ dup.collapse) :=
    biextEquiv_iff_homotopyEquiv.mpr homotopyEquiv_dedup_dup
  have h₁ : Nonempty (dedup ≅ dedup.collapse) :=
    dedup_biextensional.nonempty_iso_collapse
  exact ⟨h₀.some.symm.trans h₁.some.symm⟩

/-- …and the collapse is not the identity in disguise: `dup` is not isomorphic to its
own collapse. -/
lemma not_nonempty_iso_dup_collapse : ¬ Nonempty (dup ≅ dup.collapse) := by
  rintro ⟨i⟩
  exact not_nonempty_iso_dedup_dup
    ⟨nonempty_iso_dup_collapse_dedup.some.symm.trans i.symm⟩

end Examples

end CartesianFrames
