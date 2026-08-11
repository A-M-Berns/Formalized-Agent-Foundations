import CartesianFrames.Operations
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod

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

The §2.4 subagency relations get the same treatment in the second half of the file,
on the paper's own §2.4 examples (the driver committing to skip the country road, and
the two-member team) plus a four-row variant.  What those witnesses rule out:

* `◁` is **not the total relation** (`not_subagent_dedup_driver`), and neither is it
  the paper's `≃ᵇ` in disguise: `◁₊` and `◁ₓ` each hold between frames that are *not*
  biextensionally equivalent (`driver_addSubagent_driver3` with
  `not_biextEquiv_driver_driver3`; `teamC_multSubagent_teamD` with
  `not_biextEquiv_teamC_teamD`), so `Definition 18` and `Definition 19` are not
  degenerate in either direction;
* the relations are **oriented** as the paper orients them
  (`not_subagent_driver3_driver`, `not_subagent_teamD_teamC`), so they are not
  symmetric relations misread as directed ones;
* `◁₊` and `◁ₓ` are each **strictly stronger** than `◁` (`bigC_subagent_bigD` with
  `not_bigC_addSubagent_bigD` and `not_bigC_multSubagent_bigD`), so `Theorem 24`'s
  factorization is not a repackaging of a single relation;
* and that factorization is **non-trivial**: on `bigC ◁ bigD` every intermediate it
  can produce is biextensionally distinct from both endpoints
  (`every_witness_nontrivial`, non-vacuous by `bigC_decomposes`).

None of these statements is a paper claim, so none carries a paper-node annotation; the
matrices they are built from are the paper's own worked examples, cited above in prose.
Every lemma here is a non-vacuity witness (kind `N±`): each is discharged by `decide`
over concrete finite carriers, or composed from the §2.2/§2.4 layers (provenance
`(a)`).  All are hypothesis-free except `every_witness_nontrivial`, whose two
hypotheses are exactly the pair `Theorem 24` produces and are exhibited by
`bigC_decomposes`.  The concrete frames are `abbrev`s rather than `def`s so that
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

/-! ## `◁` is not the total relation

`Definition 13` would say nothing if every frame were a subagent of every other.  It
is not: there is no morphism `dedup ⟶ driver` at all, so the covering condition of
`Definition 50` fails at once. -/

/-- `Definition 13` is a real restriction; a fortiori so are `Definition 18` and
`Definition 19`, which imply it by Claim 23. -/
lemma not_subagent_dedup_driver : ¬ (dedup ◁ driver) := by
  intro h
  obtain ⟨φ, -, -⟩ := subagent_iff_subagentCovering.mp h 0
  exact not_nonempty_hom_dedup_driver ⟨φ⟩

/-! ## The committing example of §2.4: the driver skips the country road

The paper motivates `Definition 18` with a driver who *commits* to a subset of her
options.  Here `driver3` is the §2.1 matrix with a third row added — a route the
driver may rule out — and `driver` is what remains after she commits to the first
two.  The pair witnesses `◁₊` at a place where the two frames are *not*
biextensionally equivalent, so the relation is not Claim 17's `≃ᵇ`-case in
disguise. -/

/-- The §2.1 driver with a third option available. -/
abbrev driver3 : Frame ℕ where
  Agent := Fin 3
  Env := Fin 3
  outcome := ![![1, 5, 7], ![5, 5, 5], ![6, 6, 6]]

/-- The two options the driver commits to, i.e. everything but the third row. -/
abbrev committed : Set (Fin 3) := {a | a ≠ 2}

/-- `driver3` after the commitment.  This is `Definition 28`'s `Commit^B` at this
instance (checked immediately below), spelled out so that `decide` and instance
search can see the carriers. -/
abbrev driver3Commit : Frame ℕ where
  Agent := committed
  Env := Fin 3
  outcome := fun x z => driver3.outcome x.val z

example : driver3Commit = driver3.commit committed := rfl

/-- Dropping the third row does not change what the remaining two rows do. -/
def toCommit : driver ⟶ driver3Commit where
  agent := fun a => ⟨a.castSucc, by revert a; decide⟩
  env := _root_.id
  adjoint := by decide

def fromCommit : driver3Commit ⟶ driver where
  agent := fun s => if s.val = 0 then 0 else 1
  env := _root_.id
  adjoint := by
    rintro ⟨v, hv⟩ e
    have h : v ≠ 2 := hv
    show driver3.outcome v e = driver.outcome (if v = 0 then 0 else 1) e
    revert h; revert v e; decide

/-- The committing example, read straight off `Definition 18`: the common
environment is `Fin 3`, the ambient agent carrier is `driver3`'s, and the committed
subset is `committed`. -/
lemma driver_addSubagent_driver3 : driver ◁₊ driver3 := by
  refine ⟨Fin 3, Fin 3, committed, driver3.outcome, ?_, BiextEquiv.refl _⟩
  refine biextEquiv_iff_homotopyEquiv.mpr ⟨toCommit, fromCommit, ?_, ?_⟩
  · intro a e; revert a e; decide
  · rintro ⟨v, hv⟩ e
    have h : v ≠ 2 := hv
    show driver3.outcome v e
        = driver3.outcome (Fin.castSucc (if v = 0 then (0 : Fin 2) else 1)) e
    revert h; revert v e; decide

lemma driver3_biextensional : driver3.Biextensional := by
  constructor
  · intro a b h; revert h; revert a b; decide
  · intro a b h; revert h; revert a b; decide

/-- …and the two frames are **not** biextensionally equivalent, so
`driver_addSubagent_driver3` is a genuine instance of `Definition 18` rather than
Claim 17's reflexive case transported along `≃ᵇ`.  Both frames are biextensional, so
Claim 38 turns the equivalence into an isomorphism, which the agent carriers'
cardinalities forbid. -/
lemma not_biextEquiv_driver_driver3 : ¬ (driver ≃ᵇ driver3) := by
  intro h
  obtain ⟨i⟩ := (homotopyEquiv_iff_nonempty_iso_of_biextensional
    driver_biextensional driver3_biextensional).mp (biextEquiv_iff_homotopyEquiv.mp h)
  obtain ⟨f, hf⟩ := nonempty_iso_iff_exists_isIsomorphism.mp ⟨i⟩
  have := Fintype.card_le_of_surjective (show Fin 2 → Fin 3 from f.agent) hf.1.2
  simp at this

/-! ## The externalizing example of §2.4: a two-member team

The paper's second §2.4 example: a team `teamD` of three joint options, one of whose
members is externalized.  `teamZ` is the member's frame over `teamD`'s agent, and
`teamC` is the remaining member's frame — the currying `teamD°(teamZ)` on the
nose. -/

/-- The team's joint options against a two-state environment. -/
abbrev teamD : Frame ℕ where
  Agent := Fin 3
  Env := Fin 2
  outcome := ![![0, 1], ![2, 3], ![4, 5]]

/-- The externalized team member, as a frame over the team's joint options. -/
abbrev teamZ : Frame teamD.Agent where
  Agent := Fin 2
  Env := Fin 2
  outcome := ![![0, 0], ![1, 2]]

/-- The remaining member's frame: `teamD°(teamZ)` (checked below). -/
abbrev teamC : Frame ℕ where
  Agent := Fin 2
  Env := Fin 2 × Fin 2
  outcome := fun b p => teamD.outcome (teamZ.outcome b p.1) p.2

example : teamC = teamD.curry.obj teamZ := rfl

/-- The externalized member can reach every joint option — `Definition 21`'s image
condition. -/
lemma teamZ_image_univ : teamZ.image = Set.univ := by
  refine Set.eq_univ_of_forall fun c => ?_
  show ∃ a e, teamZ.outcome a e = c
  revert c; decide

/-- The team example as an instance of `Definition 19`, via Claim 22. -/
lemma teamC_multSubagent_teamD : teamC ◁ₓ teamD :=
  multSubagent_iff_multSubagentCurry.mpr ⟨teamZ, teamZ_image_univ, BiextEquiv.refl _⟩

lemma teamC_biextensional : teamC.Biextensional := by
  constructor
  · intro a b h; revert h; revert a b; decide
  · intro a b h; revert h; revert a b; decide

lemma teamD_biextensional : teamD.Biextensional := by
  constructor
  · intro a b h; revert h; revert a b; decide
  · intro a b h; revert h; revert a b; decide

/-- …and again the pair is not biextensionally equivalent, so `Definition 19` is not
degenerate here either. -/
lemma not_biextEquiv_teamC_teamD : ¬ (teamC ≃ᵇ teamD) := by
  intro h
  obtain ⟨i⟩ := (homotopyEquiv_iff_nonempty_iso_of_biextensional
    teamC_biextensional teamD_biextensional).mp (biextEquiv_iff_homotopyEquiv.mp h)
  obtain ⟨f, hf⟩ := nonempty_iso_iff_exists_isIsomorphism.mp ⟨i⟩
  have := Fintype.card_le_of_surjective (show Fin 2 → Fin 3 from f.agent) hf.1.2
  simp at this

/-! ## The relations are oriented

Both examples fail in the reverse direction, so `◁`, `◁₊`, `◁ₓ` are directed
relations and not symmetric ones misread as directed. -/

lemma not_subagent_driver3_driver : ¬ (driver3 ◁ driver) := by
  intro h
  obtain ⟨φ, -, -⟩ := subagent_iff_subagentCovering.mp h 0
  have key : ∀ (g : Fin 3 → Fin 2) (k : Fin 3 → Fin 3),
      ¬ (∀ a e, driver3.outcome a (k e) = driver.outcome (g a) e) := by decide
  exact key φ.agent φ.env φ.adjoint

lemma not_subagent_teamD_teamC : ¬ (teamD ◁ teamC) := by
  intro h
  obtain ⟨φ, -, -⟩ := subagent_iff_subagentCovering.mp h 0
  have key : ∀ (g : Fin 3 → Fin 2) (k : Fin 2 × Fin 2 → Fin 2),
      ¬ (∀ a e, teamD.outcome a (k e) = teamC.outcome (g a) e) := by decide
  exact key φ.agent φ.env φ.adjoint

/-! ## `◁₊` and `◁ₓ` are each strictly stronger than `◁`

Widening the team example to four joint options gives a single pair `bigC ◁ bigD`
on which *neither* `Definition 18` nor `Definition 19` holds.  So `Theorem 24`'s
factorization of `◁` through an intermediate frame is not a repackaging of one
relation, and — by the last lemma of the file — every intermediate it can produce is
a new frame. -/

abbrev bigD : Frame ℕ where
  Agent := Fin 4
  Env := Fin 2
  outcome := ![![0, 1], ![2, 3], ![4, 5], ![6, 7]]

abbrev bigZ : Frame bigD.Agent where
  Agent := Fin 2
  Env := Fin 2
  outcome := ![![0, 0], ![1, 2]]

abbrev bigC : Frame ℕ where
  Agent := Fin 2
  Env := Fin 2 × Fin 2
  outcome := fun b p => bigD.outcome (bigZ.outcome b p.1) p.2

example : bigC = bigD.curry.obj bigZ := rfl

/-- `bigC ◁ bigD` by `Definition 14`, via Claim 15. -/
lemma bigC_subagent_bigD : bigC ◁ bigD :=
  subagent_iff_subagentCurry.mpr ⟨bigZ, BiextEquiv.refl _⟩

lemma bigC_biextensional : bigC.Biextensional := by
  constructor
  · intro a b h; revert h; revert a b; decide
  · intro a b h; revert h; revert a b; decide

/-- `Definition 19` fails: an externalizing witness would have to reach `bigD`'s
fourth option, and the curried frame would then realize the world `6`, which `bigC`
does not — contradicting the `≃ᵇ`-invariance of `Image`. -/
lemma not_bigC_multSubagent_bigD : ¬ (bigC ◁ₓ bigD) := by
  intro h
  obtain ⟨M, himg, hM⟩ := h.multSubagentCurry
  have h3 : (3 : Fin 4) ∈ M.image := by rw [himg]; trivial
  obtain ⟨a, e, he⟩ := h3
  have h6 : (6 : ℕ) ∈ (bigD.curry.obj M).image := by
    refine ⟨a, (e, 0), ?_⟩
    show bigD.outcome (M.outcome a e) 0 = 6
    rw [he]; decide
  have h6' : (6 : ℕ) ∈ bigC.image := by rw [image_eq_of_biextEquiv hM]; exact h6
  obtain ⟨a', e', he'⟩ := h6'
  revert he'; revert a' e'; decide

/-- `Definition 18` fails: a committing witness has a one-element environment, so
`bigC`'s four environment states would have to inject into `bigD`'s two. -/
lemma not_bigC_addSubagent_bigD : ¬ (bigC ◁₊ bigD) := by
  intro h
  obtain ⟨M, hu, hM⟩ := h.addSubagentCurry
  haveI := hu
  obtain ⟨g, hg⟩ := exists_env_injective_of_biextEquiv bigC_biextensional hM
  have hg2 : Function.Injective (fun e : Fin 2 × Fin 2 => (g e).2) := fun e₀ e₁ he =>
    hg (Prod.ext (Subsingleton.elim _ _) he)
  have := Fintype.card_le_of_injective _ hg2
  simp at this

/-- `Theorem 24` really does produce something new on `bigC ◁ bigD`: any frame
sitting between them is biextensionally distinct from both endpoints.  (Were it
equivalent to `bigC`, the additive leg would give `bigC ◁₊ bigD`; were it equivalent
to `bigD`, the multiplicative leg would give `bigC ◁ₓ bigD`.) -/
lemma every_witness_nontrivial {C₂ : Frame ℕ} (hx : bigC ◁ₓ C₂) (ha : C₂ ◁₊ bigD) :
    ¬ (C₂ ≃ᵇ bigC) ∧ ¬ (C₂ ≃ᵇ bigD) :=
  ⟨fun h => not_bigC_addSubagent_bigD (ha.congr h (BiextEquiv.refl _)),
   fun h => not_bigC_multSubagent_bigD (hx.congr (BiextEquiv.refl _) h)⟩

/-- …and the hypotheses of `every_witness_nontrivial` are satisfied: `Theorem 24`
applied to `bigC_subagent_bigD` exhibits such a pair. -/
lemma bigC_decomposes : ∃ C₂, (bigC ◁ₓ C₂) ∧ (C₂ ◁₊ bigD) :=
  subagent_iff_exists_multSubagent_addSubagent.mp bigC_subagent_bigD

end Examples

end CartesianFrames
