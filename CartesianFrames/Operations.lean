import CartesianFrames.AdditiveMultiplicative
import Mathlib.Data.Set.Basic

/-!
# Committing, assuming, externalizing, internalizing

§2.4.1 of the paper: sub-environments (Definitions 25–26) with the collapse of the
multiplicative notions (Claim 27), the four operations that generate subagents and
super-environments (Definitions 28–33), the fact that they do so (Claim 34, proved in
Appendix A as Claim 45), and idempotence (Claim 35).

Two renderings are worth flagging.

*Partitions.*  Definition 31's "partition `X` of `Y`" is modeled as a `Setoid`, so
`Y/X` — the choice functions picking one element of each cell — becomes the subtype
`partitionSections` of functions `Quotient s → α` splitting `Quotient.mk s`.  Mathlib
has no such type (`Setoid.IsPartition` is a predicate on `Set (Set α)` and there is no
bundled section-of-a-quotient), so it is defined here.

*Idempotence.*  Claim 35 asserts frame *equality*; committing changes the agent's
*type* (from `A` to `↥B`, then to `↥(Subtype.val ⁻¹' B)`), so equality is not even
stateable and the four idempotence declarations give the canonical isomorphism instead
(`dd:eq-to-iso`).  An `≅` is data, not a proposition, so those four are `def`s rather
than `theorem`s — the same shape as the library's other `dd:eq-to-iso` site,
`botOfUnivIsoBot`.  Only the Commit/Assume half of Claim 35 is formalized: its
External/Internal half is
ill-typed as printed — `B` partitions `A`, not `A/B` — and is excluded by ruling; see
`CartesianFrames/KNOWLEDGE.md` (intentional deviations) and
`notes/cartesian-frames-paper-errata.md` erratum 3.
-/

universe u

namespace CartesianFrames

namespace Frame

open CategoryTheory

variable {W : Type u}

/-! ## Sub-environments (Definitions 25–26) -/

/-- Definition 25: `C` is a sub-environment of `D` when `D* ◁ C*`.

Paper node: Definition 25 (§2.4.1). -/
def SubEnv (C D : Frame W) : Prop := Subagent D.dual C.dual

@[inherit_doc] scoped infixl:50 " ◁* " => SubEnv

/-- Definition 26, additive half: `C ◁*₊ D` when `D* ◁₊ C*`.

Paper node: Definition 26 (§2.4.1). -/
def AddSubEnv (C D : Frame W) : Prop := AddSubagent D.dual C.dual

@[inherit_doc] scoped infixl:50 " ◁*₊ " => AddSubEnv

/-- Definition 26, multiplicative half: `C ◁*ₓ D` when `D* ◁ₓ C*`.

Paper node: Definition 26 (§2.4.1). -/
def MultSubEnv (C D : Frame W) : Prop := MultSubagent D.dual C.dual

@[inherit_doc] scoped infixl:50 " ◁*ₓ " => MultSubEnv

/-- Half of Claim 27, stated so that the converse is the same lemma applied to duals
(`(C*)* = C` holds definitionally).  The externalizing data dualize by swapping the
outer factors `X` and `Z` and flipping the products the middle factor sits in. -/
private lemma multSubagent_dual {C D : Frame W} (h : C ◁ₓ D) : D.dual ◁ₓ C.dual := by
  obtain ⟨X, Y, Z, f, hC, hD⟩ := h
  refine ⟨Z, Y, X, fun z y x => f x y z,
    hD.dual.trans (biextEquiv_of_nonempty_iso ⟨?_⟩),
    hC.dual.trans (biextEquiv_of_nonempty_iso ⟨?_⟩)⟩
  · exact
      { hom :=
          { agent := fun z => z
            env := fun p => (p.2, p.1)
            adjoint := fun _ _ => rfl }
        inv :=
          { agent := fun z => z
            env := fun p => (p.2, p.1)
            adjoint := fun _ _ => rfl }
        hom_inv_id := rfl
        inv_hom_id := rfl }
  · exact
      { hom :=
          { agent := fun p => (p.2, p.1)
            env := fun x => x
            adjoint := fun _ _ => rfl }
        inv :=
          { agent := fun p => (p.2, p.1)
            env := fun x => x
            adjoint := fun _ _ => rfl }
        hom_inv_id := rfl
        inv_hom_id := rfl }

/-- Multiplicative subagent and multiplicative sub-environment coincide.

Paper node: Claim 27 (§2.4.1). -/
theorem multSubagent_iff_multSubEnv {C D : Frame W} : C ◁ₓ D ↔ C ◁*ₓ D :=
  ⟨fun h => multSubagent_dual h, fun h => multSubagent_dual h⟩

/-! ## Committing and assuming (Definitions 28–29, Claim 30) -/

/-- Definition 28's `Commit^B`: restrict the agent to `B`.

Paper node: Definition 28 (§2.4.1). -/
def commit (C : Frame W) (B : Set C.Agent) : Frame W where
  Agent := B
  Env := C.Env
  outcome := fun b e => C.outcome b.val e

/-- Definition 28's `Commit^{∖B}`: restrict the agent to the complement of `B`.

Paper node: Definition 28 (§2.4.1). -/
abbrev commitCompl (C : Frame W) (B : Set C.Agent) : Frame W := C.commit Bᶜ

/-- Definition 29's `Assume^F`: restrict the environment to `F`.

Paper node: Definition 29 (§2.4.1). -/
def assume (C : Frame W) (F : Set C.Env) : Frame W where
  Agent := C.Agent
  Env := F
  outcome := fun a f => C.outcome a f.val

/-- Definition 29's `Assume^{∖F}`.

Paper node: Definition 29 (§2.4.1). -/
abbrev assumeCompl (C : Frame W) (F : Set C.Env) : Frame W := C.assume Fᶜ

/-- Committing produces additive subagents — Claim 30(1) for `B`.  As the paper says,
this is immediate from Definition 18: `Commit^B(C)` and `C` are already presented over
the common environment `Env(C)` with agent carriers `B ⊆ Agent(C)`.

Paper node: Claim 30 (§2.4.1). -/
theorem commit_addSubagent (C : Frame W) (B : Set C.Agent) : C.commit B ◁₊ C :=
  ⟨C.Agent, C.Env, B, C.outcome, BiextEquiv.refl _, BiextEquiv.refl _⟩

/-- Committing produces additive subagents — Claim 30(1) for `∖B`.

Paper node: Claim 30 (§2.4.1). -/
theorem commitCompl_addSubagent (C : Frame W) (B : Set C.Agent) : C.commitCompl B ◁₊ C :=
  C.commit_addSubagent Bᶜ

/-- Assuming produces additive super-environments — Claim 30(2) for `F`.  Unfolding
Definition 26, the goal is `Assume^F(C)* ◁₊ C*`, and `Assume^F(C)*` is `Commit^F(C*)`
on the nose, so the same two-leg witness serves.

Paper node: Claim 30 (§2.4.1). -/
theorem addSubEnv_assume (C : Frame W) (F : Set C.Env) : C ◁*₊ C.assume F :=
  ⟨C.Env, C.Agent, F, fun e a => C.outcome a e, BiextEquiv.refl _, BiextEquiv.refl _⟩

/-- Assuming produces additive super-environments — Claim 30(2) for `∖F`.

Paper node: Claim 30 (§2.4.1). -/
theorem addSubEnv_assumeCompl (C : Frame W) (F : Set C.Env) : C ◁*₊ C.assumeCompl F :=
  C.addSubEnv_assume Fᶜ

/-! ## Externalizing and internalizing (Definitions 31–33, Claims 34/45) -/

/-- Definition 31's `Y/X` for a partition rendered as a `Setoid`: the choice
functions selecting one element of each cell (`q(x) ∈ x` becomes `⟦q c⟧ = c`).

Paper node: Definition 31 (§2.4.1). -/
def partitionSections {α : Type u} (s : Setoid α) : Type u :=
  {q : Quotient s → α // ∀ c, Quotient.mk s (q c) = c}

/-- Definition 32's `External^B`: the agent becomes the choice functions `A/B`, the
environment gains the cell coordinate.

Paper node: Definition 32 (§2.4.1). -/
def external (C : Frame W) (s : Setoid C.Agent) : Frame W where
  Agent := partitionSections s
  Env := Quotient s × C.Env
  outcome := fun q p => C.outcome (q.val p.1) p.2

/-- Definition 32's `External^{/B}`: the agent becomes the cells, the environment
gains the choice-function coordinate.

Paper node: Definition 32 (§2.4.1). -/
def externalQuot (C : Frame W) (s : Setoid C.Agent) : Frame W where
  Agent := Quotient s
  Env := partitionSections s × C.Env
  outcome := fun c p => C.outcome (p.1.val c) p.2

/-- Definition 33's `Internal^F`.

Paper node: Definition 33 (§2.4.1). -/
def internal (C : Frame W) (s : Setoid C.Env) : Frame W where
  Agent := Quotient s × C.Agent
  Env := partitionSections s
  outcome := fun p q => C.outcome p.2 (q.val p.1)

/-- Definition 33's `Internal^{/F}`.

Paper node: Definition 33 (§2.4.1). -/
def internalSect (C : Frame W) (s : Setoid C.Env) : Frame W where
  Agent := partitionSections s × C.Agent
  Env := Quotient s
  outcome := fun p c => C.outcome p.2 (p.1.val c)

/-- Definition 31's choice functions are plentiful: some section selects `a` from
`a`'s own cell, uniformly in `a`.  This is the paper's "let `g₀(a) = (q, b)` where
`q(b) = a`" (Claim 45's proof), and it is the only input those proofs take from the
partition — the section property of the *ambient* choice function is never used. -/
private lemma exists_partitionSections_selecting {α : Type u} (s : Setoid α) :
    ∃ sec : α → partitionSections s, ∀ a, (sec a).val (Quotient.mk s a) = a := by
  classical
  have key : ∀ (a : α) (c : Quotient s),
      Quotient.mk s (if c = Quotient.mk s a then a else c.out) = c := by
    intro a c
    by_cases hc : c = Quotient.mk s a
    · rw [if_pos hc, hc]
    · rw [if_neg hc]
      exact Quotient.out_eq c
  exact ⟨fun a => ⟨fun c => if c = Quotient.mk s a then a else c.out, key a⟩,
    fun a => if_pos rfl⟩

/-- Externalizing produces multiplicative subagents — Claim 34/45(1) for `External^B`.
The externalizing witness is `(A/B, B, E)`; the paper's `(A/B × B, E, ⋄)` presentation
of `C` is realized by the section-through-`a` map and its evaluation inverse.

Paper node: Claim 34 (§2.4.1), Claim 45 (App. A). -/
theorem external_multSubagent (C : Frame W) (s : Setoid C.Agent) : C.external s ◁ₓ C := by
  obtain ⟨sec, hsec⟩ := exists_partitionSections_selecting s
  exact ⟨partitionSections s, Quotient s, C.Env, fun q c e => C.outcome (q.val c) e,
    BiextEquiv.refl _,
    biextEquiv_iff_homotopyEquiv.mpr
      ⟨{ agent := fun a => (sec a, Quotient.mk s a)
         env := fun e => e
         adjoint := fun a e => (congrArg (fun x => C.outcome x e) (hsec a)).symm },
       { agent := fun p => p.1.val p.2
         env := fun e => e
         adjoint := fun _ _ => rfl },
       fun a e => (congrArg (fun x => C.outcome x e) (hsec a)).symm,
       fun p e => (congrArg (fun x => C.outcome x e) (hsec (p.1.val p.2))).symm⟩⟩

/-- Externalizing produces multiplicative subagents — Claim 34/45(1) for
`External^{/B}`: the same witness with the two factors exchanged.

Paper node: Claim 34 (§2.4.1), Claim 45 (App. A). -/
theorem externalQuot_multSubagent (C : Frame W) (s : Setoid C.Agent) :
    C.externalQuot s ◁ₓ C := by
  obtain ⟨sec, hsec⟩ := exists_partitionSections_selecting s
  exact ⟨Quotient s, partitionSections s, C.Env, fun c q e => C.outcome (q.val c) e,
    BiextEquiv.refl _,
    biextEquiv_iff_homotopyEquiv.mpr
      ⟨{ agent := fun a => (Quotient.mk s a, sec a)
         env := fun e => e
         adjoint := fun a e => (congrArg (fun x => C.outcome x e) (hsec a)).symm },
       { agent := fun p => p.2.val p.1
         env := fun e => e
         adjoint := fun _ _ => rfl },
       fun a e => (congrArg (fun x => C.outcome x e) (hsec a)).symm,
       fun p e => (congrArg (fun x => C.outcome x e) (hsec (p.2.val p.1))).symm⟩⟩

/-- Internalizing produces multiplicative superagents — Claim 34/45(2) for
`Internal^F`.  The paper's route, verbatim: `Internal^F(C)*` *is* `External^F(C*)`
(here on the nose, not merely up to isomorphism), and Claim 27 transfers the
resulting multiplicative sub-environment back to a multiplicative subagent.

Paper node: Claim 34 (§2.4.1), Claim 45 (App. A). -/
theorem multSubagent_internal (C : Frame W) (s : Setoid C.Env) : C ◁ₓ C.internal s :=
  multSubagent_iff_multSubEnv.mpr (external_multSubagent C.dual s)

/-- Internalizing produces multiplicative superagents — Claim 34/45(2) for
`Internal^{/F}`, dual to `External^{/F}` in the same way.

Paper node: Claim 34 (§2.4.1), Claim 45 (App. A). -/
theorem multSubagent_internalSect (C : Frame W) (s : Setoid C.Env) :
    C ◁ₓ C.internalSect s :=
  multSubagent_iff_multSubEnv.mpr (externalQuot_multSubagent C.dual s)

/-! ## Idempotence (Claim 35, Commit/Assume half) -/

/-- Idempotence of committing, at canonical-isomorphism strength: the paper states
equality, which the subtype boundary makes unstateable; re-committing to the same
`B` (its preimage in the new agent carrier) reproduces the frame up to the
canonical isomorphism (`dd:eq-to-iso`).  Only the Commit/Assume half of Claim 35 is
formalized — the External/Internal half is ill-typed as printed and excluded by
ruling (see KNOWLEDGE.md, intentional deviations, and erratum 3).

Disclosure: the second argument `Subtype.val ⁻¹' B` is provably `Set.univ` (every
agent of `Commit^B(C)` already lies in `B`), so the subtype encoding has already
absorbed the claim's set-theoretic content — the paper's `B ∩ B = B` — and the
isomorphism is the entire remaining content.  This matches the paper, whose own
proof of this half is likewise trivial.

Paper node: Claim 35 (§2.4.1). -/
def commit_commit_self (C : Frame W) (B : Set C.Agent) :
    (C.commit B).commit (Subtype.val ⁻¹' B) ≅ C.commit B where
  hom :=
    { agent := fun b => b.val
      env := fun e => e
      adjoint := fun _ _ => rfl }
  inv :=
    { agent := fun b => ⟨b, b.property⟩
      env := fun e => e
      adjoint := fun _ _ => rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- Idempotence of committing to a complement, at canonical-isomorphism strength: the
paper states equality, which the subtype boundary makes unstateable; re-committing to
the same `B` (its preimage in the new agent carrier) reproduces the frame up to the
canonical isomorphism (`dd:eq-to-iso`).  Only the Commit/Assume half of Claim 35 is
formalized — the External/Internal half is ill-typed as printed and excluded by
ruling (see KNOWLEDGE.md, intentional deviations, and erratum 3).

Disclosure: the set actually restricted to here, `(Subtype.val ⁻¹' B)ᶜ`, is provably
`Set.univ` (no agent of `Commit^{∖B}(C)` lies in `B`), so the subtype encoding has
already absorbed the claim's set-theoretic content — the paper's `B ∩ B = B` — and
the isomorphism is the entire remaining content.  This matches the paper, whose own
proof of this half is likewise trivial.

Paper node: Claim 35 (§2.4.1). -/
def commitCompl_commitCompl_self (C : Frame W) (B : Set C.Agent) :
    (C.commitCompl B).commitCompl (Subtype.val ⁻¹' B) ≅ C.commitCompl B where
  hom :=
    { agent := fun b => b.val
      env := fun e => e
      adjoint := fun _ _ => rfl }
  inv :=
    { agent := fun b => ⟨b, b.property⟩
      env := fun e => e
      adjoint := fun _ _ => rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- Idempotence of assuming, at canonical-isomorphism strength: the paper states
equality, which the subtype boundary makes unstateable; re-assuming the same `F` (its
preimage in the new environment carrier) reproduces the frame up to the canonical
isomorphism (`dd:eq-to-iso`).  Only the Commit/Assume half of Claim 35 is
formalized — the External/Internal half is ill-typed as printed and excluded by
ruling (see KNOWLEDGE.md, intentional deviations, and erratum 3).

Disclosure: the second argument `Subtype.val ⁻¹' F` is provably `Set.univ` (every
environment state of `Assume^F(C)` already lies in `F`), so the subtype encoding has
already absorbed the claim's set-theoretic content — the paper's `F ∩ F = F` — and
the isomorphism is the entire remaining content.  This matches the paper, whose own
proof of this half is likewise trivial.

Paper node: Claim 35 (§2.4.1). -/
def assume_assume_self (C : Frame W) (F : Set C.Env) :
    (C.assume F).assume (Subtype.val ⁻¹' F) ≅ C.assume F where
  hom :=
    { agent := fun a => a
      env := fun f => ⟨f, f.property⟩
      adjoint := fun _ _ => rfl }
  inv :=
    { agent := fun a => a
      env := fun f => f.val
      adjoint := fun _ _ => rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- Idempotence of assuming a complement, at canonical-isomorphism strength: the paper
states equality, which the subtype boundary makes unstateable; re-assuming the same `F`
(its preimage in the new environment carrier) reproduces the frame up to the canonical
isomorphism (`dd:eq-to-iso`).  Only the Commit/Assume half of Claim 35 is
formalized — the External/Internal half is ill-typed as printed and excluded by
ruling (see KNOWLEDGE.md, intentional deviations, and erratum 3).

Disclosure: the set actually restricted to here, `(Subtype.val ⁻¹' F)ᶜ`, is provably
`Set.univ` (no environment state of `Assume^{∖F}(C)` lies in `F`), so the subtype
encoding has already absorbed the claim's set-theoretic content — the paper's
`F ∩ F = F` — and the isomorphism is the entire remaining content.  This matches the
paper, whose own proof of this half is likewise trivial.

Paper node: Claim 35 (§2.4.1). -/
def assumeCompl_assumeCompl_self (C : Frame W) (F : Set C.Env) :
    (C.assumeCompl F).assumeCompl (Subtype.val ⁻¹' F) ≅ C.assumeCompl F where
  hom :=
    { agent := fun a => a
      env := fun f => ⟨f, f.property⟩
      adjoint := fun _ _ => rfl }
  inv :=
    { agent := fun a => a
      env := fun f => f.val
      adjoint := fun _ _ => rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

section RegressionExamples

/- Client-side exercises of the endpoints above (endpoint-usability rule). -/

example (C : Frame W) (B : Set C.Agent) : C.commit B ◁ C :=
  (C.commit_addSubagent B).subagent

example (C : Frame W) (s : Setoid C.Agent) : C.external s ◁ C :=
  (C.external_multSubagent s).subagent

example (C : Frame W) (s : Setoid C.Env) : C ◁* C.internal s :=
  (multSubagent_iff_multSubEnv.mp (C.multSubagent_internal s)).subagent

example (C : Frame W) (F : Set C.Env) : (C.assume F).dual ◁₊ C.dual :=
  C.addSubEnv_assume F

example (C : Frame W) (B : Set C.Agent) : C.commitCompl B ◁ C :=
  (C.commitCompl_addSubagent B).subagent

example (C : Frame W) (F : Set C.Env) : (C.assumeCompl F).dual ◁₊ C.dual :=
  C.addSubEnv_assumeCompl F

example (C : Frame W) (s : Setoid C.Env) : C ◁ C.internalSect s :=
  (C.multSubagent_internalSect s).subagent

example (C : Frame W) (B : Set C.Agent) : C.commit B ≃ᵇ (C.commit B).commit (Subtype.val ⁻¹' B) :=
  (biextEquiv_of_nonempty_iso ⟨C.commit_commit_self B⟩).symm

example (C : Frame W) (B : Set C.Agent) :
    (C.commitCompl B).commitCompl (Subtype.val ⁻¹' B) ⟶ C.commitCompl B :=
  (C.commitCompl_commitCompl_self B).hom

example (C : Frame W) (F : Set C.Env) :
    (C.assume F).assume (Subtype.val ⁻¹' F) ⟶ C.assume F :=
  (C.assume_assume_self F).hom

example (C : Frame W) (F : Set C.Env) :
    (C.assumeCompl F).assumeCompl (Subtype.val ⁻¹' F) ⟶ C.assumeCompl F :=
  (C.assumeCompl_assumeCompl_self F).hom

/- The idempotence disclosure, machine-checked: the re-restricted set is everything
(and for the complement forms, the set restricted to is everything). -/

example (C : Frame W) (B : Set C.Agent) :
    (Subtype.val ⁻¹' B : Set (C.commit B).Agent) = Set.univ :=
  Set.eq_univ_of_forall fun x => x.property

example (C : Frame W) (B : Set C.Agent) :
    (Subtype.val ⁻¹' B : Set (C.commitCompl B).Agent)ᶜ = Set.univ :=
  Set.eq_univ_of_forall fun x => x.property

example (C : Frame W) (F : Set C.Env) :
    (Subtype.val ⁻¹' F : Set (C.assume F).Env) = Set.univ :=
  Set.eq_univ_of_forall fun x => x.property

example (C : Frame W) (F : Set C.Env) :
    (Subtype.val ⁻¹' F : Set (C.assumeCompl F).Env)ᶜ = Set.univ :=
  Set.eq_univ_of_forall fun x => x.property

end RegressionExamples

end Frame

end CartesianFrames
