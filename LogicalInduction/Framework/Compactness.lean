/-
# Compactness — one world for the whole deductive process

Propositional compactness in the exact form the criterion consumes: if every finite stage
of a deductive process has a propositionally consistent world, then a *single* world is
consistent with every stage (`PCWorld.ConsistentWithTheory`).

The route is Cantor space, not a proof calculus.  A `PCWorld` is an atom valuation
`ℕ → Prop` read through Foundation's Boolean evaluation, so it is a point of `ℕ → Bool` up
to atomwise equality.  For each sentence `φ` the truth set `{b | (ofBits b).Holds φ}` is
clopen — by induction on `φ`, atoms being preimages of clopens under coordinate
projections — hence each stage's consistency set is a finite intersection of clopens, so
closed.  The stage sets are nested and nonempty by hypothesis, and `ℕ → Bool` is compact
(Tychonoff over the finite discrete `Bool`), so Cantor's intersection theorem supplies a
point of every stage set at once.

Kind `P`; hypotheses `(a)` (Mathlib's Cantor intersection theorem and Foundation's atomwise
evaluation congruence — provenance `(b)` citations).  This module exists to *delete* a
repo-side joint-consistency hypothesis from the growing form of `thm:scon`, so it is
infrastructure and carries no paper node of its own.
-/
import LogicalInduction.Framework.Criterion
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.Order

namespace LogicalInduction

open LO.Propositional

namespace PCWorld

/-- A point of Cantor space read as a p.c. world. -/
private def ofBits (b : ℕ → Bool) : PCWorld := fun i => b i = true

/-- Every p.c. world agrees with some Cantor point on every sentence.  Uses Foundation's
atomwise congruence for Boolean evaluation. -/
private lemma exists_bits (v : PCWorld) :
    ∃ b : ℕ → Bool, ∀ φ : Sentence, (ofBits b).Holds φ ↔ v.Holds φ := by
  classical
  refine ⟨fun i => decide (v i), fun φ => ?_⟩
  have hatom : ∀ {a : ℕ}, (ofBits (fun i => decide (v i))) a ↔ v a := by
    intro a; simp [ofBits]
  have := Formula.Boolean.eq_fml_of_eq_atom
    (v := ofBits (fun i => decide (v i))) (u := v) hatom (φ := φ)
  simpa [Holds, Formula.Boolean.models_iff_val] using this

/-- The truth set of a sentence is clopen in Cantor space: each sentence depends on
finitely many atoms, expressed here as a direct induction over the connectives. -/
private lemma isClopen_setOf_holds (φ : Sentence) :
    IsClopen {b : ℕ → Bool | (ofBits b).Holds φ} := by
  induction φ with
  | atom a =>
      have hset : {b : ℕ → Bool | (ofBits b).Holds (Formula.atom a)}
          = (fun b : ℕ → Bool => b a) ⁻¹' {true} := by
        ext b; simp [Holds, ofBits, Formula.Boolean.val]
      rw [hset]
      exact (isClopen_discrete _).preimage (continuous_apply a)
  | falsum =>
      have hset : {b : ℕ → Bool | (ofBits b).Holds Formula.falsum} = (∅ : Set (ℕ → Bool)) := by
        ext b; simp [Holds, Formula.Boolean.val]
      rw [hset]; exact isClopen_empty
  | imp φ ψ ihφ ihψ =>
      have hset : {b : ℕ → Bool | (ofBits b).Holds (φ.imp ψ)}
          = {b : ℕ → Bool | (ofBits b).Holds φ}ᶜ ∪ {b : ℕ → Bool | (ofBits b).Holds ψ} := by
        ext b; simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_compl_iff, Holds,
          Formula.Boolean.val]
        tauto
      rw [hset]; exact ihφ.compl.union ihψ
  | and φ ψ ihφ ihψ =>
      have hset : {b : ℕ → Bool | (ofBits b).Holds (φ.and ψ)}
          = {b : ℕ → Bool | (ofBits b).Holds φ} ∩ {b : ℕ → Bool | (ofBits b).Holds ψ} := by
        ext b; simp [Holds, Formula.Boolean.val]
      rw [hset]; exact ihφ.inter ihψ
  | or φ ψ ihφ ihψ =>
      have hset : {b : ℕ → Bool | (ofBits b).Holds (φ.or ψ)}
          = {b : ℕ → Bool | (ofBits b).Holds φ} ∪ {b : ℕ → Bool | (ofBits b).Holds ψ} := by
        ext b; simp [Holds, Formula.Boolean.val]
      rw [hset]; exact ihφ.union ihψ

/-- A stage's consistency set is closed: a finite intersection of the clopen truth sets. -/
private lemma isClosed_setOf_consistentWith (D : Finset Sentence) :
    IsClosed {b : ℕ → Bool | (ofBits b).ConsistentWith D} := by
  have hset : {b : ℕ → Bool | (ofBits b).ConsistentWith D}
      = ⋂ φ, ⋂ _ : φ ∈ D, {b : ℕ → Bool | (ofBits b).Holds φ} := by
    ext b; simp [ConsistentWith]
  rw [hset]
  exact isClosed_iInter fun φ =>
    isClosed_iInter fun _ => (isClopen_setOf_holds φ).isClosed

end PCWorld

/-- **Propositional compactness for deductive processes.**  If every finite stage of `DP`
admits a propositionally consistent world, one world is consistent with *every* stage.

This is the bridge that lets the growing form of `thm:scon` drop its joint-consistency
premise: its contrapositive turns "no world satisfies the whole growing theory" into a
*single* unsatisfiable stage, which the degenerate branch
(`isLogicalInductor_of_stage_unsatisfiable`) then handles. -/
lemma DeductiveProcess.exists_consistentWithTheory (DP : DeductiveProcess)
    (h : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ∃ v : PCWorld, v.ConsistentWithTheory DP := by
  set t : ℕ → Set (ℕ → Bool) :=
    fun n => {b | (PCWorld.ofBits b).ConsistentWith (DP.D n)} with ht
  have htd : ∀ i, t (i + 1) ⊆ t i := by
    intro i b hb φ hφ; exact hb φ (DP.mono i hφ)
  have htn : ∀ i, (t i).Nonempty := by
    intro i
    obtain ⟨v, hv⟩ := h i
    obtain ⟨b, hb⟩ := PCWorld.exists_bits v
    exact ⟨b, fun φ hφ => (hb φ).2 (hv φ hφ)⟩
  have htcl : ∀ i, IsClosed (t i) := fun i =>
    PCWorld.isClosed_setOf_consistentWith (DP.D i)
  obtain ⟨b, hb⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      t htd htn (htcl 0).isCompact htcl
  exact ⟨PCWorld.ofBits b, fun n => Set.mem_iInter.mp hb n⟩

end LogicalInduction
