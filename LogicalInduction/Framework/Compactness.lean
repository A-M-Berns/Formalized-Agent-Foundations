import LogicalInduction.Framework.Criterion
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.Order

/-!
# Compactness — one world for the whole deductive process

Propositional compactness in the exact form the criterion consumes: if every finite stage
of a deductive process has a propositionally consistent world, then a *single* world is
consistent with every stage (`PCWorld.ConsistentWithTheory`).

The route is Cantor space, not a proof calculus. A `PCWorld` is an atom valuation
`ℕ → Prop` read through Foundation's Boolean evaluation, so it is a point of `ℕ → Bool` up
to atomwise equality (`PCWorld.exists_bits`). For each sentence `φ` the truth set
`{b | (ofBits b).Holds φ}` is clopen — by induction on the connectives, atoms being
preimages of clopens under coordinate projections (`PCWorld.isClopen_setOf_holds`) — hence
each stage's consistency set is a finite intersection of clopens, so closed
(`PCWorld.isClosed_setOf_consistentWith`). The stage sets are nested and nonempty by
hypothesis, and `ℕ → Bool` is compact (Tychonoff over the finite discrete `Bool`), so
Cantor's intersection theorem supplies a point of every stage set at once.

Two endpoints come out:

* `DeductiveProcess.exists_consistentWithTheory` — one world consistent with every stage.
  It is what lets the growing form of `thm:scon` be stated with no joint-consistency
  premise; the explanation is at the lemma.
* `DeductiveProcess.exists_stage_entails` — the finite-consequence form: a semantic
  consequence of the completed theory is already forced by one finite stage. Consumed by
  `Properties/FinitePerturbationCounterexample.lean` to close the settlement gap in the
  `thm:ifp` refutation.

Kind `P`; hypotheses `(a)` (Mathlib's Cantor intersection theorem and Foundation's atomwise
evaluation congruence — provenance `(b)` citations). The module is infrastructure and
carries no paper node of its own.
-/

namespace LogicalInduction

open LO.Propositional

namespace PCWorld

/-! ## Worlds as points of Cantor space -/

/-- A point of Cantor space read as a p.c. world. -/
def ofBits (b : ℕ → Bool) : PCWorld := fun i => b i = true

/-- Every p.c. world agrees with some Cantor point on every sentence.  Uses Foundation's
atomwise congruence for Boolean evaluation. -/
lemma exists_bits (v : PCWorld) :
    ∃ b : ℕ → Bool, ∀ φ : Sentence, (ofBits b).Holds φ ↔ v.Holds φ := by
  classical
  refine ⟨fun i => decide (v i), fun φ => ?_⟩
  have hatom : ∀ {a : ℕ}, (ofBits (fun i => decide (v i))) a ↔ v a := by
    intro a; simp [ofBits]
  have := Formula.Boolean.eq_fml_of_eq_atom
    (v := ofBits (fun i => decide (v i))) (u := v) hatom (φ := φ)
  simpa [Holds, Formula.Boolean.models_iff_val] using this

/-! ## Truth sets are clopen -/

/-- The truth set of a sentence is clopen in Cantor space: each sentence depends on
finitely many atoms, expressed here as a direct induction over the connectives. -/
lemma isClopen_setOf_holds (φ : Sentence) :
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
lemma isClosed_setOf_consistentWith (D : Finset Sentence) :
    IsClosed {b : ℕ → Bool | (ofBits b).ConsistentWith D} := by
  have hset : {b : ℕ → Bool | (ofBits b).ConsistentWith D}
      = ⋂ φ, ⋂ _ : φ ∈ D, {b : ℕ → Bool | (ofBits b).Holds φ} := by
    ext b; simp [ConsistentWith]
  rw [hset]
  exact isClosed_iInter fun φ =>
    isClosed_iInter fun _ => (isClopen_setOf_holds φ).isClosed

end PCWorld

/-! ## Compactness for deductive processes -/

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
    fun n => {b | (PCWorld.ofBits b).ConsistentWith (DP.D n)}
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

/-- A semantic consequence of the completed theory is already forced by one finite stage.

This is the finite-consequence form of propositional compactness.  It is useful when a
computable construction can decide finite-stage entailment: a search over stages then
eventually discovers every consequence of the completed theory. -/
lemma DeductiveProcess.exists_stage_entails (DP : DeductiveProcess) (phi : Sentence)
    (h : ∀ v : PCWorld, v.ConsistentWithTheory DP → v.Holds phi) :
    ∃ k, ∀ v : PCWorld, v.ConsistentWith (DP.D k) → v.Holds phi := by
  classical
  by_contra hstage
  push Not at hstage
  set t : ℕ → Set (ℕ → Bool) := fun n =>
    {b | (PCWorld.ofBits b).ConsistentWith (DP.D n) ∧
      ¬ (PCWorld.ofBits b).Holds phi}
  have htd : ∀ i, t (i + 1) ⊆ t i := by
    intro i b hb
    exact ⟨fun psi hpsi => hb.1 psi (DP.mono i hpsi), hb.2⟩
  have htn : ∀ i, (t i).Nonempty := by
    intro i
    obtain ⟨v, hvD, hvphi⟩ := hstage i
    obtain ⟨b, hb⟩ := PCWorld.exists_bits v
    exact ⟨b, (fun psi hpsi => (hb psi).2 (hvD psi hpsi)), fun hphi => hvphi ((hb phi).1 hphi)⟩
  have htcl : ∀ i, IsClosed (t i) := by
    intro i
    have hset : t i =
        {b : ℕ → Bool | (PCWorld.ofBits b).ConsistentWith (DP.D i)} ∩
          {b : ℕ → Bool | (PCWorld.ofBits b).Holds phi}ᶜ := by
      ext b
      simp [t]
    rw [hset]
    exact (PCWorld.isClosed_setOf_consistentWith (DP.D i)).inter
      (PCWorld.isClopen_setOf_holds phi).compl.isClosed
  obtain ⟨b, hb⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      t htd htn (htcl 0).isCompact htcl
  have hb0 : ∀ n, b ∈ t n := fun n => Set.mem_iInter.mp hb n
  exact (hb0 0).2 (h (PCWorld.ofBits b) (fun n => (hb0 n).1))

end LogicalInduction
