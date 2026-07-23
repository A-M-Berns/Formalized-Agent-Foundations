import LogicalInduction.Construction.Witnesses.LUVPresentation

/-!
# A concrete deductive process realizing the LUV threshold presentation (F7, non-vacuity)

`LUVPresentation.lean` derives the LUV world-value interfaces from the premise
`ArithmeticLUVPresentation` (the deductive process reveals the `Θ`-provable threshold literals).
This file discharges the project's **satisfiability bar** (`CLAUDE.md`): it *constructs* a
concrete deductive process `luvThresholdDP` and *proves* `ArithmeticLUVPresentation` for it, so
the Phase-B premise is not vacuous.

The construction mirrors `ComputationSyntax`/`ComputationDP`'s `theoremDP`: a two-tag event
stream (tag `0` = a positive threshold literal, tag `1` = its refutation) whose firing predicate
is `Θ`-provability of the threshold schema instance — recursively enumerable by
`provable_instances_re` — dovetailed into monotone finite stages.  A single fixed world (the
actual standard truth of each threshold predicate) is consistent with every stage, giving
`hworld` non-vacuity.

The **efficient-computability certificate** for this process (the analogue of
`theoremDP_computable`, needed to compile it into an actual `LIA` and obtain fully unconditional
endpoints) is *not* built here; it is the same ~200-line primitive-recursive encoding as the
computation tail and is recorded as remaining work in `notes/next-session.md`.  What is proved
here is exactly what makes the Phase-B derivation non-vacuous.
-/

namespace LogicalInduction

open LO.FirstOrder LO.FirstOrder.Arithmetic

namespace ComputableLUV

variable (L : ComputableLUV) (T : ArithmeticTheory)

/-- The public literal a threshold event contributes: tag `0` asserts `⌜X > r⌝`, tag `1` denies
it. -/
noncomputable def luvEventAtom (e : ℕ) : Sentence :=
  if e.unpair.1 = 0 then LO.Propositional.Formula.atom e.unpair.2
  else ∼ LO.Propositional.Formula.atom e.unpair.2

/-- The `Θ`-provability obligation a threshold event fires on. -/
def luvEventFires (e : ℕ) : Prop :=
  (e.unpair.1 = 0 ∧ T ⊢ L.thresholdSchema/[↑e.unpair.2]) ∨
    (e.unpair.1 = 1 ∧ T ⊢ L.thresholdFailureSchema/[↑e.unpair.2])

lemma luvEventFires_re [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1] :
    REPred (L.luvEventFires T) := by
  have htag : ∀ k : ℕ, REPred (fun e : ℕ => e.unpair.1 = k) := by
    intro k
    exact ComputablePred.to_re
      (Primrec.eq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const k)).computablePred
  have hpos : REPred (fun e : ℕ => T ⊢ L.thresholdSchema/[↑e.unpair.2]) :=
    REPred.comp (Primrec.snd.comp Primrec.unpair).to_comp (provable_instances_re T L.thresholdSchema)
  have hneg : REPred (fun e : ℕ => T ⊢ L.thresholdFailureSchema/[↑e.unpair.2]) :=
    REPred.comp (Primrec.snd.comp Primrec.unpair).to_comp
      (provable_instances_re T L.thresholdFailureSchema)
  exact ((htag 0).and hpos).or ((htag 1).and hneg)

/-- A partial-recursive semi-decider for `luvEventFires`. -/
lemma exists_luvEventCode [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1] :
    ∃ code : Nat.Partrec.Code, ∀ e, (code.eval e).Dom ↔ L.luvEventFires T e := by
  obtain ⟨f, hf, hfP⟩ := REPred.iff'.mp (L.luvEventFires_re T)
  obtain ⟨code, hcode⟩ := Nat.Partrec.Code.exists_code.mp
    (Partrec.nat_iff.mp (hf.map (Computable.const (0 : ℕ)).to₂))
  refine ⟨code, fun e => ?_⟩
  rw [hcode]
  exact (hfP e).symm

open Classical in
/-- Fuel-`k` dovetailer of the fired threshold atoms. -/
noncomputable def luvStage [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1] (k : ℕ) : Finset Sentence :=
  ((Finset.range (k + 1)).filter
      (fun e => (Nat.Partrec.Code.evaln k (L.exists_luvEventCode T).choose e).isSome = true)).image
    (luvEventAtom)

lemma luvStage_mono [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1] (k : ℕ) :
    L.luvStage T k ⊆ L.luvStage T (k + 1) := by
  classical
  intro φ hφ
  simp only [luvStage, Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hφ ⊢
  obtain ⟨e, ⟨he, hsome⟩, rfl⟩ := hφ
  exact ⟨e, ⟨by omega, evaln_isSome_mono (Nat.le_succ k) hsome⟩, rfl⟩

/-- The concrete deductive process enumerating the `Θ`-provable LUV threshold literals. -/
noncomputable def luvThresholdDP [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1] : DeductiveProcess where
  D := L.luvStage T
  mono := L.luvStage_mono T

/-- Coverage: every fired threshold event's atom eventually appears. -/
lemma luvThresholdDP_covers [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
    {e : ℕ} (he : L.luvEventFires T e) :
    ∃ k, luvEventAtom e ∈ (L.luvThresholdDP T).D k := by
  classical
  have hspec := (L.exists_luvEventCode T).choose_spec
  have hdom : ((L.exists_luvEventCode T).choose.eval e).Dom := (hspec e).mpr he
  obtain ⟨out, hout⟩ := Part.dom_iff_mem.mp hdom
  obtain ⟨fuel, hfuel⟩ := Nat.Partrec.Code.evaln_complete.mp hout
  refine ⟨max e fuel, ?_⟩
  simp only [luvThresholdDP, luvStage, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
  exact ⟨e, ⟨by omega, evaln_isSome_mono (le_max_right e fuel)
    (Option.isSome_iff_exists.mpr ⟨out, hfuel⟩)⟩, rfl⟩

/-! ## Non-vacuity: the standard-truth world is consistent with every stage -/

/-- The world believing each threshold atom exactly at its true value (`ThresholdPred`).  Its
negation/positive fibers are pinned by `Θ`'s decidable-threshold soundness. -/
noncomputable def luvWorld : PCWorld := fun m => L.ThresholdPred m

lemma luvWorld_consistent [𝗥₀ ⪯ T] [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
    (k : ℕ) : (L.luvWorld).ConsistentWith ((L.luvThresholdDP T).D k) := by
  classical
  intro φ hφ
  simp only [luvThresholdDP, luvStage, Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hφ
  obtain ⟨e, ⟨_, hsome⟩, rfl⟩ := hφ
  have hfires : L.luvEventFires T e := by
    have hdom : ((L.exists_luvEventCode T).choose.eval e).Dom := by
      obtain ⟨out, hout⟩ := Option.isSome_iff_exists.mp hsome
      exact Part.dom_iff_mem.mpr ⟨out, Nat.Partrec.Code.evaln_sound hout⟩
    exact ((L.exists_luvEventCode T).choose_spec e).mp hdom
  rcases hfires with ⟨htag, hprov⟩ | ⟨htag, hprov⟩
  · -- positive literal: the atom holds because Θ proves the threshold, so it is true
    simp only [luvEventAtom, htag, if_pos, holds_atom]
    show (L.luvWorld) e.unpair.2
    exact (re_complete L.thresholdPred_re).mpr (by simpa using hprov)
  · -- refutation literal: the negated atom holds because Θ proves the failure schema
    simp only [luvEventAtom, htag, if_neg (_root_.one_ne_zero), holds_not, holds_atom]
    show ¬ (L.luvWorld) e.unpair.2
    exact (re_complete L.thresholdPred_compl_re).mpr (by simpa using hprov)

lemma luvWorld_consistentWithTheory [𝗥₀ ⪯ T] [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1] :
    (L.luvWorld).ConsistentWithTheory (L.luvThresholdDP T) :=
  fun k => L.luvWorld_consistent T k

/-- **`hworld` non-vacuity.** Every stage of the constructed process has a consistent world. -/
lemma luvThresholdDP_hworld [𝗥₀ ⪯ T] [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
    (n : ℕ) : ∃ v : PCWorld, v.ConsistentWith ((L.luvThresholdDP T).D n) :=
  ⟨L.luvWorld, L.luvWorld_consistent T n⟩

/-! ## The presentation is satisfiable -/

/-- **F7 non-vacuity payoff.**  The `ArithmeticLUVPresentation` premise of `LUVPresentation.lean`
is *satisfiable*: the constructed process reveals exactly the `Θ`-provable threshold literals. -/
noncomputable def luvArithmeticPresentation [𝗥₀ ⪯ T] [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1] :
    ArithmeticLUVPresentation L (L.luvThresholdDP T) T where
  threshold_enters i r hprov := by
    have he : L.luvEventFires T (Nat.pair 0 (thresholdCode i r)) :=
      Or.inl ⟨by simp, by simpa using hprov⟩
    obtain ⟨k, hk⟩ := L.luvThresholdDP_covers T he
    refine ⟨k, ?_⟩
    simpa [luvEventAtom, thresholdSentence] using hk
  threshold_refutes i r hprov := by
    have he : L.luvEventFires T (Nat.pair 1 (thresholdCode i r)) :=
      Or.inr ⟨by simp, by simpa using hprov⟩
    obtain ⟨k, hk⟩ := L.luvThresholdDP_covers T he
    refine ⟨k, ?_⟩
    simpa [luvEventAtom, thresholdSentence] using hk

end ComputableLUV

end LogicalInduction
