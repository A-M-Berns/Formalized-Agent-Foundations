import LogicalInduction.Construction.Witnesses.LUVPresentation

/-!
# A concrete deductive process realizing the LUV threshold presentation (F7, non-vacuity)

`LUVPresentation.lean` derives the LUV world-value interfaces from the premise
`ArithmeticLUVPresentation` (the deductive process reveals the `Θ`-provable threshold literals).
This file discharges the project's **satisfiability bar** (`CLAUDE.md`): it *constructs* a
concrete deductive process `luvThresholdDP` and *proves* `ArithmeticLUVPresentation` for it, so
that premise is satisfied by a real object rather than assumed.

The construction mirrors `ComputationSyntax`/`ComputationDP`'s `theoremDP`: a two-tag event
stream (tag `0` = a positive threshold literal, tag `1` = its refutation) whose firing predicate
is `Θ`-provability of the threshold schema instance — recursively enumerable by
`provable_instances_re` — dovetailed into monotone finite stages.  A single fixed world (the
actual standard truth of each threshold predicate) is consistent with every stage, giving
`hworld` non-vacuity.

The **computability certificate** for this process is also built here
(`luvThresholdDP_computable`, the analogue of `theoremDP_computable`), which is what lets
`LUVExpectationCertified.lean` compile it into the concrete inductor and obtain the fully
unconditional certified-LUV endpoints.
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

/-! ## Efficient computability of the threshold process -/

/-- `luvEventAtom` is primitive recursive: a two-way tag split into fixed atom/negated-atom
Gödel-code pairings. -/
lemma luvEventAtom_prim : Primrec (fun e : ℕ => luvEventAtom e) := by
  apply Primrec.encode_iff.mp
  have hz : Primrec (fun e : ℕ => e.unpair.2) := Primrec.snd.comp Primrec.unpair
  have htag : Primrec (fun e : ℕ => e.unpair.1) := Primrec.fst.comp Primrec.unpair
  have encA : Primrec (fun e : ℕ => Nat.pair 1 e.unpair.2 + 1) :=
    Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 1) hz)
  have encN : Primrec (fun e : ℕ =>
      Nat.pair 2 (Nat.pair (Nat.pair 1 e.unpair.2 + 1) (Nat.pair 0 0 + 1)) + 1) :=
    Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 2)
      (Primrec₂.natPair.comp
        (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 1) hz))
        (Primrec.const (Nat.pair 0 0 + 1))))
  refine (Primrec.ite (Primrec.eq.comp htag (Primrec.const 0)) encA encN).of_eq ?_
  intro e
  by_cases h : e.unpair.1 = 0
  · simp [luvEventAtom, h, encode_atom]
  · simp [luvEventAtom, h, encode_negAtom]

lemma luvStage_eq_toFinset [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
    (c : Nat.Partrec.Code) (k : ℕ) :
    ((Finset.range (k + 1)).filter
        (fun e => (Nat.Partrec.Code.evaln k c e).isSome = true)).image luvEventAtom =
      ((List.range (k + 1)).filterMap
        (fun e => if (Nat.Partrec.Code.evaln k c e).isSome = true then some (luvEventAtom e)
          else none)).toFinset := by
  classical
  ext φ
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range,
    List.mem_toFinset, List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨e, ⟨he, hsome⟩, rfl⟩
    exact ⟨e, he, by rw [if_pos hsome]⟩
  · rintro ⟨e, he, hcond⟩
    by_cases hs : (Nat.Partrec.Code.evaln k c e).isSome = true
    · rw [if_pos hs] at hcond
      exact ⟨e, ⟨he, hs⟩, Option.some_inj.mp hcond⟩
    · rw [if_neg hs] at hcond; exact absurd hcond (by simp)

lemma luvStage_encode_prim [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1] :
    Primrec (fun k => Encodable.encode (L.luvStage T k)) := by
  set c := (L.exists_luvEventCode T).choose with hc
  have hevaln : Primrec (fun p : ℕ × ℕ => (Nat.Partrec.Code.evaln p.1 c p.2).isSome) :=
    Primrec.option_isSome.comp
      (Nat.Partrec.Code.primrec_evaln.comp
        ((Primrec.fst.pair (Primrec.const c)).pair Primrec.snd))
  have hguncur : Primrec (fun p : ℕ × ℕ =>
      if (Nat.Partrec.Code.evaln p.1 c p.2).isSome = true then some (luvEventAtom p.2)
        else (none : Option Sentence)) := by
    have hb : Primrec (fun p : ℕ × ℕ =>
        bif (Nat.Partrec.Code.evaln p.1 c p.2).isSome then some (luvEventAtom p.2)
          else (none : Option Sentence)) :=
      Primrec.cond hevaln (Primrec.option_some.comp (luvEventAtom_prim.comp Primrec.snd))
        (Primrec.const (none : Option Sentence))
    exact hb.of_eq (fun p => by
      cases hbb : (Nat.Partrec.Code.evaln p.1 c p.2).isSome <;> simp [hbb])
  have hlist : Primrec (fun k : ℕ => (List.range (k + 1)).filterMap
      (fun e => if (Nat.Partrec.Code.evaln k c e).isSome = true then some (luvEventAtom e)
        else none)) :=
    Primrec.listFilterMap (Primrec.list_range.comp Primrec.succ) hguncur.to₂
  have hkey : (fun k => Encodable.encode (L.luvStage T k)) =
      (fun k => Encodable.encode
        ((sentenceDedup ((List.range (k + 1)).filterMap
          (fun e => if (Nat.Partrec.Code.evaln k c e).isSome = true then some (luvEventAtom e)
            else none))).insertionSort sentenceCodeLE)) := by
    funext k
    rw [show L.luvStage T k = ((Finset.range (k + 1)).filter
        (fun e => (Nat.Partrec.Code.evaln k c e).isSome = true)).image luvEventAtom from rfl,
      luvStage_eq_toFinset T c k, encode_toFinset_eq]
  rw [hkey]
  exact Primrec.encode.comp (sentenceInsertionSort_prim.comp (sentenceDedup_prim.comp hlist))

/-- **The scheduled provability process is computable.**  One fixed partial-recursive program
emits the encoded stage `D k` on input `k`. -/
lemma luvThresholdDP_computable [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1] :
    ComputableDeductiveProcess (L.luvThresholdDP T) := by
  obtain ⟨code, hcode⟩ := Nat.Partrec.Code.exists_code.mp
    (Nat.Partrec.of_primrec (Primrec.nat_iff.mp (L.luvStage_encode_prim T)))
  refine ⟨code, fun k => ?_⟩
  rw [hcode]
  exact Part.mem_some _

end ComputableLUV

end LogicalInduction
