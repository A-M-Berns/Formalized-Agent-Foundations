import LogicalInduction.Construction.LUV.Arithmetic
import LogicalInduction.Construction.Paper.ComputationDP
import LogicalInduction.Properties.ExpectationProperties

/-!
# LUV world-value interfaces, and the `Θ`-provable threshold process

`Framework/Expectations.lean` and `Properties/ExpectationProperties.lean` state the world–value
coherence of logically uncertain variables (`def:luv`) as caller-supplied hypotheses —
`PCWorld.ValuesAt`, `LUVCombination.WorldValued` and `LUVCombination.ExactTheoryPresentation` —
with no arithmetic content behind them.  This module derives all three for the `dd:luv-arith`
certified class of `Construction/LUV/Arithmetic.lean`, whose LUVs are presented by rational
thresholds `num i / den i` over an arithmetic theory representing computations, and then
constructs the `def:dedproc` deductive process that satisfies the one premise the
derivation retains.

## The world-value interfaces

`LUV.tagIndex` recovers a certified LUV's family index from the code of its own threshold atom,
with `toLUV_tagIndex` the retraction on the `toLUV` image.

`ArithmeticLUVPresentation` is the one residual premise: the deductive process reveals the
`Θ`-provable positive threshold literals and the `Θ`-provable refutations.  It is the same
disclosed boundary that `ComputationTheoryPresentation` carries on the halting tail, and it is
stronger than a raw `ExactTheoryPresentation` hypothesis, because threshold truth is pinned by
`Θ`-provability of a decidable predicate rather than assumed.  It is a Tier-2 frozen structure
carrying an `[RepresentsComputations T]` instance binder.

The main result `threshold_holds_iff` collapses the world value: for such a theory every world
consistent with the process holds `⌜X_i > r⌝` exactly when the rational `r` is below the standard
value `num i / den i`, with no nonstandard slack.  What that costs, and why no soundness
instance is taken, is stated at the declaration.

From it come `exactTheoryPresentation_ofArithmetic`, consumed in `Construction/LUV/Endpoints.lean`
through `worldValued_ofArithmetic`, and `valuesAt_ofArithmetic`, the single-LUV form for the
property families that take `PCWorld.ValuesAt` directly.

## The threshold process

`ArithmeticLUVPresentation` is then satisfied by a real object rather than assumed: a two-tag
event stream over `Θ`-provability of the threshold schema instance, where tag `0` publishes
`⌜X > r⌝` and tag `1` its literal negation.  The firing predicate is recursively enumerable
(`provable_instances_re`), and `luvStage` dovetails it into monotone finite stages.  The
objects are `luvEventAtom`, `luvEventFires`, `luvStage`, `luvThresholdDP`, and the two
candidate worlds `luvWorld` and `truthWorld`.

The two tags publish complementary literals over *one* sentence rather than two separate
schemas.  That is what makes consistency of `Θ` alone enough for `luvWorld_consistent`, with no
appeal to standard truth.  `truthWorld` believes each threshold at its true value and is
defined here for `Construction/LUV/Endpoints.lean`'s scheduled-reveal process `gridDP`, which does
need the semantic world.

`luvArithmeticPresentation` (the `ArithmeticLUVPresentation` instance) and
`luvThresholdDP_hworld` (stage-wise non-vacuity) are both consumed by
`Construction/LUV/Endpoints.lean`.
The computability certificate `luvThresholdDP_computable` is built here too: one fixed
partial-recursive program emits the encoded stage `D k` on input `k`, via `luvEventAtom_prim`
and `luvStage_encode_prim`.

## Hypotheses beyond the paper

`[T.Δ₁]` (enumerating `Θ`'s theorems — the README's infrastructure binder) throughout the
process construction, and `[𝗥₀ ⪯ T]` with `[Entailment.Consistent T]` on the world lemmas.
-/

namespace LogicalInduction

open LO.FirstOrder LO.FirstOrder.Arithmetic

namespace ComputableLUV

variable (L : ComputableLUV)

/-! ## Recovering a certified LUV's family index -/

/-- Recover a computable-function LUV's family index from its threshold naming (`gt 0` is the
atom `⌜X_i > 0⌝`, whose code carries `i`).  A LUV outside the `toLUV` image tags to `0`. -/
def _root_.LogicalInduction.LUV.tagIndex (X : LUV) : ℕ :=
  match X.gt 0 with
  | LO.Propositional.Formula.atom m => codeIdx m
  | _ => 0

@[simp] lemma toLUV_tagIndex (i : ℕ) : (toLUV i).tagIndex = i := by
  simp [LUV.tagIndex, toLUV_gt, thresholdSentence, codeIdx_thresholdCode]

/-! ## The DP-reveals-provable-thresholds premise -/

/-- **`ArithmeticLUVPresentation`** — the residual background-theory premise for the LUV tail,
mirroring `ComputationTheoryPresentation`.  It says the deductive process reveals the
`Θ`-provable positive threshold literals and the `Θ`-provable refutations, translating the
first-order threshold schemas into the public propositional threshold atoms.
Paper node: `def:luv` -/
structure _root_.LogicalInduction.ArithmeticLUVPresentation
    (L : ComputableLUV) (DP : DeductiveProcess) (T : ArithmeticTheory)
    [RepresentsComputations T] where
  threshold_enters : ∀ (i : ℕ) (r : ℚ),
    T ⊢ (L.thresholdSchema T)/[‘↑(thresholdCode i r)’] →
      ∃ k, thresholdSentence i r ∈ DP.D k
  threshold_refutes : ∀ (i : ℕ) (r : ℚ),
    T ⊢ ∼((L.thresholdSchema T)/[‘↑(thresholdCode i r)’]) →
      ∃ k, (∼ thresholdSentence i r) ∈ DP.D k

variable {L}

/-! ## The world-value collapse -/

/-- For a theory representing computations whose provable thresholds the process reveals, every
consistent world holds `⌜X_i > r⌝` exactly when `r` is below the standard rational value — the
decidable-threshold discharge of `def:luv`'s world value.  Both directions run on the paper's own
representability premise (`tex:604`); no soundness instance is taken.

The `def:luv` provenance line sits on `ArithmeticLUVPresentation` above, which is the node's
carrier; this collapse is the supporting fact `AxiomAudit.lean` classifies as internal
infrastructure of the `dd:luv-arith` lane, so it carries no provenance line of its own. -/
lemma threshold_holds_iff {DP : DeductiveProcess} {T : ArithmeticTheory}
    [𝗥₀ ⪯ T] [RepresentsComputations T]
    (pres : ArithmeticLUVPresentation L DP T) {v : PCWorld}
    (hv : v.ConsistentWithTheory DP) (i : ℕ) (r : ℚ) :
    v.Holds (thresholdSentence i r) ↔ (r : ℝ) < (L.value i : ℝ) := by
  constructor
  · intro hHolds
    by_contra hcon
    have hnlt : ¬ r < L.value i := fun h => hcon (by exact_mod_cast h)
    obtain ⟨k, hk⟩ := pres.threshold_refutes i r (L.threshold_refutable i r hnlt)
    have hneg : v.Holds (∼ thresholdSentence i r) := hv k _ hk
    rw [PCWorld.holds_neg] at hneg
    exact hneg hHolds
  · intro hlt
    have hltq : r < L.value i := by exact_mod_cast hlt
    obtain ⟨k, hk⟩ := pres.threshold_enters i r (L.threshold_provable i r hltq)
    exact hv k _ hk

/-! ## Deriving `ExactTheoryPresentation`, `WorldValued` and `ValuesAt` -/

/-- **`ExactTheoryPresentation` is derived, not assumed.**  For any LUV-combination
sequence all of whose LUVs are `dd:luv-arith` LUVs, the interface is constructed from the
certified threshold arithmetic and the process-reveals-provable premise, so no caller
supplies it. -/
noncomputable def exactTheoryPresentation_ofArithmetic
    {DP : DeductiveProcess} {T : ArithmeticTheory}
    [𝗥₀ ⪯ T] [RepresentsComputations T]
    (pres : ArithmeticLUVPresentation L DP T)
    (As : ℕ → LUVCombination)
    (hAs : ∀ n, ∀ p ∈ (As n).terms, ∃ i, p.2 = toLUV i) :
    LUVCombination.ExactTheoryPresentation As DP where
  value _ X := (L.value X.tagIndex : ℝ)
  value_mem := by
    intro n p hp
    obtain ⟨i, hi⟩ := hAs n p hp
    simp only [hi, toLUV_tagIndex]
    exact ⟨by exact_mod_cast L.value_nonneg i, by exact_mod_cast L.value_le_one i⟩
  threshold_iff := by
    intro n v hv p hp r
    obtain ⟨i, hi⟩ := hAs n p hp
    simp only [hi, toLUV_tagIndex, toLUV_gt]
    exact threshold_holds_iff pres hv i r

/-- `WorldValued` is likewise derived (through `ExactTheoryPresentation`). -/
lemma worldValued_ofArithmetic
    {DP : DeductiveProcess} {T : ArithmeticTheory}
    [𝗥₀ ⪯ T] [RepresentsComputations T]
    (pres : ArithmeticLUVPresentation L DP T)
    (As : ℕ → LUVCombination)
    (hAs : ∀ n, ∀ p ∈ (As n).terms, ∃ i, p.2 = toLUV i) :
    LUVCombination.WorldValued As DP :=
  (exactTheoryPresentation_ofArithmetic pres As hAs).toWorldValued

/-- Single-LUV `PCWorld.ValuesAt` is derived: a consistent world values `X_i` at its standard
rational value. -/
lemma valuesAt_ofArithmetic
    {DP : DeductiveProcess} {T : ArithmeticTheory}
    [𝗥₀ ⪯ T] [RepresentsComputations T]
    (pres : ArithmeticLUVPresentation L DP T)
    {v : PCWorld} (hv : v.ConsistentWithTheory DP) (i : ℕ) :
    v.ValuesAt (toLUV i) (L.value i : ℝ) := by
  refine ⟨by exact_mod_cast L.value_nonneg i, by exact_mod_cast L.value_le_one i, ?_⟩
  intro r
  rw [toLUV_gt]
  constructor
  · intro hr; exact (threshold_holds_iff pres hv i r).2 hr
  · intro hr hHolds
    have := (threshold_holds_iff pres hv i r).1 hHolds
    exact absurd this (not_lt.mpr (le_of_lt hr))

end ComputableLUV

end LogicalInduction

namespace LogicalInduction

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

namespace ComputableLUV

variable (L : ComputableLUV) (T : ArithmeticTheory)

/-! ## The threshold event stream -/

/-- The public literal a threshold event contributes: tag `0` asserts `⌜X > r⌝`, tag `1` denies
it. -/
noncomputable def luvEventAtom (e : ℕ) : Sentence :=
  if e.unpair.1 = 0 then LO.Propositional.Formula.atom e.unpair.2
  else ∼ LO.Propositional.Formula.atom e.unpair.2

/-- The `Θ`-provability obligation a threshold event fires on.  Tag `1` is the **literal
negation of the same sentence** tag `0` fires on, not a separate complementary schema; that
is what makes the two mutually exclusive under consistency alone. -/
def luvEventFires [RepresentsComputations T] (e : ℕ) : Prop :=
  (e.unpair.1 = 0 ∧ T ⊢ (L.thresholdSchema T)/[↑e.unpair.2]) ∨
    (e.unpair.1 = 1 ∧ T ⊢ ∼((L.thresholdSchema T)/[↑e.unpair.2]))

lemma luvEventFires_re [T.Δ₁] [RepresentsComputations T] :
    REPred (L.luvEventFires T) := by
  have htag : ∀ k : ℕ, REPred (fun e : ℕ => e.unpair.1 = k) := by
    intro k
    exact ComputablePred.to_re
      (Primrec.eq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const k)).computablePred
  have hpos : REPred (fun e : ℕ => T ⊢ (L.thresholdSchema T)/[↑e.unpair.2]) :=
    REPred.comp (Primrec.snd.comp Primrec.unpair).to_comp
      (provable_instances_re T (L.thresholdSchema T))
  have hneg : REPred (fun e : ℕ => T ⊢ ∼((L.thresholdSchema T)/[↑e.unpair.2])) := by
    have h := REPred.comp (Primrec.snd.comp Primrec.unpair).to_comp
      (provable_instances_re T (∼(L.thresholdSchema T)))
    simpa only [LogicalConnective.HomClass.map_neg] using h
  exact ((htag 0).and hpos).or ((htag 1).and hneg)

/-- A partial-recursive semi-decider for `luvEventFires`. -/
lemma exists_luvEventCode [T.Δ₁] [RepresentsComputations T] :
    ∃ code : Nat.Partrec.Code, ∀ e, (code.eval e).Dom ↔ L.luvEventFires T e := by
  obtain ⟨f, hf, hfP⟩ := REPred.iff'.mp (L.luvEventFires_re T)
  obtain ⟨code, hcode⟩ := Nat.Partrec.Code.exists_code.mp
    (Partrec.nat_iff.mp (hf.map (Computable.const (0 : ℕ)).to₂))
  refine ⟨code, fun e => ?_⟩
  rw [hcode]
  exact (hfP e).symm

/-! ## The stages and the process -/

open Classical in
/-- Fuel-`k` dovetailer of the fired threshold atoms. -/
noncomputable def luvStage [T.Δ₁] [RepresentsComputations T] (k : ℕ) : Finset Sentence :=
  ((Finset.range (k + 1)).filter
      (fun e => (Nat.Partrec.Code.evaln k (L.exists_luvEventCode T).choose e).isSome = true)).image
    (luvEventAtom)

lemma luvStage_mono [T.Δ₁] [RepresentsComputations T] (k : ℕ) :
    L.luvStage T k ⊆ L.luvStage T (k + 1) := by
  classical
  intro φ hφ
  simp only [luvStage, Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hφ ⊢
  obtain ⟨e, ⟨he, hsome⟩, rfl⟩ := hφ
  exact ⟨e, ⟨by omega, evaln_isSome_mono (Nat.le_succ k) hsome⟩, rfl⟩

/-- The concrete deductive process enumerating the `Θ`-provable LUV threshold literals. -/
noncomputable def luvThresholdDP [T.Δ₁] [RepresentsComputations T] :
    DeductiveProcess where
  D := L.luvStage T
  mono := L.luvStage_mono T

/-- Coverage: every fired threshold event's atom eventually appears. -/
lemma luvThresholdDP_covers [T.Δ₁] [RepresentsComputations T]
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

/-! ## Worlds consistent with every stage -/

/-- The world believing each threshold atom exactly when `Θ` *proves* it.  No appeal to
standard truth: the two event tags publish complementary literals over one sentence, so
consistency of `Θ` alone keeps this world consistent with every stage. -/
noncomputable def luvWorld [RepresentsComputations T] : PCWorld :=
  fun m => T ⊢ (L.thresholdSchema T)/[‘↑m’]

/-- The world believing each threshold atom at its true value (`ThresholdPred`).  It is the
world `Construction/LUV/Endpoints.lean`'s scheduled-reveal process `gridDP` is consistent with;
`luvThresholdDP` uses `luvWorld` instead, which needs no semantics. -/
noncomputable def truthWorld : PCWorld := fun m => L.ThresholdPred m

lemma luvWorld_consistent [𝗥₀ ⪯ T] [T.Δ₁] [RepresentsComputations T]
    [Entailment.Consistent T]
    (k : ℕ) : (L.luvWorld T).ConsistentWith ((L.luvThresholdDP T).D k) := by
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
  · -- positive literal: the world believes exactly what `Θ` proves
    simp only [luvEventAtom, htag, if_pos, PCWorld.holds_atom]
    exact hprov
  · -- refutation literal: `Θ` cannot also prove the positive one, by consistency
    simp only [luvEventAtom, htag, if_neg (_root_.one_ne_zero), PCWorld.holds_neg, PCWorld.holds_atom]
    intro hpos
    have hpos' : T ⊢ ((L.thresholdSchema T)/[↑e.unpair.2] : ArithmeticSentence) := hpos
    exact (Entailment.Consistent.not_bot (𝓢 := T) inferInstance)
      (by cl_prover [hpos', hprov])

/-- The provability world is consistent with the whole process, not merely with each stage
separately.  `luvThresholdDP_hworld` is the existential form the property tail's `hworld`
obligations take. -/
lemma luvWorld_consistentWithTheory [𝗥₀ ⪯ T] [T.Δ₁] [RepresentsComputations T]
    [Entailment.Consistent T] :
    (L.luvWorld T).ConsistentWithTheory (L.luvThresholdDP T) :=
  fun k => L.luvWorld_consistent T k

/-- **`hworld` non-vacuity.** Every stage of the constructed process has a consistent world. -/
lemma luvThresholdDP_hworld [𝗥₀ ⪯ T] [T.Δ₁] [RepresentsComputations T]
    [Entailment.Consistent T]
    (n : ℕ) : ∃ v : PCWorld, v.ConsistentWith ((L.luvThresholdDP T).D n) :=
  ⟨L.luvWorld T, L.luvWorld_consistent T n⟩

/-! ## The presentation is satisfiable -/

/-- **The presentation is satisfiable.**  The constructed process reveals exactly the
`Θ`-provable threshold literals, so this module's `ArithmeticLUVPresentation`
premise holds of a real object. -/
noncomputable def luvArithmeticPresentation [𝗥₀ ⪯ T] [T.Δ₁] [RepresentsComputations T] :
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

/-! ## Computability of the process -/

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

lemma luvStage_eq_toFinset [T.Δ₁] [RepresentsComputations T]
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

lemma luvStage_encode_prim [T.Δ₁] [RepresentsComputations T] :
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
      cases (Nat.Partrec.Code.evaln p.1 c p.2).isSome <;> simp)
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
emits the encoded stage `D k` on input `k`.

This is the certificate a `_unconditional` form over `liaHistory (luvThresholdDP T)` consumes,
through `LIA_is_logical_inductor`.  No such form exists: `Construction/LUV/Endpoints.lean`'s
`_unconditional` endpoints are stated over the scheduled-reveal process `gridDP`, and its
`luvThresholdDP`-indexed `_arith` endpoints carry `[IsLogicalInductor P (L.luvThresholdDP T)]`
as a caller hypothesis. -/
lemma luvThresholdDP_computable [T.Δ₁] [RepresentsComputations T] :
    ComputableDeductiveProcess (L.luvThresholdDP T) := by
  obtain ⟨code, hcode⟩ := Nat.Partrec.Code.exists_code.mp
    (Nat.Partrec.of_primrec (Primrec.nat_iff.mp (L.luvStage_encode_prim T)))
  refine ⟨code, fun k => ?_⟩
  rw [hcode]
  exact Part.mem_some _

end ComputableLUV

end LogicalInduction
