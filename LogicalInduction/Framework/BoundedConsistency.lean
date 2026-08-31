/-
# Bounded provability, and the paper's finite consistency statements — §4.10

The paper's `Con(Θ′)(ν)` (tex:1855-1866) says

> there is no proof of `⊥` from `⌜Θ′⌝` with `ν` or fewer symbols.

This module supplies the *external* (Lean-side) side of that predicate over Foundation's
internal derivations: bounded provability `BProv`, its decidability, the total computable
ℕ-valued decider the represented lane needs, and the finite-consistency predicate
`conWithin` with the soundness bridge that makes every one of its instances **true** for a
consistent theory.

## What is measured: symbols

The bound is on the derivation's **symbol count**, as the paper says, and it is
**inclusive** (`dSize d ≤ k`), as the paper says.  `Framework/DerivationSize.lean` builds
`dSize`, the symbol count of a Foundation derivation code, by external recursion at
`V := ℕ` — which is the only place §4.10 meters anything — and proves the equations that
tie it to Foundation's own derivation constructors (`dSize_axL`, `dSize_cutRule`, …).

The earlier `dd:proofcode` modelling substitution — metering by the derivation's *Gödel
number* because Foundation exposes no size function — is **retired**.  What is left is a
*convention*, not a substitution: the paper fixes neither a Gödel encoding nor an alphabet
("written in `ℒ` using a Gödel encoding"), so some symbol-counting convention has to be
chosen, and ours is stated in full in `DerivationSize.lean`'s header.  Nothing in this
module depends on the choice beyond `le_G_dSize`.

## Why bounded *provability*, not bounded *consistency*

The represented lane must name the theory.  `conWithin T` is, for a consistent `T`,
extensionally the constant predicate `True`, so a `γ` representing its indicator would name
nothing (the `R5-F08` extensionality trap, `KNOWLEDGE.md`).  What varies with `T`'s theorems
is bounded *provability* with the sentence code in the argument, so that is what is made
computable here: `bprovValue T : ℕ → ℕ` decides `∃ d, Proof T d φ ∧ dSize d ≤ k` at the
packed argument `⟨φ, k⟩`, and the day-`n` Con claim is read off it as the value `0` at
`⟨⌜⊥⌝, f n⟩`.

## How computability is obtained

No proof checker is written.  Foundation's `Bootstrapping.Proof` is `𝚫₁`
(`Proof.definable'`), so the packed proof predicate and its negation are both `𝚺₁` by
`definability`; `re_iff_sigma1` turns each into an r.e. predicate on ℕ and
`ComputablePred.computable_iff_re_compl_re'` turns the pair into a decider.  Foundation's
own arithmetic pairing coincides with Mathlib's at `ℕ` (`nat_pair_eq`), which is what lets
the definable form (stated with `π₁`/`π₂`) and the computable form (stated with
`Nat.pair`/`Nat.unpair`) be the same predicate.

That alone decides `Proof T d φ` for a *given* `d`.  What makes the symbol-metered search
decidable — in both polarities, which is what the total decider needs — is the converse
bound `le_G_dSize : d ≤ G (dSize d)` of `DerivationSize.lean`: a derivation with at most `k`
symbols has code at most `G k`, so the unbounded search over `d` collapses to a bounded one
(`bProv_iff_bounded`).  `dSize d ≤ d` is the useless direction; this is the one that does
the work.
-/
import Foundation.FirstOrder.Incompleteness.First
import Foundation.FirstOrder.Incompleteness.RosserProvability
import Mathlib.Computability.Partrec
import LogicalInduction.Framework.RepresentsComputations
import LogicalInduction.Framework.DerivationSizeComputable

namespace LogicalInduction

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping

variable (T : ArithmeticTheory) [T.Δ₁]

/-! ## Foundation's pairing at `ℕ` is Mathlib's

`nat_pair_eq` gives the forward identity; the projections follow from it and
`pair_unpair`. -/

lemma pi₁_nat (z : ℕ) : π₁ z = z.unpair.1 := by
  have h : Nat.pair (π₁ z) (π₂ z) = z := by rw [← nat_pair_eq]; simp
  conv_rhs => rw [← h]
  simp

lemma pi₂_nat (z : ℕ) : π₂ z = z.unpair.2 := by
  have h : Nat.pair (π₁ z) (π₂ z) = z := by rw [← nat_pair_eq]; simp
  conv_rhs => rw [← h]
  simp

/-! ## The proof predicate is computable

Not the *search* — a single `Proof T d φ`, at the packed pair.  Everything metered is built
on top of this. -/

/-- Foundation's internal proof predicate at a packed argument `⟨d, φcode⟩`, spelled with
Foundation's own arithmetic pairing so that `definability` can see through it. -/
def ProofPacked (z : ℕ) : Prop := Bootstrapping.Proof (V := ℕ) T (π₁ z) (π₂ z)

/-- `Proof` is `𝚫₁`, so the packed form is `𝚺₁`.

Kind `P` (proved).  Provenance: (b) Foundation citations — `Proof.definable'`,
`pi₁_definable`, `pi₂_definable`. -/
lemma proofPacked_sigmaOne : 𝚺₁-Predicate (ProofPacked T) := by
  unfold ProofPacked; definability

/-- …and so is its negation, `Proof` being `𝚫₁`. -/
lemma not_proofPacked_sigmaOne : 𝚺₁-Predicate (fun z => ¬ ProofPacked T z) := by
  unfold ProofPacked; definability

/-- **The proof predicate is decidable.**  Both polarities are r.e. by `re_iff_sigma1`, and
a predicate r.e. together with its complement is computable.

Kind `C` (composition).  Provenance: (b) Foundation citation — `re_iff_sigma1`;
Mathlib citation — `ComputablePred.computable_iff_re_compl_re'`. -/
lemma proofPacked_computable : ComputablePred (ProofPacked T) :=
  ComputablePred.computable_iff_re_compl_re'.mpr
    ⟨re_iff_sigma1.mpr (proofPacked_sigmaOne T), re_iff_sigma1.mpr (not_proofPacked_sigmaOne T)⟩

lemma proofPacked_iff (z : ℕ) :
    ProofPacked T z ↔ Bootstrapping.Proof (V := ℕ) T z.unpair.1 z.unpair.2 := by
  simp [ProofPacked, pi₁_nat, pi₂_nat]

lemma proofPacked_pair_iff (d φcode : ℕ) :
    ProofPacked T (Nat.pair d φcode) ↔ Bootstrapping.Proof (V := ℕ) T d φcode := by
  simp [proofPacked_iff]

/-! ## Bounded provability -/

/-- **Bounded provability.**  Some `T`-derivation of the sentence coded by `φcode` has at
most `k` symbols.  The bound is **inclusive**, matching the paper's "`ν` or fewer
symbols". -/
def BProv (φcode k : ℕ) : Prop :=
  ∃ d, Bootstrapping.Proof (V := ℕ) T d φcode ∧ dSize d ≤ k

/-- **The search is bounded.**  A derivation of at most `k` symbols has code at most `G k`,
so the unbounded existential is a finite search — which is what makes `BProv` decidable in
*both* polarities, and hence the day's decider total.

Kind `C` (composition).  Provenance: (a) derived in-project from `le_G_dSize` and
`G_mono`. -/
lemma bProv_iff_bounded (φcode k : ℕ) :
    BProv T φcode k ↔ ∃ d ≤ G k, Bootstrapping.Proof (V := ℕ) T d φcode ∧ dSize d ≤ k := by
  constructor
  · rintro ⟨d, hd, hs⟩
    exact ⟨d, le_trans (le_G_dSize d) (G_mono hs), hd, hs⟩
  · rintro ⟨d, -, hd, hs⟩
    exact ⟨d, hd, hs⟩

/-- `BProv` at a single packed argument `⟨φcode, k⟩`. -/
def BProvPacked (z : ℕ) : Prop := BProv T z.unpair.1 z.unpair.2

lemma bProvPacked_iff (z : ℕ) : BProvPacked T z ↔ BProv T z.unpair.1 z.unpair.2 := Iff.rfl

/-! ## The ℕ-valued decider -/

open Classical in
/-- **The bounded-provability decider.**  `1` when the sentence coded by `z.unpair.1` has a
`T`-derivation of at most `z.unpair.2` symbols, else `0`.  Total, and — the point of the
design — its extension varies with `T`'s theorems, because the sentence code is an
*argument*. -/
noncomputable def bprovValue (z : ℕ) : ℕ := if BProvPacked T z then 1 else 0

/-- The decider is computable: the bounded search of `bProv_iff_bounded` runs over a
computable predicate (`proofPacked_computable`, `dSize_computable`) with a computable bound
(`G_computable`).

Kind `C` (composition).  Provenance: (a) derived in-project. -/
lemma bprovValue_computable : Computable (bprovValue T) := by
  classical
  obtain ⟨_, hc⟩ := proofPacked_computable T
  have hproof : Computable fun x : ℕ × ℕ =>
      decide (Bootstrapping.Proof (V := ℕ) T x.2 x.1.unpair.1) := by
    have := hc.comp (Primrec₂.natPair.to_comp.comp Computable.snd
      ((Primrec.fst.comp Primrec.unpair).to_comp.comp Computable.fst))
    refine this.of_eq fun x => ?_
    simp [proofPacked_pair_iff]
  -- `PrimrecRel` packages its own `Decidable` instance existentially, so `nat_le` has to be
  -- re-decided at the ambient instance before it composes.
  have hle : Computable fun q : ℕ × ℕ => decide (q.1 ≤ q.2) :=
    (PrimrecPred.decide Primrec.nat_le).to_comp
  have hsize : Computable fun x : ℕ × ℕ => decide (dSize x.2 ≤ x.1.unpair.2) :=
    hle.comp (Computable.pair (dSize_computable.comp Computable.snd)
      ((Primrec.snd.comp Primrec.unpair).to_comp.comp Computable.fst))
  have hp : Computable fun x : ℕ × ℕ =>
      decide (Bootstrapping.Proof (V := ℕ) T x.2 x.1.unpair.1 ∧ dSize x.2 ≤ x.1.unpair.2) := by
    have hand := (Primrec.dom_bool₂ (fun a b => a && b)).to_comp.comp hproof hsize
    refine hand.of_eq fun x => ?_
    by_cases h1 : Bootstrapping.Proof (V := ℕ) T x.2 x.1.unpair.1 <;>
      by_cases h2 : dSize x.2 ≤ x.1.unpair.2 <;> simp [h1, h2]
  have hb : Computable fun a : ℕ => G a.unpair.2 :=
    G_computable.comp (Primrec.snd.comp Primrec.unpair).to_comp
  refine (computable_boundedSearchValue
    (p := fun z d => Bootstrapping.Proof (V := ℕ) T d z.unpair.1 ∧ dSize d ≤ z.unpair.2)
    hp hb).of_eq fun z => ?_
  unfold bprovValue
  by_cases h : BProvPacked T z
  · rw [if_pos ((bProv_iff_bounded T _ _).mp h), if_pos h]
  · rw [if_neg (fun hc' => h ((bProv_iff_bounded T _ _).mpr hc')), if_neg h]

@[simp] lemma bprovValue_eq_zero_iff (z : ℕ) : bprovValue T z = 0 ↔ ¬ BProvPacked T z := by
  unfold bprovValue; split <;> simp_all

@[simp] lemma bprovValue_eq_one_iff (z : ℕ) : bprovValue T z = 1 ↔ BProvPacked T z := by
  unfold bprovValue; split <;> simp_all

/-! ## Finite consistency -/

/-- **The paper's `Con(T)(k)`**: no `T`-derivation of `⊥` has `k` or fewer symbols. -/
def conWithin (k : ℕ) : Prop := ¬ BProv T ⌜(⊥ : ArithmeticSentence)⌝ k

set_option maxHeartbeats 1000000 in
/-- **Soundness of the internal proof predicate at the standard model.**  A standard
derivation code witnessing `Proof T d ⌜φ⌝` is an actual `T`-proof of `φ`.

Kind `C` (composition).  Provenance: (b) Foundation citation —
`Bootstrapping.provable_of_standard_proof`. -/
lemma provable_of_bProv_witness (φ : ArithmeticSentence) {d : ℕ}
    (h : Bootstrapping.Proof (V := ℕ) T d ⌜φ⌝) : T ⊢ φ := by
  refine Bootstrapping.provable_of_standard_proof (V := ℕ) (n := d) ?_
  simpa [Nat.cast_id] using h

/-- **Every finite consistency statement about a consistent theory is true.**  This is the
truth premise of `thm:pac`, and it needs nothing but consistency: a derivation of `⊥` with
some symbol count is still a derivation of `⊥`.  In particular it is independent of the
symbol-counting convention.

Kind `P` (proved).  Provenance: (a) derived in-project; (b) Foundation citation —
`Bootstrapping.provable_of_standard_proof`. -/
lemma conWithin_of_consistent (hcon : Entailment.Consistent T) (k : ℕ) : conWithin T k := by
  rintro ⟨d, hd, -⟩
  exact Entailment.Consistent.not_bot hcon (provable_of_bProv_witness T ⊥ hd)

/-- Finite consistency is antitone in the bound: trusting `T` for longer is a stronger
claim. -/
lemma conWithin_anti {k k' : ℕ} (h : k ≤ k') : conWithin T k' → conWithin T k := by
  rintro hk ⟨d, hp, hs⟩
  exact hk ⟨d, hp, le_trans hs h⟩

/-! ## The universal bounded-provability decider at a horizon

The function actually represented by the §4.10 endpoints.  It takes a packed
`⟨φcode, day⟩`, evaluates the horizon `f` at the day *inside* — `f` may grow as fast as it
likes, and is never written out — and decides whether `φcode` has a `T`-derivation of at
most `f day` symbols.  It mentions no particular sentence, so one `γ` serves every day and
every claim at that horizon; the sentence `⌜⊥⌝` enters only through the *argument*. -/

/-- **The universal bounded-provability decider at horizon `f`.** -/
noncomputable def conRunValue (f : ℕ → ℕ) (z : ℕ) : ℕ :=
  bprovValue T (Nat.pair z.unpair.1 (f z.unpair.2))

/-- Total computable whenever the horizon is, which is all `RepresentsComputations` needs.

Kind `C` (composition).  Provenance: (a) derived in-project. -/
lemma conRunValue_computable {f : ℕ → ℕ} (hf : Computable f) :
    Computable (conRunValue T f) :=
  (bprovValue_computable T).comp
    (Primrec₂.natPair.to_comp.comp
      (Primrec.fst.comp Primrec.unpair).to_comp
      (hf.comp (Primrec.snd.comp Primrec.unpair).to_comp))

lemma conRunValue_pair_eq_zero_iff (f : ℕ → ℕ) (φ n : ℕ) :
    conRunValue T f (Nat.pair φ n) = 0 ↔ ¬ BProv T φ (f n) := by
  simp [conRunValue, BProvPacked]

lemma conRunValue_pair_eq_one_iff (f : ℕ → ℕ) (φ n : ℕ) :
    conRunValue T f (Nat.pair φ n) = 1 ↔ BProv T φ (f n) := by
  simp [conRunValue, BProvPacked]

/-- **The value the paper's day-`n` Con claim asserts.**  At the argument naming `⊥` and the
day, the decider is `0` — for a consistent `T`, on every day, at every horizon. -/
lemma conRunValue_bot_eq_zero {f : ℕ → ℕ} (hcon : Entailment.Consistent T) (n : ℕ) :
    conRunValue T f (Nat.pair ⌜(⊥ : ArithmeticSentence)⌝ n) = 0 :=
  (conRunValue_pair_eq_zero_iff T f _ n).mpr (conWithin_of_consistent T hcon (f n))

/-! ## Unbounded provability, and the paper's inconsistency statement

`thm:pac`/`thm:pazfc` are about the *bounded* family above.  `thm:incons` is about the
paper's `⌜Θ′⌝ is inconsistent` (tex:1863-1866), which is the **negation of the universal
generalization** of `Con(Θ′)(ν)` — that is, the unbounded `∃ν: there is a proof of ⊥ from
⌜Θ′⌝ with ν or fewer symbols`.  Nothing is metered there, so no horizon and no choice of
measure enters: the existential ranges over *all* proofs either way, and the two readings
are the same predicate.

Foundation already carries that predicate — `Bootstrapping.Provable T : ℕ → Prop`, literally
`∃ d, Proof T d φcode` — with both bridges this development needs, so nothing is built here
beyond naming it and recording the deduction-theorem reduction.

**Why a deduction family.**  The paper quantifies over an e.c. sequence of arbitrary
recursively axiomatizable theories.  Foundation's `Derivation T` takes `T` as a *meta*
parameter (through `(construction T).Fixpoint`), so there is no uniform-in-theory-code
derivability predicate to represent, and a sequence of theories cannot enter a single
sentence as an argument.  The honest restriction is the deduction family
`Θ′ₙ := Θ₀ ∪ {σₙ}` for a fixed Δ₁ base `Θ₀`: by the deduction theorem `Θ′ₙ` is inconsistent
exactly when `Θ₀ ⊢ ∼σₙ`, which *is* uniform in the code `⌜∼σₙ⌝`, so the day-`n` theory can be
named by that code inside the sentence.  This is a disclosed paraphrase of the paper's
generality, not a hidden one. -/

/-- **`T`-provability of the sentence with code `φcode`.**  Foundation's internal provability
predicate at the standard model, named here for readability: at `φcode = ⌜∼σ⌝` it says
exactly that `T ∪ {σ}` is inconsistent (`not_consistent_adjoin_iff`). -/
def ProvableCode (φcode : ℕ) : Prop := Bootstrapping.Provable (V := ℕ) T φcode

/-- Internal provability is `𝚺₁`, hence r.e. — which is all `codeOfREPred` consumes.

Kind `C` (composition).  Provenance: (b) Foundation citations —
`Bootstrapping.Provable.definable`, `re_iff_sigma1`. -/
lemma provableCode_re : REPred (ProvableCode T) :=
  re_iff_sigma1.mpr (by unfold ProvableCode; infer_instance)

/-- **Internal and external provability agree at a standard code**, in both directions.  The
forward direction is soundness of the internal proof predicate; the backward direction is the
arithmetization of an actual derivation, and is what supplies a proof *code* from a proof.

Kind `C` (composition).  Provenance: (b) Foundation citation —
`Bootstrapping.provable_iff_provable`. -/
@[simp] lemma provableCode_quote_iff (φ : ArithmeticSentence) :
    ProvableCode T ⌜φ⌝ ↔ T ⊢ φ :=
  Bootstrapping.provable_iff_provable

omit [T.Δ₁] in
/-- **The deduction-theorem reduction.**  `T ∪ {σ}` is inconsistent exactly when `T` refutes
`σ`.  This is what makes the day-`n` theory of a deduction family nameable by one sentence
code.

Kind `C` (composition).  Provenance: (b) Foundation citations —
`Entailment.not_consistent_iff_inconsistent`, `Entailment.inconsistent_iff_provable_bot`,
`Entailment.deduction_iff`, `Entailment.N!_iff_CO!`. -/
lemma not_consistent_adjoin_iff (σ : ArithmeticSentence) :
    ¬Entailment.Consistent (σ ∷ T) ↔ T ⊢ ∼σ := by
  rw [Entailment.not_consistent_iff_inconsistent, Entailment.inconsistent_iff_provable_bot,
    Entailment.deduction_iff, ← LO.Entailment.N!_iff_CO!]

/-- **The inconsistency of the day-`n` theory, read off one sentence code.**  Combining the
two bridges: `Θ₀ ∪ {σ}` is inconsistent exactly when `⌜∼σ⌝` is internally `Θ₀`-provable. -/
lemma provableCode_neg_iff_not_consistent_adjoin (σ : ArithmeticSentence) :
    ProvableCode T ⌜∼σ⌝ ↔ ¬Entailment.Consistent (σ ∷ T) := by
  rw [provableCode_quote_iff, not_consistent_adjoin_iff]

/-- `⊤` is provable in every theory, so the provability predicate is not constantly false. -/
lemma provableCode_quote_verum : ProvableCode T ⌜(⊤ : ArithmeticSentence)⌝ := by
  simp

/-- `⊥` is not provable in a consistent theory, so the provability predicate is not
constantly true.  With the previous lemma this is what makes the `thm:incons` schema
genuinely argument-sensitive. -/
lemma not_provableCode_quote_falsum (hcon : Entailment.Consistent T) :
    ¬ ProvableCode T ⌜(⊥ : ArithmeticSentence)⌝ := by
  simpa using Entailment.Consistent.not_bot hcon

-- The symbol-measure computability layer, printed here so the §4.10 substrate's axiom
-- accounting is in one place.
#print axioms dSize_computable
#print axioms sSize_computable
#print axioms fSize_computable
#print axioms tSize_computable
#print axioms G_computable
#print axioms computable_boundedSearchValue

#print axioms proofPacked_computable
#print axioms bprovValue_computable
#print axioms conWithin_of_consistent
#print axioms conRunValue_computable
#print axioms conRunValue_bot_eq_zero
#print axioms provableCode_re
#print axioms not_consistent_adjoin_iff

end LogicalInduction
