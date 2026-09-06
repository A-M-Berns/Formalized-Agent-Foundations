import LogicalInduction.Framework.ROI
import LogicalInduction.Framework.Compactness

/-!
# Boolean worlds: finite-support payouts and product-space compactness

The Boolean reading of the §2 world type, and the compactness facts about it that §4 proof
technology consumes.

## Atom occurrence

`sentenceAtomCodes` is the finite set of atom indices a sentence mentions, and
`PCWorld.holds_congr_atomCodes` the substitution lemma that a world's verdict depends only on
them. Every freshness condition in `Construction/` — a tag namespace an emitted sentence must
avoid — is stated against this set.

## Boolean worlds

`BoolPCWorld` is `ℕ → Bool` with `toPCWorld` / `ofPCWorld` bridging it to `PCWorld`, and
`eval` the Boolean evaluation of a `Sentence` under it. `atomBound` is one above the largest
atom index a sentence mentions, which is the finite support bound every executable payout
check needs. `FiniteWorld B = Fin B → Bool` is the finite, computably enumerable restriction,
with `FiniteWorld.payoutRat` its exact rational payout; `eval_toBoolPCWorld_restrict` and
`FiniteWorld.payoutRat_restrict_ofPCWorld` are the transports that reduce a universal check
over all worlds to one over `FiniteWorld B`.

`bitsWorld` and `bitsPayoutRat` are the non-dependent cousins, and they exist for compilation
rather than for the mathematics: `BoolPCWorld` is a function type and admits no `Primcodable`
instance, so `Primrec (eval v)` cannot even be stated for a world `v`. Routing through a
`List Bool` keeps every compiled quantity a function of `Primcodable` arguments
(`List Bool × Sentence`), with the world appearing only as a beta-reduced intermediate.

## Compactness in the product space

`continuous_eval` is the bridge: evaluation of a fixed sentence depends continuously on its
finitely many atoms, so model sets are clopen (`isClopen_holds`), stagewise plausibility is
closed (`isClosed_consistentWith`), and affine sublevel sets are closed
(`isClosed_affineValue_le`). `eventually_affineValue_gt_of_theory` is the uniform form §4.5
needs: a strict bound holding in every completed-theory world holds in every plausible world
from some finite stage on, by a compact-product argument over
`affineCompactConstraint`. `exists_consistentWithTheory` is the §4-local spelling of
`DeductiveProcess.exists_consistentWithTheory` (`Framework/Compactness.lean`).

The toolkit is consumed by `Properties/Support/SettlementDecision.lean` (the finite-world
settlement tests) and by `Properties/{AffineCoherence,LimitCoherence}.lean` and
`Construction/Statistics/{SettlementClock,HistoricalMaturity}.lean`.
-/

namespace LogicalInduction

open Filter Topology

/-! ## Atom occurrence

Foundation's `Formula` carries no occurrence function, so the two facts a freshness condition
on atoms needs are proved here: the finite set of atoms of a sentence, and the substitution
lemma saying a world's verdict depends only on those.  `BoolPCWorld.atomBound` below is the
numeric form of the same information — one above the largest index in this set. -/

section AtomCodes

open LO.Propositional

/-- The atom indices occurring in a propositional sentence. -/
def sentenceAtomCodes : Sentence → Finset ℕ :=
  Formula.rec' ∅ (fun a => {a})
    (fun _ _ s t => s ∪ t) (fun _ _ s t => s ∪ t) (fun _ _ s t => s ∪ t)

@[simp] lemma sentenceAtomCodes_atom (a : ℕ) :
    sentenceAtomCodes (Formula.atom a) = {a} := rfl

@[simp] lemma sentenceAtomCodes_falsum :
    sentenceAtomCodes (⊥ : Sentence) = ∅ := rfl

@[simp] lemma sentenceAtomCodes_imp (φ ψ : Sentence) :
    sentenceAtomCodes (φ 🡒 ψ) = sentenceAtomCodes φ ∪ sentenceAtomCodes ψ := rfl

@[simp] lemma sentenceAtomCodes_and (φ ψ : Sentence) :
    sentenceAtomCodes (φ ⋏ ψ) = sentenceAtomCodes φ ∪ sentenceAtomCodes ψ := rfl

@[simp] lemma sentenceAtomCodes_or (φ ψ : Sentence) :
    sentenceAtomCodes (φ ⋎ ψ) = sentenceAtomCodes φ ∪ sentenceAtomCodes ψ := rfl

@[simp] lemma sentenceAtomCodes_neg (φ : Sentence) :
    sentenceAtomCodes (∼φ) = sentenceAtomCodes φ := by
  rw [Formula.neg_def, sentenceAtomCodes_imp, sentenceAtomCodes_falsum, Finset.union_empty]

@[simp] lemma sentenceAtomCodes_verum :
    sentenceAtomCodes (⊤ : Sentence) = ∅ := rfl

/-- **Substitution.** A p.c. world's verdict on `φ` depends only on the atoms occurring in
`φ`: two valuations agreeing there agree on `φ`. -/
lemma PCWorld.holds_congr_atomCodes {v v' : PCWorld} :
    ∀ φ : Sentence, (∀ a ∈ sentenceAtomCodes φ, (v a ↔ v' a)) →
      (v.Holds φ ↔ v'.Holds φ) := by
  intro φ
  induction φ using Formula.rec' with
  | hfalsum => intro _; exact Iff.rfl
  | hatom a => intro h; exact h a (by simp)
  | himp φ ψ ihφ ihψ =>
      intro h
      have hφ := ihφ (fun a ha => h a (by simp [ha]))
      have hψ := ihψ (fun a ha => h a (by simp [ha]))
      show (v.Holds φ → v.Holds ψ) ↔ (v'.Holds φ → v'.Holds ψ)
      rw [hφ, hψ]
  | hand φ ψ ihφ ihψ =>
      intro h
      have hφ := ihφ (fun a ha => h a (by simp [ha]))
      have hψ := ihψ (fun a ha => h a (by simp [ha]))
      show (v.Holds φ ∧ v.Holds ψ) ↔ (v'.Holds φ ∧ v'.Holds ψ)
      rw [hφ, hψ]
  | hor φ ψ ihφ ihψ =>
      intro h
      have hφ := ihφ (fun a ha => h a (by simp [ha]))
      have hψ := ihψ (fun a ha => h a (by simp [ha]))
      show (v.Holds φ ∨ v.Holds ψ) ↔ (v'.Holds φ ∨ v'.Holds ψ)
      rw [hφ, hψ]

end AtomCodes

/-! ## Boolean worlds and finite-support payouts -/

/-- A Boolean-valued presentation of a propositionally consistent world, used only for
the compactness proof. -/
abbrev BoolPCWorld := ℕ → Bool

namespace BoolPCWorld

/-- Interpret a Boolean assignment as the proposition-valued assignment used by `PCWorld`. -/
def toPCWorld (v : BoolPCWorld) : PCWorld := fun a => v a = true

/-- Convert a proposition-valued assignment back to Booleans. -/
noncomputable def ofPCWorld (v : PCWorld) : BoolPCWorld := fun a =>
  @decide (v a) (Classical.propDecidable _)

@[simp] lemma ofPCWorld_toPCWorld (v : PCWorld) :
    (ofPCWorld v).toPCWorld = v := by
  funext a
  apply propext
  simp [ofPCWorld, toPCWorld]

/-- Boolean evaluation of a sentence. -/
def eval (v : BoolPCWorld) : Sentence → Bool
  | .atom a => v a
  | ⊥ => false
  | φ 🡒 ψ => !(eval v φ) || eval v ψ
  | φ ⋏ ψ => eval v φ && eval v ψ
  | φ ⋎ ψ => eval v φ || eval v ψ

/-- One above the largest atom index occurring in a sentence.  This supplies the finite
support bound used by executable maturity certificates. -/
def atomBound : Sentence → ℕ
  | .atom a => a + 1
  | ⊥ => 0
  | φ 🡒 ψ => max (atomBound φ) (atomBound ψ)
  | φ ⋏ ψ => max (atomBound φ) (atomBound ψ)
  | φ ⋎ ψ => max (atomBound φ) (atomBound ψ)

/-- A valuation of exactly the first `B` atoms.  The type is finite and has a computable
enumeration, unlike an unrestricted Boolean world. -/
abbrev FiniteWorld (B : ℕ) := Fin B → Bool

/-- Extend a finite assignment by `false` outside its certified support. -/
def FiniteWorld.toBoolPCWorld {B : ℕ} (u : FiniteWorld B) : BoolPCWorld :=
  fun a => if h : a < B then u ⟨a, h⟩ else false

/-- Restrict an arbitrary Boolean world to its first `B` atoms. -/
def FiniteWorld.restrict (v : BoolPCWorld) (B : ℕ) : FiniteWorld B :=
  fun a => v a

/-- The Boolean world denoted by a bit list; atoms past the end read `false`.

This is the non-dependent cousin of `FiniteWorld.toBoolPCWorld`, and it exists for
compilation rather than for the mathematics.  `BoolPCWorld` is `ℕ → Bool`, a *function*
type, which admits no `Primcodable` instance — so `Primrec (eval v)` cannot even be stated
for a world `v`.  Routing through a `List Bool` keeps every compiled quantity a function of
`Primcodable` arguments (`List Bool × Sentence`), with the world appearing only as a
beta-reduced intermediate.  `toBoolPCWorld_bitsToFin` and `bitsWorld_ofFn`
(`Properties/Calibration.lean`) bridge back to the dependent finite worlds. -/
def bitsWorld (l : List Bool) : BoolPCWorld := fun a => l.getD a false

/-- Rational payout under a bit list: the non-dependent form of `FiniteWorld.payoutRat`. -/
def bitsPayoutRat (l : List Bool) (φ : Sentence) : ℚ :=
  if eval (bitsWorld l) φ then 1 else 0

/-- Evaluation of a bounded-support sentence is unchanged by finite restriction and
extension.  Consequently every universal payout check over finitely many sentences can
be reduced to the finite type `FiniteWorld B`. -/
lemma eval_toBoolPCWorld_restrict (v : BoolPCWorld) (B : ℕ) (φ : Sentence)
    (hφ : atomBound φ ≤ B) :
    eval ((FiniteWorld.restrict v B).toBoolPCWorld) φ = eval v φ := by
  induction φ with
  | atom a =>
      simp only [atomBound] at hφ
      have ha : a < B := by omega
      simp [eval, FiniteWorld.toBoolPCWorld, FiniteWorld.restrict, ha]
  | falsum => simp [eval]
  | imp φ ψ ihφ ihψ =>
      simp only [atomBound, max_le_iff] at hφ
      simp [eval, ihφ hφ.1, ihψ hφ.2]
  | and φ ψ ihφ ihψ =>
      simp only [atomBound, max_le_iff] at hφ
      simp [eval, ihφ hφ.1, ihψ hφ.2]
  | or φ ψ ihφ ihψ =>
      simp only [atomBound, max_le_iff] at hφ
      simp [eval, ihφ hφ.1, ihψ hφ.2]

/-- Executable rational payout under a finite Boolean assignment. -/
def FiniteWorld.payoutRat {B : ℕ} (u : FiniteWorld B) (φ : Sentence) : ℚ :=
  if eval u.toBoolPCWorld φ then 1 else 0

@[simp] lemma eval_eq_true_iff_holds (v : BoolPCWorld) (φ : Sentence) :
    eval v φ = true ↔ v.toPCWorld.Holds φ := by
  induction φ with
  | atom a => simp [eval, toPCWorld, PCWorld.Holds, LO.Propositional.Formula.Boolean.val]
  | falsum => simp [eval, PCWorld.Holds, LO.Propositional.Formula.Boolean.val]
  | imp φ ψ ihφ ihψ =>
      cases hφ : eval v φ <;> cases hψ : eval v ψ <;>
        simp_all [eval, PCWorld.Holds, LO.Propositional.Formula.Boolean.val]
  | and φ ψ ihφ ihψ =>
      simp [eval, PCWorld.Holds, LO.Propositional.Formula.Boolean.val, ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
      simp [eval, PCWorld.Holds, LO.Propositional.Formula.Boolean.val, ihφ, ihψ]

/-- The executable finite-world payout is the exact rational payout of its extended
proposition-valued world. -/
lemma FiniteWorld.payoutRat_eq_toPCWorld {B : ℕ} (u : FiniteWorld B)
    (φ : Sentence) :
    u.payoutRat φ = u.toBoolPCWorld.toPCWorld.payoutRat φ := by
  classical
  unfold payoutRat PCWorld.payoutRat
  rw [← eval_eq_true_iff_holds]
  by_cases h : eval u.toBoolPCWorld φ = true <;> simp [h]

/-- On every sentence inside the support bound, the finite rational payout obtained by
restricting a world is exactly that world's rational payout. -/
lemma FiniteWorld.payoutRat_restrict_ofPCWorld (v : PCWorld) (B : ℕ)
    (φ : Sentence) (hφ : atomBound φ ≤ B) :
    payoutRat (restrict (ofPCWorld v) B) φ = v.payoutRat φ := by
  classical
  unfold payoutRat
  rw [eval_toBoolPCWorld_restrict (ofPCWorld v) B φ hφ]
  have heval := eval_eq_true_iff_holds (ofPCWorld v) φ
  rw [ofPCWorld_toPCWorld] at heval
  by_cases hh : v.Holds φ
  · have : eval (ofPCWorld v) φ = true := heval.mpr hh
    simp [this, PCWorld.payoutRat, hh]
  · have : eval (ofPCWorld v) φ = false := by
      apply Bool.eq_false_of_not_eq_true
      exact fun he => hh (heval.mp he)
    simp [this, PCWorld.payoutRat, hh]

/-! ## Compactness in the product space -/

/-- Sentence evaluation depends continuously on its finitely many atoms. -/
lemma continuous_eval (φ : Sentence) : Continuous (fun v : BoolPCWorld => eval v φ) := by
  induction φ with
  | atom a => exact continuous_apply a
  | falsum => exact continuous_const
  | imp φ ψ ihφ ihψ =>
      exact (continuous_of_discreteTopology : Continuous
        (fun z : Bool × Bool => (!z.1) || z.2)).comp (ihφ.prodMk ihψ)
  | and φ ψ ihφ ihψ =>
      exact (continuous_of_discreteTopology : Continuous
        (fun z : Bool × Bool => z.1 && z.2)).comp (ihφ.prodMk ihψ)
  | or φ ψ ihφ ihψ =>
      exact (continuous_of_discreteTopology : Continuous
        (fun z : Bool × Bool => z.1 || z.2)).comp (ihφ.prodMk ihψ)

/-- The model set of one sentence is clopen in the Boolean product space. -/
lemma isClopen_holds (φ : Sentence) :
    IsClopen {v : BoolPCWorld | v.toPCWorld.Holds φ} := by
  have heq : {v : BoolPCWorld | v.toPCWorld.Holds φ} =
      (fun v => eval v φ) ⁻¹' {true} := by
    ext v
    simp [eval_eq_true_iff_holds]
  rw [heq]
  exact ⟨isClosed_singleton.preimage (continuous_eval φ),
    (continuous_eval φ).isOpen_preimage _ (isOpen_discrete _)⟩

@[simp] lemma payout_toPCWorld (v : BoolPCWorld) (φ : Sentence) :
    v.toPCWorld.payout φ = if eval v φ = true then 1 else 0 := by
  rw [PCWorld.payout]
  by_cases h : eval v φ = true
  · rw [if_pos h, if_pos ((eval_eq_true_iff_holds v φ).mp h)]
  · rw [if_neg h, if_neg (fun hh => h ((eval_eq_true_iff_holds v φ).mpr hh))]

/-- The real payout of a fixed sentence is continuous on Boolean worlds. -/
lemma continuous_payout (φ : Sentence) :
    Continuous (fun v : BoolPCWorld => v.toPCWorld.payout φ) := by
  rw [show (fun v : BoolPCWorld => v.toPCWorld.payout φ) =
      (fun b : Bool => if b = true then (1 : ℝ) else 0) ∘ (fun v => eval v φ) by
    funext v
    simp [Function.comp_apply]]
  exact (continuous_of_discreteTopology : Continuous
    (fun b : Bool => if b = true then (1 : ℝ) else 0)).comp (continuous_eval φ)

/-- A fixed affine combination's value is continuous as its Boolean world varies. -/
lemma continuous_affineValue (A : AffineCombination) (P : History) :
    Continuous (fun v : BoolPCWorld => A.value P v.toPCWorld.payout) := by
  have hterms : ∀ l : List (EF × Sentence), Continuous (fun v : BoolPCWorld =>
      (l.map (fun p => p.1.denote P * v.toPCWorld.payout p.2)).sum) := by
    intro l
    induction l with
    | nil => simpa using (continuous_const : Continuous (fun _ : BoolPCWorld => (0 : ℝ)))
    | cons p ps ih =>
        have h := ((continuous_const (y := p.1.denote P)).mul (continuous_payout p.2)).add ih
        convert h using 1
        funext v
        simp [mul_ite]
  exact continuous_const.add (hterms A.terms)

/-- Boolean worlds plausible at one finite deductive stage form a closed set. -/
lemma isClosed_consistentWith (DP : DeductiveProcess) (n : ℕ) :
    IsClosed {v : BoolPCWorld | v.toPCWorld.ConsistentWith (DP.D n)} := by
  have heq : {v : BoolPCWorld | v.toPCWorld.ConsistentWith (DP.D n)} =
      ⋂ φ : {φ // φ ∈ DP.D n}, {v : BoolPCWorld | v.toPCWorld.Holds φ.1} := by
    ext v
    simp [PCWorld.ConsistentWith]
  rw [heq]
  exact isClosed_iInter (fun φ => (isClopen_holds φ.1).1)

/-- A fixed affine sublevel set is closed. -/
lemma isClosed_affineValue_le (A : AffineCombination) (P : History) (q : ℝ) :
    IsClosed {v : BoolPCWorld | A.value P v.toPCWorld.payout ≤ q} :=
  isClosed_Iic.preimage (continuous_affineValue A P)

end BoolPCWorld

/-- Closed constraints used in the compactness argument: `none` is the fixed affine
sublevel set and `some n` is finite-stage plausibility. -/
def affineCompactConstraint (DP : DeductiveProcess) (A : AffineCombination)
    (P : History) (q : ℝ) : Option ℕ → Set BoolPCWorld
  | none => {v | A.value P v.toPCWorld.payout ≤ q}
  | some n => {v | v.toPCWorld.ConsistentWith (DP.D n)}

lemma affineCompactConstraint_isClosed (DP : DeductiveProcess) (A : AffineCombination)
    (P : History) (q : ℝ) (i : Option ℕ) :
    IsClosed (affineCompactConstraint DP A P q i) := by
  cases i with
  | none => exact BoolPCWorld.isClosed_affineValue_le A P q
  | some n => exact BoolPCWorld.isClosed_consistentWith DP n

/-- Propositional compactness in the precise uniform form needed by `thm:affcoh`: if a
fixed affine combination is strictly above `q` in every world consistent with the
completed theory, then after some finite stage it is above `q` in every plausible world.

The proof is a compact-product argument: if bad finite-stage worlds existed arbitrarily
late, the closed finite-stage model sets together with the fixed affine sublevel set would
have the finite intersection property, hence a completed-theory bad world. -/
lemma eventually_affineValue_gt_of_theory
    (DP : DeductiveProcess) (A : AffineCombination) (P : History) (q : ℝ)
    (hall : ∀ v : PCWorld, v.ConsistentWithTheory DP → q < A.value P v.payout) :
    ∀ᶠ n in atTop, ∀ v : PCWorld,
      v.ConsistentWith (DP.D n) → q < A.value P v.payout := by
  by_contra hnot
  rw [Filter.not_eventually] at hnot
  have hbad : ∃ᶠ n in atTop, ∃ v : PCWorld,
      v.ConsistentWith (DP.D n) ∧ A.value P v.payout ≤ q := by
    refine hnot.mono (fun n hn => ?_)
    rcases not_forall.mp hn with ⟨v, hv⟩
    rcases Classical.not_imp.mp hv with ⟨hcons, hvalue⟩
    exact ⟨v, hcons, le_of_not_gt hvalue⟩
  have hfip : ∀ u : Finset (Option ℕ),
      (Set.univ ∩ ⋂ i ∈ u, affineCompactConstraint DP A P q i).Nonempty := by
    intro u
    let K := u.sup (fun i => i.getD 0)
    obtain ⟨m, hmK, v, hv, hvalue⟩ := Filter.frequently_atTop.mp hbad K
    refine ⟨BoolPCWorld.ofPCWorld v, ?_⟩
    constructor
    · exact Set.mem_univ _
    simp only [Set.mem_iInter]
    intro i hi
    cases i with
    | none =>
        simpa [affineCompactConstraint] using hvalue
    | some n =>
        have hnK : n ≤ K := Finset.le_sup (s := u) (f := fun i => i.getD 0) hi
        have hnm : n ≤ m := hnK.trans hmK
        have hsub : DP.D n ⊆ DP.D m := Finset.le_iff_subset.mp
          (monotone_nat_of_le_succ (fun k => Finset.le_iff_subset.mpr (DP.mono k)) hnm)
        simpa [affineCompactConstraint] using
          (show (BoolPCWorld.ofPCWorld v).toPCWorld.ConsistentWith (DP.D n) from
            fun φ hφ => by
              rw [BoolPCWorld.ofPCWorld_toPCWorld]
              exact hv φ (hsub hφ))
  obtain ⟨b, _, hb⟩ := isCompact_univ.inter_iInter_nonempty
    (affineCompactConstraint DP A P q)
    (affineCompactConstraint_isClosed DP A P q) hfip
  have hbtheory : b.toPCWorld.ConsistentWithTheory DP := by
    intro n
    have hn := Set.mem_iInter.mp hb (some n)
    simpa [affineCompactConstraint] using hn
  have hbvalue : A.value P b.toPCWorld.payout ≤ q := by
    have hnone := Set.mem_iInter.mp hb none
    simpa [affineCompactConstraint] using hnone
  have := hall b.toPCWorld hbtheory
  exact (not_lt_of_ge hbvalue) this

/-- Nonempty finite-stage plausible sets have a world in their nested intersection, i.e.
a world consistent with the completed theory. The compactness argument itself lives in
`Framework/Compactness.lean`; this is the §4.5-local spelling of it. -/
lemma exists_consistentWithTheory (DP : DeductiveProcess)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ∃ v : PCWorld, v.ConsistentWithTheory DP :=
  DP.exists_consistentWithTheory hworld

end LogicalInduction
