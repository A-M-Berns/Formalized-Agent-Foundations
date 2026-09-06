import LogicalInduction.Framework.BooleanWorlds
import LogicalInduction.Framework.ROI
import LogicalInduction.Framework.Emission.WriteOut

/-!
# Determination via the theory, and deciding settlement

When is an affine combination's value pinned down by the deductive process, and how does a
bounded computation *check* that it is?  Both questions are §4.3–4.4 proof technology rather
than paper claims, so nothing here carries a `Paper node` line.

## Determination

`AffineCombination.DeterminedViaTheory As P DP truth` says a concrete value stream `truth`
records the value of every member in every world plausible at the corresponding stage;
`ApproxDeterminedViaTheory` weakens it by an `ErrorNegligible` slack, which is what the
`dd:mesh` threshold expansions actually supply.  `eventually_close` is the transfer both
forms are consumed through.

## Settlement

An affine combination is *settled* at a stage when all plausible worlds agree on its value.
`exists_settled_stage` produces such a stage from determination, `settled_iff_agree`
identifies settlement with agreement of the finite-world rational payouts, and
`SettlementTest` / `SettlementTestBool` are the decidable presentations — the second a
`Bool`-valued test over `allBitLists`, so a bounded machine can run it.  The finite-support
bridge (`bitsToFin`, `toBoolPCWorld_bitsToFin`, `bitsWorld_ofFn`) into
`Framework/BooleanWorlds.lean`'s `FiniteWorld` is what makes the quantifier finite;
`stageSort` and `stageSatBits` are the executable reading of a deductive stage.

## Maturity certificates

`UnitMaturitySemanticCertificate` is the semantic core of a finite exact maturity checker for
a unit-magnitude trader: every numeric inequality is rational and the universal
plausible-world payoff claim is reduced to assignments to the first `maturityAtomLimit` atoms.
`unitMaturityCheckAtFuel` is the fuel-clocked decision procedure, `unitMaturityCheckAtFuel_sound`
and `_eventually_complete` its two halves.  `Construction/Statistics/HistoricalMaturity.lean` is
the client that runs it over a whole trader family.
-/

namespace LogicalInduction

open Filter Topology Set
open scoped BigOperators

/-! ## Determination via the deductive theory -/

/-- A concrete value stream witnesses that every member of an affine sequence is
determined via the completed theory.  Quantifying the value stream explicitly makes the
paper's notation `ThmValue(Aₙ)` usable without choice and exposes exactly what later
trader proofs may rely on. -/
def AffineCombination.DeterminedViaTheory
    (As : ℕ → AffineCombination) (P : History) (DP : DeductiveProcess)
    (truth : ℕ → ℝ) : Prop :=
  ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
    (As n).value P v.payout = truth n

/-- Approximate determination: every completed-theory world values `As n` within `e n` of
the advertised `truth n`.  `DeterminedViaTheory` is the `e = 0` case
(`DeterminedViaTheory.approx`).

This is the form the threshold mesh of a LUV combination satisfies.  The paper's
`def:affthmval` determines a LUV *combination*, not its component LUVs, so completed
worlds may disagree about the individual threshold sentences; what survives is that the
precision-`n` mesh reproduces the determined combination value up to the mesh error.
Every consumer below is stated at this generality; the exact statements are its `e = 0`
specializations. -/
def AffineCombination.ApproxDeterminedViaTheory
    (As : ℕ → AffineCombination) (P : History) (DP : DeductiveProcess)
    (truth e : ℕ → ℝ) : Prop :=
  ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
    |(As n).value P v.payout - truth n| ≤ e n

/-- The determination error of an approximately determined sequence is *negligible against
share magnitude*: it never exceeds the day's magnitude, and past a launch day chosen from
any tolerance it is within that fraction of it.

This is exactly what the precision-`n` threshold mesh of a bounded LUV-combination sequence
provides (`err n ≤ magnitude n / n`), and it is all the bias-run economics needs: a run
launched late enough forfeits an arbitrarily small share of its unit magnitude. -/
def AffineCombination.ErrorNegligible (As : ℕ → AffineCombination) (P : History)
    (err : ℕ → ℝ) : Prop :=
  (∀ i, 0 ≤ err i) ∧ (∀ i, err i ≤ (As i).magnitude P) ∧
    ∀ c > 0, ∃ N, ∀ i, N ≤ i → err i ≤ c * (As i).magnitude P

lemma AffineCombination.errorNegligible_zero (As : ℕ → AffineCombination) (P : History) :
    AffineCombination.ErrorNegligible As P 0 :=
  ⟨fun _ => le_rfl, fun i => (As i).magnitude_nonneg P,
    fun c hc => ⟨0, fun i _ => by
      simpa using mul_nonneg hc.le ((As i).magnitude_nonneg P)⟩⟩

lemma AffineCombination.ErrorNegligible.neg
    {As : ℕ → AffineCombination} {P : History} {err : ℕ → ℝ}
    (h : AffineCombination.ErrorNegligible As P err) :
    AffineCombination.ErrorNegligible (fun n => (As n).neg) P err := by
  obtain ⟨h0, hmag, hneg⟩ := h
  refine ⟨h0, fun i => by rw [AffineCombination.neg_magnitude]; exact hmag i,
    fun c hc => ?_⟩
  obtain ⟨N, hN⟩ := hneg c hc
  exact ⟨N, fun i hi => by rw [AffineCombination.neg_magnitude]; exact hN i hi⟩

lemma AffineCombination.DeterminedViaTheory.approx
    {As : ℕ → AffineCombination} {P : History} {DP : DeductiveProcess}
    {truth : ℕ → ℝ} (h : DeterminedViaTheory As P DP truth) :
    AffineCombination.ApproxDeterminedViaTheory As P DP truth 0 := by
  intro n v hv
  rw [h n v hv]
  simp

lemma AffineCombination.ApproxDeterminedViaTheory.neg
    {As : ℕ → AffineCombination} {P : History} {DP : DeductiveProcess}
    {truth e : ℕ → ℝ} (h : ApproxDeterminedViaTheory As P DP truth e) :
    AffineCombination.ApproxDeterminedViaTheory (fun n => (As n).neg) P DP
      (fun n => -truth n) e := by
  intro n v hv
  rw [AffineCombination.neg_value, show -(As n).value P v.payout - -truth n =
    -((As n).value P v.payout - truth n) by ring, abs_neg]
  exact h n v hv

/-- Determination in every completed-theory world becomes uniform approximate
determination over all sufficiently late finite-stage plausible worlds.  This compactness
bridge is what turns a finite capped run of weighted affine purchases into an actual ROI
component; no settlement schedule is assumed. -/
lemma AffineCombination.DeterminedViaTheory.eventually_close
    {As : ℕ → AffineCombination} {P : History} {DP : DeductiveProcess}
    {truth : ℕ → ℝ}
    (h : AffineCombination.DeterminedViaTheory As P DP truth)
    (i : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ v : PCWorld, v.ConsistentWith (DP.D n) →
      |(As i).value P v.payout - truth i| < ε := by
  have hlo := eventually_affineValue_gt_of_theory DP (As i) P (truth i - ε)
    (fun v hv => by rw [h i v hv]; linarith)
  have hhi := eventually_affineValue_gt_of_theory DP (As i).neg P (-truth i - ε)
    (fun v hv => by rw [AffineCombination.neg_value, h i v hv]; linarith)
  filter_upwards [hlo, hhi] with n hnlo hnhi
  intro v hv
  have hl := hnlo v hv
  have hu := hnhi v hv
  rw [AffineCombination.neg_value] at hu
  rw [abs_lt]
  constructor <;> linarith

/-- Approximate determination in every completed-theory world likewise becomes uniform
finite-stage approximation, with the determination error added to the tolerance. -/
lemma AffineCombination.ApproxDeterminedViaTheory.eventually_close
    {As : ℕ → AffineCombination} {P : History} {DP : DeductiveProcess}
    {truth e : ℕ → ℝ}
    (h : AffineCombination.ApproxDeterminedViaTheory As P DP truth e)
    (i : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ v : PCWorld, v.ConsistentWith (DP.D n) →
      |(As i).value P v.payout - truth i| < e i + ε := by
  have hlo := eventually_affineValue_gt_of_theory DP (As i) P (truth i - e i - ε)
    (fun v hv => by have := abs_le.1 (h i v hv); linarith [this.1])
  have hhi := eventually_affineValue_gt_of_theory DP (As i).neg P (-truth i - e i - ε)
    (fun v hv => by
      rw [AffineCombination.neg_value]
      have := abs_le.1 (h i v hv); linarith [this.2])
  filter_upwards [hlo, hhi] with n hnlo hnhi
  intro v hv
  have hl := hnlo v hv
  have hu := hnhi v hv
  rw [AffineCombination.neg_value] at hu
  rw [abs_lt]
  constructor <;> linarith

/-! ### Exact finite-stage settlement

`eventually_close` gives only *approximate* finite-stage determination, but the paper's
patient selector (`app:prandaff`) needs **exact** settlement: a stage `m` at which every
plausible world already values `As i` at exactly `truth i`.  The gap closes because an
affine combination has *finitely many* terms, so its value depends on a world only through
finitely many `{0,1}` payouts and therefore ranges over a finite set.  Pick `δ` below the
smallest nonzero gap to `truth i` and approximate determination becomes exact. -/

open Classical in
/-- The payout-sum of a fixed term list ranges over a finite set of reals: each term
contributes one of two values (`0`, or its coefficient). -/
private lemma AffineCombination.exists_termsSum_finset (P : History) :
    ∀ terms : List (EF × Sentence),
      ∃ S : Finset ℝ, ∀ v : PCWorld,
        (terms.map (fun p => p.1.denote P * v.payout p.2)).sum ∈ S
  | [] => ⟨{0}, by intro v; simp⟩
  | (e, φ) :: rest => by
      obtain ⟨S, hS⟩ := AffineCombination.exists_termsSum_finset P rest
      refine ⟨Finset.image (fun p : ℝ × ℝ => p.1 + p.2)
        (({0, e.denote P} : Finset ℝ) ×ˢ S), ?_⟩
      intro v
      simp only [List.map_cons, List.sum_cons]
      refine Finset.mem_image.mpr ⟨(e.denote P * v.payout φ, _), ?_, rfl⟩
      refine Finset.mem_product.mpr ⟨?_, hS v⟩
      by_cases h : v.Holds φ <;> simp [PCWorld.payout, h]

/-- An affine combination's value ranges over a finite set of reals, uniformly in the
world.  Finiteness of `terms` is what makes this true — it is the fact that upgrades
approximate determination to exact settlement. -/
lemma AffineCombination.exists_valueSet (A : AffineCombination) (P : History) :
    ∃ S : Finset ℝ, ∀ v : PCWorld, A.value P v.payout ∈ S := by
  classical
  obtain ⟨S, hS⟩ := AffineCombination.exists_termsSum_finset P A.terms
  exact ⟨S.image (fun x => A.const.denote P + x), fun v => Finset.mem_image_of_mem _ (hS v)⟩

/-- **Exact finite-stage settlement.**  If the completed theory determines `As i`, then
some finite stage already pins its value to `truth i` in *every* plausible world.

This is the realizability core of `PatientSettlementClock.eventually_inactive`: it is what
guarantees the settlement checker eventually fires, so the clock can be sound (inactive ⇒
settled) and still eventually go inactive.  Purely semantic — no computability claim. -/
lemma AffineCombination.DeterminedViaTheory.exists_settled_stage
    {As : ℕ → AffineCombination} {P : History} {DP : DeductiveProcess}
    {truth : ℕ → ℝ}
    (h : AffineCombination.DeterminedViaTheory As P DP truth) (i : ℕ) :
    ∃ m, ∀ v : PCWorld, v.ConsistentWith (DP.D m) →
      (As i).value P v.payout = truth i := by
  classical
  obtain ⟨S, hS⟩ := AffineCombination.exists_valueSet (As i) P
  by_cases hB : (S.filter (fun x => x ≠ truth i)).Nonempty
  · -- `δ` = smallest gap from an achievable wrong value to `truth i`; it is positive.
    have hδpos :
        0 < (S.filter (fun x => x ≠ truth i)).inf' hB (fun x => |x - truth i|) := by
      rw [Finset.lt_inf'_iff]
      intro x hx
      exact abs_pos.mpr (sub_ne_zero.mpr (Finset.mem_filter.mp hx).2)
    obtain ⟨m, hm⟩ := (h.eventually_close i _ hδpos).exists
    refine ⟨m, fun v hv => ?_⟩
    by_contra hne
    exact absurd (hm v hv)
      (not_lt.mpr (Finset.inf'_le _ (Finset.mem_filter.mpr ⟨hS v, hne⟩)))
  · -- No achievable value differs from `truth i`, so every stage settles — take `0`.
    refine ⟨0, fun v _ => ?_⟩
    by_contra hne
    exact hB ⟨_, Finset.mem_filter.mpr ⟨hS v, hne⟩⟩

/-- **The settlement test does not need to know `truth`.**  Provided the theory is
consistent, `As i` is settled at stage `m` — every world plausible at `m` values it at
exactly `truth i` — **iff** the worlds plausible at `m` merely *agree with each other*.

This is what makes the paper's `settled` machine (`app:prandaff`) implementable, and the
paper does not spell it out: a checker cannot compute `truth i` (it is defined by a limit
over the completed theory), but it *can* test agreement across the finitely many relevant
assignments.  The forward direction is trivial; the reverse leans on completed-theory
worlds being a nonempty subset of the stage-`m` plausible worlds, which is exactly where
consistency (`hworld`) is used. -/
lemma AffineCombination.DeterminedViaTheory.settled_iff_agree
    {As : ℕ → AffineCombination} {P : History} {DP : DeductiveProcess}
    {truth : ℕ → ℝ}
    (h : AffineCombination.DeterminedViaTheory As P DP truth)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (i m : ℕ) :
    (∀ v : PCWorld, v.ConsistentWith (DP.D m) → (As i).value P v.payout = truth i) ↔
      (∀ v w : PCWorld, v.ConsistentWith (DP.D m) → w.ConsistentWith (DP.D m) →
        (As i).value P v.payout = (As i).value P w.payout) := by
  constructor
  · intro hs v w hv hw
    rw [hs v hv, hs w hw]
  · intro hagree v hv
    obtain ⟨v₀, hv₀⟩ := exists_consistentWithTheory DP hworld
    rw [hagree v v₀ hv (hv₀ m), h i v₀ hv₀]

/-- **Tolerance agreement bounds the distance to `truth`.**  If the worlds plausible at
stage `m` all value `As i` within `tol` of each other, then — since some completed-theory
world is among them, and it values `As i` within `e i` of `truth i` — every plausible
world is within `tol + e i` of `truth i`.  This is the approximate replacement for the
easy direction of `settled_iff_agree`. -/
lemma AffineCombination.ApproxDeterminedViaTheory.close_of_agree
    {As : ℕ → AffineCombination} {P : History} {DP : DeductiveProcess}
    {truth e : ℕ → ℝ}
    (h : AffineCombination.ApproxDeterminedViaTheory As P DP truth e)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (i m : ℕ) (tol : ℝ)
    (hagree : ∀ v w : PCWorld, v.ConsistentWith (DP.D m) → w.ConsistentWith (DP.D m) →
      |(As i).value P v.payout - (As i).value P w.payout| ≤ tol) :
    ∀ v : PCWorld, v.ConsistentWith (DP.D m) →
      |(As i).value P v.payout - truth i| ≤ tol + e i := by
  intro v hv
  obtain ⟨v₀, hv₀⟩ := exists_consistentWithTheory DP hworld
  exact (abs_sub_le _ ((As i).value P v₀.payout) _).trans
    (add_le_add (hagree v v₀ hv (hv₀ m)) (h i v₀ hv₀))

/-- **Tolerance agreement is reachable.**  Completed-theory worlds pin `As i` to within
`e i` of `truth i`, so `eventually_close` makes the plausible worlds' spread beat any
tolerance strictly above `2 * e i` at some finite stage.  This is the realizability core
of the approximate clock's `eventually_inactive`: it is why the tolerance checker
eventually fires even though exact agreement may never hold. -/
lemma AffineCombination.ApproxDeterminedViaTheory.exists_agree_stage
    {As : ℕ → AffineCombination} {P : History} {DP : DeductiveProcess}
    {truth e : ℕ → ℝ}
    (h : AffineCombination.ApproxDeterminedViaTheory As P DP truth e)
    (i : ℕ) (tol : ℝ) (htol : 2 * e i < tol) :
    ∃ m, ∀ v w : PCWorld, v.ConsistentWith (DP.D m) → w.ConsistentWith (DP.D m) →
      |(As i).value P v.payout - (As i).value P w.payout| ≤ tol := by
  obtain ⟨m, hm⟩ := (h.eventually_close i ((tol - 2 * e i) / 2) (by linarith)).exists
  refine ⟨m, fun v w hv hw => ?_⟩
  have h1 := hm v hv
  have h2 := hm w hw
  have hstep := abs_sub_le ((As i).value P v.payout) (truth i) ((As i).value P w.payout)
  rw [abs_sub_comm (truth i)] at hstep
  linarith

/-! ### Deciding settlement

`settled_iff_agree` reduces settlement to *agreement* among plausible worlds and
`exists_settled_stage` guarantees agreement eventually holds.  What remains is to decide
agreement.  Two facts make it decidable, and both are exactly what the `ℝ`-valued
`History` hides:

* against a **rational** market every coefficient is rational (`EF.denoteRat`), so values
  compare exactly.  Over an arbitrary `History` this is equality of reals — undecidable,
  which is why no clock exists at that generality.
* an affine combination and a deductive stage each mention finitely many atoms, so world
  quantification collapses onto the finite type `BoolPCWorld.FiniteWorld`.

This mirrors the maturity checker (`unitMaturityCheckAtFuel`) below. -/

/-- Executable rational value of an affine combination under a rational price table and a
rational payout table. -/
def AffineCombination.valueRat (A : AffineCombination) (Q : ℕ → Sentence → ℚ)
    (w : Sentence → ℚ) : ℚ :=
  A.const.denoteRat Q + (A.terms.map (fun p => p.1.denoteRat Q * w p.2)).sum

private lemma AffineCombination.termsSum_eq_ratCast
    (P : History) (Q : ℕ → Sentence → ℚ) (hQ : ∀ d φ, P d φ = (Q d φ : ℝ))
    (wR : Sentence → ℝ) (wQ : Sentence → ℚ) (hw : ∀ φ, wR φ = (wQ φ : ℝ)) :
    ∀ terms : List (EF × Sentence),
      (terms.map (fun p => p.1.denote P * wR p.2)).sum
        = ((terms.map (fun p => p.1.denoteRat Q * wQ p.2)).sum : ℝ)
  | [] => by simp
  | p :: rest => by
      simp only [List.map_cons, List.sum_cons, Rat.cast_add, Rat.cast_mul]
      rw [EF.denote_eq_ratCast p.1 P Q hQ, hw p.2,
        AffineCombination.termsSum_eq_ratCast P Q hQ wR wQ hw rest]

/-- Rational affine value agrees exactly with the real semantics of an exact rational
market whenever the payout tables agree pointwise. -/
lemma AffineCombination.value_eq_ratCast (A : AffineCombination)
    (P : History) (Q : ℕ → Sentence → ℚ) (hQ : ∀ d φ, P d φ = (Q d φ : ℝ))
    (wR : Sentence → ℝ) (wQ : Sentence → ℚ) (hw : ∀ φ, wR φ = (wQ φ : ℝ)) :
    A.value P wR = (A.valueRat Q wQ : ℝ) := by
  unfold AffineCombination.value AffineCombination.valueRat
  rw [Rat.cast_add, EF.denote_eq_ratCast A.const P Q hQ,
    AffineCombination.termsSum_eq_ratCast P Q hQ wR wQ hw A.terms]

private lemma AffineCombination.termsSum_congr (Q : ℕ → Sentence → ℚ)
    (w w' : Sentence → ℚ) :
    ∀ terms : List (EF × Sentence), (∀ p ∈ terms, w p.2 = w' p.2) →
      (terms.map (fun p => p.1.denoteRat Q * w p.2)).sum
        = (terms.map (fun p => p.1.denoteRat Q * w' p.2)).sum
  | [], _ => rfl
  | p :: rest, h => by
      simp only [List.map_cons, List.sum_cons]
      rw [h p (by simp),
        AffineCombination.termsSum_congr Q w w' rest
          (fun q hq => h q (List.mem_cons_of_mem _ hq))]

/-- The rational value only inspects the payouts of the combination's own sentences. -/
lemma AffineCombination.valueRat_congr (A : AffineCombination) (Q : ℕ → Sentence → ℚ)
    (w w' : Sentence → ℚ) (h : ∀ p ∈ A.terms, w p.2 = w' p.2) :
    A.valueRat Q w = A.valueRat Q w' := by
  unfold AffineCombination.valueRat
  rw [AffineCombination.termsSum_congr Q w w' A.terms h]

/-- Support bound covering every sentence the stage-`m` settlement test inspects: the
stage's own sentences and the combination's traded sentences.  Sums rather than maxima
keep the membership proofs elementary; only the upper bound matters. -/
def AffineCombination.settlementAtomLimit (A : AffineCombination)
    (stage : Finset Sentence) : ℕ :=
  stage.sum BoolPCWorld.atomBound +
    (A.terms.map (fun p => BoolPCWorld.atomBound p.2)).sum

lemma AffineCombination.settlementAtomLimit_stage_bounded (A : AffineCombination)
    (stage : Finset Sentence) : ∀ φ ∈ stage,
      BoolPCWorld.atomBound φ ≤ A.settlementAtomLimit stage := by
  intro φ hφ
  have hsingle : BoolPCWorld.atomBound φ ≤ stage.sum BoolPCWorld.atomBound :=
    Finset.single_le_sum (fun ψ _ => Nat.zero_le (BoolPCWorld.atomBound ψ)) hφ
  unfold AffineCombination.settlementAtomLimit
  omega

lemma AffineCombination.settlementAtomLimit_terms_bounded (A : AffineCombination)
    (stage : Finset Sentence) : ∀ p ∈ A.terms,
      BoolPCWorld.atomBound p.2 ≤ A.settlementAtomLimit stage := by
  intro p hp
  have hlocal : BoolPCWorld.atomBound p.2 ≤
      (A.terms.map (fun q => BoolPCWorld.atomBound q.2)).sum :=
    List.single_le_sum (fun x _ => Nat.zero_le x) _ (List.mem_map.mpr ⟨p, hp, rfl⟩)
  unfold AffineCombination.settlementAtomLimit
  omega

/-- Restricting a plausible world to the settlement support keeps it plausible. -/
private lemma AffineCombination.restrict_plausible (A : AffineCombination)
    (stage : Finset Sentence) (v : PCWorld) (hv : v.ConsistentWith stage) :
    ∀ φ ∈ stage, BoolPCWorld.eval
      (BoolPCWorld.FiniteWorld.restrict (BoolPCWorld.ofPCWorld v)
        (A.settlementAtomLimit stage)).toBoolPCWorld φ = true := by
  intro φ hφ
  rw [BoolPCWorld.eval_toBoolPCWorld_restrict _ _ φ
    (A.settlementAtomLimit_stage_bounded stage φ hφ)]
  have heval := BoolPCWorld.eval_eq_true_iff_holds (BoolPCWorld.ofPCWorld v) φ
  rw [BoolPCWorld.ofPCWorld_toPCWorld] at heval
  exact heval.mpr (hv φ hφ)

/-- **The settlement test is decidable, on a rational market.**  If every pair of
*finite* plausible worlds assigns `A` the same rational value, then every pair of genuine
plausible worlds assigns it the same real value.

The finite quantifier on the left is over `BoolPCWorld.FiniteWorld B = Fin B → Bool`, a
`Fintype` with decidable rational equality — so the left side is a `decide`-able Boolean
test.  This is the step that needs `P` rational, and it is the whole reason
`PatientSettlementClock` is realizable at `liaHistory` but not at an arbitrary
`History`. -/
lemma AffineCombination.agree_of_finiteWorlds_agree (A : AffineCombination)
    (P : History) (Q : ℕ → Sentence → ℚ) (hQ : ∀ d φ, P d φ = (Q d φ : ℝ))
    (stage : Finset Sentence) (tol : ℚ)
    (h : ∀ u u' : BoolPCWorld.FiniteWorld (A.settlementAtomLimit stage),
      (∀ φ ∈ stage, BoolPCWorld.eval u.toBoolPCWorld φ = true) →
      (∀ φ ∈ stage, BoolPCWorld.eval u'.toBoolPCWorld φ = true) →
        |A.valueRat Q u.payoutRat - A.valueRat Q u'.payoutRat| ≤ tol)
    (v w : PCWorld) (hv : v.ConsistentWith stage) (hw : w.ConsistentWith stage) :
    |A.value P v.payout - A.value P w.payout| ≤ (tol : ℝ) := by
  classical
  have hrestrict (x : PCWorld) :
      A.valueRat Q
          (BoolPCWorld.FiniteWorld.restrict (BoolPCWorld.ofPCWorld x)
            (A.settlementAtomLimit stage)).payoutRat
        = A.valueRat Q x.payoutRat :=
    A.valueRat_congr Q _ _ (fun p hp =>
      BoolPCWorld.FiniteWorld.payoutRat_restrict_ofPCWorld x _ p.2
        (A.settlementAtomLimit_terms_bounded stage p hp))
  rw [A.value_eq_ratCast P Q hQ v.payout v.payoutRat (PCWorld.payout_eq_ratCast v),
    A.value_eq_ratCast P Q hQ w.payout w.payoutRat (PCWorld.payout_eq_ratCast w),
    ← hrestrict v, ← hrestrict w]
  have hfin := h _ _ (A.restrict_plausible stage v hv) (A.restrict_plausible stage w hw)
  exact_mod_cast hfin

/-- The converse of `agree_of_finiteWorlds_agree`: genuine agreement restricts to finite
agreement.  Every plausible *finite* world extends to a genuine plausible `PCWorld` with
the same payouts, so the finite test cannot be stricter than the real condition.  This is
what makes the concrete test **complete**, not merely sound. -/
lemma AffineCombination.finiteWorlds_agree_of_agree (A : AffineCombination)
    (P : History) (Q : ℕ → Sentence → ℚ) (hQ : ∀ d φ, P d φ = (Q d φ : ℝ))
    (stage : Finset Sentence) (tol : ℚ)
    (h : ∀ v w : PCWorld, v.ConsistentWith stage → w.ConsistentWith stage →
      |A.value P v.payout - A.value P w.payout| ≤ (tol : ℝ)) :
    ∀ u u' : BoolPCWorld.FiniteWorld (A.settlementAtomLimit stage),
      (∀ φ ∈ stage, BoolPCWorld.eval u.toBoolPCWorld φ = true) →
      (∀ φ ∈ stage, BoolPCWorld.eval u'.toBoolPCWorld φ = true) →
        |A.valueRat Q u.payoutRat - A.valueRat Q u'.payoutRat| ≤ tol := by
  classical
  intro u u' hu hu'
  have hcons (x : BoolPCWorld.FiniteWorld (A.settlementAtomLimit stage))
      (hx : ∀ φ ∈ stage, BoolPCWorld.eval x.toBoolPCWorld φ = true) :
      x.toBoolPCWorld.toPCWorld.ConsistentWith stage :=
    fun φ hφ => (BoolPCWorld.eval_eq_true_iff_holds x.toBoolPCWorld φ).1 (hx φ hφ)
  have htransfer (x : BoolPCWorld.FiniteWorld (A.settlementAtomLimit stage)) :
      A.valueRat Q x.payoutRat = A.valueRat Q x.toBoolPCWorld.toPCWorld.payoutRat :=
    A.valueRat_congr Q _ _ (fun p _ => BoolPCWorld.FiniteWorld.payoutRat_eq_toPCWorld x p.2)
  have hreal := h _ _ (hcons u hu) (hcons u' hu')
  rw [A.value_eq_ratCast P Q hQ _ _ (PCWorld.payout_eq_ratCast _),
    A.value_eq_ratCast P Q hQ _ _ (PCWorld.payout_eq_ratCast _)] at hreal
  rw [htransfer u, htransfer u']
  exact_mod_cast hreal

/-- **The concrete settlement test.**  Decidable: a `Fintype` quantifier over
`BoolPCWorld.FiniteWorld B = Fin B → Bool` with rational comparison.  This is the
object the paper's `settled` Turing machine (`app:prandaff`) decides — stated here so that
a checker's correctness is a *theorem* rather than an assumption.

The test is **agreement within a rational tolerance** `tol`, not exact agreement.  Exact
agreement is `tol = 0`; the tolerance is what makes the test satisfiable for a
combination-determined threshold mesh, whose completed worlds genuinely disagree about the
individual threshold sentences (`def:affthmval` determines the *combination*). -/
def AffineCombination.SettlementTest (A : AffineCombination) (Q : ℕ → Sentence → ℚ)
    (stage : Finset Sentence) (tol : ℚ) : Prop :=
  ∀ u u' : BoolPCWorld.FiniteWorld (A.settlementAtomLimit stage),
    (∀ φ ∈ stage, BoolPCWorld.eval u.toBoolPCWorld φ = true) →
    (∀ φ ∈ stage, BoolPCWorld.eval u'.toBoolPCWorld φ = true) →
      |A.valueRat Q u.payoutRat - A.valueRat Q u'.payoutRat| ≤ tol

instance AffineCombination.SettlementTest.decidable (A : AffineCombination)
    (Q : ℕ → Sentence → ℚ) (stage : Finset Sentence) (tol : ℚ) :
    Decidable (A.SettlementTest Q stage tol) := by
  unfold AffineCombination.SettlementTest
  infer_instance

/-! ### A non-dependent presentation of the test

`SettlementTest` quantifies over `BoolPCWorld.FiniteWorld B = Fin B → Bool`, whose *type*
depends on `B` — which is computed from the input.  Lean's `Computable` machinery wants
`Primcodable` domains and does not decompose a `decide` over such a dependent family, so no
code can be shown to recognize the test in that form.

`SettlementTestBool` is the same test presented over `List Bool` — one non-dependent
`Primcodable` type — with `settlementTestBool_iff` proving them equivalent.  The checker's
obligation is stated against the Bool version.  Bit-vectors are enumerated as lists rather
than as naturals-with-`Nat.testBit` deliberately: the list route needs only `List.ofFn`
length/index lemmas, where the numeric route would need bit arithmetic Mathlib does not
carry. -/

/-- Every Boolean list of a given length. -/
def allBitLists : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allBitLists n).flatMap (fun l => [false :: l, true :: l])

lemma mem_allBitLists : ∀ (n : ℕ) (l : List Bool), l ∈ allBitLists n ↔ l.length = n
  | 0, l => by
      simp only [allBitLists, List.mem_singleton]
      exact ⟨fun h => by rw [h]; rfl, fun h => List.length_eq_zero_iff.mp h⟩
  | n + 1, l => by
      simp only [allBitLists, List.mem_flatMap, List.mem_cons,
        List.not_mem_nil, or_false]
      constructor
      · rintro ⟨t, ht, rfl | rfl⟩ <;>
          simp [(mem_allBitLists n t).1 ht]
      · intro h
        cases l with
        | nil => simp at h
        | cons b t =>
            refine ⟨t, (mem_allBitLists n t).2 (by simpa using h), ?_⟩
            cases b <;> simp

/-- The finite world denoted by a bit list (missing entries read `false`). -/
def bitsToFin (B : ℕ) (l : List Bool) : BoolPCWorld.FiniteWorld B := fun a => l.getD a false

@[simp] lemma bitsToFin_ofFn {B : ℕ} (u : BoolPCWorld.FiniteWorld B) :
    bitsToFin B (List.ofFn u) = u := by
  funext a
  rw [bitsToFin, List.getD_eq_getElem _ _ (by simp [a.isLt])]
  simp

/-- A bit list of the right length denotes the same world whether read dependently (through
`FiniteWorld B`) or non-dependently (through `BoolPCWorld.bitsWorld`).  Past the end of the
list both read `false`: `toBoolPCWorld` by its `dif_neg` branch, `bitsWorld` because
`getD` is out of range.  This is what lets the compiled test avoid `Fin B` entirely. -/
lemma toBoolPCWorld_bitsToFin {B : ℕ} {l : List Bool} (hl : l.length = B) :
    (bitsToFin B l).toBoolPCWorld = BoolPCWorld.bitsWorld l := by
  funext a
  rw [BoolPCWorld.FiniteWorld.toBoolPCWorld, BoolPCWorld.bitsWorld]
  by_cases h : a < B
  · simp [h, bitsToFin]
  · rw [dif_neg h, List.getD_eq_default _ _ (by omega)]

lemma payoutRat_bitsToFin {B : ℕ} {l : List Bool} (hl : l.length = B) :
    (bitsToFin B l).payoutRat = BoolPCWorld.bitsPayoutRat l := by
  funext φ
  rw [BoolPCWorld.FiniteWorld.payoutRat, BoolPCWorld.bitsPayoutRat,
    toBoolPCWorld_bitsToFin hl]

lemma bitsWorld_ofFn {B : ℕ} (u : BoolPCWorld.FiniteWorld B) :
    BoolPCWorld.bitsWorld (List.ofFn u) = u.toBoolPCWorld := by
  have h := toBoolPCWorld_bitsToFin (B := B) (l := List.ofFn u) (by simp)
  rw [bitsToFin_ofFn] at h
  exact h.symm

lemma bitsPayoutRat_ofFn {B : ℕ} (u : BoolPCWorld.FiniteWorld B) :
    BoolPCWorld.bitsPayoutRat (List.ofFn u) = u.payoutRat := by
  have h := payoutRat_bitsToFin (B := B) (l := List.ofFn u) (by simp)
  rw [bitsToFin_ofFn] at h
  exact h.symm

/-! ### Extracting the stage's sentences

`Finset.toList` is noncomputable (it picks a representative through `Multiset.toList`), so
it cannot appear in a test we intend to compile.  `Finset.sort` under the order below is
both computable and *canonical*: it is the very order the stock `Finset Sentence` encoding
sorts by, so `stageSort` is the list that stage's own code decodes to.  That is what lets
the compiled checker recover the stage from its encoding. -/

/-- The order the stock `Finset Sentence` encoding sorts by: comparison of Gödel codes. -/
def sentenceCodeLE (φ ψ : Sentence) : Prop := Encodable.encode φ ≤ Encodable.encode ψ

instance : DecidableRel sentenceCodeLE := fun _ _ => Nat.decLe _ _
instance : IsTrans Sentence sentenceCodeLE := ⟨fun _ _ _ hab hbc => Nat.le_trans hab hbc⟩
instance : Std.Antisymm sentenceCodeLE :=
  ⟨fun _ _ hab hba => Encodable.encode_injective (Nat.le_antisymm hab hba)⟩
instance : Std.Total sentenceCodeLE :=
  ⟨fun φ ψ => Nat.le_total (Encodable.encode φ) (Encodable.encode ψ)⟩

/-- The stage's sentences, in the canonical order of its own encoding. -/
def stageSort (stage : Finset Sentence) : List Sentence := stage.sort sentenceCodeLE

@[simp] lemma mem_stageSort (stage : Finset Sentence) (φ : Sentence) :
    φ ∈ stageSort stage ↔ φ ∈ stage := Finset.mem_sort _

/-- Every sentence of the stage is satisfied by the world a bit list denotes.

A `List.all` over `stageSort`, not a `Finset` quantifier: `Primrec` decomposes the former
and not the latter. -/
def stageSatBits (stage : Finset Sentence) (l : List Bool) : Bool :=
  (stageSort stage).all fun φ => BoolPCWorld.eval (BoolPCWorld.bitsWorld l) φ

lemma stageSatBits_eq_true_iff (stage : Finset Sentence) (l : List Bool) :
    stageSatBits stage l = true ↔
      ∀ φ ∈ stage, BoolPCWorld.eval (BoolPCWorld.bitsWorld l) φ = true := by
  simp [stageSatBits, List.all_eq_true]

/-- Two rationals within a tolerance, as a `Bool` built from `≤` alone.  Subtraction and
`|·|` are deliberately avoided: the primitive-recursive checker has `ratLE_prim` and
`ratAdd_prim`, so this form compiles with no further rational arithmetic. -/
def ratWithin (x y tol : ℚ) : Bool := decide (x ≤ y + tol) && decide (y ≤ x + tol)

lemma ratWithin_eq_true_iff (x y tol : ℚ) :
    ratWithin x y tol = true ↔ |x - y| ≤ tol := by
  rw [ratWithin, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff,
    abs_sub_le_iff, sub_le_iff_le_add, sub_le_iff_le_add, add_comm tol y, add_comm tol x]

private lemma orNot_orNot_eq_true_iff (a b c : Bool) :
    ((!a) || (!b) || c) = true ↔ (a = true → b = true → c = true) := by
  cases a <;> cases b <;> cases c <;> simp

/-- The settlement test as a Boolean function over a non-dependent enumeration.

Every quantifier is a `List.all` and every connective a `Bool` operation, over the
`Primcodable` types `List Bool`, `Sentence` and `ℚ`.  Nothing here mentions `Fin B`, and no
world appears as an argument — `bitsWorld` is applied and beta-reduced in place.  That is
what makes the test compilable; `settlementTestBool_iff` proves it is still the same
test. -/
def AffineCombination.SettlementTestBool (A : AffineCombination) (Q : ℕ → Sentence → ℚ)
    (stage : Finset Sentence) (tol : ℚ) : Bool :=
  (allBitLists (A.settlementAtomLimit stage)).all fun l =>
    (allBitLists (A.settlementAtomLimit stage)).all fun l' =>
      !(stageSatBits stage l) || !(stageSatBits stage l') ||
        ratWithin (A.valueRat Q (BoolPCWorld.bitsPayoutRat l))
          (A.valueRat Q (BoolPCWorld.bitsPayoutRat l')) tol

/-- The `List Bool` presentation is the same test.  Surjectivity of `bitsToFin` onto
`FiniteWorld B` (via `List.ofFn`) is what makes it complete, not merely sound. -/
lemma AffineCombination.settlementTestBool_iff (A : AffineCombination)
    (Q : ℕ → Sentence → ℚ) (stage : Finset Sentence) (tol : ℚ) :
    A.SettlementTestBool Q stage tol = true ↔ A.SettlementTest Q stage tol := by
  simp only [AffineCombination.SettlementTestBool, AffineCombination.SettlementTest,
    List.all_eq_true, orNot_orNot_eq_true_iff, stageSatBits_eq_true_iff,
    ratWithin_eq_true_iff]
  constructor
  · -- Completeness: every finite world is `bitsToFin` of its own `List.ofFn`.
    intro h u u' hu hu'
    have hall := h (List.ofFn u) ((mem_allBitLists _ _).2 (by simp))
      (List.ofFn u') ((mem_allBitLists _ _).2 (by simp))
    rw [bitsWorld_ofFn, bitsWorld_ofFn, bitsPayoutRat_ofFn, bitsPayoutRat_ofFn] at hall
    exact hall hu hu'
  · -- Soundness: a listed bit list has length `B`, so it denotes `bitsToFin B l`.
    intro h l hl l' hl'
    rw [← toBoolPCWorld_bitsToFin ((mem_allBitLists _ _).1 hl),
      ← toBoolPCWorld_bitsToFin ((mem_allBitLists _ _).1 hl'),
      ← payoutRat_bitsToFin ((mem_allBitLists _ _).1 hl),
      ← payoutRat_bitsToFin ((mem_allBitLists _ _).1 hl')]
    exact h _ _

/-- **The concrete test is exactly tolerance agreement.**  Both directions: sound (a
passing test bounds the spread of the real values over all plausible worlds) and complete
(a bounded spread makes the test pass).  Rationality of the market (`hQ`) is what carries
it; `truth` never appears — a checker cannot compute `truth`, and does not need to. -/
lemma AffineCombination.settlementTest_iff_agree (A : AffineCombination)
    (P : History) (Q : ℕ → Sentence → ℚ) (hQ : ∀ d φ, P d φ = (Q d φ : ℝ))
    (stage : Finset Sentence) (tol : ℚ) :
    A.SettlementTest Q stage tol ↔
      ∀ v w : PCWorld, v.ConsistentWith stage → w.ConsistentWith stage →
        |A.value P v.payout - A.value P w.payout| ≤ (tol : ℝ) :=
  ⟨fun htest v w hv hw => A.agree_of_finiteWorlds_agree P Q hQ stage tol htest v w hv hw,
    fun hagree => A.finiteWorlds_agree_of_agree P Q hQ stage tol hagree⟩

/-- **The concrete test is exactly settlement.**  The `tol = 0` specialization of
`settlementTest_iff_agree` against exact determination: an exactly passing test says every
plausible world values `As i` at `truth i`, and conversely.  Consistency (`hworld`) is
what turns agreement into agreement *with `truth`*. -/
lemma AffineCombination.DeterminedViaTheory.settlementTest_iff_settled
    {As : ℕ → AffineCombination} {P : History} {DP : DeductiveProcess} {truth : ℕ → ℝ}
    (hdet : AffineCombination.DeterminedViaTheory As P DP truth)
    (Q : ℕ → Sentence → ℚ) (hQ : ∀ d φ, P d φ = (Q d φ : ℝ))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (i j : ℕ) :
    (As i).SettlementTest Q (DP.D j) 0 ↔
      ∀ v : PCWorld, v.ConsistentWith (DP.D j) → (As i).value P v.payout = truth i := by
  rw [hdet.settled_iff_agree hworld i j,
    (As i).settlementTest_iff_agree P Q hQ (DP.D j) 0]
  simp only [Rat.cast_zero, abs_nonpos_iff, sub_eq_zero]

lemma AffineCombination.DeterminedViaTheory.unique
    {As : ℕ → AffineCombination} {P : History} {DP : DeductiveProcess}
    {x y : ℕ → ℝ}
    (hx : AffineCombination.DeterminedViaTheory As P DP x)
    (hy : AffineCombination.DeterminedViaTheory As P DP y)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    x = y := by
  funext n
  obtain ⟨v, hv⟩ := exists_consistentWithTheory DP hworld
  rw [← hx n v hv, hy n v hv]

/-- Completed-theory determination is closed under pointwise affine negation. -/
lemma AffineCombination.DeterminedViaTheory.neg
    {As : ℕ → AffineCombination} {P : History} {DP : DeductiveProcess}
    {truth : ℕ → ℝ}
    (h : AffineCombination.DeterminedViaTheory As P DP truth) :
    AffineCombination.DeterminedViaTheory (fun n => (As n).neg) P DP
      (fun n => -truth n) := by
  intro n v hv
  rw [AffineCombination.neg_value, h n v hv]
namespace AffineCombination

/-! ## Finite exact maturity-certificate semantics -/

/-- The semantic core of a finite exact maturity checker for a unit-magnitude trader.
Every numeric inequality is rational, and the universal plausible-world payoff claim is
reduced to the finite type of assignments to the first `B` atoms.  The rational quote
function is fixed by the market's actual partial-recursive presentation, rather than being
supplied by this object.

The name records what is *not* claimed: the proposition-valued fields are not an encoded
executable payload.  `unitMaturityCheckAtFuel` below is the Boolean checker whose clocked
market and process outputs entail them. -/
structure UnitMaturitySemanticCertificate (Tr : Trader) (P : History)
    (DP : DeductiveProcess) (market : MarketComputation P)
    (ε η : ℚ) (m : ℕ) where
  atomLimit : ℕ
  deduction_bounded : ∀ φ ∈ DP.D m, BoolPCWorld.atomBound φ ≤ atomLimit
  trades_bounded : ∀ d ≤ m, ∀ p ∈ (Tr.strat d).trades,
    BoolPCWorld.atomBound p.2 ≤ atomLimit
  risk : 1 - η ≤ Tr.partialMagnitudeRat
    (fun d φ => market.quote d (Encodable.encode φ)) m
  payoff : ∀ u : BoolPCWorld.FiniteWorld atomLimit,
    (∀ φ ∈ DP.D m, BoolPCWorld.eval u.toBoolPCWorld φ = true) →
      ε - η ≤ Tr.partialNetWorthRat
        (fun d φ => market.quote d (Encodable.encode φ)) u.payoutRat m

/-- A concrete support bound for every sentence inspected by maturity through day `m`.
Using sums rather than maxima keeps the membership proofs elementary; only finiteness and
the resulting upper bound matter to the exhaustive Boolean check. -/
def maturityAtomLimit (Tr : Trader) (DP : DeductiveProcess) (m : ℕ) : ℕ :=
  (DP.D m).sum BoolPCWorld.atomBound +
    ∑ d ∈ Finset.range (m + 1),
      ((Tr.strat d).trades.map (fun p => BoolPCWorld.atomBound p.2)).sum

/-- The same support bound computed from a decoded deductive stage. -/
def maturityAtomLimitFromStage (Tr : Trader) (stage : Finset Sentence) (m : ℕ) : ℕ :=
  stage.sum BoolPCWorld.atomBound +
    ∑ d ∈ Finset.range (m + 1),
      ((Tr.strat d).trades.map (fun p => BoolPCWorld.atomBound p.2)).sum

/-- The proposition checked for one finite Boolean world at one fuel bound. -/
def unitMaturityWorldProperty
    (Tr : Trader) (P : History) (market : MarketComputation P)
    (ε η : ℚ) (m fuel : ℕ) (stage : Finset Sentence)
    (u : BoolPCWorld.FiniteWorld (maturityAtomLimitFromStage Tr stage m)) : Prop :=
  (∀ φ : {φ // φ ∈ stage},
      BoolPCWorld.eval u.toBoolPCWorld φ.1 = true) →
    match Tr.partialNetWorthRatAtFuel market fuel u.payoutRat m with
    | none => False
    | some worth => ε - η ≤ worth

/-- An explicit executable decision procedure for the single-world maturity property.
The finite quantifier over the decoded deductive stage is handled by its `Fintype`
instance; the remaining branches are Boolean equality and rational comparison. -/
def unitMaturityWorldPropertyDecidable
    (Tr : Trader) (P : History) (market : MarketComputation P)
    (ε η : ℚ) (m fuel : ℕ) (stage : Finset Sentence)
    (u : BoolPCWorld.FiniteWorld (maturityAtomLimitFromStage Tr stage m)) :
    Decidable (unitMaturityWorldProperty Tr P market ε η m fuel stage u) := by
  unfold unitMaturityWorldProperty
  letI : Decidable (∀ φ : {φ // φ ∈ stage},
      BoolPCWorld.eval u.toBoolPCWorld φ.1 = true) :=
    Fintype.decidableForallFintype
  by_cases hstage : ∀ φ : {φ // φ ∈ stage},
      BoolPCWorld.eval u.toBoolPCWorld φ.1 = true
  · cases hworth : Tr.partialNetWorthRatAtFuel market fuel u.payoutRat m with
    | none =>
        exact isFalse (fun h => by
          have := h hstage
          simp at this)
    | some worth =>
        by_cases hle : ε - η ≤ worth
        · exact isTrue (fun _ => by simpa [hworth] using hle)
        · exact isFalse (fun h => hle (by simpa [hworth] using h hstage))
  · exact isTrue (fun h => (hstage h).elim)

/-- The executable bounded maturity check.  It accepts only after the certified process
program has produced stage `m`, all required market calls have terminated, the rational
risk inequality holds, and every finite Boolean world satisfying that stage passes the
rational payoff inequality. -/
def unitMaturityCheckAtFuel
    (Tr : Trader) (P : History) (DP : DeductiveProcess)
    (market : MarketComputation P) (process : DeductiveProcessComputation DP)
    (ε η : ℚ) (m fuel : ℕ) : Bool :=
  match process.stageAtFuel fuel m with
  | none => false
  | some stage =>
      match Tr.partialMagnitudeRatAtFuel market fuel m with
      | none => false
      | some risk => by
          letI : DecidablePred (fun u : BoolPCWorld.FiniteWorld
              (maturityAtomLimitFromStage Tr stage m) =>
              unitMaturityWorldProperty Tr P market ε η m fuel stage u) :=
            unitMaturityWorldPropertyDecidable Tr P market ε η m fuel stage
          letI : Decidable (∀ u : BoolPCWorld.FiniteWorld
              (maturityAtomLimitFromStage Tr stage m),
              unitMaturityWorldProperty Tr P market ε η m fuel stage u) :=
            Fintype.decidableForallFintype
          exact decide
            (1 - η ≤ risk ∧
              ∀ u : BoolPCWorld.FiniteWorld
                  (maturityAtomLimitFromStage Tr stage m),
                unitMaturityWorldProperty Tr P market ε η m fuel stage u)

lemma maturityAtomLimit_deduction_bounded
    (Tr : Trader) (DP : DeductiveProcess) (m : ℕ) :
    ∀ φ ∈ DP.D m, BoolPCWorld.atomBound φ ≤ maturityAtomLimit Tr DP m := by
  intro φ hφ
  have hsingle : BoolPCWorld.atomBound φ ≤
      (DP.D m).sum BoolPCWorld.atomBound :=
    Finset.single_le_sum (fun ψ _ => Nat.zero_le (BoolPCWorld.atomBound ψ)) hφ
  unfold maturityAtomLimit
  omega

lemma maturityAtomLimit_trades_bounded
    (Tr : Trader) (DP : DeductiveProcess) (m : ℕ) :
    ∀ d ≤ m, ∀ p ∈ (Tr.strat d).trades,
      BoolPCWorld.atomBound p.2 ≤ maturityAtomLimit Tr DP m := by
  intro d hd p hp
  have hmem : BoolPCWorld.atomBound p.2 ∈
      ((Tr.strat d).trades.map (fun q => BoolPCWorld.atomBound q.2)) :=
    List.mem_map.mpr ⟨p, hp, rfl⟩
  have hlocal : BoolPCWorld.atomBound p.2 ≤
      ((Tr.strat d).trades.map (fun q => BoolPCWorld.atomBound q.2)).sum :=
    List.single_le_sum (fun x _ => Nat.zero_le x) _ hmem
  have hday : d ∈ Finset.range (m + 1) := Finset.mem_range.mpr (by omega)
  have houter :
      ((Tr.strat d).trades.map (fun q => BoolPCWorld.atomBound q.2)).sum ≤
        ∑ j ∈ Finset.range (m + 1),
          ((Tr.strat j).trades.map
            (fun q => BoolPCWorld.atomBound q.2)).sum :=
    Finset.single_le_sum (fun j _ => Nat.zero_le
      ((Tr.strat j).trades.map
        (fun q => BoolPCWorld.atomBound q.2)).sum) hday
  unfold maturityAtomLimit
  omega

/-- A `true` bounded check produces the exact semantic certificate. -/
def unitMaturityCheckAtFuel_certificate
    {Tr : Trader} {P : History} {DP : DeductiveProcess}
    (market : MarketComputation P) (process : DeductiveProcessComputation DP)
    {ε η : ℚ} {m fuel : ℕ}
    (hcheck : unitMaturityCheckAtFuel Tr P DP market process ε η m fuel = true) :
    UnitMaturitySemanticCertificate Tr P DP market ε η m := by
  unfold unitMaturityCheckAtFuel at hcheck
  split at hcheck
  · contradiction
  · rename_i stage hstage
    split at hcheck
    · contradiction
    · rename_i risk hrisk
      letI : DecidablePred (fun u : BoolPCWorld.FiniteWorld
          (maturityAtomLimitFromStage Tr stage m) =>
          unitMaturityWorldProperty Tr P market ε η m fuel stage u) :=
        unitMaturityWorldPropertyDecidable Tr P market ε η m fuel stage
      letI : Decidable (∀ u : BoolPCWorld.FiniteWorld
          (maturityAtomLimitFromStage Tr stage m),
          unitMaturityWorldProperty Tr P market ε η m fuel stage u) :=
        Fintype.decidableForallFintype
      have hfinite := of_decide_eq_true hcheck
      have hstageEq := process.stageAtFuel_sound hstage
      subst stage
      refine {
        atomLimit := maturityAtomLimit Tr DP m
        deduction_bounded := maturityAtomLimit_deduction_bounded Tr DP m
        trades_bounded := maturityAtomLimit_trades_bounded Tr DP m
        risk := ?_
        payoff := ?_
      }
      · have hriskEq := Tr.partialMagnitudeRatAtFuel_sound market fuel m hrisk
        simpa [hriskEq] using hfinite.1
      · intro u hu
        have hworld := hfinite.2 u (fun φ => hu φ.1 φ.2)
        split at hworld
        · exact hworld.elim
        · next worth hworth =>
            have hworthEq :=
              Tr.partialNetWorthRatAtFuel_sound market fuel u.payoutRat m hworth
            rw [hworthEq] at hworld
            exact hworld

/-- Soundness of the finite rational/Boolean maturity certificate: exhaustive finite
assignments imply the universal real-valued plausible-world payoff condition in
`Trader.Matured`. -/
lemma UnitMaturitySemanticCertificate.sound
    {Tr : Trader} {P : History} {DP : DeductiveProcess}
    (market : MarketComputation P) {ε η : ℚ} {m : ℕ}
    (c : UnitMaturitySemanticCertificate Tr P DP market ε η m)
    (hmag : Tr.magnitude P = 1) :
    Tr.Matured P DP (ε : ℝ) (η : ℝ) m := by
  constructor
  · rw [hmag, mul_one, Tr.partialMagnitude_eq_ratCast P
      (fun d φ => market.quote d (Encodable.encode φ)) market.quote_exact]
    exact_mod_cast c.risk
  · intro v hv
    let u : BoolPCWorld.FiniteWorld c.atomLimit :=
      BoolPCWorld.FiniteWorld.restrict (BoolPCWorld.ofPCWorld v) c.atomLimit
    have hu : ∀ φ ∈ DP.D m,
        BoolPCWorld.eval u.toBoolPCWorld φ = true := by
      intro φ hφ
      dsimp only [u]
      rw [BoolPCWorld.eval_toBoolPCWorld_restrict _ _ _
        (c.deduction_bounded φ hφ)]
      apply (BoolPCWorld.eval_eq_true_iff_holds _ _).2
      simpa using hv φ hφ
    have hpay := c.payoff u hu
    have hworth :
        Tr.partialNetWorthRat
            (fun d φ => market.quote d (Encodable.encode φ)) u.payoutRat m =
          Tr.partialNetWorthRat
            (fun d φ => market.quote d (Encodable.encode φ)) v.payoutRat m := by
      apply Tr.partialNetWorthRat_congr
      intro d hd p hp
      exact BoolPCWorld.FiniteWorld.payoutRat_restrict_ofPCWorld
        v c.atomLimit p.2 (c.trades_bounded d hd p hp)
    rw [hworth] at hpay
    rw [hmag, mul_one,
      Tr.netWorth_eq_ratCast P
        (fun d φ => market.quote d (Encodable.encode φ)) market.quote_exact
        v v.payoutRat
        v.payout_eq_ratCast m]
    exact_mod_cast hpay

/-- A `true` bounded check is a genuine maturity witness for a unit-magnitude trader: the
no-false-positive direction for the executable checker. -/
lemma unitMaturityCheckAtFuel_sound
    {Tr : Trader} {P : History} {DP : DeductiveProcess}
    (market : MarketComputation P) (process : DeductiveProcessComputation DP)
    {ε η : ℚ} {m fuel : ℕ}
    (hcheck : unitMaturityCheckAtFuel Tr P DP market process ε η m fuel = true)
    (hmag : Tr.magnitude P = 1) :
    Tr.Matured P DP (ε : ℝ) (η : ℝ) m :=
  (unitMaturityCheckAtFuel_certificate market process hcheck).sound market hmag

/-- Semantic completeness of the finite rational/Boolean reduction.  Every genuine
rational-parameter maturity witness for a unit-magnitude trader yields a finite support
bound and the exact rational inequalities consumed by the semantic certificate.  No
computability claim is made here. -/
def UnitMaturitySemanticCertificate.ofMatured
    {Tr : Trader} {P : History} {DP : DeductiveProcess}
    (market : MarketComputation P) {ε η : ℚ} {m : ℕ}
    (hmature : Tr.Matured P DP (ε : ℝ) (η : ℝ) m)
    (hmag : Tr.magnitude P = 1) :
    UnitMaturitySemanticCertificate Tr P DP market ε η m := by
  let Q : ℕ → Sentence → ℚ :=
    fun d φ => market.quote d (Encodable.encode φ)
  refine {
    atomLimit := maturityAtomLimit Tr DP m
    deduction_bounded := maturityAtomLimit_deduction_bounded Tr DP m
    trades_bounded := maturityAtomLimit_trades_bounded Tr DP m
    risk := ?_
    payoff := ?_
  }
  · have hrisk := hmature.1
    change 1 - η ≤ Tr.partialMagnitudeRat Q m
    rw [hmag, mul_one,
      Tr.partialMagnitude_eq_ratCast P Q market.quote_exact m] at hrisk
    exact_mod_cast hrisk
  · intro u hu
    let v : PCWorld := u.toBoolPCWorld.toPCWorld
    have hv : v.ConsistentWith (DP.D m) := by
      intro φ hφ
      exact (BoolPCWorld.eval_eq_true_iff_holds u.toBoolPCWorld φ).mp (hu φ hφ)
    have hpay := hmature.2 v hv
    have hpayout : ∀ φ, v.payout φ = (u.payoutRat φ : ℝ) := by
      intro φ
      rw [v.payout_eq_ratCast]
      congr 1
      exact (BoolPCWorld.FiniteWorld.payoutRat_eq_toPCWorld u φ).symm
    change ε - η ≤ Tr.partialNetWorthRat Q u.payoutRat m
    rw [hmag, mul_one,
      Tr.netWorth_eq_ratCast P Q market.quote_exact v u.payoutRat hpayout m] at hpay
    exact_mod_cast hpay

/-- Exact two-way semantic characterization of unit-trader maturity by the finite
rational/Boolean certificate core: the completeness half of the maturity reduction, showing
the finite certificate loses nothing that `Trader.Matured` records. -/
lemma UnitMaturitySemanticCertificate.nonempty_iff_matured
    {Tr : Trader} {P : History} {DP : DeductiveProcess}
    (market : MarketComputation P) {ε η : ℚ} {m : ℕ}
    (hmag : Tr.magnitude P = 1) :
    Nonempty (UnitMaturitySemanticCertificate Tr P DP market ε η m) ↔
      Tr.Matured P DP (ε : ℝ) (η : ℝ) m := by
  constructor
  · rintro ⟨c⟩
    exact c.sound market hmag
  · intro hmature
    exact ⟨UnitMaturitySemanticCertificate.ofMatured market hmature hmag⟩

/-- No genuine unit-trader maturity witness is missed forever: one finite interpreter
clock simultaneously recovers the deductive stage and every exact rational market quote
needed by the trader prefix, after which the exhaustive Boolean checker accepts. -/
lemma unitMaturityCheckAtFuel_eventually_complete
    {Tr : Trader} {P : History} {DP : DeductiveProcess}
    (market : MarketComputation P) (process : DeductiveProcessComputation DP)
    {ε η : ℚ} {m : ℕ}
    (hmature : Tr.Matured P DP (ε : ℝ) (η : ℝ) m)
    (hmag : Tr.magnitude P = 1) :
    ∃ fuel, unitMaturityCheckAtFuel Tr P DP market process ε η m fuel = true := by
  let c : UnitMaturitySemanticCertificate Tr P DP market ε η m :=
    UnitMaturitySemanticCertificate.ofMatured market hmature hmag
  obtain ⟨processFuel, hprocess⟩ := process.stageAtFuel_complete m
  obtain ⟨marketFuel, hmarket⟩ := market.exists_fuel_quoteAtFuel_list
    (Tr.partialMagnitudeRatQueries m ++ Tr.partialNetWorthRatQueries m)
  let fuel := max processFuel marketFuel
  have hstage : process.stageAtFuel fuel m = some (DP.D m) :=
    process.stageAtFuel_mono (le_max_left _ _) hprocess
  have hquotes : ∀ query ∈
      Tr.partialMagnitudeRatQueries m ++ Tr.partialNetWorthRatQueries m,
      market.quoteAtFuel fuel query.1 query.2 =
        some (market.quote query.1 (Encodable.encode query.2)) := by
    intro query hquery
    exact market.quoteAtFuel_mono (le_max_right _ _) (hmarket query hquery)
  have hmagnitude : Tr.partialMagnitudeRatAtFuel market fuel m = some
      (Tr.partialMagnitudeRat
        (fun d φ => market.quote d (Encodable.encode φ)) m) :=
    Tr.partialMagnitudeRatAtFuel_complete market fuel m (fun query hquery =>
      hquotes query (List.mem_append.mpr (Or.inl hquery)))
  have hnetWorth (u : BoolPCWorld.FiniteWorld (maturityAtomLimit Tr DP m)) :
      Tr.partialNetWorthRatAtFuel market fuel u.payoutRat m = some
        (Tr.partialNetWorthRat
          (fun d φ => market.quote d (Encodable.encode φ)) u.payoutRat m) :=
    Tr.partialNetWorthRatAtFuel_complete market fuel u.payoutRat m
      (fun query hquery =>
        hquotes query (List.mem_append.mpr (Or.inr hquery)))
  refine ⟨fuel, ?_⟩
  unfold unitMaturityCheckAtFuel
  rw [hstage, hmagnitude]
  letI : DecidablePred (fun u : BoolPCWorld.FiniteWorld
      (maturityAtomLimitFromStage Tr (DP.D m) m) =>
      unitMaturityWorldProperty Tr P market ε η m fuel (DP.D m) u) :=
    unitMaturityWorldPropertyDecidable Tr P market ε η m fuel (DP.D m)
  letI : Decidable (∀ u : BoolPCWorld.FiniteWorld
      (maturityAtomLimitFromStage Tr (DP.D m) m),
      unitMaturityWorldProperty Tr P market ε η m fuel (DP.D m) u) :=
    Fintype.decidableForallFintype
  apply decide_eq_true
  constructor
  · exact c.risk
  · intro u hu
    split
    · next hnone =>
        exact (Option.some_ne_none _ ((hnetWorth u).symm.trans hnone)).elim
    · next worth hsome =>
        cases Option.some.inj ((hnetWorth u).symm.trans hsome)
        exact c.payoff u (fun φ hφ => hu ⟨φ, hφ⟩)
end AffineCombination

end LogicalInduction
