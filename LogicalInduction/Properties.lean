/-
# Part III — Property tail (`LogicalInduction.Properties`)

Every property is conditioned on `[IsLogicalInductor P]` and proved via the
assume-fail → build-trader → invoke-criterion pattern, with the exploiting trader's
efficient computability certified through `EF.cost`. Grouped by paper subsection (see
roadmap §3, Part III). **Bold = M3 downstream-priority slice** (discharges deference
hypotheses).

* Convergence / Coherence:    **`thm:con`**, **`thm:lc`**
* Timely learning:            **`thm:provind`**, `thm:perkno`, `thm:tbo`
* Affine lifts (via `thm:affpolymax`): `thm:affprovind`, `thm:affcoh`, `thm:peraffkno`,
    `thm:recunbiasedaff`, `thm:wubaff`, `thm:prandaff`
* Calibration / unbiasedness: `thm:simcal`, `thm:recurringunbiasedness`, `thm:wub`
* Statistical patterns:       `thm:benford`, `thm:prand`
* Logical relationships:      `thm:lex`
* Non-Dogmatism / closure:    **`thm:nd`**, `thm:ifp`, `thm:obu`, `thm:ob`, `thm:dus`,
    `thm:strict`, `thm:scon`
* Expectations (LUV lifts):   **`thm:ec`**, **`thm:loe`**, `thm:ei`, **`thm:expprovind`**,
    `thm:expcoh`, `thm:perexpkno`, `thm:exppolymax`, `thm:recurringunbiasednessexp`,
    `thm:wubexp`, `thm:prandexp`
* Trust in consistency:       `thm:pac`, `thm:pazfc`, `thm:incons`
* Halting:                    `thm:halts`, `thm:loops`, `thm:dontwait`
* Introspection:              `thm:ref`, `thm:lp`, `thm:epr`
* Self-Trust:                 `thm:er`, **`thm:cee`**, **`thm:ceu`**, **`thm:ccee`**,
    **`thm:st`**

Naming caution (from the deference audit): the shorthand "cee" = the paper's `thm:ceu`
*No Expected Net Update*; the paper's `thm:cee` is the distinct *Expected Future
Expectations*. Don't conflate them.

This Part will certainly grow past one file — promote it to a `Properties/` directory
(one file per family) plus this file as the roll-up when it does.

## M2 status — the end-to-end loop, wired once and completely.

`buyDaily_exploits` below is the **M2 proof-of-concept**: the `assume-fail → build-trader
→ certify-e.c. → invoke-criterion` pattern, carried out with a *genuinely constructed*
exploiting trader whose efficient computability is *discharged through `EF.cost`* — no
arithmetic stub standing in for the exploit, no `sorry` anywhere in the chain.

The property is the **base case of Provability Induction** (`thm:provind`): a sentence `φ`
that the deductive process always affirms cannot be held a fixed `ε` below price 1 by a
logical inductor. The trader that forces this simply **buys one share of `φ` every day**;
because every plausible world already values `φ` at 1, its net worth is `∑ᵢ (1 − Pᵢ φ) ≥
(m+1)·ε`, which is bounded below (by 0) yet grows without bound — exploitation.

Scope note (honest): this is the cleanest *special case* — `φ` **always** deducible and
**uniformly** ε-underpriced — chosen so the exploitation is fully provable and the loop is
demonstrated with zero gaps. The general `thm:provind` (eventually deducible, `ε`-underpriced
*infinitely often*, via a continuous `max(0, ·)` buy-signal rather than a constant one) is
M3 work; it reuses this exact loop with a heavier accumulation argument.
-/
import LogicalInduction.Criterion
import LogicalInduction.Asymptotics
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.LiminfLimsup
import LogicalInduction.Computable

namespace LogicalInduction

open Filter Topology

/-! ### The exploiting trader (`def:trader`, constructed — not stubbed) -/

/-- The trader that buys exactly one share of `φ` on every day. Each day-`n` strategy is
the single pair `(1, φ)`: a constant (hence continuous, hence legal) trade of rank 0. This
is the exploiting trader for the base case of Provability Induction. -/
def buyDaily (φ : Sentence) : Trader where
  strat _ := { trades := [(EF.const 1, φ)]
               rank_le := by intro p hp; simp only [List.mem_singleton] at hp
                             subst hp; exact Nat.zero_le _ }

@[simp] theorem buyDaily_value (φ : Sentence) (V : History) (w : Sentence → ℝ) (n : ℕ) :
    ((buyDaily φ).strat n).value V w = w φ - V n φ := by
  simp [buyDaily, Strategy.value]

theorem buyDaily_netWorth (φ : Sentence) (V : History) (v : PCWorld) (m : ℕ) :
    (buyDaily φ).netWorth V v m = ∑ i ∈ Finset.range (m + 1), (v.payout φ - V i φ) := by
  simp [Trader.netWorth]

/-! ### Efficient computability, via the clocked interpreter (no stub)

The day-`n` strategy is the same constant list `[(const 1, φ)]` for every `n`, so the
program that computes it is `Code.const K`, where `K` is that list's code. It halts within
`n + K + 1` fuel (`evaln_const_self`), which is affine in `n`, hence within the polynomial
budget the faithful `EfficientlyComputable` requires. This certifies e.c. through the
genuine `dd:fuel` model — a single program producing the strategies under a poly clock. -/
theorem buyDaily_ec (φ : Sentence) : EfficientlyComputable (buyDaily φ) := by
  refine ⟨Nat.Partrec.Code.const (Encodable.encode ([(EF.const 1, φ)] : List (EF × Sentence))),
          Encodable.encode ([(EF.const 1, φ)] : List (EF × Sentence)) + 1, 1, fun n => ?_⟩
  have hs : ((buyDaily φ).strat n).trades = [(EF.const 1, φ)] := rfl
  rw [hs]
  exact Nat.Partrec.Code.evaln_mono (by simp only [pow_one]; nlinarith) (evaln_const_self _ n)

/-! ### The exploitation (`def:exploitation`, proved in full) -/

/-- If `φ` is always deducible and the market holds it uniformly `ε` below 1, the
do-buy-daily trader exploits: bounded below (net worth `≥ 0` in every plausible world,
since every world consistent with `Dₘ ∋ φ` values `φ` at 1) yet unbounded above (net worth
`≥ (m+1)·ε → ∞`). -/
theorem buyDaily_exploits (P : History) (DP : DeductiveProcess) (φ : Sentence) (ε : ℝ)
    (hε : 0 < ε) (hded : ∀ n, φ ∈ DP.D n) (hunder : ∀ n, P n φ ≤ 1 - ε)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (buyDaily φ).Exploits P DP := by
  -- In any world plausible on day `m`, `φ ∈ D m` is affirmed, so its payout is 1.
  have hpay : ∀ (m : ℕ) (v : PCWorld), v.ConsistentWith (DP.D m) → v.payout φ = 1 := by
    intro m v hv
    rw [PCWorld.payout, if_pos (hv φ (hded m))]
  refine ⟨⟨0, ?_⟩, ?_⟩
  · -- Bounded below by 0: every assessment is a sum of nonnegative `(1 − Pᵢ φ)` terms.
    rintro x ⟨m, v, hv, rfl⟩
    rw [buyDaily_netWorth]
    refine Finset.sum_nonneg (fun i _ => ?_)
    rw [hpay m v hv]; have := hunder i; linarith
  · -- Unbounded above: assessment on day `m` is `≥ (m+1)·ε`, which diverges.
    rintro ⟨B, hB⟩
    have key : ∀ m : ℕ, (m + 1 : ℝ) * ε ≤ B := by
      intro m
      obtain ⟨v, hv⟩ := hcons m
      have hmem : (buyDaily φ).netWorth P v m ∈ (buyDaily φ).plausibleAssessments P DP :=
        ⟨m, v, hv, rfl⟩
      have hge : (m + 1 : ℝ) * ε ≤ (buyDaily φ).netWorth P v m := by
        rw [buyDaily_netWorth, hpay m v hv]
        calc (m + 1 : ℝ) * ε
            = ∑ _i ∈ Finset.range (m + 1), ε := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
          _ ≤ ∑ i ∈ Finset.range (m + 1), (1 - P i φ) :=
              Finset.sum_le_sum (fun i _ => by have := hunder i; linarith)
      exact hge.trans (hB hmem)
    obtain ⟨m, hm⟩ := exists_nat_gt (B / ε)
    have hBm : B < (m : ℝ) * ε := by rw [div_lt_iff₀ hε] at hm; linarith
    have := key m
    push_cast at this
    nlinarith [this, hBm, hε]

/-! ### The criterion consequence (the loop closed against `def:lic`) -/

/-- **Base case of Provability Induction** (`thm:provind`), stated against `def:lic`: a
logical inductor cannot hold an always-deducible sentence uniformly below price 1. For
every `ε > 0` the price rises above `1 − ε` at some day. -/
theorem lic_deducible_price_near_one (P : History) (DP : DeductiveProcess)
    [hLI : IsLogicalInductor P DP] (φ : Sentence) (ε : ℝ) (hε : 0 < ε)
    (hded : ∀ n, φ ∈ DP.D n) (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ∃ n, 1 - ε < P n φ := by
  by_contra h
  push_neg at h
  exact hLI.noExploit (buyDaily φ) (buyDaily_ec φ) (buyDaily_exploits P DP φ ε hε hded h hcons)

/-! ## M3 — Provability Induction in the limit (fixed sentence), via accumulation

The base case above assumed *uniform* underpricing and concluded only that the price rises
above `1 − ε` *once*. The genuine `thm:provind` conclusion is the **limit** statement
`Pₙ(φ) → 1`. For a *fixed* always-deducible `φ` we obtain it from the **same constant
`buyDaily` trader** — no new construction, no new e.c. proof — by a stronger analysis: if
the price dips below `1 − ε` *infinitely often*, then buying one share a day accumulates
profit `≥ ε` on each of infinitely many days, so the net worth is unbounded. (The
*responsive* `max(0,·)` trader and its harder efficient-computability proof are only needed
for the **sequence** form of `thm:provind` — an `𝓔𝓒`-sequence `φₙ` — which is deferred; see
the milestone notes.) -/

/-- Exploitation under *infinitely-often* underpricing (the accumulation argument). With
prices bounded by `1`, every plausible assessment is `≥ 0` (bounded below); and along the
subsequence of underpriced days the net worth grows without bound. -/
theorem buyDaily_exploits_freq (P : History) (DP : DeductiveProcess) (φ : Sentence) (ε : ℝ)
    (hε : 0 < ε) (hded : ∀ n, φ ∈ DP.D n) (hP1 : ∀ n, P n φ ≤ 1)
    (hfreq : ∃ᶠ n in atTop, P n φ ≤ 1 - ε)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (buyDaily φ).Exploits P DP := by
  have hpay : ∀ (m : ℕ) (v : PCWorld), v.ConsistentWith (DP.D m) → v.payout φ = 1 :=
    fun m v hv => by rw [PCWorld.payout, if_pos (hv φ (hded m))]
  refine ⟨⟨0, ?_⟩, ?_⟩
  · -- bounded below by 0: each term `1 − Pᵢ φ ≥ 0` since `Pᵢ φ ≤ 1`.
    rintro x ⟨m, v, hv, rfl⟩
    rw [buyDaily_netWorth]
    refine Finset.sum_nonneg (fun i _ => ?_)
    rw [hpay m v hv]; have := hP1 i; linarith
  · -- unbounded above: extract the underpriced subsequence and accumulate.
    rintro ⟨B, hB⟩
    obtain ⟨g, hg_mono, hg⟩ := extraction_of_frequently_atTop hfreq
    obtain ⟨M, hM⟩ := exists_nat_gt (B / ε)
    obtain ⟨v, hv⟩ := hcons (g M)
    -- the day-`g M` assessment is `≥ (M+1)·ε`.
    have hsub : (Finset.range (M + 1)).image g ⊆ Finset.range (g M + 1) := by
      intro i hi
      simp only [Finset.mem_image, Finset.mem_range] at hi
      obtain ⟨k, hk, rfl⟩ := hi
      exact Finset.mem_range.mpr (by have := hg_mono.monotone (Nat.lt_succ_iff.mp hk); omega)
    have hge : (M + 1 : ℝ) * ε ≤ (buyDaily φ).netWorth P v (g M) := by
      rw [buyDaily_netWorth, hpay (g M) v hv]
      calc (M + 1 : ℝ) * ε
          = ∑ _k ∈ Finset.range (M + 1), ε := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
        _ ≤ ∑ k ∈ Finset.range (M + 1), (1 - P (g k) φ) :=
            Finset.sum_le_sum (fun k _ => by have := hg k; linarith)
        _ = ∑ i ∈ (Finset.range (M + 1)).image g, (1 - P i φ) := by
            rw [Finset.sum_image (hg_mono.injective.injOn)]
        _ ≤ ∑ i ∈ Finset.range (g M + 1), (1 - P i φ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub
              (fun i _ _ => by have := hP1 i; linarith)
    have hmem : (buyDaily φ).netWorth P v (g M) ∈ (buyDaily φ).plausibleAssessments P DP :=
      ⟨g M, v, hv, rfl⟩
    have hBm : B < (M + 1 : ℝ) * ε := by
      rw [div_lt_iff₀ hε] at hM; nlinarith
    exact absurd (le_trans hge (hB hmem)) (by linarith)

/-- **Provability Induction, limiting form, for a fixed sentence** (`thm:provind`): under a
logical inductor, an always-deducible `φ` with prices in `(-∞, 1]` has `Pₙ(φ)` eventually
within any `ε` of `1`. This is the criterion output — `¬(underpriced infinitely often)`. -/
theorem lic_deducible_eventually_ge (P : History) (DP : DeductiveProcess)
    [hLI : IsLogicalInductor P DP] (φ : Sentence) (hded : ∀ n, φ ∈ DP.D n)
    (hP1 : ∀ n, P n φ ≤ 1) (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, 1 - ε < P n φ := by
  by_contra h
  rw [not_eventually] at h
  simp only [not_lt] at h
  exact hLI.noExploit (buyDaily φ) (buyDaily_ec φ)
    (buyDaily_exploits_freq P DP φ ε hε hded hP1 h hcons)

/-- **Provability Induction, convergence form** (`thm:provind`): the price of an
always-deducible sentence converges to `1`. Packages `lic_deducible_eventually_ge` with the
upper bound `Pₙ(φ) ≤ 1` into `ConvergesTo` (`dd:asymp`). -/
theorem lic_deducible_tendsto_one (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (φ : Sentence) (hded : ∀ n, φ ∈ DP.D n)
    (hP1 : ∀ n, P n φ ≤ 1) (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ConvergesTo (fun n => P n φ) 1 := by
  refine Metric.tendsto_atTop.mpr (fun ε hε => ?_)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (lic_deducible_eventually_ge P DP φ hded hP1 hcons ε hε)
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, abs_lt]
  have h1 := hN n hn
  have h2 := hP1 n
  constructor <;> linarith

/-! ## M3 — Limit Coherence, bullet (2): disprovable ⇒ price → 0 (`thm:lc`)

The dual of the provability bullet, via the mirror-image **sell** trader. If `φ` is
disprovable — `∼φ` always deducible — then every plausible world values `φ` at `0`, so
selling one share of `φ` a day yields net worth `∑ᵢ Pᵢ(φ) ≥ 0`; if the price stays above
`ε` infinitely often that is unbounded, so a logical inductor forces `Pₙ(φ) → 0`. Same
constant-trader, same already-certified efficient computability — only the sign flips. -/

/-- In a world consistent with a set containing `∼φ`, `φ` is false (Foundation Boolean
semantics: `∼φ = φ 🡒 ⊥`, so `Holds (∼φ) ↔ ¬ Holds φ`). -/
theorem PCWorld.payout_of_disprovable (v : PCWorld) (φ : Sentence) (h : v.Holds (∼φ)) :
    v.payout φ = 0 := by
  have : ¬ v.Holds φ := by
    simpa [PCWorld.Holds, LO.Propositional.Formula.Boolean.val,
      LO.Propositional.Formula.neg_def] using h
  rw [PCWorld.payout, if_neg this]

/-- The trader that sells one share of `φ` every day (buys `-1`). -/
def sellDaily (φ : Sentence) : Trader where
  strat _ := { trades := [(EF.const (-1), φ)]
               rank_le := by intro p hp; simp only [List.mem_singleton] at hp
                             subst hp; exact Nat.zero_le _ }

theorem sellDaily_netWorth (φ : Sentence) (V : History) (v : PCWorld) (m : ℕ) :
    (sellDaily φ).netWorth V v m = ∑ i ∈ Finset.range (m + 1), (V i φ - v.payout φ) := by
  simp only [Trader.netWorth, sellDaily, Strategy.value]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [EF.denote]

theorem sellDaily_ec (φ : Sentence) : EfficientlyComputable (sellDaily φ) := by
  refine ⟨Nat.Partrec.Code.const (Encodable.encode ([(EF.const (-1), φ)] : List (EF × Sentence))),
          Encodable.encode ([(EF.const (-1), φ)] : List (EF × Sentence)) + 1, 1, fun n => ?_⟩
  have hs : ((sellDaily φ).strat n).trades = [(EF.const (-1), φ)] := rfl
  rw [hs]
  exact Nat.Partrec.Code.evaln_mono (by simp only [pow_one]; nlinarith) (evaln_const_self _ n)

/-- Exploitation of the sell trader under infinitely-often *overpricing* of a disprovable
`φ`: net worth `∑ Pᵢ(φ) ≥ 0` (prices `≥ 0`), unbounded along the overpriced subsequence. -/
theorem sellDaily_exploits_freq (P : History) (DP : DeductiveProcess) (φ : Sentence) (ε : ℝ)
    (hε : 0 < ε) (hdis : ∀ n, (∼φ) ∈ DP.D n) (hP0 : ∀ n, 0 ≤ P n φ)
    (hfreq : ∃ᶠ n in atTop, ε ≤ P n φ)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (sellDaily φ).Exploits P DP := by
  have hpay : ∀ (m : ℕ) (v : PCWorld), v.ConsistentWith (DP.D m) → v.payout φ = 0 :=
    fun m v hv => PCWorld.payout_of_disprovable v φ (hv (∼φ) (hdis m))
  refine ⟨⟨0, ?_⟩, ?_⟩
  · rintro x ⟨m, v, hv, rfl⟩
    rw [sellDaily_netWorth]
    refine Finset.sum_nonneg (fun i _ => ?_)
    rw [hpay m v hv]; have := hP0 i; linarith
  · rintro ⟨B, hB⟩
    obtain ⟨g, hg_mono, hg⟩ := extraction_of_frequently_atTop hfreq
    obtain ⟨M, hM⟩ := exists_nat_gt (B / ε)
    obtain ⟨v, hv⟩ := hcons (g M)
    have hsub : (Finset.range (M + 1)).image g ⊆ Finset.range (g M + 1) := by
      intro i hi
      simp only [Finset.mem_image, Finset.mem_range] at hi
      obtain ⟨k, hk, rfl⟩ := hi
      exact Finset.mem_range.mpr (by have := hg_mono.monotone (Nat.lt_succ_iff.mp hk); omega)
    have hge : (M + 1 : ℝ) * ε ≤ (sellDaily φ).netWorth P v (g M) := by
      rw [sellDaily_netWorth, hpay (g M) v hv]
      calc (M + 1 : ℝ) * ε
          = ∑ _k ∈ Finset.range (M + 1), ε := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
        _ ≤ ∑ k ∈ Finset.range (M + 1), (P (g k) φ - 0) :=
            Finset.sum_le_sum (fun k _ => by have := hg k; linarith)
        _ = ∑ i ∈ (Finset.range (M + 1)).image g, (P i φ - 0) := by
            rw [Finset.sum_image (hg_mono.injective.injOn)]
        _ ≤ ∑ i ∈ Finset.range (g M + 1), (P i φ - 0) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub
              (fun i _ _ => by have := hP0 i; linarith)
    have hmem : (sellDaily φ).netWorth P v (g M) ∈ (sellDaily φ).plausibleAssessments P DP :=
      ⟨g M, v, hv, rfl⟩
    have hBm : B < (M + 1 : ℝ) * ε := by rw [div_lt_iff₀ hε] at hM; nlinarith
    exact absurd (le_trans hge (hB hmem)) (by linarith)

/-! ### Boolean payout lemmas — the ingredients for finite additivity (`thm:lc` bullet 3)

A p.c. world evaluates compound sentences by Boolean algebra (Foundation's `val`), so its
`{0,1}` payouts add the way a coherent probability must. These are the reusable pieces the
additivity trader's exploitation rests on. -/

/-- `∼χ`-worlds falsify `χ` (Foundation: `∼χ = χ 🡒 ⊥`). -/
theorem PCWorld.holds_neg (v : PCWorld) (χ : Sentence) : v.Holds (∼χ) ↔ ¬ v.Holds χ := by
  simp [PCWorld.Holds, LO.Propositional.Formula.Boolean.val]

theorem PCWorld.holds_or (v : PCWorld) (φ ψ : Sentence) :
    v.Holds (φ ⋎ ψ) ↔ v.Holds φ ∨ v.Holds ψ := Iff.rfl

theorem PCWorld.holds_and (v : PCWorld) (φ ψ : Sentence) :
    v.Holds (φ ⋏ ψ) ↔ v.Holds φ ∧ v.Holds ψ := Iff.rfl

/-- **Finite additivity of payout under exclusion.** If `∼(φ∧ψ)` holds (the disjuncts are
mutually exclusive), the payout of `φ∨ψ` is the sum of the payouts — the world-level identity
behind coherent finite additivity. -/
theorem PCWorld.payout_or_of_excl (v : PCWorld) (φ ψ : Sentence)
    (h : v.Holds (∼(φ ⋏ ψ))) : v.payout (φ ⋎ ψ) = v.payout φ + v.payout ψ := by
  rw [PCWorld.holds_neg, PCWorld.holds_and] at h
  simp only [PCWorld.payout]
  by_cases hφ : v.Holds φ <;> by_cases hψ : v.Holds ψ
  · exact absurd ⟨hφ, hψ⟩ h
  · rw [if_pos (show v.Holds (φ ⋎ ψ) from Or.inl hφ), if_pos hφ, if_neg hψ]; norm_num
  · rw [if_pos (show v.Holds (φ ⋎ ψ) from Or.inr hψ), if_neg hφ, if_pos hψ]; norm_num
  · rw [if_neg (show ¬ v.Holds (φ ⋎ ψ) from not_or.mpr ⟨hφ, hψ⟩), if_neg hφ, if_neg hψ]; norm_num

/-- **Limit Coherence, bullet (2)** (`thm:lc`): the price of a disprovable sentence
converges to `0` under a logical inductor. -/
theorem lic_disprovable_tendsto_zero (P : History) (DP : DeductiveProcess)
    [hLI : IsLogicalInductor P DP] (φ : Sentence) (hdis : ∀ n, (∼φ) ∈ DP.D n)
    (hP0 : ∀ n, 0 ≤ P n φ) (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ConvergesTo (fun n => P n φ) 0 := by
  refine Metric.tendsto_atTop.mpr (fun ε hε => ?_)
  have hev : ∀ᶠ n in atTop, P n φ < ε := by
    by_contra h
    rw [not_eventually] at h
    simp only [not_lt] at h
    exact hLI.noExploit (sellDaily φ) (sellDaily_ec φ)
      (sellDaily_exploits_freq P DP φ ε hε hdis hP0 h hcons)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, abs_lt]
  have := hP0 n
  have h1 := hN n hn
  constructor <;> linarith

/-! ## `thm:con` — Convergence.

> The limit `P_∞(φ) := limₙ Pₙ(φ)` exists for all `φ`.  *(Garrabrant et al., `thm:con`.)*

The paper's argument (`sec:convergence` / `app:con`): if the market never makes up its mind
about `φ`, its price oscillates, and a trader can **arbitrage** the oscillation — buy `φ`
cheap, sell it back dear — pocketing a fixed profit on each swing at no risk, hence
exploiting. A logical inductor forbids this, so the price must converge.

This splits into two halves along the M2 pattern:

1. **The reduction (`exists_rat_oscillation_of_not_convergesTo`, proved below, no `sorry`).**
   Non-convergence of a `[0,1]`-bounded price forces a *rational* oscillation: `a < b` in `ℚ`
   with `Pₙφ < a` infinitely often and `Pₙφ > b` infinitely often. This is exactly the
   contrapositive of Mathlib's `tendsto_of_no_upcrossings`, taken over the dense set `↑ℚ ⊆ ℝ`
   — the "assume the property fails → extract the exploitable configuration" step, carried by
   a library lemma rather than hand-rolled.

2. **The exploiting trader (`oscillation_exploitable`, `sorry` — the genuine remaining work).**
   Given the oscillation, build the arbitrage trader and show it exploits. See that lemma's
   TODO for the concrete construction and the two obstacles it currently faces.

`lic_price_convergesTo` chains them against `def:lic`. -/

open Filter Topology in
/-- **Reduction step for `thm:con`** (fully proved). A `[0,1]`-bounded price that does *not*
converge must **oscillate across a rational gap**: there are rationals `a < b` with the price
below `a` infinitely often and above `b` infinitely often.

This is the contrapositive of `tendsto_of_no_upcrossings` instantiated at the dense range of
`(↑) : ℚ → ℝ`; the rationality of `a, b` is what lets the arbitrage trader use them as `EF`
constants. -/
theorem exists_rat_oscillation_of_not_convergesTo (P : History) (φ : Sentence)
    (hb : ∀ n, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hnc : ¬ ∃ L, ConvergesTo (fun n => P n φ) L) :
    ∃ a b : ℚ, (a : ℝ) < b ∧ (∃ᶠ n in atTop, P n φ < (a : ℝ)) ∧
      (∃ᶠ n in atTop, (b : ℝ) < P n φ) := by
  by_contra hcon
  refine hnc (tendsto_of_no_upcrossings (u := fun n => P n φ) Rat.denseRange_cast ?_
    (isBoundedUnder_of ⟨1, fun n => (hb n).2⟩) (isBoundedUnder_of ⟨0, fun n => (hb n).1⟩))
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hab ⟨hA, hB⟩
  exact hcon ⟨a, b, hab, hA, hB⟩

/-- **The oscillation-arbitrage trader exists and exploits** (`app:con`, the genuine hard
core — currently `sorry`).

Given a rational oscillation of `Pₙφ` across `[a, b]` (price `< a` i.o. and `> b` i.o.), with
plausible worlds available every day, there is an *efficiently computable* trader that
exploits `P`.

**The construction is genuinely subtle — hysteresis is required.** A *memoryless* target
holding `T(Pₙφ)` (hold a share when cheap, none when dear) does **not** work: its net worth is
`≈ Σ T(Pₙφ)·ΔPₙφ ≈ ∫ T dP`, and since `T` is a function of price alone this integral is
*path-independent* — it telescopes to `G(P_N) − G(P₀)` (a bounded state function) and nets
**zero over a closed oscillation cycle**. So a memoryless trader stays bounded and cannot
exploit. This is exactly the "discontinuous / not-well-formed trader" subtlety the paper flags
(`sec:convergence`): the real arbitrage needs a **stopping-time / hysteresis** rule — *buy* when
`Pₙφ < a`, then **hold** (memory!) until some later `m` with `Pₘφ > b`, then *sell* — so that
each completed swing banks `Pₘφ − Pₙφ ≥ b − a` at no risk (position closed ⇒ payout cancels),
and infinitely many swings give unbounded upside off bounded downside. Encoding that
path-dependent rule as a continuous `EF`-history function is the deferred work.

Status of the two ingredients:
- *Efficient computability — RESOLVED.* Such a trader references two consecutive days' prices;
  the day-`(n-1)` feature is now e.c. via `PolyEF.pricePred` (`Computable.lean`, the prec-fueled
  `predc`). So once the trader is written, its e.c. certification is in reach.
- *Exploitation inequality — the remaining hard core.* Constructing the hysteresis `EF` and
  proving its net worth is bounded below yet unbounded above under the oscillation hypothesis is
  a genuine discrete-arbitrage lemma (the paper itself sidesteps it in `app:con` by routing
  convergence through `thm:tbo`). Not yet formalized.

`sorry`, honestly; nothing is stubbed, and the earlier memoryless-`T` sketch is retracted as
mathematically insufficient. -/
theorem oscillation_exploitable (P : History) (DP : DeductiveProcess) (φ : Sentence)
    (a b : ℚ) (hab : (a : ℝ) < b) (hb : ∀ n, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hA : ∃ᶠ n in atTop, P n φ < (a : ℝ)) (hB : ∃ᶠ n in atTop, (b : ℝ) < P n φ) :
    ∃ Tr : Trader, EfficientlyComputable Tr ∧ Tr.Exploits P DP := by
  sorry

/-- **Convergence** (`thm:con`): under a logical inductor, the price of every sentence `φ`
converges. Proof: if not, the price oscillates across a rational gap
(`exists_rat_oscillation_of_not_convergesTo`), and that oscillation is exploitable
(`oscillation_exploitable`) by an e.c. trader — contradicting `def:lic`.

Hypotheses (both honest, both matching the rest of this file): prices lie in `[0,1]`, and each
day admits a plausible world (`hcons`; without it the market is vacuously unexploitable and
nothing constrains the price). -/
theorem lic_price_convergesTo (P : History) (DP : DeductiveProcess)
    [hLI : IsLogicalInductor P DP] (φ : Sentence)
    (hb : ∀ n, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ∃ L, ConvergesTo (fun n => P n φ) L := by
  by_contra hnc
  obtain ⟨a, b, hab, hA, hB⟩ := exists_rat_oscillation_of_not_convergesTo P φ hb hnc
  obtain ⟨Tr, hec, hexp⟩ := oscillation_exploitable P DP φ a b hab hb hcons hA hB
  exact hLI.noExploit Tr hec hexp

/-! ## M3 — Limit Coherence, bullet (3): finite additivity (`thm:lc`)

The third coherence bullet: if `⊢ ∼(φ∧ψ)` (the disjuncts are mutually exclusive) then the
limiting belief is additive, `P∞(φ∨ψ) = P∞(φ) + P∞(ψ)`. The finite-stage engine below shows the
price *gap* `Pₙ(φ∨ψ) − Pₙ(φ) − Pₙ(ψ) → 0`; with convergence (`thm:con`) this is the limit
identity. Unlike the memoryless convergence trader, the additivity trader needs **no
hysteresis**: the portfolio `σ·[(-1,φ∨ψ),(1,φ),(1,ψ)]` is *world-neutral* — by exclusivity the
`{0,1}` payouts cancel (`payout_or_of_excl`), so each day's value is the deterministic gap `σ·g`,
and a continuous buy-signal `max(0, σ·g − ε/2)` makes it a bounded-below, unbounded-above
accumulation (`exploits_of_nonneg_partialSums`). Both mispricing directions (`σ = ±1`) are one
parametrized trader. -/

/-- Reusable exploitation: a trader whose day-`i` value in every plausible world equals a fixed
nonnegative sequence `w i`, with `w n ≥ ε` frequently, exploits. -/
theorem exploits_of_nonneg_partialSums (Tr : Trader) (P : History) (DP : DeductiveProcess)
    (w : ℕ → ℝ) (ε : ℝ) (hε : 0 < ε) (hnonneg : ∀ i, 0 ≤ w i)
    (hval : ∀ (n : ℕ) (v : PCWorld), v.ConsistentWith (DP.D n) →
      Tr.netWorth P v n = ∑ i ∈ Finset.range (n+1), w i)
    (hfreq : ∃ᶠ n in atTop, ε ≤ w n)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    Tr.Exploits P DP := by
  refine ⟨⟨0, ?_⟩, ?_⟩
  · rintro x ⟨m, v, hv, rfl⟩
    rw [hval m v hv]; exact Finset.sum_nonneg (fun i _ => hnonneg i)
  · rintro ⟨B, hB⟩
    obtain ⟨g, hg_mono, hg⟩ := extraction_of_frequently_atTop hfreq
    obtain ⟨M, hM⟩ := exists_nat_gt (B / ε)
    obtain ⟨v, hv⟩ := hcons (g M)
    have hsub : (Finset.range (M+1)).image g ⊆ Finset.range (g M + 1) := by
      intro i hi; simp only [Finset.mem_image, Finset.mem_range] at hi
      obtain ⟨k, hk, rfl⟩ := hi
      exact Finset.mem_range.mpr (by have := hg_mono.monotone (Nat.lt_succ_iff.mp hk); omega)
    have hge : (M+1 : ℝ) * ε ≤ Tr.netWorth P v (g M) := by
      rw [hval (g M) v hv]
      calc (M+1:ℝ)*ε = ∑ _k ∈ Finset.range (M+1), ε := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
        _ ≤ ∑ k ∈ Finset.range (M+1), w (g k) := Finset.sum_le_sum (fun k _ => hg k)
        _ = ∑ i ∈ (Finset.range (M+1)).image g, w i :=
            (Finset.sum_image (hg_mono.injective.injOn)).symm
        _ ≤ ∑ i ∈ Finset.range (g M + 1), w i :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hnonneg i)
    have hmem : Tr.netWorth P v (g M) ∈ Tr.plausibleAssessments P DP := ⟨g M, v, hv, rfl⟩
    have hBm : B < (M+1:ℝ)*ε := by rw [div_lt_iff₀ hε] at hM; nlinarith
    exact absurd (le_trans hge (hB hmem)) (by linarith)


/-- Price gap of an exclusive pair: `P(φ∨ψ) − P(φ) − P(ψ)`, as an `EF`. -/
noncomputable def gapEF (φ ψ : Sentence) (n : ℕ) : EF :=
  .add (.price (φ ⋎ ψ) n) (.add (.mul (.const (-1)) (.price φ n)) (.mul (.const (-1)) (.price ψ n)))

/-- Continuous buy-signal for direction `σ ∈ {1,-1}`: `max(0, σ·gap − ε/2)`. -/
noncomputable def sigEF (φ ψ : Sentence) (σ ε : ℚ) (n : ℕ) : EF :=
  .max (.const 0) (.add (.mul (.const σ) (gapEF φ ψ n)) (.const (-ε/2)))

theorem gapEF_rank (φ ψ : Sentence) (n : ℕ) : (gapEF φ ψ n).rank ≤ n := by
  simp [gapEF, EF.rank]
theorem sigEF_rank (φ ψ : Sentence) (σ ε : ℚ) (n : ℕ) : (sigEF φ ψ σ ε n).rank ≤ n := by
  simp [sigEF, EF.rank, gapEF]

/-- The exclusion-arbitrage trader for direction `σ`: each day plays `sig` copies of the
world-neutral portfolio `σ·[(-1,φ∨ψ),(1,φ),(1,ψ)]`. -/
noncomputable def exclTr (φ ψ : Sentence) (σ ε : ℚ) : Trader where
  strat n := { trades := [(.mul (sigEF φ ψ σ ε n) (.const (-σ)), φ ⋎ ψ),
                          (.mul (sigEF φ ψ σ ε n) (.const σ), φ),
                          (.mul (sigEF φ ψ σ ε n) (.const σ), ψ)]
               rank_le := by
                 intro p hp
                 have hs := sigEF_rank φ ψ σ ε n
                 simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
                 rcases hp with h|h|h <;> subst h <;>
                   exact (by simpa [EF.rank] using sigEF_rank φ ψ σ ε n) }

/-- The day-`n` payoff sequence: `sig · σ · gap`, a nonnegative world-independent real. -/
noncomputable def exclW (P : History) (φ ψ : Sentence) (σ ε : ℚ) (n : ℕ) : ℝ :=
  (sigEF φ ψ σ ε n).denote P * ((σ : ℝ) * (gapEF φ ψ n).denote P)

theorem exclTr_value (φ ψ : Sentence) (σ ε : ℚ) (P : History) (v : PCWorld) (n : ℕ)
    (hv : v.Holds (∼(φ ⋏ ψ))) :
    ((exclTr φ ψ σ ε).strat n).value P v.payout = exclW P φ ψ σ ε n := by
  have hpay : v.payout (φ ⋎ ψ) = v.payout φ + v.payout ψ := PCWorld.payout_or_of_excl v φ ψ hv
  simp only [exclTr, exclW, gapEF, Strategy.value, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, EF.denote_mul, EF.denote_const, EF.denote_add, EF.denote_price,
    Pi.mul_apply, Pi.add_apply]
  rw [hpay]; push_cast; ring

/-- Denotation of the buy-signal: `max(0, σ·gap − ε/2)`. -/
theorem sigEF_denote (φ ψ : Sentence) (σ ε : ℚ) (P : History) (n : ℕ) :
    (sigEF φ ψ σ ε n).denote P = max 0 ((σ:ℝ) * (gapEF φ ψ n).denote P + (-(ε:ℝ)/2)) := by
  simp only [sigEF, EF.denote_max, EF.denote_add, EF.denote_mul, EF.denote_const,
    Pi.add_apply, Pi.mul_apply]; push_cast; ring_nf

/-- `exclW` is nonnegative (needs `ε > 0`): when the signal fires, `σ·gap ≥ ε/2 > 0`. -/
theorem exclW_nonneg (P : History) (φ ψ : Sentence) (σ ε : ℚ) (hε : 0 < ε) (n : ℕ) :
    0 ≤ exclW P φ ψ σ ε n := by
  rw [exclW, sigEF_denote]
  set G := (σ:ℝ) * (gapEF φ ψ n).denote P with hG
  by_cases h : G + (-(ε:ℝ)/2) ≤ 0
  · rw [max_eq_left h]; simp
  · push_neg at h
    have hεr : (0:ℝ) < (ε:ℝ) := by exact_mod_cast hε
    exact mul_nonneg (le_max_left _ _) (by nlinarith [h, hεr])

theorem exclTr_netWorth (φ ψ : Sentence) (σ ε : ℚ) (P : History) (DP : DeductiveProcess)
    (hexcl : ∀ n, (∼(φ ⋏ ψ)) ∈ DP.D n) (n : ℕ) (v : PCWorld) (hv : v.ConsistentWith (DP.D n)) :
    (exclTr φ ψ σ ε).netWorth P v n = ∑ i ∈ Finset.range (n+1), exclW P φ ψ σ ε i := by
  simp only [Trader.netWorth]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact exclTr_value φ ψ σ ε P v i (hv _ (hexcl n))


/-- The real price-gap equals the `gapEF` denotation. -/
theorem gapEF_denote (φ ψ : Sentence) (P : History) (n : ℕ) :
    (gapEF φ ψ n).denote P = P n (φ ⋎ ψ) - P n φ - P n ψ := by
  simp only [gapEF, EF.denote_add, EF.denote_mul, EF.denote_const, EF.denote_price,
    Pi.add_apply, Pi.mul_apply]; push_cast; ring

/-- The signal template is efficiently computable. -/
theorem sigEF_polyEF (φ ψ : Sentence) (σ ε : ℚ) : PolyEF (sigEF φ ψ σ ε) := by
  have hgap : PolyEF (gapEF φ ψ) :=
    (PolyEF.price (φ ⋎ ψ)).add
      (((PolyEF.const (-1)).mul (PolyEF.price φ)).add ((PolyEF.const (-1)).mul (PolyEF.price ψ)))
  exact (PolyEF.const 0).max (((PolyEF.const σ).mul hgap).add (PolyEF.const (-ε/2)))

/-- The exclusion-arbitrage trader is efficiently computable (three single-day templates,
assembled through the `Nat.pair`-tree list encoding). -/
theorem exclTr_ec (φ ψ : Sentence) (σ ε : ℚ) : EfficientlyComputable (exclTr φ ψ σ ε) := by
  obtain ⟨_, h1⟩ := (sigEF_polyEF φ ψ σ ε).mul (PolyEF.const (-σ))
  obtain ⟨_, h2⟩ := (sigEF_polyEF φ ψ σ ε).mul (PolyEF.const σ)
  obtain ⟨_, h3⟩ := (sigEF_polyEF φ ψ σ ε).mul (PolyEF.const σ)
  have e1 := h1.pair (PolyFueled.const (Encodable.encode (φ ⋎ ψ)))
  have e2 := h2.pair (PolyFueled.const (Encodable.encode φ))
  have e3 := h3.pair (PolyFueled.const (Encodable.encode ψ))
  have l1 := ((e1.pair ((e2.pair ((e3.pair (PolyFueled.const 0)).succ_comp)).succ_comp)).succ_comp)
  have heq : (fun n => Nat.pair (Nat.pair (EF.mul (sigEF φ ψ σ ε n) (EF.const (-σ))).toNat
      (Encodable.encode (φ ⋎ ψ)))
      (Nat.pair (Nat.pair (EF.mul (sigEF φ ψ σ ε n) (EF.const σ)).toNat (Encodable.encode φ))
        (Nat.pair (Nat.pair (EF.mul (sigEF φ ψ σ ε n) (EF.const σ)).toNat (Encodable.encode ψ))
          0 + 1) + 1) + 1)
      = (fun n => Encodable.encode ((exclTr φ ψ σ ε).strat n).trades) := by
    funext n; rfl
  rw [heq] at l1
  exact EfficientlyComputable.of_polyFueled l1

/-- Under a logical inductor with `∼(φ∧ψ)` revealed, if `σ·gap ≥ ε` frequently then the
exclusion-arbitrage trader (direction `σ`, rational threshold `ε > 0`) exploits — contradicting
`def:lic`. Its net worth is `Σ exclW`, each term nonnegative (world-neutral by exclusivity), and
`≥ ε²/2` on the frequently-underpriced days. -/
theorem exclTr_exploits (P : History) (DP : DeductiveProcess) (φ ψ : Sentence) (σ ε : ℚ)
    (hε : 0 < ε) (hexcl : ∀ n, (∼(φ ⋏ ψ)) ∈ DP.D n)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hfreq : ∃ᶠ n in atTop, (ε:ℝ) ≤ (σ:ℝ) * (gapEF φ ψ n).denote P) :
    (exclTr φ ψ σ ε).Exploits P DP := by
  have hεr : (0:ℝ) < (ε:ℝ) := by exact_mod_cast hε
  refine exploits_of_nonneg_partialSums (exclTr φ ψ σ ε) P DP (exclW P φ ψ σ ε) ((ε:ℝ)^2/2)
    (by positivity) (fun i => exclW_nonneg P φ ψ σ ε hε i)
    (exclTr_netWorth φ ψ σ ε P DP hexcl) ?_ hcons
  refine hfreq.mono (fun n hn => ?_)
  rw [exclW, sigEF_denote]
  set g := (σ:ℝ) * (gapEF φ ψ n).denote P with hgdef
  rw [max_eq_right (by linarith)]
  nlinarith [hn, hεr]

/-- **Finite additivity of the limiting belief** (`thm:lc`, bullet 3, finite-stage form): if
`∼(φ∧ψ)` is a theorem (the disjuncts are exclusive), the price gap
`Pₙ(φ∨ψ) − Pₙ(φ) − Pₙ(ψ)` converges to `0` under a logical inductor. Hence
`P∞(φ∨ψ) = P∞(φ) + P∞(ψ)` wherever the limits exist (`thm:con`). Both over- and under-pricing
are killed by the world-neutral portfolio `σ·[(-1,φ∨ψ),(1,φ),(1,ψ)]` (`σ = ±1`), whose value is
world-independent by exclusivity. -/
theorem lic_excl_gap_tendsto_zero (P : History) (DP : DeductiveProcess)
    [hLI : IsLogicalInductor P DP] (φ ψ : Sentence) (hexcl : ∀ n, (∼(φ ⋏ ψ)) ∈ DP.D n)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ConvergesTo (fun n => P n (φ ⋎ ψ) - P n φ - P n ψ) 0 := by
  refine Metric.tendsto_atTop.mpr (fun ε hε => ?_)
  obtain ⟨q, hq0, hqε⟩ := exists_rat_btwn hε
  have hq0' : 0 < q := by exact_mod_cast hq0
  -- upper: gap eventually < q
  have h1 : ∀ᶠ n in atTop, (gapEF φ ψ n).denote P < (q:ℝ) := by
    by_contra hc; rw [not_eventually] at hc; simp only [not_lt] at hc
    exact hLI.noExploit _ (exclTr_ec φ ψ 1 q)
      (exclTr_exploits P DP φ ψ 1 q hq0' hexcl hcons (by simpa using hc))
  -- lower: gap eventually > -q
  have h2 : ∀ᶠ n in atTop, -(q:ℝ) < (gapEF φ ψ n).denote P := by
    by_contra hc; rw [not_eventually] at hc; simp only [not_lt] at hc
    refine hLI.noExploit _ (exclTr_ec φ ψ (-1) q)
      (exclTr_exploits P DP φ ψ (-1) q hq0' hexcl hcons ?_)
    refine hc.mono (fun n hn => ?_)
    push_cast; nlinarith [hn]
  have hfin : ∀ᶠ n in atTop, dist (P n (φ ⋎ ψ) - P n φ - P n ψ) 0 < ε := by
    filter_upwards [h1, h2] with n hn1 hn2
    rw [Real.dist_eq, ← gapEF_denote φ ψ P n, abs_lt]
    constructor <;> linarith
  exact eventually_atTop.mp hfin

/-- **Finite additivity of the limit** (`thm:lc`, bullet 3, limit form): wherever the three
prices converge (guaranteed by `thm:con`), an exclusive disjunction's limiting price is the sum
`P∞(φ∨ψ) = P∞(φ) + P∞(ψ)`. Immediate from `lic_excl_gap_tendsto_zero` and uniqueness of limits.
Stated with the convergences as explicit hypotheses so it is unconditional (the sorry lives only
in the general `thm:con`, not here). -/
theorem lic_limit_additive (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (φ ψ : Sentence) (hexcl : ∀ n, (∼(φ ⋏ ψ)) ∈ DP.D n)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (Lφψ Lφ Lψ : ℝ) (hφψ : ConvergesTo (fun n => P n (φ ⋎ ψ)) Lφψ)
    (hφ : ConvergesTo (fun n => P n φ) Lφ) (hψ : ConvergesTo (fun n => P n ψ) Lψ) :
    Lφψ = Lφ + Lψ := by
  have hgap := lic_excl_gap_tendsto_zero P DP φ ψ hexcl hcons
  have hto : ConvergesTo (fun n => P n (φ ⋎ ψ) - P n φ - P n ψ) (Lφψ - Lφ - Lψ) :=
    (hφψ.sub hφ).sub hψ
  have := tendsto_nhds_unique hto hgap
  linarith

/-! ## `thm:provind` — sequence form (efficiently computable sentence sequence)

The fixed-`φ` limiting form (`lic_deducible_tendsto_one`) generalizes to a *sequence* `φₙ`: the
same constant buy trader, now indexed, works — the only new ingredient is certifying the
trader efficiently computable when the *sentence* varies, which needs the sequence to be an
efficiently computable sequence of sentences (`hφ`, the paper's `𝓔𝓒`-sequence), discharged via
`ec_of_polyEF_seq`. -/

/-- The trader that buys one share of `φ n` on day `n` — the constant-coefficient trader for
the **sequence** form of Provability Induction. -/
noncomputable def buySeq (φ : ℕ → Sentence) : Trader where
  strat n := { trades := [(.const 1, φ n)]
               rank_le := by intro p hp; simp only [List.mem_singleton] at hp; subst hp
                             simp [EF.rank] }

theorem buySeq_value (φ : ℕ → Sentence) (V : History) (v : PCWorld) (n : ℕ)
    (hpay : v.payout (φ n) = 1) :
    ((buySeq φ).strat n).value V v.payout = 1 - V n (φ n) := by
  simp only [buySeq, Strategy.value, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    EF.denote_const, Pi.zero_apply]
  rw [hpay]; push_cast; ring

theorem buySeq_ec (φ : ℕ → Sentence) {cφ : Nat.Partrec.Code}
    (hφ : PolyFueled cφ (fun n => Encodable.encode (φ n))) :
    EfficientlyComputable (buySeq φ) :=
  ec_of_polyEF_seq (PolyEF.const 1) hφ (fun _ => rfl)

/-- **Provability Induction, sequence form** (`thm:provind`): for an efficiently computable
sequence of sentences `φₙ`, each deducible by its own day, the price `Pₙ(φₙ) → 1`. Same
constant buy trader as the fixed case, now indexed by the sequence; e.c. via `ec_of_polyEF_seq`
and the `𝓔𝓒`-sequence hypothesis. -/
theorem lic_provind_seq (P : History) (DP : DeductiveProcess) [hLI : IsLogicalInductor P DP]
    (φ : ℕ → Sentence) {cφ : Nat.Partrec.Code}
    (hφ : PolyFueled cφ (fun n => Encodable.encode (φ n)))
    (hded : ∀ n, φ n ∈ DP.D n) (hP1 : ∀ n, P n (φ n) ≤ 1)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ConvergesTo (fun n => P n (φ n)) 1 := by
  refine Metric.tendsto_atTop.mpr (fun ε hε => ?_)
  have hev : ∀ᶠ n in atTop, 1 - ε < P n (φ n) := by
    by_contra h
    rw [not_eventually] at h; simp only [not_lt] at h
    refine hLI.noExploit (buySeq φ) (buySeq_ec φ hφ) ?_
    refine exploits_of_nonneg_partialSums (buySeq φ) P DP (fun i => 1 - P i (φ i)) ε hε
      (fun i => by have := hP1 i; linarith) ?_ ?_ hcons
    · intro n v hv
      simp only [Trader.netWorth]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hsub : DP.D i ⊆ DP.D n := Finset.le_iff_subset.mp
        (monotone_nat_of_le_succ (fun k => Finset.le_iff_subset.mpr (DP.mono k)) hi')
      have hmem : φ i ∈ DP.D n := hsub (hded i)
      exact buySeq_value φ P v i (by rw [PCWorld.payout, if_pos (hv _ hmem)])
    · exact h.mono (fun n hn => by linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, abs_lt]
  have := hP1 n; have := hN n hn; constructor <;> linarith

/-! ## `thm:lex` — learning logical equivalence

If `⊢ φ ↔ ψ` then the prices track each other: `Pₙφ − Pₙψ → 0`. Structurally this is the
additivity result with a *two*-sentence world-neutral portfolio `σ·[(1,φ),(-1,ψ)]` — by
equivalence the payouts are equal (`payout_eq_of_iff`), so the day value is the deterministic
difference `σ·(Pφ−Pψ)`, and the same buy-signal + reusable exploitation engine apply. -/

/-- If both `∼φ⋎ψ` and `∼ψ⋎φ` hold (i.e. `φ ↔ ψ`), the payouts coincide. -/
theorem PCWorld.payout_eq_of_iff (v : PCWorld) (φ ψ : Sentence)
    (h1 : v.Holds (∼φ ⋎ ψ)) (h2 : v.Holds (∼ψ ⋎ φ)) : v.payout φ = v.payout ψ := by
  rw [PCWorld.holds_or, PCWorld.holds_neg] at h1 h2
  simp only [PCWorld.payout]
  by_cases hφ : v.Holds φ <;> by_cases hψ : v.Holds ψ <;>
    simp_all [hφ, hψ]

/-- Price difference `Pₙφ − Pₙψ` as an `EF`. -/
noncomputable def gap2EF (φ ψ : Sentence) (n : ℕ) : EF :=
  .add (.price φ n) (.mul (.const (-1)) (.price ψ n))

noncomputable def sig2EF (φ ψ : Sentence) (σ ε : ℚ) (n : ℕ) : EF :=
  .max (.const 0) (.add (.mul (.const σ) (gap2EF φ ψ n)) (.const (-ε/2)))

theorem gap2EF_denote (φ ψ : Sentence) (P : History) (n : ℕ) :
    (gap2EF φ ψ n).denote P = P n φ - P n ψ := by
  simp only [gap2EF, EF.denote_add, EF.denote_mul, EF.denote_const, EF.denote_price,
    Pi.add_apply, Pi.mul_apply]; push_cast; ring

theorem sig2EF_denote (φ ψ : Sentence) (σ ε : ℚ) (P : History) (n : ℕ) :
    (sig2EF φ ψ σ ε n).denote P = max 0 ((σ:ℝ) * (gap2EF φ ψ n).denote P + (-(ε:ℝ)/2)) := by
  simp only [sig2EF, EF.denote_max, EF.denote_add, EF.denote_mul, EF.denote_const,
    Pi.add_apply, Pi.mul_apply]; push_cast; ring_nf

/-- The equivalence-arbitrage trader for direction `σ`: plays `sig` copies of
`σ·[(1,φ),(-1,ψ)]` — world-neutral when `φ ↔ ψ`. -/
noncomputable def eqTr (φ ψ : Sentence) (σ ε : ℚ) : Trader where
  strat n := { trades := [(.mul (sig2EF φ ψ σ ε n) (.const (-σ)), φ),
                          (.mul (sig2EF φ ψ σ ε n) (.const σ), ψ)]
               rank_le := by
                 intro p hp
                 have hs : (sig2EF φ ψ σ ε n).rank ≤ n := by simp [sig2EF, EF.rank, gap2EF]
                 simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
                 rcases hp with h|h <;> subst h <;>
                   exact (by simpa [EF.rank] using hs) }

noncomputable def eqW (P : History) (φ ψ : Sentence) (σ ε : ℚ) (n : ℕ) : ℝ :=
  (sig2EF φ ψ σ ε n).denote P * ((σ : ℝ) * (gap2EF φ ψ n).denote P)

theorem eqTr_value (φ ψ : Sentence) (σ ε : ℚ) (P : History) (v : PCWorld) (n : ℕ)
    (h1 : v.Holds (∼φ ⋎ ψ)) (h2 : v.Holds (∼ψ ⋎ φ)) :
    ((eqTr φ ψ σ ε).strat n).value P v.payout = eqW P φ ψ σ ε n := by
  have hpay : v.payout φ = v.payout ψ := PCWorld.payout_eq_of_iff v φ ψ h1 h2
  simp only [eqTr, eqW, gap2EF, Strategy.value, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, EF.denote_mul, EF.denote_const, EF.denote_add, EF.denote_price,
    Pi.mul_apply, Pi.add_apply]
  rw [hpay]; push_cast; ring

theorem eqW_nonneg (P : History) (φ ψ : Sentence) (σ ε : ℚ) (hε : 0 < ε) (n : ℕ) :
    0 ≤ eqW P φ ψ σ ε n := by
  rw [eqW, sig2EF_denote]
  set G := (σ:ℝ) * (gap2EF φ ψ n).denote P with hG
  by_cases h : G + (-(ε:ℝ)/2) ≤ 0
  · rw [max_eq_left h]; simp
  · push_neg at h
    have hεr : (0:ℝ) < (ε:ℝ) := by exact_mod_cast hε
    exact mul_nonneg (le_max_left _ _) (by nlinarith [h, hεr])

theorem sig2EF_polyEF (φ ψ : Sentence) (σ ε : ℚ) : PolyEF (sig2EF φ ψ σ ε) := by
  have hgap : PolyEF (gap2EF φ ψ) :=
    (PolyEF.price φ).add ((PolyEF.const (-1)).mul (PolyEF.price ψ))
  exact (PolyEF.const 0).max (((PolyEF.const σ).mul hgap).add (PolyEF.const (-ε/2)))

theorem eqTr_ec (φ ψ : Sentence) (σ ε : ℚ) : EfficientlyComputable (eqTr φ ψ σ ε) := by
  obtain ⟨_, h1⟩ := (sig2EF_polyEF φ ψ σ ε).mul (PolyEF.const (-σ))
  obtain ⟨_, h2⟩ := (sig2EF_polyEF φ ψ σ ε).mul (PolyEF.const σ)
  have e1 := h1.pair (PolyFueled.const (Encodable.encode φ))
  have e2 := h2.pair (PolyFueled.const (Encodable.encode ψ))
  have l1 := ((e1.pair ((e2.pair (PolyFueled.const 0)).succ_comp)).succ_comp)
  have heq : (fun n => Nat.pair (Nat.pair (EF.mul (sig2EF φ ψ σ ε n) (EF.const (-σ))).toNat
      (Encodable.encode φ))
      (Nat.pair (Nat.pair (EF.mul (sig2EF φ ψ σ ε n) (EF.const σ)).toNat (Encodable.encode ψ))
        0 + 1) + 1)
      = (fun n => Encodable.encode ((eqTr φ ψ σ ε).strat n).trades) := by funext n; rfl
  rw [heq] at l1
  exact EfficientlyComputable.of_polyFueled l1

theorem eqTr_exploits (P : History) (DP : DeductiveProcess) (φ ψ : Sentence) (σ ε : ℚ)
    (hε : 0 < ε) (himp1 : ∀ n, (∼φ ⋎ ψ) ∈ DP.D n) (himp2 : ∀ n, (∼ψ ⋎ φ) ∈ DP.D n)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hfreq : ∃ᶠ n in atTop, (ε:ℝ) ≤ (σ:ℝ) * (gap2EF φ ψ n).denote P) :
    (eqTr φ ψ σ ε).Exploits P DP := by
  have hεr : (0:ℝ) < (ε:ℝ) := by exact_mod_cast hε
  refine exploits_of_nonneg_partialSums (eqTr φ ψ σ ε) P DP (eqW P φ ψ σ ε) ((ε:ℝ)^2/2)
    (by positivity) (fun i => eqW_nonneg P φ ψ σ ε hε i) ?_ ?_ hcons
  · intro n v hv
    simp only [Trader.netWorth]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact eqTr_value φ ψ σ ε P v i (hv _ (himp1 n)) (hv _ (himp2 n))
  · refine hfreq.mono (fun n hn => ?_)
    rw [eqW, sig2EF_denote]
    set g := (σ:ℝ) * (gap2EF φ ψ n).denote P with hgdef
    rw [max_eq_right (by linarith)]
    nlinarith [hn, hεr]

/-- **Learning of logical equivalence** (`thm:lex`, finite-stage form): if `⊢ φ ↔ ψ` (both
implications revealed by the deductive process), the price difference `Pₙφ − Pₙψ → 0` under a
logical inductor. World-neutral 2-sentence portfolio (payouts equal by equivalence). -/
theorem lic_lex_tendsto_zero (P : History) (DP : DeductiveProcess)
    [hLI : IsLogicalInductor P DP] (φ ψ : Sentence) (himp1 : ∀ n, (∼φ ⋎ ψ) ∈ DP.D n)
    (himp2 : ∀ n, (∼ψ ⋎ φ) ∈ DP.D n) (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ConvergesTo (fun n => P n φ - P n ψ) 0 := by
  refine Metric.tendsto_atTop.mpr (fun ε hε => ?_)
  obtain ⟨q, hq0, hqε⟩ := exists_rat_btwn hε
  have hq0' : 0 < q := by exact_mod_cast hq0
  have h1 : ∀ᶠ n in atTop, (gap2EF φ ψ n).denote P < (q:ℝ) := by
    by_contra hc; rw [not_eventually] at hc; simp only [not_lt] at hc
    exact hLI.noExploit _ (eqTr_ec φ ψ 1 q)
      (eqTr_exploits P DP φ ψ 1 q hq0' himp1 himp2 hcons (by simpa using hc))
  have h2 : ∀ᶠ n in atTop, -(q:ℝ) < (gap2EF φ ψ n).denote P := by
    by_contra hc; rw [not_eventually] at hc; simp only [not_lt] at hc
    refine hLI.noExploit _ (eqTr_ec φ ψ (-1) q)
      (eqTr_exploits P DP φ ψ (-1) q hq0' himp1 himp2 hcons ?_)
    refine hc.mono (fun n hn => ?_); push_cast; nlinarith [hn]
  have hfin : ∀ᶠ n in atTop, dist (P n φ - P n ψ) 0 < ε := by
    filter_upwards [h1, h2] with n hn1 hn2
    rw [Real.dist_eq, ← gap2EF_denote φ ψ P n, abs_lt]; constructor <;> linarith
  exact eventually_atTop.mp hfin

end LogicalInduction
