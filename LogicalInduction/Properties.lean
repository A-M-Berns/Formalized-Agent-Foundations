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

end LogicalInduction
