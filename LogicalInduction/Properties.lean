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
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace LogicalInduction

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

end LogicalInduction
