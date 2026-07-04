/-
# Integration test — discharging deference-corpus hypotheses (roadmap M3)

The downstream consumers (`deference-in-logical-induction`, `dose-response`) prove the
deference/dose-response *algebra* but take every Logical-Induction fact as a **named
hypothesis** over abstract `ℕ → ℝ` sequences, in their own `DeferenceAsymp` vocabulary
(`Approx` / `AsympLE`). This file is the roadmap's M3 integration test: *does our work
actually plug into that back end?* We check it two ways.

**Part A — vocabulary drop-in.** `DeferenceAsymp.Approx`/`AsympLE` are *definitionally* our
`Asymptotics.AsympEq`/`AsympLE` (`Tendsto (·−·) atTop (𝓝 0)` and the `ε`-form). We reproduce
a real deference theorem — `value_argmax_asymptotic` from `LeanDeference.lean` — verbatim in
*our* vocabulary and prove it with *our* combinators. It compiles, so `LogicalInduction.
Asymptotics` is a genuine drop-in for `DeferenceAsymp`. (Writing this test is what surfaced
the three combinators just added to `Asymptotics`: `AsympLE.trans`, `AsympLE.trans_asympEq`,
`AsympEq.finsetSum` — the corpus's `AsympLE.trans` / `trans_approx` / `approx_sum`.)

**Part B — LI-content discharge, at the level we have reached.** The corpus's hypotheses are
mostly *expectation*-level (`thm:cee/ceu/ccee/loe/expprovind` over `E^H_n`), which sits above
a LUV bridge we have not built yet. But a Provability-Induction / Convergence hypothesis is
*price*-level, and we have it: `lic_deducible_tendsto_one` discharges a hypothesis of the
exact shape `Approx (fun n => P n φ) (fun _ => 1)`. Part B wires that end to end.

**What this test establishes, and what it does not.** It establishes that the asymptotic
interface matches exactly and that a price-level LI theorem of ours discharges a
provind-shaped hypothesis with no adapter. It does *not* reach the expectation-level
hypotheses the corpus mostly runs on — that needs the LUV/expectation layer (Engine, M3/M4).
See the milestone notes.
-/
import LogicalInduction.Properties
import LogicalInduction.Expectations

namespace LogicalInduction.IntegrationTest

open LogicalInduction Filter Topology

/-! ## Part A — the deference asymptotics module is our `Asymptotics`

`DeferenceAsymp.Approx a b := Tendsto (fun n => a n - b n) atTop (𝓝 0)` is our `AsympEq`;
`DeferenceAsymp.AsympLE a b := ∀ ε>0, ∀ᶠ n, a n ≤ b n + ε` is our `AsympLE`. These `example`s
witness the definitional match, so their `≂ₙ`/`≲` are our `≈ₙ`/`≲ₙ`. -/

example (a b : ℕ → ℝ) : (a ≈ₙ b) = Tendsto (fun n => a n - b n) atTop (𝓝 0) := rfl
example (a b : ℕ → ℝ) : (a ≲ₙ b) = (∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, a n ≤ b n + ε) := rfl

/-- **Reproduction of `DeferenceArgmax.value_argmax_asymptotic`** (from the deference
corpus's `LeanDeference.lean`), stated in *our* vocabulary and proved with *our* combinators.
Its named hypotheses are the LI theorems `thm:cee` (`hUM_S`, `hCee`) and `thm:expprovind`
(`hMon`); the conclusion is *Value*. That this typechecks against `LogicalInduction.
Asymptotics` is the interface check: our module supplies exactly the algebra the deference
proof runs on. -/
theorem value_argmax_asymptotic
    (ES Em Emi Eoi : ℕ → ℝ)
    (hUM_S : ES ≈ₙ Em)          -- thm:cee on the selected LUV Ŝ
    (hMon : Emi ≲ₙ Em)          -- thm:expprovind, from M ≥ mᵢ
    (hCee : Eoi ≈ₙ Emi) :       -- thm:cee on Oⁱ
    Eoi ≲ₙ ES :=
  ((hCee.asympLE).trans hMon).trans_asympEq hUM_S.symm

/-! ## Part B — discharging a Provability-Induction hypothesis for real

A downstream theorem that consumes `thm:provind` for a fixed deducible sentence would take a
hypothesis of the form `Approx (fun n => P n φ) (fun _ => 1)` — "the price of `φ` converges to
1". We model such a consumer and discharge its hypothesis from a *logical inductor*, with no
adapter: our `lic_deducible_tendsto_one` produces exactly that `AsympEq`. -/

/-- The shape of the LI fact a provind-consuming deference theorem names. -/
def ProvindHypothesis (P : History) (φ : Sentence) : Prop :=
  (fun n => P n φ) ≈ₙ (fun _ => 1)

/-- Our convergence theorem produces the named hypothesis exactly (`ConvergesTo … 1` is
`≈ₙ` against the constant `1`, by `convergesTo_iff_asympEq_const`). -/
theorem provind_hypothesis_discharged (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (φ : Sentence) (hded : ∀ n, φ ∈ DP.D n)
    (hP1 : ∀ n, P n φ ≤ 1) (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ProvindHypothesis P φ :=
  convergesTo_iff_asympEq_const.mp (lic_deducible_tendsto_one P DP φ hded hP1 hcons)

/-- End-to-end wiring: a deference-style consumer that, *given* the provind hypothesis, draws
a conclusion (here the trivial `≲ₙ`-reflexivity stand-in for whatever it actually derives) —
composed with the discharge above, so under `[IsLogicalInductor P DP]` the consumer's LI
hypothesis is supplied entirely from our side. -/
example (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP] (φ : Sentence)
    (hded : ∀ n, φ ∈ DP.D n) (hP1 : ∀ n, P n φ ≤ 1)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (consumer : ProvindHypothesis P φ → (fun n => P n φ) ≲ₙ (fun _ => 1)) :
    (fun n => P n φ) ≲ₙ (fun _ => (1 : ℝ)) :=
  consumer (provind_hypothesis_discharged P DP φ hded hP1 hcons)

/-! ## Part C — closing the level gap: expectation-level interface

The corpus's *main* hypotheses are over expectations `E^H_n(X)`, which it treats as abstract
`ℕ → ℝ`. With the LUV bridge (`Expectations.lean`) those are now **concrete**: `E^H_n(X)` is
`X.expectSeq P`, a real sum of `P`'s prices on `X`'s threshold sentences. So the corpus's
`ES, Em, …` are literally `X.expectSeq P` for concrete LUVs, and its expectation hypotheses
`Approx (E_now X) (E_now Y)` are `X.expectSeq P ≈ₙ Y.expectSeq P` here — the *same* type. -/

/-- The corpus's `E_now(X) : ℕ → ℝ` slot is inhabited by our concrete expectation sequence. -/
noncomputable example (P : History) (X : LUV) : ℕ → ℝ := X.expectSeq P

/-- A `thm:cee`-shaped expectation hypothesis, in our concrete objects. -/
example (P : History) (X Y : LUV) : Prop := X.expectSeq P ≈ₙ Y.expectSeq P

/-- **The deference `Value` theorem, applied to our concrete expectations.** Every abstract
`E_now(·)` slot in `value_argmax_asymptotic` is instantiated by `expectSeq P` of a concrete
LUV. The LI hypotheses (`thm:cee`/`thm:expprovind`) are still assumed here — proving them is
the property-tail work `Expectations.lean` states — but the *interface is closed*: the
corpus's expectation sequences are our objects, with no adapter and no type mismatch. -/
example (P : History) (Ŝ M mi Oi : LUV)
    (hUM_S : Ŝ.expectSeq P ≈ₙ M.expectSeq P)      -- thm:cee on the selected LUV
    (hMon  : mi.expectSeq P ≲ₙ M.expectSeq P)     -- thm:expprovind
    (hCee  : Oi.expectSeq P ≈ₙ mi.expectSeq P) :  -- thm:cee on Oⁱ
    Oi.expectSeq P ≲ₙ Ŝ.expectSeq P :=
  value_argmax_asymptotic _ _ _ _ hUM_S hMon hCee

end LogicalInduction.IntegrationTest
