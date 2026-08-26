# Logical Induction — paper errata

Defects in arXiv:1609.03543v5 itself, as opposed to discrepancies introduced by this
formalization. Line references are into the committed source `1609.03543v5-main.tex`.
Each entry states the published claim, the defect, and what this repository does instead.

| | node | severity |
| --- | --- | --- |
| PE1 | `thm:ifp` — Closure under Finite Perturbations | **the theorem is false** |
| PE2 | `thm:recurringunbiasednessexp` / `thm:wubexp` | swapped hypothesis (transcription) |
| PE3 | `app:prandaff` — decidability of `Settled(n,m)` | claim false as written; repairable |
| PE4 | `app:prandaff` — patience argument | unstated monotonicity assumption |
| PE5 | `def:seqprand` vs. `thm:prand` | sign inconsistency |

---

## PE1 — Closure under Finite Perturbations (`thm:ifp`)

### Published statement

> Let `⟨p⟩` and `⟨p'⟩` be markets with `pₙ = p'ₙ` for all but finitely many `n`. Then
> `⟨p⟩` is a logical inductor if and only if `⟨p'⟩` is a logical inductor.

(`1609.03543v5-main.tex:1521–1524`, proved in `app:ifp`.) A pricing is *any* computable
rational valuation and a market *any* computable sequence of pricings
(`def:pricing`/`def:marketprocess`, tex:676–682) — no finite support, no runtime bound, no
bound on the size of the returned rational. §4 quantifies over arbitrary markets
deliberately, noting that the constructed `LIA` has finite support per day but that the
results are stated in the general case (tex:993–997).

### Defect

**The theorem is false**, and its published proof is separately invalid.

The proof (tex:6047–6062) transports an exploiting trader by rewriting every early price
leaf `φ^{*i}`, `i < N`, into the constant `pᵢ(φ)`, and justifies the rewrite's efficiency
thus: "only finitely many constants `pᵢ(φ)` are needed, and can be hard-coded into `F`."
There are finitely many early *days* `i`, but `φ` ranges over all sentences, and a day-`n`
strategy may name new sentences in old-day leaves as `n` grows. So the constant set is
infinite, `F` must *compute* `pᵢ(φ)` rather than table it, and `def:marketprocess` bounds
neither the runtime of that computation nor the size of its rational output. Hard-coding
the finitely many *programs* does not help: running one on a varying sentence can take
superpolynomial time and return a rational needing superpolynomially many symbols to
print.

That is a gap in the proof. The theorem itself fails for the same underlying reason, one
step further out.

### Formal refutation

`FinitePerturbationCounterexample.not_overgeneral_ifp`
(`Construction/Witnesses/FinitePerturbationWitness.lean`) proves the negation of the
printed statement, at the paper's own quantifier (`IsMachineLogicalInductor`,
`MachineEfficientTrader`), with no theory parameter and no unproved hypothesis. It is
kernel-checked and axiom-clean; `not_overgeneral_ifp_ofTheory` is the same result over any
Σ₁-sound Δ₁ theory extending `𝗜𝚺₁`. The abstract reduction it rests on,
`not_overgeneral_ifp_of_advice`, lives in `Properties/FinitePerturbationCounterexample.lean`.

Neither declaration carries a `Paper node:` line: they refute a paper statement rather
than render one.

### Counterexample mechanism

A single changed pricing day is an infinite computable function, and `def:marketprocess`
puts no bound on its runtime or output size. That is enough for one day to act as
persistent historical advice, handing an efficient trader information it could not compute
for itself. The gap between *computable* and *efficiently computable* is exactly what the
perturbation smuggles across.

Made precise:

* `P` is the constructed `LIA` over the `𝗜𝚺₁` theorem process — a genuine machine logical
  inductor (`LIA_isMachineLogicalInductor`).
* `χ` is the repository's diagonal price family: in every world consistent with the
  completed theory, `χ n` holds exactly when `P n (χ n) < 1/2`. A trader knowing that one
  bit earns a *certain* `≥ 1/2` on day `n` once the day has settled — buy below the
  threshold, where the sentence is true; short at or above it, where it is false.
  Computing the bit is computable but not polynomial-time, which is why `P` itself
  survives.
* `P'` changes **day `0` only**, publishing the sign and schedule bits as the prices of
  advice atoms at otherwise unused tags. It is a legal `ComputableMarket`: the day-`0` row
  is a total computable search, terminating by propositional compactness
  (`DeductiveProcess.exists_stage_entails`).
* The exploiting trader is a genuine `MachineEfficientTrader`, and never computes the
  bits. Its day-`n` coefficient is the rank-`0` feature
  `price (schedAtom n) 0 * (2 * price (signAtom n) 0 - 1)`, so the *market* supplies the
  advice at valuation time. A sparse schedule lets each round settle before the next
  opens, bounding downside by `1` while settled rounds accumulate `≥ 1/2` each.

So `P` satisfies the criterion, `P'` agrees with it from day `1` on and is computable, and
`P'` is exploited. No repair of the appendix's transport argument can close this: the
theorem, not merely its proof, is wrong.

### Corrected replacement

Finite *support* is what rescues the hard-coding step, and the repository proves that
case.

`FreezeOracle.machine_lic_iff_of_recognizableSupport`
(`Construction/Witnesses/FreezeOracle.lean`) is the statement to cite:

```lean
theorem machine_lic_iff_of_recognizableSupport (P P' : History) (DP : DeductiveProcess)
    (hPcomp : ComputableMarket P) (hP'comp : ComputableMarket P')
    (hpert : RecognizableSupportPerturbation P P') :
    IsMachineLogicalInductor P DP ↔ IsMachineLogicalInductor P' DP
```

`RecognizableSupportPerturbation P P'` asks for a finite set `S` of `(day, sentence)`
coordinates off which the two markets agree, every sentence in it `Recognizable`. There is
no certificate hypothesis: the freeze certificate each market needs is *compiled* from its
own computability certificate by
`FreezeOracle.machineFiniteSupportPatch_ofRecognizable`.

Two things about that statement, both stated at the declaration:

1. **Its hypothesis is strictly stronger than the paper's.** Finite support implies tail
   agreement (`FiniteSupportPerturbation.tail_agree`); the converse fails — a day-`0`
   market pricing the sentence of code `n` at `1 − 1/2^(2^n)` agrees with `LIA` from day
   `1` and is not finitely supported. This is a *corrected* theorem, a proper restriction
   of `thm:ifp`, not a restatement of it.
2. **The one residual hypothesis is representation, not mathematics.** `Recognizable ψ` —
   `BotFree ψ` and `NoReserved ψ` — constrains the *syntax* of the finitely many sentences
   whose price moves, and constrains no market, trader, or perturbation. Each half stands
   for one `Complexity.FP` primitive this toolkit lacks: `BotFree` for **integer square
   root** (Foundation's `Formula.ofNat` discards the payload at tag `0`, so `⊥` has
   infinitely many escape codes and deciding whether a code denotes `⊥` is deciding
   whether it is a perfect square — polynomial time mathematically), and `NoReserved` for
   a **structured-payload parser**. Neither half has slack: every position in a term is
   escape-able, so `BotFree` must be hereditary, and a structured spelling at any subterm
   breaks completeness. `decode_and_noncanonical` proves the first restriction *necessary*
   rather than an artifact. So the unrestricted finite-*support* statement is, as far as
   this development can tell, true, and unprovable here for want of two primitives rather
   than for want of a theorem.

The underlying general form, taking a freeze certificate per market, is
`machine_lic_iff_of_finiteSupportPerturbation` (`Properties/FinitePerturbations.lean`).

### Downstream consequence

* **Non-vacuous.** `FreezeOracle.machine_lic_iff_twoPoint` is the corrected theorem at a
  concrete pair of computable markets with real `Nat.Partrec.Code` tables, proved to
  differ at the frozen coordinate, discharging every hypothesis at once.
* **Informative.** Those particular markets price everything at zero but one coordinate
  and are very likely exploitable, so the equivalence might hold there because both sides
  fail. `LIAPerturbation.machineLogicalInductor_liaPerturbed` removes that qualification:
  `liaHistory DP` is a machine logical inductor, and moving one price at the
  `Recognizable` coordinate `(0, atom 0)` — a genuinely nonzero change,
  `liaPerturbed_ne` — yields a market that still is, **by this theorem and nothing else**.
  That market is the output of no construction here. The instance inherits
  `Construction/LIA.lean`'s own two hypotheses (LIA's market program, a computable
  deductive process), which are pre-existing and unchanged.
* **The fuel-class certificates remain uninhabited.** `EfficientPrefixPatch` and
  `FiniteSupportPatch` have no inhabitant anywhere: the fuel calculus does not close over
  the escape-leaf decode the frozen lookup needs (`dd:fuel`; see
  `Construction/Witnesses/RpnFreeze.lean`). Only the machine-class certificate is
  discharged. `lic_iff_of_finitePerturbation` and `lic_iff_of_finiteSupportPerturbation`
  therefore still carry certificate hypotheses with no exhibited witness.
* **The degenerate discharge is available and deliberately not taken.** `S = ∅` makes the
  freeze the identity and inhabits any certificate, at the cost of forcing `P = P'`.
  Recorded here so nobody later mistakes it for a discharge.

Verdict wording for downstream documentation:

> The published unrestricted finite-perturbation theorem is false, and the repository
> proves it false; its published proof is separately invalid. The repository proves a
> corrected finite-*support* theorem — the restricted case in which the published proof's
> own justification is sound — at the paper's own quantifier, with no certificate
> hypothesis and one residual syntactic side condition. The fuel-class readings of the
> same theorem still have no inhabited certificate.

---

## PE2 — Swapped good-feedback hypothesis in the expectation unbiasedness pair (`thm:recurringunbiasednessexp`, `thm:wubexp`)

**Confirmed statement-level erratum in v5; not a soundness defect.** Worth forwarding to
the authors.

### Published statement and defect

The two expectation-level unbiasedness theorems in §4.8 attach the good-feedback
hypothesis to the wrong member of the pair, mirroring the correctly-stated affine pair
(`thm:recunbiasedaff` / `thm:wubaff`) incorrectly.

* **Expectation Recurring Unbiasedness** (tex:1812–1820, `thm:recurringunbiasednessexp`)
  states its weighting as "a generable divergent weighting **weighting** such that the
  support of `w` is contained in the image of `f`." That clause is spurious: it references
  a deferral function `f` the statement never introduces, and its correctly-stated affine
  analogue `thm:recunbiasedaff` (tex:1469–1478) has no such clause. The doubled word is a
  second typo in the same line.
* **Expectation Unbiasedness From Feedback** (tex:1822–1832, `thm:wubexp`) states only "a
  generable divergent weighting" and *lacks* the support-in-image clause — even though its
  affine analogue `thm:wubaff` (tex:1480–1490) carries it. Its timely-computability clause
  also writes `thmval(affₙ)` where the theorem's sequence is `affluv`.

So the clause belongs on the feedback theorem and is absent there, while appearing
spuriously on the recurring theorem.

### Why it is transcription, not mathematics

The appendix proofs use the intended hypotheses: Expectation Recurring Unbiasedness
reduces to the clause-free affine 4.5.9, Expectation Unbiasedness From Feedback to the
clause-bearing affine 4.5.10. The theorems are true as intended; only the printed §4.8
statements (restated verbatim at v5 pp. 112–113) are garbled. Correct statements: 4.8.15
with a bare generable divergent weighting concluding a limit point at `0`; 4.8.16 with the
deferral function, timely value computability and support ⊆ image of `f`, concluding
`≈ₙ 0`.

### Repository status

The formalization places the hypotheses correctly and does not inherit the bug.
`recurringunbiasednessexp` (`Construction/Witnesses/HistoricalMaturity.lean`) takes a
generable divergent weighting with no deferral or image-of-`f` hypothesis and concludes a
limit point; the pseudorandom/feedback capstones (`prandaff` and the `wubexp` route) carry
the deferral function, `PatientSettlementClock` and pseudorandomness data and conclude a
full limit. This is forced by construction: the full-limit conclusion is not provable
without the deferral clause, and the limit-point conclusion does not need it.

---

## PE3 — `Settled(n,m)` decidability as written (`app:prandaff`)

**Repaired in-repo; the paper's assertion is fixable but not literally true as stated.**

tex:4865 asserts that `Settled(n,m)` — "all worlds in `pcworlds(D_m)` value the
combination `Aₙ` at `thmval(Aₙ)`" — is decidable. As written the predicate mentions
`thmval(Aₙ)`, which is not computable, so the literal test is not one a machine can run.

The repair, which the paper's proof clearly intends: under consistency of the theory,
settlement is equivalent to inter-world *agreement* on the finitely many relevant truth
assignments, a finite decidable test given exact rational market quotes. Formalized as
`AffineCombination.DeterminedViaTheory.settled_iff_agree` (`Properties/Calibration.lean`),
with the rational-quote requirement supplied by `IsLogicalInductor.marketComputable`.

---

## PE4 — Patience argument assumes a monotone deferral function (`app:prandaff`)

**Repaired in-repo by a strengthened trader.**

tex:4923 argues the constructed weighting is `f`-patient via
`Σ_{n≤m} [f(n) ≥ m] αₙ ≤ 1`, which implicitly assumes the deferral function is monotone;
`def:deferralfunc` (tex:1240) requires only `f(n) > n`. For non-monotone `f` the bracket
can admit unboundedly many terms between `m` and `f`-images from far below.

The repository's trader replaces the bracket with the envelope `max_{k≤i} f k`
(`deferralEnvelope`, `Properties/Pseudorandomness.lean`), which restores the bound for
arbitrary deferral functions. Justified in the docstring at the definition site.

---

## PE5 — Sign inconsistency in `def:seqprand` vs. `thm:prand`'s one-sided forms

**Repaired in-repo by orienting the definition to its advertised conclusion; disclosed at
the definition site.** Minor, and plausibly a transcription slip.

`def:seqprand` (tex:1305–1311) displays the weighted average of `(pᵢ − ThmInd(φᵢ))` and
says the `≈ₙ` may be replaced by `≳ₙ` to give "varied pseudorandom **above** ⟨p⟩".
`thm:prand` (tex:1314–1320) then pairs that notion with the conclusion `Pₙ(φₙ) ≳ₙ pₙ`.
With the paper's centering those two `≳ₙ`s point in opposite directions: bounding
`avg(p − ThmInd)` *below* says the truth frequency undershoots `p`, which forces the price
*down*, not up.

The repository centers the other way —
`VariedPseudorandomAbove truth p := PseudorandomAbove (truth − p)`
(`Properties/Pseudorandomness.lean`) — which is the orientation the exploiting-trader
argument needs and which makes the paper's advertised conclusion come out right. Disclosed
in that definition's docstring.
