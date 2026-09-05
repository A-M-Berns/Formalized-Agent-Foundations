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
| PE6 | `thm:ref` / `app:ref` — Introspection | printed hypotheses too weak for the printed proof |
| PE7 | `Con(PA)(Ack)` gloss (tex:1859) | gloss contradicts its definition (off by one) |
| PE8 | `app:incons` — proof of `thm:incons` | proof cites representability where Σ₁-completeness is needed |

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

Both closed forms carry `Paper node: \`thm:ifp\``. A refutation belongs to the node it
refutes: the label records that the declaration is part of this formalization's account of
that node, not that it repeats the printed statement. `not_overgeneral_ifp` is a canonical
trust-surface endpoint and is audited exactly like any other.

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

`FreezeOracle.machine_lic_iff_of_finiteSupport`
(`Construction/Witnesses/FreezeOracle.lean`) is the statement to cite:

```lean
theorem machine_lic_iff_of_finiteSupport (P P' : History) (DP : DeductiveProcess)
    (hPcomp : ComputableMarket P) (hP'comp : ComputableMarket P')
    (hpert : FiniteSupportPerturbation P P') :
    IsMachineLogicalInductor P DP ↔ IsMachineLogicalInductor P' DP
```

`FiniteSupportPerturbation P P'` asks for a finite set `S` of `(day, sentence)` coordinates
off which the two markets agree, and asks nothing else — nothing about the sentences in it.
There is no certificate hypothesis either: the freeze certificate each market needs is
*compiled* from its own computability certificate by
`FreezeOracle.machineFiniteSupportPatch`. The earlier
`machine_lic_iff_of_noReservedSupport` and `machine_lic_iff_of_recognizableSupport` survive
as one-line compatibility corollaries.

Two things about that statement, both stated at the declaration:

1. **Its hypothesis is strictly stronger than the paper's.** Finite support implies tail
   agreement (`FiniteSupportPerturbation.tail_agree`); the converse fails, and that is now
   also proved rather than argued — `tailAgree_not_finiteSupport` exhibits two markets
   agreeing from day one that differ at infinitely many coordinates, because a day's fibre
   is infinite. So

   ```
   finite coordinate support  ⇒  eventual day agreement
   eventual day agreement     ⇏  finite coordinate support
   ```

   and the corrected theorem cannot re-derive the refuted one. This is a *corrected*
   theorem, a proper restriction of `thm:ifp`, not a restatement of it. The counterexample
   above is exactly on the wrong side of that line: it moves one whole pricing row, hence
   infinitely many coordinates.
2. **No residual hypothesis on the moved sentences remains.** There used to be two, both
   constraining the *syntax* of the finitely many sentences whose price moves rather than
   any market, trader, or perturbation. Each stood for a missing `Complexity.FP` device, and
   each was retired by building the device — never by weakening or renaming the condition.

   `BotFree` is **gone**, and the way it went is worth recording. It stood for **integer
   square root**: Foundation's `Formula.ofNat` discards the payload at tag `0`, so `⊥` has
   infinitely many escape codes (`decode_falsum_noncanonical`, `decode_and_noncanonical`),
   and deciding whether a code denotes `⊥` is deciding whether it is a perfect square. That
   primitive is now built — `DigitFP.sqrtRemW_mem_FP` and `DigitFP.unpairW_spec` supply
   base-4 integer square root and `Nat.unpair` inside `Complexity.FP`,
   `FiberTest.fiberW_mem_FP` the escape-leaf decode test on top of them — and the recognizer
   was rebuilt around it: `RpnFreeze.patterns` replaces the finite spelling list by a finite
   list of *patterns with holes*, confining the infinite fibre inside a hole predicate, and
   `PatAuto.ifParse_mem_FP` decides the whole thing in polynomial time.
   `FreezeOracle.machine_lic_iff_hardPoint` exercises the difference at `atom 0 ⋏ ⊥`, a
   sentence the previous endpoint provably could not freeze
   (`FreezeOracle.not_recognizable_hardS`).

   `NoReserved` is **gone** too, and it stood for a **structured-payload recognizer** —
   which turned out to be two problems rather than one. A structured leaf is spelled
   `[1, 0, pol] ++ 1^L ++ [0] ++ p ++ [19]` with `L = |p|`.

   The first problem is the length identification. `L` is unbounded even for a fixed target,
   because `parseStructuredNat` has a self-loop at the numeral `0` (`1^k 0` spells `0` for
   every `k`), so matching the unary field against the payload's own length is `aⁿbⁿ` and no
   finite-state device decides it — no extension of a spelling list could have closed this.
   `CtrAuto.ctrMachine` does: `RunAuto.BlockMachine` instantiated as a finite control paired
   with one unary counter, whose state grows a mark per token and stays inside
   `Complexity.FP`.

   The second problem is larger and was not anticipated when `NoReserved` was first
   disclosed: recognizing *which* payload token strings denote the fixed formula code, given
   that numeral padding and the double negation `[20, 20]` both preserve a code, so the set
   is infinite and not a spelling list either. `PayAuto` decides it exactly, by top-down
   predictive parsing against a stack of obligations that carries the pending negation as a
   *parity bit* instead of applying `negFormulaCode`. That keeps every child code an
   `unpair` component of its parent, so a potential argument bounds the reachable stacks and
   the state set is finite. The parity step is sound because `negFormulaCode` is an
   involution **on the parser's range** — it is not one on `ℕ`, where tags 2/3 discard their
   payload; `PayAuto.WFCode` carries the difference.

   `StructPat.parseRpn_iff_segMatch` is the characterization the two devices are hung on: a
   run denotes `ψ` under the full grammar exactly when it matches one of `ψ`'s finitely many
   *segment* patterns, structured blocks included, for every `ψ`.
   `FreezeOracle.machine_lic_iff_reservedPoint` exercises the difference at a reserved atom,
   a coordinate neither earlier endpoint could freeze
   (`FreezeOracle.not_noReserved_pointS_reserved`).

   What is disclosed in their place is a property of the *construction*, not of the
   statement: the recognizer is compiled per frozen sentence, so its polynomial-time
   constants depend on that sentence. That is the paper's own "finitely many constants can
   be hard-coded", and it is sound precisely because the support is finite — which is
   exactly where the printed finite-*days* proof fails and this one does not.

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

A second, independent confirmation of the intended placement: the *plain* affine
recurring-unbiasedness theorem (`thm:recurringunbiasedness`, tex:1225–1233) carries no
support clause and introduces no deferral function at all, exactly parallel to how the
expectation recurring theorem should read.

The formalization places the hypotheses correctly and declares the correction at the
statements. `BoundedSequence.recurringunbiasednessexp`
(`Construction/Witnesses/HistoricalMaturity.lean`) takes a generable divergent weighting
with no deferral or image-of-`f` hypothesis and concludes a limit point;
`luv_wubexp_ofComputation` and `luv_wubexp_ofComputation_unconditional`
(`Construction/Witnesses/FeedbackTruth.lean`, `FeedbackUnconditional.lean`) carry the
deferral function and the support-in-image hypothesis and conclude a full limit. This is
forced by construction: the full-limit conclusion is not provable without the deferral
clause, and the limit-point conclusion does not need it.

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

A concrete counterexample to the printed pairing: take every `φᵢ` Θ-refutable and e.c.,
`pᵢ = 1/2`, and `f(n) = n+1`, so the constant weighting is `f`-patient and divergent. Then
`avg(p − ThmInd) = 1/2 ≳ₙ 0` and the family is "varied pseudorandom above ⟨p⟩" as printed
— yet provability induction forces `Pₙ(φₙ) ≈ₙ 0`, contradicting the advertised
`Pₙ(φₙ) ≳ₙ 1/2`.

The repository centers the other way —
`VariedPseudorandomAbove truth p := PseudorandomAbove (truth − p)`
(`Properties/Pseudorandomness.lean`) — which is the orientation the exploiting-trader
argument needs and which makes the paper's advertised conclusion come out right. Disclosed
in that definition's docstring.

---

## PE6 — Introspection's printed hypotheses do not license its printed proof (`thm:ref`, `app:ref`)

**The theorem is not false.** Its printed hypotheses are insufficient to run its own printed
proof. That is a different defect from PE1 and should not be read as the same one.

### Published statement

> Let `⟨φ⟩` be an e.c. sequence of sentences, and `⟨a⟩`, `⟨b⟩` be **ℙ-generable** sequences
> of probabilities. Then, for any e.c. sequence of positive rationals `⟨δ⟩ → 0`, there
> exists a sequence of positive rationals `⟨ε⟩ → 0` such that for all `n`: (1) if
> `ℙₙ(φₙ) ∈ (aₙ+δₙ, bₙ−δₙ)` then `ℙₙ(⌜⌜aₙ⌝ < ⌜ℙ⌝_⌜n⌝(⌜φₙ⌝) < ⌜bₙ⌝⌝) > 1−εₙ`; (2) if
> `ℙₙ(φₙ) ∉ (aₙ−δₙ, bₙ+δₙ)` then that same price is `< εₙ`.

(`1609.03543v5-main.tex:1969–1981`, proved in `app:ref`, tex:5310.) Note that `⟨φ⟩` and
`⟨δ⟩` are required **e.c.**, while `⟨a⟩` and `⟨b⟩` are required only ℙ-generable.

### Defect

`app:ref` sets `ψₙ := ⌜⌜aₙ⌝ < ⌜ℙ⌝_⌜n⌝(⌜φₙ⌝) < ⌜bₙ⌝⌝` and applies `thm:affprovind` to the
combination `ctsind_{δₙ}(aₙ < ℙₙ(φₙ) < bₙ) · (1 − ψₙ)`, and to its counterpart for the
second statement.

`thm:affprovind` quantifies over `BCS` (`def:bap`): bounded **ℙ-generable** ℝ-combination
sequences. By `def:ece`, ℙ-generable means there is an **e.c.** `EF`-combination progression
whose value at `ℙ` is the combination; and by `def:affcomsen` an `EF`-combination
`c + f₁φ₁ + ⋯ + f_kφ_k` names its **sentences** as well as its features. So the appendix's
application requires the sequence `⟨ψ⟩` to be efficiently writable.

The *coefficient* `ctsind_{δₙ}(aₙ < ℙₙ(φₙ) < bₙ)` is a feature, and ℙ-generability of
`⟨a⟩`, `⟨b⟩` is exactly what makes it e.c. The *sentence* `ψₙ` is not. As printed it
contains the numerals `⌜aₙ⌝` and `⌜bₙ⌝`, so writing it requires producing those numerals
from `n`. `def:ece` supplies an e.c. **feature expression** whose *value at the market* is
`aₙ`; it supplies no program producing the numeral. Recovering the numeral means evaluating
that expression against the market's prices, and `def:marketprocess` bounds neither the
runtime of the market program nor the size of the rationals it returns — the same
unboundedness PE1 turns into a counterexample. So `aₙ` is obtainable computably but not in
time polynomial in `n`, `⟨ψ⟩` is not e.c., and `thm:affprovind` does not apply.

The omission reads as an oversight rather than a subtlety: the same statement is careful to
demand e.c. of `⟨φ⟩` and `⟨δ⟩`, which it needs for exactly this reason.

### What the repository does about it

The Lean development does **not** inherit the gap, and does not need the missing
hypothesis, because of `dd:quote-code`. The introspection target sentence is not a literal
formula containing numerals for `aₙ` and `bₙ`; it is a *code-indexed quote atom*,
`BooleanQuoteCode.sentence n = quoteAtom ⟪code, n⟫`, whose emission cost is a pairing with
`n` and is therefore independent of `a` and `b` altogether
(`BooleanQuoteCode.sentence_poly`). What the construction needs of `a` and `b` is only that
the interval predicate `aₙ < ℙₙ(φₙ) < bₙ` be **decidable**, so the deductive process can
enter the corresponding quote claim — and decidability, unlike efficiency, does follow from
ℙ-generability once a market program is in hand (`PGenerableRat.computable`, which
dovetails the feature's evaluation against the market's quote program).

So the paper's route needs `⟨a⟩`, `⟨b⟩` efficiently writable; this development's route needs
them only computable, which the printed hypotheses do give. `thm:ref` is therefore
formalized at the paper's own hypothesis strength over the constructed inductor, and the
defect above is confined to the printed proof.

`lic_introspection_closed` (`Construction/Witnesses/QuoteCodeOfMarket.lean`) carries
exactly the paper's hypotheses. Two `PolyRatCodes` premises formerly stood on the interval
bounds; they were consumed only as `.computable`, which is derivable from the endpoint's own
`GeneratedRatFeature` data, and have been removed. The node is classified `exact`.

---

## PE7 — The `Con(PA)(Ack)` gloss contradicts its own definition (`sec:trust`)

**Off-by-one in an illustrative gloss; no statement or proof is affected.**

tex:1857 defines `Con(Θ′)(ν)` as "there is no proof of ⊥ from `⌜Θ′⌝` with `ν` or fewer
symbols" — an inclusive bound. Two lines later, tex:1859 glosses
`Con(PA)(⌜Ack(10,10)⌝)` as saying that any proof of ⊥ from PA "requires **at least**
Ack(10,10) symbols"; by the definition it requires *more than* Ack(10,10).

The formalization follows the definition, not the gloss: `BProv`'s bound is inclusive
(`dSize d ≤ k`, `Framework/BoundedConsistency.lean`), so `conWithin T k` is exactly the
definition's reading. Recorded so that the inclusive bound is not misread as drift
against the gloss.

---

## PE8 — `app:incons` invokes representability where Σ₁-completeness is needed

**The theorem is fine; the printed proof cites the wrong hypothesis for its key step.**

The proof of `thm:incons` (tex:4487–4491) argues, for both conjuncts: each
`⌜Θ′ₙ is inconsistent⌝` "is provable in 𝗣𝗔, and Θ represents computations, [so] each of
these statements is provable in Θ". Representability of computable functions
(tex:600–604) does not transfer 𝗣𝗔-provability to Θ: it yields facts of the form
`Θ ⊢ ∀ν(γ(n̄,ν) ↔ ν = ȳ)`, not an inclusion of theories. What actually discharges the
step is that the inconsistency statements are Σ₁ and true, so Σ₁-completeness of Θ
suffices — a property the paper never states among its standing assumptions on Θ
(tex:993–997).

The formalization proves the step by the correct route: `re_complete_mp` under
`[𝗣𝗔⁻ ⪯ T]`. This is one of the two places that motivate the globally disclosed
`[𝗣𝗔⁻ ⪯ T]` hypothesis (see the README's discussion of arithmetic-theory assumptions):
the paper's own argument tacitly consumes arithmetical strength beyond its stated
premises at exactly this point.


---

## Citation record — where the paper actually says it

Not errata: these are locations in `1609.03543v5-main.tex` that this development cites and
that are easy to cite wrongly, recorded here because each cost a correction pass. A wrong
`tex:` line is invisible to every checker.

| what | where | the mistake to avoid |
| --- | --- | --- |
| the primitive connectives `¬ ∧ ∨ ⟹ ⟺` | tex:560 | — |
| the quantifiers `∀ ∃`, and `∀x.φ` read as `¬∃x.¬φ` | tex:568-573 | citing tex:571-577 |
| the prime-sentence decomposition (Boolean atoms of a first-order theory) | tex:566-573 | citing tex:560, which is the connective paragraph |
| `⌜⟨f⟩(7)⌝` is shorthand for `⌜γ_f(7,ν)⌝` | tex:1655 | citing tex:1660 |
| `thm:pazfc`'s own hypothesis — `Θ′` **any recursively axiomatizable consistent theory** | tex:1882 | quoting it as `𝗣𝗔 + Con(𝗣𝗔)`, or as containing `Θ`; the paper states **no** containment hypothesis |
| the informal "stronger than `Θ`" framing of `thm:pazfc` | tex:1879 | reading it as part of the theorem's hypotheses |
| `𝗭𝗙𝗖` as the worked example for `thm:pazfc` | tex:1889 | — |
| `def:ec` meters *writing the object out* | tex:753-755, explicitly tex:1931-1933 | reading it as a bound on a Gödel code's value |
