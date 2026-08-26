# Logical Induction — paper errata and open formalization questions

_Last reviewed: 2026-07-23 against arXiv:1609.03543v5._

This ledger records defects in the source paper rather than discrepancies introduced by the
Lean development. Paper errata are intentionally excluded from
[`faithfulness-audit-2026-08-08.md`](faithfulness-audit-2026-08-08.md), whose scope is the
faithfulness and completeness of this repository.

## PE1 — Closure under Finite Perturbations (`thm:ifp`)

**Status: the published theorem is FALSE, and the repository now proves it false.**
`FinitePerturbationCounterexample.not_overgeneral_ifp`
(`Construction/Witnesses/FinitePerturbationWitness.lean`) is a kernel-checked, axiom-clean
refutation of the unrestricted statement at the paper's own quantifier, with no theory
parameter. The published *proof* is separately invalid, for the independent reason recorded
below; the repository additionally proves a corrected finite-*support* theorem, which is the
restricted case in which the published proof's own justification is sound.

### Published statement and proof

The paper defines a pricing as any computable rational valuation and a market as a computable
sequence of pricings (`1609.03543v5-main.tex:676–682`). Neither definition requires finite
support, polynomial-time price lookup, or a polynomial bound on the size of the returned
rational. The property section explicitly says that, although the constructed `LIA` has
finite support each day, its results quantify over arbitrary markets
(`1609.03543v5-main.tex:993–997`).

`thm:ifp` says that two markets which differ on only finitely many days are either both
logical inductors or both non-inductors. In `app:ifp`, an exploiting trader is transported
between the markets by transforming every old price leaf `φ^{*i}`, for `i < N`, into the
constant price `P_i(φ)`. The proof claims that this transformation is efficiently computable
because only finitely many constants are needed (`1609.03543v5-main.tex:6047–6062`).

That justification is false. There are finitely many early days `i`, but `φ` ranges over all
sentences. As the trader's day grows, its efficiently generated strategy may mention new
sentences in old-day price leaves. The transformation must therefore evaluate the arbitrary
computable functions `φ ↦ P_i(φ)` and emit their exact rational results. The market
definition supplies no polynomial runtime or output-size bound, so this transformation need
not preserve efficient computability.

Hard-coding the finitely many *programs* for the early pricings does not fix the issue:
executing those programs on a varying sentence can still take superpolynomial time, and the
resulting rational can itself require superpolynomially many symbols to print.

### What the current Lean development proves

[`LogicalInduction/Properties/FinitePerturbations.lean`](../LogicalInduction/Properties/FinitePerturbations.lean)
formalizes the semantic freezing transformation, its rank and syntax properties, the bounded
net-worth error, and preservation of exploitation. Its `EfficientPrefixPatch P cutoff`
records the missing computational condition: freezing the exact early quote table of `P`
must preserve efficient trader generation.

The theorem `lic_iff_of_finitePerturbation` proves the paper's biconditional when both market
prefixes carry this certificate. This is strictly weaker than unrestricted `thm:ifp`.

**Correction (2026-08-02).** An earlier version of this paragraph asserted that the
restricted statement "is not vacuous", on the strength of a declaration
`liaEfficientPrefixPatch` said to build the required finite lookup compiler. **No such
declaration exists** — the name appears nowhere in the repo outside prose, and
`Properties/FinitePerturbations.lean` states the opposite in its own words: the efficiency
certificate for the emitted stream is not discharged, so no `LIA` instance of
`EfficientPrefixPatch` exists. `EfficientPrefixPatch` therefore has **zero inhabitants
anywhere**, and `lic_iff_of_finitePerturbation`'s hypothesis has no exhibited witness. The
restricted statement must not be described as non-vacuous until one is built. This is
exactly the failure the inhabitation lens exists to catch, and it survived in the ledger
that was supposed to be catching it.

The informal large-output example in the Lean source shows why the certificate cannot be
derived from `ComputableMarket` alone: an early pricing can assign a sentence of code `n` a
rational whose exact numeral has size exponential—or worse—in `n`. This establishes a
failure of the paper's proposed efficient transformation, not by itself a counterexample to
the theorem's logical-inductor biconditional. In the repository's clocked interpreter an
output may be numerically larger than its raw fuel, but `codeEvaln_result_le` together with
`codeEvalBound_poly` bounds a fixed program's output by a code-dependent polynomial in that
fuel. That is the output-size obstruction used here.

### The corrected theorem (2026-08-26)

Finite support is exactly what rescues the hard-coding step, and the repository now proves
that case. `FiniteSupportPerturbation P P'` says the two markets differ on only finitely
many `(day, sentence)` price *coordinates*; the freeze then reads its quote table at
finitely many places, so the appendix's "hard-code the constants" justification is
literally valid. `lic_iff_of_finiteSupportPerturbation` and
`machine_lic_iff_of_finiteSupportPerturbation` (the latter at the paper's own quantifier,
`MachineEfficientTrader`) carry it.

Two things must be said plainly about that theorem, and are said at the statement:

1. **Its hypothesis is strictly stronger than the paper's.** Finite support implies
   tail agreement (`FiniteSupportPerturbation.tail_agree`); the converse fails — the
   day-`0` huge-numeral market above agrees with `LIA` from day `1` and is not finitely
   supported. So this is a *corrected* theorem, a proper restriction of `thm:ifp`, not a
   restatement of it. The published unrestricted theorem is still unresolved and its
   published proof is still invalid.
2. **Its machine certificate is now inhabited; its fuel certificates are not, and the
   theorem is still not exhibited non-vacuous end to end.** See the 2026-08-26 update
   below for the precise state. Nothing here should be described as non-vacuous without
   reading it — that is the failure the 2026-08-02 correction above exists to catch.

### The unrestricted statement, settled (2026-08-26): it is false

What was a research-level stretch goal is now a theorem. Alternative 2 below is the one that
held.

1. ~~**The unrestricted theorem:** prove `thm:ifp` for arbitrary computable markets using a
   transport argument that does not require efficient access to the changed prefixes~~ —
   impossible, by the counterexample.
2. **Its negation** — *proved*: `not_overgeneral_ifp`. The construction is exactly the
   advice-tape route this ledger anticipated below, made precise:

   * `P` is the constructed `LIA` over the `𝗜𝚺₁` theorem process, a genuine machine logical
     inductor (`LIA_isMachineLogicalInductor`).
   * `χ` is the repo's diagonal price family: in every world consistent with the completed
     theory, `χ n` holds exactly when `P n (χ n) < 1/2`. So a trader knowing only that one
     bit earns a *certain* `≥ 1/2` on day `n` once the day has settled — buy below the
     threshold, where the sentence is true; short at or above it, where it is false.
   * `P'` changes **day `0` only**, publishing the sign and schedule bits as the prices of
     advice atoms at otherwise unused tags. It is a legal `ComputableMarket`: the day-`0`
     row is a total computable search, terminating by propositional compactness
     (`DeductiveProcess.exists_stage_entails`).
   * The exploiting trader is genuinely `MachineEfficientTrader`. It never computes the
     bits: its day-`n` coefficient is the rank-`0` feature
     `price (schedAtom n) 0 * (2 * price (signAtom n) 0 - 1)`, so the *market* supplies the
     advice at valuation time. A sparse schedule lets each round settle before the next
     opens, bounding downside by `1` while the settled rounds accumulate `≥ 1/2` each.

**The mechanism, stated plainly.** A single changed pricing day is an infinite computable
function, and `def:marketprocess` puts no bound on its runtime or output size. That is
enough for one day to act as persistent historical advice, handing an efficient trader
information it could not compute for itself. The gap between *computable* and *efficiently
computable* is exactly what the perturbation smuggles across, and no amount of care in the
appendix's transport argument can close it — the theorem, not merely its proof, is wrong.

The earlier note that formal success "requires the full separation result — one
tail-equivalent market satisfying the LIC and the other admitting an efficient exploiter —
not merely another proof that `EfficientPrefixPatch` can be uninhabited" was the right bar,
and it is the bar that has been met.

The finite-support theorem is a *third* outcome, and it settles neither of these: it
repairs the appendix's argument on the restricted domain where that argument is valid,
while leaving the unrestricted statement open.

### The restricted theorems still have no witness (and what stands in the way, 2026-08-26)

**`MachineFiniteSupportPatch` is now inhabited**
(`FreezeOracle.machineFiniteSupportPatch_ofTable`), for a market whose frozen coordinates
are presented by a finite entry table subject to three conditions: `BotFree` and
`NoReserved` per table sentence (bundled as `Recognizable`) and a `TablePresentation`
naming exactly the coordinates of `S`. The witness is at a table with a real row, and the
quote is a parameter, so the two markets can genuinely differ on `S` — the degenerate
`S = ∅` route is not what inhabits it. The complexity budget `R_length_le`, previously
assumed, is now *derived*, because the emitted suffix is one of finitely many constant
words.

**What is still not established.** No concrete pair of computable markets is constructed,
so `machine_lic_iff_of_finiteSupportPerturbation` is not exhibited non-vacuous end to end:
the freeze certificate is discharged, the market pair is not. And the fuel-class
certificates `EfficientPrefixPatch` and `FiniteSupportPatch` remain **uninhabited** — the
fuel calculus does not close over the escape-leaf decode the lookup needs, which is
precisely the `dd:fuel` inverse-operation ceiling.

Two things sharpened the route to this, and are recorded because they are what made it
reachable:

* **The escape-leaf keystone is narrower than recorded.** `RpnFreeze.lean` said the freeze
  matcher cannot compare against a fixed numeral because `Formula.ofNat` ignores the payload
  at tag `0`, so `decode` is not injective and the test reduces to `Nat.unpair` / integer
  square root. True, but tags `1`–`4` *are* injective given injective sub-decodes, so the
  decoder is injective on exactly the **falsum-free** sentences
  (`decode_eq_some_iff_of_botFree`, `Construction/Witnesses/CanonicalCodes.lean`), and there
  the whole test is a constant comparison (`sentenceMatches_of_botFree`). The restriction is
  necessary rather than a proof artifact — `decode_falsum_noncanonical` and
  `decode_and_noncanonical` exhibit the ambiguity and its propagation. So square root is
  forced **iff** the frozen quote table contains a `⊥` subformula. It is not known whether
  `LIA`'s table is `⊥`-free; its entries are populated dynamically.
* **The remaining obstruction is the FP transport, not the square root.** Three pieces, none
  built: a selector-indexed token model for `EF.freezeOn` (the existing exactness chain is
  keyed to `freezeBefore`/`cutoff`); an FP certification of the freeze transducer through
  `Framework/Machine/FPFold.lean`, including the polynomial state bound on malformed inputs;
  and the run-level decision `runMatches` as an FP function, where the *structured
  paper-prime leaf* is a second, independent ambiguity source that the `⊥` result does not
  touch.

One degenerate discharge is available and is deliberately **not** taken: `S = ∅` makes the
freeze the identity and inhabits the structure trivially, but it also forces `P = P'`. That
is exactly the degenerate non-vacuity this repository's audit standard rejects, and it is
recorded here so that nobody later mistakes it for a discharge.

The precise verdict documentation should now use:

> The published unrestricted finite-perturbation theorem is **false**, and the repository
> proves it false. Its published proof is separately invalid. The repository proves a
> corrected finite-*support* theorem — the restricted case in which the published proof's
> own justification is sound — and the efficiently patchable case at the paper's own
> hypothesis shape. Neither restricted theorem has an inhabited patch certificate.

## PE2 — Swapped good-feedback hypothesis in the expectation unbiasedness pair (`thm:recurringunbiasednessexp`, `thm:wubexp`)

**Status:** confirmed statement-level erratum in arXiv v5, not a soundness defect. The
repository's formalization independently carries the corrected hypotheses. Reported here for
disclosure; worth forwarding to the authors.

### The defect

The two expectation-level unbiasedness theorems in §4.8 have the good-feedback hypothesis
attached to the wrong member of the pair, mirroring the correctly-stated affine pair
(`thm:recunbiasedaff` / `thm:wubaff`) incorrectly.

- **Expectation Recurring Unbiasedness, Thm 4.8.15** (`main.tex:1812–1820`,
  `\label{thm:recurringunbiasednessexp}`) states its weighting as "a `\pgenable` divergent
  weighting **weighting** such that the support of `w` is contained in the image of `f`."
  This carries a **spurious** good-feedback clause: (i) it references a deferral function `f`
  the statement never introduces, and (ii) its correctly-stated affine analogue Affine
  Recurring Unbiasedness (`thm:recunbiasedaff`, `main.tex:1469–1478`) has **no** such clause.
  The doubled word "weighting weighting" is a second typo in the same line.

- **Expectation Unbiasedness From Feedback, Thm 4.8.16** (`main.tex:1822–1832`,
  `\label{thm:wubexp}`) states only "a `\pgenable` divergent weighting" and **lacks** the
  "support ⊆ image of `f`" clause — even though its affine analogue Affine Unbiasedness from
  Feedback (`thm:wubaff`, `main.tex:1480–1490`) **does** carry it. Its timely-computability
  clause also writes `\thmval(\aff_n)` where the theorem's sequence is `\affluv`.

So the "support of `w` contained in the image of `f`" good-feedback hypothesis has been
swapped: it belongs on the feedback theorem (4.8.16) and is absent there, while appearing
spuriously on the recurring theorem (4.8.15).

### Why it is a transcription error, not a mathematical one

The paper's own appendix proofs use the intended (correct) hypotheses. Expectation Recurring
Unbiasedness is proved by reduction to the clause-free affine 4.5.9, and Expectation
Unbiasedness From Feedback by reduction to the clause-bearing affine 4.5.10. The theorems are
therefore true as intended; only the printed §4.8 statements (restated verbatim at v5
pp. 112–113) are garbled. The correct statements are: 4.8.15 with a bare generable divergent
weighting concluding a limit point at 0; 4.8.16 with the deferral function, timely value
computability, and support ⊆ image of `f`, concluding `\eqsim_n 0`.

### Repository status

The Lean development independently places the hypotheses correctly, so it does not inherit the
bug. `recurringunbiasednessexp` (`Construction/Witnesses/HistoricalMaturity.lean`) takes a
generable divergent weighting with no deferral/image-of-`f` hypothesis and concludes a limit
point; the pseudorandom/feedback capstones (`prandaff` and the `wubexp` route) carry the
deferral function, `PatientSettlementClock`, and pseudorandomness data and conclude a full
limit. This is forced by construction: the full-limit conclusion is not provable without the
deferral clause, and the limit-point conclusion does not need it, so building the actual
proofs disciplined the statements into the corrected shape. The discrepancy was not previously
recorded as a paper erratum.

## PE3 — `Settled(n,m)` decidability as written (`app:prandaff`)

**Status:** repaired in-repo; the paper's assertion is fixable but not literally true as
stated.

`1609.03543v5-main.tex:4865` asserts that `Settled(n,m)` — "all worlds in
`pcworlds(D_m)` value the combination `A_n` at `thmval(A_n)`" — is decidable. As written
the predicate mentions `thmval(A_n)`, which is not computable, so the literal test is not
one a machine can run. The repair (which the paper's proof clearly intends): under
consistency of the theory, settlement is equivalent to inter-world *agreement* on the
finitely many relevant truth assignments, which is a finite decidable test given exact
rational market quotes. Formalized as
`AffineCombination.DeterminedViaTheory.settled_iff_agree`
(`Properties/Calibration.lean`), with the rational-quote requirement supplied by
`IsLogicalInductor.marketComputable`. Discovered during the 2026-07-28 F9 investigation.

## PE4 — Patience argument assumes a monotone deferral function (`app:prandaff`)

**Status:** repaired in-repo by a strengthened trader; not previously recorded.

`1609.03543v5-main.tex:4905` argues the constructed weighting is `f`-patient via
`Σ_{n≤m} [f(n) ≥ m] α_n ≤ 1`, which implicitly assumes the deferral function is
monotone; `def:deferralfunc` (tex:1240) requires only `f(n) > n`. For non-monotone `f`
the bracket can admit unboundedly many terms between `m` and `f`-images from far below.
The repo's trader replaces the bracket with the envelope `max_{k≤i} f k`
(`deferralEnvelope`, `Properties/Pseudorandomness.lean`), which restores the bound for
arbitrary deferral functions. Justified in the docstring at the definition site;
surfaced as an erratum during the 2026-07-28 F9 investigation.

## PE5 — Sign inconsistency in `def:seqprand` vs. `thm:prand`'s one-sided forms

**Status:** repaired in-repo by orienting the definition to its advertised conclusion;
disclosed at the definition site. Minor, and plausibly a transcription slip.

`def:seqprand` (`1609.03543v5-main.tex:1305–1311`) displays the weighted average of
`(pᵢ − ThmInd(φᵢ))` and says the `≂ₙ` may be replaced by `≳ₙ` to give "varied
pseudorandom **above** ⟨p⟩". `thm:prand` (tex:1314–1320) then pairs that notion with the
conclusion `Pₙ(φₙ) ≳ₙ pₙ`. With the paper's centering those two `≳ₙ`s point in opposite
directions: bounding `avg(p − ThmInd)` *below* says the truth frequency undershoots `p`,
which forces the price *down*, not up. The repo centers the other way —
`VariedPseudorandomAbove truth p := PseudorandomAbove (truth − p)`
(`Properties/Pseudorandomness.lean`) — which is the orientation the exploiting-trader
argument actually needs and which makes the paper's advertised conclusion come out
right. Disclosed in that definition's docstring ("with the sign oriented to match its
advertised conclusion"). Surfaced by the 2026-07-29 closing audit.
