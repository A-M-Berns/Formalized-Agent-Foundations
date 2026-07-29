# Logical Induction — paper errata and open formalization questions

_Last reviewed: 2026-07-23 against arXiv:1609.03543v5._

This ledger records defects in the source paper rather than discrepancies introduced by the
Lean development. Paper errata are intentionally excluded from
[`faithfulness-audit-2026-07-28.md`](faithfulness-audit-2026-07-28.md), whose scope is the
faithfulness and completeness of this repository.

## PE1 — Closure under Finite Perturbations (`thm:ifp`)

**Status:** the published proof has a genuine efficiency gap. The unrestricted theorem is
not formalized, and its truth under the paper's definitions remains unsettled. The repository
proves a qualified theorem for efficiently presentable finite prefixes.

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
prefixes carry this certificate. This is strictly weaker than unrestricted `thm:ifp`, but it
is not vacuous. The constructed `liaHistory` has finite rational belief states, and
`liaEfficientPrefixPatch` builds the required finite lookup compiler.

The informal large-output example in the Lean source shows why the certificate cannot be
derived from `ComputableMarket` alone: an early pricing can assign a sentence of code `n` a
rational whose exact numeral has size exponential—or worse—in `n`. This establishes a
failure of the paper's proposed efficient transformation, not by itself a counterexample to
the theorem's logical-inductor biconditional. In the repository's clocked interpreter an
output may be numerically larger than its raw fuel, but `codeEvaln_result_le` together with
`codeEvalBound_poly` bounds a fixed program's output by a code-dependent polynomial in that
fuel. That is the output-size obstruction used here.

### Stretch goal: settle the unrestricted statement

It is a research-level stretch goal to formalize one of the following:

1. **The unrestricted theorem:** prove `thm:ifp` for arbitrary computable markets using a
   transport argument that does not require efficient access to the changed prefixes; or
2. **More likely, its negation:** construct computable markets `P` and `P'` and a computable
   deductive process `DP` such that the markets agree from some finite cutoff onward, while
   `P` is a logical inductor over `DP` and `P'` is not.

A promising counterexample route is to use one changed early pricing as a slow-computable
advice table. Later efficiently generated traders can query that table through old-day price
features, potentially obtaining computational information unavailable to traders facing the
unmodified prefix. Formal success requires the full separation result—one tail-equivalent
market satisfying the LIC and the other admitting an efficient exploiter—not merely another
proof that `EfficientPrefixPatch` can be uninhabited.

Until one of these alternatives is formalized, documentation should use the precise verdict:

> The published proof of unrestricted finite-perturbation closure is invalid; the
> unrestricted theorem is unresolved, and the repository proves the efficiently patchable
> case.

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
