# Logical Induction — paper errata and open formalization questions

_Last reviewed: 2026-07-23 against arXiv:1609.03543v5._

This ledger records defects in the source paper rather than discrepancies introduced by the
Lean development. Paper errata are intentionally excluded from
[`m7-errata-audit.md`](m7-errata-audit.md), whose scope is the faithfulness and completeness
of this repository.

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
