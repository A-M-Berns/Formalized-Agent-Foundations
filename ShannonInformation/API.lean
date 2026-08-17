/-
Copyright (c) 2026 Formalized Agent Foundations contributors.
Released under Apache 2.0 license.

This module is FAF-authored.  The mathematics it exposes is **not**: it is re-exported
from a pinned, audited vendoring of the PFR project's Shannon-information library.  See
`ShannonInformation/README.md` and `ShannonInformation/vendor/PROVENANCE.md`.
-/
module

public import PFR.ForMathlib.Entropy.Basic
public import PFR.ForMathlib.Entropy.Measure
public import PFR.ForMathlib.FiniteRange.Defs
public import PFR.ForMathlib.ConditionalIndependence
public import ShannonInformation.FiniteEntropy.Defs
public import ShannonInformation.FiniteEntropy.Pi

/-!
# `ShannonInformation.API` — the FAF-facing Shannon-information surface

This is the **recommended import** for any FAF work that needs entropy, conditional
entropy, mutual information, or conditional mutual information:

```lean
import ShannonInformation.API
```

A downstream paper formalization should not need to name a `PFR.*` module, and should not
define its own entropy: the vocabulary below is the shared one.

## What this module is

A thin re-export layer, deliberately.  FAF has **not** independently formalized Shannon
information theory; it consumes a pinned, kernel-checked formalization produced by the
[PFR project](https://github.com/teorth/pfr) (Tao et al.), vendored at commit
`01c9b666945eaf73b3f7d8b20ffe003f8640e630` under Apache-2.0.  The value this module adds
is *stability and discoverability*, not mathematics:

* one import path that survives re-vendoring, so downstream files do not encode which
  upstream module happens to hold which lemma today;
* a documented inventory of the vocabulary FAF expects to use;
* a small number of generic convenience lemmas that are genuinely missing upstream, each
  marked below and each proved here (never `sorry`ed, never axiomatized).

There is intentionally **no wrapper ontology**: `entropy` is PFR's `entropy`, `H[X ; μ]` is
PFR's notation, and a lemma cited through this module is the same declaration an auditor
would find upstream.  Aliases are avoided except where noted, precisely so that a
statement read here cannot subtly differ from the statement that was proved.

## Scope — read this before relying on a statement

The vendored API is stated for **finite-range** random variables on measure spaces
(`FiniteRange`, `MeasurableSingletonClass`, `Countable`), which is *narrower* than the
"countable discrete with finite entropy" setting some agent-foundations papers assume.
This is a real mathematical boundary, not a presentational one, and it is analysed in
`ShannonInformation/SCOPE.md`.  **Read that file before assuming a result applies to a
variable with infinite range.**  The hypothesis class those theorems should eventually be
stated over — `ShannonInformation.FiniteEntropyOf` — exists as of this commit, with its
instances and closure lemmas; the theorems themselves have not moved yet.

## Vocabulary exposed

| concept | declaration | notation |
| --- | --- | --- |
| entropy | `ProbabilityTheory.entropy` | `H[X ; μ]`, `H[X]` |
| conditional entropy | `ProbabilityTheory.condEntropy` | `H[X \| Y ; μ]` |
| mutual information | `ProbabilityTheory.mutualInfo` | `I[X : Y ; μ]` |
| conditional mutual information | `ProbabilityTheory.condMutualInfo` | `I[X : Y \| Z ; μ]` |
| finite-range variables | `FiniteRange` | — |
| finite-entropy measures | `ShannonInformation.FiniteEntropyMeasure` | — |
| finite-entropy variables | `ShannonInformation.FiniteEntropyOf` | — |
| conditional independence | `ProbabilityTheory.CondIndepFun` | — |

Selected facts, by the category the task cares about:

* **chain rules** — `chain_rule`, `chain_rule'`, `chain_rule''`, `cond_chain_rule`,
  `cond_chain_rule'`;
* **nonnegativity** — `entropy_nonneg`, `condEntropy_nonneg`, `mutualInfo_nonneg`,
  `condMutualInfo_nonneg`;
* **independence characterizations** — `mutualInfo_eq_zero` (`I[X : Y] = 0 ↔ IndepFun X Y`),
  `condMutualInfo_eq_zero` (`I[X : Y | Z] = 0 ↔ CondIndepFun X Y Z`), `entropy_pair_eq_add`;
* **identically-distributed invariance** — `IdentDistrib.entropy_congr`,
  `IdentDistrib.condEntropy_eq`, `IdentDistrib.mutualInfo_eq`;
* **entropy under maps / pullback** — `entropy_comp_le`, `entropy_comp_of_injective`,
  `entropy_of_comp_eq_of_comp`, `condEntropy_comp_self`, `mutual_comp_le`;
* **submodularity and friends** — `entropy_submodular`, `entropy_pair_le_add`,
  `condEntropy_le_entropy`, `entropy_triple_add_entropy_le`.

`#print axioms` on anything reachable from here reports only `propext`,
`Classical.choice`, `Quot.sound`; see `AxiomAudit.lean`.
-/

public section

namespace ShannonInformation

/-!
## No new entropy *definitions*; one FAF-authored generalization layer

This module adds **no** entropy definitions.  Every information quantity a client reads
through it is upstream's, verbatim, so a statement here cannot drift from the statement
that was actually proved, nothing has to be re-audited when the vendored tree is re-pinned,
and FAF's authorship claim stays honest: this repository has not re-formalized Shannon
information theory, it is consuming PFR's.

It is, however, **no longer empty of new mathematics**.  Re-exported alongside the vendored
surface is one FAF-authored layer, `ShannonInformation/FiniteEntropy/`, which exists
because the vendored theorems are stated for `FiniteRange` variables and several FAF
consumers are not inside that fragment (`SCOPE.md` §2, and
`Condensation/notes/finite-range-generalization-plan.md`).  It adds a *hypothesis class*,
not a definition — entropy is still PFR's `measureEntropy`:

* `ShannonInformation.FiniteEntropyMeasure` — a `Prop`-valued class asserting that the
  series defining `Hm[μ]` converges.  Its summand is `measureEntropy`'s summand verbatim.
* `ShannonInformation.FiniteEntropyOf X μ` — abbreviation for
  `FiniteEntropyMeasure (μ.map X)`.
* `ShannonInformation.finiteEntropy_of_finiteSupport`,
  `ShannonInformation.finiteEntropy_of_finiteRange` — instances, so the entire existing
  `FiniteRange` instance graph discharges the new class automatically.  Nothing that was
  provable before stops being provable.
* `ShannonInformation.FiniteEntropyOf.summable` — the bridge to `entropy_eq_sum`: under
  the class, the `∑'` that lemma writes `H[X ; μ]` as is a genuine sum, not the junk value
  `0` that `∑'` returns on a non-summable family.
* closure lemmas: `finiteEntropyMeasure_map`, `finiteEntropyMeasure_prod`,
  `finiteEntropyOf_comp`, `finiteEntropyOf_fst`, `finiteEntropyOf_snd`,
  `finiteEntropyOf_pair`, `finiteEntropyOf_pullback`, and — for a **finite** index only,
  since countable products genuinely fail — `finiteEntropyOf_measurableEquiv`,
  `finiteEntropyOf_piFin`, `finiteEntropyOf_pi`.
* the abstract nonnegative-family core they rest on, in
  `ShannonInformation/FiniteEntropy/Summable.lean`: `negMulLog_tsum_le`,
  `tsum_negMulLog_eq_add`, `tsum_mul_log_div_nonneg`, `negMulLog_le_add_of_le`,
  `summable_negMulLog_tsum_fiber`, `tsum_negMulLog_tsum_fiber_le`.

The vendored *theorems* are still stated at `FiniteRange`; restating them at
`FiniteEntropyOf` is later phases of that plan.  Every declaration above is proved here
(never `sorry`ed, never axiomatized), listed in `ShannonInformation/README.md`, and covered
by `ShannonInformation/AxiomAudit.lean`.

Any further genuinely generic convenience lemma needed by more than one client belongs
here, inside this namespace, under the same conditions.  Paper-specific material never
belongs here.

Derivations that clients can do in a line or two — `H[X | X] = 0`, entropy of a constant,
zero mutual information for an independent pair — are demonstrated in
`APITests/ShannonInformation.lean` rather than pre-packaged here, so that those tests
actually test the surface instead of restating it.  The non-vacuity witness for
`FiniteEntropyOf` — a geometric variable on `ℕ`, which has finite entropy and *no* finite
range — lives in `APITests/ShannonInformationFiniteEntropy.lean`.
-/

end ShannonInformation
