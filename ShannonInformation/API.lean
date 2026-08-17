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
public import ShannonInformation.FiniteEntropy.ChainRule
public import ShannonInformation.FiniteEntropy.Inequalities
public import ShannonInformation.FiniteEntropy.Derived

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
`ShannonInformation/SCOPE.md`.

**As of this commit there are two parallel surfaces**, and choosing between them is the
first decision a client makes:

* the vendored `ProbabilityTheory.*` statements, at `[FiniteRange X]`;
* FAF's `ShannonInformation.*` statements, at `[ShannonInformation.FiniteEntropyOf X μ]`,
  which is strictly weaker (a geometric variable on `ℕ` satisfies it and has infinite
  range).

See "Which version to cite" below.  **Read `SCOPE.md` before assuming a result applies to a
variable with infinite range**: not every vendored theorem has been restated.

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

## Which version to cite

`ShannonInformation.foo` and `ProbabilityTheory.foo` are, for most of the names below, the
**same fact with different finiteness hypotheses**.  Prefer the `ShannonInformation` one
unless you specifically want the vendored statement: `FiniteRange X` gives
`FiniteEntropyOf X μ` by a priority-100 instance, so anything provable through the vendored
version is provable through ours, and not conversely.

| fact | vendored, at `FiniteRange` | FAF, at `FiniteEntropyOf` |
| --- | --- | --- |
| chain rules | `ProbabilityTheory.chain_rule`, `.chain_rule'`, `.chain_rule''`, `.cond_chain_rule`, `.cond_chain_rule'` | `ShannonInformation.` same names |
| `H[X \| Y]` as a sum | `ProbabilityTheory.condEntropy_eq_sum` (a `Finset` sum) | `ShannonInformation.condEntropy_eq_tsum` (a `tsum`) |
| subadditivity, mutual information | `ProbabilityTheory.entropy_pair_le_add`, `.mutualInfo_nonneg`, `.condMutualInfo_nonneg` | `ShannonInformation.` same names |
| independence characterizations | `ProbabilityTheory.mutualInfo_eq_zero`, `.entropy_pair_eq_add`, `.condMutualInfo_eq_zero` | `ShannonInformation.` same names |
| submodularity | `ProbabilityTheory.entropy_submodular`, `.entropy_triple_add_entropy_le`, `.condEntropy_le_entropy` | `ShannonInformation.` same names |
| data processing | `ProbabilityTheory.entropy_comp_le`, `.mutual_comp_le`, `.condEntropy_comp_ge` | `ShannonInformation.` same names |
| conditional mutual information | `ProbabilityTheory.condMutualInfo_eq`, `.condMutualInfo_eq'` | `ShannonInformation.` same names |
| entropy under maps | `ProbabilityTheory.condEntropy_comp_self`, `.condEntropy_of_injective'`, `.entropy_of_comp_eq_of_comp` | `ShannonInformation.` same names |
| identically distributed | `ProbabilityTheory.IdentDistrib.condEntropy_eq` | `ShannonInformation.IdentDistrib.condEntropy_eq` |
| everything hypothesis-free | `ProbabilityTheory.entropy_nonneg`, `.condEntropy_nonneg`, `.entropy_comm`, `.entropy_assoc`, `.entropy_comp_of_injective`, `.condEntropy_comp_of_injective`, `.entropy_prod_comp`, `.mutualInfo_comm`, `.condMutualInfo_comm`, `.IdentDistrib.entropy_congr`, `.IdentDistrib.mutualInfo_eq` | — *no FAF version, and none needed*: these carry no `FiniteRange` upstream |

Not restated at `FiniteEntropyOf` (still `FiniteRange`-only): `ent_of_cond_indep`,
`mutualInfo_const`, `const_of_nonpos_entropy`, `condEntropy_of_injective`,
`condMutualInfo_of_inj`/`_of_inj'`/`_of_inj_map`, `mutual_comp_comp_le`,
`condMutual_comp_comp_le`, `IndepFun.condEntropy_eq_entropy`.  Each would generalize by the
same rewrite chain as its neighbours; see `FiniteEntropy/Derived.lean`'s header.

### Three hazards when both surfaces are open

1. **Shadowing.**  A client with `open ProbabilityTheory ShannonInformation` has two
   declarations for most names above.  Lean resolves an ambiguous overload by *elaboration
   success*, not by the enclosing namespace — so a bare `condMutualInfo_eq` can silently
   pick the `FiniteRange` version and then fail with `failed to synthesize FiniteRange Z`.
   **Write the fully qualified name whenever both surfaces are in scope.**  This is not
   hypothetical; it happened while writing this layer.

2. **`μ` explicit versus implicit.**  The FAF versions were written to their own proofs'
   convenience and do not match PFR argument-for-argument.  Examples:
   `ProbabilityTheory.entropy_pair_le_add hX hY μ` versus
   `ShannonInformation.entropy_pair_le_add hX hY` (`μ` implicit);
   `ProbabilityTheory.condEntropy_le_entropy μ hX hY` versus
   `ShannonInformation.condEntropy_le_entropy hX hY`.  Also
   `ShannonInformation.condMutualInfo_eq_zero` takes an extra `hZ : Measurable Z` that the
   vendored one does not need.  Swapping namespaces is a namespace swap *plus* an argument
   fix; expect the compiler to tell you which.

3. **Measure hypothesis.**  The FAF versions are at `[IsZeroOrProbabilityMeasure μ]`.  That
   matches PFR wherever PFR carries a measure hypothesis, but three vendored statements
   carry **none** — `ProbabilityTheory.mutualInfo_nonneg`, `.entropy_pair_le_add`,
   `.condMutualInfo_nonneg` hold for an arbitrary measure, because they route through
   `measureMutualInfo_nonneg`, which normalises internally.  A client relying on one of
   those for a non-probability measure must keep the vendored version.  One further
   direction of loss: `ShannonInformation.condMutualInfo_eq` requires `FiniteEntropyOf` on
   all three variables where `ProbabilityTheory.condMutualInfo_eq` requires `FiniteRange`
   only on `Z`.

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

On top of the class sit the restated **theorems**, which is the substance of the layer:

* `ShannonInformation/FiniteEntropy/ChainRule.lean` — `chain_rule`, `chain_rule'`,
  `chain_rule''`, `cond_chain_rule`, `cond_chain_rule'`, `condEntropy_eq_entropy_pair_sub`,
  `condEntropy_eq_tsum`, `condMutualInfo_eq`, and the integrability machinery that makes
  them non-vacuous (`integrable_entropy_cond`, `summable_measureReal_mul_entropy_cond`,
  `measureReal_mul_entropy_cond`, `map_cond_measureReal_singleton`,
  `integrable_of_summable_measureReal_mul_norm`).  No kernel layer anywhere.
* `ShannonInformation/FiniteEntropy/Inequalities.lean` — subadditivity and the independence
  equality case: `entropy_pair_le_add`, `mutualInfo_nonneg`, `mutualInfo_eq_zero`,
  `entropy_pair_eq_add`, `condMutualInfo_nonneg`, `condMutualInfo_eq_zero`,
  `condEntropy_le_entropy`, `condEntropy_pair_le_add`, `entropy_submodular`,
  `entropy_triple_add_entropy_le`, plus the abstract and law-level layers they factor
  through (`tsum_negMulLog_prod_le`, `tsum_negMulLog_prod_eq_add_iff`,
  `measureEntropy_prod_le_add`, `measureEntropy_prod_eq_add_iff`) and the conditioning
  closure (`finiteEntropyMeasure_zero`, `measureReal_map_cond_singleton`,
  `finiteEntropyOf_cond`).
* `ShannonInformation/FiniteEntropy/Derived.lean` — the corpus that follows from those two
  by rewriting: `entropy_comp_le`, `entropy_of_comp_eq_of_comp`, `condEntropy_comp_self`,
  `condEntropy_of_injective'`, `mutualInfo_eq_entropy_sub_condEntropy` and its primed twin,
  `condEntropy_comp_ge`, `mutual_comp_le`, `condMutualInfo_eq'`,
  `IdentDistrib.condEntropy_eq`.

Every declaration above is proved here (never `sorry`ed, never axiomatized), listed in
`ShannonInformation/README.md`, and covered by `ShannonInformation/AxiomAudit.lean`.  What
has *not* moved off `FiniteRange` is listed under "Which version to cite" above.

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
