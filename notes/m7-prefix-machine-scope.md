# M7-PREFIX-MACHINE — construction scope

_Drafted 2026-07-20. Status: scoping, not started._

The boundary that, if constructed, discharges the Occam-bound disclosures
`lic_occam_lower` and `lic_occamBounds` (paper `thm:ob` / App. `ob`), moving the project
from 12/15 to 13/15 constructed. Currently disclosed in the README.

## What "constructed" means here

Provide a constructor
`PrefixMachinePresentation.ofUniversalMachine : … → PrefixMachinePresentation κ`
(and inhabit `OccamThresholdEmission`) from a concrete universal self-delimiting machine,
discharging every field of `PrefixMachinePresentation` (`Properties/OccamBounds.lean:33`)
with a real proof rather than an assumption. The paper-specific market proof downstream of
the structure is **already formalized** — this is purely about inhabiting the boundary.

## Field-by-field obligation

`PrefixMachinePresentation κ` (κ : Sentence → ℕ is prefix complexity; `prefixWeight κ φ =
1/2^(κ φ)`):

| Field | Statement | Nature | Aristotle-able? |
|---|---|---|---|
| `sentence`, `sentence_codes` | efficient enumeration of all sentences with polynomial codes | repo computability (`PolySentenceCodes`, encoding) | **no** — needs repo `PolyFueled`/`Sentence` infra |
| `approximation` + `_codes`/`_nonneg`/`_le`/`_tendsto` | polynomial rational from-below approximation to `2^{-κ}` | repo computability + basic analysis | **no** — repo infra; the `tendsto` is small analysis |
| `kraft` | `∀ N, ∑_{i<N} 2^{-κ(sentenceᵢ)} ≤ 1` | **pure combinatorics/analysis** | **YES** — this is the extractable core |
| `covers` | enumeration is surjective | repo computability | **no** |

`OccamThresholdEmission` (`:73`): two `PolyRatCodes` emission facts — repo computability.

`PrefixNegationCompiler` (`:81`): `overhead : ℕ` + `κ(∼φ) ≤ κ φ + overhead`. The
downstream `weight_div_le_neg` is **already proved**; only the `overhead` witness (a fixed
negation program's length) is a construction obligation, and a small one.

## Honest bottom line

M7-PREFIX-MACHINE is **not** a single Aristotle job. It is a genuine universal-prefix-
machine construction over the repo's computability substrate (enumeration, polynomial
from-below approximation, coverage), of which exactly **one** sub-obligation — the finite
Kraft inequality — is a clean, Mathlib-only lemma that Mathlib lacks and Aristotle could
plausibly supply. Discharging Kraft does not discharge the boundary; it removes the one
piece that is mathematics rather than plumbing, and that is currently absent from Mathlib.

Recommended order if reopened:
1. Land `kraft_inequality` (Aristotle project `scratchpad/kraft`, below), verify in-repo.
2. Build the concrete self-delimiting machine and its `code : Sentence → List Bool`
   (prefix-free, `κ φ = (code φ).length`); derive the `kraft` field from step 1.
3. Polynomial from-below `approximation` to `2^{-κ}` and its codes.
4. `covers` and the two `OccamThresholdEmission` emissions.
5. `PrefixNegationCompiler.overhead` witness.

Steps 2–5 are repo computability work of comparable weight to the other M7 witnesses;
only step 1 is offloadable.

## Extracted Aristotle project (step 1)

`scratchpad/kraft/` — Mathlib-only, statement validated to elaborate in-repo:

```lean
theorem kraft_inequality {S : Finset (List Bool)}
    (hpf : ∀ a ∈ S, ∀ b ∈ S, a <+: b → a = b) :
    ∑ w ∈ S, (1 / 2 : ℝ) ^ w.length ≤ 1
```

Prefix-free = antichain under list-prefix `<+:`. Preferred proof is the counting argument
(each length-`ℓ` codeword blocks `2^(L−ℓ)` of the `2^L` length-`L` strings; prefix-freeness
⟹ disjoint ⟹ `∑ 2^{−ℓᵢ} ≤ 1`); the docstring also notes the dyadic-interval proof.

To match the repo, the in-repo glue will instantiate `S` as the image of `Finset.range N`
under the machine's `code`, with `w.length = κ (sentenceᵢ)`; that glue is step 2, not part
of the extracted lemma.
