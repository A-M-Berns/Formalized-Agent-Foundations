# Formalization Knowledge — Parametric Bounded Löb (Critch 2019), branch `critch-pbl`

Permanent, curated facts about this formalization. Committed with the code; read by every
harness agent before working. Add an entry only if a future fresh-context agent would act
differently for knowing it. One bullet per fact, newest last. Cross-reference finding IDs
(RN-Fxx) where an entry originated from an audit. Paper: `notes/critch2019.pdf`
(§3 pp. 3–5 defines □ₖ; §3.2 Properties 1–2; §4 Defn 1 + Properties 3–4 + Theorem 1).
Project plan: `notes/critch-pbl-roadmap.md` — its four standing scope decisions are binding.

## Correspondence table

| Paper (§/symbol) | Lean name | Notes |
|---|---|---|
| §3.1 `BBew[m,n,k]` | (Phase 0: `bewBounded`, TBD) | bound `k` is an **object-level** variable, unlike Foundation's `RestrictedProvable` (meta-level bound) |

## Design decisions

- Roadmap standing decision 1: proof-size measure is an internal derivation-size function
  native to Foundation's encoding, **not** the paper's "characters with abbreviations" and
  not Gödel-number magnitude. This is a type-(c) modeling substitution by construction —
  disclosed up front, per the repo's provenance discipline. Theorems only need *some*
  computable expansion function E for the chosen measure.
- Roadmap standing decision 2: agents are sentence families via derivability conditions
  (paper eq. 6.5); program semantics/quining out of scope (mirrors the Barász boundary).
- Roadmap standing decision 3: Gödel-quote/diagonal machinery keeps unary numerals;
  efficient numerals only on the parameter-specialization path.
- Roadmap standing decision 4: numeral cost is an abstract ν(k) — never bake in O(lg k).

## Intentional deviations from the paper

(None yet beyond standing decision 1's measure substitution, recorded above until its
formal DISCLOSURE case is made.)

## Disclosures (residual modeling substitutions)

(None approved yet.)

## Paper errata

## Pitfalls
