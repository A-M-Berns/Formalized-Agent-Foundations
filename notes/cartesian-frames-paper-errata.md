# Cartesian Frames (arXiv:2109.10996v1) — paper errata noticed during formalization

Curated during the Lean formalization in `CartesianFrames/`; each entry cites the
TeX source `notes/2109.10996v1-main.tex`.

1. **Claim 53 (App. B), proof gap.** The printed proof's final display
   (`φ_e = φ_e ∘ τ ∘ σ`, TeX ~L1323–1331) verifies only the *agent* components.
   The environment components — `j ↦ e` versus `j ↦ h_σ(h_τ(h_{φ_e}(j)))` — agree
   only up to duplicate columns (via the homotopy), while Definition 13 demands
   morphism equality. The factorization exists as claimed: redirect the factoring
   morphism's environment map on the single fibre over the chosen `f ∈ F` to `e` —
   exactly the construction in the paper's *commented-out* "currying implies
   covering" proof (TeX L1334–1377). The Lean proof
   (`Frame.SubagentCurry.subagent`) uses that construction; the claim is true as
   stated.

2. **Claim 35, binder garble.** The claim's preamble quantifies "for any subset
   `B ⊆ A`, and for any partition `F` of `E`", then lists `Assume^B` (Definition 29
   takes a subset of `E`) and `External^F` (Definition 32 takes a partition of
   `A`). The indices as printed do not typecheck against the operations'
   definitions.

3. **Claim 35, External/Internal idempotence ill-typed.** `External^B(C)` has agent
   `A/B`, and `B` is a partition of `A`, not of `A/B`, so `External^B(External^B(C))`
   is not well-formed as written (likewise `Internal`). The intended statement
   ("externalizing an already-external choice is a no-op") would need an
   interpretation the paper does not supply. **Resolution (Anson, 2026-08-11):**
   recorded as an erratum; the formalization covers only the Commit/Assume half of
   Claim 35 and deliberately leaves the External/Internal half unformalized — see
   `CartesianFrames/KNOWLEDGE.md`, intentional deviations.

4. **Definition 10, carrier naming.** The definition introduces the image frame as
   `(B, F, ⋆)` as if the carriers changed; the functor leaves agent and
   environment carriers unchanged — only outcomes are mapped through `p`. (Benign
   once noticed; recorded because it misled a first reading.)
