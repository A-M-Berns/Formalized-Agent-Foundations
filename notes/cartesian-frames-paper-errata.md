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

4. **Claim 43 (App. A), proof gap.** The printed proof defines
   `h₃(y, z) = (y, b, h₀(z))` "for some `b ∈ B` (it does not matter which)"
   (TeX ~L1009), silently assuming `Agent(D)` is nonempty; when `B = ∅` the
   morphism cannot be constructed and the argument does not run. The claim is true
   as stated: `B = ∅` forces `X × Y` empty (via the biextensional equivalence),
   and every obligation in the required equivalence quantifies over an `X` while
   reaching a `Y`, so a degenerate `M` (image vacuously all of `∅`) works. The
   Lean proof (`Frame.MultSubagent.multSubagentCurry`) case-splits on
   `Nonempty D.Agent`, reproducing the paper verbatim in the nonempty case. Same
   shape as erratum 1: printed proof incomplete, statement sound.

5. **Definition 50 (App. B), false parenthetical.** After the covering definition
   the paper writes "`E` is covered by `F`, or equivalently, there is a morphism
   `(g, h)` with `h` surjective" (TeX ~L1209). The two are not equivalent:
   different environment states of `C` may be hit by different morphisms.
   Counterexample over `W = Bool`: `C = (PUnit, Bool, (_, e) ↦ e)`,
   `D = (Bool, PUnit, (b, _) ↦ b)` — the covering condition holds, but every
   morphism's `env` has singleton domain, so none is surjective onto `Bool`.
   (Compiled witness, round-2 audit.) `Frame.SubagentCovering` formalizes the
   correct per-`e` form.

6. **Definition 10, carrier naming.** The definition introduces the image frame as
   `(B, F, ⋆)` as if the carriers changed; the functor leaves agent and
   environment carriers unchanged — only outcomes are mapped through `p`. (Benign
   once noticed; recorded because it misled a first reading.)
