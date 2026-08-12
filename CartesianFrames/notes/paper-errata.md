# Cartesian Frames (arXiv:2109.10996v1) — paper errata noticed during formalization

Curated during the Lean formalization in `CartesianFrames/`; each entry cites the
TeX source `CartesianFrames/notes/2109.10996v1-main.tex`.

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

7. **Definition 54 (App. B), loose "unique".** The follow-up remark to the
   categorical definition of additive subagent — "we require the morphism from `C`
   to `D` to be unique" (TeX ~L1387) — is loose prose for "a *single shared* `φ₀`
   serves every `φ`", i.e. the quantifier order `∃ φ₀, ∀ φ, …` rather than
   `∀ φ, ∃ φ₀, …`. Read literally, as uniqueness of the element of `hom(C, D)`, it
   would falsify Claim 56: `colDup = (Fin 1, Fin 2, ![![0, 0]])` satisfies
   `colDup ◁₊ colDup` (Claim 23's reflexivity) while its endomorphism monoid has at
   least two elements — the identity and the column-collapsing `phi0`
   (`CartesianFrames.Examples.two_distinct_endos`, compiled witness, round-3 audit).
   `Frame.AddSubagentCategorical` formalizes the `∃`-reading. Note also that the
   definition's relaxation to factorization *up to homotopy* is load-bearing rather
   than cosmetic — but this has to be checked at the level of the *relation*, not at
   a single `φ₀`. The per-`φ₀` facts do **not** establish it:
   `Examples.phi0_no_exact_factorization` shows only that exact factorization fails
   at the particular `φ₀ = phi0`, and since the definition quantifies `∃ φ₀`, the
   choice `φ₀ = 𝟙 colDup` factors every `φ` exactly (`φ = 𝟙 ≫ φ`), so the
   exact-factorization variant of the relation holds for `colDup ◁₊ colDup` too and
   nothing is separated. The genuine separator is a different pair: the
   homotopy-relaxed relation holds between `colDup` and the 1×1 frame
   `Examples.oneCol` (`Examples.colDup_addSubagentCategorical_oneCol`), while the
   exact-factorization variant — a single `φ₀ : colDup ⟶ oneCol` through which every
   `colDup ⟶ ⊥` factors on the nose — fails there
   (`Examples.not_exact_factorization_colDup_oneCol`), because morphisms into `⊥` are
   determined by their environment component and `oneCol`'s environment is a
   singleton, so `(φ₀ ≫ φ₁).env` is the constant `φ₀.env 0` while `φ.env` ranges over
   both states of `colDup`'s environment. (Compiled witnesses, final adversarial
   audit.)

8. **Claim 45 (App. A), false footnote.** The proof of part (1) constructs
   `(g₀, h₀) : C → (A/B × B, E, ⋄)` and `(g₁, h₁)` back, then adds in a footnote
   (TeX L1108): "In fact these morphisms are bijective and so establish an
   isomorphism, as the reader can verify." They are not. `g₁ : A/B × B → A` is
   `g₁(q, b) = q(b)`, and it is not injective as soon as some cell has more than one
   element: for `A = {1, 2, 3, 4}` split into two 2-element cells there are four
   choice functions, so `|A/B × B| = 4 · 2 = 8 > 4 = |A|`. What the proof actually
   establishes — the two morphisms compose to something homotopic to the identity in
   both orders — is all Claim 45 needs and all `Frame.external_multSubagent` /
   `Frame.externalQuot_multSubagent` use; only the parenthetical strengthening to an
   isomorphism is wrong.

9. **Theorem 24 (§2.4), printed proof omits the reverse implication.** The statement
   is an *iff* (`C₀ ◁ C₁` iff there is a `C₂` with `C₀ ◁ₓ C₂ ◁₊ C₁`), but the proof
   (TeX L619–630) argues only the forward direction, constructing
   `C₂ = (Image(D), E₁, ·₂)` from `C₀ ◁ C₁`. The converse is never argued. It does
   follow from material the paper already has — Claim 23(1) turns `◁ₓ` and `◁₊` into
   `◁`, and Claim 16 chains them — and that is the route
   `Frame.subagent_iff_exists_multSubagent_addSubagent` takes; it proves both
   directions.

10. **Claim 38 (App. A), proof over-infers bijectivity.** From the single composite
    identity `g_ψ ∘ g_φ = id_A` the proof concludes "and `g_ψ`, `g_φ` are bijective"
    (TeX L849). That inference is invalid: one composite identity gives only
    injectivity of `g_φ` and surjectivity of `g_ψ`. The other homotopy of the
    equivalence, together with biextensionality of `D`, is what forces the reverse
    composite `g_φ ∘ g_ψ = id_B`. The Lean proof
    (`Frame.homotopyEquiv_iff_nonempty_iso_of_biextensional`) establishes both
    identities before invoking a two-sided-inverse criterion. Statement sound;
    printed proof incomplete, as in errata 1 and 4.

11. **Claims 44 and 52 (App. A/B), ill-typed displayed calculations.** Two transcription
    slips in otherwise-correct arguments. Claim 44's second display (TeX L1058–1069)
    writes `g₁(x · y) ⋆ z` at L1066, although `g₁`'s domain is `X × Y` while `x · y`
    lies in `B` — the intended line is `g₁(x, y) ⋆ z = g₁(g₀(b)) ⋆ z`. Claim 52's
    first display (TeX L1257–1262) writes `a · f` at L1261, although `f` lies in `D`'s
    environment `F` and `·` takes `C`'s environment `E`; the adjointness step is
    `g(a) ⋆ f = a · h(f)`. Both Lean proofs
    (`Frame.MultSubagentCurry.multSubagent`, `Frame.SubagentCovering.subagentCurry`)
    use the well-typed equations.
