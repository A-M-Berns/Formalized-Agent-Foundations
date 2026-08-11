# Formalization Knowledge — Cartesian Frames (arXiv:2109.10996)

Permanent, curated facts for fresh-context harness agents.  Read
`CartesianFrames/README.md`, `CartesianFrames.lean`, and the paper before adding
entries.  Scope of the formalization: **all 60 numbered nodes**, both appendices
(user ruling, 2026-08-11).

## Correspondence table

| Paper node | Lean declaration | Status |
|---|---|---|
| Definition 1 | `CartesianFrames.Frame`, `Frame.image` | defined |
| Definition 2 | `Frame.Hom`, `Frame.Hom.comp`, `Frame.instChuCategory` (named instance) | defined; category laws hold by `rfl` |
| Definition 3 | `Frame.Hom.IsIsomorphism`; bridge `nonempty_iso_iff_exists_isIsomorphism` to Mathlib `C ≅ D` | defined + bridged |
| Definition 4 | `Frame.Biextensional` | defined |
| Definition 5 | `Frame.agentSetoid`, `Frame.envSetoid` | defined |
| Definition 6 | `Frame.collapse` (+ internal `collapse_biextensional`) | defined |
| Definition 7 | `Frame.BiextEquiv`, scoped `≃ᵇ` | defined |
| Claim 8 | `Frame.nonempty_iso_of_eq`, `Frame.biextEquiv_of_nonempty_iso` | proved |
| Definition 9 | `Frame.dual`, `Frame.Hom.dual`, `Frame.dualFunctor` | defined; `(C*)* = C` is `rfl` |
| Definition 10 | `Frame.mapWorlds` (functor); footnote = `Frame.BiextEquiv.mapWorlds` | defined + footnote proved |
| Definition 11 | `Frame.curry` (functor) | defined |
| Definition 12 | `Frame.botOf`, `Frame.instBot` (`⊥`); `botOfUnivIsoBot` is the dd:eq-to-iso bridge | defined |
| Definition 13 | `Frame.Subagent`, scoped `◁` (primary) | defined |
| Definition 14 | `Frame.SubagentCurry` | defined |
| Claim 15 | `Frame.subagent_iff_subagentCurry` | proved |
| Claim 16 | `Frame.Subagent.trans` | proved |
| Claim 17 | `Frame.Subagent.refl`, `Frame.Subagent.of_biextEquiv` | proved |
| Definition 50 | `Frame.SubagentCovering` | defined |
| Claim 51 | `Frame.subagent_iff_subagentCovering` | proved |
| Claim 52 | `Frame.SubagentCovering.subagentCurry` | proved |
| Claim 53 | `Frame.SubagentCurry.subagent` | proved (see erratum) |
| Definition 36 | `Frame.Homotopic` (+ equivalence/congruence lemmas) | defined |
| Definition 37 | `Frame.HomotopyEquiv` | defined |
| Claim 38 | `Frame.homotopyEquiv_iff_nonempty_iso_of_biextensional` | proved |
| Claim 39 | `Frame.biextEquiv_iff_homotopyEquiv` | proved |
| Claim 40 | `Frame.biextEquiv_of_nonempty_iso` (shared with Claim 8) | proved |
| Definitions 10–35, 41–58, remaining Claims, Theorem 24 | — | not started |

Unnumbered but load-bearing: `Frame.Biextensional.nonempty_iso_collapse`
(`C.Biextensional → Nonempty (C ≅ C.collapse)` — the step the paper takes silently
whenever it replaces a biextensional frame by its collapse; use it, don't re-derive);
`Frame.homotopyEquiv_collapse` (`C ≃ Ĉ`, inside Claim 39's proof); `Frame.dual_dual`
(`(C*)* = C`, App. B prose near Claim 46).  `CartesianFrames/Examples.lean`
(namespace `CartesianFrames.Examples`) holds the paper's worked matrices as concrete
frames — `driver` (§2.1), `dedup`/`dup` (§2.2 duplicate-row pair), `row`/`col` — with
morphisms and 15 non-vacuity witnesses (homotopy/biextensional equivalence strictly
weaker than iso, `Homotopic` neither equality nor total, collapse genuinely deletes).
Reuse these for future non-vacuity or counterexample work.

## Design decisions (settled with Anson, 2026-08-11)

- `dd:universe`: all three carrier types of a frame live in one Lean universe.
- `dd:cat` (**user-decided**): all-in Mathlib category theory from `Basic.lean`.
  Rationale: the paper's own Definitions 9–11 say "the functor …" in the main body;
  a late categorical layer would leave two parallel spellings of composition.
  Consequence: Mathlib's `Functor`/`Iso`/`Limits` vocabulary is part of the trust
  surface.  Claim 46 will be an `Equivalence` (Mathlib has no strict isomorphism of
  categories) plus the strict `dual_dual : C.dual.dual = C`.
- `dd:eq-to-iso` (**user-decided**): where the paper asserts literal frame
  *equality* that the subtype/quotient encoding makes unstateable (Claim 35
  idempotence and kin), state the canonical *isomorphism* `≅` — the strongest
  expressible form — with a per-site disclosure.  Do **not** weaken such sites to
  biextensional equivalence; add `≃`-corollaries only as one-line consequences.
- Primary definitions: the paper's *first-presented* definition of each subagency
  relation owns the plain name/notation — categorical (Def 13) for `◁`, committing
  (Def 18) for `◁₊`, externalizing (Def 19) for `◁ₓ`.  The other seven definitions
  (14, 20, 21, 50, 54, 57, 58) are named variants with iff-theorems (Claims 15, 22,
  51–53, 55–56, 59–60).  Proofs may route through whichever variant is convenient.
- Subset-flavored operations (Defs 18, 28, 29) use `Set`/subtype rendering:
  `Commit` takes `B : Set C.Agent` and produces agent carrier `↥B`.
- Partitions (Defs 31–33) will be modeled as `Setoid`; the paper's `A/B` (choice
  functions selecting one element per cell) becomes
  `{q : Quotient s → A // ∀ c, ⟦q c⟧ = c}`.  Search Mathlib's partition API before
  writing this (`Setoid.IsPartition`, `Quotient.out`, …).
- The paper overloads `≃` for biextensional equivalence (main text) and homotopy
  equivalence (Appendix A), proving them equivalent only at Claim 39.  Keep two
  distinct Lean names; biextensional equivalence gets the notation; Claim 39 is the
  bridge.  Do not overload prematurely.
- Unnumbered load-bearing facts become named internal lemmas annotated to their
  surrounding definition: morphisms `C ⟶ ⊥` biject with `C.Env` (used by Claims 51,
  53, 55), and `p°` preserves biextensional equivalence (Def 10's footnote).

## Paper errata (details in `notes/cartesian-frames-paper-errata.md`)

- **Claim 53's printed proof has a gap**: its final display checks only agent
  components of `φ_e = φ_e ∘ τ ∘ σ`; the env components agree only up to duplicate
  columns, while Definition 13 demands morphism equality.  The Lean proof of
  `SubagentCurry.subagent` uses the env-redirect construction from the paper's
  commented-out currying→covering proof (TeX L1334–1377).  The claim is true as
  stated — auditors comparing the Lean proof against the printed proof should
  expect this divergence; the *statement* is verbatim.
- Claim 35 has a binder garble and an ill-typed External/Internal half (below).

## Deferred interpretation question (do not resolve unilaterally)

**Claim 35 is partially ill-typed in the paper's own set theory.**  `Commit`/`Assume`
idempotence is fine (`B ⊆ B`).  But `External^B(C)` has agent `A/B`, and `B` is a
partition of `A`, not of `A/B`, so `External^B(External^B(C))` is not well-formed as
written; likewise `Internal`.  The claim's binder line also garbles indices
(`Assume^B` with `B ⊆ A`; `External^F` with `F` a partition of `E`, contradicting
Definition 32).  Plan of record: before Stage 4, consult the original AI Alignment
Forum sequence (Garrabrant 2020, paper footnote 1) for the intended statement,
propose a reading, and **escalate to Anson** as a concrete decision + paper-errata
note.  Auditors: flag any formalization of Claim 35's External/Internal half that
was not preceded by that ruling.

## Surface conventions (post round 1 — enforced fail-closed by the checker)

- The literal string used for paper-node annotations is a **reserved string** in this
  library: every occurrence must be the last non-blank line of a `/-- … -/`
  docstring, attached to a *named* declaration, and that declaration must be listed
  in `AxiomAudit.lean`'s CF-INVENTORY (per-declaration coverage — sharing a node
  with a listed declaration is not enough).  It may not appear in prose anywhere
  under `CartesianFrames/` (not in `/-!` blocks, not in comments) — write
  "paper-node line" instead.  Internal lemmas cite nodes in prose without the marker.
- `scripts/lint_paper_labels.py` is library-sensitive: a CF `theorem` must name a
  numbered Claim or Theorem on one line; the LI alternatives (`thm:`/`§`/`App.`) are
  rejected for `CartesianFrames/`.  A `theorem` citing only a Definition also fails,
  by design.
- `scripts/check_trust_surface.py` hashes `AxiomAudit.lean`, so any CF-INVENTORY
  edit makes it report stale even though the page is LI-only.  Regenerate
  (`python3 scripts/gen-trust-surface.py`) LAST, after all AxiomAudit edits.

## Pitfalls

- A frame morphism's environment map reverses direction.  Consequently
  `(f ≫ g).env = f.env ∘ g.env`.
- Definition 10's TeX names the mapped carriers `B` and `F`, but the intended functor
  leaves the agent and environment carriers unchanged; only outcomes are mapped by
  `p`.
- Category laws and `dual_dual` hold by `rfl` (definitional eta for structures and
  functions).  Prefer `rfl` before reaching for `ext` in this layer.
- `≃ᵇ` is `infixl:25` (matching Mathlib's `≃`; keep it): it binds looser than `∧`
  (35) and `¬` (40), so parenthesize — `(C ≃ᵇ D) ∧ P`, `¬ (C ≃ᵇ D)`.  It is scoped
  inside `CartesianFrames.Frame`; `open CartesianFrames` alone gives
  "expected token" — clients need `open Frame` or `open scoped CartesianFrames.Frame`.
- Concrete `Frame` witnesses must be `abbrev`, not `def`, or `decide`/instance
  search cannot see the carriers.  `![…]` needs `Mathlib.Data.Fin.VecNotation`;
  deciding over an empty hom-type needs `Mathlib.Data.Fintype.Pi`.
  `Frame.Biextensional`'s fields use strict-implicit binders, so the anonymous
  constructor `⟨fun _ => rfl, …⟩` fails; use `constructor <;> intros`.
- On a biextensional frame, `Homotopic f g → f = g` — homotopy is a genuine
  weakening only on non-biextensional frames (`env_ext` also forces
  `φ.env ∘ ψ.env = id`).  Any strictness witness must live on a frame with
  duplicates (`Examples.dupLoop`); no Claim-38 forward witness with `φ ≫ ψ ≠ 𝟙`
  exists on biextensional frames — do not hunt for one.
- `Homotopic f g ↔ ∀ a e, D.outcome (f.agent a) e = D.outcome (g.agent a) e`
  (pointwise `agentSetoid`-relatedness of the agent maps); Definition 36's
  asymmetric phrasing is provably symmetric on bundled morphisms.
- Boundary facts (checked): empty-`Agent` frame is biextensional iff its `Env` is a
  subsingleton; over `W = Unit` a biextensional frame has ≤1 agent and ≤1 env;
  `Frame W` is inhabited for every `W` (empty carriers), so no endpoint is vacuous
  merely from `W`'s emptiness.
- Build calibration (2026-08-11, this machine): seeding a worktree from the
  integration `.lake` ≈ 100 s; incremental full `lake build` after touching
  CartesianFrames + AxiomAudit ≈ 8–12 min (AxiomAudit alone ~2 min).  Budget one
  background build, not several.

## Cleared suspicions (round 1 — do not re-raise without new evidence)

- Mathlib has no Chu construction at the current pin; `Frame`/`Hom`/the category
  instance duplicate nothing.  Re-check only on a pin move.
- Definition 3's bijective-components condition coincides with Mathlib's `C ≅ D`
  (inverse pair automatically satisfies adjointness); nothing hidden in stating
  claims with `Nonempty (C ≅ D)`.
- Claim 38's biextensionality hypotheses are load-bearing and satisfiable
  (both directions falsifiable if either is dropped); Claim 8's second half is a
  strict implication.  Witnesses live in `Examples.lean`.
- `Homotopic` orientation, `HomotopyEquiv`'s `≫`-order, `collapse`'s
  `Quotient.lift₂` binder order (positional, misleadingly named — do not "fix"
  without re-checking), and `dual`-as-transpose were each hand-verified in round 1.
