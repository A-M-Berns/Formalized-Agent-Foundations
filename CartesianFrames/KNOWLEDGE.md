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
| Definition 18 | `Frame.AddSubagent`, scoped `◁₊` (primary) | defined |
| Definition 19 | `Frame.MultSubagent`, scoped `◁ₓ` (primary) | defined |
| Definition 20 | `Frame.AddSubagentCurry` | defined |
| Definition 21 | `Frame.MultSubagentCurry` | defined |
| Claim 22 | `Frame.addSubagent_iff_addSubagentCurry`, `Frame.multSubagent_iff_multSubagentCurry` | proved |
| Claim 23 | `{Add,Mult}Subagent.{subagent, congr, refl, trans}` | proved |
| Theorem 24 | `Frame.subagent_iff_exists_multSubagent_addSubagent` | proved |
| Claims 41–44 | `AddSubagent.addSubagentCurry`, `AddSubagentCurry.addSubagent`, `MultSubagent.multSubagentCurry`, `MultSubagentCurry.multSubagent` | proved (43: see erratum) |
| Definition 36 | `Frame.Homotopic` (+ equivalence/congruence lemmas) | defined |
| Definition 37 | `Frame.HomotopyEquiv` | defined |
| Claim 38 | `Frame.homotopyEquiv_iff_nonempty_iso_of_biextensional` | proved |
| Claim 39 | `Frame.biextEquiv_iff_homotopyEquiv` | proved |
| Claim 40 | `Frame.biextEquiv_of_nonempty_iso` (shared with Claim 8) | proved |
| Definition 25 | `Frame.SubEnv` (`◁*`) | defined |
| Definition 26 | `Frame.AddSubEnv` (`◁*₊`), `Frame.MultSubEnv` (`◁*ₓ`) | defined |
| Claim 27 | `Frame.multSubagent_iff_multSubEnv` | proved |
| Definitions 28–29 | `Frame.commit`/`commitCompl`, `Frame.assume`/`assumeCompl` | defined |
| Claim 30 | `Frame.{commit,commitCompl}_addSubagent`, `Frame.addSubEnv_{assume,assumeCompl}` | proved |
| Definition 31 | `Frame.partitionSections` (no Mathlib counterpart at this pin) | defined |
| Definitions 32–33 | `Frame.external`/`externalQuot`, `Frame.internal`/`internalSect` | defined |
| Claim 34 / Claim 45 | `Frame.{external,externalQuot}_multSubagent`, `Frame.multSubagent_{internal,internalSect}` | proved |
| Claim 35 (Commit/Assume half only, by ruling) | `Frame.commit_commit_self` + 3 kin (iso-valued `def`s, dd:eq-to-iso) | proved |
| Claim 46 | `Frame.dualFunctor_isEquivalence` + strict `Frame.dualEquivalence_functor_comp_inverse`/`_inverse_comp_functor` (both `rfl`; carrier `Frame.dualEquivalence`) | proved — concession purely nominal |
| Definition 47 | `Frame.instZero`, `Frame.instTop` | defined |
| Claim 48 | `Frame.nonempty_isInitial_zero`/`_isTerminal_top` (carriers `zeroIsInitial`/`topIsTerminal`) | proved |
| Definition 49 | `Frame.oneOf`, `Frame.instOne` (`(⊥_S)* = 1_S` is `rfl`) | defined |
| Definition 54 | `Frame.AddSubagentCategorical` | defined |
| Claims 55–56 | `Frame.AddSubagentCategorical.addSubagent`, `Frame.AddSubagent.addSubagentCategorical` (+ iff package) | proved |
| Definition 57 | `Frame.MultSubagentCategorical` | defined |
| Definition 58 | `Frame.MultSubagentSubEnv` | defined |
| Claim 59 | `Frame.multSubagentCategorical_iff_multSubagentSubEnv` | proved |
| Claim 60 | `Frame.multSubagentSubEnv_iff_multSubagent` | proved |

**All 60 numbered nodes of the paper now have Lean carriers** (Claim 35's
External/Internal half excluded by ruling; see intentional deviations).

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

## Stage 3b internal lemmas (private in `AdditiveMultiplicative.lean` — promote, don't re-derive)

`nonempty_agent_of_biextEquiv` / `nonempty_env_of_biextEquiv` (carrier nonemptiness
transports across `≃ᵇ`); `biextEquiv_botOf_image` (`[Unique M.Env] → M ≃ᵇ botOf
M.image`); `biextEquiv_curry_transport` (`D°(Z) ≃ᵇ D'°(σ°(Z))` from a homotopy
pair; `mapWorlds` keeps the env carrier so `Unique` survives); `curryCurryIso`
(`(E°(M))°(N) ≅ E°(N∘M)`, all fields `rfl`); `exists_image_univ_curry`
(class-hitting image patched to literally-full image without disturbing `E°(N)` up
to `≃ᵇ`).  Consequence worth remembering: **`◁ₓ`-transitivity does NOT need App. B's
Claim 60** — do not re-sequence it on that account.  Defeq-first rule extends to
`curry`/`mapWorlds` composites: in Theorem 24 `C₂.curry.obj M` is *literally*
`C₁.curry.obj D`; try `rfl`/plain hypothesis reuse before building an iso.

## Paper errata (details in `notes/cartesian-frames-paper-errata.md`)

- **Claim 53's printed proof has a gap**: its final display checks only agent
  components of `φ_e = φ_e ∘ τ ∘ σ`; the env components agree only up to duplicate
  columns, while Definition 13 demands morphism equality.  The Lean proof of
  `SubagentCurry.subagent` uses the env-redirect construction from the paper's
  commented-out currying→covering proof (TeX L1334–1377).  The claim is true as
  stated — auditors comparing the Lean proof against the printed proof should
  expect this divergence; the *statement* is verbatim.
- Claim 35 has a binder garble and an ill-typed External/Internal half (below).

## Intentional deviations (user-ruled)

**Claim 35, External/Internal half: not formalized (Anson, 2026-08-11).**  The
half is ill-typed in the paper's own set theory: `External^B(C)` has agent `A/B`,
and `B` is a partition of `A`, not of `A/B`, so `External^B(External^B(C))` is not
well-formed as written; likewise `Internal`.  The claim's binder line also garbles
indices (`Assume^B` with `B ⊆ A`; `External^F` with `F` a partition of `E`,
contradicting Definition 32).  Ruling: record as a paper erratum
(`notes/cartesian-frames-paper-errata.md` #3) and formalize **only the
Commit/Assume half** of Claim 35 (at canonical-iso strength per `dd:eq-to-iso`).
The External/Internal half stays unformalized; its idempotence-theorem carriers do
not exist and must not be invented.  Consequence for the surface accounting:
Claim 35 is *partially* formalized by design — its `Paper node:` annotation sits
only on the Commit/Assume idempotence theorems, and the README discloses the
partial status.  Auditors: do not raise the missing External/Internal half as a
gap; do flag any attempt to formalize it without a new user ruling.

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
  The trap bites *inside definition bodies* too, and the downstream errors look
  nothing like a precedence problem (`Iso.mk has 4 explicit fields…`, bogus
  projection errors) — it cost Stage 3b an elaboration round.
- Mathlib (current pin) has no `Unique (α × β)` instance (`Inhabited` and
  `Subsingleton` products exist); build it with `Unique.mk' _`, as a `def` (it's
  `Type`-valued) marked `@[reducible]`/`abbrev`.
- `Set.eq_univ_of_forall`/`_iff_forall` need `import Mathlib.Data.Set.Basic` — the
  CF import chain reaches `Set` only via `CategoryTheory.Opposites`.
- Seeded `.lake` oleans can be stale relative to the worktree's HEAD, presenting as
  a *missing name* (`Unknown constant` for a declaration that exists), not a type
  error.  Rebuild the upstream module (`lake build CartesianFrames.<Mod>`) before
  believing `lake env lean`.
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

## Stage 4 + round 2 lessons

- **`lake build -j4` does not exist on this toolchain** (Lake 5.0.0/Lean 4.31.0)
  and the flag error **exits 0 through a pipe** — a one-line log is the only tell.
  Use `LEAN_NUM_THREADS=4 lake build`; always confirm the log ends in
  "Build completed successfully".
- **AxiomAudit imports CF modules individually**, not the root: a new CF module
  needs BOTH the root import and an `AxiomAudit.lean` import line, else the audit
  build fails late with a misleading `Unknown constant`.
- **`dd:eq-to-iso` sites are `def`s**: `X ≅ Y` is Type-valued, so `theorem` is an
  elaboration error; do not weaken to `Nonempty (≅)` (forgets which iso).  Same
  for Claim 48's `IsInitial`/`IsTerminal` carriers (theorems state `Nonempty _`,
  defs carry the data).
- **`lint_paper_labels.py` requires a docstring ending `-/` immediately before
  every `theorem`** — no shared docstrings across consecutive theorems.
- **Claim 46 is strict**: both dual composites are definitionally `𝟭` (`rfl`);
  `Functor.comp`/`Functor.id` have lambda fields with defeq bodies + proof fields.
  No `eqToIso`/`aesop_cat`/op-unop plumbing needed anywhere in the equivalence.
- **`Homotopic`'s useful direction is almost always `.symm`** (env-side rewrite
  `C.outcome a ((α≫β).env e) = C.outcome a e`); the un-symmed form gives the
  agent-side fact, true but useless for the App. B calc chains.  Dualizing a
  homotopy pair also needs `.symm` plus swapped argument order.
- **Definition 32/33 duals pair STRAIGHT**: `(C.internal s).dual = C.dual.external s`
  and `(C.internalSect s).dual = C.dual.externalQuot s`, on the nose; likewise
  `(C.assume F).dual = C.dual.commit F`.  The "crossed" intuition is wrong because
  dual swaps carriers.
- Claim 45's externalizing proofs need only per-`a` sections (`sec a ⟦a⟧ = a`,
  classical `if`); keep them inside an `∃`-lemma to avoid a noncomputable def.
- Concrete-witness toolbox (round 2, code in
  `.harness/audit/round2-lensC-probe.lean`): `decide` can't see through
  `Frame.image` (insert `show ∃ a e, …` first); product-`Env` frames need
  `Mathlib.Data.Fintype.Prod`; subtype-agent `decide` recipe (re-`have` the
  membership, `show` on the underlying `Fin`, revert, decide); prove `≃ᵇ`
  obligations via `biextEquiv_iff_homotopyEquiv`, not `Iso`.
- `AddSubagent`'s binder order is `Y Z X f` (superset first) — destructuring in
  the paper's `X Y Z` order silently misbinds.
- **Name collision**: `CartesianFrames.Frame` vs Mathlib's `Order.Frame` — with
  both open Lean can silently pick `Order.Frame` when the expected type
  disambiguates.  Qualify in client-facing docs.
- `⊥` is a maximum for `◁` (`C ◁ ⊥` always) and `IsEmpty C.Env → C ◁ D` —
  faithful to the paper; subagency witnesses need nonempty `Env` and non-`⊥` RHS.
- THREE reusable `≃ᵇ`-invariants now LIVE in Biextensional.lean:
  `image_eq_of_biextEquiv`, `exists_env_injective_of_biextEquiv`, and (since round
  3) `BiextEquiv.dual`.  Do not re-derive the one-sided subset form (internal).
- Examples.lean's second half (round-2 fix) covers §2.4: `driver3`/`committed`/
  `driver3Commit`, the paper's team example (`teamD`/`teamZ`/`teamC`), and
  `bigD`/`bigZ`/`bigC`, with witnesses for non-totality, both refinements
  non-degenerate on the paper's own examples, orientation guards both directions,
  strictness of `◁₊`/`◁ₓ` below `◁`, and Theorem-24 content
  (`every_witness_nontrivial`, non-vacuous via `bigC_decomposes`).  Reuse before
  building new counterexample frames.
- Concrete witnesses over the OPERATIONS must not use `C.commit B` etc. directly:
  they are `def`s, so instance search can't find `Fintype` on their carriers and
  `decide` fails.  Write the frame as a literal `abbrev` and pin the identity with
  a checked `example : lit = C.commit B := rfl` (Examples.lean does this; its
  import moved to CartesianFrames.Operations as a result — Examples is now the
  leaf of the whole CF chain).
- `Homotopic`-`.symm` clarification: `.symm` means `Homotopic.symm` (swaps which
  argument supplies env vs agent map) — `Eq.symm` on the applied equation is a
  DIFFERENT statement and won't typecheck against env-side goals.
- Stale-olean trap, edit-time form: after editing an upstream CF module, `lake env
  lean <downstream>` reports newly added upstream declarations as `Unknown
  identifier` and `obtain` fails with a bogus "not an inductive datatype".
  Rebuild the changed chain (`lake build CartesianFrames.<Mod>`, ~20 s) first.
- The Type-u WLOG docstring in AdditiveMultiplicative.lean is now the corrected
  honest version (additive certified by Claims 41/42; multiplicative by the
  unformalized collapse/cardinality argument).  Do not re-assert "WLOG by Claims
  41–44" — that exact sentence was findings R2-F02/F07.

## Round 3 additions

- Examples.lean's third block ("Operation and Appendix-B witnesses"): `ext_genuine`
  (external on a 2-cell partition of bigD is a genuine non-reflexive `◁ₓ`),
  `driver3Assume` + `◁*₊` witness, `colDup`/`phi0` (smallest frame with nontrivial
  endomorphism monoid; Def 54's homotopy relaxation load-bearing —
  `phi0_no_exact_factorization` vs `cat54_holds`), App B relation instances and
  non-totality examples, dualized Def 25/26 examples.  Second dd:eq-to-iso bridge:
  `oneOfUnivIsoOne` (Def 49).  Claim 35's `= Set.univ` absorption is disclosed at
  the sites AND pinned by four checked `example`s.
- `Nonempty (partitionSections s)` in general is a KNOWN GAP as public surface (the
  probe's one-liner exists only as a private specialized def in Examples); if
  needed, it belongs beside `partitionSections` in Operations.lean.
- Gate-script traps: `check_trust_surface.py` exits 0 even on FAIL — read its
  output line, never its exit status (same class as the `lake build -j4` trap).
  The CF-INVENTORY preamble's unannotated-groups enumeration has no script check —
  recount it in the same edit as any inventory change.
- Build calibration correction: documentation/witness-sized CF rounds rebuild the
  whole chain in ~2 min total; only cold or Mathlib-touching builds need the long
  budget.
- Paper erratum 7 (Def 54 "unique" is loose prose; literal reading falsifies
  Claim 56 — compiled falsifier `two_distinct_endos`).

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
