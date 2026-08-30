# Formalization Knowledge — Cartesian Frames (arXiv:2109.10996)

Permanent, curated facts for anyone picking this library up cold.  Read
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

Three unnumbered facts carry weight the paper never states outright:
`Frame.Biextensional.nonempty_iso_collapse` (`C.Biextensional → Nonempty (C ≅ C.collapse)`
— the step the paper takes silently whenever it replaces a biextensional frame by its
collapse), `Frame.homotopyEquiv_collapse` (`C ≃ Ĉ`, inside Claim 39's proof), and
`Frame.dual_dual` (`(C*)* = C`, Appendix B prose near Claim 46).  The concrete frames
and separation witnesses live in `CartesianFrames/Examples.lean`; see *The witness
library* below.

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
## Intentional deviations (user-ruled)

**Claim 35, External/Internal half: not formalized (Anson, 2026-08-11).**  The
half is ill-typed in the paper's own set theory: `External^B(C)` has agent `A/B`,
and `B` is a partition of `A`, not of `A/B`, so `External^B(External^B(C))` is not
well-formed as written; likewise `Internal`.  The claim's binder line also garbles
indices (`Assume^B` with `B ⊆ A`; `External^F` with `F` a partition of `E`,
contradicting Definition 32).  Ruling: record as a paper erratum
(`notes/paper-errata.md` #3) and formalize **only the
Commit/Assume half** of Claim 35 (at canonical-iso strength per `dd:eq-to-iso`).
The External/Internal half stays unformalized; its idempotence-theorem carriers do
not exist and must not be invented.  Consequence for the surface accounting:
Claim 35 is *partially* formalized by design — its `Paper node:` annotation sits
only on the Commit/Assume idempotence theorems, and the README discloses the
partial status.  Auditors: do not raise the missing External/Internal half as a
gap; do flag any attempt to formalize it without a new user ruling.

## Paper errata (details in `notes/paper-errata.md`)

- **Claim 53's printed proof has a gap**: its final display checks only agent
  components of `φ_e = φ_e ∘ τ ∘ σ`; the env components agree only up to duplicate
  columns, while Definition 13 demands morphism equality.  The Lean proof of
  `SubagentCurry.subagent` uses the env-redirect construction from the paper's
  commented-out currying→covering proof (TeX L1334–1377).  The claim is true as
  stated — auditors comparing the Lean proof against the printed proof should
  expect this divergence; the *statement* is verbatim.
- Claim 35 has a binder garble and an ill-typed External/Internal half (below).

## Reusable internal API — check here before deriving anything

Private in `AdditiveMultiplicative.lean` (promote rather than re-derive):
`nonempty_agent_of_biextEquiv` / `nonempty_env_of_biextEquiv` (carrier nonemptiness
transports across `≃ᵇ`); `biextEquiv_botOf_image` (`[Unique M.Env] → M ≃ᵇ botOf
M.image`); `biextEquiv_curry_transport` (`D°(Z) ≃ᵇ D'°(σ°(Z))` from a homotopy pair —
`mapWorlds` keeps the env carrier, so `Unique` survives); `curryCurryIso`
(`(E°(M))°(N) ≅ E°(N∘M)`, all fields `rfl`); `exists_image_univ_curry` (a
class-hitting image patched to a literally-full one without disturbing `E°(N)` up to
`≃ᵇ`).  A consequence worth keeping: **`◁ₓ`-transitivity does not need Appendix B's
Claim 60** — do not re-sequence Claim 60 on its account.

Public in `Biextensional.lean`, three invariants of `≃ᵇ` — the standard refuters when
you need to show a subagency relation *fails*: `image_eq_of_biextEquiv`,
`exists_env_injective_of_biextEquiv` (note the biextensionality hypothesis is on the
frame whose `Env` is the injection's *source*), and `BiextEquiv.dual`.  Do not
re-derive the one-sided image-subset form; it is internal to the equality's proof.

Public in `Operations.lean` for Definition 31: `partitionSectionsOut` (the canonical
`Quotient.out` section) and the `Nonempty (partitionSections s)` instance, so every
`Setoid` visibly admits a section.  These do **not** subsume the private
`exists_partitionSections_selecting`, which selects a *given* element from its own
cell — that is what the Claim 34/45 proofs need.

Defeq-first rule: this library is unusually rich in definitional equalities.  Category
laws, `dual_dual`, `Hom.dual_dual`, both Claim 46 composites, `(C.internal s).dual =
C.dual.external s`, `(C.assume F).dual = C.dual.commit F`, and Theorem 24's
`C₂.curry.obj M = C₁.curry.obj D` are all `rfl`.  Try `rfl` and plain hypothesis reuse
before constructing an isomorphism.

## The witness library (`Examples.lean`)

Concrete frames carrying every non-vacuity and separation fact, so that no endpoint
rests on an uninhabited or degenerate hypothesis.  Reuse these before building new
counterexample frames.

- §2.1–2.2, the paper's own matrices: `driver`; the duplicate-row pair `dedup`/`dup`
  with `dupLoop`; `row`/`col`.  They witness that biextensional and homotopy
  equivalence are *strictly* weaker than isomorphism, that `Homotopic` is neither
  equality nor the total relation, and that the collapse genuinely deletes.
- §2.4 subagency: `driver3` with `committed`/`driver3Commit` (the paper's committing
  example), the team example `teamD`/`teamZ`/`teamC`, and `bigD`/`bigZ`/`bigC`.  They
  witness non-totality, both refinements non-degenerately on the paper's own
  examples, orientation in *both* directions, strictness of `◁₊`/`◁ₓ` below `◁`, and
  Theorem 24's decomposition content (`every_witness_nontrivial`, whose antecedent
  `bigC_decomposes` exhibits).
- Operations and Appendix B: `bigDCells` (a genuine 2-cell partition) with
  `externalBigD_multSubagent_not_biextEquiv`; `assumedEnvs`/`driver3Assume`;
  `colDup` with `colDupLoop` — the smallest frame here with a non-trivial
  endomorphism monoid — and `oneCol` with `colDupToOneCol`.

**The Definition 54 separator is the subtle one.**  A per-`φ₀` non-factorization fact
never separates an `∃ φ₀`-quantified relation: `φ₀ = 𝟙` factors every `φ` exactly, so
the exactified variant of Definition 54 holds trivially wherever `C ◁₊ C` does.  That
error stood in this file and in the errata for three audit rounds before a
fresh-context audit caught it.  The real separation is
`colDup_addSubagentCategorical_oneCol` against `not_exact_factorization_colDup_oneCol`:
the target's single environment state pins the composite while `colDup`'s duplicate
columns keep the homotopy condition satisfiable.  `colDupLoop_no_exact_factorization`
is the per-`φ₀` fact and does **not** establish the relation-level claim.

## Surface conventions — enforced fail-closed by the checker

- The literal string used for paper-node annotations is a **reserved string** in this
  library: every occurrence must be the last non-blank line of a `/-- … -/`
  docstring, attached to a *named* declaration, and that declaration must itself be
  listed in `AxiomAudit.lean`'s CF-INVENTORY (per-declaration coverage — sharing a
  node with a listed declaration is not enough).  It may not appear in prose anywhere
  under `CartesianFrames/`, not in `/-!` blocks and not in comments; write
  "paper-node line" instead.  Internal lemmas cite nodes in prose, without the marker.
- `theorem` is reserved for numbered paper claims and theorems; `lint_paper_labels.py`
  additionally requires a CF `theorem` to name a numbered Claim or Theorem on one
  line, and rejects the LogicalInduction alternatives (`thm:`/`§`/`App.`).  A
  `theorem` citing only a Definition fails by design.
- **Data-valued endpoints are `def`s, not `theorem`s.**  `X ≅ Y` is `Type`-valued, so
  the `dd:eq-to-iso` sites and Claim 48's `IsInitial`/`IsTerminal` carriers are `def`s
  (the theorems beside them state `Nonempty _`).  Do not weaken an iso to
  `Nonempty (≅)` to make it a `theorem` — that forgets *which* isomorphism.
- `#assert_axioms_clean` permits the three standard axioms, so `Quotient.out`-based
  noncomputable definitions are inventoriable; do not avoid choice on cleanliness
  grounds.
- The CF-INVENTORY preamble enumerates the listed names that carry no annotation of
  their own.  **No script checks that count** — recount it by hand in the same edit as
  any inventory change.

## Pitfalls

### Notation and elaboration

- A frame morphism's environment map reverses direction: `(f ≫ g).env = f.env ∘ g.env`.
- `≃ᵇ` is `infixl:25` (matching Mathlib's `≃`; keep it), so it binds looser than `∧`
  (35) and `¬` (40) — parenthesize as `(C ≃ᵇ D) ∧ P`, `¬ (C ≃ᵇ D)`.  The trap bites
  *inside definition bodies* too, where the resulting errors look nothing like a
  precedence problem (`Iso.mk has 4 explicit fields…`, bogus projection errors).
- `≃ᵇ` and `◁` are scoped in `CartesianFrames.Frame`: `open CartesianFrames` alone
  yields "expected token".  Clients need `open Frame` or
  `open scoped CartesianFrames.Frame`.
- **Name collision**: `CartesianFrames.Frame` vs Mathlib's `Order.Frame`.  With both
  open, Lean can *silently* choose `Order.Frame` when the expected type disambiguates.
  Qualify in client-facing docs.
- `Homotopic f g` unfolds with the env map from `g` and the agent map from `f`, so the
  useful direction is almost always `Homotopic.symm` — which is *not* `Eq.symm` on the
  applied equation, a different statement that will not typecheck against env-side
  goals.  Dualizing a homotopy pair needs `.symm` plus swapped argument order.
- `Frame.Biextensional`'s fields use strict-implicit binders, so the anonymous
  constructor `⟨fun _ => rfl, …⟩` fails; use `constructor <;> intros`.
- A `Type`-valued `example` needs `noncomputable` just as a `def` does.  To exercise a
  noncomputable endpoint, state a `Prop` about it instead.
- Mathlib at this pin has no `Unique (α × β)` instance (`Inhabited` and `Subsingleton`
  products exist); build one with `Unique.mk' _`, as a `def` (it is `Type`-valued)
  marked `@[reducible]`/`abbrev`.

### Concrete witnesses

- Concrete `Frame` witnesses must be `abbrev`, not `def`, or `decide` and instance
  search cannot see through to the carriers.  For the same reason a witness over an
  *operation* must not be written `C.commit B` (the operations are `def`s): write the
  frame literally and pin the identity with a checked `example : lit = C.commit B := rfl`.
- `decide` cannot see through `Frame.image`; insert `show ∃ a e, …` first.  Deciding
  over an empty hom-type needs `Mathlib.Data.Fintype.Pi`; product-`Env` frames need
  `Mathlib.Data.Fintype.Prod`; `![…]` needs `Mathlib.Data.Fin.VecNotation`;
  `Set.eq_univ_of_forall` needs `Mathlib.Data.Set.Basic`.
- `decide` refuses a goal mentioning a local free variable — hoist the fact into a
  `∀`-quantified `have` first.  When the carrier is `Fin 1`, `Subsingleton.elim`
  sidesteps the issue entirely and reads better.
- Subtype-agent goals: re-`have` the membership, `show` the goal on the underlying
  `Fin`, then revert and decide.  Prove `≃ᵇ` obligations through
  `biextEquiv_iff_homotopyEquiv`, never by building an `Iso` (which would force
  subtype-level coherence proofs).
- `AddSubagent`'s binder order is `Y Z X f` — superset first.  Destructuring in the
  paper's `X Y Z` reading order silently misbinds.

### Mathematical gotchas

- On a biextensional frame, `Homotopic f g → f = g`, since `env_ext` also forces
  `φ.env ∘ ψ.env = id`.  Homotopy is a genuine weakening only on frames with
  duplicates — do not hunt for a Claim-38 forward witness with `φ ≫ ψ ≠ 𝟙` on
  biextensional frames.
- `⊥` is a maximum for `◁` (`C ◁ ⊥` always), and `IsEmpty C.Env → C ◁ D` for every
  `D`.  Both are faithful to the paper, but any intended non-vacuity witness must
  therefore have a nonempty `Env` and a right-hand side other than `⊥`.
- Empty-`Agent` frames are biextensional iff their `Env` is a subsingleton; over
  `W = Unit` a biextensional frame has at most one agent and one env; `Frame W` is
  inhabited for every `W`.  So no endpoint is vacuous merely from `W` being empty.
- Definition 32/33 duals pair **straight**, not crossed:
  `(C.internal s).dual = C.dual.external s`.  The crossed intuition fails because
  dualizing swaps the carriers.
- Claim 45's externalizing proofs need only a per-`a` section (`sec a ⟦a⟧ = a`,
  classical `if`); keep it inside an `∃`-lemma to avoid a noncomputable definition.
- The `Type u` bound on Definitions 18/19's set existentials is WLOG, but only the
  *additive* half is certified in-library (by Claims 41/42, whose witnesses are `D`'s
  own carriers).  The multiplicative half holds by an unformalized argument, two
  routes: (a) quotient the carriers by outcome-equivalence in the order `X`, `Z`, `Y`
  (quotienting `Y` first does *not* give a `u`-small type: `Y/~` embeds into
  `X × Z → W`, small only once `X`, `Z` have been replaced by `X/~ ↪ Agent(Ĉ)` and
  `Z/~ ↪ Env(D̂)`); or (b) large-`◁ₓ` ⟹ `C ◁ D ∧ C ◁* D` (both size-free) ⟹ Lean's
  Claim 60 forward direction ⟹ `u`-small `◁ₓ`, since that direction's witnesses are
  `C.Agent`, `C ⟶ D`, `D.Env`.  `exists_image_univ_curry` plays no role in either (an
  earlier note said it did).  Do not re-assert "WLOG by Claims 41–44"; that sentence was
  an audit finding.

### Toolchain

- **Gate scripts and builds lie about their exit status.**  `lake build -j4` does not
  exist on this toolchain and its flag error exits 0; a `lake build` piped through
  `tee`/`tail` reports the *pipe's* status, so a failed build can look green; and
  `check_trust_surface.py` exits 0 even when it prints FAIL.  Read the output — a
  build is green only when its log ends "Build completed successfully".  Use
  `LEAN_NUM_THREADS=n lake build` to cap parallelism.
- `AxiomAudit.lean` imports the CF modules individually, not the root: a new module
  needs both the root import and an `AxiomAudit.lean` import line, or the audit build
  fails late with a misleading `Unknown constant`.
- Seeded `.lake` oleans go stale relative to an edited source and present as a
  *missing name* (`Unknown identifier`/`Unknown constant` for a declaration that
  plainly exists), with `obtain` then failing with a bogus "not an inductive
  datatype".  Rebuild the edited module before believing `lake env lean`.
- `check_trust_surface.py` hashes `AxiomAudit.lean`, so any inventory edit makes it
  report stale even though the generated page is LogicalInduction-only.  Regenerate
  **last**, after every inventory edit is final.
- Build calibration on this machine: seeding a worktree's `.lake` from the integration
  checkout is 40–100 s, and a full incremental `lake build` after touching several CF
  modules plus `AxiomAudit` is 2–3 minutes.  Budget the long estimate only for cold or
  Mathlib-touching builds.
- Style: `awk 'length > 100'` counts *bytes*, so it over-reports line length by 30–50%
  on this library's notation-dense files.  Measure with Python's `len` on decoded text.

## Cleared suspicions — do not re-raise without new evidence

- Mathlib has no Chu-space construction at this pin, so `Frame`, `Hom`, and the
  category instance duplicate nothing; there is likewise no bundled
  section-of-a-quotient type, so `partitionSections` is not a duplicate.  Re-check
  only on a pin move.
- Definition 3's bijective-components condition really does coincide with Mathlib's
  `C ≅ D`: the inverse pair automatically satisfies adjointness.  Nothing is hidden by
  stating the claims with `Nonempty (C ≅ D)`.
- Claim 38's biextensionality hypotheses are load-bearing and satisfiable — the `iff`
  fails if either is dropped — and Claim 8's second half is a strict implication.
- `Homotopic`'s orientation, `HomotopyEquiv`'s `≫`-order, `collapse`'s `Quotient.lift₂`
  binder order (positional, and misleadingly named — do not "fix" it without
  re-checking), and `dual`-as-transpose were each verified by hand.
- Modeling Definition 31's partitions as `Setoid` is *safer* than a `Set (Set α)`
  rendering, not merely more convenient: a set-theoretic partition containing an empty
  cell would make `A/B` empty and falsify Claim 34.  `Setoid` cells are automatically
  nonempty.
- `AddSubagentCurry` uses `Unique M.Env`, not `Subsingleton` — the latter would admit
  an empty environment and trivialize `◁₊`.
- Claim 43's empty-`Agent(D)` branch is honest: `IsEmpty (X × Y)` is *derived* from the
  hypothesis, not assumed, and `M.image = Set.univ` holds because the target is empty.
- The subagency relations' orientation was checked in both directions on both of the
  paper's worked examples: a reversed definition would still be inhabited, so
  inhabitation alone proves nothing.
