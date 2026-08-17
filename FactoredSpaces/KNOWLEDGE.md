# Formalization Knowledge — Factored Space Models (arXiv:2412.02579, branch `factored-space-models`)

Permanent, curated facts about this formalization. Committed with the code; read by every
harness agent before working. Add an entry only if a future fresh-context agent would act
differently for knowing it. One bullet per fact, newest last. Cross-reference finding IDs
(RN-Fxx) where an entry originated from an audit.

## Correspondence table

Paper notation ↔ Lean names (namespace `FactoredSpaces`).

| Paper (§/symbol) | Lean name | Notes |
|---|---|---|
| `Ω = ×_{i∈I} Ω_i` (Def 4.2) | `Pt Ω` for `Ω : I → Type v` | `dd:pi-space`; finiteness of `I` / `Ω_i` are instance hypotheses where used |
| `Ω_J`, `π_J`, `A_J` | `PtOn Ω J`, `proj J`, `projSet J A` | `PtOn Ω J = ∀ i : J, Ω i` |
| `U_i`, `U_J` (Def 4.2) | `bg i`, `proj J` | |
| `a_J · b_{I∖J}` (merge) | `J.piecewise a b` | Mathlib `Finset.piecewise` (`dd:splice`) |
| `S_J × T_{I∖J}` | `splice J S T` | `prodSplit J C = splice J C C` |
| `X ▷_C Y` (Def 4.1) | `DerivedOn C X Y` | `X ▷ Y` is `DerivedOn Set.univ X Y` |
| `(X, Y)` joint variable | `pair X Y` | |
| `J` disintegrates `C` (Def 4.5) | `Disintegrates J C` | stated as `C = prodSplit J C`; work with `disintegrates_iff_splice` |
| `J` generates `X` given `C` (Def 4.6) | `Generates J X C` | `generates_iff` is the working form |
| `H(X | C)`, `H(X)` (Def 4.6) | `history X C`, `history X Set.univ` | `Finset I` |
| `1_A`, `H(A | C)` | `indic A`, `eventHistory A C` | `dd:event-indicator` |
| the event `x` = `{X = x}` | `fiber X x` | |
| `X ⊥_Ω Y`, `X ⊥_Ω Y | Z` (Def 4.10) | `StructIndep X Y`, `StructIndepGiven X Y Z` | |
| `X ≤_Ω Y`, `X <_Ω Y` (Def 4.11) | `Before X Y`, `StrictlyBefore X Y` | |
| Lemma 4.7 | `generates_history`, `history_subset_of_generates`, `history_unique_minimal` | |
| Lemma 4.8 | `history_pair` | |
| Lemma 4.9 | `history_eq_iUnion_fibers` (Set form, no finiteness of `Val(X)`), `history_eq_biUnion_fibers` | |
| Lemma 4.12 | `structIndep_of_before`, `before_of_forall_bg`, `before_iff_forall_structIndep` | |
| Lemma A.1 | `Disintegrates.union`, `Disintegrates.inter` | |
| Lemma A.2 | `Generates.inter` | |
| Lemma B.1 | `structIndepGiven_pair` | |
| Lemma C.3 | `derivedOn_iff` | needs `[Nonempty β]`, see errata |
| Lemma C.4 | `generates_indic_iff_agree` (i⟺ii), `generates_indic_iff_splice` (i⟺iii), `eventHistory_minimal_splice` | |

## Design decisions

* **Splice encoding (`dd:splice`).** The obvious rendering of `C_J × C_{I∖J}` through
  `(∀ i : ↥J, Ω i)` and transports across `↥(J ∪ K) ≃ ↥J ⊕ ↥K` makes §4 and Appendix A a
  dependent-subtype slog. Disintegration is equivalent to closure under
  `Finset.piecewise` (`disintegrates_iff_splice`, proved against the literal product form),
  after which Lemma A.1 is two `piecewise` rewrites (`piecewise_union`, `piecewise_inter`)
  and A.2 / 4.7 / 4.8 / C.4 are short. Measured in the spike (`notes/spike-2026-08-17.md`).
* **Definition 4.5 stated literally.** `Disintegrates J C := C = prodSplit J C` with
  `prodSplit` built from the genuine projections `proj J`, so the paper node reads against
  the paper; the splice form is a proved equivalence, not the definition.
* **`history` is a `Finset.inf` over `Finset.univ.filter`,** with a single classical
  `Decidable` instance chosen inside the definition (`by classical; exact …`). Spike
  finding: with a per-proof `classical` the `Finset.filter` instances in `history_le`
  diverge and the goal gets stuck; keep the instance inside `history` and let callers
  `simp [history]`.
* **Unbundled factored space (`dd:pi-space`).** No `FactoredSpace` structure; the paper's
  objects live over `Pt Ω` for ambient `(I, Ω)`. Chosen so that variables, events and
  distributions need no coercions; the cost is that "there exists a factored space model"
  (Proposition 5.8) quantifies over `(I : Type) (Ω : I → Type)` explicitly.
* **`Val(X)` is the codomain (`dd:variable`).** Lemma 4.9's union over `Val(X)` is stated
  over the whole codomain type, which drops the paper's finiteness of `Val(X)` (the
  unattained values contribute empty histories); a `Fintype` `Finset.biUnion` form is
  provided alongside.
* **Universe in Lemma 4.12.** "For all variables `Z` on `Ω`" cannot range over all
  universes inside one `Prop`; `before_iff_forall_structIndep` lets `Val(Z)` range over
  `Type v` (the factors' universe, where the witnesses `U_i` live), and the ⟹ direction
  `structIndep_of_before` is stated separately, universe-polymorphic in `Val(Z)`.
* **Semigraphoid axioms via Theorem 6.2.** Proposition 5.2's axioms 1–4 are proved, as in
  the paper, from soundness+completeness and the semigraphoid axioms of probabilistic
  conditional independence — but the latter are *proved* for the paper's Definition 6.1
  (product-identity form, `P(C) = 0 ⟹ independent`), not cited from Pearl, so no
  citation boundary remains. Composition (axiom 6) is Lemma B.1, proved directly from
  `history_pair`. (Stage 3.)

## Intentional deviations from the paper

* **`[Nonempty β]` in Lemma C.3 (`derivedOn_iff`).** The paper's (ii)⟹(i) direction
  chooses `f(x)` "arbitrary" for unattained `x`, which presupposes `Val(Y)` inhabited; the
  statement is false for `C = ∅`, `Val(X)` nonempty, `Val(Y)` empty. The hypothesis is
  added and disclosed at the declaration; it propagates as `[Nonempty α]` on
  `generates_iff` and its consumers. See errata.

## Disclosures (residual modeling substitutions)

None.

## Paper errata

* **Lemma C.3** needs `Val(Y)` nonempty (see above); recorded in `notes/paper-errata.md`.
* **Definition 4.2** does not require the factors `Ω_i` to be nonempty, so `Ω` may be
  empty; later arguments that pick a point of `Ω` (or a distribution on it) implicitly
  assume it is not. Statements here add the hypothesis where they need it.

## Pitfalls

* `omit [Fintype I] in` / `omit [DecidableEq I] in` must precede the docstring, not sit
  between the docstring and the declaration.
* `Finset.piecewise` unfolds by `simp [Finset.piecewise, hi]`; after `set c := J.piecewise
  a b`, `simp [hc, hi]` already suffices and the extra `Finset.piecewise` argument is
  flagged unused.
* `Jᶜ` on `Finset I` needs `[Fintype I]` in scope (`Compl (Finset I)`), so every lemma
  mentioning a complement sits after `variable [Fintype I]`.
