/-
# Logical Induction (Garrabrant et al., arXiv:1609.03543) — Lean 4 formalization

The root roll-up: importing this file brings in the whole formalization. Start here, then
read `LogicalInduction/README.md` for what is proved, the two declared modeling
boundaries, and the faithfulness record; `AxiomAudit.lean` is the checked inventory of
every public endpoint. The library follows the paper's own sectioning — `Framework` is
§2–3 (sentences, markets, features, traders, exploitation, the criterion, efficient
computability, expectations, and the shared asymptotic vocabulary), `Properties` is the
§4 property tail with one file per theorem family, and `Construction` is the §5 existence
proof, with `Construction/Witnesses/` holding the representation machinery that
discharges the property tail's interfaces over the concrete constructed inductor. Every
paper-facing statement cites the paper's real `\label`, and the citation is checked in
both directions by script.

## Reading the repository against the paper

Core vocabulary, repo name → paper name (labels are the paper's own `\label`s):

* `Sentence` — sentences of the base language (`def:lang`), propositional via Foundation.
* `History` (usually `P`) — the market: one pricing per day (`def:market`).
* `PCWorld` — a plausible world: a propositionally consistent `{0,1}` valuation
  (`def:world`).
* `DeductiveProcess` (usually `DP`) — the deductive process `D̄` (`def:worlds`).
* `EF` — an expressible feature (`def:valfeature`/`def:tf`).
* `Trader`, `AffineCombination` — traders and their affine buy combinations
  (`def:trader`, `def:tradestrat`).
* `MachineEfficientTrader` — `def:ec` at the paper's own quantifier: ordinary machine
  polynomial time, through `Complexity.FP`. This is the class the construction enumerates
  and dominates.
* `EfficientlyComputable` / `PolyFueled` — the fuel-clocked interpreter certificates
  (`dd:fuel`). Internal certification technology: every certificate implies membership in
  the machine class (`EfficientlyComputable.toMachine`).
* `IsMachineLogicalInductor` — the logical induction criterion at the machine class
  (`def:lic`), and what the construction proves.
* `IsLogicalInductor` — the same criterion over the fuel class, kept as a compatibility
  predicate; every machine logical inductor is one.
* `LUV` — a logically uncertain variable (`def:luv`).
* `LIA` — the paper's logical induction algorithm (`def:lia`).

## Design-decision labels (`dd:*`)

A `dd:` label marks a place where the formalization makes a *choice* the paper does not
force, and every affected statement cites the label rather than restating the choice. The
list is exhaustive; a label appearing nowhere below is not in use.

* **`dd:fuel`** — a trader's efficiency *certificate* is a fuel-clocked interpreter
  bound: a `Nat.Partrec.Code` program emitting its trade stream within a polynomial fuel
  bound on Mathlib's `evaln` (`EfficientlyComputable` / `PolyFueled`). This is no longer a
  substitution for the paper's class. `def:ec` itself is `MachineEfficientTrader` —
  ordinary machine polynomial time via `Complexity.FP` — the construction enumerates and
  dominates *that*, and `EfficientlyComputable.toMachine` proves every fuel certificate
  lands inside it. The label now marks a *sufficient certification device*, and what
  remains open is only its converse (the model card's lower calibration), which nothing
  paper-facing depends on.
* **`dd:dsl`** — expressible features (`EF`) are a *reified* datatype with two semantics
  (a denotation into `ℝ` and a token/cost semantics), rather than Lean functions. The
  syntax is what carries the efficiency certificate, so features must be objects that can
  be emitted and metered.
* **`dd:asymp`** — one module, `Framework/Asymptotics`, owns the limit vocabulary
  (`≈ₙ`, `≳ₙ`, `≲ₙ`, "eventually within ε", "converges to"), built on Mathlib's
  `Tendsto` and `∀ᶠ n in atTop`, in the limiting rather than the finite-stage form. It is
  never redefined per file.
* **`dd:luv-arith`** — the certified LUV class: a logically uncertain variable presented
  by rational thresholds `num i / den i ∈ ℚ ∩ [0,1]` over an arithmetic theory, for which
  the world-value and threshold-emission obligations are *proved* rather than assumed.
  Endpoints suffixed `_arith` are the paper's statement restricted to this class, and are
  where the general layer's representation hypotheses get discharged.
* **`dd:quote-code`** — quotation data is *code-indexed*: a quote structure carries a
  selector `code : ℕ` naming the program being quoted, instead of quantifying over an
  abstract quotation schema. This is what makes the quotation presentation satisfiable
  (an abstract free-schema version was not).
* **`dd:mesh`** — `thm:ccee`'s quoted product `⌜Xₙ · w_{f(n)}⌝` is realized on a finite
  *mesh* of the deferred weight's own threshold atoms, so it reflects the product only to
  within `1/(n+1)` rather than exactly. This is a disclosed type-`(c)` substitution, not
  merely a presentation choice: an exactly-reflecting product LUV would need either the
  weight's *value* (unavailable to an emitter) or an infinite disjunction (absent from the
  propositional substrate). It is what buys the paper's arbitrary e.c. source family; the
  slack is carried explicitly by `ConditionalExpectationQuote.slack`.

## Naming conventions

* `lic_<node>` is a consequence of the logical induction criterion, mirroring the paper
  node named in its docstring — `lic_provind` ↔ `thm:provind`, `lic_nonDogmatism` ↔
  `thm:nd`. Such statements take `[IsLogicalInductor P DP]`. (`lic_iff_of_finitePerturbation`
  is the one transport rather than consequence.) Where the paper's statement is about a
  combination or a LUV rather than a sentence, the endpoint lives in the corresponding
  namespace and drops the prefix — `AffineCombination.BoundedCombinationSequence.prandaff`,
  `LUVCombination.BoundedSequence.wubexp`.
* `theorem` is reserved for paper-facing statements, and every one of them ends its
  docstring with a `Paper node:` line listing labels verbatim from the paper's
  `\label{…}`. Internal statements are `lemma` or `private lemma`; they carry no
  `Paper node:` line and may be renamed or inlined freely.
* Suffixes say what has been discharged, and compose left to right:
  - `_ofComputation` / `_ofCode` / `_ofRepresentation` / `_ofPrefixMachine` / … — the
    same statement with a formerly *assumed* boundary interface supplied by a concrete
    construction named in the suffix.
  - `_unconditional` — the `[IsLogicalInductor P DP]` hypothesis is gone: the statement
    holds of the constructed `LIA` over the constructed deductive process. Representation
    data may still be a caller hypothesis.
  - `_closed` — `_unconditional` *and* the reflection/quote-code data constructed too, so
    nothing remains but the statement's own data and its efficiency certificates. This is
    the strongest form a property endpoint takes.
  - `_arith` — restricted to the `dd:luv-arith` certified class (see above).
  - `_above` / `_below` / `_eq` — the one-sided comparison directions of a two-sided
    asymptotic conclusion.

`scripts/coverage-classification.md` records, per paper label, which of these forms the
strongest endpoint actually reaches.
-/
import LogicalInduction.Framework
import LogicalInduction.Properties
import LogicalInduction.Construction
