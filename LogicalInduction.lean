/-
# Logical Induction (Garrabrant et al., arXiv:1609.03543) — Lean 4 formalization

The root roll-up: importing this file brings in the whole formalization. Start here, then
read `LogicalInduction/README.md` for what is proved, the declared modeling boundary,
and the faithfulness record; `AxiomAudit.lean` is the checked inventory of
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
* **`dd:nnf`** — the *semantic* object language is Foundation's
  **negation-normal-form** `Semiformula` (constructors `verum/falsum/rel/nrel/and/or/all/exs`,
  negation a meta-level involution, `A 🡒 B` notation for `∼A ⋎ B`, `A 🡘 B` notation for
  `(A 🡒 B) ⋏ (B 🡒 A)`), but *writing* is metered on a **source** language, not on that
  normal form. `ArithSource k` (`Construction/Witnesses/ArithmeticSource.lean`) carries the
  paper's own primitive connectives (tex:560) — `¬`, `∧`, `∨`, `⟹`, `⟺`, `∀`, `∃`, plus
  atomic leaves — `compile : ArithSource k → ArithmeticSemiformula ℕ k` gives it its
  meaning (`eval_compile`), and `def:ec`'s condition is `PolyArithmeticSourceSeq`: one
  emitted token per node of the formula **as the paper writes it**. Normal-form expansion
  happens inside the parser (tags `20`/`21`/`22`) and is never charged. So this label no
  longer marks a substitution: nothing pays twice for a `⟺`. What it marks is the
  two-layer architecture, and the fact that the normal-form-metered class
  `PolyArithmeticFormulaSeq` is retained as a **strictness foil** rather than deleted: it
  embeds (`PolyArithmeticFormulaSeq.toSource`) and the inclusion is *strict*, witnessed at
  the left-nested chain `Φ₀ = A`, `Φₖ₊₁ = Φₖ ⟺ A`, which costs `5n + 4` source tokens
  (`iffChainSource_polyArithmeticSourceSeq`, `sourceTokens_iffChainSource_length`) and
  `≥ 2ⁿ` normal-form tokens (`iffChain_not_polyArithmeticFormulaSeq`,
  `two_pow_le_encode_iffChain`). That family is carried all the way to a literal paper LUV
  family (`iffPaperLUVSeq`, `iffPaperLUVSeq_frontend`), so
  `PolyArithmeticFormulaSeq ⊊ PolyArithmeticSourceSeq` is proved, not asserted.
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
* **`dd:symbolcount`** — §4.10's finite proof searches are metered by the **symbol count
  of the derivation**, as the paper's `Con(Θ′)(ν)` is (tex:1855-1866), with the bound
  inclusive. Foundation exposes no size function on its internal derivations, so
  `Framework/DerivationSize.lean` builds one: `dSize`, defined by external recursion over
  the derivation codes at `V := ℕ`, with equations tying it to Foundation's own
  constructors (`dSize_axL`, `dSize_cutRule`, …) and the converse bound
  `le_G_dSize : d ≤ G (dSize d)` that keeps the metered search decidable in both
  polarities. This is a **convention, not a modelling substitution**: the paper fixes
  neither a Gödel encoding nor an alphabet ("written in `ℒ` using a Gödel encoding"), so
  some counting convention must be chosen, and ours — one symbol per rule name,
  connective, quantifier, predicate, function symbol and variable occurrence, one
  separator per argument-list entry, and, for every variable, function and relation index,
  its binary digit count **plus one marker token** (`idxLen n = Nat.size n + 1`, so
  `idxLen 0 = 1` and `idxLen 1 = 2`; the marker is what separates an index numeral from
  the material following it) — is stated in full in that module's header. The index
  convention is the same write-out metering the rest of this development uses (`def:ec`),
  and it is what makes the measure finite-fibred; the fixed per-index marker over-counts,
  which is the safe direction for a bound. Nothing outside `DerivationSize.lean` depends
  on the choice *for the truth of the endpoints* — `conWithin_of_consistent`, which proves
  every day's claim from consistency alone, never mentions `dSize` — the choice affects
  only which horizons discharge the non-degeneracy side conditions
  (`conGamma_mentions_zero_of_bProv`, `conGamma_mentions_zero_of_horizon_unbounded`), whose
  hypotheses are quantitative in the measure. *(This entry replaces the retired
  `dd:proofcode`, which disclosed the Gödel-number measure that stood in for the paper's
  symbol count before tranche 9a.)*
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
