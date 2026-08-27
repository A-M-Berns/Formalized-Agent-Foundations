# Formalization knowledge — Logical Induction (arXiv:1609.03543)

Facts about this formalization that a reader working on it would otherwise have to
rediscover: the paper-to-Lean correspondence at the points where the names do not match,
and the design decisions that are settled and should not be relitigated. It deliberately
does not duplicate the canonical documents — read those first.

- Trust surface, disclosures and strength claims: `LogicalInduction/README.md`
- Recommended consumer import and its boundaries: `LogicalInduction/API.lean`
- `dd:*` design-decision glossary, naming conventions, endpoint-suffix ladder:
  `LogicalInduction.lean`
- `dd:fuel` model card: `Framework/Computable.lean` ("### `dd:fuel` model card")
- Defects in the source paper: `notes/paper-errata.md`
- Lean and toolchain traps: `notes/lean-gotchas.md` — the single home for pitfalls
- Checked endpoint inventory and axiom accounting: `AxiomAudit.lean`

## Correspondence table

The full paper-to-Lean correspondence is carried by the `Paper node:` docstring lines and
checked two-way by `scripts/check-paper-nodes.sh`. Listed here are only the places where the
name does not say what the object is.

| Paper (§/symbol) | Lean name | What to know |
|---|---|---|
| `def:ec`, §3.3 (`sec:efc`, tex:749) | `MachineEfficientTrader` (`Framework/Criterion.lean`) | The paper's own quantifier: ordinary machine polynomial time via `Complexity.FP`, over the **unary** day. This is the class the construction enumerates and dominates. |
| `def:ec`, certification | `EfficientlyComputable` / `PolyFueled` (`Framework/Computable.lean`) | Fuel-clocked `Nat.Partrec.Code` certificates (`dd:fuel`). A *sufficient* route into the machine class (`EfficientlyComputable.toMachine`), not a definition of it. Fuel meters the **value** `n`, not its bit length, which is sound only because the day is unary. |
| `def:lic` | `IsMachineLogicalInductor` (`Framework/MachineEfficiency.lean`) | The criterion the construction proves. `IsLogicalInductor` is the same criterion over the fuel class, kept as the compatibility predicate the §4 tail is stated against. |

- `def:ec` is paper **§3.3**, not §2.2 — §2 is Notation, §3 is the Criterion.
- `evaln_output_can_exceed_fuel` (`Framework/Computable.lean:51`), `codeEvalBound`,
  `codeEvalBound_poly` and `codeEvaln_result_le` (`Framework/Emission.lean:21–78`) are
  **repo** lemmas, not Mathlib. Grepping Mathlib for them finds nothing.

## Settled design decisions

**The two efficiency classes, and which way the inclusion runs.**

- `EfficientlyComputable Tr → MachineEfficientTrader Tr` is proved
  (`EfficientlyComputable.toMachine`). The converse is **not** proved, and the honest
  wording for it is "not attempted; structurally blocked in the fuel calculus's toolkit" —
  never "false as stated" or "provably fails". `RpnFreeze` records a *structural toolkit*
  obstruction (`BigDigits` is closed under forward polynomial carry recurrences and open
  under inverses) and itself says the claim holds in the intended complexity model;
  `not_polyFueled_two_pow` (`Framework/Computable.lean:1679`) separates only `PolyFueled`,
  by output size. The model card's "Lower calibration — OPEN" wording is authoritative.
- The fuel bound is polynomial in the **day**, and the day is unary, so composing
  `codeEvalSteps_poly` (`Framework/Machine/CodeSteps.lean`) with either the `PolyFueled`
  bound or `EfficientlyComputable`'s explicit clock `a * (n + 1) ^ k + a` gives a step count
  polynomial in the input length. A binary day rendering would silently strengthen the class.
- The clock normal form's `+ a` summand and `(n + 1)` base are load-bearing for
  satisfiability at degenerate inputs: `|output| ≤ |input| + t` at `w = []` needs
  `clock 0 ≥ output length`, which `2a` supplies and a bare `a · n ^ k` would not.
- The `IsPolyBounded f` conjunct of `PolyFueled` is derivable from the other two, via
  `codeEvaln_result_le` + `codeEvalBound_poly` + `IsPolyBounded.comp`.
- `codeEvalBound c k` is polynomial in the fuel **per fixed code** — the degree grows with
  the code, since `pair` doubles it. The `n ≤ k` guard caps every value passed onward, which
  is why exponential-growth codes return `none` rather than break the bound.
- `IsPolyBounded.mul` lives in `Framework/Machine/CodeSteps.lean`, not beside the other
  closure lemmas in `Framework/Computable.lean`: the `prec` step count is what needed it.

**Serialization and the decoding pipeline.**

- `Trader` is a one-field structure, so `EfficientlyComputable`'s witness equality
  `clockedTrader lc tc clock = Tr` is interchangeable with the pointwise form
  `∀ n, strategyOfTokens n (unRpn (undigitize (clockedTokens lc tc (clock n) n))) = Tr.strat n`.
  Machine-side bridges consume the pointwise form.
- In that chain `clockedTokens` emits the **digit** stream — one digit per `tokenCode` call —
  not tokens. Clamping digits by `min · 4` is semantics-preserving, because
  `undigitizeStep` branches only on `d < 4` and treats every `d ≥ 4` as a block terminator
  (`undigitize_map_min_four`). That clamp is what lets the machine emit a fixed three bits
  per digit.
- The clamp lemma `undigitize ∘ map (min · 4) = undigitize` is a one-line `blockSplit`
  invariance from `undigitize_eq_blockSplit` (`Framework/DigitArith.lean:934`) plus
  `blockStep`, not a from-scratch induction.
- **Degenerate inhabitants are not evidence of content.** The interpretation chain's empty
  conventions cooperate — `undigitize [] = []`, `unRpn [] = []`,
  `deserializeTrades [] = some []`, `strategyOfTokens n [] = ⟨[], _⟩` — so
  `strategyOfTokens n (unRpn (undigitize [])) = Trader.zero.strat n` closes by `rfl`, and any
  class of the shape `∃ F, «F is efficient» ∧ interp ∘ F = Tr.strat` is inhabited by the
  constant-`[]` witness. `MachineEfficientTrader` included. Never cite such a witness as
  evidence that a machine statement has content.

**The `evaln` simulation.**

- `evaln`'s `prec` ladder never underflows, and no intermediate guard fails once the
  top-level `guard (n ≤ k)` passes (`y ≤ Nat.pair a y ≤ k`, and
  `Nat.pair a j + (y − j) ≤ Nat.pair a y`); the base `cf` guard is free too, since
  `a ≤ Nat.pair a 0`. The live `none` sources in a `prec` simulation are: fuel `0`, the top
  guard, `cf`/`cg` *internal* failure, and `cg`'s own guard on the assembled argument
  `Nat.pair a (Nat.pair y i)` — which is genuinely unbounded by `n` and genuinely fails. No
  underflow test phase is needed. `rfind'` contrasts: its argument grows while fuel shrinks,
  so its guard failures are real.
- Failure **order** within a level is irrelevant to extensional agreement: every branch is a
  total `Option` computation, so an upward `prec` loop need not mirror the downward
  recursion's detection order, only its value.
- `Nat.pair` monotonicity for guard arithmetic is in Mathlib: `Nat.left_le_pair`,
  `Nat.right_le_pair`, `Nat.pair_lt_pair_left`, `Nat.pair_lt_pair_right`,
  `Nat.add_le_pair` (`Mathlib/Data/Nat/Pairing.lean:102–148`). Cite, do not re-derive.

**Layering in the executable machine side.**

- `Construction/Machine/DescExec.lean` is indexed by machine **descriptions**, not machines:
  `LIACompiler` needs the enumeration to be primitive recursive, and a `Complexity.TM k`
  bundles its state type and its tapes as functions, neither of which `Primrec` can see.
- Executability (`Primrec`), polynomial-time soundness of each indexed computation, and
  coverage of every polynomial-time trader are three different facts, and the modules are
  split along exactly those lines. Making the primitive-recursive evaluator carry the
  complexity proof is the conflation to avoid.
- The semantic class and the enumeration are kept apart on purpose:
  `MachineEfficientTrader` is not defined as "occurs in the enumeration"; that every member
  does occur is the content of `exists_enumeratedTrader_eq`.

**Known dead weight.** `PolyEF` (`Framework/Computable.lean:258`) is a dead-end layer:
consumed only by other `PolyEF` lemmas, never converted to any emission class. It is a
consolidation candidate, recorded here so it is not mistaken for load-bearing.

## Intentional deviations from the paper

The standing modeling choices are the `dd:*` labels in `LogicalInduction.lean`, with the
type-`(c)` substitutions and their justifications in `LogicalInduction/README.md`. Entries
there are not audit findings unless the justification itself is wrong.

## Paper errata

`notes/paper-errata.md` is the ledger. The one a reader must know before using §4.6: the
published `thm:ifp` is **false**, and the repository proves it false; what is available is
the corrected finite-support theorem
`FreezeOracle.machine_lic_iff_of_recognizableSupport`.

## Pitfalls

See `notes/lean-gotchas.md`.
