# M6 verification packet — construction Part 1

Date: 2026-07-14. Scope: paper `lem:fpl`, `def:markemaker`, and `lem:mm` only.
`Budgeter`, `TradingFirm`, `LIA`, unconditional existence, and all M7 compilation work are
explicitly excluded.

## Statement comparison

| Paper obligation | Lean realization | Alignment and disclosed substitution |
|---|---|---|
| `lem:fpl`: a continuous finite day strategy admits a `[0,1]` price vector whose value is nonpositive in every possible world | `fixed_point_lemma` | Exact for the repository's actual finite `Strategy n`. `Strategy.shares` aggregates repeated occurrences before applying Brouwer. The vector is indexed by syntactic support and is zero elsewhere. “Possible world” is the existing `PCWorld` Foundation Boolean model. Days are 0-based. |
| `def:markemaker`: effectively find a rational finite-support approximation with world value at most `2^{-n}` | `RationalBeliefState`, `MarketMakerAccepts`, `marketMakerSearchUpTo`, `MarketMaker_search_clock`, `MarketMaker_support`, `MarketMaker_range`, `MarketMaker_worldValue_le` | The candidate enumeration is concrete finite rational association lists. Each fuel step decodes one candidate and decides the exact rational inequality for every support-bit table. Rational density proves termination. The exposed allowance is `2^{-(n+1)}` because Lean day `0` is paper day `1`. The executable witness is the fuel-recursive Lean program and stopping-clock theorem, not a separate `Nat.Partrec.Code` recompilation; no polynomial bound is claimed or required here. |
| `lem:mm`: the MarketMaker induced by any trader is not exploited by that trader | `marketMakerStates`, `marketMakerHistory`, `marketMaker_not_exploited` | Exact quantifier strength: every `Trader` and every `DeductiveProcess`. History recursion uses precisely the earlier rational states. Per-day bounds sum to `<1`, so plausible net worth is uniformly bounded above. The proof does not assume efficient computability, budgeting, or a trading firm. |

## Anti-vacuity and trust checks

- `MarketMakerAccepts` contains only finite support inclusion and exact rational inequalities;
  it does not carry the desired real-world theorem as a field.
- The real inequality is derived by cast-soundness, and the all-`PCWorld` result is derived
  from support locality.
- `MarketMaker` decodes the enumerated first success with `Option.get`; there is no
  `Classical.choose` selecting a belief state.
- The fixed-point theorem is the already kernel-checked in-project Brouwer result.
- Expected capstone axiom surface: `propext`, `Classical.choice`, and `Quot.sound` only.

## Exit results

- `lake build LogicalInduction.Construction`: 2,426/2,426 jobs passed.
- `lake build`: 2,671/2,671 jobs passed.
- Executable `sorry`/`admit`/`sorryAx` scan: empty (historical prose mentions excluded).
- `git diff --check`: clean.
- `#print axioms` for `fixed_point_lemma_bounded`, `fixed_point_lemma`,
  `MarketMaker_search_clock`, and `marketMaker_not_exploited`: exactly `propext`,
  `Classical.choice`, and `Quot.sound`.
