# Thin first-order LUV frontend

The target is the paper's literal `def:luv`, compiled into FAF's existing abstract `LUV`
interface. This is separate from exact CCEE, which is already closed over arbitrary abstract
sources by `lic_no_expected_net_update_conditional_closed_exact`.

## Representation spike

`PaperLUV.lean` chooses a fixed representation of a nonnegative rational inside one-sorted
arithmetic: a value object is the Foundation pair code of numerator `a` and positive
denominator `b`. `paperRatGtDef r` expresses strict comparison by cross multiplication.
`paperRatGtDef_eval_nat` checks the intended standard-model semantics. A `PaperLUV T` keeps
the literal one-variable formula separate from sequence efficiency and carries object-level
Foundation proofs of unique existence and `[0,1]` membership. Its threshold is uniformly
`∀ q, X(q) → q > r`; negative and above-one thresholds are not replaced by public constants.

The pair representation is deliberately an ordered-value frontend, not a rational arithmetic
library. Different fraction codes such as `1/2` and `2/4` have the same external threshold cut,
while the `PaperLUV` uniqueness proof selects one object-level code. This is sufficient for
expectations and `ValuesAt`; arithmetic/equality closure between LUV values remains outside this
PR unless a downstream consumer demonstrates that canonical reduction is necessary.

## Completed semantic bridge

The literal object now supplies its abstract completed-world semantics without any
caller-provided cut certificate. Foundation arithmetic completeness derives three ordinary
theorems of `T` from `PaperLUV.unique` and `PaperLUV.unit`:

- every negative rational threshold holds;
- every threshold strictly above one is false;
- threshold truth is downward closed.

`paperTheoryDP T` publishes the prime decompositions of those theorems. Prime decomposition
respects negation and implication in every `PCWorld`, so no auxiliary `paperCutLawDP` is
needed. Consequently `PaperLUV.rationalCutAt` constructs the abstract rational cut in every
completed `paperTheoryDP` world, and `PaperLUV.source_valued` obtains a real `ValuesAt`
witness from the generic supremum theorem in `Framework/RationalCut.lean`.

## Remaining compiler boundary

The existing `paperPrimeDecompose` correctly treats quantified first-order sentences as
propositional prime atoms, matching the paper. Its public atom name, however, contains the
whole first-order Gödel code. Existing canonical RPN represents that atom by the single token
`paperPrimeCode ... + 5`. Producing this token under `PolyFueled` meters construction of the
whole natural code, not emission of the first-order formula's symbols.

Thus primitive-recursive Gödel compilation is not enough to prove the required
symbol-metered `RpnThresholdCodeSeq`. The next implementation milestone is a narrow additive
structured-prime block in the RPN frontend (or an equivalent fixed semantic handle): emit a
first-order prime formula symbol-by-symbol, then contract it to the existing tag-7 public atom.
It must preserve all current RPN clients and prove a bridge to `RpnSentenceCodes`.

No caller-supplied threshold family or cut certificate enters the semantic API. The next
checkpoint is solely the symbol-metered structured-prime emission bridge.
