# Thin first-order LUV frontend

The target is the paper's literal `def:luv`, compiled into FAF's existing abstract `LUV`
interface. This is separate from exact CCEE, which is already closed over arbitrary abstract
sources by `lic_no_expected_net_update_conditional_closed_exact`.

## Representation spike

`PaperLUV.lean` chooses a fixed representation of a nonnegative rational inside one-sorted
arithmetic: a value object is the Foundation pair code of numerator `a` and positive
denominator `b`. `paperRatGtDef a b` expresses strict comparison by cross multiplication.
`paperRatGtDef_eval_nat` checks the intended standard-model semantics. A `PaperLUV T` keeps
the literal one-variable formula separate from sequence efficiency and carries object-level
proofs of unique existence and `[0,1]` membership.

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

After that bridge, the remaining semantic work is to derive the public upper/downward laws
from the two `PaperLUV` theory proofs and expose them through the canonical
`paperTheoryDP`/`paperCutLawDP` process. No caller-supplied threshold family or cut certificate
should enter the final API.
