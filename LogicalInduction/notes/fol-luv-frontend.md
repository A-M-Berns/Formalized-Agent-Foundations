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

## Structured-RPN kill test: counted format blocked

The existing `paperPrimeDecompose` correctly treats quantified first-order sentences as
propositional prime atoms, matching the paper. Its public atom name, however, contains the
whole first-order Gödel code. Existing canonical RPN represents that atom by the single token
`paperPrimeCode ... + 5`. Producing this token under `PolyFueled` meters construction of the
whole natural code, not emission of the first-order formula's symbols.

`StructuredPaperRpn.lean` tests the proposed additive format without installing it in the
shared parser:

```text
[1, 0, polarityCode, symbolCount, symbols...]
```

where the formerly invalid ordinary payload `0` is the marker and the explicit count makes
the block self-delimiting. The checkpoint grammar is intentionally tiny: postfix symbols for
first-order `⊤`, conjunction, and existential quantification. It contracts a linearly growing
family `∃ x, (⊤ ∧ ⋯ ∧ ⊤)` to the exact existing tag-`7` `paperPrimeSentence`, and
`structuredFOTestBlock_polySegStream` proves that the input block itself is polynomially
emittable.

The basic cost boundary is favorable: `PolySegStream` would certify only the structured
input symbols, while contraction is a denotational validation step rather than a
`PolyFueled` output. The giant final Gödel value is therefore not itself the blocker.

The blocker is the rest of the RPN ABI. `parseRpn_structuredFOTestBlock_none` proves that the
current parser rejects the marker, while
`structuredFOTest_conditioning_exits_after_marker` proves that the conditioning run automaton
exits after `[1,0]`, before polarity, count, or formula symbols. Installing the counted parser
branch would make its central run/parse theorem false. Moreover, the generic conditioning
compiler accepts arbitrary digit-emitted inputs and clamps large token values; storing an
untrusted count token directly would reintroduce a polynomial-output problem on malformed
streams even though valid counted blocks have small counts.

The next implementation milestone must therefore change the block framing before building a
full codec. The leading candidate is a small-token, self-delimiting prefix grammar (or a
reserved small terminator) whose scanner tracks only polynomially bounded parse state. That
format must be implemented jointly in `parseRpn`, its numeric mirror, `RpnConditioning`, and
the corresponding freeze/splice scanners, with the run/parse invariant re-proved. Only after
that green integration should the grammar be generalized to complete arithmetic syntax.

No caller-supplied threshold family or cut certificate enters the semantic API. The next
checkpoint is a scanner-compatible structured-leaf framing spike.
