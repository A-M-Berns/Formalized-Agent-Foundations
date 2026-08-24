# Literal first-order LUV frontend

## What is formalized

The paper's `def:luv` is a first-order formula, free in one variable, that the theory
proves defines a unique value in `[0,1]`. The repository's abstract `LUV` is the
propositional threshold family `gt : ℚ → Sentence` that downstream results consume.

This frontend supplies the missing half: a literal Foundation-arithmetic object that
*produces* the abstract interface, rather than an abstraction standing in for it. A
`PaperLUV` is an actual one-variable arithmetic formula carrying object-level Foundation
proofs; it compiles to an ordinary `LUV` whose thresholds are the paper's own literal
threshold sentences, and it supplies world-value semantics and symbol-metered efficiency
as *derived* facts instead of caller-supplied certificates.

Two independent bridges meet in `PaperLUVSeq`:

```text
semantic:   PaperLUV → paperTheoryDP → rational cut → ValuesAt
syntactic:  PolyArithmeticFormulaSeq → structured RPN → RpnThresholdCodeSeq
```

Downstream code is untouched: it still consumes the abstract `LUV`.

## PaperLUV

```lean
structure PaperLUV (T : ArithmeticTheory) [T.Δ₁] where
  formula : ArithmeticSemisentence 1
  unique  : T ⊢ ∃⁰! formula
  unit    : T ⊢ ∀⁰ (formula 🡒 paperRatUnitDef)
```

The two proofs are object-level derivations in `T`, not Lean-level side conditions. The
threshold syntax is literal and uniform:

```lean
thresholdFormula X r = ∀⁰ (X.formula 🡒 paperRatGtDef r)
```

Negative thresholds and thresholds above one are *not* replaced by public constants; they
are the same formula shape, and their truth is derived rather than stipulated.
`PaperLUV.toLUV` compiles the literal object into the abstract interface by prime
decomposition, so `X.toLUV.gt r` is exactly `paperPrimeDecompose (X.thresholdFormula r)`.

## Rational value representation

A value is represented inside one-sorted arithmetic as the Foundation pair code of a
numerator `a` and a positive denominator `b`, and `paperRatGtDef r` compares it against an
external rational by cross multiplication.

This is deliberately an **ordered-value** representation, not a canonical rational
arithmetic library. Distinct fraction codes such as `1/2` and `2/4` remain distinct object
codes; what `PaperLUV.unique` fixes is the object-level code the formula selects, and what
the thresholds determine is the external cut. That is what LUV expectation semantics needs:
the represented real is recovered through the rational cut, not through internal
normalization. Arithmetic or equality closure *between* LUV values — a genuine
arithmetic-internal rational library — is outside this frontend, and its absence is a scope
boundary rather than a defect in `def:luv`.

## Completed-world semantics

The literal object supplies its own completed-world semantics with no caller-provided cut
certificate. Foundation's arithmetic completeness derives three ordinary theorems of `T`
from `unique` and `unit`:

- every negative rational threshold holds;
- every threshold strictly above one fails;
- threshold truth is downward closed.

`paperTheoryDP T` publishes the prime decompositions of those theorems, and prime
decomposition respects negation and implication in every `PCWorld`. So
`PaperLUV.rationalCutAt` builds the abstract rational cut in every completed
`paperTheoryDP` world, and `PaperLUV.source_valued` extracts a real `ValuesAt` witness
through the generic supremum argument in `Framework/RationalCut.lean`. No
`PaperCutLawDP`, proof-carrying source, semantic handle, or custom deductive process
appears anywhere on this path.

## Structured arithmetic syntax codec

The efficiency problem is that the abstract threshold atom's *name* contains the whole
first-order Gödel code. Emitting that name as a token would meter construction of an
astronomically large natural rather than emission of the formula's symbols.

`StructuredPaperRpn.lean` solves this by extending the RPN grammar with a structured leaf
whose tokens are all small, and letting the *parser* build the large code by contraction:

```text
[1, 0, polarity] ++ replicate payload.length 1 ++ [0] ++ payload ++ [19]
```

The dispatch prefix `[1, 0]` is backwards compatible because propositional sentence code
`0` never decoded under the old grammar, so every legacy stream keeps its old parse
(`parseRpn_of_legacy`). The payload is a prefix tree over the alphabet `0..18` covering the
complete Foundation arithmetic syntax used here — bound and free variables, `0`, `1`,
addition, multiplication, positive and negated equality and `<`, conjunction, disjunction,
and both quantifiers — with naturals themselves encoded as recursive small-token binary
rather than as one large value. Token `19` is reserved as a terminator, which is what lets
the strategy grammar's streaming scanners recognize the whole leaf as one atom without
replaying the Foundation decoder.

*Design rationale for the framing.* An earlier attempt used an explicit symbol **count**
field. That is self-delimiting for the parser but wrong for the rest of the ABI: the
conditioning automaton clamps large token values, so an untrusted count reintroduces a
polynomial-output problem on malformed streams, and the run/parse correspondence fails at
the marker. Small-token unary length plus a reserved terminator keeps every scanner's state
polynomially bounded on *arbitrary* input, which is the property the shared grammar needs.

The leaf contracts to the **exact existing** public syntax — `paperPrimeSentence` and
`paperPrimeDecompose` — not to an alias or a semantic handle.

## Symbol-metered efficiency

The efficiency hypothesis is structural:

```lean
PolyArithmeticFormulaSeq φ  :=  PolySegStream (fun n => encodeArithmeticFormulaSymbols (φ n))
```

It certifies emission of the formula's *symbols*, and asks nothing about the magnitude of
Foundation Gödel codes. The emitted-token audit pins the cost model: every payload token is
`< 19`, every framing tag is a fixed small constant, and the tag-7 atom code is produced by
`parseRpn` contraction and never appears in the emitter's output.

The lifting endpoints are `structuredPaperPrime_rpnSentenceCodes` and, for the
quantifier-headed propositions that threshold syntax always produces,
`structuredPaperDecomposeAll_rpnSentenceCodes`.

## PaperLUVSeq

A single `PaperLUV` carries no efficiency certificate, so the family layer supplies one —
and supplies it on the LUVs' *own defining formulas*:

```lean
structure PaperLUVSeq (T : ArithmeticTheory) [T.Δ₁] where
  luv        : ℕ → PaperLUV T
  structural : PolyArithmeticFormulaSeq (fun n => (luv n).formula)
```

Everything the threshold syntax adds on top is discharged internally: the implication
shell, the fixed comparison template of `paperRatGtDef`, and the reduced numerator and
denominator of the query rational `i / k` (whose `gcd` normalization uses the fuel
calculus's existing `gcdc`/`divmod1` primitives). The results are

```lean
PaperLUVSeq.rpnThresholdCodeSeq                    : LUV.RpnThresholdCodeSeq …
PaperLUVSeq.source_valued_and_rpnThresholdCodeSeq  : ValuesAt … ∧ RpnThresholdCodeSeq …
```

## Concrete non-vacuity witness

`unitFracPaperLUVSeq` is the family of literal paper LUVs of value `1/(n+1)`. Its defining
formulas genuinely grow with `n`; its uniqueness and `[0,1]` facts are object-level
derivations valid in any theory extending `𝗜𝚺₁`; and its structural certificate is proved
from the formulas' token layout. `unitFracPaperLUVSeq_frontend` instantiates the capstone,
so both frontend conclusions hold of an actual first-order family.

`PaperLUVSeq.const` also exists, but a constant family is a convenience, not the
non-vacuity witness.

## Downstream interface

`PaperLUVSeq` supplies exactly the two abstract interfaces downstream LUV results expect:
world-valuedness and `LUV.RpnThresholdCodeSeq`. It is deliberately *not* wired into the
exact-CCEE consumers here: those take a `PresentedLUVSeq`, whose `threshold_named` field
requires thresholds named by a semantic-handle schema (`semanticPrimeSentence`) — the
naming this frontend exists to avoid. Connecting the two would mean changing the fixed
deductive process or reintroducing handles, which is separate architectural work and not
part of this frontend.

## Scope and remaining limitations

- **Ordered-value representation.** As above: a numerator/positive-denominator pair code,
  not canonical rational arithmetic, and no arithmetic closure between LUV values.
- **Decomposition bridge is head-scoped.** `structuredPaperDecomposeAll_rpnSentenceCodes`
  covers quantifier-headed propositions, which is what `thresholdFormula` always produces.
  A version for arbitrary outer Boolean structure would need a bracket-counting scan over
  the payload; it is not required by this frontend.
- **The abstract carrier is unchanged.** Downstream theorems still quantify over `LUV`,
  which admits threshold families that are not literal paper LUVs. `def:luv` itself is
  classified `instantiated` — its definition is rendered by `PaperLUV` — while that
  carrier-level charge is carried by `def:blcp`.
- **`dd:fuel` is independent.** The legacy-only positional matcher in `RpnFreeze` is scoped
  to the pre-structured grammar for a fuel-model reason that predates this work and is not
  a limitation of this codec; see that module's disclosure.
