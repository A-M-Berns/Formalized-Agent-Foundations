import LogicalInduction.Framework.Machine.SentenceMachine

/-!
# The splice write-out class, machine reading: its combinators and the trader capstones

`MachineSpliceStream` (`Framework/Machine/WriteOutMachine.lean`) is `BigSpliceStream` with
its `BigTokenStream` replaced by `MachineTokenStream`: a `Complexity.FP` function of the
unary day emits a block-complete word whose tokens `UnRpnContractsTo` the target stream.
This file carries the combinator suite, mirroring `BigSpliceStream.*`
(`Framework/Emission/WriteOut.lean`), and the three capstones a client assembles an
exploiting trader with — `MachineSpliceStream.ec`,
`EfficientlyComputable.ofSingleTradeBlocksBig` and `.ofTradeBlocksBig`.

Because both classes are stated *over* their token stream, every combinator proof here has
the same shape as its fuel-metered twin: `obtain` the underlying stream, run the identical
`MachineTokenStream` closure lemma in place of the `BigTokenStream` one, and reuse the
`UnRpnContractsTo` argument — `UnRpnTransparent.single`, `.payload`,
`UnRpnContractsTo.append`, `.priceChunk`, `.tradeChunk` — verbatim, those being facts about
token lists and nothing else.

## What a `ℕ → ℕ` parameter becomes, and the two roles it plays

The fuel-metered combinators take every `ℕ → ℕ` parameter as a `PolyFueled c f` hypothesis,
whichever of its two roles it is in. A machine cannot read a `Nat.Partrec.Code`, and the two
roles separate here:

* **Reindexing** — `comp`, `ifZero`, `concatVar`, `tradeSlot`, `priceSlot`, `repeatTag`,
  `serialize_price`'s sentence index. The parameter names a *day*, and the machine rendering
  is a **unary ruler**, `(fun z => List.replicate (f z.length) false) ∈ Complexity.FP`: the
  day it names is rebuilt from that ruler's own length, and the ruler's `FP` witness already
  bounds `f n` polynomially, so no separate length side condition is asked for.
  `UnaryRuler.of_polyFueled` supplies the ruler from the fuel-metered hypothesis, and
  `UnaryRuler.id` is the identity case that `PolyFueled.id` plays on the fuel side.
* **A token in the stream** — `bigPayload`, `serialize_const_write`, `serialize_var`,
  `serialize_price`'s day. The parameter's *value* is written out, so the machine rendering
  is `MachineDigits f`, which is strictly more general than a ruler (a ruler's own word is
  polynomially long, so a ruler cannot name an exponential value, while `MachineDigits` can
  — that is what the write-out layer exists for). `MachineDigits.ofUnaryRuler` is the way in
  from a ruler when a caller has only that.

Both hypotheses are weaker than the fuel-metered `PolyFueled c f` they replace — the
inclusion runs fuel to machine and is all that is proved — so every combinator here is
stronger than its twin at every such argument.  No converse is provided, so whether either
weakening is *strict* is open; what is proved strict is the separation between the two
machine forms above.

## Length side conditions

None of these combinators asks for one. `Complexity.FP` membership already bounds an emitted
word's length by a polynomial in its argument (`Cobham.output_length_poly_of_mem_FP`), which
is what the streaming concatenation behind `concatVar` needs; the scaffolding tag blocks are
`FPFold.constFn_mem_FP`; and no token's *value* is bounded anywhere.

## The three fuel-side rows with no separate mirror

`BigSpliceStream.payload` is the value-bounded twin of `.bigPayload`; on this side there is
one token-value hypothesis, `MachineDigits`, so the two collapse into `bigPayload` and
`payload` would be a duplicate. `BigSpliceStream.serialize_const_comp` collapses into
`serialize_const_write` for the same reason. `BigSpliceStream.ofRpnSpliceStream` takes a
fuel-metered class as its hypothesis, which nothing on this side may do; the corresponding
inclusion is `BigSpliceStream.toMachine ∘ BigSpliceStream.ofRpnSpliceStream`, already
available and needing no name here.

## The value lane, and why this file never needs it

The mirror's one non-obvious member is **`MachineRatCodes.toMachineDigits`**, the machine
reading of `DigitRatCodes.toBigDigits`, which reassembles the flat code `⌜q n⌝` from the three
separate runs `MachineRatCodes` carries. `Encodable.encode` on `ℚ` pairs its components, and
`Nat.pair a b` is `b * b + a` or `a * a + a + b`, so the reassembly needs base-four
*multiplication* on digit words. `DigitFP.mulW` (`Framework/Machine/DigitArithFP.lean`)
supplies it: a Horner loop over the multiplier's digits under `Cobham.iterate_mem_FP`, with
the running product truncated at a ruler built from the two operands, so the state stays
bounded without any length bound on `addW`. The unary route (`TokenFold.uMul_mem_FP`) is
unsound for a class whose values may be exponential in the day and is deliberately not it.
`MachineDigits.natPair` and `MachineRatCodes.toMachineDigits`
(`Framework/Machine/WriteOutMachine.lean`) are built on it.

Nothing in this file consumes either, because `serialize_const_write` is stated at
`MachineDigits (fun n => ⌜q n⌝)` **directly** rather than at `MachineRatCodes q`: that is
the hypothesis it actually consumes, and it is exactly the shape of its fuel-side twin,
which takes `BigDigits (fun z => ⌜q z⌝)` rather than `DigitRatCodes q`. What consumes them is
outside this file: `ratCodeFeature_generated` (`Framework/Expectations.lean`),
`PairedWeighting.ofRatCodes` (`Construction/Quotation/DeferralFibre.lean`),
`sentenceMinusProbability_polySequence` (`Properties/TimelyLearning.lean`) and
`PolyPositiveWidths` (`Properties/Calibration.lean`) each reach `serialize_const_write` from a
*rational* certificate, and each takes `MachineRatCodes` and crosses by `.toMachineDigits`.
`ratCodeFeature_generated` is among them because this file sits upstream of
`Framework/Expectations.lean`: the `LUV` threshold section lives in the leaf
`Framework/Machine/ThresholdMachine.lean`, so `SpliceMachine` does not reach `Expectations`
and `Expectations` imports it instead.

The faithful §4 endpoints' *trader* is certified here too. They route through
`AffineCombination.PolySequence` and `PolySequence.buyBelowTrader_ec`, whose three emission
fields are `MachineSpliceStream` / `MachineSentenceCodes`, so that trader lands in `def:ec`
by `MachineSpliceStream.ec` and the endpoints consuming it take `[IsLogicalInductor]`.

`PolySequence.termCount_poly` is `UnaryRuler termCount` (`Framework/Machine/Ruler.lean`), so
**no field of that structure is fuel-metered**. The derived counts — the persistence,
triangular, mesh, gradual, bias-run and scheduled lanes build theirs by `segPrefix` and
`segLocate` — are assembled at the ruler class by the *same* device `concatVar` runs,
`TokenFold.concatUnaryPair_mem_FP` applied to a ruler rather than to a stream: one segment
ruler's output per block for the prefix sum (`UnaryRuler.segPrefix`), one mark per block that
fits for the locator (`UnaryRuler.segLocate`). No random access into a prefix table is needed,
and none is available.

## What the surface takes

The machine emission calculus is complete for what the §4 surface asks of it, and the surface
is stated on it: **no canonical endpoint takes a fuel- or value-metered emission premise**,
printed or through a boundary structure.  (The two non-emission premises,
`DeferralFunction.graph_fp` and `FeedbackTruth.FeedbackTruthComputation.computes`, render
the paper's own polynomial-in-the-output conditions, and are machine-metered too — read on
the unary pair whose length carries the bound; see the `dd:fuel` model card.) The Occam gate
compiler runs on this file's
combinators end to end, with its trader certified at `MachineSpliceStream.ec`, and the
conditioning lane's `condition_codes` fields are `MachineSentenceCodes`: the operational
witnesses carry a `def:ec` translation certificate only, so nothing there asks the fuel
calculus for a closure fact.

What is fuel-metered anywhere is deliberate and binds no endpoint premise: the two
ROI maturity schedules' `check_poly` — a schedule predicate, not a reindexer and not emitted
data — and the calibration classes `DigitRatCodes`, `BigDigits`, `DigitMachineCodes`,
`PolyMachineCodes`,
`PolyNatCodes` and `PolyArithmeticSourceSeq`, which exist as the fuel-side producer routes
and as the subjects of the strictness proofs. The converse inclusion is open, and
nothing on the paper surface waits on it.

## Inhabitation

A closure suite takes certificates and returns certificates, so it says nothing about what is
in the class. `Framework/Machine/Witnesses.lean` answers that separately:
`machineSpliceStream_atomTrade` is a trade frame carrying the day's own atom, and
`efficientlyComputable_buyAtomDaily` runs `ofSingleTradeBlocksBig` on a trader whose traded
sentence changes every day — from machine data throughout, with no fuel certificate in the
derivation. Both come with the lemma saying the family is not a constant sequence.

Everything here is supporting infrastructure rather than a paper claim, so the declarations
are `lemma`s and carry no `Paper node` line; the paper node they serve, `def:ec`, is carried
by `EfficientlyComputable` itself.
-/

namespace LogicalInduction

open Nat.Partrec.Code

-- `Nat.sqrt` is scoped irreducible: elaboration over paired indices otherwise loops in
-- `whnf` (the same reason `Framework/Emission/RpnSplice.lean` sets it).
attribute [local irreducible] Nat.sqrt

namespace MachineSpliceStream

/-- **A machine-metered stream with no sentence slots is spliceable by transparency**:
contraction leaves it unchanged. No side condition. Fuel-side twin:
`BigSpliceStream.ofTransparent`. -/
lemma ofTransparent {ts : ℕ → List ℕ} (h : MachineTokenStream ts)
    (ht : ∀ z, UnRpnTransparent (ts z)) : MachineSpliceStream ts :=
  ⟨ts, h, fun z => (ht z).contractsTo⟩

/-- **Congruence.** The contraction is transported pointwise; the stream is untouched. No
side condition. Fuel-side twin: `BigSpliceStream.of_eq`. -/
lemma of_eq {a b : ℕ → List ℕ} (h : MachineSpliceStream a) (hab : ∀ z, a z = b z) :
    MachineSpliceStream b := by
  obtain ⟨s, hs, hc⟩ := h
  exact ⟨s, hs, fun z => (hab z) ▸ hc z⟩

/-- **Concatenation**, the workhorse an emission is assembled from.
`MachineTokenStream.append` moves the word — `Cobham.appendFn_mem_FP` for the bits,
`TokenFold.BlockWF.append` for the splice discipline, `TokenFold.decodeBits_append` for the
decode — and `UnRpnContractsTo.append` composes the two contractions. No length side
condition; the block-completeness the split needs is the conjunct `MachineTokenStream`
carries. Fuel-side twin: `BigSpliceStream.append`. -/
lemma append {a b : ℕ → List ℕ} (ha : MachineSpliceStream a) (hb : MachineSpliceStream b) :
    MachineSpliceStream (fun z => a z ++ b z) := by
  obtain ⟨sa, hsa, hca⟩ := ha
  obtain ⟨sb, hsb, hcb⟩ := hb
  exact ⟨fun z => sa z ++ sb z, hsa.append hsb, fun z => (hca z).append (hcb z)⟩

/-- **Reindexing along a machine-readable map.** `MachineTokenStream.comp` moves the stream;
the contraction follows it unchanged. The reindexer arrives as a unary ruler, whose own `FP`
witness bounds `f n` polynomially, so no separate length side condition is asked for.
Fuel-side twin: `BigSpliceStream.comp`, which takes `PolyFueled c f`;
`UnaryRuler.of_polyFueled` converts one to the other. -/
lemma comp {ts : ℕ → List ℕ} (h : MachineSpliceStream ts) {f : ℕ → ℕ}
    (hf : UnaryRuler f) :
    MachineSpliceStream (fun z => ts (f z)) := by
  obtain ⟨s, hs, hc⟩ := h
  exact ⟨fun z => s (f z), hs.comp hf, fun z => hc (f z)⟩

/-- **Two-way dispatch on whether a test vanishes.** `MachineTokenStream.ifZero` selects
between the two words by comparing the test ruler's length with `0`
(`TokenFold.ifEqLen_mem_FP`), and the contraction is whichever branch's. The test arrives as
a unary ruler; no length side condition. Fuel-side twin: `BigSpliceStream.ifZero`. -/
lemma ifZero {s₀ s₁ : ℕ → List ℕ} (h₀ : MachineSpliceStream s₀) (h₁ : MachineSpliceStream s₁)
    {t : ℕ → ℕ}
    (ht : UnaryRuler t) :
    MachineSpliceStream (fun z => if t z = 0 then s₀ z else s₁ z) := by
  obtain ⟨a, ha, hca⟩ := h₀
  obtain ⟨b, hb, hcb⟩ := h₁
  refine ⟨fun z => if t z = 0 then a z else b z, ha.ifZero hb ht, fun z => ?_⟩
  by_cases hz : t z = 0
  · simpa [hz] using hca z
  · simpa [hz] using hcb z

/-- **Variable-count concatenation**: `cnt n` machine-metered segments, the `j`-th indexed
`Nat.pair n j`, concatenated on day `n`. `MachineTokenStream.concatVar` streams the word —
the fuel side's random-access scan into its own future output is not available to a machine
— and the contraction is composed by induction on the count, exactly the fuel proof's
induction, `UnRpnContractsTo` being a fact about token lists alone.

The count arrives as a unary ruler; the per-segment length side condition the fold demands
is discharged inside `MachineTokenStream.concatVar` from
`Cobham.output_length_poly_of_mem_FP`, so nothing is asked for here. Fuel-side twin:
`BigSpliceStream.concatVar`. -/
lemma concatVar {seg : ℕ → List ℕ} (hseg : MachineSpliceStream seg) {cnt : ℕ → ℕ}
    (hcnt : UnaryRuler cnt) :
    MachineSpliceStream (fun n =>
      (List.range (cnt n)).flatMap fun j => seg (Nat.pair n j)) := by
  obtain ⟨s, hs, hc⟩ := hseg
  refine ⟨fun n => (List.range (cnt n)).flatMap fun j => s (Nat.pair n j),
    hs.concatVar hcnt, fun n => ?_⟩
  have key : ∀ m : ℕ, UnRpnContractsTo
      ((List.range m).flatMap fun j => s (Nat.pair n j))
      ((List.range m).flatMap fun j => seg (Nat.pair n j)) := by
    intro m
    induction m with
    | zero => intro rest; simp
    | succ m ih =>
        rw [List.range_succ, List.flatMap_append, List.flatMap_append]
        simpa using ih.append (hc (Nat.pair n m))
  exact key (cnt n)

/-! ### Leaves and slots -/

/-- **A bare operator/close token as a spliceable stream.** The emitted word is the constant
`TokenFold.tokBits [t]`, so the certificate does not read the day at all; transparency is
`UnRpnTransparent.single`. No side condition. Fuel-side twin: `BigSpliceStream.tag`. -/
lemma tag (t : ℕ) (ht : t ≠ 0 ∧ t ≠ 1 ∧ t ≠ 6 ∧ t ≠ 7) :
    MachineSpliceStream (fun _ : ℕ => [t]) :=
  ofTransparent (MachineTokenStream.const [t]) (fun _ => UnRpnTransparent.single t ht)

/-- **A written-out payload chunk**: a `1`/`7` tag whose payload token is written out
digit by digit, so its value may be exponential in the day. The word is the constant tag
block appended to the value's own block (`MachineTokenStream.append` at a `MachineDigits`
certificate, which is by definition the one-token stream `fun n => [f n]`), and the chunk is
transparent by `UnRpnTransparent.payload`. No length side condition.

Fuel-side twin: `BigSpliceStream.bigPayload`. Its value-bounded sibling
`BigSpliceStream.payload` has no separate mirror — `MachineDigits` is the only token-value
hypothesis on this side, so the two collapse into this lemma;
`MachineDigits.ofUnaryRuler` is how a caller holding a ruler reaches it. -/
lemma bigPayload (t : ℕ) (ht : t = 1 ∨ t = 7) {f : ℕ → ℕ} (hf : MachineDigits f) :
    MachineSpliceStream (fun z => [t, f z]) :=
  ofTransparent
    (((MachineTokenStream.const [t]).append hf).of_eq (fun _ => rfl))
    (fun z => UnRpnTransparent.payload t (f z) ht)

/-- **A written-out sentence slot**: the price leaf `[0, ⌜φ (f m)⌝, f m]` on a machine-metered
sentence sequence. The sentence's block is spliced in where its Gödel code will stand and
`UnRpnContractsTo.priceChunk` contracts the splice; the trailing day token is the same
parameter read as a value, through `MachineDigits.ofUnaryRuler`.

The parameter is a unary ruler, in both of its roles at once, exactly as the fuel side takes
one `PolyFueled c f` for both. No length side condition. Fuel-side twin:
`BigSpliceStream.priceSlot`. -/
lemma priceSlot {φ : ℕ → Sentence} (hφ : MachineSentenceCodes φ) {f : ℕ → ℕ}
    (hf : UnaryRuler f) :
    MachineSpliceStream (fun m => [0, Encodable.encode (φ (f m)), f m]) := by
  obtain ⟨s, hs, hp⟩ := hφ
  refine ⟨fun m => 0 :: s (f m) ++ [f m], ?_,
    fun m => UnRpnContractsTo.priceChunk (hp (f m)) (f m)⟩
  exact (((MachineTokenStream.const [0]).append (hs.comp hf)).append
    (MachineDigits.ofUnaryRuler hf)).of_eq (fun m => by simp)

/-- **A written-out trade frame**: `[6, ⌜φ (f m)⌝]` on a machine-metered sentence sequence.
The constant splice marker `6` in front of the sentence's own block, contracted by
`UnRpnContractsTo.tradeChunk`. The reindexer arrives as a unary ruler; no length side
condition. Fuel-side twin: `BigSpliceStream.tradeSlot`. -/
lemma tradeSlot {φ : ℕ → Sentence} (hφ : MachineSentenceCodes φ) {f : ℕ → ℕ}
    (hf : UnaryRuler f) :
    MachineSpliceStream (fun m => [6, Encodable.encode (φ (f m))]) := by
  obtain ⟨s, hs, hp⟩ := hφ
  exact ⟨fun m => 6 :: s (f m),
    ((MachineTokenStream.const [6]).append (hs.comp hf)).of_eq (fun m => by simp),
    fun m => UnRpnContractsTo.tradeChunk (hp (f m))⟩

/-- **A replicated close/operator tag as a spliceable stream.** `concatVar` at the constant
one-token segment, the list identity being that a `flatMap` of singletons over
`List.range m` is `List.replicate m`. The count arrives as a unary ruler; no length side
condition. Fuel-side twin: `BigSpliceStream.repeatTag`. -/
lemma repeatTag (t : ℕ) (ht : t ≠ 0 ∧ t ≠ 1 ∧ t ≠ 6 ∧ t ≠ 7) {cnt : ℕ → ℕ}
    (hcnt : UnaryRuler cnt) :
    MachineSpliceStream (fun n => List.replicate (cnt n) t) := by
  have key : ∀ m : ℕ, ((List.range m).flatMap fun _ : ℕ => [t]) = List.replicate m t := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [List.range_succ, List.flatMap_append, ih, List.replicate_succ']
        simp
  exact ((tag t ht).concatVar hcnt).of_eq (fun n => key (cnt n))

/-! ### Serialization combinator mirrors

One member per `EF` constructor, mirroring `BigSpliceStream.serialize_*`: an emission
assembly written against that suite transfers by renaming combinators. Operator tails and
payload frames are transparent; only the price leaf opens a sentence slot. -/

/-- The `+` node, tag `2`, appended to its two arguments' serializations. Fuel-side twin:
`BigSpliceStream.serialize_add`. -/
lemma serialize_add {A B : ℕ → EF}
    (hA : MachineSpliceStream (fun z => (A z).serialize))
    (hB : MachineSpliceStream (fun z => (B z).serialize)) :
    MachineSpliceStream (fun z => (EF.add (A z) (B z)).serialize) :=
  ((hA.append hB).append (tag 2 (by norm_num))).of_eq (fun z => by simp [EF.serialize])

/-- The `*` node, tag `3`. Fuel-side twin: `BigSpliceStream.serialize_mul`. -/
lemma serialize_mul {A B : ℕ → EF}
    (hA : MachineSpliceStream (fun z => (A z).serialize))
    (hB : MachineSpliceStream (fun z => (B z).serialize)) :
    MachineSpliceStream (fun z => (EF.mul (A z) (B z)).serialize) :=
  ((hA.append hB).append (tag 3 (by norm_num))).of_eq (fun z => by simp [EF.serialize])

/-- The `max` node, tag `4`. Fuel-side twin: `BigSpliceStream.serialize_max`. -/
lemma serialize_max {A B : ℕ → EF}
    (hA : MachineSpliceStream (fun z => (A z).serialize))
    (hB : MachineSpliceStream (fun z => (B z).serialize)) :
    MachineSpliceStream (fun z => (EF.max (A z) (B z)).serialize) :=
  ((hA.append hB).append (tag 4 (by norm_num))).of_eq (fun z => by simp [EF.serialize])

/-- The reciprocal node, tag `5`, appended to its argument's serialization. Fuel-side twin:
`BigSpliceStream.serialize_safeRecip`. -/
lemma serialize_safeRecip {A : ℕ → EF}
    (hA : MachineSpliceStream (fun z => (A z).serialize)) :
    MachineSpliceStream (fun z => (EF.safeRecip (A z)).serialize) :=
  (hA.append (tag 5 (by norm_num))).of_eq (fun z => by simp [EF.serialize])

/-- The `let` node, tag `8`, appended to the bound expression's serialization followed by
the body's. Fuel-side twin: `BigSpliceStream.serialize_letE`. -/
lemma serialize_letE {X Body : ℕ → EF}
    (hX : MachineSpliceStream (fun z => (X z).serialize))
    (hBody : MachineSpliceStream (fun z => (Body z).serialize)) :
    MachineSpliceStream (fun z => (EF.letE (X z) (Body z)).serialize) :=
  ((hX.append hBody).append (tag 8 (by norm_num))).of_eq (fun z => by simp [EF.serialize])

/-- **A fixed rational constant.** Its chunk `[1, ⌜q⌝]` costs the same to write on every
day, so the emitter is `MachineDigits.const` inside `bigPayload` and reads no day at all. No
side condition. Fuel-side twin: `BigSpliceStream.serialize_const`. -/
lemma serialize_const (q : ℚ) :
    MachineSpliceStream (fun _ : ℕ => (EF.const q).serialize) :=
  (bigPayload 1 (Or.inl rfl) (MachineDigits.const (Encodable.encode q))).of_eq
    (fun _ => rfl)

/-- **A written-out rational constant.** The emitter knows `⌜q z⌝` only through its digits,
so `q z`'s Gödel code may be exponential in **magnitude** — the paper's `δ n = 2⁻ⁿ` is the
motivating case, whose denominator `2ⁿ` is exponential as a number.  Its emitted
representation stays polynomially **long**: that is exactly what the `MachineDigits`
hypothesis bounds, and the distinction between the two is what the write-out ladder exists
to keep.

The hypothesis is stated at `MachineDigits (fun n => ⌜q n⌝)` directly rather than at
`MachineRatCodes q`, because that is the hypothesis this lemma consumes and the shape its
fuel-side twin has. A caller holding the three-run `MachineRatCodes` form reaches it through
`MachineRatCodes.toMachineDigits`, which reassembles the flat code by
`MachineDigits.natPair` over `DigitFP.mulW` — the mirror of the route every fuel-side caller
takes through `DigitRatCodes.toBigDigits`.

No length side condition. Fuel-side twin: `BigSpliceStream.serialize_const_write`; its
value-bounded sibling `.serialize_const_comp` collapses into this one, `MachineDigits` being
the only token-value hypothesis on this side. -/
lemma serialize_const_write {q : ℕ → ℚ}
    (hq : MachineDigits fun z => Encodable.encode (q z)) :
    MachineSpliceStream (fun z => (EF.const (q z)).serialize) :=
  (bigPayload 1 (Or.inl rfl) hq).of_eq (fun _ => rfl)

/-- **A variable leaf**, tag `7`, whose index is written out digit by digit. No length side
condition. Fuel-side twin: `BigSpliceStream.serialize_var`, whose `PolyFueled cf f`
hypothesis reaches this shape through `BigDigits.of_polyFueled` and `BigDigits.toMachine`,
or a ruler-holding caller through `MachineDigits.ofUnaryRuler`. -/
lemma serialize_var {f : ℕ → ℕ} (hf : MachineDigits f) :
    MachineSpliceStream (fun z => (EF.var (f z)).serialize) :=
  (bigPayload 7 (Or.inr rfl) hf).of_eq (fun _ => rfl)

/-- **A written-out varying price leaf**: the sentence slot from a machine-metered block
stream, the day from a written-out index. The two parameters are in different roles — `sf`
reindexes the sentence family and so is a unary ruler, `df` is written into the stream as a
token and so is a `MachineDigits` certificate, which admits an exponentially large day
index where a ruler could not. No length side condition. Fuel-side twin:
`BigSpliceStream.serialize_price`, which meters both with `PolyFueled`. -/
lemma serialize_price {φ : ℕ → Sentence} (hφ : MachineSentenceCodes φ) {sf df : ℕ → ℕ}
    (hs : UnaryRuler sf)
    (hd : MachineDigits df) :
    MachineSpliceStream (fun z => (EF.price (φ (sf z)) (df z)).serialize) := by
  obtain ⟨s, hstream, hp⟩ := hφ
  refine ⟨fun z => 0 :: s (sf z) ++ [df z], ?_, fun z => ?_⟩
  · exact (((MachineTokenStream.const [0]).append (hstream.comp hs)).append hd).of_eq
      (fun z => by simp)
  · have hcontract := UnRpnContractsTo.priceChunk (hp (sf z)) (df z)
    exact fun rest => by simpa [EF.serialize] using hcontract rest

/-- **A transparent whole-serialization for price-free features.** A feature with no `price`
leaf opens no sentence slot, so its serialization contracts to itself
(`EF.serialize_unRpnTransparent`) and any machine-metered emission of it is spliceable. No
length side condition. Fuel-side twin: `BigSpliceStream.ofPriceFree`. -/
lemma ofPriceFree {A : ℕ → EF} (h : MachineTokenStream (fun z => (A z).serialize))
    (hfree : ∀ z, (A z).priceFree) :
    MachineSpliceStream (fun z => (A z).serialize) :=
  ofTransparent h (fun z => EF.serialize_unRpnTransparent (A z) (hfree z))

end MachineSpliceStream

/-! ## The trader capstones

`MachineSpliceStream.ec` is where the write-out lane meets `def:ec` itself: from
the point where the emitted word's decode is `serializeTrades (Tr.strat n).trades` onward,
the argument is the fuel proof of `BigSpliceStream.ec` term for term, because
`EfficientlyComputable` unfolds to
`strategyOfOutput n (F (unaryDay n)) = Tr.strat n` and `strategyOfOutput n w` is
`strategyOfTokens n (unRpn (TokenFold.decodeBits w))` definitionally. No adapter is needed.

The two constructors over it are the entry points a client actually uses. Their hypotheses
are the machine classes throughout — `MachineTokenStream` / `MachineSpliceStream` /
`MachineSentenceCodes` and unary rulers, never a fuel-metered class — so a client who never
writes a `Nat.Partrec.Code` can discharge them, and a client holding fuel certificates
reaches them through `BigSpliceStream.toMachine`, `BigSentenceCodes.toMachine` and
`UnaryRuler.of_polyFueled`. -/

/-- **The machine realization theorem**: a trader whose per-day trade serialization is
machine-metered spliceable is efficiently computable. The mirror of `BigSpliceStream.ec`, with no
polynomial bound on any emitted token's value. No length side condition. -/
lemma MachineSpliceStream.ec (Tr : Trader)
    (h : MachineSpliceStream (fun n => serializeTrades (Tr.strat n).trades)) :
    EfficientlyComputable Tr := by
  obtain ⟨s, hs, hc⟩ := h
  refine ec_of_machineTokenStream Tr hs (fun n => ?_)
  have hun : unRpn (s n) = serializeTrades (Tr.strat n).trades := (hc n).unRpn_eq
  rw [hun]
  have hdecode := deserializeTrades_serializeTrades (Tr.strat n).trades
  cases hS : Tr.strat n with
  | mk trades rank_le =>
      simp only [strategyOfTokens]
      rw [hS] at hdecode
      split
      · next hnone =>
          rw [hdecode] at hnone; exact absurd hnone (by simp)
      · next trades' hsome =>
          rw [hdecode] at hsome
          obtain rfl := Option.some.inj hsome
          rw [dif_pos rank_le]

/-- **Single-trade realization over machine data.** A trader whose day-`n` strategy is the
single trade `(f n, φ n)`, with a price-free coefficient stream and a machine-metered
sentence family, is efficiently computable. Every hypothesis is a machine class: no
`Nat.Partrec.Code`, no fuel clock.

The assembly is two steps — the trade frame `[6, ⌜φ n⌝]` at the identity ruler
(`MachineSpliceStream.tradeSlot` at `UnaryRuler.id`), appended to the coefficient stream —
and then `MachineSpliceStream.ec`. No length side condition. Fuel-side twin:
`PolyFueledTrader.ofSingleTradeBlocksBig` (`Framework/Emission/WriteOut.lean`). -/
lemma EfficientlyComputable.ofSingleTradeBlocksBig (Tr : Trader) (f : ℕ → EF)
    (φ : ℕ → Sentence)
    (hf : MachineTokenStream fun n => (f n).serialize)
    (hfree : ∀ n, (f n).priceFree)
    (hφ : MachineSentenceCodes φ)
    (hTr : ∀ n, (Tr.strat n).trades = [(f n, φ n)]) :
    EfficientlyComputable Tr := by
  have hfB : MachineSpliceStream (fun n => (f n).serialize) :=
    MachineSpliceStream.ofPriceFree hf hfree
  have hslot : MachineSpliceStream (fun n => [6, Encodable.encode (φ n)]) :=
    (MachineSpliceStream.tradeSlot hφ (f := fun n => n) UnaryRuler.id).of_eq (fun _ => rfl)
  refine MachineSpliceStream.ec Tr ((hfB.append hslot).of_eq (fun n => ?_))
  rw [hTr n]
  simp [serializeTrades]

/-- **Variable-count realization over machine data.** A trader playing `count n` trades on
day `n` (indexed `z = ⟨n, j⟩`), with a machine-metered spliceable coefficient stream and a
machine-metered sentence family, is efficiently computable. This is the machine reading of
`def:ec`'s trade-block constructor, and the route an exploiting-trader construction takes
when the number of trades grows with the day.

The count arrives as a unary ruler — a machine cannot take `PolyFueled c count`, `count`
not being a word function, and the ruler is exactly the iteration count the streaming
concatenation's fold consumes. `UnaryRuler.of_polyFueled` supplies it from a fuel-metered
count.

The assembly is the five steps of the fuel proof with the machine combinators in place of
the fuel ones: the trade frame at the identity ruler, appended to the coefficient stream,
`concatVar` over the count, `of_eq` against `serializeTrades_eq_flatMap`, and
`MachineSpliceStream.ec`. Only `MachineTokenStream.concatVar` is new content; everything
else is a rename. No price-freeness hypothesis on the coefficients is needed:
`MachineSpliceStream` already records how each coefficient block contracts. No length side
condition. Fuel-side twin: `PolyFueledTrader.ofTradeBlocksBig`. -/
lemma EfficientlyComputable.ofTradeBlocksBig (Tr : Trader)
    (count : ℕ → ℕ) (f : ℕ → EF) (φ : ℕ → Sentence)
    (hcount : UnaryRuler count)
    (hf : MachineSpliceStream fun z => (f z).serialize)
    (hφ : MachineSentenceCodes φ)
    (hTr : ∀ n, (Tr.strat n).trades =
      (List.range (count n)).map fun j => (f (Nat.pair n j), φ (Nat.pair n j))) :
    EfficientlyComputable Tr := by
  have hslot : MachineSpliceStream (fun z => [6, Encodable.encode (φ z)]) :=
    (MachineSpliceStream.tradeSlot hφ (f := fun n => n) UnaryRuler.id).of_eq (fun _ => rfl)
  refine MachineSpliceStream.ec Tr
    (((hf.append hslot).concatVar hcount).of_eq (fun n => ?_))
  rw [hTr n, serializeTrades_eq_flatMap]
  simp [List.flatMap_map]

end LogicalInduction
