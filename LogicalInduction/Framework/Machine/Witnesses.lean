import LogicalInduction.Framework.Machine.SpliceMachine

/-!
# Non-vacuity witnesses for the machine emission classes

`Framework/Machine/WriteOutMachine.lean` states six machine-metered emission classes —
`MachineTokenStream`, `MachineSentenceCodes`, `MachineSpliceStream`, `MachineDigits`,
`MachineMachineCodes`, `MachineRatCodes` — and `Framework/Machine/SentenceMachine.lean` and
`Framework/Machine/SpliceMachine.lean` carry their closure suites and the two trader
capstones. A closure suite proves nothing about inhabitation: every combinator there takes a
certificate and returns one, so a class with only the constant sequences in it would satisfy
all of them.

This file inhabits each class by a **constructed** sequence that genuinely varies with the
day, and states that variation as a lemma rather than leaving it to the reader. Each
*family* exhibited here has a `_nonconstant` companion saying it is not `fun _ => c` for any
`c`, which is the degenerate shape a non-vacuity claim can otherwise hide behind. The
companion is stated once per family, not once per witness: `machineTokenStream_atom` and
`machineSentenceCodes_atom` are the same atom family read at two classes and share
`machineSentenceCodes_atom_nonconstant`; `machineDigits_ratCode_two_pow_inv` is
`machineRatCodes_two_pow_inv`'s flat code and shares
`machineRatCodes_two_pow_inv_nonconstant`; and `machineTokenStream_marks` is the run
`machineDigits_tokenListNat_marks` names, covered by
`machineDigits_tokenListNat_marks_nonconstant`.

## What each witness exhibits

* `unaryRuler_triangle` — the *count* class `UnaryRuler`
  (`Framework/Machine/Ruler.lean`) at a day-varying count that is not one of its base cases:
  the triangular numbers `Σ_{j<n} j`, assembled by `UnaryRuler.segPrefix` over the segment
  layout whose `j`-th block has width `j`. This is the device the derived term counts of the
  persistence, triangular, mesh, gradual, bias-run and scheduled lanes run on, exercised on a
  family no constant sequence bounds.
* `machineDigits_id` — the day itself, reached from the *length* lane
  (`MachineDigits.ofUnaryRuler` at `UnaryRuler.id`): a value the machine knows only as a
  count of marks.
* `machineDigits_two_pow` — `2 ^ n`, reached from the fuel-metered `bigDigits_two_pow`
  through `BigDigits.toMachine`. Its *value* is exponential in the day, where a unary ruler's
  own word is polynomially long: the value/length asymmetry the write-out layer exists for,
  exhibited inside the machine class. That the ruler lane cannot reach this family is argued,
  not carried by a lemma here.
* `machineTokenStream_atom` — the one-token stream `[n + 5]`, the identity ruler's value and
  the constant `5` summed by `MachineDigits.add`, which is `rpn` of the day's atom.
* `machineSentenceCodes_atom` — the atom family `⌜aₙ⌝`, that stream read as a sentence
  through `MachineSentenceCodes.ofCanonical`.
* `machineSentenceCodes_conjRange` — the conjunction of the first `n` atoms, whose emitted
  *word* grows with the day: `MachineSentenceCodes.bigAnd` streams `n` conjunct blocks through
  `MachineTokenStream.concatVar`, so this is the variable-width machinery exercised on a
  family no constant sequence bounds.
* `machineMachineCodes_nest` and `machineRatCodes_two_pow_inv` — the two classes over
  `MachineDigits`, at the same families their fuel-metered strictness lemmas use
  (`Nat.Partrec.Code.nest`, `δ n = 2⁻ⁿ`), with `machineDigits_ratCode_two_pow_inv` the
  second of those pushed back down to a single value through
  `MachineRatCodes.toMachineDigits`.
* `machineSpliceStream_atomTrade` — a trade frame carrying the day's own atom, through
  `MachineSpliceStream.tradeSlot`.
* `buyAtomDaily` and `efficientlyComputable_buyAtomDaily` — the capstone: a trader whose
  day-`n` strategy trades a *different* sentence each day, certified at `def:ec`'s own class
  through `EfficientlyComputable.ofSingleTradeBlocksBig`. No fuel certificate,
  `Nat.Partrec.Code` or `PolyFueledTrader` hypothesis appears anywhere in that
  derivation — the whole route is machine data.

## What these do not claim

Nothing here is a paper node: the classes are the write-out lane's machine readings, and
these are their inhabitation exhibits. Nor is any of them a converse — the three witnesses
that start from a fuel-metered family (`machineDigits_two_pow`, `machineMachineCodes_nest`,
`machineRatCodes_two_pow_inv`) cross the forward bridges only, and the rest are built from
machine data alone.
-/

namespace LogicalInduction

open LO.Propositional

/-- A family that takes two different values is not a constant sequence. The `_nonconstant`
companions below are all this lemma at an explicit pair of days. -/
private lemma ne_const {α : Type*} {f : ℕ → α} {a b : ℕ} (hab : f a ≠ f b) (c : α) :
    f ≠ fun _ => c :=
  fun h => hab (by rw [h])

/-! ## The count class

`UnaryRuler` is the machine reading of a fuel-metered count. Its closure calculus is what
`AffineCombination.PolySequence.termCount_poly` is discharged from, so the interesting
inhabitant is not a constant or the identity — those are lemmas of the calculus — but a count
the *prefix scan* produces. -/

/-- **A variable-width prefix sum is a unary ruler.** The segment layout whose `j`-th block
has width `j`, scanned through `n` blocks, is the triangular number `Σ_{j<n} j`; the
certificate is `UnaryRuler.segPrefix` at the segment ruler `UnaryRuler.unpairSnd`, composed
with the diagonal `n ↦ ⟨n,n⟩`. Nothing fuel-metered appears in the derivation.

This is the shape every derived term count in the development has — a prefix sum over a
segment layout whose widths are themselves a ruler — so it inhabits the class at the device
`AffineCombination.PolySequence.termCount_poly` is stated over, not merely at a base
case. -/
lemma unaryRuler_triangle :
    UnaryRuler (fun n => segPrefix (fun q => q.unpair.2) n n) :=
  ((UnaryRuler.segPrefix UnaryRuler.unpairSnd).comp
    (UnaryRuler.id.pair UnaryRuler.id)).of_eq (fun n => by simp)

/-- The triangular count is not a constant sequence: it is `0` on day `0` and `1` on day
`2`. -/
lemma unaryRuler_triangle_nonconstant (c : ℕ) :
    (fun n => segPrefix (fun q => q.unpair.2) n n) ≠ fun _ => c := by
  refine ne_const (f := fun n => segPrefix (fun q : ℕ => q.unpair.2) n n)
    (a := 0) (b := 2) ?_ c
  norm_num [segPrefix]

/-! ## The value classes -/

/-- **The day itself is machine-metered.** `MachineDigits.ofUnaryRuler` at the identity
ruler: the certificate reads its argument's length and nothing else, and
`TokenFold.unaryBlock` converts those `n` marks to base-four digits before appending the
terminator, so the emitted word is `O(log n)` bits long. This is the machine rendering of a
`PolyFueled c f` parameter in a token position, inhabited at `f = id`. -/
lemma machineDigits_id : MachineDigits (fun n => n) :=
  MachineDigits.ofUnaryRuler (f := fun n => n) UnaryRuler.id

/-- The day is not a constant sequence: days `0` and `1` differ. -/
lemma machineDigits_id_nonconstant (c : ℕ) : (fun n : ℕ => n) ≠ fun _ => c :=
  ne_const (f := fun n : ℕ => n) (a := 0) (b := 1) (by norm_num) c

/-- **An exponential value is machine-metered.** `bigDigits_two_pow` written out and carried
across `BigDigits.toMachine`. The point is not merely that the family is non-constant but
that its *values* are exponential in the day, where a unary ruler's own word is polynomially
long — so the ruler lane and the written-value lane are inhabited by genuinely different
families. That `MachineDigits.ofUnaryRuler` cannot reach this one is argued, not carried by a
lemma. -/
lemma machineDigits_two_pow : MachineDigits (fun n => 2 ^ n) :=
  BigDigits.toMachine bigDigits_two_pow

/-- `2 ^ n` is not a constant sequence: `2 ^ 0 = 1` and `2 ^ 1 = 2`. -/
lemma machineDigits_two_pow_nonconstant (c : ℕ) : (fun n : ℕ => 2 ^ n) ≠ fun _ => c :=
  ne_const (f := fun n : ℕ => 2 ^ n) (a := 0) (b := 1) (by norm_num) c

/-- **A machine-code family is machine-metered.** `Nat.Partrec.Code.nest` — the left-nested
spine `nest 0 = zero`, `nest (n+1) = pair (nest n) zero` — has poly-fueled digit access to
its source number (`bigDigits_sourceNat_nest`), so it crosses `DigitMachineCodes.toMachine`.
It is the same family `digitMachineCodes_nest_not_polyMachineCodes` uses to separate the
write-out class from the whole-value one, so what inhabits the machine class here is a family
the whole-value class provably excludes. -/
lemma machineMachineCodes_nest : MachineMachineCodes Nat.Partrec.Code.nest :=
  DigitMachineCodes.toMachine Nat.Partrec.Code.bigDigits_sourceNat_nest

/-- The `nest` family is not a constant sequence: `nest 0` is `zero` and `nest 1` is a
`pair` node. -/
lemma machineMachineCodes_nest_nonconstant (c : Nat.Partrec.Code) :
    Nat.Partrec.Code.nest ≠ fun _ => c :=
  ne_const (f := Nat.Partrec.Code.nest) (a := 0) (b := 1)
    (by simp [Nat.Partrec.Code.nest]) c

/-- **A rational family is machine-metered.** The paper's own tolerance sequence
`δ n = 2⁻ⁿ`, carried across `DigitRatCodes.toMachine` field for field. Its numerator run is
constant and its denominator run is `machineDigits_two_pow`'s, so the three-run split of
`MachineRatCodes` is inhabited by a family whose code `⟪2, 2ⁿ⟫` is exponential — the family
`digitRatCodes_two_pow_inv_not_polyRatCodes` uses to exclude `PolyRatCodes`. -/
lemma machineRatCodes_two_pow_inv :
    MachineRatCodes (fun n => (((2 ^ n : ℕ) : ℚ))⁻¹) :=
  DigitRatCodes.toMachine digitRatCodes_two_pow_inv

/-- **A rational's flat code is machine-metered.** `machineRatCodes_two_pow_inv` pushed
through `MachineRatCodes.toMachineDigits`: the three separate runs are reassembled into the
single value `⌜δ n⌝`, exponential in the day. This is the bridge `DigitFP.mulW` unblocks,
exercised on the family it exists for. -/
lemma machineDigits_ratCode_two_pow_inv :
    MachineDigits (fun n => Encodable.encode ((((2 ^ n : ℕ) : ℚ))⁻¹)) :=
  machineRatCodes_two_pow_inv.toMachineDigits

/-- `δ n = 2⁻ⁿ` is not a constant sequence: `δ 0 = 1` and `δ 1 = 1/2`. -/
lemma machineRatCodes_two_pow_inv_nonconstant (c : ℚ) :
    (fun n => (((2 ^ n : ℕ) : ℚ))⁻¹) ≠ fun _ => c :=
  ne_const (f := fun n => (((2 ^ n : ℕ) : ℚ))⁻¹) (a := 0) (b := 1) (by norm_num) c

/-! ## The token and sentence classes -/

/-- **A day-varying token stream.** `rpn` of the day's atom is the one-token list `[n + 5]`,
which is `MachineDigits.add` of the identity ruler's value and the constant `5`. Nothing
constant emits it: the token's value grows with the day. -/
lemma machineTokenStream_atom :
    MachineTokenStream (fun n => rpn (Formula.atom n : Sentence)) :=
  MachineTokenStream.of_eq (machineDigits_id.add (MachineDigits.const 5)) (fun _ => rfl)

/-- **The atom family is machine-metered.** `MachineSentenceCodes.ofCanonical` at the stream
above: the emitted block is the canonical Polish word of `⌜aₙ⌝`. This is the smallest sentence
family that varies with the day, and it is what the splice and trader witnesses below are
built over. -/
lemma machineSentenceCodes_atom :
    MachineSentenceCodes (fun n => (Formula.atom n : Sentence)) :=
  MachineSentenceCodes.ofCanonical machineTokenStream_atom

/-- The atom family is not a constant sequence: `a₀` and `a₁` are different sentences. -/
lemma machineSentenceCodes_atom_nonconstant (c : Sentence) :
    (fun n => (Formula.atom n : Sentence)) ≠ fun _ => c :=
  ne_const (f := fun n => (Formula.atom n : Sentence)) (a := 0) (b := 1) (by simp) c

/-- **A sentence family whose emitted word grows with the day.** The conjunction of the first
`n` atoms, assembled by `MachineSentenceCodes.bigAnd`: the conjunct stream is the atom family
reindexed by `Nat.unpair.2` and the width is the identity ruler, so the emitted word is `n`
conjunct blocks streamed through `MachineTokenStream.concatVar` followed by the block for `⊤`.

This is the witness that matters for the class's non-degeneracy. Three lengths have to be
kept apart. `machineSentenceCodes_atom` varies in a token's *value* at a fixed **token
count** — its decoded run is the one-element list `[n + 5]` on every day, though the emitted
bit word must grow to name an unbounded token. This one varies in the token count itself:
`n` conjunct blocks on day `n`. It is the emitted word's **bit length** that the class's
polynomial bounds, and only the token count is constant in the first witness. -/
lemma machineSentenceCodes_conjRange :
    MachineSentenceCodes
      (fun n => sentenceConjunction ((List.range n).map (fun j => (Formula.atom j : Sentence)))) :=
  MachineSentenceCodes.bigAnd
    (D := fun _ j => (Formula.atom j : Sentence))
    (machineSentenceCodes_atom.comp (f := fun m => m.unpair.2)
      (UnaryRuler.unpairSnd))
    (cnt := fun n => n) UnaryRuler.id

/-- The growing conjunction is not a constant sequence: day `0` emits the empty conjunction
`⊤` and day `1` emits `a₀ ⋏ ⊤`. -/
lemma machineSentenceCodes_conjRange_nonconstant (c : Sentence) :
    (fun n => sentenceConjunction
      ((List.range n).map (fun j => (Formula.atom j : Sentence)))) ≠ fun _ => c :=
  ne_const
    (f := fun n => sentenceConjunction
      ((List.range n).map (fun j => (Formula.atom j : Sentence))))
    (a := 0) (b := 1) (by simp [sentenceConjunction]) c

/-! ## The splice class and the trader capstone -/

/-- **A day-varying spliceable stream.** The trade frame `[6, ⌜aₙ⌝]` on the atom family, at
the identity ruler: `MachineSpliceStream.tradeSlot` splices the sentence's block in where its
Gödel code stands, and the contraction is `UnRpnContractsTo.tradeChunk`. The emitted frame
differs from day to day because the spliced sentence does. -/
lemma machineSpliceStream_atomTrade :
    MachineSpliceStream (fun n => [6, Encodable.encode (Formula.atom n : Sentence)]) :=
  MachineSpliceStream.tradeSlot machineSentenceCodes_atom (f := fun n => n) UnaryRuler.id

/-- The trade frame is not a constant sequence: `⌜a₀⌝ ≠ ⌜a₁⌝`, `Encodable.encode` being
injective. -/
lemma machineSpliceStream_atomTrade_nonconstant (c : List ℕ) :
    (fun n => [6, Encodable.encode (Formula.atom n : Sentence)]) ≠ fun _ => c :=
  ne_const (f := fun n => [6, Encodable.encode (Formula.atom n : Sentence)])
    (a := 0) (b := 1) (by simp) c

/-- A trader that buys one share of the day's *own* atom: its day-`n` strategy is the single
trade `(1, ⌜aₙ⌝)`, so the sentence it trades changes every day. Written here rather than in a
test file because `efficientlyComputable_buyAtomDaily` is a non-vacuity witness for
`def:ec` and belongs beside the class it inhabits. -/
def buyAtomDaily : Trader where
  strat n :=
    { trades := [(EF.const 1, (Formula.atom n : Sentence))]
      rank_le := by simp }

/-- The trader's strategy genuinely varies with the day: day `0` trades `⌜a₀⌝` and day `1`
trades `⌜a₁⌝`. -/
lemma buyAtomDaily_nonconstant :
    (buyAtomDaily.strat 0).trades ≠ (buyAtomDaily.strat 1).trades := by
  simp [buyAtomDaily]

/-- **The capstone witness: `def:ec` contains a trader whose strategy varies
with the day.** `EfficientlyComputable.ofSingleTradeBlocksBig` at the constant coefficient
stream and the atom family, whose certificate is `machineSentenceCodes_atom`.

The derivation is machine data throughout: no `Nat.Partrec.Code`, no `PolyFueled`, no
`PolyFueledTrader` hypothesis and no appeal to `PolyFueledTrader.toEfficientlyComputable` appears
in it. So `def:ec` is inhabited on its own terms, not only as the image of the fuel
class under the bridge. -/
lemma efficientlyComputable_buyAtomDaily : EfficientlyComputable buyAtomDaily :=
  EfficientlyComputable.ofSingleTradeBlocksBig buyAtomDaily (fun _ => EF.const 1)
    (fun n => (Formula.atom n : Sentence))
    (MachineTokenStream.const (EF.const 1).serialize)
    (fun _ => trivial)
    machineSentenceCodes_atom
    (fun _ => rfl)

/-! ## The delivery interface

`MachineDigits.ofTokenListNat` (`Framework/Machine/WriteOutMachine.lean`) turns an emitted
token run into the machine-metered *name* of that run.  Its inhabitation is separate from
its statement, and the witness below is a run whose length grows with the day, so the named
value grows exponentially — which is the point of naming by write-out rather than by
value. -/

/-- A day-varying emitted token run: `n` copies of the token `1`, streamed by
`MachineTokenStream.concatVar` at the identity ruler. -/
lemma machineTokenStream_marks : MachineTokenStream (fun n => List.replicate n 1) :=
  MachineTokenStream.of_eq
    (MachineTokenStream.concatVar (MachineTokenStream.const [1]) UnaryRuler.id)
    (fun n => by rw [TokenFold.flatMap_const_singleton, List.length_range])

/-- **The delivery interface is inhabited at a day-varying run.**  The name of `n` marks is
`Nat.ofDigits 64 (1^n ++ [63])`, which grows like `64 ^ n` — a value no unary ruler reaches,
carried by a certificate whose emitted word is linear in the day. -/
lemma machineDigits_tokenListNat_marks :
    MachineDigits (fun n => tokenListNat (List.replicate n 1)) :=
  MachineDigits.ofTokenListNat machineTokenStream_marks
    (fun n t ht => by rw [List.eq_of_mem_replicate ht]; norm_num)

/-- The name of `n` marks is not a constant sequence: days `0` and `1` differ. -/
lemma machineDigits_tokenListNat_marks_nonconstant (c : ℕ) :
    (fun n => tokenListNat (List.replicate n 1)) ≠ fun _ => c := by
  refine ne_const (a := 0) (b := 1) (fun h => ?_) c
  have hlt : ∀ (k : ℕ), ∀ t ∈ List.replicate k 1, t < 63 :=
    fun k t ht => by rw [List.eq_of_mem_replicate ht]; norm_num
  have := tokenListNat_injective (hlt 0) (hlt 1) h
  simp at this

end LogicalInduction
