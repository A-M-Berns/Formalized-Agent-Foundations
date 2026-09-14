import LogicalInduction.Framework.Machine.WriteOutMachine

/-!
# The sentence write-out class, machine reading: its combinators

`MachineSentenceCodes` (`Framework/Machine/WriteOutMachine.lean`) is `BigSentenceCodes` with
its `BigTokenStream` replaced by `MachineTokenStream`: a `Complexity.FP` function of the
unary day emits a block-complete word whose tokens are a self-delimiting RPN block parsing
to `φ d`. This file carries the combinator suite, mirroring `BigSentenceCodes.*`
(`Framework/Emission/WriteOut.lean`) one for one.

Because both classes are stated *over* their token stream, every proof here has the same
shape as its fuel-metered twin: `obtain` the underlying stream, run the identical
`MachineTokenStream` closure lemma in place of the `BigTokenStream` one, and reuse the
parse argument — `parseRpn_cons`, `parseRpn_block_head`, `parseRpn_mono`,
`parseRpn_conjChain` — verbatim, those being facts about token lists and nothing else.

## What a `ℕ → ℕ` parameter becomes

The fuel-metered combinators take their reindexers, dispatch tests and segment counts as
`PolyFueled c f` hypotheses. A machine cannot read a `Nat.Partrec.Code`, so on this side
each such parameter is a **unary ruler** — `(fun z => List.replicate (f z.length) false) ∈
Complexity.FP` — which is weaker than the fuel-metered hypothesis, being supplied from it by
`UnaryRuler.of_polyFueled`. The machine combinators are therefore stronger than their
fuel-metered counterparts at every such argument. Only that inclusion is proved: no converse
is provided, and none is claimed, so whether the weakening is *strict* is left open.

`modDispatch` is the one place where the ruler is not a hypothesis: its reindexer and its
`k` tests are built inside the proof from `divmodc_polyFueled` and friends, exactly as the
fuel-metered proof builds them, and each is converted to a ruler on the spot.

## Length side conditions

None of these combinators asks for one. `Complexity.FP` membership already bounds an
emitted word's length by a polynomial in its argument
(`Cobham.output_length_poly_of_mem_FP`), which is what the streaming concatenation behind
`bigAnd` needs; the constant scaffolding blocks are `FPFold.constFn_mem_FP`; and no token's
*value* is bounded anywhere, which is the whole point of the write-out layer.

## The asymmetry, and where the threshold interfaces live

This file mirrors `BigSentenceCodes.*` and nothing else; it knows about token streams,
parses and rulers, and it does not know what a `LUV` is.  The machine readings of the two
`def:ec` threshold interfaces — `LUV.MachineThresholdCodes` and
`LUV.MachineThresholdCodeSeq`, together with the two `toMachine` bridges — are therefore
**not** here.  They are in `Framework/Machine/ThresholdMachine.lean`, the one leaf of
`Framework/Machine/` that imports `Framework/Expectations.lean`.

That split is load-bearing rather than tidy.  `LUV` is declared in
`Framework/Expectations.lean`, so a threshold reading stated here would put this file — and
with it `SpliceMachine` and `Witnesses` — downstream of `Expectations`, which could then use
no machine combinator at all.  The concrete consequence is visible at
`Framework/Expectations.lean`'s own `def:ece` constructors: they are stated at
`MachineRatCodes` because they reach `MachineSpliceStream.serialize_const_write`, which the
import edge `Expectations → Framework/Machine/SpliceMachine.lean` is what allows.  The rule:
nothing in this file, in `SpliceMachine` or in `Witnesses` may mention `LUV` or anything else
from `Expectations`; such a statement belongs in `ThresholdMachine`.

## Not mirrored

`or` and `imp` exist only at the token-metered `RpnSentenceCodes`, never at
`BigSentenceCodes`, so there is nothing here for them to mirror; the tag arithmetic is
`and`'s at tags `4` and `2`.  `bigOr` is the exception: the `thm:ccee` mesh product needs a
disjunction whose width grows with the index, and it is the one place a machine-metered
consumer reaches for one, so it *is* mirrored here (off `parseRpn_disjChain`, the same parse
law `RpnSentenceCodes.bigOr` runs).

## Inhabitation

Closure says nothing about what is in the class. `Framework/Machine/Witnesses.lean` answers
that separately: `machineSentenceCodes_atom` is the atom family `⌜aₙ⌝`, and
`machineSentenceCodes_conjRange` is the conjunction of the first `n` atoms — a family whose
emitted *word* grows with the day, which is the quantity the class's polynomial bounds. Each
comes with the lemma saying it is not a constant sequence.

Everything in this file is supporting infrastructure rather than a paper claim, so the
declarations are `lemma`s and carry no `Paper node` line.
-/

namespace LogicalInduction

-- `Nat.sqrt` is scoped irreducible: `PolyFueled` elaboration over paired inputs otherwise
-- loops in `whnf` (the same reason `Framework/Emission/RpnSplice.lean` sets it).
attribute [local irreducible] Nat.sqrt

namespace MachineSentenceCodes

/-- **A machine-metered canonical Polish stream certifies the sequence.** The emitted
tokens are `rpn (φ d)` itself, which `parseRpn_rpn` parses to `φ d` with nothing left over.
Side condition: none — the symbol count is whatever the `FP` witness emits, and individual
symbols may carry values exponential in the day. Fuel-side twin:
`BigSentenceCodes.ofCanonical`. -/
lemma ofCanonical {φ : ℕ → Sentence}
    (h : MachineTokenStream fun n => rpn (φ n)) : MachineSentenceCodes φ :=
  ⟨_, h, fun n => by
    simpa using parseRpn_rpn (φ n) [] (le_refl (rpn (φ n)).length)⟩

/-- **A value-bounded code sequence is machine-metered.** The composition of the fuel-side
adapter `BigSentenceCodes.ofPolySentenceCodes` with the bridge `BigSentenceCodes.toMachine`,
so a caller holding a `PolySentenceCodes` certificate need not name both. Side condition:
none beyond the hypothesis. Fuel-side twin: `BigSentenceCodes.ofPolySentenceCodes`. -/
lemma ofPolySentenceCodes {φ : ℕ → Sentence} (h : PolySentenceCodes φ) :
    MachineSentenceCodes φ :=
  (BigSentenceCodes.ofPolySentenceCodes h).toMachine

/-- **Congruence.** The parse condition is transported pointwise; the stream is untouched.
No side condition. Fuel-side twin: `BigSentenceCodes.of_eq`. -/
lemma of_eq {φ ψ : ℕ → Sentence} (h : MachineSentenceCodes φ) (hφψ : ∀ n, φ n = ψ n) :
    MachineSentenceCodes ψ := by
  obtain ⟨s, hs, hp⟩ := h
  exact ⟨s, hs, fun n => (hφψ n) ▸ hp n⟩

/-- **Reindexing along a machine-readable map.** `MachineTokenStream.comp` moves the
stream; the parse condition follows it unchanged. The reindexer arrives as a unary ruler,
whose own `FP` witness bounds `f n` polynomially — so no separate length side condition is
asked for. Fuel-side twin: `BigSentenceCodes.comp`, which takes `PolyFueled c f` instead;
`UnaryRuler.of_polyFueled` converts one to the other. -/
lemma comp {φ : ℕ → Sentence} (h : MachineSentenceCodes φ) {f : ℕ → ℕ}
    (hf : UnaryRuler f) :
    MachineSentenceCodes (fun z => φ (f z)) := by
  obtain ⟨s, hs, hp⟩ := h
  exact ⟨fun z => s (f z), hs.comp hf, fun z => hp (f z)⟩

/-- **A constant sentence is machine-metered.** Its canonical Polish run is a fixed token
list, so the emitter is `MachineTokenStream.const` and reads no day at all. No side
condition. Fuel-side twin: `BigSentenceCodes.const` — which routes through
`RpnSentenceCodes.const`, where this one is machine-native. -/
lemma const (φ : Sentence) : MachineSentenceCodes (fun _ => φ) :=
  ofCanonical (MachineTokenStream.const (rpn φ))

/-- **Two-way dispatch on whether a test vanishes.** `MachineTokenStream.ifZero` selects
between the two block streams, and the parse condition is whichever branch's. The test
arrives as a unary ruler; no length side condition. Fuel-side twin:
`BigSentenceCodes.ifZero`, whose `PolyFueled ct t` hypothesis reaches this shape through
`UnaryRuler.of_polyFueled`. -/
lemma ifZero {φ ψ : ℕ → Sentence} (hφ : MachineSentenceCodes φ) (hψ : MachineSentenceCodes ψ)
    {t : ℕ → ℕ}
    (ht : UnaryRuler t) :
    MachineSentenceCodes (fun z => if t z = 0 then φ z else ψ z) := by
  obtain ⟨a, ha, hpa⟩ := hφ
  obtain ⟨b, hb, hpb⟩ := hψ
  refine ⟨fun z => if t z = 0 then a z else b z, ha.ifZero hb ht, fun z => ?_⟩
  by_cases hz : t z = 0
  · simpa [hz] using hpa z
  · simpa [hz] using hpb z

/-- **Conjunction.** The fixed `⋏` tag `3` in front of the two blocks, which the prefix
parser consumes in order; the tag block is `MachineTokenStream.const` and the splice is
`MachineTokenStream.append`, whose block-completeness discipline is exactly what
`MachineTokenStream` carries the `TokenFold.BlockWF` conjunct for. No length side
condition. Fuel-side twin: `BigSentenceCodes.and`, whose parse argument this reuses
verbatim. -/
lemma and {φ ψ : ℕ → Sentence} (hφ : MachineSentenceCodes φ) (hψ : MachineSentenceCodes ψ) :
    MachineSentenceCodes (fun z => φ z ⋏ ψ z) := by
  obtain ⟨a, ha, hpa⟩ := hφ
  obtain ⟨b, hb, hpb⟩ := hψ
  refine ⟨fun z => 3 :: (a z ++ b z),
    (((MachineTokenStream.const [3]).append ha).append hb).of_eq (fun z => by simp),
    fun z => ?_⟩
  have hlen : (3 :: (a z ++ b z)).length = (a z).length + (b z).length + 1 := by simp
  rw [hlen, parseRpn_cons]
  rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]
  rw [parseRpn_block_head (hpa z) (b z) (by omega)]
  simp only [Option.bind_some]
  rw [parseRpn_mono (b z) (show (b z).length ≤ (a z).length + (b z).length by omega)
    (hpb z)]
  rfl

/-- **Negation.** Foundation spells `∼φ` as `φ 🡒 ⊥` definitionally and `rpn` tags an
implication with `2`, so this is `and`'s argument at tag `2` with the constant `⊥` block as
the second stream. No length side condition. Fuel-side twin: `BigSentenceCodes.neg`. -/
lemma neg {φ : ℕ → Sentence} (hφ : MachineSentenceCodes φ) :
    MachineSentenceCodes (fun z => ∼(φ z)) := by
  obtain ⟨a, ha, hpa⟩ := hφ
  obtain ⟨b, hb, hpb⟩ := MachineSentenceCodes.const (⊥ : Sentence)
  refine ⟨fun z => 2 :: (a z ++ b z),
    (((MachineTokenStream.const [2]).append ha).append hb).of_eq (fun z => by simp),
    fun z => ?_⟩
  have hlen : (2 :: (a z ++ b z)).length = (a z).length + (b z).length + 1 := by simp
  rw [hlen, parseRpn_cons]
  rw [if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]
  rw [parseRpn_block_head (hpa z) (b z) (by omega)]
  simp only [Option.bind_some]
  rw [parseRpn_mono (b z) (show (b z).length ≤ (a z).length + (b z).length by omega)
    (hpb z)]
  rfl

/-- **Variable-width conjunction.** `D z j` is the `j`-th conjunct at index `z`, presented
by one machine-metered block stream on the paired index, and `cnt z` conjuncts are taken.
The emitted block is `cnt z` `⋏`-tagged conjunct blocks followed by the three-token
constant `[2, 0, 0]` (the block for `⊤`), assembled by `MachineTokenStream.concatVar` —
which streams the concatenation rather than indexing into it, a machine having no random
access to its own future output.

The count arrives as a unary ruler. The per-segment length side condition `concatVar`
demands is discharged inside it from `Cobham.output_length_poly_of_mem_FP`, so nothing is
asked for here; no positivity hypothesis on `cnt` is needed either, the empty width folding
to `⊤`. Fuel-side twin: `BigSentenceCodes.bigAnd`, whose `parseRpn_conjChain` argument this
reuses verbatim. -/
lemma bigAnd {D : ℕ → ℕ → Sentence}
    (hD : MachineSentenceCodes fun m => D m.unpair.1 m.unpair.2)
    {cnt : ℕ → ℕ}
    (hcnt : UnaryRuler cnt) :
    MachineSentenceCodes (fun z => sentenceConjunction ((List.range (cnt z)).map (D z))) := by
  obtain ⟨b, hb, hpb⟩ := hD
  have hseg : MachineTokenStream (fun m => 3 :: b m) :=
    ((MachineTokenStream.const [3]).append hb).of_eq (fun m => by simp)
  refine ⟨fun z => ((List.range (cnt z)).flatMap fun j => 3 :: b (Nat.pair z j)) ++ [2, 0, 0],
    ((hseg.concatVar hcnt).append (MachineTokenStream.const [2, 0, 0])).of_eq
      (fun z => rfl), fun z => ?_⟩
  have hblk : ∀ j, parseRpn (b (Nat.pair z j)).length (b (Nat.pair z j)) =
      some (D z j, []) := by
    intro j
    simpa using hpb (Nat.pair z j)
  have := parseRpn_conjChain (fun j => b (Nat.pair z j)) (fun j => D z j) hblk
    (cnt z) 0 []
    ((((List.range (cnt z)).flatMap fun j => 3 :: b (Nat.pair z (0 + j))) ++
      2 :: 0 :: 0 :: []).length)
    le_rfl
  simpa using this

/-- **Variable-width disjunction.** The `⋎` mirror of `bigAnd`: `cnt z` `⋎`-tagged disjunct
blocks followed by the single `⊥` token `0`, read by the prefix parser as the
right-associated `sentenceDisjunction` (`parseRpn_disjChain`, shared verbatim with
`RpnSentenceCodes.bigOr`, which is the only other class this width-varying disjunction is
stated at — `BigSentenceCodes` has no `bigOr`).

The count arrives as a unary ruler, and `MachineTokenStream.concatVar` discharges its own
per-segment length side condition, exactly as in `bigAnd`. This is what the `thm:ccee` mesh
product needs: the width of the disjunction grows with the index, so its block cannot be a
fixed tuple of segments. -/
lemma bigOr {D : ℕ → ℕ → Sentence}
    (hD : MachineSentenceCodes fun m => D m.unpair.1 m.unpair.2)
    {cnt : ℕ → ℕ}
    (hcnt : UnaryRuler cnt) :
    MachineSentenceCodes (fun z => sentenceDisjunction ((List.range (cnt z)).map (D z))) := by
  obtain ⟨b, hb, hpb⟩ := hD
  have hseg : MachineTokenStream (fun m => 4 :: b m) :=
    ((MachineTokenStream.const [4]).append hb).of_eq (fun m => by simp)
  refine ⟨fun z => ((List.range (cnt z)).flatMap fun j => 4 :: b (Nat.pair z j)) ++ [0],
    ((hseg.concatVar hcnt).append (MachineTokenStream.const [0])).of_eq
      (fun z => rfl), fun z => ?_⟩
  have hblk : ∀ j, parseRpn (b (Nat.pair z j)).length (b (Nat.pair z j)) =
      some (D z j, []) := by
    intro j
    simpa using hpb (Nat.pair z j)
  have := parseRpn_disjChain (fun j => b (Nat.pair z j)) (fun j => D z j) hblk
    (cnt z) 0 []
    ((((List.range (cnt z)).flatMap fun j => 4 :: b (Nat.pair z (0 + j))) ++
      0 :: []).length)
    le_rfl
  simpa using this

end MachineSentenceCodes

/-- **Finite mod-`k` dispatch between machine-metered sentence families.** The paper's
fixed-`k` family forms (`thm:lex`) quantify over `k` independent 𝓔𝓒 sequences read through
`z ↦ φ (z.unpair.2 % k) z.unpair.1`; this assembles them by `k` nested
`MachineSentenceCodes.ifZero`s, the same induction the fuel-metered version runs.

The reindexer `z ↦ z.unpair.1` and the `k` equality tests are *not* hypotheses: they are
built inside the proof from `divmodc_polyFueled`, `addc_polyFueled` and `subc_polyFueled`
exactly as `BigSentenceCodes.modDispatch` builds them, and each is handed to the machine
combinator as a unary ruler through `UnaryRuler.of_polyFueled`. So the only hypotheses are
the `k` families themselves, and there is no length side condition. Fuel-side twin:
`BigSentenceCodes.modDispatch`. -/
lemma MachineSentenceCodes.modDispatch {k : ℕ} (hk : 0 < k) {φ : ℕ → ℕ → Sentence}
    (hφ : ∀ j < k, MachineSentenceCodes (φ j)) :
    MachineSentenceCodes (fun z => φ (z.unpair.2 % k) z.unpair.1) := by
  obtain ⟨cdm, hdm⟩ := divmodc_polyFueled k hk
  obtain ⟨cadd, hadd⟩ := addc_polyFueled
  have hrem : PolyFueled _ (fun z : ℕ => z.unpair.2 % k) :=
    (PolyFueled.right.comp (hdm.comp PolyFueled.right)).of_eq (fun z => by simp)
  have hleft := UnaryRuler.unpairFst
  have H : ∀ m, m ≤ k → MachineSentenceCodes (fun z =>
      if z.unpair.2 % k < m then φ (z.unpair.2 % k) z.unpair.1
      else φ 0 z.unpair.1) := by
    intro m
    induction m with
    | zero =>
        intro _
        exact ((hφ 0 hk).comp (f := fun n : ℕ => (Nat.unpair n).1) hleft).of_eq
          (fun z => by simp)
    | succ m ih =>
        intro hm
        have hmk : m < k := hm
        have htest := UnaryRuler.of_polyFueled
          ((hadd.comp ((subc_polyFueled.comp (hrem.pair (PolyFueled.const m))).pair
            (subc_polyFueled.comp ((PolyFueled.const m).pair hrem)))).of_eq
            (fun z : ℕ => by simp) :
            PolyFueled _ (fun z : ℕ => (z.unpair.2 % k - m) + (m - z.unpair.2 % k)))
        refine (MachineSentenceCodes.ifZero
          (t := fun z : ℕ => ((Nat.unpair z).2 % k - m) + (m - (Nat.unpair z).2 % k))
          ((hφ m hmk).comp (f := fun n : ℕ => (Nat.unpair n).1) hleft)
          (ih (le_of_lt hm)) htest).of_eq (fun z => ?_)
        by_cases heq : z.unpair.2 % k = m
        · rw [if_pos (by omega), if_pos (by omega), heq]
        · rw [if_neg (by omega)]
          by_cases hlt : z.unpair.2 % k < m + 1
          · rw [if_pos hlt, if_pos (by omega)]
          · rw [if_neg hlt, if_neg (by omega)]
  exact (H k le_rfl).of_eq (fun z => by
    rw [if_pos (Nat.mod_lt z.unpair.2 hk)])

end LogicalInduction
