/-
# Polynomial-time streaming folds

`MachineEfficientTrader` (`Framework/Criterion.lean`) asks for a `Complexity.FP` function of
the *unary* day whose output word `strategyOfOutput` decodes to the trader's strategy.
Transporting a trader across a **syntactic** rewrite of that serialized stream — freezing a
price leaf, splicing a conditioning block — therefore means exhibiting the rewrite itself as
an `FP` function.  This file is the reusable core of that job.

The clients are not finite-state.  `RpnConditioning.rpnConditionRun` carries a packed state
`⟨mode, counter, runLen⟩` together with a buffered sentence run: `mode` is finite, but the
open-subtree counter, the run length and the buffer are all unbounded, bounded only by the
input length.  So the theorem they need is not a Mealy-machine theorem but a **fold with an
`FP` step whose state stays polynomially bounded** — which is exactly what the fork's
`Complexity.Cobham.recFoldClamp_mem_FP` provides once the clamp is discharged.

Contents:

* `recFold_mem_FP` — `FP` is closed under a right fold with an `FP` step, a constant base
  and a polynomially bounded running value;
* `foldlBits`, `foldlBits_mem_FP` — the same closure in the left-to-right form the stream
  rewriters use, obtained by folding over the reversed input;
* `mem_FP_withInput` — how a transduction recovers the day `n` from `unaryDay n`;
* `unaryOfBits_le_mem_FP` — the guarded unary expansion: read a value off the stream and
  emit that many marks, clamped to a length already available.  This is the one piece plain
  composition does not give, because the value read is data, not a length;
* `strategyOfOutput_digitsToBits` and its unconditional clamped form — the adapters that
  lift a *digit*-level rewrite to the bit level `MachineEfficientTrader` reads.

**Import disclosure.** This file imports `Complexitylib.Classes.P.Cobham.Internal`, which the
fork treats as proof internals (`Cobham.lean` imports it non-publicly).  The fold engine
`recFoldClamp_mem_FP`, the block projections `fstBlock`/`sndBlock` and the string kit
(`pairFn_mem_FP`, `appendFn_mem_FP`, `takeLenFn_mem_FP`, `selectHeadFn_mem_FP`) live only
there; nothing here depends on Cobham's algebra itself, only on those `FP` closure lemmas.
If the fork ever promotes them to a public closure module, this import should follow.

Everything in this file is supporting infrastructure rather than a paper claim, so the
declarations are `lemma`s and carry no `Paper node:` line.
-/
import LogicalInduction.Framework.Machine.DigitBits
import Complexitylib.Classes.P.Composition
import Complexitylib.Classes.P.PairWithInput
import Complexitylib.Classes.P.Cobham.Internal
import Complexitylib.Mathlib.NatBits

namespace LogicalInduction.FPFold

open Complexity Complexity.Cobham

/-! ## Constants -/

/-- Every constant word is polynomial-time.

The fork has `Cobham.const_nil_mem_FP` and `Cobham.cons_mem_FP` but no lemma for an
arbitrary constant word; this is the one-line induction over them.
Proof kind: `P`.  Provenance: (b) `Complexitylib.Classes.P.Cobham.Internal`. -/
lemma constFn_mem_FP (c : List Bool) : (fun _ : List Bool => c) ∈ FP := by
  induction c with
  | nil => exact const_nil_mem_FP
  | cons b c ih =>
      have h := mem_FP_comp ih (cons_mem_FP b)
      have heq : ((fun x : List Bool => b :: x) ∘ fun _ : List Bool => c)
          = fun _ : List Bool => b :: c := rfl
      rwa [heq] at h

/-! ## The fold combinator -/

/-- **`FP` is closed under a right fold with an `FP` step and a polynomially bounded
running value.**

`W z` is a parameter block the step may read (anything the rewrite needs that is not in the
stream), `S z` is the string folded over, and the step — `A` on a `false` bit, `B` on a
`true` one — receives `pair (pair (W z) acc) t`: the parameter, the value already computed
on the tail, and the tail itself.  The base value `e` is a constant.

The bound is stated at `(W z).length + (S z).length` rather than at `z.length` because the
fold is run on the packed string `pair (W z) (S z)`, whose length dominates that sum.

Proof kind: `C` composition.  Provenance: (b) `Cobham.recFoldClamp_mem_FP`,
`Cobham.recFoldClamp_eq_recFold`, `Cobham.pairFn_mem_FP`, `mem_FP_comp`,
`polynomial_eval_mono_nat`. -/
lemma recFold_mem_FP {A B W S : List Bool → List Bool}
    (hA : A ∈ FP) (hB : B ∈ FP) (hW : W ∈ FP) (hS : S ∈ FP)
    (e : List Bool) (p : Polynomial ℕ)
    (hbnd : ∀ z t, t.length ≤ (S z).length →
      (recFold A B e (W z) t).length ≤ p.eval ((W z).length + (S z).length)) :
    (fun z => recFold A B e (W z) (S z)) ∈ FP := by
  have hΦ : (fun z => pair (W z) (S z)) ∈ FP := pairFn_mem_FP hW hS
  have hclamp := recFoldClamp_mem_FP hA hB (E := fun _ => e) (constFn_mem_FP e) p
  have hcomp := mem_FP_comp hΦ hclamp
  have heq : ((fun y => recFoldClamp A B (p.eval y.length) e (fstBlock y) (sndBlock y))
        ∘ fun z => pair (W z) (S z))
      = fun z => recFold A B e (W z) (S z) := by
    funext z
    simp only [Function.comp_apply, fstBlock_pair, sndBlock_pair]
    refine recFoldClamp_eq_recFold (S z) fun t ht => ?_
    refine le_trans (hbnd z t ht) (polynomial_eval_mono_nat p ?_)
    rw [pair_length]
    omega
  rwa [heq] at hcomp

/-! ## The left-to-right form

`recFold` peels the *head* of its argument outermost, so folding it over `s.reverse`
consumes `s` from the front: the innermost computation is the one on `s`'s first bit.  That
is the direction every stream rewriter in `Construction/Witnesses/` runs in. -/

/-- A left-to-right fold over a bit string, with the step selected by the bit.  The state is
an arbitrary word; a rewriter packs its automaton state and its output-so-far into it with
`Complexity.pair` and reads the result back with `sndBlock`. -/
def foldlBits (A B : List Bool → List Bool) (W : List Bool) :
    List Bool → List Bool → List Bool
  | st, [] => st
  | st, b :: bs => foldlBits A B W ((bif b then B else A) (pair W st)) bs

@[simp] lemma foldlBits_nil (A B : List Bool → List Bool) (W st : List Bool) :
    foldlBits A B W st [] = st := rfl

@[simp] lemma foldlBits_cons (A B : List Bool → List Bool) (W st : List Bool)
    (b : Bool) (bs : List Bool) :
    foldlBits A B W st (b :: bs)
      = foldlBits A B W ((bif b then B else A) (pair W st)) bs := rfl

/-- Appending one bit applies one more step. -/
lemma foldlBits_append_singleton (A B : List Bool → List Bool) (W : List Bool)
    (b : Bool) : ∀ (st bs : List Bool),
    foldlBits A B W st (bs ++ [b])
      = (bif b then B else A) (pair W (foldlBits A B W st bs))
  | _, [] => rfl
  | st, c :: cs => by
      rw [List.cons_append, foldlBits_cons, foldlBits_cons,
        foldlBits_append_singleton A B W b _ cs]

/-- **The left fold is the right fold over the reversed input**, once the step is told to
ignore the tail component `recFold` hands it. -/
lemma recFold_reverse (A B : List Bool → List Bool) (W e : List Bool) :
    ∀ r : List Bool,
      recFold (A ∘ fstBlock) (B ∘ fstBlock) e W r = foldlBits A B W e r.reverse
  | [] => rfl
  | b :: t => by
      show (bif b then B ∘ fstBlock else A ∘ fstBlock)
          (pair (pair W (recFold (A ∘ fstBlock) (B ∘ fstBlock) e W t)) t) = _
      rw [recFold_reverse A B W e t, List.reverse_cons,
        foldlBits_append_singleton A B W b e t.reverse]
      cases b <;> simp [Function.comp_apply, fstBlock_pair]

/-- **`FP` is closed under a left-to-right fold with an `FP` step and a polynomially bounded
state.**

This is the shape the stream rewriters use: `S z` is the serialized stream, `W z` a
parameter block, `e` the initial state, and the step reads `pair (W z) st`.  The hypothesis
is exactly "the state stays polynomially bounded on every prefix" — stated over *all* words
`u` no longer than the stream, because the clamp inside `recFold_mem_FP` must be discharged
on the machine's malformed inputs too, not only on the intended trajectory.

Proof kind: `C` composition.  Provenance: (b) `recFold_mem_FP`, `Complexity.reverse_mem_FP`,
`Cobham.fstBlock_mem_FP`, `mem_FP_comp`. -/
lemma foldlBits_mem_FP {A B W S : List Bool → List Bool}
    (hA : A ∈ FP) (hB : B ∈ FP) (hW : W ∈ FP) (hS : S ∈ FP)
    (e : List Bool) (p : Polynomial ℕ)
    (hbnd : ∀ z u, u.length ≤ (S z).length →
      (foldlBits A B (W z) e u).length ≤ p.eval ((W z).length + (S z).length)) :
    (fun z => foldlBits A B (W z) e (S z)) ∈ FP := by
  have hAf : (A ∘ fstBlock) ∈ FP := mem_FP_comp fstBlock_mem_FP hA
  have hBf : (B ∘ fstBlock) ∈ FP := mem_FP_comp fstBlock_mem_FP hB
  have hSr : (fun z => (S z).reverse) ∈ FP := mem_FP_comp hS reverse_mem_FP
  have h := recFold_mem_FP (A := A ∘ fstBlock) (B := B ∘ fstBlock) (W := W)
    (S := fun z => (S z).reverse) hAf hBf hW hSr e p (fun z t ht => by
      rw [recFold_reverse]
      refine le_trans (hbnd z t.reverse (by simpa using ht)) ?_
      exact polynomial_eval_mono_nat p (by simp))
  have heq : (fun z => recFold (A ∘ fstBlock) (B ∘ fstBlock) e (W z) ((S z).reverse))
      = fun z => foldlBits A B (W z) e (S z) := by
    funext z
    rw [recFold_reverse, List.reverse_reverse]
  rwa [heq] at h

/-! ## The guarded unary expansion

Every other closure in this file moves *words* around, so it composes.  Turning a value
**read off the stream** into that many marks does not: `Complexity.FP` has length arithmetic
(`Cobham.mulLenFn_mem_FP`, `Complexity.unaryLength_mem_FP`) but no way to make a length out
of data, and unclamped it would not even be polynomial — a `k`-bit value denotes up to
`2 ^ k` marks.

The clamp is what makes it legitimate and is exactly the guard the clients have: a day read
out of a day-`n` strategy stream is `≤ n`, and `n` is the length of a word already in hand
(`mem_FP_withInput` below puts `unaryDay n` there).  So the primitive is *"emit
`min value cap` marks"*, with `cap` a length rather than a number, and it is a fold: one
doubling per bit, truncated at `cap` after every step. -/

/-- One step of the guarded expansion: double the unary accumulator, add the incoming bit,
and truncate to the cap.  The argument is `pair cap acc`. -/
private def dblStep (b : Bool) (u : List Bool) : List Bool :=
  ((sndBlock u ++ sndBlock u) ++ (if b then [true] else [])).take (fstBlock u).length

private lemma dblStep_mem_FP (b : Bool) : dblStep b ∈ FP :=
  takeLenFn_mem_FP fstBlock_mem_FP
    (appendFn_mem_FP (appendFn_mem_FP sndBlock_mem_FP sndBlock_mem_FP)
      (constFn_mem_FP (if b then [true] else [])))

/-- Snoc for big-endian decoding.  The fork proves this as `Nat.fromBits_append_singleton`
but keeps it `private`; it is recovered here from the public little-endian interface. -/
private lemma fromBits_append_singleton (bs : List Bool) (b : Bool) :
    Nat.fromBits (bs ++ [b]) = 2 * Nat.fromBits bs + (if b then 1 else 0) := by
  have hrev : (bs ++ [b]).reverse = b :: bs.reverse := by simp
  have h1 : Nat.fromBits (bs ++ [b]) = Nat.fromBitsLE (b :: bs.reverse) := by
    show Nat.fromBits (bs ++ [b]) = Nat.fromBits ((b :: bs.reverse).reverse)
    rw [← hrev, List.reverse_reverse]
  have h2 : Nat.fromBitsLE bs.reverse = Nat.fromBits bs := by
    show Nat.fromBits bs.reverse.reverse = Nat.fromBits bs
    rw [List.reverse_reverse]
  rw [h1, Nat.fromBitsLE_cons, h2]
  omega

/-- **The expansion computes what it says.** Truncating after every doubling is invisible:
once the accumulator saturates it stays saturated, and the true value has already passed the
cap, so both sides read `cap`. -/
private lemma foldlBits_dblStep (W : List Bool) : ∀ bs : List Bool,
    foldlBits (dblStep false) (dblStep true) W [] bs
      = List.replicate (min (Nat.fromBits bs) W.length) true := by
  intro bs
  induction bs using List.reverseRecOn with
  | nil => simp [Nat.fromBits]
  | append_singleton cs b ih =>
      rw [foldlBits_append_singleton, ih, fromBits_append_singleton]
      have hrep : ∀ m : ℕ,
          dblStep b (pair W (List.replicate m true))
            = List.replicate (min (2 * m + (if b then 1 else 0)) W.length) true := by
        intro m
        rw [dblStep, fstBlock_pair, sndBlock_pair, ← List.replicate_add]
        cases b with
        | false =>
            simp only [if_neg (by simp : ¬ (false = true)), List.append_nil,
              List.take_replicate]
            congr 1
            omega
        | true =>
            have hsucc : List.replicate (m + m) true ++ [true]
                = List.replicate (m + m + 1) true :=
              (List.replicate_add (m + m) 1 true).symm
            have hif : (if true = true then [true] else ([] : List Bool)) = [true] := by
              simp
            have hif1 : (if true = true then 1 else 0) = 1 := by simp
            rw [hif, hif1, hsucc, List.take_replicate]
            congr 1
            omega
      have hstep : (bif b then dblStep true else dblStep false) = dblStep b := by
        cases b <;> rfl
      have hmin : ∀ v L β : ℕ, min (2 * min v L + β) L = min (2 * v + β) L := by
        intro v L β
        omega
      rw [hstep, hrep, hmin]

/-- **Guarded unary expansion is polynomial-time.** `V z` is a value read off the stream,
big-endian; `C z` is a word whose *length* is the guard.  The result is `min` of the two,
in unary.

This is the piece plain composition does not give, and it is what lets a rewrite feed a day
read out of the stream to an oracle indexed by unary days: `blocks ∘ unaryOfBits_le` is then
an ordinary `mem_FP_comp`.

Proof kind: `C` composition.  Provenance: (b) `foldlBits_mem_FP` above,
`Cobham.takeLenFn_mem_FP`, `Cobham.appendFn_mem_FP`, `Nat.fromBitsLE_cons`;
(a) `foldlBits_dblStep`. -/
lemma unaryOfBits_le_mem_FP {V C : List Bool → List Bool} (hV : V ∈ FP) (hC : C ∈ FP) :
    (fun z => List.replicate (min (Nat.fromBits (V z)) (C z).length) true) ∈ FP := by
  have h := foldlBits_mem_FP (A := dblStep false) (B := dblStep true) (W := C) (S := V)
    (dblStep_mem_FP false) (dblStep_mem_FP true) hC hV [] Polynomial.X
    (fun z u _ => by
      rw [foldlBits_dblStep]
      simp only [List.length_replicate, Polynomial.eval_X]
      omega)
  have heq : (fun z => foldlBits (dblStep false) (dblStep true) (C z) [] (V z))
      = fun z => List.replicate (min (Nat.fromBits (V z)) (C z).length) true := by
    funext z
    rw [foldlBits_dblStep]
  rwa [heq] at h

/-- **An oracle indexed by unary days may be called on a day read off the stream.**

This is the whole of the "oracle-valued emitter" question, and the answer is that there is
nothing to add: an emitter is just an `FP` function of the step's packed argument, so once
`unaryOfBits_le_mem_FP` turns the *value* `D` into the *word* `unaryDay D`, calling
`Blocks` on it is an ordinary `mem_FP_comp`.  `V` and `C` here are arbitrary `FP` functions
of the step's argument, so instantiating `V` at the extraction of the day slot and `C` at
the guard word is exactly what a rewriter's step does.

Note what the guard buys: without it the composite is not merely unproved but *false* as a
polynomial-time claim, since a `k`-bit day would name up to `2 ^ k` marks.

Proof kind: `C` composition.  Provenance: (b) `mem_FP_comp`; (a) `unaryOfBits_le_mem_FP`. -/
lemma emitOracle_mem_FP {V C Blocks : List Bool → List Bool}
    (hV : V ∈ FP) (hC : C ∈ FP) (hBlocks : Blocks ∈ FP) :
    (fun z => Blocks (List.replicate (min (Nat.fromBits (V z)) (C z).length) true)) ∈ FP :=
  mem_FP_comp (unaryOfBits_le_mem_FP hV hC) hBlocks

/-! ## Recovering the day -/

/-- **The composite that makes the machine's own input available to a transduction.**

A transported trader's output function is `fun x => G (pair (F x) x)`: the original
`MachineEfficientTrader` witness `F` produces the stream, and `G` rewrites it with the raw
input still beside it.  Since the input is `unaryDay n`, this is how the rewrite learns the
day `n` — as the length of `sndBlock`.

Proof kind: `C` composition.  Provenance: (b) `mem_FP_pairWithInput`, `mem_FP_comp`. -/
lemma mem_FP_withInput {F G : List Bool → List Bool} (hF : F ∈ FP) (hG : G ∈ FP) :
    (fun x => G (pair (F x) x)) ∈ FP :=
  mem_FP_comp (mem_FP_pairWithInput hF) hG

end LogicalInduction.FPFold

/-! ## Digit-level rewrites, read back by `strategyOfOutput` -/

namespace LogicalInduction

/-- A digit-level rewrite lifts to the bit level through `digitsToBits`, provided the digits
it emits fit in three bits.

Proof kind: `C` composition.  Provenance: (a) `bitsToDigits_digitsToBits`. -/
lemma strategyOfOutput_digitsToBits (n : ℕ) (ds : List ℕ) (h : ∀ d ∈ ds, d < 8) :
    strategyOfOutput n (digitsToBits ds)
      = strategyOfTokens n (unRpn (undigitize ds)) := by
  rw [strategyOfOutput, bitsToDigits_digitsToBits ds h]

/-- **The adapter, unconditionally.** Clamping every digit at the block terminator makes it
fit in three bits and is invisible to `undigitize`, so *any* digit stream — including the
unbounded token values a rewrite may emit — round-trips through the bit rendering
`MachineEfficientTrader` reads.

Proof kind: `C` composition.  Provenance: (a) `strategyOfOutput_digitsToBits`,
`undigitize_map_min_four`. -/
lemma strategyOfOutput_digitsToBits_clamp (n : ℕ) (ds : List ℕ) :
    strategyOfOutput n (digitsToBits (ds.map (fun d => min d 4)))
      = strategyOfTokens n (unRpn (undigitize ds)) := by
  rw [strategyOfOutput_digitsToBits n _ (by
        intro d hd
        obtain ⟨e, -, rfl⟩ := List.mem_map.mp hd
        omega),
    undigitize_map_min_four]

end LogicalInduction
