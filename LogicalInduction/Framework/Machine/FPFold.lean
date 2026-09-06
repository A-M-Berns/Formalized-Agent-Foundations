import LogicalInduction.Framework.Machine.DigitBits
import Complexitylib.Classes.P.Composition
import Complexitylib.Classes.P.PairWithInput
import Complexitylib.Classes.P.Cobham.Internal

/-!
# Polynomial-time streaming folds

`MachineEfficientTrader` (`def:ec`, `Framework/Criterion.lean`) asks for a `Complexity.FP`
function of the *unary* day whose output word `strategyOfOutput` decodes to the trader's
strategy.  Transporting a trader across a **syntactic** rewrite of that serialized stream —
freezing a price leaf, splicing a conditioning block — therefore means exhibiting the
rewrite itself as an `FP` function.  This file is the reusable core of that job.

The clients are not finite-state.  `RpnConditioning.rpnConditionRun`
(`Construction/Conditioning/Transduction.lean`) carries a packed state `⟨mode, counter, runLen⟩`
together with a buffered sentence run: `mode` is finite, but the open-subtree counter, the
run length and the buffer are all unbounded, bounded only by the input length.  So what they
need is not a Mealy-machine theorem but a **fold with an `FP` step whose state stays
polynomially bounded** — which is exactly what the fork's
`Complexity.Cobham.recFoldClamp_mem_FP` provides once the clamp is discharged.

Contents:

* `constFn_mem_FP` — the arbitrary constant word the fork does not supply;
* `recFold_mem_FP` — `FP` is closed under a right fold with an `FP` step, a constant base
  and a polynomially bounded running value;
* `foldlBits`, `foldlBits_mem_FP` — the same closure in the left-to-right form the stream
  rewriters use, obtained by folding over the reversed input (`recFold_reverse`).  The state
  bound is demanded on every word no longer than the stream, because the clamp has to be
  discharged on the machine's malformed inputs too;
* `mem_FP_withInput` — how a transduction recovers the day `n` from `unaryDay n`.

`Framework/Machine/TokenFold.lean` builds the tokenizer on `foldlBits_mem_FP`, and the
§4-family stream rewriters under `Construction/` reach the fold through that tokenizer;
`Construction/Conditioning/Transduction.lean` takes `mem_FP_withInput`.  `constFn_mem_FP` is used
wherever a rewrite emits a fixed word.

**Import disclosure.** This file imports `Complexitylib.Classes.P.Cobham.Internal`, which the
fork treats as proof internals (`Cobham.lean` imports it non-publicly).  The fold engine
(`recFoldClamp_mem_FP`, `recFoldClamp_eq_recFold`), the block projection `fstBlock` and the
string kit (`pairFn_mem_FP`, `const_nil_mem_FP`, `cons_mem_FP`) live only there; nothing here
depends on Cobham's algebra itself, only on those `FP` closure lemmas.

Everything in this file is supporting infrastructure rather than a paper claim, so the
declarations are `lemma`s and carry no `Paper node` line.
-/

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
is the direction every stream rewriter in the `Construction/` lanes runs in. -/

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
