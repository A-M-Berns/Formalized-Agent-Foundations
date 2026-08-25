/-
# Compiling `Nat.Partrec.Code` to ordinary Turing machines

Stage 2B of the efficiency-model program (`LogicalInduction/notes/complexitylib-adoption.md`
Part XII). The arithmetic substrate is complete upstream; this file starts the compiler
from `Nat.Partrec.Code` into `complexitylib` register machines, proved **exactly** against
`Nat.Partrec.Code.evaln` — not against the unclocked `eval`.

## What `evaln` actually says

Read off Mathlib's definition, not from memory. `Code` has exactly eight constructors and
**no `const`** (`Code.const` is a derived definition). At fuel `0` every code is `none`, and
at fuel `k + 1` *every* constructor begins with the same `guard (n ≤ k)`. Since
`n ≤ k ↔ n < k + 1`, and `n < 0` is false, the single test

```
n < fuel
```

is the whole guard, uniformly, including the fuel-`0` case. That is why the guard is
centralized here (Route B of the tranche's choice) rather than repeated per constructor:
`evaln_zero_eq` and its siblings state each constructor as `if n < k then … else none`.

The recursive constructors re-check the guard on their own sub-calls, so centralizing it
does *not* mean hoisting it out of the recursion — each compiled machine begins with it.

## No control flow

The compiled machines are **straight-line**. Rather than branching on the guard, each
constructor computes its answer unconditionally and multiplies both result registers by
the `0/1` guard flag (`resultTag_ite`, `resultVal_ite`). This is the same multiplicative
mask that removed the branch from `pairTM` upstream, and it is what keeps `ifTM` — whose
output-tape test is incompatible with the `OutAcc` emission convention — out of the
compiler entirely. `OutAcc ys` is carried through every machine here unchanged.

The cost is that a compiled machine does its work even when the guard fails and the answer
is discarded. That is bounded work, and `codeEvalSteps` already bounds the whole code
tree, so it does not threaten the eventual polynomial bound.

## Status

Non-recursive constructors only: `zero`, `succ`, `left`, `right`. `pair` and `comp` are
**not** in this file yet; see Part XII of the note for the register-window design they
need and why it is a separate pass.
-/
import Complexitylib.Models.TuringMachine.Registers.Pairing
import Mathlib.Computability.PartrecCode

namespace LogicalInduction.EvalnCompiler

open Complexity Complexity.TM

variable {n : ℕ}

/-! ## The exact `evaln` equations for the non-recursive constructors -/

lemma evaln_zero_eq (k m : ℕ) :
    Nat.Partrec.Code.evaln k Nat.Partrec.Code.zero m = if m < k then some 0 else none := by
  cases k with
  | zero => simp [Nat.Partrec.Code.evaln]
  | succ k =>
    simp only [Nat.Partrec.Code.evaln, Nat.lt_succ_iff]
    split_ifs with h <;> simp [h]

lemma evaln_succ_eq (k m : ℕ) :
    Nat.Partrec.Code.evaln k Nat.Partrec.Code.succ m = if m < k then some (m + 1) else none := by
  cases k with
  | zero => simp [Nat.Partrec.Code.evaln]
  | succ k =>
    simp only [Nat.Partrec.Code.evaln, Nat.lt_succ_iff]
    split_ifs with h <;> simp [h]

lemma evaln_left_eq (k m : ℕ) :
    Nat.Partrec.Code.evaln k Nat.Partrec.Code.left m = if m < k then some m.unpair.1 else none := by
  cases k with
  | zero => simp [Nat.Partrec.Code.evaln]
  | succ k =>
    simp only [Nat.Partrec.Code.evaln, Nat.lt_succ_iff]
    split_ifs with h <;> simp [h]

lemma evaln_right_eq (k m : ℕ) :
    Nat.Partrec.Code.evaln k Nat.Partrec.Code.right m = if m < k then some m.unpair.2 else none := by
  cases k with
  | zero => simp [Nat.Partrec.Code.evaln]
  | succ k =>
    simp only [Nat.Partrec.Code.evaln, Nat.lt_succ_iff]
    split_ifs with h <;> simp [h]

/-! ## The result convention -/

/-- Tag register contents for an `Option ℕ`: `0` is `none`, `1` is `some`. -/
def resultTag : Option ℕ → ℕ
  | Option.none => 0
  | Option.some _ => 1

/-- Value register contents. `none` is represented **canonically**, with the value
    register cleared to `0`, so that a compiled machine's post-state is a definite
    register-value vector rather than a vector with a don't-care entry. -/
def resultVal : Option ℕ → ℕ
  | Option.none => 0
  | Option.some x => x

@[simp] lemma resultTag_none : resultTag none = 0 := rfl
@[simp] lemma resultVal_none : resultVal none = 0 := rfl
@[simp] lemma resultTag_some (x : ℕ) : resultTag (some x) = 1 := rfl
@[simp] lemma resultVal_some (x : ℕ) : resultVal (some x) = x := rfl

/-- **The masking identity.** A guarded `evaln` result is the *product* of the guard flag
    with the unguarded answer — in both components.

    This is what removes control flow from the compiler: instead of branching on the
    fuel/input guard, the machine computes the constructor's answer unconditionally and
    multiplies both result registers by the `0/1` guard flag. -/
lemma resultTag_ite (p : Prop) [Decidable p] (o : Option ℕ) :
    resultTag (if p then o else none) = (if p then 1 else 0) * resultTag o := by
  split_ifs <;> simp

lemma resultVal_ite (p : Prop) [Decidable p] (o : Option ℕ) :
    resultVal (if p then o else none) = (if p then 1 else 0) * resultVal o := by
  split_ifs <;> simp

/-! ## The compiled-machine register layout

| index | role |
| ---: | --- |
| `0` | input `n` |
| `1` | fuel `k` |
| `2` | result tag |
| `3` | result value |
| `4` | the fuel/input guard flag `[n < k]` |
| `5` | the guard's scratch (`k - n`) |
| `6`–`15` | body scratch, ten registers — enough for `unpairTM` and `pairTM` |
-/

/-- The sixteen registers a compiled `Code` machine uses. -/
abbrev CodeRegs (n : ℕ) := Regs 16 n

/-- The correctness shape every constructor proves: after the run, registers `2` and `3`
    hold the tag and value of `evaln fuel c n`, where the fuel and input are read from
    registers `1` and `0` of the *entry* state. -/
def EncodesEvaln (c : Nat.Partrec.Code) (v u : Fin 16 → ℕ) : Prop :=
  u 2 = resultTag (Nat.Partrec.Code.evaln (v 1) c (v 0)) ∧
  u 3 = resultVal (Nat.Partrec.Code.evaln (v 1) c (v 0))

/-! ### `Code.zero` -/

/-- `evaln k zero n`. Three straight-line stages: compute the guard flag, copy it into the
    tag, clear the value. No control flow — the `none` case is exactly `tag = 0`. -/
def compileZero (r : CodeRegs n) : TM n :=
  seqTM (ltFlagTM (r 0) (r 1) (r 5) (r 4)) <|
  seqTM (copyIntoTM (r 4) (r 2))
        (clearRegTM (r 3))

def zeroVals (v : Fin 16 → ℕ) : Fin 16 → ℕ := fun k =>
  if k = 2 then (if v 0 < v 1 then 1 else 0)
  else if k = 3 then 0
  else if k = 4 then (if v 0 < v 1 then 1 else 0)
  else if k = 5 then v 1 - v 0
  else v k

lemma zeroVals_encodes (v : Fin 16 → ℕ) : EncodesEvaln Nat.Partrec.Code.zero v (zeroVals v) := by
  refine ⟨?_, ?_⟩ <;> rw [evaln_zero_eq] <;> simp only [zeroVals] <;> split_ifs <;> simp_all

lemma compileZero_hoareTime (r : CodeRegs n) (v : Fin 16 → ℕ) (B : ℕ)
    (inp₀ : Tape) (w₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hpark : ∀ i, Parked (w₀ i)) (hB : ∀ k, v k < B) :
    (compileZero r).HoareTime
      (EmitPred inp₀ (regsWork r w₀ v) ys)
      (EmitPred inp₀ (regsWork r w₀ (zeroVals v)) ys)
      (3 * evalnArithmeticCost B + 2) := by
  have hpv := parked_regsWork r hpark
  have hle : ∀ k, v k ≤ B := fun k => Nat.le_of_lt (hB k)
  -- S1: guard
  have h1 := ltFlagTM_hoareTime (r 0) (r 1) (r 5) (r 4)
      (r.ne (by decide)) (r.ne (by decide)) (r.ne (by decide))
      (v 0) (v 1) (v 5) (v 4) inp₀ (regsWork r w₀ v) ys hinp₀ (hpv v)
      (regsWork_apply r w₀ v 0) (regsWork_apply r w₀ v 1)
      (regsWork_apply r w₀ v 5) (regsWork_apply r w₀ v 4)
  rw [regsWork_update, regsWork_update] at h1
  replace h1 := h1.mono_bound
    (ltFlagTime_le_arith (v 0) (v 1) (v 5) (v 4) B (hle 0) (hle 1) (hle 5) (hle 4))
  set V1 := Function.update (Function.update v 5 (v 1 - v 0)) 4
      (if v 0 < v 1 then 1 else 0) with hV1
  have g1_4 : V1 4 = (if v 0 < v 1 then 1 else 0) := by rw [hV1]; simp [Function.update_apply]
  have g1_2 : V1 2 = v 2 := by rw [hV1]; simp [Function.update_apply]
  -- S2: tag := gflag
  have h2 := copyIntoTM_hoareTime (r 4) (r 2) (r.ne (by decide))
      (if v 0 < v 1 then 1 else 0) (v 2) inp₀ (regsWork r w₀ V1) ys hinp₀
      (fun i _ => hpv V1 i) (by rw [regsWork_apply, g1_4]) (by rw [regsWork_apply, g1_2])
  rw [regsWork_update] at h2
  replace h2 := h2.mono_bound
    (copyIntoTime_le_arith (if v 0 < v 1 then 1 else 0) (v 2) B
      (by have := hB 0; split_ifs <;> omega) (hle 2))
  set V2 := Function.update V1 2 (if v 0 < v 1 then 1 else 0) with hV2
  have g2_3 : V2 3 = v 3 := by rw [hV2, hV1]; simp [Function.update_apply]
  -- S3: val := 0
  have h3 := clearRegTM_hoareTime (r 3) (v 3) inp₀ (regsWork r w₀ V2) ys hinp₀
      (fun i _ => hpv V2 i) (by rw [regsWork_apply, g2_3])
  rw [regsWork_update] at h3
  replace h3 := h3.mono_bound (regOpTime_le_arith (v 3) B (hle 3))
  have hfin : Function.update V2 3 0 = zeroVals v := by
    funext k
    simp only [hV2, hV1, zeroVals, Function.update_apply]
    fin_cases k <;> simp
  rw [hfin] at h3
  exact (seqEmit hinp₀ (hpv V1) h1 (seqEmit hinp₀ (hpv V2) h2 h3)).mono_bound (by omega)

/-! ### `Code.succ` -/

/-- `evaln k succ n`. The answer `n + 1` is computed unconditionally into scratch and then
    **masked** by the guard flag: `val := gflag * (n + 1)`. When the guard fails both result
    registers are `0`, which is exactly the canonical `none`. -/
def compileSucc (r : CodeRegs n) : TM n :=
  seqTM (ltFlagTM (r 0) (r 1) (r 5) (r 4)) <|
  seqTM (copyIntoTM (r 0) (r 6)) <|
  seqTM (incRegTM (r 6)) <|
  seqTM (copyIntoTM (r 4) (r 2)) <|
  seqTM (clearRegTM (r 3))
        (mulAddIntoTM (r 4) (r 6) (r 3))

def succVals (v : Fin 16 → ℕ) : Fin 16 → ℕ := fun k =>
  if k = 2 then (if v 0 < v 1 then 1 else 0)
  else if k = 3 then 0 + (if v 0 < v 1 then 1 else 0) * (v 0 + 1)
  else if k = 4 then (if v 0 < v 1 then 1 else 0)
  else if k = 5 then v 1 - v 0
  else if k = 6 then v 0 + 1
  else v k

lemma succVals_encodes (v : Fin 16 → ℕ) : EncodesEvaln Nat.Partrec.Code.succ v (succVals v) := by
  refine ⟨?_, ?_⟩ <;> rw [evaln_succ_eq] <;> simp only [succVals] <;> split_ifs <;> simp_all

lemma compileSucc_hoareTime (r : CodeRegs n) (v : Fin 16 → ℕ) (B : ℕ)
    (inp₀ : Tape) (w₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hpark : ∀ i, Parked (w₀ i)) (hB : ∀ k, v k < B) :
    (compileSucc r).HoareTime
      (EmitPred inp₀ (regsWork r w₀ v) ys)
      (EmitPred inp₀ (regsWork r w₀ (succVals v)) ys)
      (6 * evalnArithmeticCost B + 5) := by
  have hpv := parked_regsWork r hpark
  have hle : ∀ k, v k ≤ B := fun k => Nat.le_of_lt (hB k)
  have hg : (if v 0 < v 1 then 1 else 0) ≤ B := by have := hB 0; split_ifs <;> omega
  have hn1 : v 0 + 1 ≤ B := hB 0
  -- S1: guard
  have h1 := ltFlagTM_hoareTime (r 0) (r 1) (r 5) (r 4)
      (r.ne (by decide)) (r.ne (by decide)) (r.ne (by decide))
      (v 0) (v 1) (v 5) (v 4) inp₀ (regsWork r w₀ v) ys hinp₀ (hpv v)
      (regsWork_apply r w₀ v 0) (regsWork_apply r w₀ v 1)
      (regsWork_apply r w₀ v 5) (regsWork_apply r w₀ v 4)
  rw [regsWork_update, regsWork_update] at h1
  replace h1 := h1.mono_bound
    (ltFlagTime_le_arith (v 0) (v 1) (v 5) (v 4) B (hle 0) (hle 1) (hle 5) (hle 4))
  set V1 := Function.update (Function.update v 5 (v 1 - v 0)) 4
      (if v 0 < v 1 then 1 else 0) with hV1
  have g1_0 : V1 0 = v 0 := by rw [hV1]; simp [Function.update_apply]
  have g1_6 : V1 6 = v 6 := by rw [hV1]; simp [Function.update_apply]
  -- S2: sc := n
  have h2 := copyIntoTM_hoareTime (r 0) (r 6) (r.ne (by decide)) (v 0) (v 6) inp₀
      (regsWork r w₀ V1) ys hinp₀ (fun i _ => hpv V1 i)
      (by rw [regsWork_apply, g1_0]) (by rw [regsWork_apply, g1_6])
  rw [regsWork_update] at h2
  replace h2 := h2.mono_bound (copyIntoTime_le_arith (v 0) (v 6) B (hle 0) (hle 6))
  set V2 := Function.update V1 6 (v 0) with hV2
  have g2_6 : V2 6 = v 0 := by rw [hV2]; simp [Function.update_apply]
  -- S3: sc := n + 1
  have h3 := incRegTM_hoareTime (r 6) (v 0) inp₀ (regsWork r w₀ V2) ys hinp₀
      (fun i _ => hpv V2 i) (by rw [regsWork_apply, g2_6])
  rw [regsWork_update] at h3
  replace h3 := h3.mono_bound (regOpTime_le_arith (v 0) B (hle 0))
  set V3 := Function.update V2 6 (v 0 + 1) with hV3
  have g3_4 : V3 4 = (if v 0 < v 1 then 1 else 0) := by
    rw [hV3, hV2, hV1]; simp [Function.update_apply]
  have g3_2 : V3 2 = v 2 := by rw [hV3, hV2, hV1]; simp [Function.update_apply]
  -- S4: tag := gflag
  have h4 := copyIntoTM_hoareTime (r 4) (r 2) (r.ne (by decide))
      (if v 0 < v 1 then 1 else 0) (v 2) inp₀ (regsWork r w₀ V3) ys hinp₀
      (fun i _ => hpv V3 i) (by rw [regsWork_apply, g3_4]) (by rw [regsWork_apply, g3_2])
  rw [regsWork_update] at h4
  replace h4 := h4.mono_bound
    (copyIntoTime_le_arith (if v 0 < v 1 then 1 else 0) (v 2) B hg (hle 2))
  set V4 := Function.update V3 2 (if v 0 < v 1 then 1 else 0) with hV4
  have g4_3 : V4 3 = v 3 := by rw [hV4, hV3, hV2, hV1]; simp [Function.update_apply]
  -- S5: val := 0
  have h5 := clearRegTM_hoareTime (r 3) (v 3) inp₀ (regsWork r w₀ V4) ys hinp₀
      (fun i _ => hpv V4 i) (by rw [regsWork_apply, g4_3])
  rw [regsWork_update] at h5
  replace h5 := h5.mono_bound (regOpTime_le_arith (v 3) B (hle 3))
  set V5 := Function.update V4 3 0 with hV5
  have g5_4 : V5 4 = (if v 0 < v 1 then 1 else 0) := by
    rw [hV5, hV4, hV3, hV2, hV1]; simp [Function.update_apply]
  have g5_6 : V5 6 = v 0 + 1 := by rw [hV5, hV4, hV3]; simp [Function.update_apply]
  have g5_3 : V5 3 = 0 := by rw [hV5]; simp [Function.update_apply]
  -- S6: val := gflag * (n + 1)
  have h6 := mulAddIntoTM_hoareTime (r 4) (r 6) (r 3)
      (r.ne (by decide)) (r.ne (by decide)) (r.ne (by decide))
      (if v 0 < v 1 then 1 else 0) (v 0 + 1) 0 inp₀ (regsWork r w₀ V5) ys hinp₀
      (fun i _ => hpv V5 i) (by rw [regsWork_apply, g5_4]) (by rw [regsWork_apply, g5_6])
      (by rw [regsWork_apply, g5_3])
  rw [regsWork_update] at h6
  replace h6 := h6.mono_bound
    (mulAddTime_le_arith (if v 0 < v 1 then 1 else 0) (v 0 + 1) 0 B hg hn1 (by omega))
  have hfin : Function.update V5 3 (0 + (if v 0 < v 1 then 1 else 0) * (v 0 + 1))
      = succVals v := by
    funext k
    simp only [hV5, hV4, hV3, hV2, hV1, succVals, Function.update_apply]
    fin_cases k <;> simp
  rw [hfin] at h6
  exact (seqEmit hinp₀ (hpv V1) h1 <|
    seqEmit hinp₀ (hpv V2) h2 <|
    seqEmit hinp₀ (hpv V3) h3 <|
    seqEmit hinp₀ (hpv V4) h4 <|
    seqEmit hinp₀ (hpv V5) h5 h6).mono_bound (by omega)

/-! ### `Code.left` and `Code.right`

Both are `unpairTM` on the input, masked by the guard flag. The nine registers `unpairTM`
needs are the window `6`–`14` of the compiled layout, reached through `unpairWindow`; the
loop counter it needs is the input register itself, which `forRegTM` leaves untouched. -/

/-- The nine-register window `unpairTM` runs in: compiled registers `6`–`14`. -/
def unpairWindow : Fin 9 ↪ Fin 16 :=
  ⟨fun j => ⟨j.val + 6, by have := j.isLt; omega⟩, by
    intro a b h
    have : a.val + 6 = b.val + 6 := congrArg Fin.val h
    exact Fin.ext (by omega)⟩

@[simp] lemma unpairWindow_zero : unpairWindow 0 = (6 : Fin 16) := by decide
@[simp] lemma unpairWindow_one : unpairWindow 1 = (7 : Fin 16) := by decide

/-- `evaln k left n` / `evaln k right n`, sharing one machine: unpair the input into the
    window, then mask the selected component by the guard flag. -/
def compileProj (r : CodeRegs n) (wj : Fin 9) : TM n :=
  seqTM (ltFlagTM (r 0) (r 1) (r 5) (r 4)) <|
  seqTM (unpairTM (unpairWindow.trans r) (r 0)) <|
  seqTM (copyIntoTM (r 4) (r 2)) <|
  seqTM (clearRegTM (r 3))
        (mulAddIntoTM (r 4) (r (unpairWindow wj)) (r 3))

/-- The state after the shared guard stage. -/
def afterGuard (v : Fin 16 → ℕ) : Fin 16 → ℕ :=
  Function.update (Function.update v 5 (v 1 - v 0)) 4 (if v 0 < v 1 then 1 else 0)

/-- The state after the unpair stage. -/
noncomputable def afterUnpair (v : Fin 16 → ℕ) : Fin 16 → ℕ :=
  writeWindow unpairWindow (afterGuard v)
    (unpairVals (fun j => afterGuard v (unpairWindow j)) (v 0))

noncomputable def projVals (v : Fin 16 → ℕ) (wj : Fin 9) : Fin 16 → ℕ :=
  Function.update (Function.update (afterUnpair v) 2 (if v 0 < v 1 then 1 else 0)) 3
    (0 + (if v 0 < v 1 then 1 else 0) * afterUnpair v (unpairWindow wj))

lemma afterGuard_zero (v : Fin 16 → ℕ) : afterGuard v 0 = v 0 := by
  simp [afterGuard, Function.update_apply]

lemma afterUnpair_window (v : Fin 16 → ℕ) (j : Fin 9) :
    afterUnpair v (unpairWindow j) =
      unpairVals (fun i => afterGuard v (unpairWindow i)) (v 0) j := by
  rw [afterUnpair, writeWindow_apply]

lemma afterUnpair_left (v : Fin 16 → ℕ) :
    afterUnpair v (unpairWindow 0) = (Nat.unpair (v 0)).1 := by
  rw [afterUnpair_window, unpairVals_zero]

lemma afterUnpair_right (v : Fin 16 → ℕ) :
    afterUnpair v (unpairWindow 1) = (Nat.unpair (v 0)).2 := by
  rw [afterUnpair_window, unpairVals_one]

lemma leftVals_encodes (v : Fin 16 → ℕ) :
    EncodesEvaln Nat.Partrec.Code.left v (projVals v 0) := by
  constructor
  · rw [evaln_left_eq, projVals]
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  · rw [evaln_left_eq, projVals]
    simp only [Function.update_apply, afterUnpair_left]
    split_ifs <;> simp_all

lemma rightVals_encodes (v : Fin 16 → ℕ) :
    EncodesEvaln Nat.Partrec.Code.right v (projVals v 1) := by
  constructor
  · rw [evaln_right_eq, projVals]
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  · rw [evaln_right_eq, projVals]
    simp only [Function.update_apply, afterUnpair_right]
    split_ifs <;> simp_all

lemma compileProj_hoareTime (r : CodeRegs n) (wj : Fin 9) (v : Fin 16 → ℕ) (B : ℕ)
    (inp₀ : Tape) (w₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hpark : ∀ i, Parked (w₀ i)) (hB : ∀ k, v k < B) :
    (compileProj r wj).HoareTime
      (EmitPred inp₀ (regsWork r w₀ v) ys)
      (EmitPred inp₀ (regsWork r w₀ (projVals v wj)) ys)
      (5 * evalnArithmeticCost B + 4) := by
  have hpv := parked_regsWork r hpark
  have hle : ∀ k, v k ≤ B := fun k => Nat.le_of_lt (hB k)
  have hg : (if v 0 < v 1 then 1 else 0) ≤ B := by have := hB 0; split_ifs <;> omega
  -- S1: guard
  have h1 := ltFlagTM_hoareTime (r 0) (r 1) (r 5) (r 4)
      (r.ne (by decide)) (r.ne (by decide)) (r.ne (by decide))
      (v 0) (v 1) (v 5) (v 4) inp₀ (regsWork r w₀ v) ys hinp₀ (hpv v)
      (regsWork_apply r w₀ v 0) (regsWork_apply r w₀ v 1)
      (regsWork_apply r w₀ v 5) (regsWork_apply r w₀ v 4)
  rw [regsWork_update, regsWork_update] at h1
  replace h1 := h1.mono_bound
    (ltFlagTime_le_arith (v 0) (v 1) (v 5) (v 4) B (hle 0) (hle 1) (hle 5) (hle 4))
  have hAG : Function.update (Function.update v 5 (v 1 - v 0)) 4
      (if v 0 < v 1 then 1 else 0) = afterGuard v := rfl
  rw [hAG] at h1
  have hB1 : 1 ≤ B := by have := hB 0; omega
  have hAGle : ∀ k, afterGuard v k ≤ B := by
    intro k
    rw [afterGuard]
    simp only [Function.update_apply]
    split_ifs <;> (have h1 := hle 1; have hk := hle k; omega)
  -- S2: unpair the input into the window
  have hctr : ∀ k : Fin 9, (unpairWindow.trans r) k ≠ r 0 := by
    intro k
    refine Regs.ne r ?_
    intro e
    have := congrArg Fin.val e
    simp [unpairWindow] at this
  have h2 := unpairTM_hoareTime_arith (unpairWindow.trans r) (r 0) hctr
      (fun j => afterGuard v (unpairWindow j)) (v 0) B inp₀
      (regsWork r w₀ (afterGuard v)) ys hinp₀ (hpv (afterGuard v))
      (by rw [regsWork_apply, afterGuard_zero]) (hle 0)
      (fun k => hAGle (unpairWindow k))
  rw [← regsWork_restrict, regsWork_window] at h2
  have hAU : writeWindow unpairWindow (afterGuard v)
      (unpairVals (fun j => afterGuard v (unpairWindow j)) (v 0)) = afterUnpair v := rfl
  rw [hAU] at h2
  have hAUle : ∀ k, afterUnpair v k ≤ B := by
    intro k
    by_cases hk : ∃ j, unpairWindow j = k
    · obtain ⟨j, rfl⟩ := hk
      rw [afterUnpair_window]
      exact unpairVals_bounded _ B (fun i => hAGle (unpairWindow i)) (v 0) (hle 0) j
    · rw [afterUnpair, writeWindow_of_ne _ _ _ (fun j e => hk ⟨j, e⟩)]
      exact hAGle k
  have hAU4 : afterUnpair v 4 = (if v 0 < v 1 then 1 else 0) := by
    rw [afterUnpair, writeWindow_of_ne _ _ _ (by decide), afterGuard]
    simp [Function.update_apply]
  have hAU2 : afterUnpair v 2 = v 2 := by
    rw [afterUnpair, writeWindow_of_ne _ _ _ (by decide), afterGuard]
    simp [Function.update_apply]
  -- S3: tag := gflag
  have h3 := copyIntoTM_hoareTime (r 4) (r 2) (r.ne (by decide))
      (if v 0 < v 1 then 1 else 0) (v 2) inp₀ (regsWork r w₀ (afterUnpair v)) ys hinp₀
      (fun i _ => hpv (afterUnpair v) i)
      (by rw [regsWork_apply, hAU4]) (by rw [regsWork_apply, hAU2])
  rw [regsWork_update] at h3
  replace h3 := h3.mono_bound
    (copyIntoTime_le_arith (if v 0 < v 1 then 1 else 0) (v 2) B hg (hle 2))
  set V3 := Function.update (afterUnpair v) 2 (if v 0 < v 1 then 1 else 0) with hV3
  have g3_3 : V3 3 = afterUnpair v 3 := by rw [hV3]; simp [Function.update_apply]
  -- S4: val := 0
  have h4 := clearRegTM_hoareTime (r 3) (afterUnpair v 3) inp₀ (regsWork r w₀ V3) ys hinp₀
      (fun i _ => hpv V3 i) (by rw [regsWork_apply, g3_3])
  rw [regsWork_update] at h4
  replace h4 := h4.mono_bound (regOpTime_le_arith (afterUnpair v 3) B (hAUle 3))
  set V4 := Function.update V3 3 0 with hV4
  have g4_4 : V4 4 = (if v 0 < v 1 then 1 else 0) := by
    rw [hV4, hV3]; simp [Function.update_apply, hAU4]
  have g4_w : V4 (unpairWindow wj) = afterUnpair v (unpairWindow wj) := by
    rw [hV4, hV3]
    have h2' : unpairWindow wj ≠ (2 : Fin 16) := by
      intro e; have := congrArg Fin.val e; simp [unpairWindow] at this
    have h3' : unpairWindow wj ≠ (3 : Fin 16) := by
      intro e; have := congrArg Fin.val e; simp [unpairWindow] at this
    simp [Function.update_apply, h2', h3']
  have g4_3 : V4 3 = 0 := by rw [hV4]; simp [Function.update_apply]
  -- S5: val := gflag * projection
  have h5 := mulAddIntoTM_hoareTime (r 4) (r (unpairWindow wj)) (r 3)
      (r.ne (by intro e; have := congrArg Fin.val e; simp [unpairWindow] at this))
      (r.ne (by decide))
      (r.ne (by intro e; have := congrArg Fin.val e; simp [unpairWindow] at this))
      (if v 0 < v 1 then 1 else 0) (afterUnpair v (unpairWindow wj)) 0 inp₀
      (regsWork r w₀ V4) ys hinp₀ (fun i _ => hpv V4 i)
      (by rw [regsWork_apply, g4_4]) (by rw [regsWork_apply, g4_w])
      (by rw [regsWork_apply, g4_3])
  rw [regsWork_update] at h5
  replace h5 := h5.mono_bound
    (mulAddTime_le_arith (if v 0 < v 1 then 1 else 0)
      (afterUnpair v (unpairWindow wj)) 0 B hg (hAUle _) (by omega))
  have hfin : Function.update V4 3
      (0 + (if v 0 < v 1 then 1 else 0) * afterUnpair v (unpairWindow wj))
      = projVals v wj := by
    rw [hV4, hV3, projVals, Function.update_idem]
  rw [hfin] at h5
  exact (seqEmit hinp₀ (hpv (afterGuard v)) h1 <|
    seqEmit hinp₀ (hpv (afterUnpair v)) h2 <|
    seqEmit hinp₀ (hpv V3) h3 <|
    seqEmit hinp₀ (hpv V4) h4 h5).mono_bound (by omega)

/-- `evaln k left n`, exactly. -/
def compileLeft (r : CodeRegs n) : TM n := compileProj r 0

/-- `evaln k right n`, exactly. -/
def compileRight (r : CodeRegs n) : TM n := compileProj r 1

end LogicalInduction.EvalnCompiler
