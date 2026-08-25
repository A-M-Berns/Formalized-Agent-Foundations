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

/-! ## `pair` and `comp`: exact equations and the mask formulas

Both recursive children receive the parent's fuel **undecremented** — `evaln (k+1) cf n`
and `evaln (k+1) cg n` for `pair`, `evaln (k+1) cg n` then `evaln (k+1) cf x` for `comp`.
Only `prec` and `rfind'` decrement, and only for their self-calls. -/

lemma evaln_pair_eq (k : ℕ) (cf cg : Nat.Partrec.Code) (m : ℕ) :
    Nat.Partrec.Code.evaln k (cf.pair cg) m
      = if m < k then
          (Nat.pair <$> Nat.Partrec.Code.evaln k cf m <*> Nat.Partrec.Code.evaln k cg m)
        else none := by
  cases k with
  | zero => simp [Nat.Partrec.Code.evaln]
  | succ k =>
    simp only [Nat.Partrec.Code.evaln, Nat.lt_succ_iff]
    split_ifs with h <;> simp [h]

lemma evaln_comp_eq (k : ℕ) (cf cg : Nat.Partrec.Code) (m : ℕ) :
    Nat.Partrec.Code.evaln k (cf.comp cg) m
      = if m < k then
          (Nat.Partrec.Code.evaln k cg m >>= fun x => Nat.Partrec.Code.evaln k cf x)
        else none := by
  cases k with
  | zero => simp [Nat.Partrec.Code.evaln]
  | succ k =>
    simp only [Nat.Partrec.Code.evaln, Nat.lt_succ_iff]
    split_ifs with h <;> simp [h]

/-! ### The masks

Each says: the compiled machine may run **every** subcomputation unconditionally and
recover the exact `evaln` answer by multiplying the result registers by a product of
`0/1` tags. No control flow is needed to suppress a failed branch. -/

@[simp] lemma resultTag_mul_resultVal (o : Option ℕ) :
    resultTag o * resultVal o = resultVal o := by cases o <;> simp

lemma pair_mask_tag (k : ℕ) (cf cg : Nat.Partrec.Code) (m : ℕ) :
    resultTag (Nat.Partrec.Code.evaln k (cf.pair cg) m)
      = (if m < k then 1 else 0) * resultTag (Nat.Partrec.Code.evaln k cf m)
          * resultTag (Nat.Partrec.Code.evaln k cg m) := by
  rw [evaln_pair_eq]
  cases hF : Nat.Partrec.Code.evaln k cf m <;> cases hG : Nat.Partrec.Code.evaln k cg m <;>
    split_ifs <;> simp [Seq.seq]

lemma pair_mask_val (k : ℕ) (cf cg : Nat.Partrec.Code) (m : ℕ) :
    resultVal (Nat.Partrec.Code.evaln k (cf.pair cg) m)
      = (if m < k then 1 else 0) * resultTag (Nat.Partrec.Code.evaln k cf m)
          * resultTag (Nat.Partrec.Code.evaln k cg m)
          * Nat.pair (resultVal (Nat.Partrec.Code.evaln k cf m))
              (resultVal (Nat.Partrec.Code.evaln k cg m)) := by
  rw [evaln_pair_eq]
  cases hF : Nat.Partrec.Code.evaln k cf m <;> cases hG : Nat.Partrec.Code.evaln k cg m <;>
    split_ifs <;> simp [Seq.seq]

/-- **The `comp` mask.** `cf` is applied to `resultVal` of `cg`'s answer — which is `0`
    when `cg` failed, so the machine may run `cf` on garbage and still be exactly right,
    because the `cg` tag factor zeroes the product. -/
lemma comp_mask_tag (k : ℕ) (cf cg : Nat.Partrec.Code) (m : ℕ) :
    resultTag (Nat.Partrec.Code.evaln k (cf.comp cg) m)
      = (if m < k then 1 else 0) * resultTag (Nat.Partrec.Code.evaln k cg m)
          * resultTag (Nat.Partrec.Code.evaln k cf
              (resultVal (Nat.Partrec.Code.evaln k cg m))) := by
  rw [evaln_comp_eq]
  cases hG : Nat.Partrec.Code.evaln k cg m <;> split_ifs <;> simp [Seq.seq]

lemma comp_mask_val (k : ℕ) (cf cg : Nat.Partrec.Code) (m : ℕ) :
    resultVal (Nat.Partrec.Code.evaln k (cf.comp cg) m)
      = (if m < k then 1 else 0) * resultTag (Nat.Partrec.Code.evaln k cg m)
          * resultTag (Nat.Partrec.Code.evaln k cf
              (resultVal (Nat.Partrec.Code.evaln k cg m)))
          * resultVal (Nat.Partrec.Code.evaln k cf
              (resultVal (Nat.Partrec.Code.evaln k cg m))) := by
  rw [evaln_comp_eq]
  cases hG : Nat.Partrec.Code.evaln k cg m <;> split_ifs <;> simp [Seq.seq]
/-! ## Ambient-arity compilation: size-indexed disjoint register intervals

A compiled machine for `c` uses `16 * codeSize c` registers of an ambient file, laid out as
disjoint intervals: the node's own sixteen first, then each child's whole subtree. Parent
and children are all `TM n` for the *same* ambient `n`; only the naming embedding differs,
so ordinary `seqTM` composes them and no lifting is needed.

Because the intervals are disjoint, a child's execution cannot touch the parent's block —
that is structural (`writeWindow_of_ne` on an index range), not a frame argument. -/

/-- Registers a compiled code occupies: its own block plus its children's subtrees.

    Defined *directly* rather than as `16 * codeSize c`, so that
    `codeRegs (pair cf cg)` reduces to `16 + codeRegs cf + codeRegs cg`
    **definitionally**. Without that every recursive call in `compileCodeAt` would need a
    transport along an arity equation, and the dependent-type friction would spread
    through the whole assembly. -/
def codeRegs : Nat.Partrec.Code → ℕ
  | .zero => 16
  | .succ => 16
  | .left => 16
  | .right => 16
  | .pair cf cg => 16 + codeRegs cf + codeRegs cg
  | .comp cf cg => 16 + codeRegs cf + codeRegs cg
  | .prec cf cg => 16 + codeRegs cf + codeRegs cg
  | .rfind' cf => 16 + codeRegs cf

lemma codeRegs_ge (c : Nat.Partrec.Code) : 16 ≤ codeRegs c := by
  cases c <;> simp [codeRegs] <;> omega

/-! ### The three intervals of a binary node

For `pair cf cg` / `comp cf cg`, `codeRegs = 16 + codeRegs cf + codeRegs cg`. -/

variable (cf cg : Nat.Partrec.Code)

/-- Self block fits. -/
lemma selfFits : 0 + 16 ≤ 16 + codeRegs cf + codeRegs cg := by omega

/-- First child's subtree fits. -/
lemma leftFits : 16 + codeRegs cf ≤ 16 + codeRegs cf + codeRegs cg := by omega

/-- Second child's subtree fits. -/
lemma rightFits : (16 + codeRegs cf) + codeRegs cg ≤ 16 + codeRegs cf + codeRegs cg := by
  omega

/-- The first child's *local* sixteen fit. -/
lemma leftLocalFits : 16 + 16 ≤ 16 + codeRegs cf + codeRegs cg := by
  have := codeRegs_ge cf; omega

/-- The second child's *local* sixteen fit. -/
lemma rightLocalFits : (16 + codeRegs cf) + 16 ≤ 16 + codeRegs cf + codeRegs cg := by
  have := codeRegs_ge cg; omega

/-! ### Windows of a binary node

Ambient arity `16 + af + ag`: the node's own sixteen at offset `0`, the first child's
subtree at `16`, the second's at `16 + af`. `selfW`/`leftLoc`/`rightLoc` name the three
*local* sixteen-register blocks; `leftSub`/`rightSub` name the children's whole subtrees,
which is what a child machine's spec is stated over. -/

section Binary
variable {af ag : ℕ}

/-- The node's own sixteen registers. -/
def selfW (af ag : ℕ) : Fin 16 ↪ Fin (16 + af + ag) := shiftEmb 0 (by omega)
/-- The first child's whole subtree. -/
def leftSub (af ag : ℕ) : Fin af ↪ Fin (16 + af + ag) := shiftEmb 16 (by omega)
/-- The second child's whole subtree. -/
def rightSub (af ag : ℕ) : Fin ag ↪ Fin (16 + af + ag) := shiftEmb (16 + af) (by omega)
/-- The first child's own sixteen. -/
def leftLoc (af ag : ℕ) (h : 16 ≤ af) : Fin 16 ↪ Fin (16 + af + ag) :=
  shiftEmb 16 (by omega)
/-- The second child's own sixteen. -/
def rightLoc (af ag : ℕ) (h : 16 ≤ ag) : Fin 16 ↪ Fin (16 + af + ag) :=
  shiftEmb (16 + af) (by omega)

/-- A child's local block is the first sixteen of its subtree. -/
lemma leftLoc_eq (h : 16 ≤ af) (j : Fin 16) :
    leftLoc af ag h j = leftSub af ag ⟨(j : ℕ), by have := j.isLt; omega⟩ := by
  apply Fin.ext; simp [leftLoc, leftSub, shiftEmb_val]

lemma rightLoc_eq (h : 16 ≤ ag) (j : Fin 16) :
    rightLoc af ag h j = rightSub af ag ⟨(j : ℕ), by have := j.isLt; omega⟩ := by
  apply Fin.ext; simp [rightLoc, rightSub, shiftEmb_val]

/-- `pairTM` occupies registers `6`–`13` of the node's own block. -/
def pairSlot : Fin 8 ↪ Fin 16 := shiftEmb 6 (by omega)

end Binary

/-! ### Index disequalities for a binary node

All of them reduce to arithmetic on the three offsets `0`, `16`, `16 + af`. -/

section BinaryNe
variable {af ag : ℕ}

lemma selfW_ne_selfW (i j : Fin 16) (h : (i : ℕ) ≠ (j : ℕ)) :
    selfW af ag i ≠ selfW af ag j := by
  apply amb_ne; simpa using h

lemma selfW_ne_leftLoc (haf : 16 ≤ af) (i j : Fin 16) :
    selfW af ag i ≠ leftLoc af ag haf j := by
  apply amb_ne; have := i.isLt; simp; omega

lemma selfW_ne_rightLoc (hag : 16 ≤ ag) (haf : 16 ≤ af) (i j : Fin 16) :
    selfW af ag i ≠ rightLoc af ag hag j := by
  apply amb_ne; have := i.isLt; simp; omega

lemma leftLoc_ne_rightLoc (haf : 16 ≤ af) (hag : 16 ≤ ag) (i j : Fin 16) :
    leftLoc af ag haf i ≠ rightLoc af ag hag j := by
  apply amb_ne; have := i.isLt; simp; omega

/-- The self block is outside the first child's subtree. -/
lemma leftSub_ne_selfW (i : Fin af) (j : Fin 16) :
    leftSub af ag i ≠ selfW af ag j := by
  apply amb_ne; have := j.isLt; simp; omega

/-- The self block is outside the second child's subtree. -/
lemma rightSub_ne_selfW (haf : 16 ≤ af) (i : Fin ag) (j : Fin 16) :
    rightSub af ag i ≠ selfW af ag j := by
  apply amb_ne; have := j.isLt; simp; omega

/-- The first child's block is outside the second child's subtree. -/
lemma rightSub_ne_leftLoc (haf : 16 ≤ af) (i : Fin ag) (j : Fin 16) :
    rightSub af ag i ≠ leftLoc af ag haf j := by
  apply amb_ne; have := j.isLt; simp; omega

end BinaryNe

/-! ### Semantic closure: the machine's mask arithmetic *is* `evaln`

These are the theorems the machine proofs reduce to. Once a compiled node has computed
`gflag * tagF * tagG` into its tag register and `tag * Nat.pair valF valG` into its value
register, correctness is exactly the already-proved mask identity — no case analysis on
which child failed. -/

lemma pair_encodes (k m tagF valF tagG valG : ℕ) (cf cg : Nat.Partrec.Code)
    (hFt : tagF = resultTag (Nat.Partrec.Code.evaln k cf m))
    (hFv : valF = resultVal (Nat.Partrec.Code.evaln k cf m))
    (hGt : tagG = resultTag (Nat.Partrec.Code.evaln k cg m))
    (hGv : valG = resultVal (Nat.Partrec.Code.evaln k cg m)) :
    (if m < k then 1 else 0) * tagF * tagG
        = resultTag (Nat.Partrec.Code.evaln k (cf.pair cg) m) ∧
      ((if m < k then 1 else 0) * tagF * tagG) * Nat.pair valF valG
        = resultVal (Nat.Partrec.Code.evaln k (cf.pair cg) m) := by
  subst hFt; subst hFv; subst hGt; subst hGv
  exact ⟨(pair_mask_tag k cf cg m).symm, (pair_mask_val k cf cg m).symm⟩

/-- For `comp` the second factor is `cf` applied to `cg`'s *value* — which is `0` when `cg`
    failed. The machine runs `cf` on that `0` unconditionally and the `cg` tag factor
    zeroes the product, so no branch is needed. -/
lemma comp_encodes (k m tagG valG tagF valF : ℕ) (cf cg : Nat.Partrec.Code)
    (hGt : tagG = resultTag (Nat.Partrec.Code.evaln k cg m))
    (hGv : valG = resultVal (Nat.Partrec.Code.evaln k cg m))
    (hFt : tagF = resultTag (Nat.Partrec.Code.evaln k cf valG))
    (hFv : valF = resultVal (Nat.Partrec.Code.evaln k cf valG)) :
    (if m < k then 1 else 0) * tagG * tagF
        = resultTag (Nat.Partrec.Code.evaln k (cf.comp cg) m) ∧
      ((if m < k then 1 else 0) * tagG * tagF) * valF
        = resultVal (Nat.Partrec.Code.evaln k (cf.comp cg) m) := by
  subst hGt; subst hGv; subst hFt; subst hFv
  exact ⟨(comp_mask_tag k cf cg m).symm, (comp_mask_val k cf cg m).symm⟩

/-! ### Phase A of `pair`: feed both children and run them

The phase that exercises nested compilation. Both children receive the parent's *original*
input and fuel (undecremented, per the `evaln` equation), each runs in its own subtree, and
the parent's own block is preserved — structurally, because the intervals are disjoint. -/

section PhaseA
variable {af ag : ℕ}

/-- The first child's subtree misses the second child's block. -/
lemma leftSub_ne_rightLoc (hag : 16 ≤ ag) (i : Fin af) (j : Fin 16) :
    leftSub af ag i ≠ rightLoc af ag hag j := by
  apply amb_ne; have := i.isLt; simp; omega

def pairPhaseA (af ag : ℕ) (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (R : Regs (16 + af + ag) n) (Mf Mg : TM n) : TM n :=
  seqTM (copyIntoTM (R (selfW af ag 0)) (R (leftLoc af ag haf 0))) <|
  seqTM (copyIntoTM (R (selfW af ag 1)) (R (leftLoc af ag haf 1))) <|
  seqTM Mf <|
  seqTM (copyIntoTM (R (selfW af ag 0)) (R (rightLoc af ag hag 0))) <|
  seqTM (copyIntoTM (R (selfW af ag 1)) (R (rightLoc af ag hag 1)))
        Mg

noncomputable def pairPhaseAVec (af ag : ℕ) (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (Ff : (Fin af → ℕ) → Fin af → ℕ) (Fg : (Fin ag → ℕ) → Fin ag → ℕ)
    (V : Fin (16 + af + ag) → ℕ) : Fin (16 + af + ag) → ℕ :=
  let V1 := Function.update V (leftLoc af ag haf 0) (V (selfW af ag 0))
  let V2 := Function.update V1 (leftLoc af ag haf 1) (V (selfW af ag 1))
  let V3 := writeWindow (leftSub af ag) V2 (Ff (fun j => V2 (leftSub af ag j)))
  let V4 := Function.update V3 (rightLoc af ag hag 0) (V (selfW af ag 0))
  let V5 := Function.update V4 (rightLoc af ag hag 1) (V (selfW af ag 1))
  writeWindow (rightSub af ag) V5 (Fg (fun j => V5 (rightSub af ag j)))

lemma pairPhaseA_hoareTime (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (R : Regs (16 + af + ag) n) (Mf Mg : TM n)
    (Ff : (Fin af → ℕ) → Fin af → ℕ) (Fg : (Fin ag → ℕ) → Fin ag → ℕ) (tf tg : ℕ)
    (V : Fin (16 + af + ag) → ℕ) (B : ℕ)
    (inp₀ : Tape) (w₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hpark : ∀ i, Parked (w₀ i)) (hB : ∀ k, V k < B)
    (hFfB : ∀ u : Fin af → ℕ, (∀ k, u k < B) → ∀ k, Ff u k < B)
    (hFgB : ∀ u : Fin ag → ℕ, (∀ k, u k < B) → ∀ k, Fg u k < B)
    (hMf : ∀ (Wb : Fin n → Tape) (u : Fin af → ℕ), (∀ i, Parked (Wb i)) → (∀ k, u k < B) →
      Mf.HoareTime (EmitPred inp₀ (regsWork ((leftSub af ag).trans R) Wb u) ys)
                   (EmitPred inp₀ (regsWork ((leftSub af ag).trans R) Wb (Ff u)) ys) tf)
    (hMg : ∀ (Wb : Fin n → Tape) (u : Fin ag → ℕ), (∀ i, Parked (Wb i)) → (∀ k, u k < B) →
      Mg.HoareTime (EmitPred inp₀ (regsWork ((rightSub af ag).trans R) Wb u) ys)
                   (EmitPred inp₀ (regsWork ((rightSub af ag).trans R) Wb (Fg u)) ys) tg) :
    (pairPhaseA af ag haf hag R Mf Mg).HoareTime
      (EmitPred inp₀ (regsWork R w₀ V) ys)
      (EmitPred inp₀ (regsWork R w₀ (pairPhaseAVec af ag haf hag Ff Fg V)) ys)
      (4 * evalnArithmeticCost B + tf + tg + 5) := by
  have hpv := parked_regsWork R hpark
  have hle : ∀ k, V k ≤ B := fun k => Nat.le_of_lt (hB k)
  -- S1
  have h1 := copyIntoTM_hoareTime (R (selfW af ag 0)) (R (leftLoc af ag haf 0))
      (Regs.ne R (selfW_ne_leftLoc haf 0 0)) (V (selfW af ag 0)) (V (leftLoc af ag haf 0))
      inp₀ (regsWork R w₀ V) ys hinp₀ (fun i _ => hpv V i)
      (regsWork_apply R w₀ V _) (regsWork_apply R w₀ V _)
  rw [regsWork_update] at h1
  replace h1 := h1.mono_bound (copyIntoTime_le_arith _ _ B (hle _) (hle _))
  set V1 := Function.update V (leftLoc af ag haf 0) (V (selfW af ag 0)) with hV1
  have b1 : ∀ k, V1 k < B := by
    intro k; rw [hV1]; simp only [Function.update_apply]; split_ifs <;> exact hB _
  -- S2
  have h2 := copyIntoTM_hoareTime (R (selfW af ag 1)) (R (leftLoc af ag haf 1))
      (Regs.ne R (selfW_ne_leftLoc haf 1 1)) (V (selfW af ag 1)) (V1 (leftLoc af ag haf 1))
      inp₀ (regsWork R w₀ V1) ys hinp₀ (fun i _ => hpv V1 i)
      (by rw [regsWork_apply, hV1,
        Function.update_of_ne (selfW_ne_leftLoc haf 1 0)])
      (regsWork_apply R w₀ V1 _)
  rw [regsWork_update] at h2
  replace h2 := h2.mono_bound
    (copyIntoTime_le_arith _ _ B (hle _) (Nat.le_of_lt (b1 _)))
  set V2 := Function.update V1 (leftLoc af ag haf 1) (V (selfW af ag 1)) with hV2
  have b2 : ∀ k, V2 k < B := by
    intro k; rw [hV2]; simp only [Function.update_apply]; split_ifs
    · exact hB _
    · exact b1 _
  -- everything outside the first subtree is still `V`
  have out2 : ∀ k, (∀ j, leftSub af ag j ≠ k) → V2 k = V k := by
    intro k hk
    have e0 : leftLoc af ag haf 0 ≠ k := by
      rw [leftLoc_eq]; exact hk _
    have e1 : leftLoc af ag haf 1 ≠ k := by
      rw [leftLoc_eq]; exact hk _
    rw [hV2, Function.update_of_ne (Ne.symm e1), hV1, Function.update_of_ne (Ne.symm e0)]
  -- S3: run cf
  have h3 := runChild (leftSub af ag) R Mf Ff tf B w₀ hpark V2 b2 hMf
  set V3 := writeWindow (leftSub af ag) V2 (Ff (fun j => V2 (leftSub af ag j))) with hV3
  have b3 : ∀ k, V3 k < B := by
    intro k; rw [hV3]
    exact writeWindow_bounded _ _ _ B b2 (fun j => hFfB _ (fun i => b2 _) j) k
  have out3 : ∀ k, (∀ j, leftSub af ag j ≠ k) → V3 k = V k := by
    intro k hk
    rw [hV3, runChild_frame _ _ _ hk]; exact out2 k hk
  -- S4
  have h4 := copyIntoTM_hoareTime (R (selfW af ag 0)) (R (rightLoc af ag hag 0))
      (Regs.ne R (selfW_ne_rightLoc hag haf 0 0)) (V (selfW af ag 0))
      (V3 (rightLoc af ag hag 0))
      inp₀ (regsWork R w₀ V3) ys hinp₀ (fun i _ => hpv V3 i)
      (by rw [regsWork_apply, out3 _ (fun j => leftSub_ne_selfW j 0)])
      (regsWork_apply R w₀ V3 _)
  rw [regsWork_update] at h4
  replace h4 := h4.mono_bound
    (copyIntoTime_le_arith _ _ B (hle _) (Nat.le_of_lt (b3 _)))
  set V4 := Function.update V3 (rightLoc af ag hag 0) (V (selfW af ag 0)) with hV4
  have b4 : ∀ k, V4 k < B := by
    intro k; rw [hV4]; simp only [Function.update_apply]; split_ifs
    · exact hB _
    · exact b3 _
  -- S5
  have h5 := copyIntoTM_hoareTime (R (selfW af ag 1)) (R (rightLoc af ag hag 1))
      (Regs.ne R (selfW_ne_rightLoc hag haf 1 1)) (V (selfW af ag 1))
      (V4 (rightLoc af ag hag 1))
      inp₀ (regsWork R w₀ V4) ys hinp₀ (fun i _ => hpv V4 i)
      (by rw [regsWork_apply, hV4,
        Function.update_of_ne (selfW_ne_rightLoc hag haf 1 0),
        out3 _ (fun j => leftSub_ne_selfW j 1)])
      (regsWork_apply R w₀ V4 _)
  rw [regsWork_update] at h5
  replace h5 := h5.mono_bound
    (copyIntoTime_le_arith _ _ B (hle _) (Nat.le_of_lt (b4 _)))
  set V5 := Function.update V4 (rightLoc af ag hag 1) (V (selfW af ag 1)) with hV5
  have b5 : ∀ k, V5 k < B := by
    intro k; rw [hV5]; simp only [Function.update_apply]; split_ifs
    · exact hB _
    · exact b4 _
  -- S6: run cg
  have h6 := runChild (rightSub af ag) R Mg Fg tg B w₀ hpark V5 b5 hMg
  exact (seqEmit hinp₀ (hpv V1) h1 <|
    seqEmit hinp₀ (hpv V2) h2 <|
    seqEmit hinp₀ (hpv V3) h3 <|
    seqEmit hinp₀ (hpv V4) h4 <|
    seqEmit hinp₀ (hpv V5) h5 h6).mono_bound (by omega)

end PhaseA

/-! ### Phase B of `pair`: pair the child values and mask

Ten single-register stages over one ambient vector. Stated over an *arbitrary* entry
vector `W`, so it composes with Phase A by instantiation rather than by threading.

The only value that can leave the size bound is `pairTM`'s output, so that is the one
explicit hypothesis (`hfit`); the caller supplies a `B` large enough, which is exactly what
`codeEvalBound` will do at the global step. -/

section PhaseB
variable {af ag : ℕ}

def pairPhaseB (af ag : ℕ) (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (R : Regs (16 + af + ag) n) : TM n :=
  seqTM (copyIntoTM (R (leftLoc af ag haf 3)) (R (selfW af ag 6))) <|
  seqTM (copyIntoTM (R (rightLoc af ag hag 3)) (R (selfW af ag 7))) <|
  seqTM (pairTM (pairSlot.trans ((selfW af ag).trans R))) <|
  seqTM (ltFlagTM (R (selfW af ag 0)) (R (selfW af ag 1))
          (R (selfW af ag 5)) (R (selfW af ag 4))) <|
  seqTM (clearRegTM (R (selfW af ag 14))) <|
  seqTM (mulAddIntoTM (R (selfW af ag 4)) (R (leftLoc af ag haf 2))
          (R (selfW af ag 14))) <|
  seqTM (clearRegTM (R (selfW af ag 2))) <|
  seqTM (mulAddIntoTM (R (selfW af ag 14)) (R (rightLoc af ag hag 2))
          (R (selfW af ag 2))) <|
  seqTM (clearRegTM (R (selfW af ag 3)))
        (mulAddIntoTM (R (selfW af ag 2)) (R (selfW af ag 12)) (R (selfW af ag 3)))

noncomputable def pairPhaseBVec (af ag : ℕ) (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (W : Fin (16 + af + ag) → ℕ) : Fin (16 + af + ag) → ℕ :=
  let W7 := Function.update W (selfW af ag 6) (W (leftLoc af ag haf 3))
  let W8 := Function.update W7 (selfW af ag 7) (W7 (rightLoc af ag hag 3))
  let W9 := writeWindow (pairSlot.trans (selfW af ag)) W8
              (pairVals (fun j => W8 ((pairSlot.trans (selfW af ag)) j)))
  let W10 := Function.update W9 (selfW af ag 5) (W9 (selfW af ag 1) - W9 (selfW af ag 0))
  let W11 := Function.update W10 (selfW af ag 4)
              (if W9 (selfW af ag 0) < W9 (selfW af ag 1) then 1 else 0)
  let W12 := Function.update W11 (selfW af ag 14) 0
  let W13 := Function.update W12 (selfW af ag 14)
              (0 + W12 (selfW af ag 4) * W12 (leftLoc af ag haf 2))
  let W14 := Function.update W13 (selfW af ag 2) 0
  let W15 := Function.update W14 (selfW af ag 2)
              (0 + W14 (selfW af ag 14) * W14 (rightLoc af ag hag 2))
  let W16 := Function.update W15 (selfW af ag 3) 0
  Function.update W16 (selfW af ag 3)
    (0 + W16 (selfW af ag 2) * W16 (selfW af ag 12))

end PhaseB

section PhaseBProof
variable {af ag : ℕ}

/-- `pairTM`'s eight registers, as an ambient window: offset `6` of the node's block. -/
def pairAmb (af ag : ℕ) : Fin 8 ↪ Fin (16 + af + ag) := shiftEmb 6 (by omega)

lemma pairAmb_eq : pairSlot.trans (selfW af ag) = pairAmb af ag := by
  apply Function.Embedding.ext
  intro j
  apply Fin.ext
  simp [pairSlot, selfW, pairAmb, shiftEmb_val]

lemma pairAmb_ne_selfW (i : Fin 8) (j : Fin 16) (h : 6 + (i : ℕ) ≠ (j : ℕ)) :
    pairAmb af ag i ≠ selfW af ag j := by
  apply amb_ne; simpa using h

lemma pairAmb_ne_leftLoc (haf : 16 ≤ af) (i : Fin 8) (j : Fin 16) :
    pairAmb af ag i ≠ leftLoc af ag haf j := by
  apply amb_ne; have := i.isLt; simp; omega

lemma pairAmb_ne_rightLoc (hag : 16 ≤ ag) (haf : 16 ≤ af) (i : Fin 8) (j : Fin 16) :
    pairAmb af ag i ≠ rightLoc af ag hag j := by
  apply amb_ne; have := i.isLt; simp; omega

lemma pairTrans_zero : (pairSlot.trans (selfW af ag)) 0 = selfW af ag 6 := by
  have h : pairSlot 0 = (6 : Fin 16) := by decide
  simp [Function.Embedding.trans_apply, h]

lemma pairTrans_one : (pairSlot.trans (selfW af ag)) 1 = selfW af ag 7 := by
  have h : pairSlot 1 = (7 : Fin 16) := by decide
  simp [Function.Embedding.trans_apply, h]

lemma pairTrans_six : (pairSlot.trans (selfW af ag)) 6 = selfW af ag 12 := by
  have h : pairSlot 6 = (12 : Fin 16) := by decide
  simp [Function.Embedding.trans_apply, h]

/-- `selfW 12` is `pairTM`'s output register. -/
lemma selfW_twelve : selfW af ag 12 = pairAmb af ag 6 := by
  apply Fin.ext; simp [selfW, pairAmb, shiftEmb_val]

lemma selfW_six : selfW af ag 6 = pairAmb af ag 0 := by
  apply Fin.ext; simp [selfW, pairAmb, shiftEmb_val]

lemma selfW_seven : selfW af ag 7 = pairAmb af ag 1 := by
  apply Fin.ext; simp [selfW, pairAmb, shiftEmb_val]

/-- Every value `pairTM` leaves in its window stays inside the bound, given that its
    output does. -/
lemma pairVals_lt (v : Fin 8 → ℕ) (B : ℕ) (hB2 : 2 ≤ B) (hv : ∀ k, v k < B)
    (hfit : Nat.pair (v 0) (v 1) < B) (k : Fin 8) : pairVals v k < B := by
  have h0 := hv 0
  have h1 := hv 1
  have hk := hv k
  simp only [pairVals]
  split_ifs <;> omega

end PhaseBProof

section PhaseBMain
variable {af ag : ℕ}

lemma pairPhaseB_hoareTime (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (R : Regs (16 + af + ag) n) (W : Fin (16 + af + ag) → ℕ) (B : ℕ)
    (inp₀ : Tape) (w₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hpark : ∀ i, Parked (w₀ i)) (hB2 : 2 ≤ B)
    (hW : ∀ k, W k < B)
    (hfit : Nat.pair (W (leftLoc af ag haf 3)) (W (rightLoc af ag hag 3)) < B)
    (htagF : W (leftLoc af ag haf 2) ≤ 1) (htagG : W (rightLoc af ag hag 2) ≤ 1) :
    (pairPhaseB af ag haf hag R).HoareTime
      (EmitPred inp₀ (regsWork R w₀ W) ys)
      (EmitPred inp₀ (regsWork R w₀ (pairPhaseBVec af ag haf hag W)) ys)
      (10 * evalnArithmeticCost B + 9) := by
  have hpv := parked_regsWork R hpark
  have hle : ∀ k, W k ≤ B := fun k => Nat.le_of_lt (hW k)
  -- S7: pair slot a := cf.val
  have h7 := copyIntoTM_hoareTime (R (leftLoc af ag haf 3)) (R (selfW af ag 6))
      (Regs.ne R (Ne.symm (selfW_ne_leftLoc haf 6 3)))
      (W (leftLoc af ag haf 3)) (W (selfW af ag 6))
      inp₀ (regsWork R w₀ W) ys hinp₀ (fun i _ => hpv W i)
      (regsWork_apply R w₀ W _) (regsWork_apply R w₀ W _)
  rw [regsWork_update] at h7
  replace h7 := h7.mono_bound (copyIntoTime_le_arith _ _ B (hle _) (hle _))
  set W7 := Function.update W (selfW af ag 6) (W (leftLoc af ag haf 3)) with hW7
  have b7 : ∀ k, W7 k < B := by
    intro k; rw [hW7]; simp only [Function.update_apply]; split_ifs <;> exact hW _
  have r7_Lg3 : W7 (rightLoc af ag hag 3) = W (rightLoc af ag hag 3) := by
    rw [hW7, Function.update_of_ne (Ne.symm (selfW_ne_rightLoc hag haf 6 3))]
  -- S8: pair slot b := cg.val
  have h8 := copyIntoTM_hoareTime (R (rightLoc af ag hag 3)) (R (selfW af ag 7))
      (Regs.ne R (Ne.symm (selfW_ne_rightLoc hag haf 7 3)))
      (W7 (rightLoc af ag hag 3)) (W7 (selfW af ag 7))
      inp₀ (regsWork R w₀ W7) ys hinp₀ (fun i _ => hpv W7 i)
      (regsWork_apply R w₀ W7 _) (regsWork_apply R w₀ W7 _)
  rw [regsWork_update] at h8
  replace h8 := h8.mono_bound
    (copyIntoTime_le_arith _ _ B (Nat.le_of_lt (b7 _)) (Nat.le_of_lt (b7 _)))
  set W8 := Function.update W7 (selfW af ag 7) (W7 (rightLoc af ag hag 3)) with hW8
  have b8 : ∀ k, W8 k < B := by
    intro k; rw [hW8]; simp only [Function.update_apply]; split_ifs <;> exact b7 _
  have r8_6 : W8 (selfW af ag 6) = W (leftLoc af ag haf 3) := by
    rw [hW8, Function.update_of_ne (selfW_ne_selfW 6 7 (by decide)), hW7,
      Function.update_self]
  have r8_7 : W8 (selfW af ag 7) = W (rightLoc af ag hag 3) := by
    rw [hW8, Function.update_self, r7_Lg3]
  have hps0 : pairSlot 0 = (6 : Fin 16) := by decide
  have hps1 : pairSlot 1 = (7 : Fin 16) := by decide
  -- S9: pair the two values
  have hpairspec : ∀ (Wb : Fin n → Tape) (u : Fin 8 → ℕ), (∀ i, Parked (Wb i)) →
      (∀ k, u k < B) →
      (pairTM (pairSlot.trans ((selfW af ag).trans R))).HoareTime
        (EmitPred inp₀ (regsWork ((pairSlot.trans (selfW af ag)).trans R) Wb u) ys)
        (EmitPred inp₀ (regsWork ((pairSlot.trans (selfW af ag)).trans R) Wb
          (pairVals u)) ys) (evalnArithmeticCost B) :=
    fun Wb u hp hu => pairTM_hoareTime_arith _ u B inp₀ Wb ys hinp₀ hp
      (fun k => Nat.le_of_lt (hu k))
  have h9 := runChild (pairSlot.trans (selfW af ag)) R
      (pairTM (pairSlot.trans ((selfW af ag).trans R))) pairVals
      (evalnArithmeticCost B) B w₀ hpark W8 b8 hpairspec
  set W9 := writeWindow (pairSlot.trans (selfW af ag)) W8
      (pairVals (fun j => W8 ((pairSlot.trans (selfW af ag)) j))) with hW9
  have b9 : ∀ k, W9 k < B := by
    intro k; rw [hW9]
    refine writeWindow_bounded _ _ _ B b8 (fun j => ?_) k
    refine pairVals_lt _ B hB2 (fun i => b8 _) ?_ j
    simp only [Function.Embedding.trans_apply, hps0, hps1]
    rw [r8_6, r8_7]; exact hfit

  -- reads through the pair window
  have r9 : ∀ (i : Fin 16), (∀ j : Fin 8, 6 + (j : ℕ) ≠ (i : ℕ)) →
      W9 (selfW af ag i) = W (selfW af ag i) := by
    intro i hi
    have h6 : (i : ℕ) ≠ ((6 : Fin 16) : ℕ) := by
      have := hi 0; simp at this ⊢; omega
    have h7 : (i : ℕ) ≠ ((7 : Fin 16) : ℕ) := by
      have := hi 1; simp at this ⊢; omega
    rw [hW9, runChild_frame _ _ _ (fun j => by
        rw [pairAmb_eq]; exact pairAmb_ne_selfW j i (hi j)),
      hW8, Function.update_of_ne (selfW_ne_selfW i 7 h7),
      hW7, Function.update_of_ne (selfW_ne_selfW i 6 h6)]
  have r9_Lf : ∀ j : Fin 16, W9 (leftLoc af ag haf j) = W (leftLoc af ag haf j) := by
    intro j
    rw [hW9, runChild_frame _ _ _ (fun i => by
        rw [pairAmb_eq]; exact pairAmb_ne_leftLoc haf i j),
      hW8, Function.update_of_ne (Ne.symm (selfW_ne_leftLoc haf 7 j)),
      hW7, Function.update_of_ne (Ne.symm (selfW_ne_leftLoc haf 6 j))]
  have r9_Lg : ∀ j : Fin 16, W9 (rightLoc af ag hag j) = W (rightLoc af ag hag j) := by
    intro j
    rw [hW9, runChild_frame _ _ _ (fun i => by
        rw [pairAmb_eq]; exact pairAmb_ne_rightLoc hag haf i j),
      hW8, Function.update_of_ne (Ne.symm (selfW_ne_rightLoc hag haf 7 j)),
      hW7, Function.update_of_ne (Ne.symm (selfW_ne_rightLoc hag haf 6 j))]
  have r9_12 : W9 (selfW af ag 12)
      = Nat.pair (W (leftLoc af ag haf 3)) (W (rightLoc af ag hag 3)) := by
    rw [← pairTrans_six, hW9, writeWindow_apply]
    simp only [pairVals, Function.Embedding.trans_apply, hps0, hps1]
    simp [r8_6, r8_7]
  -- S10: the outer guard
  have h10 := ltFlagTM_hoareTime (R (selfW af ag 0)) (R (selfW af ag 1))
      (R (selfW af ag 5)) (R (selfW af ag 4))
      (Regs.ne R (selfW_ne_selfW 0 5 (by decide)))
      (Regs.ne R (selfW_ne_selfW 1 5 (by decide)))
      (Regs.ne R (selfW_ne_selfW 5 4 (by decide)))
      (W9 (selfW af ag 0)) (W9 (selfW af ag 1)) (W9 (selfW af ag 5)) (W9 (selfW af ag 4))
      inp₀ (regsWork R w₀ W9) ys hinp₀ (fun i => hpv W9 i)
      (regsWork_apply R w₀ W9 _) (regsWork_apply R w₀ W9 _)
      (regsWork_apply R w₀ W9 _) (regsWork_apply R w₀ W9 _)
  rw [regsWork_update, regsWork_update] at h10
  replace h10 := h10.mono_bound
    (ltFlagTime_le_arith _ _ _ _ B (Nat.le_of_lt (b9 _)) (Nat.le_of_lt (b9 _))
      (Nat.le_of_lt (b9 _)) (Nat.le_of_lt (b9 _)))
  set W11 := Function.update
      (Function.update W9 (selfW af ag 5) (W9 (selfW af ag 1) - W9 (selfW af ag 0)))
      (selfW af ag 4)
      (if W9 (selfW af ag 0) < W9 (selfW af ag 1) then 1 else 0) with hW11
  have b11 : ∀ k, W11 k < B := by
    intro k; rw [hW11]; simp only [Function.update_apply]
    split_ifs <;> first | omega | (have := b9 (selfW af ag 1); omega) | exact b9 _
  have r11_14 : W11 (selfW af ag 14) = W (selfW af ag 14) := by
    rw [hW11, Function.update_of_ne (selfW_ne_selfW 14 4 (by decide)),
      Function.update_of_ne (selfW_ne_selfW 14 5 (by decide))]
    exact r9 14 (by intro j; have := j.isLt; simp; omega)
  have r11_4 : W11 (selfW af ag 4)
      = (if W9 (selfW af ag 0) < W9 (selfW af ag 1) then 1 else 0) := by
    rw [hW11, Function.update_self]
  have r11_Lf2 : W11 (leftLoc af ag haf 2) = W (leftLoc af ag haf 2) := by
    rw [hW11, Function.update_of_ne (Ne.symm (selfW_ne_leftLoc haf 4 2)),
      Function.update_of_ne (Ne.symm (selfW_ne_leftLoc haf 5 2))]
    exact r9_Lf 2
  -- S11: clear the mask scratch
  have h11 := clearRegTM_hoareTime (R (selfW af ag 14)) (W11 (selfW af ag 14)) inp₀
      (regsWork R w₀ W11) ys hinp₀ (fun i _ => hpv W11 i) (regsWork_apply R w₀ W11 _)
  rw [regsWork_update] at h11
  replace h11 := h11.mono_bound (regOpTime_le_arith _ B (Nat.le_of_lt (b11 _)))
  set W12 := Function.update W11 (selfW af ag 14) 0 with hW12
  have b12 : ∀ k, W12 k < B := by
    intro k; rw [hW12]; simp only [Function.update_apply]; split_ifs
    · omega
    · exact b11 _
  -- S12: scratch := gflag * cf.tag
  have h12 := mulAddIntoTM_hoareTime (R (selfW af ag 4)) (R (leftLoc af ag haf 2))
      (R (selfW af ag 14))
      (Regs.ne R (selfW_ne_leftLoc haf 4 2))
      (Regs.ne R (selfW_ne_selfW 4 14 (by decide)))
      (Regs.ne R (Ne.symm (selfW_ne_leftLoc haf 14 2)))
      (W12 (selfW af ag 4)) (W12 (leftLoc af ag haf 2)) 0
      inp₀ (regsWork R w₀ W12) ys hinp₀ (fun i _ => hpv W12 i)
      (regsWork_apply R w₀ W12 _) (regsWork_apply R w₀ W12 _)
      (by rw [regsWork_apply, hW12, Function.update_self])
  rw [regsWork_update] at h12
  replace h12 := h12.mono_bound
    (mulAddTime_le_arith _ _ 0 B (Nat.le_of_lt (b12 _)) (Nat.le_of_lt (b12 _)) (by omega))
  set W13 := Function.update W12 (selfW af ag 14)
      (0 + W12 (selfW af ag 4) * W12 (leftLoc af ag haf 2)) with hW13
  have hflag12 : W12 (selfW af ag 4) ≤ 1 := by
    rw [hW12, Function.update_of_ne (selfW_ne_selfW 4 14 (by decide)), r11_4]
    split_ifs <;> omega
  have b13 : ∀ k, W13 k < B := by
    intro k; rw [hW13]; simp only [Function.update_apply]; split_ifs
    · have := b12 (leftLoc af ag haf 2)
      calc 0 + W12 (selfW af ag 4) * W12 (leftLoc af ag haf 2)
          ≤ 1 * W12 (leftLoc af ag haf 2) := by
            simpa using Nat.mul_le_mul hflag12 (le_refl _)
        _ < B := by omega
    · exact b12 _
  -- S13: clear the tag
  have h13 := clearRegTM_hoareTime (R (selfW af ag 2)) (W13 (selfW af ag 2)) inp₀
      (regsWork R w₀ W13) ys hinp₀ (fun i _ => hpv W13 i) (regsWork_apply R w₀ W13 _)
  rw [regsWork_update] at h13
  replace h13 := h13.mono_bound (regOpTime_le_arith _ B (Nat.le_of_lt (b13 _)))
  set W14 := Function.update W13 (selfW af ag 2) 0 with hW14
  have b14 : ∀ k, W14 k < B := by
    intro k; rw [hW14]; simp only [Function.update_apply]; split_ifs
    · omega
    · exact b13 _
  -- S14: tag := scratch * cg.tag
  have h14 := mulAddIntoTM_hoareTime (R (selfW af ag 14)) (R (rightLoc af ag hag 2))
      (R (selfW af ag 2))
      (Regs.ne R (selfW_ne_rightLoc hag haf 14 2))
      (Regs.ne R (selfW_ne_selfW 14 2 (by decide)))
      (Regs.ne R (Ne.symm (selfW_ne_rightLoc hag haf 2 2)))
      (W14 (selfW af ag 14)) (W14 (rightLoc af ag hag 2)) 0
      inp₀ (regsWork R w₀ W14) ys hinp₀ (fun i _ => hpv W14 i)
      (regsWork_apply R w₀ W14 _) (regsWork_apply R w₀ W14 _)
      (by rw [regsWork_apply, hW14, Function.update_self])
  rw [regsWork_update] at h14
  replace h14 := h14.mono_bound
    (mulAddTime_le_arith _ _ 0 B (Nat.le_of_lt (b14 _)) (Nat.le_of_lt (b14 _)) (by omega))
  set W15 := Function.update W14 (selfW af ag 2)
      (0 + W14 (selfW af ag 14) * W14 (rightLoc af ag hag 2)) with hW15
  have hflag14 : W14 (selfW af ag 14) ≤ 1 := by
    rw [hW14, Function.update_of_ne (selfW_ne_selfW 14 2 (by decide)), hW13,
      Function.update_self]
    have := b12 (leftLoc af ag haf 2)
    calc 0 + W12 (selfW af ag 4) * W12 (leftLoc af ag haf 2)
        ≤ 1 * W12 (leftLoc af ag haf 2) := by
          simpa using Nat.mul_le_mul hflag12 (le_refl _)
      _ = W12 (leftLoc af ag haf 2) := by omega
      _ ≤ 1 := by
          rw [hW12, Function.update_of_ne (Ne.symm (selfW_ne_leftLoc haf 14 2)), r11_Lf2]
          exact htagF
  have b15 : ∀ k, W15 k < B := by
    intro k; rw [hW15]; simp only [Function.update_apply]; split_ifs
    · have := b14 (rightLoc af ag hag 2)
      calc 0 + W14 (selfW af ag 14) * W14 (rightLoc af ag hag 2)
          ≤ 1 * W14 (rightLoc af ag hag 2) := by
            simpa using Nat.mul_le_mul hflag14 (le_refl _)
        _ < B := by omega
    · exact b14 _
  -- S15: clear the value
  have h15 := clearRegTM_hoareTime (R (selfW af ag 3)) (W15 (selfW af ag 3)) inp₀
      (regsWork R w₀ W15) ys hinp₀ (fun i _ => hpv W15 i) (regsWork_apply R w₀ W15 _)
  rw [regsWork_update] at h15
  replace h15 := h15.mono_bound (regOpTime_le_arith _ B (Nat.le_of_lt (b15 _)))
  set W16 := Function.update W15 (selfW af ag 3) 0 with hW16
  have b16 : ∀ k, W16 k < B := by
    intro k; rw [hW16]; simp only [Function.update_apply]; split_ifs
    · omega
    · exact b15 _
  -- S16: value := tag * pair
  have h16 := mulAddIntoTM_hoareTime (R (selfW af ag 2)) (R (selfW af ag 12))
      (R (selfW af ag 3))
      (Regs.ne R (selfW_ne_selfW 2 12 (by decide)))
      (Regs.ne R (selfW_ne_selfW 2 3 (by decide)))
      (Regs.ne R (selfW_ne_selfW 12 3 (by decide)))
      (W16 (selfW af ag 2)) (W16 (selfW af ag 12)) 0
      inp₀ (regsWork R w₀ W16) ys hinp₀ (fun i _ => hpv W16 i)
      (regsWork_apply R w₀ W16 _) (regsWork_apply R w₀ W16 _)
      (by rw [regsWork_apply, hW16, Function.update_self])
  rw [regsWork_update] at h16
  replace h16 := h16.mono_bound
    (mulAddTime_le_arith _ _ 0 B (Nat.le_of_lt (b16 _)) (Nat.le_of_lt (b16 _)) (by omega))
  exact (seqEmit hinp₀ (hpv W7) h7 <|
    seqEmit hinp₀ (hpv W8) h8 <|
    seqEmit hinp₀ (hpv W9) h9 <|
    seqEmit hinp₀ (hpv W11) h10 <|
    seqEmit hinp₀ (hpv W12) h11 <|
    seqEmit hinp₀ (hpv W13) h12 <|
    seqEmit hinp₀ (hpv W14) h13 <|
    seqEmit hinp₀ (hpv W15) h14 <|
    seqEmit hinp₀ (hpv W16) h15 h16).mono_bound (by omega)

end PhaseBMain

section PairCompose
variable {af ag : ℕ}

/-- **The `pair` machine**: feed and run both children, then pair and mask. -/
def compilePairTM (af ag : ℕ) (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (R : Regs (16 + af + ag) n) (Mf Mg : TM n) : TM n :=
  seqTM (pairPhaseA af ag haf hag R Mf Mg) (pairPhaseB af ag haf hag R)

/-- Phase A keeps every register inside the size bound. -/
lemma pairPhaseAVec_lt (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (Ff : (Fin af → ℕ) → Fin af → ℕ) (Fg : (Fin ag → ℕ) → Fin ag → ℕ)
    (V : Fin (16 + af + ag) → ℕ) (B : ℕ) (hB : ∀ k, V k < B)
    (hFfB : ∀ u : Fin af → ℕ, (∀ k, u k < B) → ∀ k, Ff u k < B)
    (hFgB : ∀ u : Fin ag → ℕ, (∀ k, u k < B) → ∀ k, Fg u k < B) :
    ∀ k, pairPhaseAVec af ag haf hag Ff Fg V k < B := by
  intro k
  simp only [pairPhaseAVec]
  set V1 := Function.update V (leftLoc af ag haf 0) (V (selfW af ag 0)) with hV1
  set V2 := Function.update V1 (leftLoc af ag haf 1) (V (selfW af ag 1)) with hV2
  set V3 := writeWindow (leftSub af ag) V2 (Ff fun j => V2 (leftSub af ag j)) with hV3
  set V4 := Function.update V3 (rightLoc af ag hag 0) (V (selfW af ag 0)) with hV4
  set V5 := Function.update V4 (rightLoc af ag hag 1) (V (selfW af ag 1)) with hV5
  have b1 : ∀ k, V1 k < B := by
    intro k; rw [hV1]; simp only [Function.update_apply]; split_ifs <;> exact hB _
  have b2 : ∀ k, V2 k < B := by
    intro k; rw [hV2]; simp only [Function.update_apply]; split_ifs
    · exact hB _
    · exact b1 _
  have b3 : ∀ k, V3 k < B := by
    intro k; rw [hV3]
    exact writeWindow_bounded _ _ _ B b2 (fun j => hFfB _ (fun i => b2 _) j) k
  have b4 : ∀ k, V4 k < B := by
    intro k; rw [hV4]; simp only [Function.update_apply]; split_ifs
    · exact hB _
    · exact b3 _
  have b5 : ∀ k, V5 k < B := by
    intro k; rw [hV5]; simp only [Function.update_apply]; split_ifs
    · exact hB _
    · exact b4 _
  exact writeWindow_bounded _ _ _ B b5 (fun j => hFgB _ (fun i => b5 _) j) k

/-- **`pair`, complete.** Both children run in their own subtrees, their values are paired,
    and the result is masked by `gflag * tagF * tagG`. -/
lemma compilePairTM_hoareTime (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (R : Regs (16 + af + ag) n) (Mf Mg : TM n)
    (Ff : (Fin af → ℕ) → Fin af → ℕ) (Fg : (Fin ag → ℕ) → Fin ag → ℕ) (tf tg : ℕ)
    (V : Fin (16 + af + ag) → ℕ) (B : ℕ)
    (inp₀ : Tape) (w₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hpark : ∀ i, Parked (w₀ i)) (hB2 : 2 ≤ B) (hB : ∀ k, V k < B)
    (hFfB : ∀ u : Fin af → ℕ, (∀ k, u k < B) → ∀ k, Ff u k < B)
    (hFgB : ∀ u : Fin ag → ℕ, (∀ k, u k < B) → ∀ k, Fg u k < B)
    (hMf : ∀ (Wb : Fin n → Tape) (u : Fin af → ℕ), (∀ i, Parked (Wb i)) → (∀ k, u k < B) →
      Mf.HoareTime (EmitPred inp₀ (regsWork ((leftSub af ag).trans R) Wb u) ys)
                   (EmitPred inp₀ (regsWork ((leftSub af ag).trans R) Wb (Ff u)) ys) tf)
    (hMg : ∀ (Wb : Fin n → Tape) (u : Fin ag → ℕ), (∀ i, Parked (Wb i)) → (∀ k, u k < B) →
      Mg.HoareTime (EmitPred inp₀ (regsWork ((rightSub af ag).trans R) Wb u) ys)
                   (EmitPred inp₀ (regsWork ((rightSub af ag).trans R) Wb (Fg u)) ys) tg)
    (hfit : Nat.pair (pairPhaseAVec af ag haf hag Ff Fg V (leftLoc af ag haf 3))
              (pairPhaseAVec af ag haf hag Ff Fg V (rightLoc af ag hag 3)) < B)
    (htagF : pairPhaseAVec af ag haf hag Ff Fg V (leftLoc af ag haf 2) ≤ 1)
    (htagG : pairPhaseAVec af ag haf hag Ff Fg V (rightLoc af ag hag 2) ≤ 1) :
    (compilePairTM af ag haf hag R Mf Mg).HoareTime
      (EmitPred inp₀ (regsWork R w₀ V) ys)
      (EmitPred inp₀ (regsWork R w₀
        (pairPhaseBVec af ag haf hag (pairPhaseAVec af ag haf hag Ff Fg V))) ys)
      (14 * evalnArithmeticCost B + tf + tg + 15) := by
  have hA := pairPhaseA_hoareTime haf hag R Mf Mg Ff Fg tf tg V B inp₀ w₀ ys hinp₀ hpark
    hB hFfB hFgB hMf hMg
  have hAlt := pairPhaseAVec_lt haf hag Ff Fg V B hB hFfB hFgB
  have hBph := pairPhaseB_hoareTime haf hag R (pairPhaseAVec af ag haf hag Ff Fg V) B
    inp₀ w₀ ys hinp₀ hpark hB2 hAlt hfit htagF htagG
  exact (seqEmit hinp₀ (parked_regsWork R hpark _) hA hBph).mono_bound (by omega)

end PairCompose

/-! ### `comp` Phase A: run `cg`, feed its value to `cf`, run `cf`

The one place where a child's *input* is another child's output. `cf` runs
unconditionally: when `cg` returned `none` its value register is the canonical `0`, and
Phase B's mask discards `cf`'s answer. -/

section CompA
variable {af ag : ℕ}

def compPhaseA (af ag : ℕ) (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (R : Regs (16 + af + ag) n) (Mf Mg : TM n) : TM n :=
  seqTM (copyIntoTM (R (selfW af ag 0)) (R (rightLoc af ag hag 0))) <|
  seqTM (copyIntoTM (R (selfW af ag 1)) (R (rightLoc af ag hag 1))) <|
  seqTM Mg <|
  seqTM (copyIntoTM (R (rightLoc af ag hag 3)) (R (leftLoc af ag haf 0))) <|
  seqTM (copyIntoTM (R (selfW af ag 1)) (R (leftLoc af ag haf 1)))
        Mf

noncomputable def compPhaseAVec (af ag : ℕ) (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (Ff : (Fin af → ℕ) → Fin af → ℕ) (Fg : (Fin ag → ℕ) → Fin ag → ℕ)
    (V : Fin (16 + af + ag) → ℕ) : Fin (16 + af + ag) → ℕ :=
  let V1 := Function.update V (rightLoc af ag hag 0) (V (selfW af ag 0))
  let V2 := Function.update V1 (rightLoc af ag hag 1) (V (selfW af ag 1))
  let V3 := writeWindow (rightSub af ag) V2 (Fg (fun j => V2 (rightSub af ag j)))
  let V4 := Function.update V3 (leftLoc af ag haf 0) (V3 (rightLoc af ag hag 3))
  let V5 := Function.update V4 (leftLoc af ag haf 1) (V (selfW af ag 1))
  writeWindow (leftSub af ag) V5 (Ff (fun j => V5 (leftSub af ag j)))

lemma compPhaseA_hoareTime (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (R : Regs (16 + af + ag) n) (Mf Mg : TM n)
    (Ff : (Fin af → ℕ) → Fin af → ℕ) (Fg : (Fin ag → ℕ) → Fin ag → ℕ) (tf tg : ℕ)
    (V : Fin (16 + af + ag) → ℕ) (B : ℕ)
    (inp₀ : Tape) (w₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hpark : ∀ i, Parked (w₀ i)) (hB : ∀ k, V k < B)
    (hFfB : ∀ u : Fin af → ℕ, (∀ k, u k < B) → ∀ k, Ff u k < B)
    (hFgB : ∀ u : Fin ag → ℕ, (∀ k, u k < B) → ∀ k, Fg u k < B)
    (hMf : ∀ (Wb : Fin n → Tape) (u : Fin af → ℕ), (∀ i, Parked (Wb i)) → (∀ k, u k < B) →
      Mf.HoareTime (EmitPred inp₀ (regsWork ((leftSub af ag).trans R) Wb u) ys)
                   (EmitPred inp₀ (regsWork ((leftSub af ag).trans R) Wb (Ff u)) ys) tf)
    (hMg : ∀ (Wb : Fin n → Tape) (u : Fin ag → ℕ), (∀ i, Parked (Wb i)) → (∀ k, u k < B) →
      Mg.HoareTime (EmitPred inp₀ (regsWork ((rightSub af ag).trans R) Wb u) ys)
                   (EmitPred inp₀ (regsWork ((rightSub af ag).trans R) Wb (Fg u)) ys) tg) :
    (compPhaseA af ag haf hag R Mf Mg).HoareTime
      (EmitPred inp₀ (regsWork R w₀ V) ys)
      (EmitPred inp₀ (regsWork R w₀ (compPhaseAVec af ag haf hag Ff Fg V)) ys)
      (4 * evalnArithmeticCost B + tf + tg + 5) := by
  have hpv := parked_regsWork R hpark
  have hle : ∀ k, V k ≤ B := fun k => Nat.le_of_lt (hB k)
  -- S1: cg.input := parent input
  have h1 := copyIntoTM_hoareTime (R (selfW af ag 0)) (R (rightLoc af ag hag 0))
      (Regs.ne R (selfW_ne_rightLoc hag haf 0 0)) (V (selfW af ag 0))
      (V (rightLoc af ag hag 0))
      inp₀ (regsWork R w₀ V) ys hinp₀ (fun i _ => hpv V i)
      (regsWork_apply R w₀ V _) (regsWork_apply R w₀ V _)
  rw [regsWork_update] at h1
  replace h1 := h1.mono_bound (copyIntoTime_le_arith _ _ B (hle _) (hle _))
  set V1 := Function.update V (rightLoc af ag hag 0) (V (selfW af ag 0)) with hV1
  have b1 : ∀ k, V1 k < B := by
    intro k; rw [hV1]; simp only [Function.update_apply]; split_ifs <;> exact hB _
  -- S2: cg.fuel := parent fuel
  have h2 := copyIntoTM_hoareTime (R (selfW af ag 1)) (R (rightLoc af ag hag 1))
      (Regs.ne R (selfW_ne_rightLoc hag haf 1 1)) (V (selfW af ag 1))
      (V1 (rightLoc af ag hag 1))
      inp₀ (regsWork R w₀ V1) ys hinp₀ (fun i _ => hpv V1 i)
      (by rw [regsWork_apply, hV1,
        Function.update_of_ne (selfW_ne_rightLoc hag haf 1 0)])
      (regsWork_apply R w₀ V1 _)
  rw [regsWork_update] at h2
  replace h2 := h2.mono_bound
    (copyIntoTime_le_arith _ _ B (hle _) (Nat.le_of_lt (b1 _)))
  set V2 := Function.update V1 (rightLoc af ag hag 1) (V (selfW af ag 1)) with hV2
  have b2 : ∀ k, V2 k < B := by
    intro k; rw [hV2]; simp only [Function.update_apply]; split_ifs
    · exact hB _
    · exact b1 _
  have out2 : ∀ k, (∀ j, rightSub af ag j ≠ k) → V2 k = V k := by
    intro k hk
    have e0 : rightLoc af ag hag 0 ≠ k := by rw [rightLoc_eq]; exact hk _
    have e1 : rightLoc af ag hag 1 ≠ k := by rw [rightLoc_eq]; exact hk _
    rw [hV2, Function.update_of_ne (Ne.symm e1), hV1, Function.update_of_ne (Ne.symm e0)]
  -- S3: run cg
  have h3 := runChild (rightSub af ag) R Mg Fg tg B w₀ hpark V2 b2 hMg
  set V3 := writeWindow (rightSub af ag) V2 (Fg (fun j => V2 (rightSub af ag j))) with hV3
  have b3 : ∀ k, V3 k < B := by
    intro k; rw [hV3]
    exact writeWindow_bounded _ _ _ B b2 (fun j => hFgB _ (fun i => b2 _) j) k
  have out3 : ∀ k, (∀ j, rightSub af ag j ≠ k) → V3 k = V k := by
    intro k hk
    rw [hV3, runChild_frame _ _ _ hk]; exact out2 k hk
  -- S4: cf.input := cg's value
  have h4 := copyIntoTM_hoareTime (R (rightLoc af ag hag 3)) (R (leftLoc af ag haf 0))
      (Regs.ne R (Ne.symm (leftLoc_ne_rightLoc haf hag 0 3)))
      (V3 (rightLoc af ag hag 3)) (V3 (leftLoc af ag haf 0))
      inp₀ (regsWork R w₀ V3) ys hinp₀ (fun i _ => hpv V3 i)
      (regsWork_apply R w₀ V3 _) (regsWork_apply R w₀ V3 _)
  rw [regsWork_update] at h4
  replace h4 := h4.mono_bound
    (copyIntoTime_le_arith _ _ B (Nat.le_of_lt (b3 _)) (Nat.le_of_lt (b3 _)))
  set V4 := Function.update V3 (leftLoc af ag haf 0) (V3 (rightLoc af ag hag 3)) with hV4
  have b4 : ∀ k, V4 k < B := by
    intro k; rw [hV4]; simp only [Function.update_apply]; split_ifs
    · exact b3 _
    · exact b3 _
  -- S5: cf.fuel := parent fuel
  have h5 := copyIntoTM_hoareTime (R (selfW af ag 1)) (R (leftLoc af ag haf 1))
      (Regs.ne R (selfW_ne_leftLoc haf 1 1)) (V (selfW af ag 1))
      (V4 (leftLoc af ag haf 1))
      inp₀ (regsWork R w₀ V4) ys hinp₀ (fun i _ => hpv V4 i)
      (by rw [regsWork_apply, hV4,
        Function.update_of_ne (selfW_ne_leftLoc haf 1 0),
        out3 _ (fun j => rightSub_ne_selfW haf j 1)])
      (regsWork_apply R w₀ V4 _)
  rw [regsWork_update] at h5
  replace h5 := h5.mono_bound
    (copyIntoTime_le_arith _ _ B (hle _) (Nat.le_of_lt (b4 _)))
  set V5 := Function.update V4 (leftLoc af ag haf 1) (V (selfW af ag 1)) with hV5
  have b5 : ∀ k, V5 k < B := by
    intro k; rw [hV5]; simp only [Function.update_apply]; split_ifs
    · exact hB _
    · exact b4 _
  -- S6: run cf
  have h6 := runChild (leftSub af ag) R Mf Ff tf B w₀ hpark V5 b5 hMf
  exact (seqEmit hinp₀ (hpv V1) h1 <|
    seqEmit hinp₀ (hpv V2) h2 <|
    seqEmit hinp₀ (hpv V3) h3 <|
    seqEmit hinp₀ (hpv V4) h4 <|
    seqEmit hinp₀ (hpv V5) h5 h6).mono_bound (by omega)

end CompA

/-! ### `comp` Phase B: mask

Seven single-register stages. Simpler than `pair`'s Phase B — there is no `pairTM`, so no
value can leave the size bound. -/

section CompB
variable {af ag : ℕ}

def compPhaseB (af ag : ℕ) (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (R : Regs (16 + af + ag) n) : TM n :=
  seqTM (ltFlagTM (R (selfW af ag 0)) (R (selfW af ag 1))
          (R (selfW af ag 5)) (R (selfW af ag 4))) <|
  seqTM (clearRegTM (R (selfW af ag 14))) <|
  seqTM (mulAddIntoTM (R (selfW af ag 4)) (R (rightLoc af ag hag 2))
          (R (selfW af ag 14))) <|
  seqTM (clearRegTM (R (selfW af ag 2))) <|
  seqTM (mulAddIntoTM (R (selfW af ag 14)) (R (leftLoc af ag haf 2))
          (R (selfW af ag 2))) <|
  seqTM (clearRegTM (R (selfW af ag 3)))
        (mulAddIntoTM (R (selfW af ag 2)) (R (leftLoc af ag haf 3)) (R (selfW af ag 3)))

noncomputable def compPhaseBVec (af ag : ℕ) (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (W : Fin (16 + af + ag) → ℕ) : Fin (16 + af + ag) → ℕ :=
  let W1 := Function.update W (selfW af ag 5) (W (selfW af ag 1) - W (selfW af ag 0))
  let W2 := Function.update W1 (selfW af ag 4)
              (if W (selfW af ag 0) < W (selfW af ag 1) then 1 else 0)
  let W3 := Function.update W2 (selfW af ag 14) 0
  let W4 := Function.update W3 (selfW af ag 14)
              (0 + W3 (selfW af ag 4) * W3 (rightLoc af ag hag 2))
  let W5 := Function.update W4 (selfW af ag 2) 0
  let W6 := Function.update W5 (selfW af ag 2)
              (0 + W5 (selfW af ag 14) * W5 (leftLoc af ag haf 2))
  let W7 := Function.update W6 (selfW af ag 3) 0
  Function.update W7 (selfW af ag 3)
    (0 + W7 (selfW af ag 2) * W7 (leftLoc af ag haf 3))

lemma compPhaseB_hoareTime (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (R : Regs (16 + af + ag) n) (W : Fin (16 + af + ag) → ℕ) (B : ℕ)
    (inp₀ : Tape) (w₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hpark : ∀ i, Parked (w₀ i)) (hW : ∀ k, W k < B)
    (htagG : W (rightLoc af ag hag 2) ≤ 1) (htagF : W (leftLoc af ag haf 2) ≤ 1) :
    (compPhaseB af ag haf hag R).HoareTime
      (EmitPred inp₀ (regsWork R w₀ W) ys)
      (EmitPred inp₀ (regsWork R w₀ (compPhaseBVec af ag haf hag W)) ys)
      (7 * evalnArithmeticCost B + 6) := by
  have hpv := parked_regsWork R hpark
  have hle : ∀ k, W k ≤ B := fun k => Nat.le_of_lt (hW k)
  have hBpos : 0 < B := Nat.lt_of_le_of_lt (Nat.zero_le _) (hW (selfW af ag 0))
  -- S1: the outer guard
  have h1 := ltFlagTM_hoareTime (R (selfW af ag 0)) (R (selfW af ag 1))
      (R (selfW af ag 5)) (R (selfW af ag 4))
      (Regs.ne R (selfW_ne_selfW 0 5 (by decide)))
      (Regs.ne R (selfW_ne_selfW 1 5 (by decide)))
      (Regs.ne R (selfW_ne_selfW 5 4 (by decide)))
      (W (selfW af ag 0)) (W (selfW af ag 1)) (W (selfW af ag 5)) (W (selfW af ag 4))
      inp₀ (regsWork R w₀ W) ys hinp₀ (fun i => hpv W i)
      (regsWork_apply R w₀ W _) (regsWork_apply R w₀ W _)
      (regsWork_apply R w₀ W _) (regsWork_apply R w₀ W _)
  rw [regsWork_update, regsWork_update] at h1
  replace h1 := h1.mono_bound
    (ltFlagTime_le_arith _ _ _ _ B (hle _) (hle _) (hle _) (hle _))
  set W2 := Function.update
      (Function.update W (selfW af ag 5) (W (selfW af ag 1) - W (selfW af ag 0)))
      (selfW af ag 4) (if W (selfW af ag 0) < W (selfW af ag 1) then 1 else 0) with hW2
  have b2 : ∀ k, W2 k < B := by
    intro k; rw [hW2]; simp only [Function.update_apply]
    split_ifs <;> first | omega | (have := hW (selfW af ag 1); omega) | exact hW _
  have r2_4 : W2 (selfW af ag 4)
      = (if W (selfW af ag 0) < W (selfW af ag 1) then 1 else 0) := by
    rw [hW2, Function.update_self]
  have r2_14 : W2 (selfW af ag 14) = W (selfW af ag 14) := by
    rw [hW2, Function.update_of_ne (selfW_ne_selfW 14 4 (by decide)),
      Function.update_of_ne (selfW_ne_selfW 14 5 (by decide))]
  have r2_Lg2 : W2 (rightLoc af ag hag 2) = W (rightLoc af ag hag 2) := by
    rw [hW2, Function.update_of_ne (Ne.symm (selfW_ne_rightLoc hag haf 4 2)),
      Function.update_of_ne (Ne.symm (selfW_ne_rightLoc hag haf 5 2))]
  -- S2: clear the mask scratch
  have h2 := clearRegTM_hoareTime (R (selfW af ag 14)) (W2 (selfW af ag 14)) inp₀
      (regsWork R w₀ W2) ys hinp₀ (fun i _ => hpv W2 i) (regsWork_apply R w₀ W2 _)
  rw [regsWork_update] at h2
  replace h2 := h2.mono_bound (regOpTime_le_arith _ B (Nat.le_of_lt (b2 _)))
  set W3 := Function.update W2 (selfW af ag 14) 0 with hW3
  have b3 : ∀ k, W3 k < B := by
    intro k; rw [hW3]; simp only [Function.update_apply]; split_ifs
    · omega
    · exact b2 _
  have hflag3 : W3 (selfW af ag 4) ≤ 1 := by
    rw [hW3, Function.update_of_ne (selfW_ne_selfW 4 14 (by decide)), r2_4]
    split_ifs <;> omega
  have r3_Lg2 : W3 (rightLoc af ag hag 2) = W (rightLoc af ag hag 2) := by
    rw [hW3, Function.update_of_ne (Ne.symm (selfW_ne_rightLoc hag haf 14 2)), r2_Lg2]
  -- S3: scratch := gflag * cg.tag
  have h3 := mulAddIntoTM_hoareTime (R (selfW af ag 4)) (R (rightLoc af ag hag 2))
      (R (selfW af ag 14))
      (Regs.ne R (selfW_ne_rightLoc hag haf 4 2))
      (Regs.ne R (selfW_ne_selfW 4 14 (by decide)))
      (Regs.ne R (Ne.symm (selfW_ne_rightLoc hag haf 14 2)))
      (W3 (selfW af ag 4)) (W3 (rightLoc af ag hag 2)) 0
      inp₀ (regsWork R w₀ W3) ys hinp₀ (fun i _ => hpv W3 i)
      (regsWork_apply R w₀ W3 _) (regsWork_apply R w₀ W3 _)
      (by rw [regsWork_apply, hW3, Function.update_self])
  rw [regsWork_update] at h3
  replace h3 := h3.mono_bound
    (mulAddTime_le_arith _ _ 0 B (Nat.le_of_lt (b3 _)) (Nat.le_of_lt (b3 _)) (by omega))
  set W4 := Function.update W3 (selfW af ag 14)
      (0 + W3 (selfW af ag 4) * W3 (rightLoc af ag hag 2)) with hW4
  have hmask4 : W4 (selfW af ag 14) ≤ 1 := by
    rw [hW4, Function.update_self, r3_Lg2]
    calc 0 + W3 (selfW af ag 4) * W (rightLoc af ag hag 2)
        ≤ 1 * 1 := by simpa using Nat.mul_le_mul hflag3 htagG
      _ = 1 := by norm_num
  have b4 : ∀ k, W4 k < B := by
    intro k; rw [hW4]; simp only [Function.update_apply]; split_ifs
    · have hb := b3 (rightLoc af ag hag 2)
      calc 0 + W3 (selfW af ag 4) * W3 (rightLoc af ag hag 2)
          ≤ 1 * W3 (rightLoc af ag hag 2) := by
            simpa using Nat.mul_le_mul hflag3 (le_refl (W3 (rightLoc af ag hag 2)))
        _ < B := by omega
    · exact b3 _
  have r4_Lf2 : W4 (leftLoc af ag haf 2) = W (leftLoc af ag haf 2) := by
    rw [hW4, Function.update_of_ne (Ne.symm (selfW_ne_leftLoc haf 14 2)), hW3,
      Function.update_of_ne (Ne.symm (selfW_ne_leftLoc haf 14 2)), hW2,
      Function.update_of_ne (Ne.symm (selfW_ne_leftLoc haf 4 2)),
      Function.update_of_ne (Ne.symm (selfW_ne_leftLoc haf 5 2))]
  -- S4: clear the tag
  have h4 := clearRegTM_hoareTime (R (selfW af ag 2)) (W4 (selfW af ag 2)) inp₀
      (regsWork R w₀ W4) ys hinp₀ (fun i _ => hpv W4 i) (regsWork_apply R w₀ W4 _)
  rw [regsWork_update] at h4
  replace h4 := h4.mono_bound (regOpTime_le_arith _ B (Nat.le_of_lt (b4 _)))
  set W5 := Function.update W4 (selfW af ag 2) 0 with hW5
  have b5 : ∀ k, W5 k < B := by
    intro k; rw [hW5]; simp only [Function.update_apply]; split_ifs
    · omega
    · exact b4 _
  have hmask5 : W5 (selfW af ag 14) ≤ 1 := by
    rw [hW5, Function.update_of_ne (selfW_ne_selfW 14 2 (by decide))]; exact hmask4
  have r5_Lf2 : W5 (leftLoc af ag haf 2) = W (leftLoc af ag haf 2) := by
    rw [hW5, Function.update_of_ne (Ne.symm (selfW_ne_leftLoc haf 2 2)), r4_Lf2]
  -- S5: tag := scratch * cf.tag
  have h5 := mulAddIntoTM_hoareTime (R (selfW af ag 14)) (R (leftLoc af ag haf 2))
      (R (selfW af ag 2))
      (Regs.ne R (selfW_ne_leftLoc haf 14 2))
      (Regs.ne R (selfW_ne_selfW 14 2 (by decide)))
      (Regs.ne R (Ne.symm (selfW_ne_leftLoc haf 2 2)))
      (W5 (selfW af ag 14)) (W5 (leftLoc af ag haf 2)) 0
      inp₀ (regsWork R w₀ W5) ys hinp₀ (fun i _ => hpv W5 i)
      (regsWork_apply R w₀ W5 _) (regsWork_apply R w₀ W5 _)
      (by rw [regsWork_apply, hW5, Function.update_self])
  rw [regsWork_update] at h5
  replace h5 := h5.mono_bound
    (mulAddTime_le_arith _ _ 0 B (Nat.le_of_lt (b5 _)) (Nat.le_of_lt (b5 _)) (by omega))
  set W6 := Function.update W5 (selfW af ag 2)
      (0 + W5 (selfW af ag 14) * W5 (leftLoc af ag haf 2)) with hW6
  have hmask6 : W6 (selfW af ag 2) ≤ 1 := by
    rw [hW6, Function.update_self, r5_Lf2]
    calc 0 + W5 (selfW af ag 14) * W (leftLoc af ag haf 2)
        ≤ 1 * 1 := by simpa using Nat.mul_le_mul hmask5 htagF
      _ = 1 := by norm_num
  have b6 : ∀ k, W6 k < B := by
    intro k; rw [hW6]; simp only [Function.update_apply]; split_ifs
    · have hb := b5 (leftLoc af ag haf 2)
      calc 0 + W5 (selfW af ag 14) * W5 (leftLoc af ag haf 2)
          ≤ 1 * W5 (leftLoc af ag haf 2) := by
            simpa using Nat.mul_le_mul hmask5 (le_refl (W5 (leftLoc af ag haf 2)))
        _ < B := by omega
    · exact b5 _
  have r6_Lf3 : W6 (leftLoc af ag haf 3) = W (leftLoc af ag haf 3) := by
    rw [hW6, Function.update_of_ne (Ne.symm (selfW_ne_leftLoc haf 2 3)), hW5,
      Function.update_of_ne (Ne.symm (selfW_ne_leftLoc haf 2 3)), hW4,
      Function.update_of_ne (Ne.symm (selfW_ne_leftLoc haf 14 3)), hW3,
      Function.update_of_ne (Ne.symm (selfW_ne_leftLoc haf 14 3)), hW2,
      Function.update_of_ne (Ne.symm (selfW_ne_leftLoc haf 4 3)),
      Function.update_of_ne (Ne.symm (selfW_ne_leftLoc haf 5 3))]
  -- S6: clear the value
  have h6 := clearRegTM_hoareTime (R (selfW af ag 3)) (W6 (selfW af ag 3)) inp₀
      (regsWork R w₀ W6) ys hinp₀ (fun i _ => hpv W6 i) (regsWork_apply R w₀ W6 _)
  rw [regsWork_update] at h6
  replace h6 := h6.mono_bound (regOpTime_le_arith _ B (Nat.le_of_lt (b6 _)))
  set W7 := Function.update W6 (selfW af ag 3) 0 with hW7
  have b7 : ∀ k, W7 k < B := by
    intro k; rw [hW7]; simp only [Function.update_apply]; split_ifs
    · omega
    · exact b6 _
  -- S7: value := tag * cf.value
  have h7 := mulAddIntoTM_hoareTime (R (selfW af ag 2)) (R (leftLoc af ag haf 3))
      (R (selfW af ag 3))
      (Regs.ne R (selfW_ne_leftLoc haf 2 3))
      (Regs.ne R (selfW_ne_selfW 2 3 (by decide)))
      (Regs.ne R (Ne.symm (selfW_ne_leftLoc haf 3 3)))
      (W7 (selfW af ag 2)) (W7 (leftLoc af ag haf 3)) 0
      inp₀ (regsWork R w₀ W7) ys hinp₀ (fun i _ => hpv W7 i)
      (regsWork_apply R w₀ W7 _) (regsWork_apply R w₀ W7 _)
      (by rw [regsWork_apply, hW7, Function.update_self])
  rw [regsWork_update] at h7
  replace h7 := h7.mono_bound
    (mulAddTime_le_arith _ _ 0 B (Nat.le_of_lt (b7 _)) (Nat.le_of_lt (b7 _)) (by omega))
  exact (seqEmit hinp₀ (hpv W2) h1 <|
    seqEmit hinp₀ (hpv W3) h2 <|
    seqEmit hinp₀ (hpv W4) h3 <|
    seqEmit hinp₀ (hpv W5) h4 <|
    seqEmit hinp₀ (hpv W6) h5 <|
    seqEmit hinp₀ (hpv W7) h6 h7).mono_bound (by omega)

end CompB

section CompCompose
variable {af ag : ℕ}

/-- **The `comp` machine**: run `cg`, feed its value to `cf`, run `cf`, then mask. -/
def compileCompTM (af ag : ℕ) (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (R : Regs (16 + af + ag) n) (Mf Mg : TM n) : TM n :=
  seqTM (compPhaseA af ag haf hag R Mf Mg) (compPhaseB af ag haf hag R)

/-- Phase A keeps every register inside the size bound. -/
lemma compPhaseAVec_lt (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (Ff : (Fin af → ℕ) → Fin af → ℕ) (Fg : (Fin ag → ℕ) → Fin ag → ℕ)
    (V : Fin (16 + af + ag) → ℕ) (B : ℕ) (hB : ∀ k, V k < B)
    (hFfB : ∀ u : Fin af → ℕ, (∀ k, u k < B) → ∀ k, Ff u k < B)
    (hFgB : ∀ u : Fin ag → ℕ, (∀ k, u k < B) → ∀ k, Fg u k < B) :
    ∀ k, compPhaseAVec af ag haf hag Ff Fg V k < B := by
  intro k
  simp only [compPhaseAVec]
  set V1 := Function.update V (rightLoc af ag hag 0) (V (selfW af ag 0)) with hV1
  set V2 := Function.update V1 (rightLoc af ag hag 1) (V (selfW af ag 1)) with hV2
  set V3 := writeWindow (rightSub af ag) V2 (Fg fun j => V2 (rightSub af ag j)) with hV3
  set V4 := Function.update V3 (leftLoc af ag haf 0) (V3 (rightLoc af ag hag 3)) with hV4
  set V5 := Function.update V4 (leftLoc af ag haf 1) (V (selfW af ag 1)) with hV5
  have b1 : ∀ k, V1 k < B := by
    intro k; rw [hV1]; simp only [Function.update_apply]; split_ifs <;> exact hB _
  have b2 : ∀ k, V2 k < B := by
    intro k; rw [hV2]; simp only [Function.update_apply]; split_ifs
    · exact hB _
    · exact b1 _
  have b3 : ∀ k, V3 k < B := by
    intro k; rw [hV3]
    exact writeWindow_bounded _ _ _ B b2 (fun j => hFgB _ (fun i => b2 _) j) k
  have b4 : ∀ k, V4 k < B := by
    intro k; rw [hV4]; simp only [Function.update_apply]; split_ifs
    · exact b3 _
    · exact b3 _
  have b5 : ∀ k, V5 k < B := by
    intro k; rw [hV5]; simp only [Function.update_apply]; split_ifs
    · exact hB _
    · exact b4 _
  exact writeWindow_bounded _ _ _ B b5 (fun j => hFfB _ (fun i => b5 _) j) k

/-- **`comp`, complete.** -/
lemma compileCompTM_hoareTime (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (R : Regs (16 + af + ag) n) (Mf Mg : TM n)
    (Ff : (Fin af → ℕ) → Fin af → ℕ) (Fg : (Fin ag → ℕ) → Fin ag → ℕ) (tf tg : ℕ)
    (V : Fin (16 + af + ag) → ℕ) (B : ℕ)
    (inp₀ : Tape) (w₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hpark : ∀ i, Parked (w₀ i)) (hB : ∀ k, V k < B)
    (hFfB : ∀ u : Fin af → ℕ, (∀ k, u k < B) → ∀ k, Ff u k < B)
    (hFgB : ∀ u : Fin ag → ℕ, (∀ k, u k < B) → ∀ k, Fg u k < B)
    (hMf : ∀ (Wb : Fin n → Tape) (u : Fin af → ℕ), (∀ i, Parked (Wb i)) → (∀ k, u k < B) →
      Mf.HoareTime (EmitPred inp₀ (regsWork ((leftSub af ag).trans R) Wb u) ys)
                   (EmitPred inp₀ (regsWork ((leftSub af ag).trans R) Wb (Ff u)) ys) tf)
    (hMg : ∀ (Wb : Fin n → Tape) (u : Fin ag → ℕ), (∀ i, Parked (Wb i)) → (∀ k, u k < B) →
      Mg.HoareTime (EmitPred inp₀ (regsWork ((rightSub af ag).trans R) Wb u) ys)
                   (EmitPred inp₀ (regsWork ((rightSub af ag).trans R) Wb (Fg u)) ys) tg)
    (htagG : compPhaseAVec af ag haf hag Ff Fg V (rightLoc af ag hag 2) ≤ 1)
    (htagF : compPhaseAVec af ag haf hag Ff Fg V (leftLoc af ag haf 2) ≤ 1) :
    (compileCompTM af ag haf hag R Mf Mg).HoareTime
      (EmitPred inp₀ (regsWork R w₀ V) ys)
      (EmitPred inp₀ (regsWork R w₀
        (compPhaseBVec af ag haf hag (compPhaseAVec af ag haf hag Ff Fg V))) ys)
      (11 * evalnArithmeticCost B + tf + tg + 12) := by
  have hA := compPhaseA_hoareTime haf hag R Mf Mg Ff Fg tf tg V B inp₀ w₀ ys hinp₀ hpark
    hB hFfB hFgB hMf hMg
  have hAlt := compPhaseAVec_lt haf hag Ff Fg V B hB hFfB hFgB
  have hBph := compPhaseB_hoareTime haf hag R (compPhaseAVec af ag haf hag Ff Fg V) B
    inp₀ w₀ ys hinp₀ hpark hAlt htagG htagF
  exact (seqEmit hinp₀ (parked_regsWork R hpark _) hA hBph).mono_bound (by omega)

end CompCompose
/-! ## The compiler API

`compileCodeAt c R` compiles `c` into the ambient register file named by `R`, whose arity
`codeRegs c` is the node's own sixteen plus each child's whole subtree. Parent and every
descendant inhabit the same `TM n`, differing only in which registers they name, so
ordinary `seqTM` composes them with no lifting between arities.

The result is an `Option`: `none` marks the two fuel-recursive constructors, which are not
implemented yet. That is deliberate — a placeholder machine returning canonical `none`
would typecheck and be silently *wrong* for those codes, which is exactly the kind of stub
this repository's standards exist to catch. `none` here says "not compiled", never
"compiles to failure". -/

/-- **The compiler.** Structural recursion on `Code`; parent and every descendant inhabit
    the same ambient `TM n`, differing only in which registers they name. -/
def compileCodeAt : (c : Nat.Partrec.Code) → Regs (codeRegs c) n → Option (TM n)
  | .zero, R => some (compileZero R)
  | .succ, R => some (compileSucc R)
  | .left, R => some (compileProj R 0)
  | .right, R => some (compileProj R 1)
  | .pair cf cg, R => do
      let Mf ← compileCodeAt cf ((leftSub (codeRegs cf) (codeRegs cg)).trans R)
      let Mg ← compileCodeAt cg ((rightSub (codeRegs cf) (codeRegs cg)).trans R)
      some (compilePairTM (codeRegs cf) (codeRegs cg)
        (codeRegs_ge cf) (codeRegs_ge cg) R Mf Mg)
  | .comp cf cg, R => do
      let Mf ← compileCodeAt cf ((leftSub (codeRegs cf) (codeRegs cg)).trans R)
      let Mg ← compileCodeAt cg ((rightSub (codeRegs cf) (codeRegs cg)).trans R)
      some (compileCompTM (codeRegs cf) (codeRegs cg)
        (codeRegs_ge cf) (codeRegs_ge cg) R Mf Mg)
  | .prec _ _, _ => none
  | .rfind' _, _ => none

/-- The compiler succeeds exactly on the fuel-recursion-free fragment. -/
lemma compileCodeAt_isSome_zero (R : Regs (codeRegs .zero) n) :
    (compileCodeAt .zero R).isSome := rfl

lemma compileCodeAt_isSome_pair (cf cg : Nat.Partrec.Code)
    (R : Regs (codeRegs (cf.pair cg)) n)
    (hf : (compileCodeAt cf ((leftSub (codeRegs cf) (codeRegs cg)).trans R)).isSome)
    (hg : (compileCodeAt cg ((rightSub (codeRegs cf) (codeRegs cg)).trans R)).isSome) :
    (compileCodeAt (cf.pair cg) R).isSome := by
  rw [compileCodeAt]
  cases hF : compileCodeAt cf ((leftSub (codeRegs cf) (codeRegs cg)).trans R) with
  | none => rw [hF] at hf; exact absurd hf (by simp)
  | some Mf =>
    cases hG : compileCodeAt cg ((rightSub (codeRegs cf) (codeRegs cg)).trans R) with
    | none => rw [hG] at hg; exact absurd hg (by simp)
    | some Mg => simp

/-! ## `prec`: the exact equation, and the recurrence the machine loop implements

At fuel `k+1` the equation is

```
guard (n ≤ k)
n.unpaired fun a n' => n'.casesOn (evaln (k+1) cf a) fun y => do
  let i ← evaln k (prec cf cg) (Nat.pair a y)
  evaln (k+1) cg (Nat.pair a (Nat.pair y i))
```

so **both children run at the parent's own fuel**, and fuel decreases *only* in the
self-call. Unrolling the self-call therefore walks `(a, m) → (a, m-1) → … → (a, 0)` while
the fuel walks `k+1 → k → … → k+1-m`: the base case runs at fuel `fuel - m`, and level `j`
counting up from it runs at fuel `fuel - m + j`.

That is the whole content of the loop the machine runs, and it is why the machine iterates
*upward* from the base rather than downward from the input. -/

lemma evaln_prec_zero (k : ℕ) (cf cg : Nat.Partrec.Code) (a : ℕ) :
    Nat.Partrec.Code.evaln k (cf.prec cg) (Nat.pair a 0)
      = if Nat.pair a 0 < k then Nat.Partrec.Code.evaln k cf a else none := by
  cases k with
  | zero => simp [Nat.Partrec.Code.evaln]
  | succ k =>
    simp only [Nat.Partrec.Code.evaln, Nat.lt_succ_iff, Nat.unpaired, Nat.unpair_pair]
    split_ifs with h <;> simp [h]

lemma evaln_prec_succ (k : ℕ) (cf cg : Nat.Partrec.Code) (a j : ℕ) :
    Nat.Partrec.Code.evaln k (cf.prec cg) (Nat.pair a (j + 1))
      = if Nat.pair a (j + 1) < k then
          (Nat.Partrec.Code.evaln (k - 1) (cf.prec cg) (Nat.pair a j) >>= fun i =>
            Nat.Partrec.Code.evaln k cg (Nat.pair a (Nat.pair j i)))
        else none := by
  cases k with
  | zero => simp [Nat.Partrec.Code.evaln]
  | succ k =>
    simp only [Nat.Partrec.Code.evaln, Nat.lt_succ_iff, Nat.unpaired, Nat.unpair_pair]
    split_ifs with h <;> simp [h]

/-! ### The pure iterator

`precRun cf cg a f j` is the value the machine's loop register holds after `j` iterations,
when the base case was run at fuel `f`. It is a plain structural recursion on `j` — no
`Code` recursion — which is exactly what the machine implements. -/

def precRun (cf cg : Nat.Partrec.Code) (a : ℕ) (f : ℕ) : ℕ → Option ℕ
  | 0 => if Nat.pair a 0 < f then Nat.Partrec.Code.evaln f cf a else none
  | j + 1 =>
      if Nat.pair a (j + 1) < f + (j + 1) then
        (precRun cf cg a f j >>= fun i =>
          Nat.Partrec.Code.evaln (f + (j + 1)) cg (Nat.pair a (Nat.pair j i)))
      else none

/-- **The iterator is the semantics.** Running the loop `j` times from base fuel `f`
    computes `evaln` of `prec` at index `j` and fuel `f + j`. -/
lemma precRun_eq (cf cg : Nat.Partrec.Code) (a f : ℕ) : ∀ j,
    precRun cf cg a f j = Nat.Partrec.Code.evaln (f + j) (cf.prec cg) (Nat.pair a j)
  | 0 => by
      rw [precRun, evaln_prec_zero, Nat.add_zero]
  | j + 1 => by
      rw [precRun, evaln_prec_succ, precRun_eq cf cg a f j,
        show f + (j + 1) - 1 = f + j from by omega]

/-- Specialised to the machine's actual loop: `m` iterations from base fuel `fuel - m`
    compute the answer at fuel `fuel`, provided the outer guard holds. -/
lemma precRun_eq_evaln (cf cg : Nat.Partrec.Code) (a m fuel : ℕ)
    (hm : m ≤ fuel) :
    precRun cf cg a (fuel - m) m
      = Nat.Partrec.Code.evaln fuel (cf.prec cg) (Nat.pair a m) := by
  rw [precRun_eq]
  congr 1
  omega

/-! ## `rfind'`: the exact equation and its pure iterator

At fuel `k+1`:

```
guard (n ≤ k)
n.unpaired fun a m => do
  let x ← evaln (k+1) cf (Nat.pair a m)
  if x = 0 then pure m else evaln k (rfind' cf) (Nat.pair a (m+1))
```

so the test child runs at the parent's own fuel, and the self-call *decreases* fuel while
*increasing* the search index. Unrolling walks `(f, m) → (f-1, m+1) → …`, so a machine loop
runs at most `f` iterations — the loop bound is the **fuel**, not the input.

Contrast `prec`, whose loop bound is the unpaired index and which walks *upward* in fuel.
The two loop constructors iterate in opposite directions; that is the main thing to keep
straight when implementing them. -/

lemma evaln_rfind_eq (k : ℕ) (cf : Nat.Partrec.Code) (a m : ℕ) :
    Nat.Partrec.Code.evaln k cf.rfind' (Nat.pair a m)
      = if Nat.pair a m < k then
          (Nat.Partrec.Code.evaln k cf (Nat.pair a m) >>= fun x =>
            if x = 0 then some m
            else Nat.Partrec.Code.evaln (k - 1) cf.rfind' (Nat.pair a (m + 1)))
        else none := by
  cases k with
  | zero => simp [Nat.Partrec.Code.evaln]
  | succ k =>
    simp only [Nat.Partrec.Code.evaln, Nat.lt_succ_iff, Nat.unpaired, Nat.unpair_pair]
    split_ifs with h <;> simp [h]

/-- The search, as a plain structural recursion on fuel — no `Code` recursion. This is what
    the machine's bounded loop implements. -/
def rfindRun (cf : Nat.Partrec.Code) (a : ℕ) : ℕ → ℕ → Option ℕ
  | 0, _ => none
  | f + 1, m =>
      if Nat.pair a m < f + 1 then
        (Nat.Partrec.Code.evaln (f + 1) cf (Nat.pair a m) >>= fun x =>
          if x = 0 then some m else rfindRun cf a f (m + 1))
      else none

/-- **The iterator is the semantics.** -/
lemma rfindRun_eq (cf : Nat.Partrec.Code) (a : ℕ) : ∀ f m,
    rfindRun cf a f m = Nat.Partrec.Code.evaln f cf.rfind' (Nat.pair a m)
  | 0, m => by rw [rfindRun, evaln_rfind_eq]; simp
  | f + 1, m => by
      rw [rfindRun, evaln_rfind_eq]
      split_ifs with h
      · simp only [Nat.add_sub_cancel]
        congr 1
        funext x
        split_ifs
        · rfl
        · exact rfindRun_eq cf a f (m + 1)
      · rfl

/-- One step of the loop, in the form the machine's invariant consumes: the search at
    `(f+1, m)` either finishes here or continues at `(f, m+1)`. -/
lemma rfindRun_succ (cf : Nat.Partrec.Code) (a f m : ℕ) :
    rfindRun cf a (f + 1) m
      = if Nat.pair a m < f + 1 then
          (Nat.Partrec.Code.evaln (f + 1) cf (Nat.pair a m) >>= fun x =>
            if x = 0 then some m else rfindRun cf a f (m + 1))
        else none := by
  rw [rfindRun]

end LogicalInduction.EvalnCompiler
