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

/-- The hypothesis the structural induction supplies for a child: its interface registers
    really hold `evaln` of the child, on whatever input they are given. -/
def ChildEncodes (af : ℕ) (haf : 16 ≤ af) (cf : Nat.Partrec.Code)
    (Ff : (Fin af → ℕ) → Fin af → ℕ) : Prop :=
  ∀ u : Fin af → ℕ,
    Ff u ⟨2, by omega⟩
        = resultTag (Nat.Partrec.Code.evaln (u ⟨1, by omega⟩) cf (u ⟨0, by omega⟩)) ∧
      Ff u ⟨3, by omega⟩
        = resultVal (Nat.Partrec.Code.evaln (u ⟨1, by omega⟩) cf (u ⟨0, by omega⟩))

/-- **Running a child on the one vector it is actually given.**

    complexitylib's `runChild` asks for the child's specification at *every* bounded
    register vector, even though it instantiates that specification at a single one. That
    over-quantification is not dischargeable here: at `F := codeVals cf` the boundedness
    premise `∀ k, u k < B → ∀ k, F u k < B` is false for any usable `B` (take
    `cf = pair succ succ`, `u 0 = B - 2`, `u 1 = B - 1`). This variant asks only for the
    instance, and is otherwise identical — a candidate for upstreaming. -/
lemma runChildFixed {A m : ℕ} (W : Fin m ↪ Fin A) (R : Regs A n) (M : TM n)
    (F : (Fin m → ℕ) → Fin m → ℕ) (t : ℕ)
    {inp₀ : Tape} {ys : List Bool} (w₀ : Fin n → Tape)
    (hpark : ∀ i, Parked (w₀ i)) (V : Fin A → ℕ)
    (hM : ∀ (Wb : Fin n → Tape), (∀ i, Parked (Wb i)) →
      M.HoareTime (EmitPred inp₀ (regsWork (W.trans R) Wb (fun j => V (W j))) ys)
                  (EmitPred inp₀ (regsWork (W.trans R) Wb (F (fun j => V (W j)))) ys) t) :
    M.HoareTime (EmitPred inp₀ (regsWork R w₀ V) ys)
                (EmitPred inp₀ (regsWork R w₀ (writeWindow W V (F (fun j => V (W j))))) ys)
                t := by
  have h := hM (regsWork R w₀ V) (parked_regsWork R hpark V)
  rw [regsWork_restrict R W w₀ V, ← regsWork_window]
  exact h

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

    Defined *directly* rather than as a multiple of `codeSize c`, so that
    `codeRegs (pair cf cg)` reduces to `16 + codeRegs cf + codeRegs cg`
    **definitionally**. A `prec` node is thirty-three wide rather than sixteen: it needs
    more working registers, and the thirty-third is its loop counter, which must sit
    *outside* the block its loop body names (`precMain`, `precLoopIdx`). Without that every recursive call in `compileCodeAt` would need a
    transport along an arity equation, and the dependent-type friction would spread
    through the whole assembly. -/
def codeRegs : Nat.Partrec.Code → ℕ
  | .zero => 16
  | .succ => 16
  | .left => 16
  | .right => 16
  | .pair cf cg => 16 + codeRegs cf + codeRegs cg
  | .comp cf cg => 16 + codeRegs cf + codeRegs cg
  | .prec cf cg => 33 + codeRegs cf + codeRegs cg
  | .rfind' cf => 33 + codeRegs cf

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

/-! ## Reading a binary node's register vector

The same mechanism the `rfind'` proofs use: reading one named register out of an update to
another is a *numeric* index test, so `simp only` plus `norm_num` evaluates a whole stage
chain instead of a hand-ordered `rw` chain that breaks on any change of unfolding order. -/

section BinaryRead
variable {af ag : ℕ}

lemma selfW_update_apply (i j : Fin 16) (X : Fin (16 + af + ag) → ℕ) (x : ℕ) :
    Function.update X (selfW af ag j) x (selfW af ag i)
      = if (i : ℕ) = (j : ℕ) then x else X (selfW af ag i) := by
  by_cases h : (i : ℕ) = (j : ℕ)
  · rw [if_pos h, Fin.ext h, Function.update_self]
  · rw [if_neg h, Function.update_of_ne (selfW_ne_selfW i j h)]

lemma leftLoc_update_apply (haf : 16 ≤ af) (i j : Fin 16)
    (X : Fin (16 + af + ag) → ℕ) (x : ℕ) :
    Function.update X (leftLoc af ag haf j) x (leftLoc af ag haf i)
      = if (i : ℕ) = (j : ℕ) then x else X (leftLoc af ag haf i) := by
  by_cases h : (i : ℕ) = (j : ℕ)
  · rw [if_pos h, Fin.ext h, Function.update_self]
  · rw [if_neg h, Function.update_of_ne (fun e => h (by
      have := congrArg (Fin.val) e
      simpa [leftLoc, shiftEmb_val] using this))]

lemma rightLoc_update_apply (hag : 16 ≤ ag) (i j : Fin 16)
    (X : Fin (16 + af + ag) → ℕ) (x : ℕ) :
    Function.update X (rightLoc af ag hag j) x (rightLoc af ag hag i)
      = if (i : ℕ) = (j : ℕ) then x else X (rightLoc af ag hag i) := by
  by_cases h : (i : ℕ) = (j : ℕ)
  · rw [if_pos h, Fin.ext h, Function.update_self]
  · rw [if_neg h, Function.update_of_ne (fun e => h (by
      have := congrArg (Fin.val) e
      simpa [rightLoc, shiftEmb_val] using this))]

@[simp] lemma selfW_leftLoc_upd (haf : 16 ≤ af) (i j : Fin 16)
    (X : Fin (16 + af + ag) → ℕ) (x : ℕ) :
    Function.update X (leftLoc af ag haf j) x (selfW af ag i) = X (selfW af ag i) :=
  Function.update_of_ne (selfW_ne_leftLoc haf i j) x X

@[simp] lemma selfW_rightLoc_upd (hag : 16 ≤ ag) (haf : 16 ≤ af) (i j : Fin 16)
    (X : Fin (16 + af + ag) → ℕ) (x : ℕ) :
    Function.update X (rightLoc af ag hag j) x (selfW af ag i) = X (selfW af ag i) :=
  Function.update_of_ne (selfW_ne_rightLoc hag haf i j) x X

@[simp] lemma leftLoc_selfW_upd (haf : 16 ≤ af) (i j : Fin 16)
    (X : Fin (16 + af + ag) → ℕ) (x : ℕ) :
    Function.update X (selfW af ag j) x (leftLoc af ag haf i) = X (leftLoc af ag haf i) :=
  Function.update_of_ne (Ne.symm (selfW_ne_leftLoc haf j i)) x X

@[simp] lemma rightLoc_selfW_upd (hag : 16 ≤ ag) (haf : 16 ≤ af) (i j : Fin 16)
    (X : Fin (16 + af + ag) → ℕ) (x : ℕ) :
    Function.update X (selfW af ag j) x (rightLoc af ag hag i)
      = X (rightLoc af ag hag i) :=
  Function.update_of_ne (Ne.symm (selfW_ne_rightLoc hag haf j i)) x X

@[simp] lemma leftLoc_rightLoc_upd (haf : 16 ≤ af) (hag : 16 ≤ ag) (i j : Fin 16)
    (X : Fin (16 + af + ag) → ℕ) (x : ℕ) :
    Function.update X (rightLoc af ag hag j) x (leftLoc af ag haf i)
      = X (leftLoc af ag haf i) :=
  Function.update_of_ne (leftLoc_ne_rightLoc haf hag i j) x X

@[simp] lemma rightLoc_leftLoc_upd (haf : 16 ≤ af) (hag : 16 ≤ ag) (i j : Fin 16)
    (X : Fin (16 + af + ag) → ℕ) (x : ℕ) :
    Function.update X (leftLoc af ag haf j) x (rightLoc af ag hag i)
      = X (rightLoc af ag hag i) :=
  Function.update_of_ne (Ne.symm (leftLoc_ne_rightLoc haf hag j i)) x X

/-! ### The two child subtrees, as windows -/

lemma leftSub_win_selfW (i : Fin 16) (X : Fin (16 + af + ag) → ℕ) (u : Fin af → ℕ) :
    writeWindow (leftSub af ag) X u (selfW af ag i) = X (selfW af ag i) :=
  writeWindow_of_ne _ _ _ (fun t => leftSub_ne_selfW t i)

lemma leftSub_win_leftLoc (haf : 16 ≤ af) (j : Fin 16) (X : Fin (16 + af + ag) → ℕ)
    (u : Fin af → ℕ) :
    writeWindow (leftSub af ag) X u (leftLoc af ag haf j)
      = u ⟨(j : ℕ), by have := j.isLt; omega⟩ := by
  rw [leftLoc_eq haf, writeWindow_apply]

lemma leftSub_win_rightLoc (hag : 16 ≤ ag) (j : Fin 16) (X : Fin (16 + af + ag) → ℕ)
    (u : Fin af → ℕ) :
    writeWindow (leftSub af ag) X u (rightLoc af ag hag j) = X (rightLoc af ag hag j) :=
  writeWindow_of_ne _ _ _ (fun t => leftSub_ne_rightLoc hag t j)

lemma rightSub_win_selfW (haf : 16 ≤ af) (i : Fin 16) (X : Fin (16 + af + ag) → ℕ)
    (u : Fin ag → ℕ) :
    writeWindow (rightSub af ag) X u (selfW af ag i) = X (selfW af ag i) :=
  writeWindow_of_ne _ _ _ (fun t => rightSub_ne_selfW haf t i)

lemma rightSub_win_rightLoc (hag : 16 ≤ ag) (j : Fin 16) (X : Fin (16 + af + ag) → ℕ)
    (u : Fin ag → ℕ) :
    writeWindow (rightSub af ag) X u (rightLoc af ag hag j)
      = u ⟨(j : ℕ), by have := j.isLt; omega⟩ := by
  rw [rightLoc_eq hag, writeWindow_apply]

lemma rightSub_win_leftLoc (haf : 16 ≤ af) (j : Fin 16) (X : Fin (16 + af + ag) → ℕ)
    (u : Fin ag → ℕ) :
    writeWindow (rightSub af ag) X u (leftLoc af ag haf j) = X (leftLoc af ag haf j) :=
  writeWindow_of_ne _ _ _ (fun t => rightSub_ne_leftLoc haf t j)

/-! ### The pairing window inside the node's own block -/

/-- `pairTM`'s output vector, with the index test numeric so a `simp only` can evaluate
    it at an index that arrives as a `Fin.mk`. -/
lemma pairVals_apply (v : Fin 8 → ℕ) (k : Fin 8) :
    pairVals v k =
      if (k : ℕ) = 2 then v 1 - v 0
      else if (k : ℕ) = 3 then (if v 0 < v 1 then 1 else 0)
      else if (k : ℕ) = 4 then v 0 + (v 1 - v 0)
      else if (k : ℕ) = 5 then v 0 + (v 1 - v 0)
      else if (k : ℕ) = 6 then Nat.pair (v 0) (v 1)
      else if (k : ℕ) = 7 then 1 - (if v 0 < v 1 then 1 else 0)
      else v k := by
  simp only [pairVals, Fin.ext_iff]
  norm_num

/-- `pairTM`'s output slot. -/
lemma pairVals_six (v : Fin 8 → ℕ) : pairVals v 6 = Nat.pair (v 0) (v 1) := by
  simp [pairVals]

lemma pairWin_selfW (i : Fin 16) (h : ∀ t : Fin 8, 6 + (t : ℕ) ≠ (i : ℕ))
    (X : Fin (16 + af + ag) → ℕ) (u : Fin 8 → ℕ) :
    writeWindow (pairSlot.trans (selfW af ag)) X u (selfW af ag i) = X (selfW af ag i) := by
  rw [pairAmb_eq]
  exact writeWindow_of_ne _ _ _ (fun t => pairAmb_ne_selfW t i (h t))

/-- The pairing window as a total read-off: slots `6`–`13` of the node's block. -/
lemma pairWin_selfW_apply (i : Fin 16) (X : Fin (16 + af + ag) → ℕ) (u : Fin 8 → ℕ) :
    writeWindow (pairSlot.trans (selfW af ag)) X u (selfW af ag i)
      = if h : 6 ≤ (i : ℕ) ∧ (i : ℕ) < 14 then u ⟨(i : ℕ) - 6, by omega⟩
        else X (selfW af ag i) := by
  by_cases h : 6 ≤ (i : ℕ) ∧ (i : ℕ) < 14
  · rw [dif_pos h]
    have hid : (pairSlot.trans (selfW af ag)) ⟨(i : ℕ) - 6, by omega⟩ = selfW af ag i := by
      apply Fin.ext
      simp [pairSlot, selfW, shiftEmb_val]
      omega
    rw [← hid, writeWindow_apply]
  · rw [dif_neg h, pairAmb_eq]
    refine writeWindow_of_ne _ _ _ (fun t => pairAmb_ne_selfW t i ?_)
    have := t.isLt
    simp at h ⊢
    omega

lemma pairWin_twelve (X : Fin (16 + af + ag) → ℕ) (u : Fin 8 → ℕ) :
    writeWindow (pairSlot.trans (selfW af ag)) X u (selfW af ag 12) = u 6 := by
  rw [← pairTrans_six, writeWindow_apply]

lemma pairWin_leftLoc (haf : 16 ≤ af) (j : Fin 16) (X : Fin (16 + af + ag) → ℕ)
    (u : Fin 8 → ℕ) :
    writeWindow (pairSlot.trans (selfW af ag)) X u (leftLoc af ag haf j)
      = X (leftLoc af ag haf j) := by
  rw [pairAmb_eq]
  exact writeWindow_of_ne _ _ _ (fun t => pairAmb_ne_leftLoc haf t j)

lemma pairWin_rightLoc (hag : 16 ≤ ag) (haf : 16 ≤ af) (j : Fin 16)
    (X : Fin (16 + af + ag) → ℕ) (u : Fin 8 → ℕ) :
    writeWindow (pairSlot.trans (selfW af ag)) X u (rightLoc af ag hag j)
      = X (rightLoc af ag hag j) := by
  rw [pairAmb_eq]
  exact writeWindow_of_ne _ _ _ (fun t => pairAmb_ne_rightLoc hag haf t j)

end BinaryRead

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

/-! ### `precRun` in register terms

The machine carries `precRun`'s value as a canonical tag/value pair, so the loop needs the
iterator's tag and value *separately*, each as a product of `0/1` masks. The step case has
exactly the shape of `comp` — the previous result is bound into a child's input — so the
same masking argument applies: the child runs unconditionally on `resultVal` of the
previous level, which is the canonical `0` when that level failed, and the `alive` factor
discards the answer.

`cf` appears only in the base case: it is setup-only, and the loop body invokes `cg`
alone. -/

lemma precRun_zero_tag (cf cg : Nat.Partrec.Code) (a f : ℕ) :
    resultTag (precRun cf cg a f 0)
      = (if Nat.pair a 0 < f then 1 else 0)
          * resultTag (Nat.Partrec.Code.evaln f cf a) := by
  rw [precRun]
  split_ifs <;> simp

lemma precRun_zero_val (cf cg : Nat.Partrec.Code) (a f : ℕ) :
    resultVal (precRun cf cg a f 0)
      = (if Nat.pair a 0 < f then 1 else 0)
          * resultVal (Nat.Partrec.Code.evaln f cf a) := by
  rw [precRun]
  split_ifs <;> simp

/-- **The step mask.** `alive` is the product of the level guard, the previous level's
    tag, and the child's tag. -/
lemma precRun_succ_tag (cf cg : Nat.Partrec.Code) (a f j : ℕ) :
    resultTag (precRun cf cg a f (j + 1))
      = (if Nat.pair a (j + 1) < f + (j + 1) then 1 else 0)
          * resultTag (precRun cf cg a f j)
          * resultTag (Nat.Partrec.Code.evaln (f + (j + 1)) cg
              (Nat.pair a (Nat.pair j (resultVal (precRun cf cg a f j))))) := by
  rw [precRun]
  cases hp : precRun cf cg a f j <;> split_ifs <;> simp [hp]

lemma precRun_succ_val (cf cg : Nat.Partrec.Code) (a f j : ℕ) :
    resultVal (precRun cf cg a f (j + 1))
      = (if Nat.pair a (j + 1) < f + (j + 1) then 1 else 0)
          * resultTag (precRun cf cg a f j)
          * resultTag (Nat.Partrec.Code.evaln (f + (j + 1)) cg
              (Nat.pair a (Nat.pair j (resultVal (precRun cf cg a f j)))))
          * resultVal (Nat.Partrec.Code.evaln (f + (j + 1)) cg
              (Nat.pair a (Nat.pair j (resultVal (precRun cf cg a f j))))) := by
  rw [precRun]
  cases hp : precRun cf cg a f j <;> split_ifs <;> simp [hp]

/-- The tag is always `0` or `1`, which every mask step needs. -/
lemma resultTag_le_one (o : Option ℕ) : resultTag o ≤ 1 := by
  cases o <;> simp

/-! ### The level guards are free

`precRun` re-checks a guard at every level. The machine does not have to: `Nat.pair a ·`
is strictly increasing, so `Nat.pair a j` grows by at least `1` per level while the level
fuel `f + j` grows by exactly `1`. Hence the outer guard at level `m` implies every level
guard below it, and the loop body needs **no guard test** — saving a `pairTM` call and a
comparison per iteration. -/

lemma pair_lt_pair_succ (a b : ℕ) : Nat.pair a b < Nat.pair a (b + 1) := by
  unfold Nat.pair
  rcases lt_trichotomy a b with h | h | h
  · rw [if_pos h, if_pos (by omega)]
    have : (b + 1) * (b + 1) = b * b + 2 * b + 1 := by ring
    omega
  · subst h
    rw [if_neg (by omega), if_pos (by omega)]
    have : (a + 1) * (a + 1) = a * a + 2 * a + 1 := by ring
    omega
  · rw [if_neg (by omega)]
    rcases Nat.lt_or_ge a (b + 1) with h2 | h2
    · rw [if_pos h2]
      have hb : b + 1 = a := by omega
      rw [hb]
      have : a * a + a + b = a * a + a + (a - 1) := by omega
      omega
    · rw [if_neg (by omega)]; omega

/-- The index grows at least as fast as the level fuel. -/
lemma pair_add_le (a : ℕ) : ∀ j m, j ≤ m → Nat.pair a j + (m - j) ≤ Nat.pair a m := by
  intro j m
  induction m with
  | zero => intro h; simp_all
  | succ m ih =>
    intro h
    rcases Nat.lt_or_ge j (m + 1) with hj | hj
    · have hjm : j ≤ m := by omega
      have h1 := ih hjm
      have h2 := pair_lt_pair_succ a m
      omega
    · have : j = m + 1 := by omega
      subst this; simp

/-- **Every level guard is implied by the outer one.** -/
lemma level_guard (a m f j : ℕ) (hj : j ≤ m) (hout : Nat.pair a m < f + m) :
    Nat.pair a j < f + j := by
  have := pair_add_le a j m hj
  omega

/-! ### The guard-free iterator

Under the outer guard this is what the machine's loop actually computes. -/

def precRunG (cf cg : Nat.Partrec.Code) (a f : ℕ) : ℕ → Option ℕ
  | 0 => Nat.Partrec.Code.evaln f cf a
  | j + 1 =>
      precRunG cf cg a f j >>= fun i =>
        Nat.Partrec.Code.evaln (f + (j + 1)) cg (Nat.pair a (Nat.pair j i))

lemma precRunG_eq_precRun (cf cg : Nat.Partrec.Code) (a m f : ℕ)
    (hout : Nat.pair a m < f + m) : ∀ j, j ≤ m →
    precRunG cf cg a f j = precRun cf cg a f j
  | 0, _ => by
      rw [precRunG, precRun, if_pos (by simpa using level_guard a m f 0 (Nat.zero_le _) hout)]
  | j + 1, hj => by
      rw [precRunG, precRun, if_pos (level_guard a m f (j + 1) hj hout),
        precRunG_eq_precRun cf cg a m f hout j (by omega)]

/-! ### The guard-free step masks, and closure against `evaln`

These are what the machine's body and finish phases target: the body proves the two mask
identities, and the finish phase applies `precRunG_eq_evaln`. -/

lemma precRunG_succ_tag (cf cg : Nat.Partrec.Code) (a f j : ℕ) :
    resultTag (precRunG cf cg a f (j + 1))
      = resultTag (precRunG cf cg a f j)
          * resultTag (Nat.Partrec.Code.evaln (f + (j + 1)) cg
              (Nat.pair a (Nat.pair j (resultVal (precRunG cf cg a f j))))) := by
  rw [precRunG]
  cases hp : precRunG cf cg a f j <;> simp [hp]

lemma precRunG_succ_val (cf cg : Nat.Partrec.Code) (a f j : ℕ) :
    resultVal (precRunG cf cg a f (j + 1))
      = resultTag (precRunG cf cg a f j)
          * resultTag (Nat.Partrec.Code.evaln (f + (j + 1)) cg
              (Nat.pair a (Nat.pair j (resultVal (precRunG cf cg a f j)))))
          * resultVal (Nat.Partrec.Code.evaln (f + (j + 1)) cg
              (Nat.pair a (Nat.pair j (resultVal (precRunG cf cg a f j))))) := by
  rw [precRunG]
  cases hp : precRunG cf cg a f j <;> simp [hp]

@[simp] lemma precRunG_zero (cf cg : Nat.Partrec.Code) (a f : ℕ) :
    precRunG cf cg a f 0 = Nat.Partrec.Code.evaln f cf a := rfl

/-- **The machine's closure theorem.** The loop computes `precRunG` from base fuel
    `fuel - m`; under the outer guard that is exactly `evaln`.

    The side condition `m ≤ fuel` needed by `precRun_eq_evaln` is *implied* by the outer
    guard, since `m ≤ Nat.pair a m`. So the finish phase has only the outer guard to
    check — the same `input < fuel` test every other constructor already uses. -/
lemma precRunG_eq_evaln (cf cg : Nat.Partrec.Code) (a m fuel : ℕ)
    (hout : Nat.pair a m < fuel) :
    precRunG cf cg a (fuel - m) m
      = Nat.Partrec.Code.evaln fuel (cf.prec cg) (Nat.pair a m) := by
  have hm : m ≤ fuel := le_trans (Nat.right_le_pair a m) (Nat.le_of_lt hout)
  rw [precRunG_eq_precRun cf cg a m (fuel - m) (by omega) m le_rfl,
    precRun_eq_evaln cf cg a m fuel hm]

/-- When the outer guard fails, both sides are canonical `none` — the only top-level case
    split the whole construction needs. -/
lemma evaln_eq_none_of_not_guard (k : ℕ) (c : Nat.Partrec.Code) (m : ℕ)
    (hout : ¬ m < k) : Nat.Partrec.Code.evaln k c m = none := by
  cases h : Nat.Partrec.Code.evaln k c m with
  | none => rfl
  | some x => exact absurd (Nat.Partrec.Code.evaln_bound h) hout

/-! ## `prec`: register layout

`prec` needs more than sixteen registers of its own — a loop state, two pairing temporaries
and a pairing window — so its node block is **thirty-two** wide rather than sixteen. The
first four registers keep the standard interface (`input`, `fuel`, `tag`, `value`) so a
parent reads a `prec` child exactly like any other.

| index | role |
| ---: | --- |
| `0` | input `n`, preserved |
| `1` | fuel, preserved |
| `2` | result tag |
| `3` | result value |
| `4` | outer guard flag `[n < fuel]` |
| `5` | outer guard scratch |
| `6` | `a` — the fixed parameter, `n.unpair.1` |
| `7` | `m` — the recursion index, `n.unpair.2`; the loop counter |
| `8` | `baseFuel = fuel - m` |
| `9` | `j` — current level |
| `10` | `alive` — the cumulative success mask |
| `11` | `acc` — the reconstructed value at level `j` |
| `12` | `curFuel = baseFuel + j` |
| `13`–`15` | temporaries |
| `16`–`24` | the `unpairTM` / `pairTM` window (nine registers; `pairTM` uses eight) |
| `25`–`31` | spare |

The loop counter `7` sits in the node's own block, outside every child subtree, so
`forRegTM` never touches a child window. -/

section PrecLayout
variable {af ag : ℕ}

/-- The `prec` node's own thirty-two registers. -/
def precSelf (af ag : ℕ) : Fin 32 ↪ Fin (32 + af + ag) := shiftEmb 0 (by omega)
/-- `cf`'s whole subtree. -/
def precLeftSub (af ag : ℕ) : Fin af ↪ Fin (32 + af + ag) := shiftEmb 32 (by omega)
/-- `cg`'s whole subtree. -/
def precRightSub (af ag : ℕ) : Fin ag ↪ Fin (32 + af + ag) := shiftEmb (32 + af) (by omega)
/-- `cf`'s own sixteen. -/
def precLeftLoc (af ag : ℕ) (h : 16 ≤ af) : Fin 16 ↪ Fin (32 + af + ag) :=
  shiftEmb 32 (by omega)
/-- `cg`'s own sixteen. -/
def precRightLoc (af ag : ℕ) (h : 16 ≤ ag) : Fin 16 ↪ Fin (32 + af + ag) :=
  shiftEmb (32 + af) (by omega)
/-- The pairing window, at offset `16` of the node's block. -/
def precPairW (af ag : ℕ) : Fin 8 ↪ Fin (32 + af + ag) := shiftEmb 16 (by omega)
/-- The unpairing window, same offset, nine wide. -/
def precUnpairW (af ag : ℕ) : Fin 9 ↪ Fin (32 + af + ag) := shiftEmb 16 (by omega)

/-! ### Index disequalities -/

lemma precSelf_ne_self (i j : Fin 32) (h : (i : ℕ) ≠ (j : ℕ)) :
    precSelf af ag i ≠ precSelf af ag j := by
  apply amb_ne; simpa using h

lemma precSelf_ne_leftLoc (haf : 16 ≤ af) (i : Fin 32) (j : Fin 16) :
    precSelf af ag i ≠ precLeftLoc af ag haf j := by
  apply amb_ne; have := i.isLt; simp; omega

lemma precSelf_ne_rightLoc (hag : 16 ≤ ag) (haf : 16 ≤ af) (i : Fin 32) (j : Fin 16) :
    precSelf af ag i ≠ precRightLoc af ag hag j := by
  apply amb_ne; have := i.isLt; simp; omega

lemma precLeftLoc_ne_rightLoc (haf : 16 ≤ af) (hag : 16 ≤ ag) (i j : Fin 16) :
    precLeftLoc af ag haf i ≠ precRightLoc af ag hag j := by
  apply amb_ne; have := i.isLt; simp; omega

lemma precLeftSub_ne_self (i : Fin af) (j : Fin 32) :
    precLeftSub af ag i ≠ precSelf af ag j := by
  apply amb_ne; have := j.isLt; simp; omega

lemma precRightSub_ne_self (haf : 16 ≤ af) (i : Fin ag) (j : Fin 32) :
    precRightSub af ag i ≠ precSelf af ag j := by
  apply amb_ne; have := j.isLt; simp; omega

lemma precRightSub_ne_leftLoc (haf : 16 ≤ af) (i : Fin ag) (j : Fin 16) :
    precRightSub af ag i ≠ precLeftLoc af ag haf j := by
  apply amb_ne; have := j.isLt; simp; omega

lemma precLeftSub_ne_rightLoc (hag : 16 ≤ ag) (i : Fin af) (j : Fin 16) :
    precLeftSub af ag i ≠ precRightLoc af ag hag j := by
  apply amb_ne; have := i.isLt; simp; omega

/-- The pairing window lives inside the node's own block. -/
lemma precPairW_eq (j : Fin 8) :
    precPairW af ag j = precSelf af ag ⟨16 + (j : ℕ), by have := j.isLt; omega⟩ := by
  apply Fin.ext; simp [precPairW, precSelf, shiftEmb_val]

lemma precPairW_ne_self (i : Fin 8) (j : Fin 32) (h : 16 + (i : ℕ) ≠ (j : ℕ)) :
    precPairW af ag i ≠ precSelf af ag j := by
  apply amb_ne; simpa using h

lemma precPairW_ne_leftLoc (haf : 16 ≤ af) (i : Fin 8) (j : Fin 16) :
    precPairW af ag i ≠ precLeftLoc af ag haf j := by
  apply amb_ne; have := i.isLt; simp; omega

lemma precPairW_ne_rightLoc (hag : 16 ≤ ag) (haf : 16 ≤ af) (i : Fin 8) (j : Fin 16) :
    precPairW af ag i ≠ precRightLoc af ag hag j := by
  apply amb_ne; have := i.isLt; simp; omega

/-- A child's local block is the first sixteen of its subtree. -/
lemma precRightLoc_eq (hag : 16 ≤ ag) (j : Fin 16) :
    precRightLoc af ag hag j
      = precRightSub af ag ⟨(j : ℕ), by have := j.isLt; omega⟩ := by
  apply Fin.ext; simp [precRightLoc, precRightSub, shiftEmb_val]

lemma precLeftLoc_eq (haf : 16 ≤ af) (j : Fin 16) :
    precLeftLoc af ag haf j
      = precLeftSub af ag ⟨(j : ℕ), by have := j.isLt; omega⟩ := by
  apply Fin.ext; simp [precLeftLoc, precLeftSub, shiftEmb_val]

lemma precUnpairW_ne_self (i : Fin 9) (j : Fin 32) (h : 16 + (i : ℕ) ≠ (j : ℕ)) :
    precUnpairW af ag i ≠ precSelf af ag j := by
  apply amb_ne; simpa using h

lemma precUnpairW_ne_leftLoc (haf : 16 ≤ af) (i : Fin 9) (j : Fin 16) :
    precUnpairW af ag i ≠ precLeftLoc af ag haf j := by
  apply amb_ne; have := i.isLt; simp; omega

lemma precUnpairW_zero : (precUnpairW af ag) 0 = precSelf af ag 16 := by
  apply Fin.ext; simp [precUnpairW, precSelf, shiftEmb_val]

lemma precUnpairW_one : (precUnpairW af ag) 1 = precSelf af ag 17 := by
  apply Fin.ext; simp [precUnpairW, precSelf, shiftEmb_val]

/-- The pair window's slots, as node-block indices. -/
lemma precPairW_zero : (precPairW af ag) 0 = precSelf af ag 16 := by
  apply Fin.ext; simp [precPairW, precSelf, shiftEmb_val]

lemma precPairW_one : (precPairW af ag) 1 = precSelf af ag 17 := by
  apply Fin.ext; simp [precPairW, precSelf, shiftEmb_val]

lemma precPairW_six : (precPairW af ag) 6 = precSelf af ag 22 := by
  apply Fin.ext; simp [precPairW, precSelf, shiftEmb_val]

end PrecLayout

/-! ### Reading a `prec` node's register vector

The same numeric-index mechanism as for a binary node and for `rfind'`. -/

section PrecReadTools
variable {af ag : ℕ}

lemma precUnpairW_ne_rightLoc (hag : 16 ≤ ag) (haf : 16 ≤ af) (i : Fin 9) (j : Fin 16) :
    precUnpairW af ag i ≠ precRightLoc af ag hag j := by
  apply amb_ne; have := i.isLt; simp; omega

lemma precSelf_update_apply (i j : Fin 32) (X : Fin (32 + af + ag) → ℕ) (x : ℕ) :
    Function.update X (precSelf af ag j) x (precSelf af ag i)
      = if (i : ℕ) = (j : ℕ) then x else X (precSelf af ag i) := by
  by_cases h : (i : ℕ) = (j : ℕ)
  · rw [if_pos h, Fin.ext h, Function.update_self]
  · rw [if_neg h, Function.update_of_ne (precSelf_ne_self i j h)]

lemma precLeftLoc_update_apply (haf : 16 ≤ af) (i j : Fin 16)
    (X : Fin (32 + af + ag) → ℕ) (x : ℕ) :
    Function.update X (precLeftLoc af ag haf j) x (precLeftLoc af ag haf i)
      = if (i : ℕ) = (j : ℕ) then x else X (precLeftLoc af ag haf i) := by
  by_cases h : (i : ℕ) = (j : ℕ)
  · rw [if_pos h, Fin.ext h, Function.update_self]
  · rw [if_neg h, Function.update_of_ne (fun e => h (by
      have := congrArg (Fin.val) e
      simpa [precLeftLoc, shiftEmb_val] using this))]

lemma precRightLoc_update_apply (hag : 16 ≤ ag) (i j : Fin 16)
    (X : Fin (32 + af + ag) → ℕ) (x : ℕ) :
    Function.update X (precRightLoc af ag hag j) x (precRightLoc af ag hag i)
      = if (i : ℕ) = (j : ℕ) then x else X (precRightLoc af ag hag i) := by
  by_cases h : (i : ℕ) = (j : ℕ)
  · rw [if_pos h, Fin.ext h, Function.update_self]
  · rw [if_neg h, Function.update_of_ne (fun e => h (by
      have := congrArg (Fin.val) e
      simpa [precRightLoc, shiftEmb_val] using this))]

@[simp] lemma precSelf_leftLoc_upd (haf : 16 ≤ af) (i : Fin 32) (j : Fin 16)
    (X : Fin (32 + af + ag) → ℕ) (x : ℕ) :
    Function.update X (precLeftLoc af ag haf j) x (precSelf af ag i)
      = X (precSelf af ag i) :=
  Function.update_of_ne (precSelf_ne_leftLoc haf i j) x X

@[simp] lemma precSelf_rightLoc_upd (hag : 16 ≤ ag) (haf : 16 ≤ af) (i : Fin 32)
    (j : Fin 16) (X : Fin (32 + af + ag) → ℕ) (x : ℕ) :
    Function.update X (precRightLoc af ag hag j) x (precSelf af ag i)
      = X (precSelf af ag i) :=
  Function.update_of_ne (precSelf_ne_rightLoc hag haf i j) x X

@[simp] lemma precLeftLoc_self_upd (haf : 16 ≤ af) (i : Fin 16) (j : Fin 32)
    (X : Fin (32 + af + ag) → ℕ) (x : ℕ) :
    Function.update X (precSelf af ag j) x (precLeftLoc af ag haf i)
      = X (precLeftLoc af ag haf i) :=
  Function.update_of_ne (Ne.symm (precSelf_ne_leftLoc haf j i)) x X

@[simp] lemma precRightLoc_self_upd (hag : 16 ≤ ag) (haf : 16 ≤ af) (i : Fin 16)
    (j : Fin 32) (X : Fin (32 + af + ag) → ℕ) (x : ℕ) :
    Function.update X (precSelf af ag j) x (precRightLoc af ag hag i)
      = X (precRightLoc af ag hag i) :=
  Function.update_of_ne (Ne.symm (precSelf_ne_rightLoc hag haf j i)) x X

@[simp] lemma precLeftLoc_rightLoc_upd (haf : 16 ≤ af) (hag : 16 ≤ ag) (i j : Fin 16)
    (X : Fin (32 + af + ag) → ℕ) (x : ℕ) :
    Function.update X (precRightLoc af ag hag j) x (precLeftLoc af ag haf i)
      = X (precLeftLoc af ag haf i) :=
  Function.update_of_ne (precLeftLoc_ne_rightLoc haf hag i j) x X

@[simp] lemma precRightLoc_leftLoc_upd (haf : 16 ≤ af) (hag : 16 ≤ ag) (i j : Fin 16)
    (X : Fin (32 + af + ag) → ℕ) (x : ℕ) :
    Function.update X (precLeftLoc af ag haf j) x (precRightLoc af ag hag i)
      = X (precRightLoc af ag hag i) :=
  Function.update_of_ne (Ne.symm (precLeftLoc_ne_rightLoc haf hag j i)) x X

/-! #### Windows -/

lemma precPairWin_selfW_apply (i : Fin 32) (X : Fin (32 + af + ag) → ℕ) (u : Fin 8 → ℕ) :
    writeWindow (precPairW af ag) X u (precSelf af ag i)
      = if h : 16 ≤ (i : ℕ) ∧ (i : ℕ) < 24 then u ⟨(i : ℕ) - 16, by omega⟩
        else X (precSelf af ag i) := by
  by_cases h : 16 ≤ (i : ℕ) ∧ (i : ℕ) < 24
  · rw [dif_pos h]
    have hid : precPairW af ag ⟨(i : ℕ) - 16, by omega⟩ = precSelf af ag i := by
      apply Fin.ext
      simp [precPairW, precSelf, shiftEmb_val]
      omega
    rw [← hid, writeWindow_apply]
  · rw [dif_neg h]
    refine writeWindow_of_ne _ _ _ (fun t => precPairW_ne_self t i ?_)
    have := t.isLt
    simp at h ⊢
    omega

lemma precUnpairWin_selfW_apply (i : Fin 32) (X : Fin (32 + af + ag) → ℕ)
    (u : Fin 9 → ℕ) :
    writeWindow (precUnpairW af ag) X u (precSelf af ag i)
      = if h : 16 ≤ (i : ℕ) ∧ (i : ℕ) < 25 then u ⟨(i : ℕ) - 16, by omega⟩
        else X (precSelf af ag i) := by
  by_cases h : 16 ≤ (i : ℕ) ∧ (i : ℕ) < 25
  · rw [dif_pos h]
    have hid : precUnpairW af ag ⟨(i : ℕ) - 16, by omega⟩ = precSelf af ag i := by
      apply Fin.ext
      simp [precUnpairW, precSelf, shiftEmb_val]
      omega
    rw [← hid, writeWindow_apply]
  · rw [dif_neg h]
    refine writeWindow_of_ne _ _ _ (fun t => precUnpairW_ne_self t i ?_)
    have := t.isLt
    simp at h ⊢
    omega

@[simp] lemma precPairWin_leftLoc (haf : 16 ≤ af) (j : Fin 16)
    (X : Fin (32 + af + ag) → ℕ) (u : Fin 8 → ℕ) :
    writeWindow (precPairW af ag) X u (precLeftLoc af ag haf j)
      = X (precLeftLoc af ag haf j) :=
  writeWindow_of_ne _ _ _ (fun t => precPairW_ne_leftLoc haf t j)

@[simp] lemma precPairWin_rightLoc (hag : 16 ≤ ag) (haf : 16 ≤ af) (j : Fin 16)
    (X : Fin (32 + af + ag) → ℕ) (u : Fin 8 → ℕ) :
    writeWindow (precPairW af ag) X u (precRightLoc af ag hag j)
      = X (precRightLoc af ag hag j) :=
  writeWindow_of_ne _ _ _ (fun t => precPairW_ne_rightLoc hag haf t j)

@[simp] lemma precUnpairWin_leftLoc (haf : 16 ≤ af) (j : Fin 16)
    (X : Fin (32 + af + ag) → ℕ) (u : Fin 9 → ℕ) :
    writeWindow (precUnpairW af ag) X u (precLeftLoc af ag haf j)
      = X (precLeftLoc af ag haf j) :=
  writeWindow_of_ne _ _ _ (fun t => precUnpairW_ne_leftLoc haf t j)

@[simp] lemma precUnpairWin_rightLoc (hag : 16 ≤ ag) (haf : 16 ≤ af) (j : Fin 16)
    (X : Fin (32 + af + ag) → ℕ) (u : Fin 9 → ℕ) :
    writeWindow (precUnpairW af ag) X u (precRightLoc af ag hag j)
      = X (precRightLoc af ag hag j) :=
  writeWindow_of_ne _ _ _ (fun t => precUnpairW_ne_rightLoc hag haf t j)

@[simp] lemma precLeftSub_win_selfW (i : Fin 32) (X : Fin (32 + af + ag) → ℕ)
    (u : Fin af → ℕ) :
    writeWindow (precLeftSub af ag) X u (precSelf af ag i) = X (precSelf af ag i) :=
  writeWindow_of_ne _ _ _ (fun t => precLeftSub_ne_self t i)

lemma precLeftSub_win_leftLoc (haf : 16 ≤ af) (j : Fin 16)
    (X : Fin (32 + af + ag) → ℕ) (u : Fin af → ℕ) :
    writeWindow (precLeftSub af ag) X u (precLeftLoc af ag haf j)
      = u ⟨(j : ℕ), by have := j.isLt; omega⟩ := by
  rw [precLeftLoc_eq haf, writeWindow_apply]

@[simp] lemma precLeftSub_win_rightLoc (hag : 16 ≤ ag) (j : Fin 16)
    (X : Fin (32 + af + ag) → ℕ) (u : Fin af → ℕ) :
    writeWindow (precLeftSub af ag) X u (precRightLoc af ag hag j)
      = X (precRightLoc af ag hag j) :=
  writeWindow_of_ne _ _ _ (fun t => precLeftSub_ne_rightLoc hag t j)

@[simp] lemma precRightSub_win_selfW (haf : 16 ≤ af) (i : Fin 32)
    (X : Fin (32 + af + ag) → ℕ) (u : Fin ag → ℕ) :
    writeWindow (precRightSub af ag) X u (precSelf af ag i) = X (precSelf af ag i) :=
  writeWindow_of_ne _ _ _ (fun t => precRightSub_ne_self haf t i)

lemma precRightSub_win_rightLoc (hag : 16 ≤ ag) (j : Fin 16)
    (X : Fin (32 + af + ag) → ℕ) (u : Fin ag → ℕ) :
    writeWindow (precRightSub af ag) X u (precRightLoc af ag hag j)
      = u ⟨(j : ℕ), by have := j.isLt; omega⟩ := by
  rw [precRightLoc_eq hag, writeWindow_apply]

@[simp] lemma precRightSub_win_leftLoc (haf : 16 ≤ af) (j : Fin 16)
    (X : Fin (32 + af + ag) → ℕ) (u : Fin ag → ℕ) :
    writeWindow (precRightSub af ag) X u (precLeftLoc af ag haf j)
      = X (precLeftLoc af ag haf j) :=
  writeWindow_of_ne _ _ _ (fun t => precRightSub_ne_leftLoc haf t j)

end PrecReadTools

/-! ## `prec`: the loop body

One iteration, level `j → j+1`. Sixteen stages, two of them `pairTM` calls and one a
`runChild` on `cg`. No guard test — `level_guard` showed those are free — and no branch:
`cg` runs unconditionally on the reconstructed input, which is built from the canonical `0`
when the previous level failed, and the `alive` factor discards the answer.

`cf` does not appear: it is setup-only. -/

section PrecBody
variable {af ag : ℕ}

def precBodyTM (af ag : ℕ) (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (R : Regs (32 + af + ag) n) (Mg : TM n) : TM n :=
  seqTM (copyIntoTM (R (precSelf af ag 9)) (R (precSelf af ag 16))) <|
  seqTM (copyIntoTM (R (precSelf af ag 11)) (R (precSelf af ag 17))) <|
  seqTM (pairTM ((precPairW af ag).trans R)) <|
  seqTM (copyIntoTM (R (precSelf af ag 22)) (R (precSelf af ag 17))) <|
  seqTM (copyIntoTM (R (precSelf af ag 6)) (R (precSelf af ag 16))) <|
  seqTM (pairTM ((precPairW af ag).trans R)) <|
  seqTM (incRegTM (R (precSelf af ag 9))) <|
  seqTM (incRegTM (R (precSelf af ag 12))) <|
  seqTM (copyIntoTM (R (precSelf af ag 22)) (R (precRightLoc af ag hag 0))) <|
  seqTM (copyIntoTM (R (precSelf af ag 12)) (R (precRightLoc af ag hag 1))) <|
  seqTM Mg <|
  seqTM (clearRegTM (R (precSelf af ag 13))) <|
  seqTM (mulAddIntoTM (R (precSelf af ag 10)) (R (precRightLoc af ag hag 2))
          (R (precSelf af ag 13))) <|
  seqTM (copyIntoTM (R (precSelf af ag 13)) (R (precSelf af ag 10))) <|
  seqTM (clearRegTM (R (precSelf af ag 11)))
        (mulAddIntoTM (R (precSelf af ag 10)) (R (precRightLoc af ag hag 3))
          (R (precSelf af ag 11)))

/-- The state one iteration hands `cg`: the reconstructed input `Nat.pair a (Nat.pair j
    acc)` in `cg`'s input register, the level fuel in its fuel register, and the level
    counter and fuel already advanced. -/
noncomputable def precBodyPre (af ag : ℕ) (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (V : Fin (32 + af + ag) → ℕ) : Fin (32 + af + ag) → ℕ :=
  let V1 := Function.update V (precSelf af ag 16) (V (precSelf af ag 9))
  let V2 := Function.update V1 (precSelf af ag 17) (V1 (precSelf af ag 11))
  let V3 := writeWindow (precPairW af ag) V2
              (pairVals (fun i => V2 ((precPairW af ag) i)))
  let V4 := Function.update V3 (precSelf af ag 17) (V3 (precSelf af ag 22))
  let V5 := Function.update V4 (precSelf af ag 16) (V4 (precSelf af ag 6))
  let V6 := writeWindow (precPairW af ag) V5
              (pairVals (fun i => V5 ((precPairW af ag) i)))
  let V7 := Function.update V6 (precSelf af ag 9) (V6 (precSelf af ag 9) + 1)
  let V8 := Function.update V7 (precSelf af ag 12) (V7 (precSelf af ag 12) + 1)
  let V9 := Function.update V8 (precRightLoc af ag hag 0) (V8 (precSelf af ag 22))
  Function.update V9 (precRightLoc af ag hag 1) (V9 (precSelf af ag 12))

/-- The ambient register vector one iteration produces. -/
noncomputable def precBodyVals (af ag : ℕ) (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (Fg : (Fin ag → ℕ) → Fin ag → ℕ) (V : Fin (32 + af + ag) → ℕ) :
    Fin (32 + af + ag) → ℕ :=
  let V10 := precBodyPre af ag haf hag V
  let V11 := writeWindow (precRightSub af ag) V10
               (Fg (fun i => V10 ((precRightSub af ag) i)))
  let V12 := Function.update V11 (precSelf af ag 13) 0
  let V13 := Function.update V12 (precSelf af ag 13)
               (0 + V12 (precSelf af ag 10) * V12 (precRightLoc af ag hag 2))
  let V14 := Function.update V13 (precSelf af ag 10) (V13 (precSelf af ag 13))
  let V15 := Function.update V14 (precSelf af ag 11) 0
  Function.update V15 (precSelf af ag 11)
    (0 + V15 (precSelf af ag 10) * V15 (precRightLoc af ag hag 3))

/-- The loop state after `j` iterations. -/
noncomputable def precLoopVals (af ag : ℕ) (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (Fg : (Fin ag → ℕ) → Fin ag → ℕ) (V₀ : Fin (32 + af + ag) → ℕ) (j : ℕ) :
    Fin (32 + af + ag) → ℕ :=
  (precBodyVals af ag haf hag Fg)^[j] V₀

@[simp] lemma precLoopVals_zero (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (Fg : (Fin ag → ℕ) → Fin ag → ℕ) (V₀ : Fin (32 + af + ag) → ℕ) :
    precLoopVals af ag haf hag Fg V₀ 0 = V₀ := rfl

lemma precLoopVals_succ (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (Fg : (Fin ag → ℕ) → Fin ag → ℕ) (V₀ : Fin (32 + af + ag) → ℕ) (j : ℕ) :
    precLoopVals af ag haf hag Fg V₀ (j + 1)
      = precBodyVals af ag haf hag Fg (precLoopVals af ag haf hag Fg V₀ j) := by
  rw [precLoopVals, precLoopVals, Function.iterate_succ_apply']

end PrecBody

/-! ## `prec`: the loop body, verified

One level of the reconstruction, sixteen stages, as a Hoare specification. -/

section PrecBodyProof
variable {af ag : ℕ}

set_option maxHeartbeats 1000000 in
/-- **`precBodyTM` Hoare specification.** One level of the reconstruction.

    The two `pairTM` outputs are bounded by explicit semantic hypotheses rather than by any
    closure property of `B`: `Nat.pair` of two values below `B` is not below `B`, so the
    caller supplies the bound (at the global step, from `codeEvalBound`). -/
lemma precBody_hoareTime (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (R : Regs (32 + af + ag) n) (Mg : TM n)
    (Fg : (Fin ag → ℕ) → Fin ag → ℕ) (tg : ℕ)
    (V : Fin (32 + af + ag) → ℕ) (B : ℕ)
    (inp₀ : Tape) (w₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hpark : ∀ i, Parked (w₀ i)) (hB2 : 2 ≤ B)
    (hV : ∀ k, V k < B)
    (hFgB : ∀ u : Fin ag → ℕ, (∀ k, u k < B) → ∀ k, Fg u k < B)
    (hFgTag : ∀ u : Fin ag → ℕ, Fg u ⟨2, by omega⟩ ≤ 1)
    (halive : V (precSelf af ag 10) ≤ 1)
    (hj1 : V (precSelf af ag 9) + 1 < B)
    (hf1 : V (precSelf af ag 12) + 1 < B)
    (hp1 : Nat.pair (V (precSelf af ag 9)) (V (precSelf af ag 11)) < B)
    (hp2 : Nat.pair (V (precSelf af ag 6))
             (Nat.pair (V (precSelf af ag 9)) (V (precSelf af ag 11))) < B)
    (hMg : ∀ (Wb : Fin n → Tape) (u : Fin ag → ℕ), (∀ i, Parked (Wb i)) → (∀ k, u k < B) →
      Mg.HoareTime (EmitPred inp₀ (regsWork ((precRightSub af ag).trans R) Wb u) ys)
                   (EmitPred inp₀ (regsWork ((precRightSub af ag).trans R) Wb (Fg u)) ys) tg) :
    (precBodyTM af ag haf hag R Mg).HoareTime
      (EmitPred inp₀ (regsWork R w₀ V) ys)
      (EmitPred inp₀ (regsWork R w₀ (precBodyVals af ag haf hag Fg V)) ys)
      (15 * evalnArithmeticCost B + tg + 15) := by
  have hpv := parked_regsWork R hpark
  have hle : ∀ k, V k ≤ B := fun k => Nat.le_of_lt (hV k)
  -- S1: pair slot 0 := j
  have h1 := copyIntoTM_hoareTime (R (precSelf af ag 9)) (R (precSelf af ag 16))
      (Regs.ne R (precSelf_ne_self 9 16 (by decide)))
      (V (precSelf af ag 9)) (V (precSelf af ag 16))
      inp₀ (regsWork R w₀ V) ys hinp₀ (fun i _ => hpv V i)
      (regsWork_apply R w₀ V _) (regsWork_apply R w₀ V _)
  rw [regsWork_update] at h1
  replace h1 := h1.mono_bound (copyIntoTime_le_arith _ _ B (hle _) (hle _))
  set V1 := Function.update V (precSelf af ag 16) (V (precSelf af ag 9)) with hV1
  have b1 : ∀ k, V1 k < B := by
    intro k; rw [hV1]; simp only [Function.update_apply]; split_ifs <;> exact hV _
  -- S2: pair slot 1 := acc
  have h2 := copyIntoTM_hoareTime (R (precSelf af ag 11)) (R (precSelf af ag 17))
      (Regs.ne R (precSelf_ne_self 11 17 (by decide)))
      (V1 (precSelf af ag 11)) (V1 (precSelf af ag 17))
      inp₀ (regsWork R w₀ V1) ys hinp₀ (fun i _ => hpv V1 i)
      (regsWork_apply R w₀ V1 _) (regsWork_apply R w₀ V1 _)
  rw [regsWork_update] at h2
  replace h2 := h2.mono_bound
    (copyIntoTime_le_arith _ _ B (Nat.le_of_lt (b1 _)) (Nat.le_of_lt (b1 _)))
  set V2 := Function.update V1 (precSelf af ag 17) (V1 (precSelf af ag 11)) with hV2
  have b2 : ∀ k, V2 k < B := by
    intro k; rw [hV2]; simp only [Function.update_apply]; split_ifs <;> exact b1 _
  -- reads of the pair window at entry to S3
  have hw0 : V2 ((precPairW af ag) 0) = V (precSelf af ag 9) := by
    rw [show (precPairW af ag) 0 = precSelf af ag 16 from by
      apply Fin.ext; simp [precPairW, precSelf, shiftEmb_val]]
    rw [hV2, Function.update_of_ne (precSelf_ne_self 16 17 (by decide)), hV1,
      Function.update_self]
  have hw1 : V2 ((precPairW af ag) 1) = V (precSelf af ag 11) := by
    rw [show (precPairW af ag) 1 = precSelf af ag 17 from by
      apply Fin.ext; simp [precPairW, precSelf, shiftEmb_val]]
    rw [hV2, Function.update_self, hV1,
      Function.update_of_ne (precSelf_ne_self 11 16 (by decide))]
  -- S3: pair j acc
  have h3 := runChild (precPairW af ag) R (pairTM ((precPairW af ag).trans R)) pairVals
      (evalnArithmeticCost B) B w₀ hpark V2 b2
      (fun Wb u hp hu => pairTM_hoareTime_arith _ u B inp₀ Wb ys hinp₀ hp
        (fun k => Nat.le_of_lt (hu k)))
  set V3 := writeWindow (precPairW af ag) V2
      (pairVals (fun i => V2 ((precPairW af ag) i))) with hV3
  have b3 : ∀ k, V3 k < B := by
    intro k; rw [hV3]
    refine writeWindow_bounded _ _ _ B b2 (fun i => ?_) k
    refine pairVals_lt _ B hB2 (fun i => b2 _) ?_ i
    rw [hw0, hw1]; exact hp1
  have r3_22 : V3 (precSelf af ag 22)
      = Nat.pair (V (precSelf af ag 9)) (V (precSelf af ag 11)) := by
    rw [← precPairW_six, hV3, writeWindow_apply]
    simp only [pairVals]
    simp [hw0, hw1]
  have r3_17 : V3 (precSelf af ag 17) = V (precSelf af ag 11) := by
    rw [← precPairW_one, hV3, writeWindow_apply]
    simp only [pairVals]
    simp [hw1]
  have out3 : ∀ (i : Fin 32), (∀ t : Fin 8, 16 + (t : ℕ) ≠ (i : ℕ)) →
      V3 (precSelf af ag i) = V (precSelf af ag i) := by
    intro i hi
    have h16 : (i : ℕ) ≠ 16 := by have := hi 0; simp at this ⊢; omega
    have h17 : (i : ℕ) ≠ 17 := by have := hi 1; simp at this ⊢; omega
    rw [hV3, runChild_frame _ _ _ (fun t => precPairW_ne_self t i (hi t)),
      hV2, Function.update_of_ne (precSelf_ne_self i 17 h17),
      hV1, Function.update_of_ne (precSelf_ne_self i 16 h16)]
  -- S4: pair slot 1 := that
  have h4 := copyIntoTM_hoareTime (R (precSelf af ag 22)) (R (precSelf af ag 17))
      (Regs.ne R (precSelf_ne_self 22 17 (by decide)))
      (V3 (precSelf af ag 22)) (V3 (precSelf af ag 17))
      inp₀ (regsWork R w₀ V3) ys hinp₀ (fun i _ => hpv V3 i)
      (regsWork_apply R w₀ V3 _) (regsWork_apply R w₀ V3 _)
  rw [regsWork_update] at h4
  replace h4 := h4.mono_bound
    (copyIntoTime_le_arith _ _ B (Nat.le_of_lt (b3 _)) (Nat.le_of_lt (b3 _)))
  set V4 := Function.update V3 (precSelf af ag 17) (V3 (precSelf af ag 22)) with hV4
  have b4 : ∀ k, V4 k < B := by
    intro k; rw [hV4]; simp only [Function.update_apply]; split_ifs <;> exact b3 _
  -- S5: pair slot 0 := a
  have h5 := copyIntoTM_hoareTime (R (precSelf af ag 6)) (R (precSelf af ag 16))
      (Regs.ne R (precSelf_ne_self 6 16 (by decide)))
      (V4 (precSelf af ag 6)) (V4 (precSelf af ag 16))
      inp₀ (regsWork R w₀ V4) ys hinp₀ (fun i _ => hpv V4 i)
      (regsWork_apply R w₀ V4 _) (regsWork_apply R w₀ V4 _)
  rw [regsWork_update] at h5
  replace h5 := h5.mono_bound
    (copyIntoTime_le_arith _ _ B (Nat.le_of_lt (b4 _)) (Nat.le_of_lt (b4 _)))
  set V5 := Function.update V4 (precSelf af ag 16) (V4 (precSelf af ag 6)) with hV5
  have b5 : ∀ k, V5 k < B := by
    intro k; rw [hV5]; simp only [Function.update_apply]; split_ifs <;> exact b4 _
  have r5_w0 : V5 ((precPairW af ag) 0) = V (precSelf af ag 6) := by
    rw [precPairW_zero, hV5, Function.update_self, hV4,
      Function.update_of_ne (precSelf_ne_self 6 17 (by decide))]
    exact out3 6 (by intro t; have := t.isLt; simp; omega)
  have r5_w1 : V5 ((precPairW af ag) 1)
      = Nat.pair (V (precSelf af ag 9)) (V (precSelf af ag 11)) := by
    rw [precPairW_one, hV5, Function.update_of_ne (precSelf_ne_self 17 16 (by decide)),
      hV4, Function.update_self, r3_22]
  -- S6: pair a (pair j acc)
  have h6 := runChild (precPairW af ag) R (pairTM ((precPairW af ag).trans R)) pairVals
      (evalnArithmeticCost B) B w₀ hpark V5 b5
      (fun Wb u hp hu => pairTM_hoareTime_arith _ u B inp₀ Wb ys hinp₀ hp
        (fun k => Nat.le_of_lt (hu k)))
  set V6 := writeWindow (precPairW af ag) V5
      (pairVals (fun i => V5 ((precPairW af ag) i))) with hV6
  have b6 : ∀ k, V6 k < B := by
    intro k; rw [hV6]
    refine writeWindow_bounded _ _ _ B b5 (fun i => ?_) k
    refine pairVals_lt _ B hB2 (fun i => b5 _) ?_ i
    rw [r5_w0, r5_w1]; exact hp2
  have r6_22 : V6 (precSelf af ag 22)
      = Nat.pair (V (precSelf af ag 6))
          (Nat.pair (V (precSelf af ag 9)) (V (precSelf af ag 11))) := by
    rw [← precPairW_six, hV6, writeWindow_apply]
    simp only [pairVals]
    simp [r5_w0, r5_w1]
  have out6 : ∀ (i : Fin 32), (∀ t : Fin 8, 16 + (t : ℕ) ≠ (i : ℕ)) →
      V6 (precSelf af ag i) = V (precSelf af ag i) := by
    intro i hi
    have h16 : (i : ℕ) ≠ 16 := by have := hi 0; simp at this ⊢; omega
    have h17 : (i : ℕ) ≠ 17 := by have := hi 1; simp at this ⊢; omega
    rw [hV6, runChild_frame _ _ _ (fun t => precPairW_ne_self t i (hi t)),
      hV5, Function.update_of_ne (precSelf_ne_self i 16 h16),
      hV4, Function.update_of_ne (precSelf_ne_self i 17 h17)]
    exact out3 i hi
  -- S7: j := j + 1
  have h7 := incRegTM_hoareTime (R (precSelf af ag 9)) (V6 (precSelf af ag 9)) inp₀
      (regsWork R w₀ V6) ys hinp₀ (fun i _ => hpv V6 i) (regsWork_apply R w₀ V6 _)
  rw [regsWork_update] at h7
  replace h7 := h7.mono_bound (regOpTime_le_arith _ B (Nat.le_of_lt (b6 _)))
  set V7 := Function.update V6 (precSelf af ag 9) (V6 (precSelf af ag 9) + 1) with hV7
  have b7 : ∀ k, V7 k < B := by
    intro k; rw [hV7]; simp only [Function.update_apply]; split_ifs
    · rw [out6 9 (by intro t; have := t.isLt; simp; omega)]; exact hj1
    · exact b6 _
  -- S8: curFuel := curFuel + 1
  have h8 := incRegTM_hoareTime (R (precSelf af ag 12)) (V7 (precSelf af ag 12)) inp₀
      (regsWork R w₀ V7) ys hinp₀ (fun i _ => hpv V7 i) (regsWork_apply R w₀ V7 _)
  rw [regsWork_update] at h8
  replace h8 := h8.mono_bound (regOpTime_le_arith _ B (Nat.le_of_lt (b7 _)))
  set V8 := Function.update V7 (precSelf af ag 12) (V7 (precSelf af ag 12) + 1) with hV8
  have b8 : ∀ k, V8 k < B := by
    intro k; rw [hV8]; simp only [Function.update_apply]; split_ifs
    · rw [hV7, Function.update_of_ne (precSelf_ne_self 12 9 (by decide)),
        out6 12 (by intro t; have := t.isLt; simp; omega)]
      exact hf1
    · exact b7 _
  -- S9: cg.input := the reconstructed pair
  have h9 := copyIntoTM_hoareTime (R (precSelf af ag 22)) (R (precRightLoc af ag hag 0))
      (Regs.ne R (precSelf_ne_rightLoc hag haf 22 0))
      (V8 (precSelf af ag 22)) (V8 (precRightLoc af ag hag 0))
      inp₀ (regsWork R w₀ V8) ys hinp₀ (fun i _ => hpv V8 i)
      (regsWork_apply R w₀ V8 _) (regsWork_apply R w₀ V8 _)
  rw [regsWork_update] at h9
  replace h9 := h9.mono_bound
    (copyIntoTime_le_arith _ _ B (Nat.le_of_lt (b8 _)) (Nat.le_of_lt (b8 _)))
  set V9 := Function.update V8 (precRightLoc af ag hag 0) (V8 (precSelf af ag 22))
    with hV9
  have b9 : ∀ k, V9 k < B := by
    intro k; rw [hV9]; simp only [Function.update_apply]; split_ifs <;> exact b8 _
  -- S10: cg.fuel := curFuel
  have h10 := copyIntoTM_hoareTime (R (precSelf af ag 12)) (R (precRightLoc af ag hag 1))
      (Regs.ne R (precSelf_ne_rightLoc hag haf 12 1))
      (V9 (precSelf af ag 12)) (V9 (precRightLoc af ag hag 1))
      inp₀ (regsWork R w₀ V9) ys hinp₀ (fun i _ => hpv V9 i)
      (regsWork_apply R w₀ V9 _) (regsWork_apply R w₀ V9 _)
  rw [regsWork_update] at h10
  replace h10 := h10.mono_bound
    (copyIntoTime_le_arith _ _ B (Nat.le_of_lt (b9 _)) (Nat.le_of_lt (b9 _)))
  set V10 := Function.update V9 (precRightLoc af ag hag 1) (V9 (precSelf af ag 12))
    with hV10
  have b10 : ∀ k, V10 k < B := by
    intro k; rw [hV10]; simp only [Function.update_apply]; split_ifs <;> exact b9 _
  -- S11: run cg
  have h11 := runChild (precRightSub af ag) R Mg Fg tg B w₀ hpark V10 b10 hMg
  set V11 := writeWindow (precRightSub af ag) V10
      (Fg (fun i => V10 ((precRightSub af ag) i))) with hV11
  have b11 : ∀ k, V11 k < B := by
    intro k; rw [hV11]
    exact writeWindow_bounded _ _ _ B b10 (fun i => hFgB _ (fun t => b10 _) i) k
  have outR : ∀ (i : Fin 32), V11 (precSelf af ag i) = V10 (precSelf af ag i) := by
    intro i
    rw [hV11, runChild_frame _ _ _ (fun t => precRightSub_ne_self haf t i)]
  have r11_tag : V11 (precRightLoc af ag hag 2)
      = Fg (fun i => V10 ((precRightSub af ag) i)) ⟨2, by omega⟩ := by
    rw [precRightLoc_eq, hV11, writeWindow_apply]
    congr 1
  have r11_val : V11 (precRightLoc af ag hag 3)
      = Fg (fun i => V10 ((precRightSub af ag) i)) ⟨3, by omega⟩ := by
    rw [precRightLoc_eq, hV11, writeWindow_apply]
    congr 1
  have hAlive11 : V11 (precSelf af ag 10) ≤ 1 := by
    rw [outR 10, hV10, Function.update_of_ne (precSelf_ne_rightLoc hag haf 10 1),
      hV9, Function.update_of_ne (precSelf_ne_rightLoc hag haf 10 0),
      hV8, Function.update_of_ne (precSelf_ne_self 10 12 (by decide)),
      hV7, Function.update_of_ne (precSelf_ne_self 10 9 (by decide)),
      out6 10 (by intro t; have := t.isLt; simp; omega)]
    exact halive
  have hTag11 : V11 (precRightLoc af ag hag 2) ≤ 1 := by
    rw [r11_tag]; exact hFgTag _
  -- S12: clear the mask temp
  have h12 := clearRegTM_hoareTime (R (precSelf af ag 13)) (V11 (precSelf af ag 13)) inp₀
      (regsWork R w₀ V11) ys hinp₀ (fun i _ => hpv V11 i) (regsWork_apply R w₀ V11 _)
  rw [regsWork_update] at h12
  replace h12 := h12.mono_bound (regOpTime_le_arith _ B (Nat.le_of_lt (b11 _)))
  set V12 := Function.update V11 (precSelf af ag 13) 0 with hV12
  have b12 : ∀ k, V12 k < B := by
    intro k; rw [hV12]; simp only [Function.update_apply]; split_ifs
    · omega
    · exact b11 _
  have hAlive12 : V12 (precSelf af ag 10) ≤ 1 := by
    rw [hV12, Function.update_of_ne (precSelf_ne_self 10 13 (by decide))]; exact hAlive11
  have hTag12 : V12 (precRightLoc af ag hag 2) ≤ 1 := by
    rw [hV12, Function.update_of_ne (Ne.symm (precSelf_ne_rightLoc hag haf 13 2))]
    exact hTag11
  -- S13: temp := alive * cg.tag
  have h13 := mulAddIntoTM_hoareTime (R (precSelf af ag 10)) (R (precRightLoc af ag hag 2))
      (R (precSelf af ag 13))
      (Regs.ne R (precSelf_ne_rightLoc hag haf 10 2))
      (Regs.ne R (precSelf_ne_self 10 13 (by decide)))
      (Regs.ne R (Ne.symm (precSelf_ne_rightLoc hag haf 13 2)))
      (V12 (precSelf af ag 10)) (V12 (precRightLoc af ag hag 2)) 0
      inp₀ (regsWork R w₀ V12) ys hinp₀ (fun i _ => hpv V12 i)
      (regsWork_apply R w₀ V12 _) (regsWork_apply R w₀ V12 _)
      (by rw [regsWork_apply, hV12, Function.update_self])
  rw [regsWork_update] at h13
  replace h13 := h13.mono_bound
    (mulAddTime_le_arith _ _ 0 B (Nat.le_of_lt (b12 _)) (Nat.le_of_lt (b12 _)) (by omega))
  set V13 := Function.update V12 (precSelf af ag 13)
      (0 + V12 (precSelf af ag 10) * V12 (precRightLoc af ag hag 2)) with hV13
  have hMask13 : V13 (precSelf af ag 13) ≤ 1 := by
    rw [hV13, Function.update_self]
    calc 0 + V12 (precSelf af ag 10) * V12 (precRightLoc af ag hag 2)
        ≤ 1 * 1 := by simpa using Nat.mul_le_mul hAlive12 hTag12
      _ = 1 := by norm_num
  have b13 : ∀ k, V13 k < B := by
    intro k; rw [hV13]; simp only [Function.update_apply]; split_ifs
    · have h := hMask13; rw [hV13, Function.update_self] at h; omega
    · exact b12 _
  -- S14: alive := temp
  have h14 := copyIntoTM_hoareTime (R (precSelf af ag 13)) (R (precSelf af ag 10))
      (Regs.ne R (precSelf_ne_self 13 10 (by decide)))
      (V13 (precSelf af ag 13)) (V13 (precSelf af ag 10))
      inp₀ (regsWork R w₀ V13) ys hinp₀ (fun i _ => hpv V13 i)
      (regsWork_apply R w₀ V13 _) (regsWork_apply R w₀ V13 _)
  rw [regsWork_update] at h14
  replace h14 := h14.mono_bound
    (copyIntoTime_le_arith _ _ B (Nat.le_of_lt (b13 _)) (Nat.le_of_lt (b13 _)))
  set V14 := Function.update V13 (precSelf af ag 10) (V13 (precSelf af ag 13)) with hV14
  have b14 : ∀ k, V14 k < B := by
    intro k; rw [hV14]; simp only [Function.update_apply]; split_ifs <;> exact b13 _
  have hAlive14 : V14 (precSelf af ag 10) ≤ 1 := by
    rw [hV14, Function.update_self]; exact hMask13
  -- S15: clear acc
  have h15 := clearRegTM_hoareTime (R (precSelf af ag 11)) (V14 (precSelf af ag 11)) inp₀
      (regsWork R w₀ V14) ys hinp₀ (fun i _ => hpv V14 i) (regsWork_apply R w₀ V14 _)
  rw [regsWork_update] at h15
  replace h15 := h15.mono_bound (regOpTime_le_arith _ B (Nat.le_of_lt (b14 _)))
  set V15 := Function.update V14 (precSelf af ag 11) 0 with hV15
  have b15 : ∀ k, V15 k < B := by
    intro k; rw [hV15]; simp only [Function.update_apply]; split_ifs
    · omega
    · exact b14 _
  have hAlive15 : V15 (precSelf af ag 10) ≤ 1 := by
    rw [hV15, Function.update_of_ne (precSelf_ne_self 10 11 (by decide))]; exact hAlive14
  -- S16: acc := alive * cg.value
  have h16 := mulAddIntoTM_hoareTime (R (precSelf af ag 10)) (R (precRightLoc af ag hag 3))
      (R (precSelf af ag 11))
      (Regs.ne R (precSelf_ne_rightLoc hag haf 10 3))
      (Regs.ne R (precSelf_ne_self 10 11 (by decide)))
      (Regs.ne R (Ne.symm (precSelf_ne_rightLoc hag haf 11 3)))
      (V15 (precSelf af ag 10)) (V15 (precRightLoc af ag hag 3)) 0
      inp₀ (regsWork R w₀ V15) ys hinp₀ (fun i _ => hpv V15 i)
      (regsWork_apply R w₀ V15 _) (regsWork_apply R w₀ V15 _)
      (by rw [regsWork_apply, hV15, Function.update_self])
  rw [regsWork_update] at h16
  replace h16 := h16.mono_bound
    (mulAddTime_le_arith _ _ 0 B (Nat.le_of_lt (b15 _)) (Nat.le_of_lt (b15 _)) (by omega))
  exact (seqEmit hinp₀ (hpv V1) h1 <|
    seqEmit hinp₀ (hpv V2) h2 <|
    seqEmit hinp₀ (hpv V3) h3 <|
    seqEmit hinp₀ (hpv V4) h4 <|
    seqEmit hinp₀ (hpv V5) h5 <|
    seqEmit hinp₀ (hpv V6) h6 <|
    seqEmit hinp₀ (hpv V7) h7 <|
    seqEmit hinp₀ (hpv V8) h8 <|
    seqEmit hinp₀ (hpv V9) h9 <|
    seqEmit hinp₀ (hpv V10) h10 <|
    seqEmit hinp₀ (hpv V11) h11 <|
    seqEmit hinp₀ (hpv V12) h12 <|
    seqEmit hinp₀ (hpv V13) h13 <|
    seqEmit hinp₀ (hpv V14) h14 <|
    seqEmit hinp₀ (hpv V15) h15 h16).mono_bound (by omega)

end PrecBodyProof

/-! ### `prec`: one level, semantically

`cf` is setup-only; the body invokes `cg` alone, on `Nat.pair a (Nat.pair j acc)` at fuel
`curFuel + 1`, and folds its answer into `alive` and `acc` multiplicatively. -/

section PrecLevelSem
variable {af ag : ℕ}

lemma precBodyPre_pairOut (haf : 16 ≤ af) (hag : 16 ≤ ag) (V : Fin (32 + af + ag) → ℕ) :
    precBodyPre af ag haf hag V (precSelf af ag 22)
      = Nat.pair (V (precSelf af ag 6))
          (Nat.pair (V (precSelf af ag 9)) (V (precSelf af ag 11))) := by
  simp only [precBodyPre, precSelf_update_apply, precSelf_rightLoc_upd hag haf,
    precPairWin_selfW_apply, pairVals_apply, precPairW_zero, precPairW_one]
  norm_num

lemma precBodyPre_childIn_zero (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (V : Fin (32 + af + ag) → ℕ) :
    precBodyPre af ag haf hag V (precRightLoc af ag hag 0)
      = Nat.pair (V (precSelf af ag 6))
          (Nat.pair (V (precSelf af ag 9)) (V (precSelf af ag 11))) := by
  have h := precBodyPre_pairOut haf hag V
  simp only [precBodyPre, precRightLoc_update_apply hag, precRightLoc_self_upd hag haf,
    precPairWin_rightLoc hag haf] at h ⊢
  norm_num at h ⊢
  simp only [precSelf_update_apply, precPairWin_selfW_apply, pairVals_apply,
    precPairW_zero, precPairW_one] at h ⊢
  norm_num at h ⊢

lemma precBodyPre_childIn_one (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (V : Fin (32 + af + ag) → ℕ) :
    precBodyPre af ag haf hag V (precRightLoc af ag hag 1)
      = V (precSelf af ag 12) + 1 := by
  simp only [precBodyPre, precRightLoc_update_apply hag, precRightLoc_self_upd hag haf,
    precPairWin_rightLoc hag haf]
  norm_num
  simp only [precSelf_update_apply, precPairWin_selfW_apply,
    precSelf_rightLoc_upd hag haf, precPairW_zero, precPairW_one]
  norm_num

/-- The counter and the level fuel are advanced before `cg` runs. -/
lemma precBodyPre_j (haf : 16 ≤ af) (hag : 16 ≤ ag) (V : Fin (32 + af + ag) → ℕ) :
    precBodyPre af ag haf hag V (precSelf af ag 9) = V (precSelf af ag 9) + 1 := by
  simp only [precBodyPre, precSelf_update_apply, precSelf_rightLoc_upd hag haf,
    precPairWin_selfW_apply]
  norm_num

lemma precBodyPre_fuel (haf : 16 ≤ af) (hag : 16 ≤ ag) (V : Fin (32 + af + ag) → ℕ) :
    precBodyPre af ag haf hag V (precSelf af ag 12) = V (precSelf af ag 12) + 1 := by
  simp only [precBodyPre, precSelf_update_apply, precSelf_rightLoc_upd hag haf,
    precPairWin_selfW_apply]
  norm_num

/-- Every other node register in `0`–`15` is untouched by the pre-state. -/
lemma precBodyPre_self (haf : 16 ≤ af) (hag : 16 ≤ ag) (V : Fin (32 + af + ag) → ℕ)
    (i : Fin 32) (hw : ¬ (16 ≤ (i : ℕ) ∧ (i : ℕ) < 24)) (h9 : (i : ℕ) ≠ 9)
    (h12 : (i : ℕ) ≠ 12) :
    precBodyPre af ag haf hag V (precSelf af ag i) = V (precSelf af ag i) := by
  simp only [precBodyPre, precSelf_update_apply, precSelf_rightLoc_upd hag haf,
    precPairWin_selfW_apply, dif_neg hw]
  have h16 : (i : ℕ) ≠ 16 := by omega
  have h17 : (i : ℕ) ≠ 17 := by omega
  norm_num [h9, h12, h16, h17]

/-! #### The level -/

/-- The vector `cg` is run on at this level. -/
noncomputable def precChildIn (af ag : ℕ) (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (V : Fin (32 + af + ag) → ℕ) : Fin ag → ℕ :=
  fun i => precBodyPre af ag haf hag V (precRightSub af ag i)

lemma precChildIn_zero (haf : 16 ≤ af) (hag : 16 ≤ ag) (V : Fin (32 + af + ag) → ℕ) :
    precChildIn af ag haf hag V ⟨0, by omega⟩
      = Nat.pair (V (precSelf af ag 6))
          (Nat.pair (V (precSelf af ag 9)) (V (precSelf af ag 11))) := by
  have h : precRightSub af ag ⟨0, by omega⟩ = precRightLoc af ag hag 0 := by
    apply Fin.ext; simp [precRightSub, precRightLoc, shiftEmb_val]
  rw [precChildIn, h, precBodyPre_childIn_zero]

lemma precChildIn_one (haf : 16 ≤ af) (hag : 16 ≤ ag) (V : Fin (32 + af + ag) → ℕ) :
    precChildIn af ag haf hag V ⟨1, by omega⟩ = V (precSelf af ag 12) + 1 := by
  have h : precRightSub af ag ⟨1, by omega⟩ = precRightLoc af ag hag 1 := by
    apply Fin.ext; simp [precRightSub, precRightLoc, shiftEmb_val]
  rw [precChildIn, h, precBodyPre_childIn_one]

section
variable (haf : 16 ≤ af) (hag : 16 ≤ ag) (Fg : (Fin ag → ℕ) → Fin ag → ℕ)
  (V : Fin (32 + af + ag) → ℕ)

lemma precBodyVals_a :
    precBodyVals af ag haf hag Fg V (precSelf af ag 6) = V (precSelf af ag 6) := by
  simp only [precBodyVals, precSelf_update_apply, precRightSub_win_selfW haf]
  norm_num
  exact precBodyPre_self haf hag V 6 (by norm_num) (by norm_num) (by norm_num)

lemma precBodyVals_j :
    precBodyVals af ag haf hag Fg V (precSelf af ag 9) = V (precSelf af ag 9) + 1 := by
  simp only [precBodyVals, precSelf_update_apply, precRightSub_win_selfW haf]
  norm_num
  exact precBodyPre_j haf hag V

lemma precBodyVals_fuel :
    precBodyVals af ag haf hag Fg V (precSelf af ag 12) = V (precSelf af ag 12) + 1 := by
  simp only [precBodyVals, precSelf_update_apply, precRightSub_win_selfW haf]
  norm_num
  exact precBodyPre_fuel haf hag V

lemma precBodyVals_alive :
    precBodyVals af ag haf hag Fg V (precSelf af ag 10)
      = V (precSelf af ag 10)
          * Fg (precChildIn af ag haf hag V) ⟨2, by omega⟩ := by
  simp only [precBodyVals, precSelf_update_apply, precRightSub_win_selfW haf,
    precRightLoc_self_upd hag haf, precRightSub_win_rightLoc hag]
  norm_num
  rw [precBodyPre_self haf hag V 10 (by norm_num) (by norm_num) (by norm_num)]
  rfl

lemma precBodyVals_acc :
    precBodyVals af ag haf hag Fg V (precSelf af ag 11)
      = V (precSelf af ag 10)
          * Fg (precChildIn af ag haf hag V) ⟨2, by omega⟩
          * Fg (precChildIn af ag haf hag V) ⟨3, by omega⟩ := by
  simp only [precBodyVals, precSelf_update_apply, precRightSub_win_selfW haf,
    precRightLoc_self_upd hag haf, precRightSub_win_rightLoc hag]
  norm_num
  rw [precBodyPre_self haf hag V 10 (by norm_num) (by norm_num) (by norm_num)]
  rfl

end

end PrecLevelSem

/-! ### `prec`: the loop invariant

After `i` iterations the machine's `alive` and `acc` registers hold the tag and value of
`precRunG` at level `i`, the counter holds `i`, and the level fuel holds `baseFuel + i`. -/

section PrecLoopSem
variable {af ag : ℕ}

/-- **One level.** -/
lemma precBodyVals_isLevel (haf : 16 ≤ af) (hag : 16 ≤ ag) (cg : Nat.Partrec.Code)
    (Fg : (Fin ag → ℕ) → Fin ag → ℕ) (hFg : ChildEncodes ag hag cg Fg)
    (V : Fin (32 + af + ag) → ℕ) :
    precBodyVals af ag haf hag Fg V (precSelf af ag 10)
        = V (precSelf af ag 10)
          * resultTag (Nat.Partrec.Code.evaln (V (precSelf af ag 12) + 1) cg
              (Nat.pair (V (precSelf af ag 6))
                (Nat.pair (V (precSelf af ag 9)) (V (precSelf af ag 11))))) ∧
      precBodyVals af ag haf hag Fg V (precSelf af ag 11)
        = V (precSelf af ag 10)
          * resultTag (Nat.Partrec.Code.evaln (V (precSelf af ag 12) + 1) cg
              (Nat.pair (V (precSelf af ag 6))
                (Nat.pair (V (precSelf af ag 9)) (V (precSelf af ag 11)))))
          * resultVal (Nat.Partrec.Code.evaln (V (precSelf af ag 12) + 1) cg
              (Nat.pair (V (precSelf af ag 6))
                (Nat.pair (V (precSelf af ag 9)) (V (precSelf af ag 11))))) := by
  obtain ⟨htag, hval⟩ := hFg (precChildIn af ag haf hag V)
  rw [precChildIn_zero, precChildIn_one] at htag hval
  refine ⟨?_, ?_⟩
  · rw [precBodyVals_alive, htag]
  · rw [precBodyVals_acc, htag, hval]

/-- **The loop invariant.** -/
lemma precLoopVals_spec (haf : 16 ≤ af) (hag : 16 ≤ ag) (cf cg : Nat.Partrec.Code)
    (Fg : (Fin ag → ℕ) → Fin ag → ℕ) (hFg : ChildEncodes ag hag cg Fg)
    (V₀ : Fin (32 + af + ag) → ℕ) (a f₀ : ℕ)
    (h6 : V₀ (precSelf af ag 6) = a)
    (h9 : V₀ (precSelf af ag 9) = 0)
    (h12 : V₀ (precSelf af ag 12) = f₀)
    (h10 : V₀ (precSelf af ag 10)
      = resultTag (Nat.Partrec.Code.evaln f₀ cf a))
    (h11 : V₀ (precSelf af ag 11)
      = resultVal (Nat.Partrec.Code.evaln f₀ cf a))
    (i : ℕ) :
    precLoopVals af ag haf hag Fg V₀ i (precSelf af ag 6) = a ∧
      precLoopVals af ag haf hag Fg V₀ i (precSelf af ag 9) = i ∧
      precLoopVals af ag haf hag Fg V₀ i (precSelf af ag 12) = f₀ + i ∧
      precLoopVals af ag haf hag Fg V₀ i (precSelf af ag 10)
        = resultTag (precRunG cf cg a f₀ i) ∧
      precLoopVals af ag haf hag Fg V₀ i (precSelf af ag 11)
        = resultVal (precRunG cf cg a f₀ i) := by
  induction i with
  | zero => exact ⟨h6, h9, by simpa using h12, by simpa [precRunG] using h10,
      by simpa [precRunG] using h11⟩
  | succ k ih =>
    obtain ⟨e6, e9, e12, e10, e11⟩ := ih
    obtain ⟨ha, hc⟩ := precBodyVals_isLevel haf hag cg Fg hFg
      (precLoopVals af ag haf hag Fg V₀ k)
    rw [e6, e9, e12, e10, e11] at ha hc
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [precLoopVals_succ, precBodyVals_a, e6]
    · rw [precLoopVals_succ, precBodyVals_j, e9]
    · rw [precLoopVals_succ, precBodyVals_fuel, e12]; omega
    · rw [precLoopVals_succ, ha, precRunG_succ_tag,
        show f₀ + (k + 1) = f₀ + k + 1 from (Nat.add_assoc f₀ k 1).symm]
    · rw [precLoopVals_succ, hc, precRunG_succ_val,
        show f₀ + (k + 1) = f₀ + k + 1 from (Nat.add_assoc f₀ k 1).symm]

end PrecLoopSem

/-! ### `prec`: the level keeps every register inside the bound

The `b`-chains inside `precBody_hoareTime` bound the *intermediate* states, each feeding
the next stage's cost. These are the composite facts about the level's output vector, which
is what the loop invariant needs. -/

section PrecBodyBound
variable {af ag : ℕ}

lemma precBodyPre_lt (haf : 16 ≤ af) (hag : 16 ≤ ag) (V : Fin (32 + af + ag) → ℕ) (B : ℕ)
    (hB2 : 2 ≤ B) (hV : ∀ k, V k < B)
    (hj1 : V (precSelf af ag 9) + 1 < B) (hf1 : V (precSelf af ag 12) + 1 < B)
    (hp1 : Nat.pair (V (precSelf af ag 9)) (V (precSelf af ag 11)) < B)
    (hp2 : Nat.pair (V (precSelf af ag 6))
      (Nat.pair (V (precSelf af ag 9)) (V (precSelf af ag 11))) < B) :
    ∀ k, precBodyPre af ag haf hag V k < B := by
  intro k
  simp only [precBodyPre]
  set V1 := Function.update V (precSelf af ag 16) (V (precSelf af ag 9)) with hV1
  have b1 : ∀ k, V1 k < B := by
    intro k; rw [hV1]; simp only [Function.update_apply]; split_ifs <;> exact hV _
  set V2 := Function.update V1 (precSelf af ag 17) (V1 (precSelf af ag 11)) with hV2
  have b2 : ∀ k, V2 k < B := by
    intro k; rw [hV2]; simp only [Function.update_apply]; split_ifs <;> exact b1 _
  have hw0 : V2 ((precPairW af ag) 0) = V (precSelf af ag 9) := by
    rw [precPairW_zero, hV2, precSelf_update_apply, hV1, precSelf_update_apply]; norm_num
  have hw1 : V2 ((precPairW af ag) 1) = V (precSelf af ag 11) := by
    rw [precPairW_one, hV2, precSelf_update_apply, hV1, precSelf_update_apply]; norm_num
  set V3 := writeWindow (precPairW af ag) V2
      (pairVals (fun i => V2 ((precPairW af ag) i))) with hV3
  have b3 : ∀ k, V3 k < B := by
    intro k; rw [hV3]
    refine writeWindow_bounded _ _ _ B b2 (fun i => ?_) k
    refine pairVals_lt _ B hB2 (fun i => b2 _) ?_ i
    rw [hw0, hw1]; exact hp1
  have r3_22 : V3 (precSelf af ag 22)
      = Nat.pair (V (precSelf af ag 9)) (V (precSelf af ag 11)) := by
    rw [← precPairW_six, hV3, writeWindow_apply]
    simp only [pairVals]
    simp [hw0, hw1]
  set V4 := Function.update V3 (precSelf af ag 17) (V3 (precSelf af ag 22)) with hV4
  have b4 : ∀ k, V4 k < B := by
    intro k; rw [hV4]; simp only [Function.update_apply]; split_ifs <;> exact b3 _
  set V5 := Function.update V4 (precSelf af ag 16) (V4 (precSelf af ag 6)) with hV5
  have b5 : ∀ k, V5 k < B := by
    intro k; rw [hV5]; simp only [Function.update_apply]; split_ifs <;> exact b4 _
  have r5_w0 : V5 ((precPairW af ag) 0) = V (precSelf af ag 6) := by
    rw [precPairW_zero, hV5, Function.update_self, hV4,
      Function.update_of_ne (precSelf_ne_self 6 17 (by decide)), hV3,
      writeWindow_of_ne _ _ _ (fun t => precPairW_ne_self t 6 (by
        have := t.isLt; simp; omega)),
      hV2, Function.update_of_ne (precSelf_ne_self 6 17 (by decide)),
      hV1, Function.update_of_ne (precSelf_ne_self 6 16 (by decide))]
  have r5_w1 : V5 ((precPairW af ag) 1)
      = Nat.pair (V (precSelf af ag 9)) (V (precSelf af ag 11)) := by
    rw [precPairW_one, hV5,
      Function.update_of_ne (precSelf_ne_self 17 16 (by decide)),
      hV4, Function.update_self, r3_22]
  set V6 := writeWindow (precPairW af ag) V5
      (pairVals (fun i => V5 ((precPairW af ag) i))) with hV6
  have b6 : ∀ k, V6 k < B := by
    intro k; rw [hV6]
    refine writeWindow_bounded _ _ _ B b5 (fun i => ?_) k
    refine pairVals_lt _ B hB2 (fun i => b5 _) ?_ i
    rw [r5_w0, r5_w1]; exact hp2
  have out6 : ∀ (i : Fin 32), (∀ t : Fin 8, 16 + (t : ℕ) ≠ (i : ℕ)) →
      V6 (precSelf af ag i) = V (precSelf af ag i) := by
    intro i hi
    have h16 : (i : ℕ) ≠ 16 := by have := hi 0; simp at this ⊢; omega
    have h17 : (i : ℕ) ≠ 17 := by have := hi 1; simp at this ⊢; omega
    rw [hV6, writeWindow_of_ne _ _ _ (fun t => precPairW_ne_self t i (hi t)),
      hV5, Function.update_of_ne (precSelf_ne_self i 16 h16),
      hV4, Function.update_of_ne (precSelf_ne_self i 17 h17),
      hV3, writeWindow_of_ne _ _ _ (fun t => precPairW_ne_self t i (hi t)),
      hV2, Function.update_of_ne (precSelf_ne_self i 17 h17),
      hV1, Function.update_of_ne (precSelf_ne_self i 16 h16)]
  set V7 := Function.update V6 (precSelf af ag 9) (V6 (precSelf af ag 9) + 1) with hV7
  have b7 : ∀ k, V7 k < B := by
    intro k; rw [hV7]; simp only [Function.update_apply]; split_ifs
    · rw [out6 9 (by intro t; have := t.isLt; simp; omega)]; exact hj1
    · exact b6 _
  set V8 := Function.update V7 (precSelf af ag 12) (V7 (precSelf af ag 12) + 1) with hV8
  have b8 : ∀ k, V8 k < B := by
    intro k; rw [hV8]; simp only [Function.update_apply]; split_ifs
    · rw [hV7, Function.update_of_ne (precSelf_ne_self 12 9 (by decide)),
        out6 12 (by intro t; have := t.isLt; simp; omega)]
      exact hf1
    · exact b7 _
  set V9 := Function.update V8 (precRightLoc af ag hag 0) (V8 (precSelf af ag 22))
    with hV9
  have b9 : ∀ k, V9 k < B := by
    intro k; rw [hV9]; simp only [Function.update_apply]; split_ifs <;> exact b8 _
  simp only [Function.update_apply]
  split_ifs <;> exact b9 _

lemma precBodyVals_lt (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (Fg : (Fin ag → ℕ) → Fin ag → ℕ) (V : Fin (32 + af + ag) → ℕ) (B : ℕ)
    (hB2 : 2 ≤ B) (hV : ∀ k, V k < B)
    (halive : V (precSelf af ag 10) ≤ 1)
    (hj1 : V (precSelf af ag 9) + 1 < B) (hf1 : V (precSelf af ag 12) + 1 < B)
    (hp1 : Nat.pair (V (precSelf af ag 9)) (V (precSelf af ag 11)) < B)
    (hp2 : Nat.pair (V (precSelf af ag 6))
      (Nat.pair (V (precSelf af ag 9)) (V (precSelf af ag 11))) < B)
    (hFgB : ∀ u : Fin ag → ℕ, (∀ k, u k < B) → ∀ k, Fg u k < B)
    (hFgTag : ∀ u : Fin ag → ℕ, Fg u ⟨2, by omega⟩ ≤ 1) :
    ∀ k, precBodyVals af ag haf hag Fg V k < B := by
  have bpre := precBodyPre_lt haf hag V B hB2 hV hj1 hf1 hp1 hp2
  have halive' : precBodyPre af ag haf hag V (precSelf af ag 10) ≤ 1 := by
    rw [precBodyPre_self haf hag V 10 (by norm_num) (by norm_num) (by norm_num)]
    exact halive
  intro k
  simp only [precBodyVals]
  set V11 := writeWindow (precRightSub af ag) (precBodyPre af ag haf hag V)
      (Fg (fun i => precBodyPre af ag haf hag V ((precRightSub af ag) i))) with hV11
  have b11 : ∀ k, V11 k < B := by
    intro k; rw [hV11]
    exact writeWindow_bounded _ _ _ B bpre (fun i => hFgB _ (fun t => bpre _) i) k
  have r11_10 : V11 (precSelf af ag 10) ≤ 1 := by
    rw [hV11, precRightSub_win_selfW haf]; exact halive'
  have r11_tag : V11 (precRightLoc af ag hag 2) ≤ 1 := by
    rw [hV11, precRightSub_win_rightLoc hag]
    exact hFgTag _
  set V12 := Function.update V11 (precSelf af ag 13) 0 with hV12
  have b12 : ∀ k, V12 k < B := by
    intro k; rw [hV12]; simp only [Function.update_apply]; split_ifs
    · omega
    · exact b11 _
  have r12_10 : V12 (precSelf af ag 10) ≤ 1 := by
    rw [hV12, precSelf_update_apply]; norm_num; exact r11_10
  have r12_tag : V12 (precRightLoc af ag hag 2) ≤ 1 := by
    rw [hV12, precRightLoc_self_upd hag haf]; exact r11_tag
  set V13 := Function.update V12 (precSelf af ag 13)
      (0 + V12 (precSelf af ag 10) * V12 (precRightLoc af ag hag 2)) with hV13
  have m13 : V13 (precSelf af ag 13) ≤ 1 := by
    rw [hV13, Function.update_self]
    calc 0 + V12 (precSelf af ag 10) * V12 (precRightLoc af ag hag 2)
        ≤ 1 * 1 := by simpa using Nat.mul_le_mul r12_10 r12_tag
      _ = 1 := by norm_num
  have b13 : ∀ k, V13 k < B := by
    intro k; rw [hV13]; simp only [Function.update_apply]; split_ifs
    · have h := m13; rw [hV13, Function.update_self] at h; omega
    · exact b12 _
  set V14 := Function.update V13 (precSelf af ag 10) (V13 (precSelf af ag 13)) with hV14
  have b14 : ∀ k, V14 k < B := by
    intro k; rw [hV14]; simp only [Function.update_apply]; split_ifs <;> exact b13 _
  have m14 : V14 (precSelf af ag 10) ≤ 1 := by
    rw [hV14, Function.update_self]; exact m13
  set V15 := Function.update V14 (precSelf af ag 11) 0 with hV15
  have b15 : ∀ k, V15 k < B := by
    intro k; rw [hV15]; simp only [Function.update_apply]; split_ifs
    · omega
    · exact b14 _
  have m15 : V15 (precSelf af ag 10) ≤ 1 := by
    rw [hV15, precSelf_update_apply]; norm_num; exact m14
  simp only [Function.update_apply]
  split_ifs
  · have hb := b15 (precRightLoc af ag hag 3)
    calc 0 + V15 (precSelf af ag 10) * V15 (precRightLoc af ag hag 3)
        ≤ 1 * V15 (precRightLoc af ag hag 3) := by
          simpa using Nat.mul_le_mul m15 (le_refl (V15 (precRightLoc af ag hag 3)))
      _ < B := by omega
  · exact b15 _

end PrecBodyBound

/-! ## A register-block loop

`forRegTM` driven by a counter register that the block does not name. The body's
obligation is then exactly its ordinary `regsWork` specification: `regsWork_update_of_ne`
absorbs the loop's mid-iteration cursor tape into the ambient state, which is what that
lemma exists for. Generic in the register block — a candidate for upstreaming. -/

section RegsLoop

lemma forRegs_hoareTime {A : ℕ} (R : Regs A n) (body : TM n) (l : Fin n)
    (hl : ∀ k, R k ≠ l) (m b : ℕ) (V : ℕ → Fin A → ℕ)
    (inp₀ : Tape) (w₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hpark : ∀ i, Parked (w₀ i)) (hw₀l : w₀ l = regTape m)
    (hbody : ∀ i, i < m → ∀ (w : Fin n → Tape), (∀ j, Parked (w j)) →
      body.HoareTime (EmitPred inp₀ (regsWork R w (V i)) ys)
                     (EmitPred inp₀ (regsWork R w (V (i + 1))) ys) b) :
    (forRegTM body l).HoareTime
      (EmitPred inp₀ (regsWork R w₀ (V 0)) ys)
      (EmitPred inp₀ (regsWork R w₀ (V m)) ys)
      (m * (b + 2) + (m + 2)) := by
  refine forRegTM_hoareTime body l m inp₀ (fun i => regsWork R w₀ (V i)) (fun _ => ys) b
    hinp₀ (fun i => by rw [regsWork_of_ne _ _ _ hl]; exact hw₀l)
    (fun i j _ => parked_regsWork R hpark _ j) ?_
  intro i hi
  have hpk : ∀ j, Parked (Function.update w₀ l (⟨i + 2, regCells m⟩ : Tape) j) := by
    intro j
    by_cases hj : j = l
    · subst hj; rw [Function.update_self]; exact parked_regCells (by omega)
    · rw [Function.update_of_ne hj]; exact hpark j
  have h := hbody i hi _ hpk
  rw [regsWork_update_of_ne R w₀ (V i) hl, regsWork_update_of_ne R w₀ (V (i + 1)) hl] at h
  exact h

end RegsLoop

/-! ## `prec`: the loop

The node's block is thirty-three plus its two subtrees: the extra register is the loop
counter, and it sits **outside** the thirty-two the body names, so `forRegs_hoareTime`
applies with no re-indexing. -/

section PrecLoop
variable {af ag : ℕ}

/-- The thirty-two-plus-subtrees block the body works over. -/
def precMain (af ag : ℕ) : Fin (32 + af + ag) ↪ Fin (33 + af + ag) := shiftEmb 0 (by omega)

/-- The loop counter, the one register outside that block. -/
def precLoopIdx (af ag : ℕ) : Fin (33 + af + ag) := ⟨32 + af + ag, by omega⟩

lemma precMain_ne_loopIdx (k : Fin (32 + af + ag)) :
    precMain af ag k ≠ precLoopIdx af ag := by
  apply Fin.ne_of_val_ne
  have := k.isLt
  simp [precMain, precLoopIdx, shiftEmb_val]
  omega

/-- The body's side conditions, at one loop state. -/
def PrecBodyOK (af ag B : ℕ) (V : Fin (32 + af + ag) → ℕ) : Prop :=
  (∀ k, V k < B) ∧ V (precSelf af ag 10) ≤ 1 ∧
    V (precSelf af ag 9) + 1 < B ∧ V (precSelf af ag 12) + 1 < B ∧
    Nat.pair (V (precSelf af ag 9)) (V (precSelf af ag 11)) < B ∧
    Nat.pair (V (precSelf af ag 6))
      (Nat.pair (V (precSelf af ag 9)) (V (precSelf af ag 11))) < B

/-- **The `prec` loop.** `m` iterations of `precBodyTM`, off a counter the body's block
    does not name. -/
lemma precLoop_hoareTime (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (R : Regs (32 + af + ag) n) (l : Fin n) (hl : ∀ k, R k ≠ l) (Mg : TM n)
    (Fg : (Fin ag → ℕ) → Fin ag → ℕ) (tg B m : ℕ)
    (V₀ : Fin (32 + af + ag) → ℕ)
    (inp₀ : Tape) (w₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hpark : ∀ i, Parked (w₀ i)) (hB2 : 2 ≤ B)
    (hw₀l : w₀ l = regTape m)
    (hFgB : ∀ u : Fin ag → ℕ, (∀ k, u k < B) → ∀ k, Fg u k < B)
    (hFgTag : ∀ u : Fin ag → ℕ, Fg u ⟨2, by omega⟩ ≤ 1)
    (hOK : ∀ i, i < m → PrecBodyOK af ag B (precLoopVals af ag haf hag Fg V₀ i))
    (hMg : ∀ (Wb : Fin n → Tape) (u : Fin ag → ℕ), (∀ i, Parked (Wb i)) → (∀ k, u k < B) →
      Mg.HoareTime
        (EmitPred inp₀ (regsWork ((precRightSub af ag).trans R) Wb u) ys)
        (EmitPred inp₀ (regsWork ((precRightSub af ag).trans R) Wb (Fg u)) ys) tg) :
    (forRegTM (precBodyTM af ag haf hag R Mg) l).HoareTime
      (EmitPred inp₀ (regsWork R w₀ V₀) ys)
      (EmitPred inp₀ (regsWork R w₀ (precLoopVals af ag haf hag Fg V₀ m)) ys)
      (m * ((15 * evalnArithmeticCost B + tg + 15) + 2) + (m + 2)) := by
  refine forRegs_hoareTime R (precBodyTM af ag haf hag R Mg) l hl
    m (15 * evalnArithmeticCost B + tg + 15)
    (precLoopVals af ag haf hag Fg V₀) inp₀ w₀ ys hinp₀ hpark hw₀l ?_
  intro i hi w hw
  obtain ⟨hb, halive, hj1, hf1, hp1, hp2⟩ := hOK i hi
  rw [precLoopVals_succ]
  exact precBody_hoareTime haf hag R Mg Fg tg
    (precLoopVals af ag haf hag Fg V₀ i) B inp₀ w ys hinp₀ hw hB2 hb hFgB hFgTag
    halive hj1 hf1 hp1 hp2 hMg

end PrecLoop

section PrecBridge
variable {af ag : ℕ}

/-- **The block boundary.** A parent sees a `prec` node as one thirty-three-plus-subtrees
    register block; the node itself works over the thirty-two-plus-subtrees block its body
    names, with the loop counter as an *ambient* register outside it. The two views agree:
    the counter's value moves from the vector into the ambient tape family. -/
lemma regsWork_precMain (R : Regs (33 + af + ag) n) (w₀ : Fin n → Tape)
    (W : Fin (33 + af + ag) → ℕ) :
    regsWork R w₀ W
      = regsWork ((precMain af ag).trans R)
          (Function.update w₀ (R (precLoopIdx af ag)) (regTape (W (precLoopIdx af ag))))
          (fun k => W (precMain af ag k)) := by
  have hmain : ∀ k : Fin (32 + af + ag), (precMain af ag k : ℕ) = (k : ℕ) := by
    intro k; simp [precMain, shiftEmb_val]
  have hne : ∀ k : Fin (32 + af + ag),
      ((precMain af ag).trans R) k ≠ R (precLoopIdx af ag) := by
    intro k h
    exact precMain_ne_loopIdx k (R.injective h)
  funext j
  by_cases h : ∃ k : Fin (33 + af + ag), R k = j
  · obtain ⟨k, rfl⟩ := h
    rw [regsWork_apply]
    by_cases hk : (k : ℕ) = 32 + af + ag
    · have hkl : k = precLoopIdx af ag := Fin.ext (by simpa [precLoopIdx] using hk)
      subst hkl
      rw [regsWork_of_ne _ _ _ hne, Function.update_self]
    · have hlt : (k : ℕ) < 32 + af + ag := by have := k.isLt; omega
      have hid : precMain af ag ⟨(k : ℕ), hlt⟩ = k := Fin.ext (by rw [hmain])
      have hk' : ((precMain af ag).trans R) ⟨(k : ℕ), hlt⟩ = R k := by
        show R (precMain af ag ⟨(k : ℕ), hlt⟩) = R k
        rw [hid]
      rw [← hk', regsWork_apply, hid]
  · have h' : ∀ k : Fin (32 + af + ag), ((precMain af ag).trans R) k ≠ j :=
      fun k e => h ⟨precMain af ag k, e⟩
    have hjl : j ≠ R (precLoopIdx af ag) := fun e => h ⟨precLoopIdx af ag, e.symm⟩
    rw [regsWork_of_ne _ _ _ (fun k e => h ⟨k, e⟩), regsWork_of_ne _ _ _ h',
      Function.update_of_ne hjl]

end PrecBridge

/-! ## `prec`: the setup phase

Unpair the input into `a` and `m`, form the base fuel `fuel - m`, run `cf` on `a` at that
fuel, and seed the loop registers — `j := 0`, `alive := cf`'s tag, `acc := cf`'s value,
`curFuel := baseFuel` — finishing by copying `m` into the loop counter, which is the one
register outside the block. -/

section PrecSetup
variable {af ag : ℕ}

def precSetupTM (af ag : ℕ) (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (R : Regs (32 + af + ag) n) (l : Fin n) (Mf : TM n) : TM n :=
  seqTM (unpairTM ((precUnpairW af ag).trans R) (R (precSelf af ag 0))) <|
  seqTM (copyIntoTM (R (precSelf af ag 16)) (R (precSelf af ag 6))) <|
  seqTM (copyIntoTM (R (precSelf af ag 17)) (R (precSelf af ag 7))) <|
  seqTM (copyIntoTM (R (precSelf af ag 1)) (R (precSelf af ag 8))) <|
  seqTM (subIntoTM (R (precSelf af ag 7)) (R (precSelf af ag 8))) <|
  seqTM (copyIntoTM (R (precSelf af ag 6)) (R (precLeftLoc af ag haf 0))) <|
  seqTM (copyIntoTM (R (precSelf af ag 8)) (R (precLeftLoc af ag haf 1))) <|
  seqTM Mf <|
  seqTM (clearRegTM (R (precSelf af ag 9))) <|
  seqTM (copyIntoTM (R (precLeftLoc af ag haf 2)) (R (precSelf af ag 10))) <|
  seqTM (copyIntoTM (R (precLeftLoc af ag haf 3)) (R (precSelf af ag 11))) <|
  seqTM (copyIntoTM (R (precSelf af ag 8)) (R (precSelf af ag 12)))
        (copyIntoTM (R (precSelf af ag 7)) l)

/-- The state the setup hands `cf`: the unpaired `a` in `cf`'s input register and the base
    fuel `fuel - m` in its fuel register. -/
noncomputable def precSetupPre (af ag : ℕ) (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (V : Fin (32 + af + ag) → ℕ) : Fin (32 + af + ag) → ℕ :=
  let U1 := writeWindow (precUnpairW af ag) V
              (unpairVals (fun j => V (precUnpairW af ag j)) (V (precSelf af ag 0)))
  let U2 := Function.update U1 (precSelf af ag 6) (U1 (precSelf af ag 16))
  let U3 := Function.update U2 (precSelf af ag 7) (U2 (precSelf af ag 17))
  let U4 := Function.update U3 (precSelf af ag 8) (U3 (precSelf af ag 1))
  let U5 := Function.update U4 (precSelf af ag 8)
              (U4 (precSelf af ag 8) - U4 (precSelf af ag 7))
  let U6 := Function.update U5 (precLeftLoc af ag haf 0) (U5 (precSelf af ag 6))
  Function.update U6 (precLeftLoc af ag haf 1) (U6 (precSelf af ag 8))

/-- The register vector the setup produces. The loop counter is *not* part of it: it lives
    outside the block, and the last stage writes it into the ambient tape family. -/
noncomputable def precSetupVals (af ag : ℕ) (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (Ff : (Fin af → ℕ) → Fin af → ℕ) (V : Fin (32 + af + ag) → ℕ) :
    Fin (32 + af + ag) → ℕ :=
  let U7 := precSetupPre af ag haf hag V
  let U8 := writeWindow (precLeftSub af ag) U7 (Ff (fun i => U7 (precLeftSub af ag i)))
  let U9 := Function.update U8 (precSelf af ag 9) 0
  let U10 := Function.update U9 (precSelf af ag 10) (U9 (precLeftLoc af ag haf 2))
  let U11 := Function.update U10 (precSelf af ag 11) (U10 (precLeftLoc af ag haf 3))
  Function.update U11 (precSelf af ag 12) (U11 (precSelf af ag 8))

set_option maxHeartbeats 1000000 in
/-- **`precSetupTM` Hoare specification.** -/
lemma precSetup_hoareTime (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (R : Regs (32 + af + ag) n) (l : Fin n) (hl : ∀ k, R k ≠ l) (Mf : TM n)
    (Ff : (Fin af → ℕ) → Fin af → ℕ) (tf : ℕ)
    (V : Fin (32 + af + ag) → ℕ) (B : ℕ)
    (inp₀ : Tape) (w₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hpark : ∀ i, Parked (w₀ i))
    (cl : ℕ) (hlc : w₀ l = regTape cl) (hclB : cl ≤ B)
    (hV : ∀ k, V k < B)
    (hFfB : ∀ u : Fin af → ℕ, (∀ k, u k < B) → ∀ k, Ff u k < B)
    (hMf : ∀ (Wb : Fin n → Tape) (u : Fin af → ℕ), (∀ i, Parked (Wb i)) → (∀ k, u k < B) →
      Mf.HoareTime (EmitPred inp₀ (regsWork ((precLeftSub af ag).trans R) Wb u) ys)
                   (EmitPred inp₀ (regsWork ((precLeftSub af ag).trans R) Wb (Ff u)) ys) tf) :
    (precSetupTM af ag haf hag R l Mf).HoareTime
      (EmitPred inp₀ (regsWork R w₀ V) ys)
      (EmitPred inp₀
        (regsWork R
          (Function.update w₀ l
            (regTape (precSetupVals af ag haf hag Ff V (precSelf af ag 7))))
          (precSetupVals af ag haf hag Ff V)) ys)
      (12 * evalnArithmeticCost B + tf + 12) := by
  have hpv := parked_regsWork R hpark
  have hle : ∀ k, V k ≤ B := fun k => Nat.le_of_lt (hV k)
  have hB0 : 0 < B := Nat.lt_of_le_of_lt (Nat.zero_le _) (hV (precSelf af ag 0))
  -- S1: unpair the input
  have h1 := unpairTM_hoareTime_arith ((precUnpairW af ag).trans R) (R (precSelf af ag 0))
      (fun k h => precUnpairW_ne_self k 0 (by have := k.isLt; omega) (R.injective h))
      (fun j => V (precUnpairW af ag j)) (V (precSelf af ag 0)) B inp₀
      (regsWork R w₀ V) ys hinp₀ (hpv V)
      (regsWork_apply R w₀ V _) (hle _) (fun k => hle _)
  rw [← regsWork_restrict, regsWork_window] at h1
  set V1 := writeWindow (precUnpairW af ag) V
      (unpairVals (fun j => V (precUnpairW af ag j)) (V (precSelf af ag 0))) with hV1
  have b1 : ∀ k, V1 k < B := by
    intro k; rw [hV1]
    refine writeWindow_bounded _ _ _ B hV (fun j => ?_) k
    have := unpairVals_bounded (fun j => V (precUnpairW af ag j)) (B - 1)
      (fun i => by have := hV (precUnpairW af ag i); omega) (V (precSelf af ag 0))
      (by have := hV (precSelf af ag 0); omega) j
    omega
  have out1 : ∀ (i : Fin 32), (∀ t : Fin 9, 16 + (t : ℕ) ≠ (i : ℕ)) →
      V1 (precSelf af ag i) = V (precSelf af ag i) := by
    intro i hi
    rw [hV1, writeWindow_of_ne _ _ _ (fun t => precUnpairW_ne_self t i (hi t))]
  have r1_16 : V1 (precSelf af ag 16) = (Nat.unpair (V (precSelf af ag 0))).1 := by
    rw [← precUnpairW_zero, hV1, writeWindow_apply, unpairVals_zero]
  have r1_17 : V1 (precSelf af ag 17) = (Nat.unpair (V (precSelf af ag 0))).2 := by
    rw [← precUnpairW_one, hV1, writeWindow_apply, unpairVals_one]
  -- S2: a := (unpair inp).1
  have h2 := copyIntoTM_hoareTime (R (precSelf af ag 16)) (R (precSelf af ag 6))
      (Regs.ne R (precSelf_ne_self 16 6 (by decide)))
      (V1 (precSelf af ag 16)) (V1 (precSelf af ag 6))
      inp₀ (regsWork R w₀ V1) ys hinp₀ (fun i _ => hpv V1 i)
      (regsWork_apply R w₀ V1 _) (regsWork_apply R w₀ V1 _)
  rw [regsWork_update] at h2
  replace h2 := h2.mono_bound
    (copyIntoTime_le_arith _ _ B (Nat.le_of_lt (b1 _)) (Nat.le_of_lt (b1 _)))
  set V2 := Function.update V1 (precSelf af ag 6) (V1 (precSelf af ag 16)) with hV2
  have b2 : ∀ k, V2 k < B := by
    intro k; rw [hV2]; simp only [Function.update_apply]; split_ifs <;> exact b1 _
  -- S3: m := (unpair inp).2
  have h3 := copyIntoTM_hoareTime (R (precSelf af ag 17)) (R (precSelf af ag 7))
      (Regs.ne R (precSelf_ne_self 17 7 (by decide)))
      (V2 (precSelf af ag 17)) (V2 (precSelf af ag 7))
      inp₀ (regsWork R w₀ V2) ys hinp₀ (fun i _ => hpv V2 i)
      (regsWork_apply R w₀ V2 _) (regsWork_apply R w₀ V2 _)
  rw [regsWork_update] at h3
  replace h3 := h3.mono_bound
    (copyIntoTime_le_arith _ _ B (Nat.le_of_lt (b2 _)) (Nat.le_of_lt (b2 _)))
  set V3 := Function.update V2 (precSelf af ag 7) (V2 (precSelf af ag 17)) with hV3
  have b3 : ∀ k, V3 k < B := by
    intro k; rw [hV3]; simp only [Function.update_apply]; split_ifs <;> exact b2 _
  -- S4: baseFuel := fuel
  have h4 := copyIntoTM_hoareTime (R (precSelf af ag 1)) (R (precSelf af ag 8))
      (Regs.ne R (precSelf_ne_self 1 8 (by decide)))
      (V3 (precSelf af ag 1)) (V3 (precSelf af ag 8))
      inp₀ (regsWork R w₀ V3) ys hinp₀ (fun i _ => hpv V3 i)
      (regsWork_apply R w₀ V3 _) (regsWork_apply R w₀ V3 _)
  rw [regsWork_update] at h4
  replace h4 := h4.mono_bound
    (copyIntoTime_le_arith _ _ B (Nat.le_of_lt (b3 _)) (Nat.le_of_lt (b3 _)))
  set V4 := Function.update V3 (precSelf af ag 8) (V3 (precSelf af ag 1)) with hV4
  have b4 : ∀ k, V4 k < B := by
    intro k; rw [hV4]; simp only [Function.update_apply]; split_ifs <;> exact b3 _
  -- S5: baseFuel := fuel - m
  have h5 := subIntoTM_hoareTime (R (precSelf af ag 7)) (R (precSelf af ag 8))
      (Regs.ne R (precSelf_ne_self 7 8 (by decide)))
      (V4 (precSelf af ag 7)) (V4 (precSelf af ag 8))
      inp₀ (regsWork R w₀ V4) ys hinp₀ (fun i _ => hpv V4 i)
      (regsWork_apply R w₀ V4 _) (regsWork_apply R w₀ V4 _)
  rw [regsWork_update] at h5
  replace h5 := h5.mono_bound
    (subIntoTime_le_arith _ _ B (Nat.le_of_lt (b4 _)) (Nat.le_of_lt (b4 _)))
  set V5 := Function.update V4 (precSelf af ag 8)
      (V4 (precSelf af ag 8) - V4 (precSelf af ag 7)) with hV5
  have b5 : ∀ k, V5 k < B := by
    intro k; rw [hV5]; simp only [Function.update_apply]; split_ifs
    · have := b4 (precSelf af ag 8); omega
    · exact b4 _
  -- S6: cf.input := a
  have h6 := copyIntoTM_hoareTime (R (precSelf af ag 6)) (R (precLeftLoc af ag haf 0))
      (Regs.ne R (precSelf_ne_leftLoc haf 6 0))
      (V5 (precSelf af ag 6)) (V5 (precLeftLoc af ag haf 0))
      inp₀ (regsWork R w₀ V5) ys hinp₀ (fun i _ => hpv V5 i)
      (regsWork_apply R w₀ V5 _) (regsWork_apply R w₀ V5 _)
  rw [regsWork_update] at h6
  replace h6 := h6.mono_bound
    (copyIntoTime_le_arith _ _ B (Nat.le_of_lt (b5 _)) (Nat.le_of_lt (b5 _)))
  set V6 := Function.update V5 (precLeftLoc af ag haf 0) (V5 (precSelf af ag 6)) with hV6
  have b6 : ∀ k, V6 k < B := by
    intro k; rw [hV6]; simp only [Function.update_apply]; split_ifs <;> exact b5 _
  -- S7: cf.fuel := baseFuel
  have h7 := copyIntoTM_hoareTime (R (precSelf af ag 8)) (R (precLeftLoc af ag haf 1))
      (Regs.ne R (precSelf_ne_leftLoc haf 8 1))
      (V6 (precSelf af ag 8)) (V6 (precLeftLoc af ag haf 1))
      inp₀ (regsWork R w₀ V6) ys hinp₀ (fun i _ => hpv V6 i)
      (regsWork_apply R w₀ V6 _) (regsWork_apply R w₀ V6 _)
  rw [regsWork_update] at h7
  replace h7 := h7.mono_bound
    (copyIntoTime_le_arith _ _ B (Nat.le_of_lt (b6 _)) (Nat.le_of_lt (b6 _)))
  set V7 := Function.update V6 (precLeftLoc af ag haf 1) (V6 (precSelf af ag 8)) with hV7
  have b7 : ∀ k, V7 k < B := by
    intro k; rw [hV7]; simp only [Function.update_apply]; split_ifs <;> exact b6 _
  -- S8: run cf
  have h8 := runChild (precLeftSub af ag) R Mf Ff tf B w₀ hpark V7 b7 hMf
  set V8 := writeWindow (precLeftSub af ag) V7
      (Ff (fun i => V7 (precLeftSub af ag i))) with hV8
  have b8 : ∀ k, V8 k < B := by
    intro k; rw [hV8]
    exact writeWindow_bounded _ _ _ B b7 (fun i => hFfB _ (fun t => b7 _) i) k
  -- S9: j := 0
  have h9 := clearRegTM_hoareTime (R (precSelf af ag 9)) (V8 (precSelf af ag 9)) inp₀
      (regsWork R w₀ V8) ys hinp₀ (fun i _ => hpv V8 i) (regsWork_apply R w₀ V8 _)
  rw [regsWork_update] at h9
  replace h9 := h9.mono_bound (regOpTime_le_arith _ B (Nat.le_of_lt (b8 _)))
  set V9 := Function.update V8 (precSelf af ag 9) 0 with hV9
  have b9 : ∀ k, V9 k < B := by
    intro k; rw [hV9]; simp only [Function.update_apply]; split_ifs
    · exact hB0
    · exact b8 _
  -- S10: alive := cf's tag
  have h10 := copyIntoTM_hoareTime (R (precLeftLoc af ag haf 2)) (R (precSelf af ag 10))
      (Regs.ne R (Ne.symm (precSelf_ne_leftLoc haf 10 2)))
      (V9 (precLeftLoc af ag haf 2)) (V9 (precSelf af ag 10))
      inp₀ (regsWork R w₀ V9) ys hinp₀ (fun i _ => hpv V9 i)
      (regsWork_apply R w₀ V9 _) (regsWork_apply R w₀ V9 _)
  rw [regsWork_update] at h10
  replace h10 := h10.mono_bound
    (copyIntoTime_le_arith _ _ B (Nat.le_of_lt (b9 _)) (Nat.le_of_lt (b9 _)))
  set V10 := Function.update V9 (precSelf af ag 10) (V9 (precLeftLoc af ag haf 2)) with hV10
  have b10 : ∀ k, V10 k < B := by
    intro k; rw [hV10]; simp only [Function.update_apply]; split_ifs <;> exact b9 _
  -- S11: acc := cf's value
  have h11 := copyIntoTM_hoareTime (R (precLeftLoc af ag haf 3)) (R (precSelf af ag 11))
      (Regs.ne R (Ne.symm (precSelf_ne_leftLoc haf 11 3)))
      (V10 (precLeftLoc af ag haf 3)) (V10 (precSelf af ag 11))
      inp₀ (regsWork R w₀ V10) ys hinp₀ (fun i _ => hpv V10 i)
      (regsWork_apply R w₀ V10 _) (regsWork_apply R w₀ V10 _)
  rw [regsWork_update] at h11
  replace h11 := h11.mono_bound
    (copyIntoTime_le_arith _ _ B (Nat.le_of_lt (b10 _)) (Nat.le_of_lt (b10 _)))
  set V11 := Function.update V10 (precSelf af ag 11) (V10 (precLeftLoc af ag haf 3))
    with hV11
  have b11 : ∀ k, V11 k < B := by
    intro k; rw [hV11]; simp only [Function.update_apply]; split_ifs <;> exact b10 _
  -- S12: curFuel := baseFuel
  have h12 := copyIntoTM_hoareTime (R (precSelf af ag 8)) (R (precSelf af ag 12))
      (Regs.ne R (precSelf_ne_self 8 12 (by decide)))
      (V11 (precSelf af ag 8)) (V11 (precSelf af ag 12))
      inp₀ (regsWork R w₀ V11) ys hinp₀ (fun i _ => hpv V11 i)
      (regsWork_apply R w₀ V11 _) (regsWork_apply R w₀ V11 _)
  rw [regsWork_update] at h12
  replace h12 := h12.mono_bound
    (copyIntoTime_le_arith _ _ B (Nat.le_of_lt (b11 _)) (Nat.le_of_lt (b11 _)))
  set V12 := Function.update V11 (precSelf af ag 12) (V11 (precSelf af ag 8)) with hV12
  have b12 : ∀ k, V12 k < B := by
    intro k; rw [hV12]; simp only [Function.update_apply]; split_ifs <;> exact b11 _
  -- S13: the loop counter, an ambient register outside the block
  have h13 := copyIntoTM_hoareTime (R (precSelf af ag 7)) l (hl _)
      (V12 (precSelf af ag 7)) cl
      inp₀ (regsWork R w₀ V12) ys hinp₀ (fun i _ => hpv V12 i)
      (regsWork_apply R w₀ V12 _)
      (by rw [regsWork_of_ne _ _ _ hl]; exact hlc)
  rw [← regsWork_update_of_ne R w₀ V12 hl] at h13
  replace h13 := h13.mono_bound
    (copyIntoTime_le_arith _ cl B (Nat.le_of_lt (b12 _)) hclB)
  exact (seqEmit hinp₀ (hpv V1) h1 <|
    seqEmit hinp₀ (hpv V2) h2 <|
    seqEmit hinp₀ (hpv V3) h3 <|
    seqEmit hinp₀ (hpv V4) h4 <|
    seqEmit hinp₀ (hpv V5) h5 <|
    seqEmit hinp₀ (hpv V6) h6 <|
    seqEmit hinp₀ (hpv V7) h7 <|
    seqEmit hinp₀ (hpv V8) h8 <|
    seqEmit hinp₀ (hpv V9) h9 <|
    seqEmit hinp₀ (hpv V10) h10 <|
    seqEmit hinp₀ (hpv V11) h11 <|
    seqEmit hinp₀ (hpv V12) h12 h13).mono_bound (by omega)

end PrecSetup

/-! ## `prec`: the finish phase

The outer guard, then the two masks. `alive` has already absorbed `cf`'s tag and every
level's tag, so this is one masking level shorter than `comp`'s. -/

section PrecFinish
variable {af ag : ℕ}

def precFinishTM (af ag : ℕ) (R : Regs (32 + af + ag) n) : TM n :=
  seqTM (ltFlagTM (R (precSelf af ag 0)) (R (precSelf af ag 1))
          (R (precSelf af ag 5)) (R (precSelf af ag 4))) <|
  seqTM (clearRegTM (R (precSelf af ag 2))) <|
  seqTM (mulAddIntoTM (R (precSelf af ag 4)) (R (precSelf af ag 10))
          (R (precSelf af ag 2))) <|
  seqTM (clearRegTM (R (precSelf af ag 3)))
        (mulAddIntoTM (R (precSelf af ag 2)) (R (precSelf af ag 11)) (R (precSelf af ag 3)))

noncomputable def precFinishVals (af ag : ℕ) (W : Fin (32 + af + ag) → ℕ) :
    Fin (32 + af + ag) → ℕ :=
  let W1 := Function.update W (precSelf af ag 5) (W (precSelf af ag 1) - W (precSelf af ag 0))
  let W2 := Function.update W1 (precSelf af ag 4)
              (if W (precSelf af ag 0) < W (precSelf af ag 1) then 1 else 0)
  let W3 := Function.update W2 (precSelf af ag 2) 0
  let W4 := Function.update W3 (precSelf af ag 2)
              (0 + W3 (precSelf af ag 4) * W3 (precSelf af ag 10))
  let W5 := Function.update W4 (precSelf af ag 3) 0
  Function.update W5 (precSelf af ag 3)
    (0 + W5 (precSelf af ag 2) * W5 (precSelf af ag 11))

set_option maxHeartbeats 1000000 in
lemma precFinish_hoareTime (R : Regs (32 + af + ag) n) (W : Fin (32 + af + ag) → ℕ) (B : ℕ)
    (inp₀ : Tape) (w₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hpark : ∀ i, Parked (w₀ i)) (hW : ∀ k, W k < B)
    (halive : W (precSelf af ag 10) ≤ 1) :
    (precFinishTM af ag R).HoareTime
      (EmitPred inp₀ (regsWork R w₀ W) ys)
      (EmitPred inp₀ (regsWork R w₀ (precFinishVals af ag W)) ys)
      (5 * evalnArithmeticCost B + 4) := by
  have hpv := parked_regsWork R hpark
  have hle : ∀ k, W k ≤ B := fun k => Nat.le_of_lt (hW k)
  -- S1: the outer guard
  have h1 := ltFlagTM_hoareTime (R (precSelf af ag 0)) (R (precSelf af ag 1))
      (R (precSelf af ag 5)) (R (precSelf af ag 4))
      (Regs.ne R (precSelf_ne_self 0 5 (by decide)))
      (Regs.ne R (precSelf_ne_self 1 5 (by decide)))
      (Regs.ne R (precSelf_ne_self 5 4 (by decide)))
      (W (precSelf af ag 0)) (W (precSelf af ag 1)) (W (precSelf af ag 5))
      (W (precSelf af ag 4))
      inp₀ (regsWork R w₀ W) ys hinp₀ (fun i => hpv W i)
      (regsWork_apply R w₀ W _) (regsWork_apply R w₀ W _)
      (regsWork_apply R w₀ W _) (regsWork_apply R w₀ W _)
  rw [regsWork_update, regsWork_update] at h1
  replace h1 := h1.mono_bound
    (ltFlagTime_le_arith _ _ _ _ B (hle _) (hle _) (hle _) (hle _))
  set W2 := Function.update
      (Function.update W (precSelf af ag 5) (W (precSelf af ag 1) - W (precSelf af ag 0)))
      (precSelf af ag 4) (if W (precSelf af ag 0) < W (precSelf af ag 1) then 1 else 0)
    with hW2
  have b2 : ∀ k, W2 k < B := by
    intro k; rw [hW2]; simp only [Function.update_apply]
    split_ifs <;> first
      | (have := hW (precSelf af ag 1); omega)
      | (have := hW (precSelf af ag 0); omega)
      | exact hW _
  have r2_4 : W2 (precSelf af ag 4)
      = (if W (precSelf af ag 0) < W (precSelf af ag 1) then 1 else 0) := by
    rw [hW2, Function.update_self]
  have r2_10 : W2 (precSelf af ag 10) = W (precSelf af ag 10) := by
    rw [hW2, Function.update_of_ne (precSelf_ne_self 10 4 (by decide)),
      Function.update_of_ne (precSelf_ne_self 10 5 (by decide))]
  -- S2: clear the tag
  have h2 := clearRegTM_hoareTime (R (precSelf af ag 2)) (W2 (precSelf af ag 2)) inp₀
      (regsWork R w₀ W2) ys hinp₀ (fun i _ => hpv W2 i) (regsWork_apply R w₀ W2 _)
  rw [regsWork_update] at h2
  replace h2 := h2.mono_bound (regOpTime_le_arith _ B (Nat.le_of_lt (b2 _)))
  set W3 := Function.update W2 (precSelf af ag 2) 0 with hW3
  have b3 : ∀ k, W3 k < B := by
    intro k; rw [hW3]; simp only [Function.update_apply]; split_ifs
    · have := hW (precSelf af ag 0); omega
    · exact b2 _
  have hflag3 : W3 (precSelf af ag 4) ≤ 1 := by
    rw [hW3, Function.update_of_ne (precSelf_ne_self 4 2 (by decide)), r2_4]
    split_ifs <;> omega
  have r3_10 : W3 (precSelf af ag 10) = W (precSelf af ag 10) := by
    rw [hW3, Function.update_of_ne (precSelf_ne_self 10 2 (by decide)), r2_10]
  -- S3: tag := gflag * alive
  have h3 := mulAddIntoTM_hoareTime (R (precSelf af ag 4)) (R (precSelf af ag 10))
      (R (precSelf af ag 2))
      (Regs.ne R (precSelf_ne_self 4 10 (by decide)))
      (Regs.ne R (precSelf_ne_self 4 2 (by decide)))
      (Regs.ne R (precSelf_ne_self 10 2 (by decide)))
      (W3 (precSelf af ag 4)) (W3 (precSelf af ag 10)) 0
      inp₀ (regsWork R w₀ W3) ys hinp₀ (fun i _ => hpv W3 i)
      (regsWork_apply R w₀ W3 _) (regsWork_apply R w₀ W3 _)
      (by rw [regsWork_apply, hW3, Function.update_self])
  rw [regsWork_update] at h3
  replace h3 := h3.mono_bound
    (mulAddTime_le_arith _ _ 0 B (Nat.le_of_lt (b3 _)) (Nat.le_of_lt (b3 _)) (by omega))
  set W4 := Function.update W3 (precSelf af ag 2)
      (0 + W3 (precSelf af ag 4) * W3 (precSelf af ag 10)) with hW4
  have hmask4 : W4 (precSelf af ag 2) ≤ 1 := by
    rw [hW4, Function.update_self, r3_10]
    calc 0 + W3 (precSelf af ag 4) * W (precSelf af ag 10)
        ≤ 1 * 1 := by simpa using Nat.mul_le_mul hflag3 halive
      _ = 1 := by norm_num
  have b4 : ∀ k, W4 k < B := by
    intro k; rw [hW4]; simp only [Function.update_apply]; split_ifs
    · have hb := b3 (precSelf af ag 10)
      calc 0 + W3 (precSelf af ag 4) * W3 (precSelf af ag 10)
          ≤ 1 * W3 (precSelf af ag 10) := by
            simpa using Nat.mul_le_mul hflag3 (le_refl (W3 (precSelf af ag 10)))
        _ < B := by omega
    · exact b3 _
  -- S4: clear the value
  have h4 := clearRegTM_hoareTime (R (precSelf af ag 3)) (W4 (precSelf af ag 3)) inp₀
      (regsWork R w₀ W4) ys hinp₀ (fun i _ => hpv W4 i) (regsWork_apply R w₀ W4 _)
  rw [regsWork_update] at h4
  replace h4 := h4.mono_bound (regOpTime_le_arith _ B (Nat.le_of_lt (b4 _)))
  set W5 := Function.update W4 (precSelf af ag 3) 0 with hW5
  have b5 : ∀ k, W5 k < B := by
    intro k; rw [hW5]; simp only [Function.update_apply]; split_ifs
    · have := hW (precSelf af ag 0); omega
    · exact b4 _
  -- S5: value := tag * acc
  have h5 := mulAddIntoTM_hoareTime (R (precSelf af ag 2)) (R (precSelf af ag 11))
      (R (precSelf af ag 3))
      (Regs.ne R (precSelf_ne_self 2 11 (by decide)))
      (Regs.ne R (precSelf_ne_self 2 3 (by decide)))
      (Regs.ne R (precSelf_ne_self 11 3 (by decide)))
      (W5 (precSelf af ag 2)) (W5 (precSelf af ag 11)) 0
      inp₀ (regsWork R w₀ W5) ys hinp₀ (fun i _ => hpv W5 i)
      (regsWork_apply R w₀ W5 _) (regsWork_apply R w₀ W5 _)
      (by rw [regsWork_apply, hW5, Function.update_self])
  rw [regsWork_update] at h5
  replace h5 := h5.mono_bound
    (mulAddTime_le_arith _ _ 0 B (Nat.le_of_lt (b5 _)) (Nat.le_of_lt (b5 _)) (by omega))
  exact (seqEmit hinp₀ (hpv W2) h1 <|
    seqEmit hinp₀ (hpv W3) h2 <|
    seqEmit hinp₀ (hpv W4) h3 <|
    seqEmit hinp₀ (hpv W5) h4 h5).mono_bound (by omega)

end PrecFinish

/-! ### `prec`: the setup and finish, read off, and the node's semantics -/

section PrecCloseSem
variable {af ag : ℕ}

/-- The body writes the pair window, `9`–`13`, and `cg`'s subtree; nothing else. -/
lemma precBodyVals_self (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (Fg : (Fin ag → ℕ) → Fin ag → ℕ) (V : Fin (32 + af + ag) → ℕ) (i : Fin 32)
    (hw : ¬ (16 ≤ (i : ℕ) ∧ (i : ℕ) < 24)) (h9 : ¬ (9 ≤ (i : ℕ) ∧ (i : ℕ) ≤ 13)) :
    precBodyVals af ag haf hag Fg V (precSelf af ag i) = V (precSelf af ag i) := by
  have e9 : (i : ℕ) ≠ 9 := by omega
  have e10 : (i : ℕ) ≠ 10 := by omega
  have e11 : (i : ℕ) ≠ 11 := by omega
  have e12 : (i : ℕ) ≠ 12 := by omega
  have e13 : (i : ℕ) ≠ 13 := by omega
  simp only [precBodyVals, precSelf_update_apply, precRightSub_win_selfW haf]
  norm_num [e10, e11, e13]
  exact precBodyPre_self haf hag V i hw e9 e12

lemma precLoopVals_frame (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (Fg : (Fin ag → ℕ) → Fin ag → ℕ) (V₀ : Fin (32 + af + ag) → ℕ) (i : Fin 32)
    (hw : ¬ (16 ≤ (i : ℕ) ∧ (i : ℕ) < 24)) (h9 : ¬ (9 ≤ (i : ℕ) ∧ (i : ℕ) ≤ 13)) :
    ∀ t, precLoopVals af ag haf hag Fg V₀ t (precSelf af ag i)
      = V₀ (precSelf af ag i) := by
  intro t
  induction t with
  | zero => rfl
  | succ k ih => rw [precLoopVals_succ, precBodyVals_self haf hag Fg _ i hw h9, ih]

/-! #### The setup -/

/-- The vector `cf` is run on in the setup: the unpaired `a` and the base fuel. -/
noncomputable def precBaseIn (af ag : ℕ) (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (V : Fin (32 + af + ag) → ℕ) : Fin af → ℕ :=
  fun i => precSetupPre af ag haf hag V (precLeftSub af ag i)

lemma precSetupPre_a (haf : 16 ≤ af) (hag : 16 ≤ ag) (V : Fin (32 + af + ag) → ℕ) :
    precSetupPre af ag haf hag V (precSelf af ag 6)
      = (Nat.unpair (V (precSelf af ag 0))).1 := by
  simp only [precSetupPre, precSelf_update_apply, precSelf_leftLoc_upd haf,
    precUnpairWin_selfW_apply]
  norm_num
  exact unpairVals_zero _ _

lemma precSetupPre_m (haf : 16 ≤ af) (hag : 16 ≤ ag) (V : Fin (32 + af + ag) → ℕ) :
    precSetupPre af ag haf hag V (precSelf af ag 7)
      = (Nat.unpair (V (precSelf af ag 0))).2 := by
  simp only [precSetupPre, precSelf_update_apply, precSelf_leftLoc_upd haf,
    precUnpairWin_selfW_apply]
  norm_num
  exact unpairVals_one _ _

lemma precSetupPre_base (haf : 16 ≤ af) (hag : 16 ≤ ag) (V : Fin (32 + af + ag) → ℕ) :
    precSetupPre af ag haf hag V (precSelf af ag 8)
      = V (precSelf af ag 1) - (Nat.unpair (V (precSelf af ag 0))).2 := by
  simp only [precSetupPre, precSelf_update_apply, precSelf_leftLoc_upd haf,
    precUnpairWin_selfW_apply]
  norm_num
  rw [unpairVals_one]

lemma precSetupPre_self (haf : 16 ≤ af) (hag : 16 ≤ ag) (V : Fin (32 + af + ag) → ℕ)
    (i : Fin 32) (hw : ¬ (16 ≤ (i : ℕ) ∧ (i : ℕ) < 25)) (h6 : (i : ℕ) ≠ 6)
    (h7 : (i : ℕ) ≠ 7) (h8 : (i : ℕ) ≠ 8) :
    precSetupPre af ag haf hag V (precSelf af ag i) = V (precSelf af ag i) := by
  simp only [precSetupPre, precSelf_update_apply, precSelf_leftLoc_upd haf,
    precUnpairWin_selfW_apply, dif_neg hw]
  norm_num [h6, h7, h8]

lemma precSetupPre_childIn_zero (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (V : Fin (32 + af + ag) → ℕ) :
    precSetupPre af ag haf hag V (precLeftLoc af ag haf 0)
      = (Nat.unpair (V (precSelf af ag 0))).1 := by
  have h := precSetupPre_a haf hag V
  simp only [precSetupPre, precLeftLoc_update_apply haf, precLeftLoc_self_upd haf,
    precUnpairWin_leftLoc haf] at h ⊢
  norm_num at h ⊢
  simp only [precSelf_update_apply, precUnpairWin_selfW_apply] at h ⊢
  norm_num at h ⊢
  exact h

lemma precSetupPre_childIn_one (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (V : Fin (32 + af + ag) → ℕ) :
    precSetupPre af ag haf hag V (precLeftLoc af ag haf 1)
      = V (precSelf af ag 1) - (Nat.unpair (V (precSelf af ag 0))).2 := by
  have h := precSetupPre_base haf hag V
  simp only [precSetupPre, precLeftLoc_update_apply haf, precLeftLoc_self_upd haf,
    precUnpairWin_leftLoc haf] at h ⊢
  norm_num at h ⊢
  simp only [precSelf_update_apply, precUnpairWin_selfW_apply] at h ⊢
  norm_num at h ⊢
  exact h

lemma precBaseIn_zero (haf : 16 ≤ af) (hag : 16 ≤ ag) (V : Fin (32 + af + ag) → ℕ) :
    precBaseIn af ag haf hag V ⟨0, by omega⟩
      = (Nat.unpair (V (precSelf af ag 0))).1 := by
  have h : precLeftSub af ag ⟨0, by omega⟩ = precLeftLoc af ag haf 0 := by
    apply Fin.ext; simp [precLeftSub, precLeftLoc, shiftEmb_val]
  rw [precBaseIn, h, precSetupPre_childIn_zero]

lemma precBaseIn_one (haf : 16 ≤ af) (hag : 16 ≤ ag) (V : Fin (32 + af + ag) → ℕ) :
    precBaseIn af ag haf hag V ⟨1, by omega⟩
      = V (precSelf af ag 1) - (Nat.unpair (V (precSelf af ag 0))).2 := by
  have h : precLeftSub af ag ⟨1, by omega⟩ = precLeftLoc af ag haf 1 := by
    apply Fin.ext; simp [precLeftSub, precLeftLoc, shiftEmb_val]
  rw [precBaseIn, h, precSetupPre_childIn_one]

section
variable (haf : 16 ≤ af) (hag : 16 ≤ ag) (Ff : (Fin af → ℕ) → Fin af → ℕ)
  (V : Fin (32 + af + ag) → ℕ)

lemma precSetupVals_self (i : Fin 32) (hw : ¬ (16 ≤ (i : ℕ) ∧ (i : ℕ) < 25))
    (h6 : (i : ℕ) ≠ 6) (h7 : (i : ℕ) ≠ 7) (h8 : (i : ℕ) ≠ 8)
    (h9 : ¬ (9 ≤ (i : ℕ) ∧ (i : ℕ) ≤ 12)) :
    precSetupVals af ag haf hag Ff V (precSelf af ag i) = V (precSelf af ag i) := by
  have e9 : (i : ℕ) ≠ 9 := by omega
  have e10 : (i : ℕ) ≠ 10 := by omega
  have e11 : (i : ℕ) ≠ 11 := by omega
  have e12 : (i : ℕ) ≠ 12 := by omega
  simp only [precSetupVals, precSelf_update_apply, precLeftSub_win_selfW]
  norm_num [e9, e10, e11, e12]
  exact precSetupPre_self haf hag V i hw h6 h7 h8

lemma precSetupVals_a :
    precSetupVals af ag haf hag Ff V (precSelf af ag 6)
      = (Nat.unpair (V (precSelf af ag 0))).1 := by
  simp only [precSetupVals, precSelf_update_apply, precLeftSub_win_selfW]
  norm_num
  exact precSetupPre_a haf hag V

lemma precSetupVals_m :
    precSetupVals af ag haf hag Ff V (precSelf af ag 7)
      = (Nat.unpair (V (precSelf af ag 0))).2 := by
  simp only [precSetupVals, precSelf_update_apply, precLeftSub_win_selfW]
  norm_num
  exact precSetupPre_m haf hag V

lemma precSetupVals_base :
    precSetupVals af ag haf hag Ff V (precSelf af ag 8)
      = V (precSelf af ag 1) - (Nat.unpair (V (precSelf af ag 0))).2 := by
  simp only [precSetupVals, precSelf_update_apply, precLeftSub_win_selfW]
  norm_num
  exact precSetupPre_base haf hag V

lemma precSetupVals_j : precSetupVals af ag haf hag Ff V (precSelf af ag 9) = 0 := by
  simp only [precSetupVals, precSelf_update_apply]
  norm_num

lemma precSetupVals_curFuel :
    precSetupVals af ag haf hag Ff V (precSelf af ag 12)
      = V (precSelf af ag 1) - (Nat.unpair (V (precSelf af ag 0))).2 := by
  simp only [precSetupVals, precSelf_update_apply, precLeftSub_win_selfW]
  norm_num
  exact precSetupPre_base haf hag V

lemma precSetupVals_alive :
    precSetupVals af ag haf hag Ff V (precSelf af ag 10)
      = Ff (precBaseIn af ag haf hag V) ⟨2, by omega⟩ := by
  simp only [precSetupVals, precSelf_update_apply, precLeftLoc_self_upd haf,
    precLeftSub_win_leftLoc haf]
  norm_num
  rfl

lemma precSetupVals_acc :
    precSetupVals af ag haf hag Ff V (precSelf af ag 11)
      = Ff (precBaseIn af ag haf hag V) ⟨3, by omega⟩ := by
  simp only [precSetupVals, precSelf_update_apply, precLeftLoc_self_upd haf,
    precLeftSub_win_leftLoc haf]
  norm_num
  rfl

end

/-! #### The finish -/

lemma precFinishVals_tag (haf : 16 ≤ af) (hag : 16 ≤ ag) (W : Fin (32 + af + ag) → ℕ) :
    precFinishVals af ag W (precSelf af ag 2)
      = (if W (precSelf af ag 0) < W (precSelf af ag 1) then 1 else 0)
          * W (precSelf af ag 10) := by
  simp only [precFinishVals, precSelf_update_apply]
  norm_num

lemma precFinishVals_val (haf : 16 ≤ af) (hag : 16 ≤ ag) (W : Fin (32 + af + ag) → ℕ) :
    precFinishVals af ag W (precSelf af ag 3)
      = precFinishVals af ag W (precSelf af ag 2) * W (precSelf af ag 11) := by
  rw [precFinishVals_tag haf hag]
  simp only [precFinishVals, precSelf_update_apply]
  norm_num

end PrecCloseSem

/-! ## `prec`, assembled

Setup, then the fixed-length loop, then the finish. The loop counter is the ambient
register `l`, outside the block the three phases name. -/

section PrecCompose
variable {af ag : ℕ}

def precTM (af ag : ℕ) (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (R : Regs (32 + af + ag) n) (l : Fin n) (Mf Mg : TM n) : TM n :=
  seqTM (precSetupTM af ag haf hag R l Mf)
    (seqTM (forRegTM (precBodyTM af ag haf hag R Mg) l) (precFinishTM af ag R))

/-- The register vector the whole `prec` node produces. -/
noncomputable def precVals (af ag : ℕ) (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (Ff : (Fin af → ℕ) → Fin af → ℕ) (Fg : (Fin ag → ℕ) → Fin ag → ℕ)
    (V : Fin (32 + af + ag) → ℕ) : Fin (32 + af + ag) → ℕ :=
  precFinishVals af ag
    (precLoopVals af ag haf hag Fg (precSetupVals af ag haf hag Ff V)
      (precSetupVals af ag haf hag Ff V (precSelf af ag 7)))

set_option maxHeartbeats 1000000 in
/-- **`prec`, complete.** -/
lemma precTM_hoareTime (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (R : Regs (32 + af + ag) n) (l : Fin n) (hl : ∀ k, R k ≠ l) (Mf Mg : TM n)
    (Ff : (Fin af → ℕ) → Fin af → ℕ) (Fg : (Fin ag → ℕ) → Fin ag → ℕ) (tf tg : ℕ)
    (V : Fin (32 + af + ag) → ℕ) (B : ℕ)
    (inp₀ : Tape) (w₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hpark : ∀ i, Parked (w₀ i))
    (cl : ℕ) (hlc : w₀ l = regTape cl) (hclB : cl ≤ B)
    (hB2 : 2 ≤ B) (hV : ∀ k, V k < B)
    (hFfB : ∀ u : Fin af → ℕ, (∀ k, u k < B) → ∀ k, Ff u k < B)
    (hFgB : ∀ u : Fin ag → ℕ, (∀ k, u k < B) → ∀ k, Fg u k < B)
    (hFgTag : ∀ u : Fin ag → ℕ, Fg u ⟨2, by omega⟩ ≤ 1)
    (hOK : ∀ i, i ≤ precSetupVals af ag haf hag Ff V (precSelf af ag 7) →
      PrecBodyOK af ag B
        (precLoopVals af ag haf hag Fg (precSetupVals af ag haf hag Ff V) i))
    (hMf : ∀ (Wb : Fin n → Tape) (u : Fin af → ℕ), (∀ i, Parked (Wb i)) → (∀ k, u k < B) →
      Mf.HoareTime (EmitPred inp₀ (regsWork ((precLeftSub af ag).trans R) Wb u) ys)
                   (EmitPred inp₀ (regsWork ((precLeftSub af ag).trans R) Wb (Ff u)) ys) tf)
    (hMg : ∀ (Wb : Fin n → Tape) (u : Fin ag → ℕ), (∀ i, Parked (Wb i)) → (∀ k, u k < B) →
      Mg.HoareTime (EmitPred inp₀ (regsWork ((precRightSub af ag).trans R) Wb u) ys)
                   (EmitPred inp₀ (regsWork ((precRightSub af ag).trans R) Wb (Fg u)) ys) tg) :
    (precTM af ag haf hag R l Mf Mg).HoareTime
      (EmitPred inp₀ (regsWork R w₀ V) ys)
      (EmitPred inp₀
        (regsWork R
          (Function.update w₀ l
            (regTape (precSetupVals af ag haf hag Ff V (precSelf af ag 7))))
          (precVals af ag haf hag Ff Fg V)) ys)
      ((12 * evalnArithmeticCost B + tf + 12) + 1 +
        ((precSetupVals af ag haf hag Ff V (precSelf af ag 7)) *
            ((15 * evalnArithmeticCost B + tg + 15) + 2) +
          ((precSetupVals af ag haf hag Ff V (precSelf af ag 7)) + 2) + 1 +
          (5 * evalnArithmeticCost B + 4))) := by
  set S := precSetupVals af ag haf hag Ff V with hS
  set m := S (precSelf af ag 7) with hm
  set w₁ := Function.update w₀ l (regTape m) with hw₁
  have hpark₁ : ∀ i, Parked (w₁ i) := by
    intro i; rw [hw₁]
    by_cases hi : i = l
    · subst hi; rw [Function.update_self]; exact parked_regTape _
    · rw [Function.update_of_ne hi]; exact hpark i
  have hsetup := precSetup_hoareTime haf hag R l hl Mf Ff tf V B inp₀ w₀ ys hinp₀ hpark
    cl hlc hclB hV hFfB hMf
  have hloop := precLoop_hoareTime (af := af) (ag := ag) haf hag R l hl Mg Fg tg B m S
    inp₀ w₁ ys hinp₀ hpark₁ hB2 (by rw [hw₁, Function.update_self]) hFgB hFgTag
    (fun i hi => hOK i (Nat.le_of_lt hi)) hMg
  obtain ⟨hLb, hLalive, -, -, -, -⟩ := hOK m le_rfl
  have hfin := precFinish_hoareTime (af := af) (ag := ag) R
    (precLoopVals af ag haf hag Fg S m) B inp₀ w₁ ys hinp₀ hpark₁ hLb hLalive
  exact seqEmit hinp₀ (parked_regsWork R hpark₁ S) hsetup
    (seqEmit hinp₀ (parked_regsWork R hpark₁ _) hloop hfin)

end PrecCompose

/-! ### `prec`, semantically complete -/

section PrecEncodes
variable {af ag : ℕ}

/-- **`prec`, semantically complete.** Given children that encode `evaln`, the node's tag
    and value registers hold the tag and value of `evaln fuel (prec cf cg) inp`. -/
lemma precVals_encodes (haf : 16 ≤ af) (hag : 16 ≤ ag) (cf cg : Nat.Partrec.Code)
    (Ff : (Fin af → ℕ) → Fin af → ℕ) (Fg : (Fin ag → ℕ) → Fin ag → ℕ)
    (hFf : ChildEncodes af haf cf Ff) (hFg : ChildEncodes ag hag cg Fg)
    (V : Fin (32 + af + ag) → ℕ) :
    precVals af ag haf hag Ff Fg V (precSelf af ag 2)
        = resultTag (Nat.Partrec.Code.evaln (V (precSelf af ag 1)) (cf.prec cg)
            (V (precSelf af ag 0))) ∧
      precVals af ag haf hag Ff Fg V (precSelf af ag 3)
        = resultVal (Nat.Partrec.Code.evaln (V (precSelf af ag 1)) (cf.prec cg)
            (V (precSelf af ag 0))) := by
  have hpair : Nat.pair (Nat.unpair (V (precSelf af ag 0))).1
      (Nat.unpair (V (precSelf af ag 0))).2 = V (precSelf af ag 0) := Nat.pair_unpair _
  obtain ⟨hbt, hbv⟩ := hFf (precBaseIn af ag haf hag V)
  rw [precBaseIn_zero, precBaseIn_one] at hbt hbv
  obtain ⟨-, -, -, hL10, hL11⟩ :=
    precLoopVals_spec haf hag cf cg Fg hFg (precSetupVals af ag haf hag Ff V)
      (Nat.unpair (V (precSelf af ag 0))).1
      (V (precSelf af ag 1) - (Nat.unpair (V (precSelf af ag 0))).2)
      (precSetupVals_a haf hag Ff V) (precSetupVals_j haf hag Ff V)
      (precSetupVals_curFuel haf hag Ff V)
      (by rw [precSetupVals_alive, hbt]) (by rw [precSetupVals_acc, hbv])
      (Nat.unpair (V (precSelf af ag 0))).2
  have hL0 : precLoopVals af ag haf hag Fg (precSetupVals af ag haf hag Ff V)
      (Nat.unpair (V (precSelf af ag 0))).2 (precSelf af ag 0) = V (precSelf af ag 0) := by
    rw [precLoopVals_frame haf hag Fg _ 0 (by norm_num) (by norm_num),
      precSetupVals_self haf hag Ff V 0 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)]
  have hL1 : precLoopVals af ag haf hag Fg (precSetupVals af ag haf hag Ff V)
      (Nat.unpair (V (precSelf af ag 0))).2 (precSelf af ag 1) = V (precSelf af ag 1) := by
    rw [precLoopVals_frame haf hag Fg _ 1 (by norm_num) (by norm_num),
      precSetupVals_self haf hag Ff V 1 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)]
  have htag : precVals af ag haf hag Ff Fg V (precSelf af ag 2)
      = (if V (precSelf af ag 0) < V (precSelf af ag 1) then 1 else 0)
          * resultTag (precRunG cf cg (Nat.unpair (V (precSelf af ag 0))).1
              (V (precSelf af ag 1) - (Nat.unpair (V (precSelf af ag 0))).2)
              (Nat.unpair (V (precSelf af ag 0))).2) := by
    rw [precVals, precSetupVals_m, precFinishVals_tag haf hag, hL0, hL1, hL10]
  have hval : precVals af ag haf hag Ff Fg V (precSelf af ag 3)
      = precVals af ag haf hag Ff Fg V (precSelf af ag 2)
          * resultVal (precRunG cf cg (Nat.unpair (V (precSelf af ag 0))).1
              (V (precSelf af ag 1) - (Nat.unpair (V (precSelf af ag 0))).2)
              (Nat.unpair (V (precSelf af ag 0))).2) := by
    rw [precVals, precSetupVals_m, precFinishVals_val haf hag, hL11]
  by_cases hg : V (precSelf af ag 0) < V (precSelf af ag 1)
  · have hout : Nat.pair (Nat.unpair (V (precSelf af ag 0))).1
        (Nat.unpair (V (precSelf af ag 0))).2 < V (precSelf af ag 1) := by
      rw [hpair]; exact hg
    have heq := precRunG_eq_evaln cf cg (Nat.unpair (V (precSelf af ag 0))).1
      (Nat.unpair (V (precSelf af ag 0))).2 (V (precSelf af ag 1)) hout
    rw [hpair] at heq
    refine ⟨?_, ?_⟩
    · rw [htag, if_pos hg, heq]; omega
    · rw [hval, htag, if_pos hg, heq]; simp
  · have hnone := evaln_eq_none_of_not_guard (V (precSelf af ag 1)) (cf.prec cg)
      (V (precSelf af ag 0)) hg
    refine ⟨?_, ?_⟩
    · rw [htag, if_neg hg, hnone]; simp
    · rw [hval, htag, if_neg hg, hnone]; simp

end PrecEncodes

/-! ## `prec`: the setup keeps every register inside the bound -/

section PrecSetupBound
variable {af ag : ℕ}

lemma precSetupPre_lt (haf : 16 ≤ af) (hag : 16 ≤ ag) (V : Fin (32 + af + ag) → ℕ)
    (B : ℕ) (hV : ∀ k, V k < B) : ∀ k, precSetupPre af ag haf hag V k < B := by
  have hB0 : 0 < B := Nat.lt_of_le_of_lt (Nat.zero_le _) (hV (precSelf af ag 0))
  intro k
  simp only [precSetupPre]
  set U1 := writeWindow (precUnpairW af ag) V
      (unpairVals (fun j => V (precUnpairW af ag j)) (V (precSelf af ag 0))) with hU1
  have b1 : ∀ k, U1 k < B := by
    intro k; rw [hU1]
    refine writeWindow_bounded _ _ _ B hV (fun j => ?_) k
    have := unpairVals_bounded (fun j => V (precUnpairW af ag j)) (B - 1)
      (fun i => by have := hV (precUnpairW af ag i); omega) (V (precSelf af ag 0))
      (by have := hV (precSelf af ag 0); omega) j
    omega
  set U2 := Function.update U1 (precSelf af ag 6) (U1 (precSelf af ag 16)) with hU2
  have b2 : ∀ k, U2 k < B := by
    intro k; rw [hU2]; simp only [Function.update_apply]; split_ifs <;> exact b1 _
  set U3 := Function.update U2 (precSelf af ag 7) (U2 (precSelf af ag 17)) with hU3
  have b3 : ∀ k, U3 k < B := by
    intro k; rw [hU3]; simp only [Function.update_apply]; split_ifs <;> exact b2 _
  set U4 := Function.update U3 (precSelf af ag 8) (U3 (precSelf af ag 1)) with hU4
  have b4 : ∀ k, U4 k < B := by
    intro k; rw [hU4]; simp only [Function.update_apply]; split_ifs <;> exact b3 _
  set U5 := Function.update U4 (precSelf af ag 8)
      (U4 (precSelf af ag 8) - U4 (precSelf af ag 7)) with hU5
  have b5 : ∀ k, U5 k < B := by
    intro k; rw [hU5]; simp only [Function.update_apply]; split_ifs
    · have := b4 (precSelf af ag 8); omega
    · exact b4 _
  set U6 := Function.update U5 (precLeftLoc af ag haf 0) (U5 (precSelf af ag 6)) with hU6
  have b6 : ∀ k, U6 k < B := by
    intro k; rw [hU6]; simp only [Function.update_apply]; split_ifs <;> exact b5 _
  simp only [Function.update_apply]; split_ifs <;> exact b6 _

lemma precSetupVals_lt (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (Ff : (Fin af → ℕ) → Fin af → ℕ) (V : Fin (32 + af + ag) → ℕ) (B : ℕ)
    (hV : ∀ k, V k < B)
    (hFfB : ∀ u : Fin af → ℕ, (∀ k, u k < B) → ∀ k, Ff u k < B) :
    ∀ k, precSetupVals af ag haf hag Ff V k < B := by
  have hB0 : 0 < B := Nat.lt_of_le_of_lt (Nat.zero_le _) (hV (precSelf af ag 0))
  have b7 := precSetupPre_lt haf hag V B hV
  intro k
  simp only [precSetupVals]
  set U8 := writeWindow (precLeftSub af ag) (precSetupPre af ag haf hag V)
      (Ff (fun i => precSetupPre af ag haf hag V (precLeftSub af ag i))) with hU8
  have b8 : ∀ k, U8 k < B := by
    intro k; rw [hU8]
    exact writeWindow_bounded _ _ _ B b7 (fun i => hFfB _ (fun t => b7 _) i) k
  set U9 := Function.update U8 (precSelf af ag 9) 0 with hU9
  have b9 : ∀ k, U9 k < B := by
    intro k; rw [hU9]; simp only [Function.update_apply]; split_ifs
    · exact hB0
    · exact b8 _
  set U10 := Function.update U9 (precSelf af ag 10) (U9 (precLeftLoc af ag haf 2)) with hU10
  have b10 : ∀ k, U10 k < B := by
    intro k; rw [hU10]; simp only [Function.update_apply]; split_ifs <;> exact b9 _
  set U11 := Function.update U10 (precSelf af ag 11) (U10 (precLeftLoc af ag haf 3))
    with hU11
  have b11 : ∀ k, U11 k < B := by
    intro k; rw [hU11]; simp only [Function.update_apply]; split_ifs <;> exact b10 _
  simp only [Function.update_apply]; split_ifs <;> exact b11 _

end PrecSetupBound

/-! ## `rfind'`: the exact equation, and the search the machine loop implements

At fuel `k+1`,

```
guard (n ≤ k)
n.unpaired fun a m => do
  let x ← evaln (k+1) cf (Nat.pair a m)
  if x = 0 then pure m else evaln k (rfind' cf) (Nat.pair a (m+1))
```

so the fuel decreases by one per level while the index `m` increases by one. Unlike
`prec`, the level guards are **not** free here: `Nat.pair a (m+t)` grows while the level
fuel `k+1-t` shrinks, so a guard can fail part-way down and the machine must test it.

The machine carries three registers — `searching`, `found`, `result` — and one level is
`rfLevel`: the guard, the child's tag, and the zero test enter multiplicatively, so there
is still no branch. `rfIter` is the fixed-length iterate, and `rfIter_spec` says the loop
run for `fuel` levels computes `evaln fuel (rfind' cf)` in both components. -/

section RfindPure

lemma evaln_rfind'_zero (cf : Nat.Partrec.Code) (m : ℕ) :
    Nat.Partrec.Code.evaln 0 cf.rfind' m = Option.none := by
  simp [Nat.Partrec.Code.evaln]

lemma evaln_rfind'_succ (k : ℕ) (cf : Nat.Partrec.Code) (a m : ℕ) :
    Nat.Partrec.Code.evaln (k + 1) cf.rfind' (Nat.pair a m)
      = if Nat.pair a m < k + 1 then
          (Nat.Partrec.Code.evaln (k + 1) cf (Nat.pair a m)).bind fun x =>
            if x = 0 then some m
            else Nat.Partrec.Code.evaln k cf.rfind' (Nat.pair a (m + 1))
        else Option.none := by
  simp only [Nat.Partrec.Code.evaln, Nat.unpaired, Nat.unpair_pair, Nat.lt_succ_iff]
  split_ifs with h <;> simp [h, Option.bind]

/-- One level of the search, as the machine performs it: guard, child tag, and zero test
    all enter multiplicatively. The triple is `(searching, found, result)`. -/
def rfLevel (cf : Nat.Partrec.Code) (a : ℕ) (st : ℕ × ℕ × ℕ) (f m : ℕ) : ℕ × ℕ × ℕ :=
  let o := Nat.Partrec.Code.evaln f cf (Nat.pair a m)
  let live := st.1 * (if Nat.pair a m < f then 1 else 0) * resultTag o
  let z := if resultVal o = 0 then 1 else 0
  let hit := live * z
  (live * (1 - z), st.2.1 + hit, st.2.2 + hit * m)

/-- The fixed-length iterate: `t` levels, starting at fuel `f` and index `m`. -/
def rfIter (cf : Nat.Partrec.Code) (a : ℕ) : ℕ × ℕ × ℕ → ℕ → ℕ → ℕ → ℕ × ℕ × ℕ
  | st, _, _, 0 => st
  | st, f, m, t + 1 => rfIter cf a (rfLevel cf a st f m) (f - 1) (m + 1) t

@[simp] lemma rfIter_zero (cf a st f m) : rfIter cf a st f m 0 = st := rfl

lemma rfIter_succ (cf a st f m t) :
    rfIter cf a st f m (t + 1) = rfIter cf a (rfLevel cf a st f m) (f - 1) (m + 1) t := rfl

/-- **The search is `evaln`.** Running the loop for exactly `f` levels computes
    `evaln f (rfind' cf) (Nat.pair a m)` in both components, with the incoming
    `searching` flag multiplying the whole answer. -/
lemma rfIter_spec (cf : Nat.Partrec.Code) (a : ℕ) :
    ∀ (f m s fo r : ℕ),
      (rfIter cf a (s, fo, r) f m f).2.1
          = fo + s * resultTag (Nat.Partrec.Code.evaln f cf.rfind' (Nat.pair a m)) ∧
        (rfIter cf a (s, fo, r) f m f).2.2
          = r + s * resultVal (Nat.Partrec.Code.evaln f cf.rfind' (Nat.pair a m)) := by
  intro f
  induction f with
  | zero => intro m s fo r; simp [evaln_rfind'_zero]
  | succ k ih =>
    intro m s fo r
    rw [rfIter_succ]
    have hstep := ih (m + 1) ((rfLevel cf a (s, fo, r) (k + 1) m).1)
      ((rfLevel cf a (s, fo, r) (k + 1) m).2.1)
      ((rfLevel cf a (s, fo, r) (k + 1) m).2.2)
    simp only [Nat.add_sub_cancel] at hstep ⊢
    rw [hstep.1, hstep.2, evaln_rfind'_succ]
    simp only [rfLevel]
    by_cases hg : Nat.pair a m < k + 1
    · simp only [hg, if_true]
      cases hoe : Nat.Partrec.Code.evaln (k + 1) cf (Nat.pair a m) with
      | none => simp
      | some x =>
        by_cases hx : x = 0
        · subst hx; simp
        · simp only [resultTag_some, resultVal_some, hx, if_false, mul_one,
            Option.bind_some]
          cases Nat.Partrec.Code.evaln k cf.rfind' (Nat.pair a (m + 1)) <;> simp
    · simp [hg]

end RfindPure

/-! ## `rfind'`: register layout

Like `prec`, an `rfind'` node is thirty-three registers wide plus its child's subtree: the
thirty-third is the loop counter, which must sit outside the block the body names.

```
0–5  interface + outer guard      6 a   7 m   8 curFuel
9 searching  10 found  11 result  12 the constant 1
13 guard flag  14 zero flag  15 hit  16 nz  17–19 temps  20–28 pair/unpair window
```
-/

section RfindLayout
variable {af : ℕ}

/-- The node's own thirty-two registers. -/
def rfSelf (af : ℕ) : Fin 32 ↪ Fin (32 + af) := shiftEmb 0 (by omega)
/-- `cf`'s whole subtree. -/
def rfSub (af : ℕ) : Fin af ↪ Fin (32 + af) := shiftEmb 32 (by omega)
/-- `cf`'s own sixteen. -/
def rfLoc (af : ℕ) (h : 16 ≤ af) : Fin 16 ↪ Fin (32 + af) := shiftEmb 32 (by omega)
/-- The pairing window, at offset `20`. -/
def rfPairW (af : ℕ) : Fin 8 ↪ Fin (32 + af) := shiftEmb 20 (by omega)
/-- The unpairing window, same offset, nine wide. -/
def rfUnpairW (af : ℕ) : Fin 9 ↪ Fin (32 + af) := shiftEmb 20 (by omega)
/-- The thirty-two-plus-subtree block the body works over. -/
def rfMain (af : ℕ) : Fin (32 + af) ↪ Fin (33 + af) := shiftEmb 0 (by omega)
/-- The loop counter, the one register outside that block. -/
def rfLoopIdx (af : ℕ) : Fin (33 + af) := ⟨32 + af, by omega⟩

lemma rfSelf_ne_self (i j : Fin 32) (h : (i : ℕ) ≠ (j : ℕ)) :
    rfSelf af i ≠ rfSelf af j := by
  apply amb_ne; simpa using h

lemma rfSelf_ne_loc (haf : 16 ≤ af) (i : Fin 32) (j : Fin 16) :
    rfSelf af i ≠ rfLoc af haf j := by
  apply amb_ne; have := i.isLt; simp; omega

lemma rfSub_ne_self (i : Fin af) (j : Fin 32) : rfSub af i ≠ rfSelf af j := by
  apply amb_ne; have := j.isLt; simp; omega

lemma rfPairW_ne_self (i : Fin 8) (j : Fin 32) (h : 20 + (i : ℕ) ≠ (j : ℕ)) :
    rfPairW af i ≠ rfSelf af j := by
  apply amb_ne; simpa using h

lemma rfUnpairW_ne_self (i : Fin 9) (j : Fin 32) (h : 20 + (i : ℕ) ≠ (j : ℕ)) :
    rfUnpairW af i ≠ rfSelf af j := by
  apply amb_ne; simpa using h

lemma rfPairW_ne_loc (haf : 16 ≤ af) (i : Fin 8) (j : Fin 16) :
    rfPairW af i ≠ rfLoc af haf j := by
  apply amb_ne; have := i.isLt; simp; omega

lemma rfUnpairW_ne_loc (haf : 16 ≤ af) (i : Fin 9) (j : Fin 16) :
    rfUnpairW af i ≠ rfLoc af haf j := by
  apply amb_ne; have := i.isLt; simp; omega

/-- A child's local block is the first sixteen of its subtree. -/
lemma rfLoc_eq (haf : 16 ≤ af) (j : Fin 16) :
    rfLoc af haf j = rfSub af ⟨(j : ℕ), by have := j.isLt; omega⟩ := by
  apply Fin.ext; simp [rfLoc, rfSub, shiftEmb_val]

lemma rfPairW_zero : (rfPairW af) 0 = rfSelf af 20 := by
  apply Fin.ext; simp [rfPairW, rfSelf, shiftEmb_val]

lemma rfPairW_one : (rfPairW af) 1 = rfSelf af 21 := by
  apply Fin.ext; simp [rfPairW, rfSelf, shiftEmb_val]

lemma rfPairW_six : (rfPairW af) 6 = rfSelf af 26 := by
  apply Fin.ext; simp [rfPairW, rfSelf, shiftEmb_val]

lemma rfUnpairW_zero : (rfUnpairW af) 0 = rfSelf af 20 := by
  apply Fin.ext; simp [rfUnpairW, rfSelf, shiftEmb_val]

lemma rfUnpairW_one : (rfUnpairW af) 1 = rfSelf af 21 := by
  apply Fin.ext; simp [rfUnpairW, rfSelf, shiftEmb_val]

lemma rfMain_ne_loopIdx (k : Fin (32 + af)) : rfMain af k ≠ rfLoopIdx af := by
  apply Fin.ne_of_val_ne
  have := k.isLt
  simp [rfMain, rfLoopIdx, shiftEmb_val]
  omega

end RfindLayout

/-! ## `rfind'`: the loop body

One level of the search: build `Nat.pair a m`, test the level guard, run `cf`, then fold
the guard, the child's tag and the zero test into `searching`, `found` and `result` — all
multiplicatively, so there is no branch and the loop has fixed length. -/

section RfindBody
variable {af : ℕ}

def rfPhaseA (af : ℕ) (haf : 16 ≤ af) (R : Regs (32 + af) n) (Mf : TM n) : TM n :=
  seqTM (copyIntoTM (R (rfSelf af 6)) (R (rfSelf af 20))) <|
  seqTM (copyIntoTM (R (rfSelf af 7)) (R (rfSelf af 21))) <|
  seqTM (pairTM ((rfPairW af).trans R)) <|
  seqTM (copyIntoTM (R (rfSelf af 26)) (R (rfLoc af haf 0))) <|
  seqTM (copyIntoTM (R (rfSelf af 8)) (R (rfLoc af haf 1))) <|
  seqTM (ltFlagTM (R (rfSelf af 26)) (R (rfSelf af 8)) (R (rfSelf af 5))
          (R (rfSelf af 13)))
        Mf

def rfPhaseB1 (af : ℕ) (haf : 16 ≤ af) (R : Regs (32 + af) n) : TM n :=
  seqTM (clearRegTM (R (rfSelf af 17))) <|
  seqTM (mulAddIntoTM (R (rfSelf af 9)) (R (rfSelf af 13)) (R (rfSelf af 17))) <|
  seqTM (clearRegTM (R (rfSelf af 9))) <|
  seqTM (mulAddIntoTM (R (rfSelf af 17)) (R (rfLoc af haf 2)) (R (rfSelf af 9))) <|
  seqTM (ltFlagTM (R (rfLoc af haf 3)) (R (rfSelf af 12)) (R (rfSelf af 5))
          (R (rfSelf af 14))) <|
  seqTM (clearRegTM (R (rfSelf af 15)))
        (mulAddIntoTM (R (rfSelf af 9)) (R (rfSelf af 14)) (R (rfSelf af 15)))

def rfPhaseB2 (af : ℕ) (haf : 16 ≤ af) (R : Regs (32 + af) n) : TM n :=
  seqTM (mulAddIntoTM (R (rfSelf af 15)) (R (rfSelf af 7)) (R (rfSelf af 11))) <|
  seqTM (addIntoTM (R (rfSelf af 15)) (R (rfSelf af 10))) <|
  seqTM (copyIntoTM (R (rfSelf af 12)) (R (rfSelf af 16))) <|
  seqTM (subIntoTM (R (rfSelf af 14)) (R (rfSelf af 16))) <|
  seqTM (clearRegTM (R (rfSelf af 17))) <|
  seqTM (mulAddIntoTM (R (rfSelf af 9)) (R (rfSelf af 16)) (R (rfSelf af 17))) <|
  seqTM (copyIntoTM (R (rfSelf af 17)) (R (rfSelf af 9))) <|
  seqTM (incRegTM (R (rfSelf af 7)))
        (decRegTM (R (rfSelf af 8)))

def rfPhaseB (af : ℕ) (haf : 16 ≤ af) (R : Regs (32 + af) n) : TM n :=
  seqTM (rfPhaseB1 af haf R) (rfPhaseB2 af haf R)

def rfBodyTM (af : ℕ) (haf : 16 ≤ af) (R : Regs (32 + af) n) (Mf : TM n) : TM n :=
  seqTM (rfPhaseA af haf R Mf) (rfPhaseB af haf R)

/-- The level's input pair, `Nat.pair a m`, built in the node's pairing window. -/
noncomputable def rfPhaseAPair (af : ℕ) (V : Fin (32 + af) → ℕ) : Fin (32 + af) → ℕ :=
  let V1 := Function.update V (rfSelf af 20) (V (rfSelf af 6))
  let V2 := Function.update V1 (rfSelf af 21) (V1 (rfSelf af 7))
  writeWindow (rfPairW af) V2 (pairVals (fun i => V2 ((rfPairW af) i)))

/-- The state phase A hands the child: the level's input pair in the child's input
    register, the level fuel in its fuel register, and the level guard in `13`. -/
noncomputable def rfPhaseAPre (af : ℕ) (haf : 16 ≤ af) (V : Fin (32 + af) → ℕ) :
    Fin (32 + af) → ℕ :=
  let V3 := rfPhaseAPair af V
  let V4 := Function.update V3 (rfLoc af haf 0) (V3 (rfSelf af 26))
  let V5 := Function.update V4 (rfLoc af haf 1) (V4 (rfSelf af 8))
  Function.update
    (Function.update V5 (rfSelf af 5) (V5 (rfSelf af 8) - V5 (rfSelf af 26)))
    (rfSelf af 13) (if V5 (rfSelf af 26) < V5 (rfSelf af 8) then 1 else 0)

/-- What phase A leaves: that state, with the child run on it. -/
noncomputable def rfPhaseAVals (af : ℕ) (haf : 16 ≤ af)
    (Ff : (Fin af → ℕ) → Fin af → ℕ) (V : Fin (32 + af) → ℕ) : Fin (32 + af) → ℕ :=
  writeWindow (rfSub af) (rfPhaseAPre af haf V)
    (Ff (fun i => rfPhaseAPre af haf V (rfSub af i)))

/-- What phase B leaves: the guard, the child's tag and the zero test folded into
    `searching`, `found` and `result`, and the level advanced. -/
noncomputable def rfPhaseB1Vals (af : ℕ) (haf : 16 ≤ af) (W : Fin (32 + af) → ℕ) :
    Fin (32 + af) → ℕ :=
  let V8 := Function.update W (rfSelf af 17) 0
  let V9 := Function.update V8 (rfSelf af 17) (0 + V8 (rfSelf af 9) * V8 (rfSelf af 13))
  let V10 := Function.update V9 (rfSelf af 9) 0
  let V11 := Function.update V10 (rfSelf af 9)
               (0 + V10 (rfSelf af 17) * V10 (rfLoc af haf 2))
  let V12 := Function.update
               (Function.update V11 (rfSelf af 5)
                 (V11 (rfSelf af 12) - V11 (rfLoc af haf 3)))
               (rfSelf af 14)
               (if V11 (rfLoc af haf 3) < V11 (rfSelf af 12) then 1 else 0)
  let V13 := Function.update V12 (rfSelf af 15) 0
  Function.update V13 (rfSelf af 15) (0 + V13 (rfSelf af 9) * V13 (rfSelf af 14))

/-- What phase B2 leaves: the hit folded into `found` and `result`, `searching` narrowed
    by the zero test, and the level advanced. -/
noncomputable def rfPhaseB2Vals (af : ℕ) (haf : 16 ≤ af) (V14 : Fin (32 + af) → ℕ) :
    Fin (32 + af) → ℕ :=
  let V15 := Function.update V14 (rfSelf af 11)
               (V14 (rfSelf af 11) + V14 (rfSelf af 15) * V14 (rfSelf af 7))
  let V16 := Function.update V15 (rfSelf af 10)
               (V15 (rfSelf af 10) + V15 (rfSelf af 15))
  let V17 := Function.update V16 (rfSelf af 16) (V16 (rfSelf af 12))
  let V18 := Function.update V17 (rfSelf af 16)
               (V17 (rfSelf af 16) - V17 (rfSelf af 14))
  let V19 := Function.update V18 (rfSelf af 17) 0
  let V20 := Function.update V19 (rfSelf af 17)
               (0 + V19 (rfSelf af 9) * V19 (rfSelf af 16))
  let V21 := Function.update V20 (rfSelf af 9) (V20 (rfSelf af 17))
  let V22 := Function.update V21 (rfSelf af 7) (V21 (rfSelf af 7) + 1)
  Function.update V22 (rfSelf af 8) (V22 (rfSelf af 8) - 1)

noncomputable def rfPhaseBVals (af : ℕ) (haf : 16 ≤ af) (W : Fin (32 + af) → ℕ) :
    Fin (32 + af) → ℕ :=
  rfPhaseB2Vals af haf (rfPhaseB1Vals af haf W)

/-- The ambient register vector one level produces. -/
noncomputable def rfBodyVals (af : ℕ) (haf : 16 ≤ af)
    (Ff : (Fin af → ℕ) → Fin af → ℕ) (V : Fin (32 + af) → ℕ) : Fin (32 + af) → ℕ :=
  rfPhaseBVals af haf (rfPhaseAVals af haf Ff V)

/-- The loop state after `t` levels. -/
noncomputable def rfLoopVals (af : ℕ) (haf : 16 ≤ af)
    (Ff : (Fin af → ℕ) → Fin af → ℕ) (V₀ : Fin (32 + af) → ℕ) (t : ℕ) :
    Fin (32 + af) → ℕ :=
  (rfBodyVals af haf Ff)^[t] V₀

@[simp] lemma rfLoopVals_zero (haf : 16 ≤ af) (Ff : (Fin af → ℕ) → Fin af → ℕ)
    (V₀ : Fin (32 + af) → ℕ) : rfLoopVals af haf Ff V₀ 0 = V₀ := rfl

lemma rfLoopVals_succ (haf : 16 ≤ af) (Ff : (Fin af → ℕ) → Fin af → ℕ)
    (V₀ : Fin (32 + af) → ℕ) (t : ℕ) :
    rfLoopVals af haf Ff V₀ (t + 1) = rfBodyVals af haf Ff (rfLoopVals af haf Ff V₀ t) := by
  rw [rfLoopVals, rfLoopVals, Function.iterate_succ_apply']

end RfindBody

section RfindPhaseAProof
variable {af : ℕ}

set_option maxHeartbeats 1000000 in
/-- **`rfPhaseA` Hoare specification.** -/
lemma rfPhaseA_hoareTime (haf : 16 ≤ af)
    (R : Regs (32 + af) n) (Mf : TM n)
    (Ff : (Fin af → ℕ) → Fin af → ℕ) (tf : ℕ)
    (V : Fin (32 + af) → ℕ) (B : ℕ)
    (inp₀ : Tape) (w₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hpark : ∀ i, Parked (w₀ i)) (hB2 : 2 ≤ B)
    (hV : ∀ k, V k < B)
    (hp : Nat.pair (V (rfSelf af 6)) (V (rfSelf af 7)) < B)
    (hFfB : ∀ u : Fin af → ℕ, (∀ k, u k < B) → ∀ k, Ff u k < B)
    (hMf : ∀ (Wb : Fin n → Tape) (u : Fin af → ℕ), (∀ i, Parked (Wb i)) → (∀ k, u k < B) →
      Mf.HoareTime (EmitPred inp₀ (regsWork ((rfSub af).trans R) Wb u) ys)
                   (EmitPred inp₀ (regsWork ((rfSub af).trans R) Wb (Ff u)) ys) tf) :
    (rfPhaseA af haf R Mf).HoareTime
      (EmitPred inp₀ (regsWork R w₀ V) ys)
      (EmitPred inp₀ (regsWork R w₀ (rfPhaseAVals af haf Ff V)) ys)
      (6 * evalnArithmeticCost B + tf + 6) := by
  have hpv := parked_regsWork R hpark
  have hle : ∀ k, V k ≤ B := fun k => Nat.le_of_lt (hV k)
  -- S1: pair slot 0 := a
  have h1 := copyIntoTM_hoareTime (R (rfSelf af 6)) (R (rfSelf af 20))
      (Regs.ne R (rfSelf_ne_self 6 20 (by decide)))
      (V (rfSelf af 6)) (V (rfSelf af 20))
      inp₀ (regsWork R w₀ V) ys hinp₀ (fun i _ => hpv V i)
      (regsWork_apply R w₀ V _) (regsWork_apply R w₀ V _)
  rw [regsWork_update] at h1
  replace h1 := h1.mono_bound (copyIntoTime_le_arith _ _ B (hle _) (hle _))
  set V1 := Function.update V (rfSelf af 20) (V (rfSelf af 6)) with hV1
  have b1 : ∀ k, V1 k < B := by
    intro k; rw [hV1]; simp only [Function.update_apply]; split_ifs <;> exact hV _
  -- S2: pair slot 1 := m
  have h2 := copyIntoTM_hoareTime (R (rfSelf af 7)) (R (rfSelf af 21))
      (Regs.ne R (rfSelf_ne_self 7 21 (by decide)))
      (V1 (rfSelf af 7)) (V1 (rfSelf af 21))
      inp₀ (regsWork R w₀ V1) ys hinp₀ (fun i _ => hpv V1 i)
      (regsWork_apply R w₀ V1 _) (regsWork_apply R w₀ V1 _)
  rw [regsWork_update] at h2
  replace h2 := h2.mono_bound
    (copyIntoTime_le_arith _ _ B (Nat.le_of_lt (b1 _)) (Nat.le_of_lt (b1 _)))
  set V2 := Function.update V1 (rfSelf af 21) (V1 (rfSelf af 7)) with hV2
  have b2 : ∀ k, V2 k < B := by
    intro k; rw [hV2]; simp only [Function.update_apply]; split_ifs <;> exact b1 _
  have hw0 : V2 ((rfPairW af) 0) = V (rfSelf af 6) := by
    rw [rfPairW_zero, hV2, Function.update_of_ne (rfSelf_ne_self 20 21 (by decide)),
      hV1, Function.update_self]
  have hw1 : V2 ((rfPairW af) 1) = V (rfSelf af 7) := by
    rw [rfPairW_one, hV2, Function.update_self, hV1,
      Function.update_of_ne (rfSelf_ne_self 7 20 (by decide))]
  -- S3: pair a m
  have h3 := runChild (rfPairW af) R (pairTM ((rfPairW af).trans R)) pairVals
      (evalnArithmeticCost B) B w₀ hpark V2 b2
      (fun Wb u hpk hu => pairTM_hoareTime_arith _ u B inp₀ Wb ys hinp₀ hpk
        (fun k => Nat.le_of_lt (hu k)))
  set V3 := writeWindow (rfPairW af) V2 (pairVals (fun i => V2 ((rfPairW af) i))) with hV3
  have b3 : ∀ k, V3 k < B := by
    intro k; rw [hV3]
    refine writeWindow_bounded _ _ _ B b2 (fun i => ?_) k
    refine pairVals_lt _ B hB2 (fun i => b2 _) ?_ i
    rw [hw0, hw1]; exact hp
  have out2 : ∀ (i : Fin 32), (∀ t : Fin 8, 20 + (t : ℕ) ≠ (i : ℕ)) →
      V3 (rfSelf af i) = V (rfSelf af i) := by
    intro i hi
    have h20 : (i : ℕ) ≠ 20 := by have := hi 0; simp at this ⊢; omega
    have h21 : (i : ℕ) ≠ 21 := by have := hi 1; simp at this ⊢; omega
    rw [hV3, runChild_frame _ _ _ (fun t => rfPairW_ne_self t i (hi t)),
      hV2, Function.update_of_ne (rfSelf_ne_self i 21 h21),
      hV1, Function.update_of_ne (rfSelf_ne_self i 20 h20)]
  have r3_26 : V3 (rfSelf af 26) = Nat.pair (V (rfSelf af 6)) (V (rfSelf af 7)) := by
    rw [← rfPairW_six, hV3, writeWindow_apply]
    simp only [pairVals]
    simp [hw0, hw1]
  -- S4: cf.input := that pair
  have h4 := copyIntoTM_hoareTime (R (rfSelf af 26)) (R (rfLoc af haf 0))
      (Regs.ne R (rfSelf_ne_loc haf 26 0))
      (V3 (rfSelf af 26)) (V3 (rfLoc af haf 0))
      inp₀ (regsWork R w₀ V3) ys hinp₀ (fun i _ => hpv V3 i)
      (regsWork_apply R w₀ V3 _) (regsWork_apply R w₀ V3 _)
  rw [regsWork_update] at h4
  replace h4 := h4.mono_bound
    (copyIntoTime_le_arith _ _ B (Nat.le_of_lt (b3 _)) (Nat.le_of_lt (b3 _)))
  set V4 := Function.update V3 (rfLoc af haf 0) (V3 (rfSelf af 26)) with hV4
  have b4 : ∀ k, V4 k < B := by
    intro k; rw [hV4]; simp only [Function.update_apply]; split_ifs <;> exact b3 _
  -- S5: cf.fuel := curFuel
  have h5 := copyIntoTM_hoareTime (R (rfSelf af 8)) (R (rfLoc af haf 1))
      (Regs.ne R (rfSelf_ne_loc haf 8 1))
      (V4 (rfSelf af 8)) (V4 (rfLoc af haf 1))
      inp₀ (regsWork R w₀ V4) ys hinp₀ (fun i _ => hpv V4 i)
      (regsWork_apply R w₀ V4 _) (regsWork_apply R w₀ V4 _)
  rw [regsWork_update] at h5
  replace h5 := h5.mono_bound
    (copyIntoTime_le_arith _ _ B (Nat.le_of_lt (b4 _)) (Nat.le_of_lt (b4 _)))
  set V5 := Function.update V4 (rfLoc af haf 1) (V4 (rfSelf af 8)) with hV5
  have b5 : ∀ k, V5 k < B := by
    intro k; rw [hV5]; simp only [Function.update_apply]; split_ifs <;> exact b4 _
  -- S6: the level guard
  have h6 := ltFlagTM_hoareTime (R (rfSelf af 26)) (R (rfSelf af 8)) (R (rfSelf af 5))
      (R (rfSelf af 13))
      (Regs.ne R (rfSelf_ne_self 26 5 (by decide)))
      (Regs.ne R (rfSelf_ne_self 8 5 (by decide)))
      (Regs.ne R (rfSelf_ne_self 5 13 (by decide)))
      (V5 (rfSelf af 26)) (V5 (rfSelf af 8)) (V5 (rfSelf af 5)) (V5 (rfSelf af 13))
      inp₀ (regsWork R w₀ V5) ys hinp₀ (fun i => hpv V5 i)
      (regsWork_apply R w₀ V5 _) (regsWork_apply R w₀ V5 _)
      (regsWork_apply R w₀ V5 _) (regsWork_apply R w₀ V5 _)
  rw [regsWork_update, regsWork_update] at h6
  replace h6 := h6.mono_bound
    (ltFlagTime_le_arith _ _ _ _ B (Nat.le_of_lt (b5 _)) (Nat.le_of_lt (b5 _))
      (Nat.le_of_lt (b5 _)) (Nat.le_of_lt (b5 _)))
  set V6 := Function.update
      (Function.update V5 (rfSelf af 5) (V5 (rfSelf af 8) - V5 (rfSelf af 26)))
      (rfSelf af 13) (if V5 (rfSelf af 26) < V5 (rfSelf af 8) then 1 else 0) with hV6
  have b6 : ∀ k, V6 k < B := by
    intro k; rw [hV6]; simp only [Function.update_apply]
    split_ifs <;> first
      | omega
      | (have := b5 (rfSelf af 8); omega)
      | exact b5 _
  -- S7: run cf
  have h7 := runChild (rfSub af) R Mf Ff tf B w₀ hpark V6 b6 hMf
  exact (seqEmit hinp₀ (hpv V1) h1 <|
    seqEmit hinp₀ (hpv V2) h2 <|
    seqEmit hinp₀ (hpv V3) h3 <|
    seqEmit hinp₀ (hpv V4) h4 <|
    seqEmit hinp₀ (hpv V5) h5 <|
    seqEmit hinp₀ (hpv V6) h6 h7).mono_bound (by omega)

end RfindPhaseAProof



section RfindPhaseBProof
variable {af : ℕ}

/-- Reading a node register out of an update to a node register: the index comparison is
    numeric, so `decide` discharges it and a `simp only` evaluates any stage chain. -/
lemma rfSelf_update_apply (i j : Fin 32) (X : Fin (32 + af) → ℕ) (x : ℕ) :
    Function.update X (rfSelf af j) x (rfSelf af i)
      = if (i : ℕ) = (j : ℕ) then x else X (rfSelf af i) := by
  by_cases h : (i : ℕ) = (j : ℕ)
  · rw [if_pos h, Fin.ext h, Function.update_self]
  · rw [if_neg h, Function.update_of_ne (rfSelf_ne_self i j h)]

/-- A child register never collides with a node register. -/
lemma rfLoc_update_apply (haf : 16 ≤ af) (i : Fin 16) (j : Fin 32)
    (X : Fin (32 + af) → ℕ) (x : ℕ) :
    Function.update X (rfSelf af j) x (rfLoc af haf i) = X (rfLoc af haf i) :=
  Function.update_of_ne (Ne.symm (rfSelf_ne_loc haf j i)) x X

/-- Phase B1's `searching`: the incoming flag, the level guard and the child's tag. -/
lemma rfPhaseB1Vals_search (haf : 16 ≤ af) (W : Fin (32 + af) → ℕ) :
    rfPhaseB1Vals af haf W (rfSelf af 9)
      = W (rfSelf af 9) * W (rfSelf af 13) * W (rfLoc af haf 2) := by
  simp only [rfPhaseB1Vals, rfSelf_update_apply, rfLoc_update_apply haf]
  norm_num

/-- Phase B1's `hit`: that, times the zero test. -/
lemma rfPhaseB1Vals_hit (haf : 16 ≤ af) (W : Fin (32 + af) → ℕ) :
    rfPhaseB1Vals af haf W (rfSelf af 15)
      = W (rfSelf af 9) * W (rfSelf af 13) * W (rfLoc af haf 2)
          * (if W (rfLoc af haf 3) < W (rfSelf af 12) then 1 else 0) := by
  simp only [rfPhaseB1Vals, rfSelf_update_apply, rfLoc_update_apply haf]
  norm_num

/-- Phase B1's comparison scratch. -/
lemma rfPhaseB1Vals_scratch (haf : 16 ≤ af) (W : Fin (32 + af) → ℕ) :
    rfPhaseB1Vals af haf W (rfSelf af 5) = W (rfSelf af 12) - W (rfLoc af haf 3) := by
  simp only [rfPhaseB1Vals, rfSelf_update_apply, rfLoc_update_apply haf]
  norm_num

/-- Phase B1's zero test. -/
lemma rfPhaseB1Vals_zero (haf : 16 ≤ af) (W : Fin (32 + af) → ℕ) :
    rfPhaseB1Vals af haf W (rfSelf af 14)
      = if W (rfLoc af haf 3) < W (rfSelf af 12) then 1 else 0 := by
  simp only [rfPhaseB1Vals, rfSelf_update_apply, rfLoc_update_apply haf]
  norm_num

/-- Phase B1's temp: the incoming flag times the level guard. -/
lemma rfPhaseB1Vals_temp (haf : 16 ≤ af) (W : Fin (32 + af) → ℕ) :
    rfPhaseB1Vals af haf W (rfSelf af 17) = W (rfSelf af 9) * W (rfSelf af 13) := by
  simp only [rfPhaseB1Vals, rfSelf_update_apply, rfLoc_update_apply haf]
  norm_num

/-- Phase B1 writes only registers `5`, `9`, `14`, `15` and `17` — of any register at
    all, not merely of the node's own. -/
lemma rfPhaseB1Vals_frame (haf : 16 ≤ af) (W : Fin (32 + af) → ℕ) {k : Fin (32 + af)}
    (h5 : k ≠ rfSelf af 5) (h9 : k ≠ rfSelf af 9) (h14 : k ≠ rfSelf af 14)
    (h15 : k ≠ rfSelf af 15) (h17 : k ≠ rfSelf af 17) :
    rfPhaseB1Vals af haf W k = W k := by
  simp only [rfPhaseB1Vals, Function.update_of_ne h15, Function.update_of_ne h14,
    Function.update_of_ne h5, Function.update_of_ne h9, Function.update_of_ne h17]

/-- Phase B1 keeps every register inside the bound. -/
lemma rfPhaseB1Vals_lt (haf : 16 ≤ af) (W : Fin (32 + af) → ℕ) (B : ℕ) (hB2 : 2 ≤ B)
    (hW : ∀ k, W k < B) (hsearch : W (rfSelf af 9) ≤ 1) (hgflag : W (rfSelf af 13) ≤ 1)
    (htag : W (rfLoc af haf 2) ≤ 1) :
    ∀ k, rfPhaseB1Vals af haf W k < B := by
  have hs : rfPhaseB1Vals af haf W (rfSelf af 9) ≤ 1 := by
    rw [rfPhaseB1Vals_search]
    calc W (rfSelf af 9) * W (rfSelf af 13) * W (rfLoc af haf 2) ≤ 1 * 1 := by
          simpa using Nat.mul_le_mul (by simpa using Nat.mul_le_mul hsearch hgflag) htag
      _ = 1 := by norm_num
  have hh : rfPhaseB1Vals af haf W (rfSelf af 15) ≤ 1 := by
    rw [rfPhaseB1Vals_hit, ← rfPhaseB1Vals_search haf W]
    calc rfPhaseB1Vals af haf W (rfSelf af 9)
            * (if W (rfLoc af haf 3) < W (rfSelf af 12) then 1 else 0)
        ≤ 1 * 1 := Nat.mul_le_mul hs (by split_ifs <;> omega)
      _ = 1 := by norm_num
  intro k
  by_cases h5 : k = rfSelf af 5
  · subst h5; rw [rfPhaseB1Vals_scratch]; have := hW (rfSelf af 12); omega
  by_cases h9 : k = rfSelf af 9
  · subst h9; omega
  by_cases h14 : k = rfSelf af 14
  · subst h14; rw [rfPhaseB1Vals_zero]; split_ifs <;> omega
  by_cases h15 : k = rfSelf af 15
  · subst h15; omega
  by_cases h17 : k = rfSelf af 17
  · subst h17
    rw [rfPhaseB1Vals_temp]
    calc W (rfSelf af 9) * W (rfSelf af 13) ≤ 1 * 1 := Nat.mul_le_mul hsearch hgflag
      _ < B := by omega
  · rw [rfPhaseB1Vals_frame haf W h5 h9 h14 h15 h17]; exact hW k

/-- Phase B1 touches only registers `5`, `9`, `14`, `15` and `17`. -/
lemma rfPhaseB1Vals_of_ne (haf : 16 ≤ af) (W : Fin (32 + af) → ℕ) (i : Fin 32)
    (h5 : (i : ℕ) ≠ 5) (h9 : (i : ℕ) ≠ 9) (h14 : (i : ℕ) ≠ 14) (h15 : (i : ℕ) ≠ 15)
    (h17 : (i : ℕ) ≠ 17) :
    rfPhaseB1Vals af haf W (rfSelf af i) = W (rfSelf af i) := by
  simp [rfPhaseB1Vals, rfSelf_update_apply, rfLoc_update_apply haf, h5, h9, h14, h15, h17]

/-- Phase B1 leaves the child's registers alone. -/
lemma rfPhaseB1Vals_loc (haf : 16 ≤ af) (W : Fin (32 + af) → ℕ) (i : Fin 16) :
    rfPhaseB1Vals af haf W (rfLoc af haf i) = W (rfLoc af haf i) := by
  simp only [rfPhaseB1Vals, rfLoc_update_apply haf]

set_option maxHeartbeats 1000000 in
/-- **`rfPhaseB1` Hoare specification.** The guard, the child's tag and the zero test are
    reduced to two flags: `searching` and `hit`. -/
lemma rfPhaseB1_hoareTime (haf : 16 ≤ af)
    (R : Regs (32 + af) n) (W : Fin (32 + af) → ℕ) (B : ℕ)
    (inp₀ : Tape) (w₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hpark : ∀ i, Parked (w₀ i)) (hB2 : 2 ≤ B)
    (hW : ∀ k, W k < B)
    (hsearch : W (rfSelf af 9) ≤ 1)
    (hgflag : W (rfSelf af 13) ≤ 1)
    (htag : W (rfLoc af haf 2) ≤ 1) :
    (rfPhaseB1 af haf R).HoareTime
      (EmitPred inp₀ (regsWork R w₀ W) ys)
      (EmitPred inp₀ (regsWork R w₀ (rfPhaseB1Vals af haf W)) ys)
      (7 * evalnArithmeticCost B + 6) := by
  have hpv := parked_regsWork R hpark
  have hle : ∀ k, W k ≤ B := fun k => Nat.le_of_lt (hW k)
  have hB0 : 0 < B := by omega
  -- S1: clear the temp
  have h8 := clearRegTM_hoareTime (R (rfSelf af 17)) (W (rfSelf af 17)) inp₀
      (regsWork R w₀ W) ys hinp₀ (fun i _ => hpv W i) (regsWork_apply R w₀ W _)
  rw [regsWork_update] at h8
  replace h8 := h8.mono_bound (regOpTime_le_arith _ B (hle _))
  set V8 := Function.update W (rfSelf af 17) 0 with hV8
  have b8 : ∀ k, V8 k < B := by
    intro k; rw [hV8]; simp only [Function.update_apply]; split_ifs
    · omega
    · exact hW _
  have r8_9 : V8 (rfSelf af 9) = W (rfSelf af 9) := by
    rw [hV8, rfSelf_update_apply]; norm_num
  have r8_13 : V8 (rfSelf af 13) = W (rfSelf af 13) := by
    rw [hV8, rfSelf_update_apply]; norm_num
  -- S2: temp := searching * guard
  have h9 := mulAddIntoTM_hoareTime (R (rfSelf af 9)) (R (rfSelf af 13))
      (R (rfSelf af 17))
      (Regs.ne R (rfSelf_ne_self 9 13 (by decide)))
      (Regs.ne R (rfSelf_ne_self 9 17 (by decide)))
      (Regs.ne R (rfSelf_ne_self 13 17 (by decide)))
      (V8 (rfSelf af 9)) (V8 (rfSelf af 13)) 0
      inp₀ (regsWork R w₀ V8) ys hinp₀ (fun i _ => hpv V8 i)
      (regsWork_apply R w₀ V8 _) (regsWork_apply R w₀ V8 _)
      (by rw [regsWork_apply, hV8, Function.update_self])
  rw [regsWork_update] at h9
  replace h9 := h9.mono_bound
    (mulAddTime_le_arith _ _ 0 B (Nat.le_of_lt (b8 _)) (Nat.le_of_lt (b8 _)) (by omega))
  set V9 := Function.update V8 (rfSelf af 17)
      (0 + V8 (rfSelf af 9) * V8 (rfSelf af 13)) with hV9
  have m9 : V9 (rfSelf af 17) ≤ 1 := by
    rw [hV9, Function.update_self, r8_9, r8_13]
    calc 0 + W (rfSelf af 9) * W (rfSelf af 13) ≤ 1 * 1 := by
          simpa using Nat.mul_le_mul hsearch hgflag
      _ = 1 := by norm_num
  have b9 : ∀ k, V9 k < B := by
    intro k; rw [hV9]; simp only [Function.update_apply]; split_ifs
    · have h := m9; rw [hV9, Function.update_self] at h; omega
    · exact b8 _
  -- S3: clear searching
  have h10 := clearRegTM_hoareTime (R (rfSelf af 9)) (V9 (rfSelf af 9)) inp₀
      (regsWork R w₀ V9) ys hinp₀ (fun i _ => hpv V9 i) (regsWork_apply R w₀ V9 _)
  rw [regsWork_update] at h10
  replace h10 := h10.mono_bound (regOpTime_le_arith _ B (Nat.le_of_lt (b9 _)))
  set V10 := Function.update V9 (rfSelf af 9) 0 with hV10
  have b10 : ∀ k, V10 k < B := by
    intro k; rw [hV10]; simp only [Function.update_apply]; split_ifs
    · omega
    · exact b9 _
  have r10_17 : V10 (rfSelf af 17) ≤ 1 := by
    rw [hV10, rfSelf_update_apply]; norm_num; exact m9
  have r10_L2 : V10 (rfLoc af haf 2) = W (rfLoc af haf 2) := by
    rw [hV10, rfLoc_update_apply haf, hV9, rfLoc_update_apply haf, hV8,
      rfLoc_update_apply haf]
  -- S4: searching := temp * the child's tag
  have h11 := mulAddIntoTM_hoareTime (R (rfSelf af 17)) (R (rfLoc af haf 2))
      (R (rfSelf af 9))
      (Regs.ne R (rfSelf_ne_loc haf 17 2))
      (Regs.ne R (rfSelf_ne_self 17 9 (by decide)))
      (Regs.ne R (Ne.symm (rfSelf_ne_loc haf 9 2)))
      (V10 (rfSelf af 17)) (V10 (rfLoc af haf 2)) 0
      inp₀ (regsWork R w₀ V10) ys hinp₀ (fun i _ => hpv V10 i)
      (regsWork_apply R w₀ V10 _) (regsWork_apply R w₀ V10 _)
      (by rw [regsWork_apply, hV10, Function.update_self])
  rw [regsWork_update] at h11
  replace h11 := h11.mono_bound
    (mulAddTime_le_arith _ _ 0 B (Nat.le_of_lt (b10 _)) (Nat.le_of_lt (b10 _)) (by omega))
  set V11 := Function.update V10 (rfSelf af 9)
      (0 + V10 (rfSelf af 17) * V10 (rfLoc af haf 2)) with hV11
  have m11 : V11 (rfSelf af 9) ≤ 1 := by
    rw [hV11, Function.update_self, r10_L2]
    calc 0 + V10 (rfSelf af 17) * W (rfLoc af haf 2) ≤ 1 * 1 := by
          simpa using Nat.mul_le_mul r10_17 htag
      _ = 1 := by norm_num
  have b11 : ∀ k, V11 k < B := by
    intro k; rw [hV11]; simp only [Function.update_apply]; split_ifs
    · have h := m11; rw [hV11, Function.update_self] at h; omega
    · exact b10 _
  -- S5: the zero test
  have h12 := ltFlagTM_hoareTime (R (rfLoc af haf 3)) (R (rfSelf af 12)) (R (rfSelf af 5))
      (R (rfSelf af 14))
      (Regs.ne R (Ne.symm (rfSelf_ne_loc haf 5 3)))
      (Regs.ne R (rfSelf_ne_self 12 5 (by decide)))
      (Regs.ne R (rfSelf_ne_self 5 14 (by decide)))
      (V11 (rfLoc af haf 3)) (V11 (rfSelf af 12)) (V11 (rfSelf af 5)) (V11 (rfSelf af 14))
      inp₀ (regsWork R w₀ V11) ys hinp₀ (fun i => hpv V11 i)
      (regsWork_apply R w₀ V11 _) (regsWork_apply R w₀ V11 _)
      (regsWork_apply R w₀ V11 _) (regsWork_apply R w₀ V11 _)
  rw [regsWork_update, regsWork_update] at h12
  replace h12 := h12.mono_bound
    (ltFlagTime_le_arith _ _ _ _ B (Nat.le_of_lt (b11 _)) (Nat.le_of_lt (b11 _))
      (Nat.le_of_lt (b11 _)) (Nat.le_of_lt (b11 _)))
  set V12 := Function.update
      (Function.update V11 (rfSelf af 5) (V11 (rfSelf af 12) - V11 (rfLoc af haf 3)))
      (rfSelf af 14) (if V11 (rfLoc af haf 3) < V11 (rfSelf af 12) then 1 else 0)
    with hV12
  have b12 : ∀ k, V12 k < B := by
    intro k; rw [hV12]; simp only [Function.update_apply]
    split_ifs <;> first
      | omega
      | (have := b11 (rfSelf af 12); omega)
      | exact b11 _
  have m12_9 : V12 (rfSelf af 9) ≤ 1 := by
    rw [hV12, rfSelf_update_apply, rfSelf_update_apply]; norm_num; exact m11
  have m12_14 : V12 (rfSelf af 14) ≤ 1 := by
    rw [hV12, Function.update_self]; split_ifs <;> omega
  -- S6: clear hit
  have h13 := clearRegTM_hoareTime (R (rfSelf af 15)) (V12 (rfSelf af 15)) inp₀
      (regsWork R w₀ V12) ys hinp₀ (fun i _ => hpv V12 i) (regsWork_apply R w₀ V12 _)
  rw [regsWork_update] at h13
  replace h13 := h13.mono_bound (regOpTime_le_arith _ B (Nat.le_of_lt (b12 _)))
  set V13 := Function.update V12 (rfSelf af 15) 0 with hV13
  have b13 : ∀ k, V13 k < B := by
    intro k; rw [hV13]; simp only [Function.update_apply]; split_ifs
    · omega
    · exact b12 _
  have m13_9 : V13 (rfSelf af 9) ≤ 1 := by
    rw [hV13, rfSelf_update_apply]; norm_num; exact m12_9
  have m13_14 : V13 (rfSelf af 14) ≤ 1 := by
    rw [hV13, rfSelf_update_apply]; norm_num; exact m12_14
  -- S7: hit := searching * the zero flag
  have h14 := mulAddIntoTM_hoareTime (R (rfSelf af 9)) (R (rfSelf af 14))
      (R (rfSelf af 15))
      (Regs.ne R (rfSelf_ne_self 9 14 (by decide)))
      (Regs.ne R (rfSelf_ne_self 9 15 (by decide)))
      (Regs.ne R (rfSelf_ne_self 14 15 (by decide)))
      (V13 (rfSelf af 9)) (V13 (rfSelf af 14)) 0
      inp₀ (regsWork R w₀ V13) ys hinp₀ (fun i _ => hpv V13 i)
      (regsWork_apply R w₀ V13 _) (regsWork_apply R w₀ V13 _)
      (by rw [regsWork_apply, hV13, Function.update_self])
  rw [regsWork_update] at h14
  replace h14 := h14.mono_bound
    (mulAddTime_le_arith _ _ 0 B (Nat.le_of_lt (b13 _)) (Nat.le_of_lt (b13 _)) (by omega))
  exact (seqEmit hinp₀ (hpv V8) h8 <|
    seqEmit hinp₀ (hpv V9) h9 <|
    seqEmit hinp₀ (hpv V10) h10 <|
    seqEmit hinp₀ (hpv V11) h11 <|
    seqEmit hinp₀ (hpv V12) h12 <|
    seqEmit hinp₀ (hpv V13) h13 h14).mono_bound (by omega)

set_option maxHeartbeats 1000000 in
/-- **`rfPhaseB2` Hoare specification.** The hit folds into `found` and `result`,
    `searching` is narrowed by the zero test, and the level advances. -/
lemma rfPhaseB2_hoareTime (haf : 16 ≤ af)
    (R : Regs (32 + af) n) (X : Fin (32 + af) → ℕ) (B : ℕ)
    (inp₀ : Tape) (w₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hpark : ∀ i, Parked (w₀ i)) (hB2 : 2 ≤ B)
    (hX : ∀ k, X k < B)
    (hhit : X (rfSelf af 15) ≤ 1)
    (hs9 : X (rfSelf af 9) ≤ 1)
    (hm1 : X (rfSelf af 7) + 1 < B)
    (hres : X (rfSelf af 11) + X (rfSelf af 7) < B)
    (hfound : X (rfSelf af 10) + 1 < B) :
    (rfPhaseB2 af haf R).HoareTime
      (EmitPred inp₀ (regsWork R w₀ X) ys)
      (EmitPred inp₀ (regsWork R w₀ (rfPhaseB2Vals af haf X)) ys)
      (9 * evalnArithmeticCost B + 8) := by
  have hpv := parked_regsWork R hpark
  have hle : ∀ k, X k ≤ B := fun k => Nat.le_of_lt (hX k)
  have hB0 : 0 < B := by omega
  -- S1: result += hit * m
  have h15 := mulAddIntoTM_hoareTime (R (rfSelf af 15)) (R (rfSelf af 7))
      (R (rfSelf af 11))
      (Regs.ne R (rfSelf_ne_self 15 7 (by decide)))
      (Regs.ne R (rfSelf_ne_self 15 11 (by decide)))
      (Regs.ne R (rfSelf_ne_self 7 11 (by decide)))
      (X (rfSelf af 15)) (X (rfSelf af 7)) (X (rfSelf af 11))
      inp₀ (regsWork R w₀ X) ys hinp₀ (fun i _ => hpv X i)
      (regsWork_apply R w₀ X _) (regsWork_apply R w₀ X _) (regsWork_apply R w₀ X _)
  rw [regsWork_update] at h15
  replace h15 := h15.mono_bound
    (mulAddTime_le_arith _ _ _ B (hle _) (hle _) (hle _))
  set V15 := Function.update X (rfSelf af 11)
      (X (rfSelf af 11) + X (rfSelf af 15) * X (rfSelf af 7)) with hV15
  have hmul : X (rfSelf af 15) * X (rfSelf af 7) ≤ X (rfSelf af 7) := by
    calc X (rfSelf af 15) * X (rfSelf af 7) ≤ 1 * X (rfSelf af 7) :=
          Nat.mul_le_mul hhit (le_refl _)
      _ = X (rfSelf af 7) := by norm_num
  have b15 : ∀ k, V15 k < B := by
    intro k; rw [hV15]; simp only [Function.update_apply]; split_ifs
    · omega
    · exact hX _
  have r15_15 : V15 (rfSelf af 15) = X (rfSelf af 15) := by
    rw [hV15, rfSelf_update_apply]; norm_num
  have r15_10 : V15 (rfSelf af 10) = X (rfSelf af 10) := by
    rw [hV15, rfSelf_update_apply]; norm_num
  -- S2: found += hit
  have h16 := addIntoTM_hoareTime (R (rfSelf af 15)) (R (rfSelf af 10))
      (Regs.ne R (rfSelf_ne_self 15 10 (by decide)))
      (V15 (rfSelf af 15)) (V15 (rfSelf af 10))
      inp₀ (regsWork R w₀ V15) ys hinp₀ (fun i _ => hpv V15 i)
      (regsWork_apply R w₀ V15 _) (regsWork_apply R w₀ V15 _)
  rw [regsWork_update] at h16
  replace h16 := h16.mono_bound
    (addIntoTime_le_arith _ _ B (Nat.le_of_lt (b15 _)) (Nat.le_of_lt (b15 _)))
  set V16 := Function.update V15 (rfSelf af 10)
      (V15 (rfSelf af 10) + V15 (rfSelf af 15)) with hV16
  have b16 : ∀ k, V16 k < B := by
    intro k; rw [hV16]; simp only [Function.update_apply]; split_ifs
    · rw [r15_10, r15_15]; omega
    · exact b15 _
  -- S3: nz := the constant one
  have h17 := copyIntoTM_hoareTime (R (rfSelf af 12)) (R (rfSelf af 16))
      (Regs.ne R (rfSelf_ne_self 12 16 (by decide)))
      (V16 (rfSelf af 12)) (V16 (rfSelf af 16))
      inp₀ (regsWork R w₀ V16) ys hinp₀ (fun i _ => hpv V16 i)
      (regsWork_apply R w₀ V16 _) (regsWork_apply R w₀ V16 _)
  rw [regsWork_update] at h17
  replace h17 := h17.mono_bound
    (copyIntoTime_le_arith _ _ B (Nat.le_of_lt (b16 _)) (Nat.le_of_lt (b16 _)))
  set V17 := Function.update V16 (rfSelf af 16) (V16 (rfSelf af 12)) with hV17
  have b17 : ∀ k, V17 k < B := by
    intro k; rw [hV17]; simp only [Function.update_apply]; split_ifs <;> exact b16 _
  -- S4: nz := one - the zero flag
  have h18 := subIntoTM_hoareTime (R (rfSelf af 14)) (R (rfSelf af 16))
      (Regs.ne R (rfSelf_ne_self 14 16 (by decide)))
      (V17 (rfSelf af 14)) (V17 (rfSelf af 16))
      inp₀ (regsWork R w₀ V17) ys hinp₀ (fun i _ => hpv V17 i)
      (regsWork_apply R w₀ V17 _) (regsWork_apply R w₀ V17 _)
  rw [regsWork_update] at h18
  replace h18 := h18.mono_bound
    (subIntoTime_le_arith _ _ B (Nat.le_of_lt (b17 _)) (Nat.le_of_lt (b17 _)))
  set V18 := Function.update V17 (rfSelf af 16)
      (V17 (rfSelf af 16) - V17 (rfSelf af 14)) with hV18
  have b18 : ∀ k, V18 k < B := by
    intro k; rw [hV18]; simp only [Function.update_apply]; split_ifs
    · have := b17 (rfSelf af 16); omega
    · exact b17 _
  -- S5: clear the temp
  have h19 := clearRegTM_hoareTime (R (rfSelf af 17)) (V18 (rfSelf af 17)) inp₀
      (regsWork R w₀ V18) ys hinp₀ (fun i _ => hpv V18 i) (regsWork_apply R w₀ V18 _)
  rw [regsWork_update] at h19
  replace h19 := h19.mono_bound (regOpTime_le_arith _ B (Nat.le_of_lt (b18 _)))
  set V19 := Function.update V18 (rfSelf af 17) 0 with hV19
  have b19 : ∀ k, V19 k < B := by
    intro k; rw [hV19]; simp only [Function.update_apply]; split_ifs
    · omega
    · exact b18 _
  have r19_9 : V19 (rfSelf af 9) = X (rfSelf af 9) := by
    simp [hV19, hV18, hV17, hV16, hV15, rfSelf_update_apply]
  have m19_9 : V19 (rfSelf af 9) ≤ 1 := by rw [r19_9]; exact hs9
  -- S6: temp := searching * nz
  have h20 := mulAddIntoTM_hoareTime (R (rfSelf af 9)) (R (rfSelf af 16))
      (R (rfSelf af 17))
      (Regs.ne R (rfSelf_ne_self 9 16 (by decide)))
      (Regs.ne R (rfSelf_ne_self 9 17 (by decide)))
      (Regs.ne R (rfSelf_ne_self 16 17 (by decide)))
      (V19 (rfSelf af 9)) (V19 (rfSelf af 16)) 0
      inp₀ (regsWork R w₀ V19) ys hinp₀ (fun i _ => hpv V19 i)
      (regsWork_apply R w₀ V19 _) (regsWork_apply R w₀ V19 _)
      (by rw [regsWork_apply, hV19, Function.update_self])
  rw [regsWork_update] at h20
  replace h20 := h20.mono_bound
    (mulAddTime_le_arith _ _ 0 B (Nat.le_of_lt (b19 _)) (Nat.le_of_lt (b19 _)) (by omega))
  set V20 := Function.update V19 (rfSelf af 17)
      (0 + V19 (rfSelf af 9) * V19 (rfSelf af 16)) with hV20
  have b20 : ∀ k, V20 k < B := by
    intro k; rw [hV20]; simp only [Function.update_apply]; split_ifs
    · have hb := b19 (rfSelf af 16)
      calc 0 + V19 (rfSelf af 9) * V19 (rfSelf af 16)
          ≤ 1 * V19 (rfSelf af 16) := by
            simpa using Nat.mul_le_mul m19_9 (le_refl (V19 (rfSelf af 16)))
        _ < B := by omega
    · exact b19 _
  -- S7: searching := temp
  have h21 := copyIntoTM_hoareTime (R (rfSelf af 17)) (R (rfSelf af 9))
      (Regs.ne R (rfSelf_ne_self 17 9 (by decide)))
      (V20 (rfSelf af 17)) (V20 (rfSelf af 9))
      inp₀ (regsWork R w₀ V20) ys hinp₀ (fun i _ => hpv V20 i)
      (regsWork_apply R w₀ V20 _) (regsWork_apply R w₀ V20 _)
  rw [regsWork_update] at h21
  replace h21 := h21.mono_bound
    (copyIntoTime_le_arith _ _ B (Nat.le_of_lt (b20 _)) (Nat.le_of_lt (b20 _)))
  set V21 := Function.update V20 (rfSelf af 9) (V20 (rfSelf af 17)) with hV21
  have b21 : ∀ k, V21 k < B := by
    intro k; rw [hV21]; simp only [Function.update_apply]; split_ifs <;> exact b20 _
  have r21_7 : V21 (rfSelf af 7) = X (rfSelf af 7) := by
    simp [hV21, hV20, hV19, hV18, hV17, hV16, hV15, rfSelf_update_apply]
  -- S8: m := m + 1
  have h22 := incRegTM_hoareTime (R (rfSelf af 7)) (V21 (rfSelf af 7)) inp₀
      (regsWork R w₀ V21) ys hinp₀ (fun i _ => hpv V21 i) (regsWork_apply R w₀ V21 _)
  rw [regsWork_update] at h22
  replace h22 := h22.mono_bound (regOpTime_le_arith _ B (Nat.le_of_lt (b21 _)))
  set V22 := Function.update V21 (rfSelf af 7) (V21 (rfSelf af 7) + 1) with hV22
  have b22 : ∀ k, V22 k < B := by
    intro k; rw [hV22]; simp only [Function.update_apply]; split_ifs
    · rw [r21_7]; exact hm1
    · exact b21 _
  -- S9: curFuel := curFuel - 1
  have h23 := decRegTM_hoareTime (R (rfSelf af 8)) (V22 (rfSelf af 8)) inp₀
      (regsWork R w₀ V22) ys hinp₀ (fun i _ => hpv V22 i) (regsWork_apply R w₀ V22 _)
  rw [regsWork_update] at h23
  replace h23 := h23.mono_bound (regOpTime_le_arith _ B (Nat.le_of_lt (b22 _)))
  exact (seqEmit hinp₀ (hpv V15) h15 <|
    seqEmit hinp₀ (hpv V16) h16 <|
    seqEmit hinp₀ (hpv V17) h17 <|
    seqEmit hinp₀ (hpv V18) h18 <|
    seqEmit hinp₀ (hpv V19) h19 <|
    seqEmit hinp₀ (hpv V20) h20 <|
    seqEmit hinp₀ (hpv V21) h21 <|
    seqEmit hinp₀ (hpv V22) h22 h23).mono_bound (by omega)

end RfindPhaseBProof

/-! ### Reading an `rfind'` node's register vector

The same numeric-index mechanism as for a binary node. -/

section RfindReadTools
variable {af : ℕ}

lemma rfLoc_rfLoc_update_apply (haf : 16 ≤ af) (i j : Fin 16)
    (X : Fin (32 + af) → ℕ) (x : ℕ) :
    Function.update X (rfLoc af haf j) x (rfLoc af haf i)
      = if (i : ℕ) = (j : ℕ) then x else X (rfLoc af haf i) := by
  by_cases h : (i : ℕ) = (j : ℕ)
  · rw [if_pos h, Fin.ext h, Function.update_self]
  · rw [if_neg h, Function.update_of_ne (fun e => h (by
      have := congrArg (Fin.val) e
      simpa [rfLoc, shiftEmb_val] using this))]

@[simp] lemma rfSelf_rfLoc_upd (haf : 16 ≤ af) (i : Fin 32) (j : Fin 16)
    (X : Fin (32 + af) → ℕ) (x : ℕ) :
    Function.update X (rfLoc af haf j) x (rfSelf af i) = X (rfSelf af i) :=
  Function.update_of_ne (rfSelf_ne_loc haf i j) x X

/-- The pairing window as a total read-off: slots `20`–`27` of the node's block. -/
lemma rfPairWin_selfW_apply (i : Fin 32) (X : Fin (32 + af) → ℕ) (u : Fin 8 → ℕ) :
    writeWindow (rfPairW af) X u (rfSelf af i)
      = if h : 20 ≤ (i : ℕ) ∧ (i : ℕ) < 28 then u ⟨(i : ℕ) - 20, by omega⟩
        else X (rfSelf af i) := by
  by_cases h : 20 ≤ (i : ℕ) ∧ (i : ℕ) < 28
  · rw [dif_pos h]
    have hid : rfPairW af ⟨(i : ℕ) - 20, by omega⟩ = rfSelf af i := by
      apply Fin.ext
      simp [rfPairW, rfSelf, shiftEmb_val]
      omega
    rw [← hid, writeWindow_apply]
  · rw [dif_neg h]
    refine writeWindow_of_ne _ _ _ (fun t => rfPairW_ne_self t i ?_)
    have := t.isLt
    simp at h ⊢
    omega

lemma rfPairWin_rfLoc (haf : 16 ≤ af) (j : Fin 16) (X : Fin (32 + af) → ℕ)
    (u : Fin 8 → ℕ) :
    writeWindow (rfPairW af) X u (rfLoc af haf j) = X (rfLoc af haf j) :=
  writeWindow_of_ne _ _ _ (fun t => rfPairW_ne_loc haf t j)

/-- The unpairing window as a total read-off: slots `20`–`28`. -/
lemma rfUnpairWin_selfW_apply (i : Fin 32) (X : Fin (32 + af) → ℕ) (u : Fin 9 → ℕ) :
    writeWindow (rfUnpairW af) X u (rfSelf af i)
      = if h : 20 ≤ (i : ℕ) ∧ (i : ℕ) < 29 then u ⟨(i : ℕ) - 20, by omega⟩
        else X (rfSelf af i) := by
  by_cases h : 20 ≤ (i : ℕ) ∧ (i : ℕ) < 29
  · rw [dif_pos h]
    have hid : rfUnpairW af ⟨(i : ℕ) - 20, by omega⟩ = rfSelf af i := by
      apply Fin.ext
      simp [rfUnpairW, rfSelf, shiftEmb_val]
      omega
    rw [← hid, writeWindow_apply]
  · rw [dif_neg h]
    refine writeWindow_of_ne _ _ _ (fun t => rfUnpairW_ne_self t i ?_)
    have := t.isLt
    simp at h ⊢
    omega

lemma rfSub_win_rfLoc (haf : 16 ≤ af) (j : Fin 16) (X : Fin (32 + af) → ℕ)
    (u : Fin af → ℕ) :
    writeWindow (rfSub af) X u (rfLoc af haf j)
      = u ⟨(j : ℕ), by have := j.isLt; omega⟩ := by
  rw [rfLoc_eq haf, writeWindow_apply]

end RfindReadTools

/-! ### `rfind'`: what the child sees, and the level guard -/

section RfindPhaseASem
variable {af : ℕ}

lemma rfPhaseAPair_pairOut (V : Fin (32 + af) → ℕ) :
    rfPhaseAPair af V (rfSelf af 26)
      = Nat.pair (V (rfSelf af 6)) (V (rfSelf af 7)) := by
  simp only [rfPhaseAPair, rfPairWin_selfW_apply, pairVals_apply, rfPairW_zero,
    rfPairW_one, rfSelf_update_apply]
  norm_num

lemma rfPhaseAPair_selfW (V : Fin (32 + af) → ℕ) (i : Fin 32)
    (h : ¬ (20 ≤ (i : ℕ) ∧ (i : ℕ) < 28)) :
    rfPhaseAPair af V (rfSelf af i) = V (rfSelf af i) := by
  have h20 : (i : ℕ) ≠ 20 := by omega
  have h21 : (i : ℕ) ≠ 21 := by omega
  simp only [rfPhaseAPair, rfPairWin_selfW_apply, dif_neg h, rfSelf_update_apply]
  norm_num [h20, h21]

lemma rfPhaseAPair_rfLoc (haf : 16 ≤ af) (V : Fin (32 + af) → ℕ) (j : Fin 16) :
    rfPhaseAPair af V (rfLoc af haf j) = V (rfLoc af haf j) := by
  simp only [rfPhaseAPair, rfPairWin_rfLoc haf, rfLoc_update_apply haf]

/-- The child's input register: this level's `Nat.pair a m`. -/
lemma rfPhaseAPre_childIn_zero (haf : 16 ≤ af) (V : Fin (32 + af) → ℕ) :
    rfPhaseAPre af haf V (rfLoc af haf 0)
      = Nat.pair (V (rfSelf af 6)) (V (rfSelf af 7)) := by
  simp only [rfPhaseAPre, rfSelf_rfLoc_upd haf, rfLoc_rfLoc_update_apply haf]
  norm_num
  exact rfPhaseAPair_pairOut V

/-- The child's fuel register: this level's fuel. -/
lemma rfPhaseAPre_childIn_one (haf : 16 ≤ af) (V : Fin (32 + af) → ℕ) :
    rfPhaseAPre af haf V (rfLoc af haf 1) = V (rfSelf af 8) := by
  simp only [rfPhaseAPre, rfSelf_rfLoc_upd haf, rfLoc_rfLoc_update_apply haf]
  norm_num
  exact rfPhaseAPair_selfW V 8 (by norm_num)

/-- The level guard: `Nat.pair a m < fuel`. -/
lemma rfPhaseAVals_guard_val (haf : 16 ≤ af) (Ff : (Fin af → ℕ) → Fin af → ℕ)
    (V : Fin (32 + af) → ℕ) :
    rfPhaseAVals af haf Ff V (rfSelf af 13)
      = if Nat.pair (V (rfSelf af 6)) (V (rfSelf af 7)) < V (rfSelf af 8) then 1 else 0 := by
  rw [rfPhaseAVals, writeWindow_of_ne _ _ _ (fun t => rfSub_ne_self t 13)]
  simp only [rfPhaseAPre, Function.update_self, rfSelf_rfLoc_upd haf,
    rfPhaseAPair_pairOut, rfPhaseAPair_selfW V 8 (by norm_num)]

end RfindPhaseASem

section RfindPhaseARead
variable {af : ℕ}

/-- Phase A's pre-state writes the pair window and the guard registers `5` and `13`;
    every other node register is untouched. -/
lemma rfPhaseAPre_self (haf : 16 ≤ af) (V : Fin (32 + af) → ℕ) (i : Fin 32)
    (hw : ¬ (20 ≤ (i : ℕ) ∧ (i : ℕ) < 28)) (h5 : (i : ℕ) ≠ 5) (h13 : (i : ℕ) ≠ 13) :
    rfPhaseAPre af haf V (rfSelf af i) = V (rfSelf af i) := by
  simp only [rfPhaseAPre, rfSelf_update_apply, rfSelf_rfLoc_upd haf]
  norm_num [h5, h13]
  exact rfPhaseAPair_selfW V i hw

lemma rfPhaseAVals_self (haf : 16 ≤ af) (Ff : (Fin af → ℕ) → Fin af → ℕ)
    (V : Fin (32 + af) → ℕ) (i : Fin 32)
    (hw : ¬ (20 ≤ (i : ℕ) ∧ (i : ℕ) < 28)) (h5 : (i : ℕ) ≠ 5) (h13 : (i : ℕ) ≠ 13) :
    rfPhaseAVals af haf Ff V (rfSelf af i) = V (rfSelf af i) := by
  rw [rfPhaseAVals, writeWindow_of_ne _ _ _ (fun t => rfSub_ne_self t i),
    rfPhaseAPre_self haf V i hw h5 h13]

/-- Phase A's level guard is a flag. -/
lemma rfPhaseAVals_guard (haf : 16 ≤ af) (Ff : (Fin af → ℕ) → Fin af → ℕ)
    (V : Fin (32 + af) → ℕ) :
    rfPhaseAVals af haf Ff V (rfSelf af 13) ≤ 1 := by
  rw [rfPhaseAVals_guard_val]
  split_ifs <;> omega

/-- Phase A's child registers hold the child's own answer. -/
lemma rfPhaseAVals_child (haf : 16 ≤ af) (Ff : (Fin af → ℕ) → Fin af → ℕ)
    (V : Fin (32 + af) → ℕ) (j : Fin 16) :
    rfPhaseAVals af haf Ff V (rfLoc af haf j)
      = Ff (fun i => rfPhaseAPre af haf V (rfSub af i))
          ⟨(j : ℕ), by have := j.isLt; omega⟩ := by
  rw [rfPhaseAVals, rfLoc_eq haf, writeWindow_apply]

/-- The pairing window keeps every register inside the bound. -/
lemma rfPhaseAPair_lt (V : Fin (32 + af) → ℕ) (B : ℕ) (hB2 : 2 ≤ B) (hV : ∀ k, V k < B)
    (hp : Nat.pair (V (rfSelf af 6)) (V (rfSelf af 7)) < B) :
    ∀ k, rfPhaseAPair af V k < B := by
  simp only [rfPhaseAPair]
  set V1 := Function.update V (rfSelf af 20) (V (rfSelf af 6)) with hV1
  have b1 : ∀ k, V1 k < B := by
    intro k; rw [hV1]; simp only [Function.update_apply]; split_ifs <;> exact hV _
  set V2 := Function.update V1 (rfSelf af 21) (V1 (rfSelf af 7)) with hV2
  have b2 : ∀ k, V2 k < B := by
    intro k; rw [hV2]; simp only [Function.update_apply]; split_ifs <;> exact b1 _
  have hw0 : V2 ((rfPairW af) 0) = V (rfSelf af 6) := by
    rw [rfPairW_zero, hV2, rfSelf_update_apply, hV1, rfSelf_update_apply]; norm_num
  have hw1 : V2 ((rfPairW af) 1) = V (rfSelf af 7) := by
    rw [rfPairW_one, hV2, rfSelf_update_apply, hV1, rfSelf_update_apply]; norm_num
  intro k
  refine writeWindow_bounded _ _ _ B b2 (fun i => ?_) k
  refine pairVals_lt _ B hB2 (fun i => b2 _) ?_ i
  rw [hw0, hw1]; exact hp

/-- Phase A keeps every register inside the bound. -/
lemma rfPhaseAVals_lt (haf : 16 ≤ af) (Ff : (Fin af → ℕ) → Fin af → ℕ)
    (V : Fin (32 + af) → ℕ) (B : ℕ) (hB2 : 2 ≤ B) (hV : ∀ k, V k < B)
    (hp : Nat.pair (V (rfSelf af 6)) (V (rfSelf af 7)) < B)
    (hFfB : ∀ u : Fin af → ℕ, (∀ k, u k < B) → ∀ k, Ff u k < B) :
    ∀ k, rfPhaseAVals af haf Ff V k < B := by
  have b3 := rfPhaseAPair_lt V B hB2 hV hp
  have hpre : ∀ k, rfPhaseAPre af haf V k < B := by
    simp only [rfPhaseAPre]
    set V4 := Function.update (rfPhaseAPair af V) (rfLoc af haf 0)
        (rfPhaseAPair af V (rfSelf af 26)) with hV4
    have b4 : ∀ k, V4 k < B := by
      intro k; rw [hV4]; simp only [Function.update_apply]; split_ifs <;> exact b3 _
    set V5 := Function.update V4 (rfLoc af haf 1) (V4 (rfSelf af 8)) with hV5
    have b5 : ∀ k, V5 k < B := by
      intro k; rw [hV5]; simp only [Function.update_apply]; split_ifs <;> exact b4 _
    intro k
    simp only [Function.update_apply]
    split_ifs <;> first
      | omega
      | (have := b5 (rfSelf af 8); omega)
      | exact b5 _
  intro k
  rw [rfPhaseAVals]
  exact writeWindow_bounded _ _ _ B hpre (fun i => hFfB _ (fun t => hpre _) i) k

end RfindPhaseARead

section RfindBodyCompose
variable {af : ℕ}

lemma rfPhaseB1Vals_search_le_one (haf : 16 ≤ af) (W : Fin (32 + af) → ℕ)
    (hsearch : W (rfSelf af 9) ≤ 1) (hgflag : W (rfSelf af 13) ≤ 1)
    (htag : W (rfLoc af haf 2) ≤ 1) :
    rfPhaseB1Vals af haf W (rfSelf af 9) ≤ 1 := by
  rw [rfPhaseB1Vals_search]
  calc W (rfSelf af 9) * W (rfSelf af 13) * W (rfLoc af haf 2) ≤ 1 * 1 := by
        simpa using Nat.mul_le_mul (by simpa using Nat.mul_le_mul hsearch hgflag) htag
    _ = 1 := by norm_num

lemma rfPhaseB1Vals_hit_le_one (haf : 16 ≤ af) (W : Fin (32 + af) → ℕ)
    (hsearch : W (rfSelf af 9) ≤ 1) (hgflag : W (rfSelf af 13) ≤ 1)
    (htag : W (rfLoc af haf 2) ≤ 1) :
    rfPhaseB1Vals af haf W (rfSelf af 15) ≤ 1 := by
  rw [rfPhaseB1Vals_hit, ← rfPhaseB1Vals_search haf W]
  calc rfPhaseB1Vals af haf W (rfSelf af 9)
          * (if W (rfLoc af haf 3) < W (rfSelf af 12) then 1 else 0)
      ≤ 1 * 1 :=
        Nat.mul_le_mul (rfPhaseB1Vals_search_le_one haf W hsearch hgflag htag)
          (by split_ifs <;> omega)
    _ = 1 := by norm_num

/-- **`rfPhaseB` Hoare specification.** -/
lemma rfPhaseB_hoareTime (haf : 16 ≤ af)
    (R : Regs (32 + af) n) (W : Fin (32 + af) → ℕ) (B : ℕ)
    (inp₀ : Tape) (w₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hpark : ∀ i, Parked (w₀ i)) (hB2 : 2 ≤ B)
    (hW : ∀ k, W k < B)
    (hsearch : W (rfSelf af 9) ≤ 1)
    (hgflag : W (rfSelf af 13) ≤ 1)
    (htag : W (rfLoc af haf 2) ≤ 1)
    (hm1 : W (rfSelf af 7) + 1 < B)
    (hres : W (rfSelf af 11) + W (rfSelf af 7) < B)
    (hfound : W (rfSelf af 10) + 1 < B) :
    (rfPhaseB af haf R).HoareTime
      (EmitPred inp₀ (regsWork R w₀ W) ys)
      (EmitPred inp₀ (regsWork R w₀ (rfPhaseBVals af haf W)) ys)
      (16 * evalnArithmeticCost B + 15) := by
  have h1 := rfPhaseB1_hoareTime haf R W B inp₀ w₀ ys hinp₀ hpark hB2 hW hsearch hgflag htag
  have hb := rfPhaseB1Vals_lt haf W B hB2 hW hsearch hgflag htag
  have f7 : rfPhaseB1Vals af haf W (rfSelf af 7) = W (rfSelf af 7) :=
    rfPhaseB1Vals_frame haf W (rfSelf_ne_self 7 5 (by decide))
      (rfSelf_ne_self 7 9 (by decide)) (rfSelf_ne_self 7 14 (by decide))
      (rfSelf_ne_self 7 15 (by decide)) (rfSelf_ne_self 7 17 (by decide))
  have f10 : rfPhaseB1Vals af haf W (rfSelf af 10) = W (rfSelf af 10) :=
    rfPhaseB1Vals_frame haf W (rfSelf_ne_self 10 5 (by decide))
      (rfSelf_ne_self 10 9 (by decide)) (rfSelf_ne_self 10 14 (by decide))
      (rfSelf_ne_self 10 15 (by decide)) (rfSelf_ne_self 10 17 (by decide))
  have f11 : rfPhaseB1Vals af haf W (rfSelf af 11) = W (rfSelf af 11) :=
    rfPhaseB1Vals_frame haf W (rfSelf_ne_self 11 5 (by decide))
      (rfSelf_ne_self 11 9 (by decide)) (rfSelf_ne_self 11 14 (by decide))
      (rfSelf_ne_self 11 15 (by decide)) (rfSelf_ne_self 11 17 (by decide))
  have h2 := rfPhaseB2_hoareTime haf R (rfPhaseB1Vals af haf W) B inp₀ w₀ ys hinp₀ hpark
    hB2 hb (rfPhaseB1Vals_hit_le_one haf W hsearch hgflag htag)
    (rfPhaseB1Vals_search_le_one haf W hsearch hgflag htag)
    (by rw [f7]; exact hm1) (by rw [f11, f7]; exact hres) (by rw [f10]; exact hfound)
  exact (seqEmit hinp₀ (parked_regsWork R hpark _) h1 h2).mono_bound (by omega)

/-- **`rfBodyTM` Hoare specification.** One level of the search. -/
lemma rfBody_hoareTime (haf : 16 ≤ af)
    (R : Regs (32 + af) n) (Mf : TM n)
    (Ff : (Fin af → ℕ) → Fin af → ℕ) (tf : ℕ)
    (V : Fin (32 + af) → ℕ) (B : ℕ)
    (inp₀ : Tape) (w₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hpark : ∀ i, Parked (w₀ i)) (hB2 : 2 ≤ B)
    (hV : ∀ k, V k < B)
    (hp : Nat.pair (V (rfSelf af 6)) (V (rfSelf af 7)) < B)
    (hsearch : V (rfSelf af 9) ≤ 1)
    (hm1 : V (rfSelf af 7) + 1 < B)
    (hres : V (rfSelf af 11) + V (rfSelf af 7) < B)
    (hfound : V (rfSelf af 10) + 1 < B)
    (hFfB : ∀ u : Fin af → ℕ, (∀ k, u k < B) → ∀ k, Ff u k < B)
    (hFfTag : ∀ u : Fin af → ℕ, Ff u ⟨2, by omega⟩ ≤ 1)
    (hMf : ∀ (Wb : Fin n → Tape) (u : Fin af → ℕ), (∀ i, Parked (Wb i)) → (∀ k, u k < B) →
      Mf.HoareTime (EmitPred inp₀ (regsWork ((rfSub af).trans R) Wb u) ys)
                   (EmitPred inp₀ (regsWork ((rfSub af).trans R) Wb (Ff u)) ys) tf) :
    (rfBodyTM af haf R Mf).HoareTime
      (EmitPred inp₀ (regsWork R w₀ V) ys)
      (EmitPred inp₀ (regsWork R w₀ (rfBodyVals af haf Ff V)) ys)
      (22 * evalnArithmeticCost B + tf + 22) := by
  have hA := rfPhaseA_hoareTime haf R Mf Ff tf V B inp₀ w₀ ys hinp₀ hpark hB2 hV hp hFfB hMf
  have hAb := rfPhaseAVals_lt haf Ff V B hB2 hV hp hFfB
  have a9 : rfPhaseAVals af haf Ff V (rfSelf af 9) = V (rfSelf af 9) :=
    rfPhaseAVals_self haf Ff V 9 (by norm_num) (by norm_num) (by norm_num)
  have a7 : rfPhaseAVals af haf Ff V (rfSelf af 7) = V (rfSelf af 7) :=
    rfPhaseAVals_self haf Ff V 7 (by norm_num) (by norm_num) (by norm_num)
  have a10 : rfPhaseAVals af haf Ff V (rfSelf af 10) = V (rfSelf af 10) :=
    rfPhaseAVals_self haf Ff V 10 (by norm_num) (by norm_num) (by norm_num)
  have a11 : rfPhaseAVals af haf Ff V (rfSelf af 11) = V (rfSelf af 11) :=
    rfPhaseAVals_self haf Ff V 11 (by norm_num) (by norm_num) (by norm_num)
  have atag : rfPhaseAVals af haf Ff V (rfLoc af haf 2) ≤ 1 := by
    rw [rfPhaseAVals_child]
    convert hFfTag (fun i => rfPhaseAPre af haf V (rfSub af i)) using 2
    apply Fin.ext
    simp
  have hB := rfPhaseB_hoareTime haf R (rfPhaseAVals af haf Ff V) B inp₀ w₀ ys hinp₀ hpark
    hB2 hAb (by rw [a9]; exact hsearch) (rfPhaseAVals_guard haf Ff V) atag
    (by rw [a7]; exact hm1) (by rw [a11, a7]; exact hres) (by rw [a10]; exact hfound)
  exact (seqEmit hinp₀ (parked_regsWork R hpark _) hA hB).mono_bound (by omega)

end RfindBodyCompose

/-! ### `rfind'`: one level, semantically

Phase B2's read-offs, then the whole level: the machine's `rfBodyVals` **is** `rfLevel`,
provided the child's registers really hold `evaln` of the child on the level's input. -/

section RfindLevelSem
variable {af : ℕ}

lemma rfPhaseB2Vals_result (haf : 16 ≤ af) (X : Fin (32 + af) → ℕ) :
    rfPhaseB2Vals af haf X (rfSelf af 11)
      = X (rfSelf af 11) + X (rfSelf af 15) * X (rfSelf af 7) := by
  simp only [rfPhaseB2Vals, rfSelf_update_apply]
  norm_num

lemma rfPhaseB2Vals_found (haf : 16 ≤ af) (X : Fin (32 + af) → ℕ) :
    rfPhaseB2Vals af haf X (rfSelf af 10) = X (rfSelf af 10) + X (rfSelf af 15) := by
  simp only [rfPhaseB2Vals, rfSelf_update_apply]
  norm_num

lemma rfPhaseB2Vals_search (haf : 16 ≤ af) (X : Fin (32 + af) → ℕ) :
    rfPhaseB2Vals af haf X (rfSelf af 9)
      = X (rfSelf af 9) * (X (rfSelf af 12) - X (rfSelf af 14)) := by
  simp only [rfPhaseB2Vals, rfSelf_update_apply]
  norm_num

lemma rfPhaseB2Vals_m (haf : 16 ≤ af) (X : Fin (32 + af) → ℕ) :
    rfPhaseB2Vals af haf X (rfSelf af 7) = X (rfSelf af 7) + 1 := by
  simp only [rfPhaseB2Vals, rfSelf_update_apply]
  norm_num

lemma rfPhaseB2Vals_fuel (haf : 16 ≤ af) (X : Fin (32 + af) → ℕ) :
    rfPhaseB2Vals af haf X (rfSelf af 8) = X (rfSelf af 8) - 1 := by
  simp only [rfPhaseB2Vals, rfSelf_update_apply]
  norm_num

/-- Phase B2 writes only `7`–`11`, `16` and `17`. -/
lemma rfPhaseB2Vals_of_ne (haf : 16 ≤ af) (X : Fin (32 + af) → ℕ) (i : Fin 32)
    (h : ¬ (7 ≤ (i : ℕ) ∧ (i : ℕ) ≤ 11)) (h16 : (i : ℕ) ≠ 16) (h17 : (i : ℕ) ≠ 17) :
    rfPhaseB2Vals af haf X (rfSelf af i) = X (rfSelf af i) := by
  have h7 : (i : ℕ) ≠ 7 := by omega
  have h8 : (i : ℕ) ≠ 8 := by omega
  have h9 : (i : ℕ) ≠ 9 := by omega
  have h10 : (i : ℕ) ≠ 10 := by omega
  have h11 : (i : ℕ) ≠ 11 := by omega
  simp only [rfPhaseB2Vals, rfSelf_update_apply]
  norm_num [h7, h8, h9, h10, h11, h16, h17]

/-! #### The level -/

/-- The vector the child is run on at this level. -/
noncomputable def rfChildIn (af : ℕ) (haf : 16 ≤ af) (V : Fin (32 + af) → ℕ) :
    Fin af → ℕ :=
  fun i => rfPhaseAPre af haf V (rfSub af i)

lemma rfChildIn_zero (haf : 16 ≤ af) (V : Fin (32 + af) → ℕ) :
    rfChildIn af haf V ⟨0, by omega⟩
      = Nat.pair (V (rfSelf af 6)) (V (rfSelf af 7)) := by
  have h : rfSub af ⟨0, by omega⟩ = rfLoc af haf 0 := by
    apply Fin.ext; simp [rfSub, rfLoc, shiftEmb_val]
  rw [rfChildIn, h, rfPhaseAPre_childIn_zero]

lemma rfChildIn_one (haf : 16 ≤ af) (V : Fin (32 + af) → ℕ) :
    rfChildIn af haf V ⟨1, by omega⟩ = V (rfSelf af 8) := by
  have h : rfSub af ⟨1, by omega⟩ = rfLoc af haf 1 := by
    apply Fin.ext; simp [rfSub, rfLoc, shiftEmb_val]
  rw [rfChildIn, h, rfPhaseAPre_childIn_one]

/-- This level's `live` flag: still searching, the guard held, and the child answered. -/
noncomputable def rfLive (af : ℕ) (haf : 16 ≤ af) (Ff : (Fin af → ℕ) → Fin af → ℕ)
    (V : Fin (32 + af) → ℕ) : ℕ :=
  V (rfSelf af 9)
    * (if Nat.pair (V (rfSelf af 6)) (V (rfSelf af 7)) < V (rfSelf af 8) then 1 else 0)
    * Ff (rfChildIn af haf V) ⟨2, by omega⟩

/-- This level's zero test on the child's value. -/
noncomputable def rfZero (af : ℕ) (haf : 16 ≤ af) (Ff : (Fin af → ℕ) → Fin af → ℕ)
    (V : Fin (32 + af) → ℕ) : ℕ :=
  if Ff (rfChildIn af haf V) ⟨3, by omega⟩ < V (rfSelf af 12) then 1 else 0

section
variable (haf : 16 ≤ af) (Ff : (Fin af → ℕ) → Fin af → ℕ) (V : Fin (32 + af) → ℕ)

private lemma rfA_self (i : Fin 32) (hw : ¬ (20 ≤ (i : ℕ) ∧ (i : ℕ) < 28))
    (h5 : (i : ℕ) ≠ 5) (h13 : (i : ℕ) ≠ 13) :
    rfPhaseAVals af haf Ff V (rfSelf af i) = V (rfSelf af i) :=
  rfPhaseAVals_self haf Ff V i hw h5 h13

private lemma rfB1_frame (i : Fin 32) (hw : ¬ (20 ≤ (i : ℕ) ∧ (i : ℕ) < 28))
    (h5 : (i : ℕ) ≠ 5) (h9 : (i : ℕ) ≠ 9) (h13 : (i : ℕ) ≠ 13) (h14 : (i : ℕ) ≠ 14)
    (h15 : (i : ℕ) ≠ 15) (h17 : (i : ℕ) ≠ 17) :
    rfPhaseB1Vals af haf (rfPhaseAVals af haf Ff V) (rfSelf af i) = V (rfSelf af i) := by
  rw [rfPhaseB1Vals_of_ne haf _ i h5 h9 h14 h15 h17, rfA_self haf Ff V i hw h5 h13]

lemma rfBodyVals_a : rfBodyVals af haf Ff V (rfSelf af 6) = V (rfSelf af 6) := by
  rw [rfBodyVals, rfPhaseBVals, rfPhaseB2Vals_of_ne haf _ 6 (by norm_num) (by norm_num) (by norm_num),
    rfB1_frame haf Ff V 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)]

lemma rfBodyVals_one : rfBodyVals af haf Ff V (rfSelf af 12) = V (rfSelf af 12) := by
  rw [rfBodyVals, rfPhaseBVals, rfPhaseB2Vals_of_ne haf _ 12 (by norm_num) (by norm_num) (by norm_num),
    rfB1_frame haf Ff V 12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)]

lemma rfBodyVals_m : rfBodyVals af haf Ff V (rfSelf af 7) = V (rfSelf af 7) + 1 := by
  rw [rfBodyVals, rfPhaseBVals, rfPhaseB2Vals_m,
    rfB1_frame haf Ff V 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)]

lemma rfBodyVals_fuel : rfBodyVals af haf Ff V (rfSelf af 8) = V (rfSelf af 8) - 1 := by
  rw [rfBodyVals, rfPhaseBVals, rfPhaseB2Vals_fuel,
    rfB1_frame haf Ff V 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)]

private lemma rfB1_live :
    rfPhaseB1Vals af haf (rfPhaseAVals af haf Ff V) (rfSelf af 9)
      = rfLive af haf Ff V := by
  rw [rfPhaseB1Vals_search, rfLive, rfPhaseAVals_guard_val, rfPhaseAVals_child,
    rfA_self haf Ff V 9 (by norm_num) (by norm_num) (by norm_num)]
  rfl

private lemma rfB1_zero :
    rfPhaseB1Vals af haf (rfPhaseAVals af haf Ff V) (rfSelf af 14)
      = rfZero af haf Ff V := by
  rw [rfPhaseB1Vals_zero, rfZero, rfPhaseAVals_child,
    rfA_self haf Ff V 12 (by norm_num) (by norm_num) (by norm_num)]
  rfl

private lemma rfB1_hit :
    rfPhaseB1Vals af haf (rfPhaseAVals af haf Ff V) (rfSelf af 15)
      = rfLive af haf Ff V * rfZero af haf Ff V := by
  rw [rfPhaseB1Vals_hit, ← rfPhaseB1Vals_search haf (rfPhaseAVals af haf Ff V),
    rfB1_live, ← rfB1_zero]
  rw [rfPhaseB1Vals_zero, rfPhaseAVals_child,
    rfA_self haf Ff V 12 (by norm_num) (by norm_num) (by norm_num)]

lemma rfBodyVals_search :
    rfBodyVals af haf Ff V (rfSelf af 9)
      = rfLive af haf Ff V * (V (rfSelf af 12) - rfZero af haf Ff V) := by
  rw [rfBodyVals, rfPhaseBVals, rfPhaseB2Vals_search, rfB1_live, rfB1_zero,
    rfB1_frame haf Ff V 12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)]

lemma rfBodyVals_found :
    rfBodyVals af haf Ff V (rfSelf af 10)
      = V (rfSelf af 10) + rfLive af haf Ff V * rfZero af haf Ff V := by
  rw [rfBodyVals, rfPhaseBVals, rfPhaseB2Vals_found, rfB1_hit,
    rfB1_frame haf Ff V 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)]

lemma rfBodyVals_result :
    rfBodyVals af haf Ff V (rfSelf af 11)
      = V (rfSelf af 11)
          + rfLive af haf Ff V * rfZero af haf Ff V * V (rfSelf af 7) := by
  rw [rfBodyVals, rfPhaseBVals, rfPhaseB2Vals_result, rfB1_hit,
    rfB1_frame haf Ff V 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num),
    rfB1_frame haf Ff V 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)]

end

end RfindLevelSem

/-! ### `rfind'`, semantically complete

The child's registers hold `evaln` of the child; the loop state after `i` levels is
`rfIter` at level `i`; and after `fuel` levels `rfIter_spec` turns that into
`evaln fuel (rfind' cf)`. -/

section RfindClose
variable {af : ℕ}

/-- The iterate, unfolded from the *right*: the last level runs at fuel `f - t` on index
    `m + t`. -/
lemma rfIter_succ' (cf : Nat.Partrec.Code) (a : ℕ) :
    ∀ (t : ℕ) (st : ℕ × ℕ × ℕ) (f m : ℕ),
      rfIter cf a st f m (t + 1) = rfLevel cf a (rfIter cf a st f m t) (f - t) (m + t) := by
  intro t
  induction t with
  | zero => intro st f m; simp [rfIter_succ]
  | succ k ih =>
    intro st f m
    rw [rfIter_succ, ih (rfLevel cf a st f m) (f - 1) (m + 1), ← rfIter_succ]
    congr 1
    · omega
    · omega

/-- **One level.** The machine's level is `rfLevel`, given a child that encodes `evaln`. -/
lemma rfBodyVals_isLevel (haf : 16 ≤ af) (cf : Nat.Partrec.Code)
    (Ff : (Fin af → ℕ) → Fin af → ℕ) (hFf : ChildEncodes af haf cf Ff)
    (V : Fin (32 + af) → ℕ) (h12 : V (rfSelf af 12) = 1) :
    (rfBodyVals af haf Ff V (rfSelf af 9), rfBodyVals af haf Ff V (rfSelf af 10),
      rfBodyVals af haf Ff V (rfSelf af 11))
      = rfLevel cf (V (rfSelf af 6))
          (V (rfSelf af 9), V (rfSelf af 10), V (rfSelf af 11))
          (V (rfSelf af 8)) (V (rfSelf af 7)) := by
  obtain ⟨htag, hval⟩ := hFf (rfChildIn af haf V)
  rw [rfChildIn_zero, rfChildIn_one] at htag hval
  have hlive : rfLive af haf Ff V
      = V (rfSelf af 9)
        * (if Nat.pair (V (rfSelf af 6)) (V (rfSelf af 7)) < V (rfSelf af 8) then 1 else 0)
        * resultTag (Nat.Partrec.Code.evaln (V (rfSelf af 8)) cf
            (Nat.pair (V (rfSelf af 6)) (V (rfSelf af 7)))) := by
    rw [rfLive, htag]
  have hzero : rfZero af haf Ff V
      = (if resultVal (Nat.Partrec.Code.evaln (V (rfSelf af 8)) cf
            (Nat.pair (V (rfSelf af 6)) (V (rfSelf af 7)))) = 0 then 1 else 0) := by
    rw [rfZero, hval, h12]
    split_ifs with h1 h2 h2 <;> omega
  rw [rfBodyVals_search, rfBodyVals_found, rfBodyVals_result, hlive, hzero, h12]
  simp only [rfLevel]

/-- **The loop invariant.** -/
lemma rfLoopVals_spec (haf : 16 ≤ af) (cf : Nat.Partrec.Code)
    (Ff : (Fin af → ℕ) → Fin af → ℕ) (hFf : ChildEncodes af haf cf Ff)
    (V₀ : Fin (32 + af) → ℕ) (h12 : V₀ (rfSelf af 12) = 1) (i : ℕ) :
    rfLoopVals af haf Ff V₀ i (rfSelf af 6) = V₀ (rfSelf af 6) ∧
      rfLoopVals af haf Ff V₀ i (rfSelf af 7) = V₀ (rfSelf af 7) + i ∧
      rfLoopVals af haf Ff V₀ i (rfSelf af 8) = V₀ (rfSelf af 8) - i ∧
      rfLoopVals af haf Ff V₀ i (rfSelf af 12) = 1 ∧
      (rfLoopVals af haf Ff V₀ i (rfSelf af 9),
        rfLoopVals af haf Ff V₀ i (rfSelf af 10),
        rfLoopVals af haf Ff V₀ i (rfSelf af 11))
        = rfIter cf (V₀ (rfSelf af 6))
            (V₀ (rfSelf af 9), V₀ (rfSelf af 10), V₀ (rfSelf af 11))
            (V₀ (rfSelf af 8)) (V₀ (rfSelf af 7)) i := by
  induction i with
  | zero => simp [h12]
  | succ k ih =>
    obtain ⟨e6, e7, e8, e12, etriple⟩ := ih
    rw [rfLoopVals_succ]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [rfBodyVals_a, e6]
    · rw [rfBodyVals_m, e7]; omega
    · rw [rfBodyVals_fuel, e8]; omega
    · rw [rfBodyVals_one, e12]
    · rw [rfBodyVals_isLevel haf cf Ff hFf _ e12, e6, e7, e8, etriple, rfIter_succ']

end RfindClose

/-! ### `rfind'`: the level keeps every register inside the bound -/

section RfindBodyBound
variable {af : ℕ}

lemma rfPhaseB2Vals_nz (haf : 16 ≤ af) (X : Fin (32 + af) → ℕ) :
    rfPhaseB2Vals af haf X (rfSelf af 16)
      = X (rfSelf af 12) - X (rfSelf af 14) := by
  simp only [rfPhaseB2Vals, rfSelf_update_apply]
  norm_num

lemma rfPhaseB2Vals_temp (haf : 16 ≤ af) (X : Fin (32 + af) → ℕ) :
    rfPhaseB2Vals af haf X (rfSelf af 17)
      = X (rfSelf af 9) * (X (rfSelf af 12) - X (rfSelf af 14)) := by
  simp only [rfPhaseB2Vals, rfSelf_update_apply]
  norm_num

/-- Phase B2 writes only `7`–`11`, `16` and `17` — of any register at all. -/
lemma rfPhaseB2Vals_frame (haf : 16 ≤ af) (X : Fin (32 + af) → ℕ) {k : Fin (32 + af)}
    (h7 : k ≠ rfSelf af 7) (h8 : k ≠ rfSelf af 8) (h9 : k ≠ rfSelf af 9)
    (h10 : k ≠ rfSelf af 10) (h11 : k ≠ rfSelf af 11) (h16 : k ≠ rfSelf af 16)
    (h17 : k ≠ rfSelf af 17) :
    rfPhaseB2Vals af haf X k = X k := by
  simp only [rfPhaseB2Vals, Function.update_of_ne h8, Function.update_of_ne h7,
    Function.update_of_ne h9, Function.update_of_ne h17, Function.update_of_ne h16,
    Function.update_of_ne h10, Function.update_of_ne h11]

lemma rfPhaseB2Vals_lt (haf : 16 ≤ af) (X : Fin (32 + af) → ℕ) (B : ℕ)
    (hX : ∀ k, X k < B)
    (hhit : X (rfSelf af 15) ≤ 1) (hs9 : X (rfSelf af 9) ≤ 1)
    (hm1 : X (rfSelf af 7) + 1 < B)
    (hres : X (rfSelf af 11) + X (rfSelf af 7) < B)
    (hfound : X (rfSelf af 10) + 1 < B) :
    ∀ k, rfPhaseB2Vals af haf X k < B := by
  have hmul : X (rfSelf af 15) * X (rfSelf af 7) ≤ X (rfSelf af 7) := by
    calc X (rfSelf af 15) * X (rfSelf af 7) ≤ 1 * X (rfSelf af 7) :=
          Nat.mul_le_mul hhit (le_refl _)
      _ = X (rfSelf af 7) := by norm_num
  intro k
  by_cases h7 : k = rfSelf af 7
  · subst h7; rw [rfPhaseB2Vals_m]; exact hm1
  by_cases h8 : k = rfSelf af 8
  · subst h8; rw [rfPhaseB2Vals_fuel]; have := hX (rfSelf af 8); omega
  by_cases h9 : k = rfSelf af 9
  · subst h9
    rw [rfPhaseB2Vals_search]
    have hb := hX (rfSelf af 12)
    calc X (rfSelf af 9) * (X (rfSelf af 12) - X (rfSelf af 14))
        ≤ 1 * (X (rfSelf af 12) - X (rfSelf af 14)) :=
          Nat.mul_le_mul hs9 (le_refl _)
      _ < B := by omega
  by_cases h10 : k = rfSelf af 10
  · subst h10; rw [rfPhaseB2Vals_found]; omega
  by_cases h11 : k = rfSelf af 11
  · subst h11; rw [rfPhaseB2Vals_result]; omega
  by_cases h16 : k = rfSelf af 16
  · subst h16; rw [rfPhaseB2Vals_nz]; have := hX (rfSelf af 12); omega
  by_cases h17 : k = rfSelf af 17
  · subst h17
    rw [rfPhaseB2Vals_temp]
    have hb := hX (rfSelf af 12)
    calc X (rfSelf af 9) * (X (rfSelf af 12) - X (rfSelf af 14))
        ≤ 1 * (X (rfSelf af 12) - X (rfSelf af 14)) :=
          Nat.mul_le_mul hs9 (le_refl _)
      _ < B := by omega
  · rw [rfPhaseB2Vals_frame haf X h7 h8 h9 h10 h11 h16 h17]; exact hX k

/-- **The level keeps every register inside the bound.** -/
lemma rfBodyVals_lt (haf : 16 ≤ af) (Ff : (Fin af → ℕ) → Fin af → ℕ)
    (V : Fin (32 + af) → ℕ) (B : ℕ) (hB2 : 2 ≤ B) (hV : ∀ k, V k < B)
    (hp : Nat.pair (V (rfSelf af 6)) (V (rfSelf af 7)) < B)
    (hsearch : V (rfSelf af 9) ≤ 1)
    (hm1 : V (rfSelf af 7) + 1 < B)
    (hres : V (rfSelf af 11) + V (rfSelf af 7) < B)
    (hfound : V (rfSelf af 10) + 1 < B)
    (hFfB : ∀ u : Fin af → ℕ, (∀ k, u k < B) → ∀ k, Ff u k < B)
    (hFfTag : ∀ u : Fin af → ℕ, Ff u ⟨2, by omega⟩ ≤ 1) :
    ∀ k, rfBodyVals af haf Ff V k < B := by
  have hAb := rfPhaseAVals_lt haf Ff V B hB2 hV hp hFfB
  have a9 : rfPhaseAVals af haf Ff V (rfSelf af 9) = V (rfSelf af 9) :=
    rfPhaseAVals_self haf Ff V 9 (by norm_num) (by norm_num) (by norm_num)
  have a7 : rfPhaseAVals af haf Ff V (rfSelf af 7) = V (rfSelf af 7) :=
    rfPhaseAVals_self haf Ff V 7 (by norm_num) (by norm_num) (by norm_num)
  have a10 : rfPhaseAVals af haf Ff V (rfSelf af 10) = V (rfSelf af 10) :=
    rfPhaseAVals_self haf Ff V 10 (by norm_num) (by norm_num) (by norm_num)
  have a11 : rfPhaseAVals af haf Ff V (rfSelf af 11) = V (rfSelf af 11) :=
    rfPhaseAVals_self haf Ff V 11 (by norm_num) (by norm_num) (by norm_num)
  have atag : rfPhaseAVals af haf Ff V (rfLoc af haf 2) ≤ 1 := by
    rw [rfPhaseAVals_child]
    convert hFfTag (fun i => rfPhaseAPre af haf V (rfSub af i)) using 2
    apply Fin.ext
    simp
  have hB1b := rfPhaseB1Vals_lt haf (rfPhaseAVals af haf Ff V) B hB2 hAb
    (by rw [a9]; exact hsearch) (rfPhaseAVals_guard haf Ff V) atag
  have f7 : rfPhaseB1Vals af haf (rfPhaseAVals af haf Ff V) (rfSelf af 7)
      = V (rfSelf af 7) := by
    rw [rfPhaseB1Vals_frame haf _ (rfSelf_ne_self 7 5 (by decide))
      (rfSelf_ne_self 7 9 (by decide)) (rfSelf_ne_self 7 14 (by decide))
      (rfSelf_ne_self 7 15 (by decide)) (rfSelf_ne_self 7 17 (by decide)), a7]
  have f10 : rfPhaseB1Vals af haf (rfPhaseAVals af haf Ff V) (rfSelf af 10)
      = V (rfSelf af 10) := by
    rw [rfPhaseB1Vals_frame haf _ (rfSelf_ne_self 10 5 (by decide))
      (rfSelf_ne_self 10 9 (by decide)) (rfSelf_ne_self 10 14 (by decide))
      (rfSelf_ne_self 10 15 (by decide)) (rfSelf_ne_self 10 17 (by decide)), a10]
  have f11 : rfPhaseB1Vals af haf (rfPhaseAVals af haf Ff V) (rfSelf af 11)
      = V (rfSelf af 11) := by
    rw [rfPhaseB1Vals_frame haf _ (rfSelf_ne_self 11 5 (by decide))
      (rfSelf_ne_self 11 9 (by decide)) (rfSelf_ne_self 11 14 (by decide))
      (rfSelf_ne_self 11 15 (by decide)) (rfSelf_ne_self 11 17 (by decide)), a11]
  exact rfPhaseB2Vals_lt haf (rfPhaseB1Vals af haf (rfPhaseAVals af haf Ff V)) B hB1b
    (rfPhaseB1Vals_hit_le_one haf _ (by rw [a9]; exact hsearch)
      (rfPhaseAVals_guard haf Ff V) atag)
    (rfPhaseB1Vals_search_le_one haf _ (by rw [a9]; exact hsearch)
      (rfPhaseAVals_guard haf Ff V) atag)
    (by rw [f7]; exact hm1) (by rw [f11, f7]; exact hres) (by rw [f10]; exact hfound)

end RfindBodyBound

/-! ## `rfind'`: the setup and finish phases

Setup unpairs the input into `a` and `m`, seeds the search state — `searching := 1`,
`found := 0`, `result := 0` — installs the constant `1`, and copies the fuel into the loop
counter. Finish reads the two answer registers out. -/

section RfindSetup
variable {af : ℕ}

def rfSetupTM (af : ℕ) (haf : 16 ≤ af) (R : Regs (32 + af) n) (l : Fin n) : TM n :=
  seqTM (unpairTM ((rfUnpairW af).trans R) (R (rfSelf af 0))) <|
  seqTM (copyIntoTM (R (rfSelf af 20)) (R (rfSelf af 6))) <|
  seqTM (copyIntoTM (R (rfSelf af 21)) (R (rfSelf af 7))) <|
  seqTM (copyIntoTM (R (rfSelf af 1)) (R (rfSelf af 8))) <|
  seqTM (setOneTM (R (rfSelf af 9))) <|
  seqTM (clearRegTM (R (rfSelf af 10))) <|
  seqTM (clearRegTM (R (rfSelf af 11))) <|
  seqTM (setOneTM (R (rfSelf af 12)))
        (copyIntoTM (R (rfSelf af 1)) l)

noncomputable def rfSetupVals (af : ℕ) (haf : 16 ≤ af) (V : Fin (32 + af) → ℕ) :
    Fin (32 + af) → ℕ :=
  let U1 := writeWindow (rfUnpairW af) V
              (unpairVals (fun j => V (rfUnpairW af j)) (V (rfSelf af 0)))
  let U2 := Function.update U1 (rfSelf af 6) (U1 (rfSelf af 20))
  let U3 := Function.update U2 (rfSelf af 7) (U2 (rfSelf af 21))
  let U4 := Function.update U3 (rfSelf af 8) (U3 (rfSelf af 1))
  let U5 := Function.update U4 (rfSelf af 9) 1
  let U6 := Function.update U5 (rfSelf af 10) 0
  let U7 := Function.update U6 (rfSelf af 11) 0
  Function.update U7 (rfSelf af 12) 1

set_option maxHeartbeats 1000000 in
/-- **`rfSetupTM` Hoare specification.** -/
lemma rfSetup_hoareTime (haf : 16 ≤ af)
    (R : Regs (32 + af) n) (l : Fin n) (hl : ∀ k, R k ≠ l)
    (V : Fin (32 + af) → ℕ) (B : ℕ)
    (inp₀ : Tape) (w₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hpark : ∀ i, Parked (w₀ i))
    (cl : ℕ) (hlc : w₀ l = regTape cl) (hclB : cl ≤ B)
    (hB2 : 2 ≤ B) (hV : ∀ k, V k < B) :
    (rfSetupTM af haf R l).HoareTime
      (EmitPred inp₀ (regsWork R w₀ V) ys)
      (EmitPred inp₀
        (regsWork R
          (Function.update w₀ l (regTape (rfSetupVals af haf V (rfSelf af 1))))
          (rfSetupVals af haf V)) ys)
      (9 * evalnArithmeticCost B + 8) := by
  have hpv := parked_regsWork R hpark
  have hle : ∀ k, V k ≤ B := fun k => Nat.le_of_lt (hV k)
  have hB0 : 0 < B := by omega
  -- S1: unpair the input
  have h1 := unpairTM_hoareTime_arith ((rfUnpairW af).trans R) (R (rfSelf af 0))
      (fun k h => rfUnpairW_ne_self k 0 (by have := k.isLt; omega) (R.injective h))
      (fun j => V (rfUnpairW af j)) (V (rfSelf af 0)) B inp₀
      (regsWork R w₀ V) ys hinp₀ (hpv V)
      (regsWork_apply R w₀ V _) (hle _) (fun k => hle _)
  rw [← regsWork_restrict, regsWork_window] at h1
  set V1 := writeWindow (rfUnpairW af) V
      (unpairVals (fun j => V (rfUnpairW af j)) (V (rfSelf af 0))) with hV1
  have b1 : ∀ k, V1 k < B := by
    intro k; rw [hV1]
    refine writeWindow_bounded _ _ _ B hV (fun j => ?_) k
    have := unpairVals_bounded (fun j => V (rfUnpairW af j)) (B - 1)
      (fun i => by have := hV (rfUnpairW af i); omega) (V (rfSelf af 0))
      (by have := hV (rfSelf af 0); omega) j
    omega
  -- S2: a := the left component
  have h2 := copyIntoTM_hoareTime (R (rfSelf af 20)) (R (rfSelf af 6))
      (Regs.ne R (rfSelf_ne_self 20 6 (by decide)))
      (V1 (rfSelf af 20)) (V1 (rfSelf af 6))
      inp₀ (regsWork R w₀ V1) ys hinp₀ (fun i _ => hpv V1 i)
      (regsWork_apply R w₀ V1 _) (regsWork_apply R w₀ V1 _)
  rw [regsWork_update] at h2
  replace h2 := h2.mono_bound
    (copyIntoTime_le_arith _ _ B (Nat.le_of_lt (b1 _)) (Nat.le_of_lt (b1 _)))
  set V2 := Function.update V1 (rfSelf af 6) (V1 (rfSelf af 20)) with hV2
  have b2 : ∀ k, V2 k < B := by
    intro k; rw [hV2]; simp only [Function.update_apply]; split_ifs <;> exact b1 _
  -- S3: m := the right component
  have h3 := copyIntoTM_hoareTime (R (rfSelf af 21)) (R (rfSelf af 7))
      (Regs.ne R (rfSelf_ne_self 21 7 (by decide)))
      (V2 (rfSelf af 21)) (V2 (rfSelf af 7))
      inp₀ (regsWork R w₀ V2) ys hinp₀ (fun i _ => hpv V2 i)
      (regsWork_apply R w₀ V2 _) (regsWork_apply R w₀ V2 _)
  rw [regsWork_update] at h3
  replace h3 := h3.mono_bound
    (copyIntoTime_le_arith _ _ B (Nat.le_of_lt (b2 _)) (Nat.le_of_lt (b2 _)))
  set V3 := Function.update V2 (rfSelf af 7) (V2 (rfSelf af 21)) with hV3
  have b3 : ∀ k, V3 k < B := by
    intro k; rw [hV3]; simp only [Function.update_apply]; split_ifs <;> exact b2 _
  -- S4: curFuel := fuel
  have h4 := copyIntoTM_hoareTime (R (rfSelf af 1)) (R (rfSelf af 8))
      (Regs.ne R (rfSelf_ne_self 1 8 (by decide)))
      (V3 (rfSelf af 1)) (V3 (rfSelf af 8))
      inp₀ (regsWork R w₀ V3) ys hinp₀ (fun i _ => hpv V3 i)
      (regsWork_apply R w₀ V3 _) (regsWork_apply R w₀ V3 _)
  rw [regsWork_update] at h4
  replace h4 := h4.mono_bound
    (copyIntoTime_le_arith _ _ B (Nat.le_of_lt (b3 _)) (Nat.le_of_lt (b3 _)))
  set V4 := Function.update V3 (rfSelf af 8) (V3 (rfSelf af 1)) with hV4
  have b4 : ∀ k, V4 k < B := by
    intro k; rw [hV4]; simp only [Function.update_apply]; split_ifs <;> exact b3 _
  -- S5: searching := 1
  have h5 := setOneTM_hoareTime (R (rfSelf af 9)) (V4 (rfSelf af 9)) inp₀
      (regsWork R w₀ V4) ys hinp₀ (fun i _ => hpv V4 i) (regsWork_apply R w₀ V4 _)
  rw [regsWork_update] at h5
  replace h5 := h5.mono_bound (setOneTime_le_arith _ B (Nat.le_of_lt (b4 _)))
  set V5 := Function.update V4 (rfSelf af 9) 1 with hV5
  have b5 : ∀ k, V5 k < B := by
    intro k; rw [hV5]; simp only [Function.update_apply]; split_ifs
    · omega
    · exact b4 _
  -- S6: found := 0
  have h6 := clearRegTM_hoareTime (R (rfSelf af 10)) (V5 (rfSelf af 10)) inp₀
      (regsWork R w₀ V5) ys hinp₀ (fun i _ => hpv V5 i) (regsWork_apply R w₀ V5 _)
  rw [regsWork_update] at h6
  replace h6 := h6.mono_bound (regOpTime_le_arith _ B (Nat.le_of_lt (b5 _)))
  set V6 := Function.update V5 (rfSelf af 10) 0 with hV6
  have b6 : ∀ k, V6 k < B := by
    intro k; rw [hV6]; simp only [Function.update_apply]; split_ifs
    · omega
    · exact b5 _
  -- S7: result := 0
  have h7 := clearRegTM_hoareTime (R (rfSelf af 11)) (V6 (rfSelf af 11)) inp₀
      (regsWork R w₀ V6) ys hinp₀ (fun i _ => hpv V6 i) (regsWork_apply R w₀ V6 _)
  rw [regsWork_update] at h7
  replace h7 := h7.mono_bound (regOpTime_le_arith _ B (Nat.le_of_lt (b6 _)))
  set V7 := Function.update V6 (rfSelf af 11) 0 with hV7
  have b7 : ∀ k, V7 k < B := by
    intro k; rw [hV7]; simp only [Function.update_apply]; split_ifs
    · omega
    · exact b6 _
  -- S8: the constant one
  have h8 := setOneTM_hoareTime (R (rfSelf af 12)) (V7 (rfSelf af 12)) inp₀
      (regsWork R w₀ V7) ys hinp₀ (fun i _ => hpv V7 i) (regsWork_apply R w₀ V7 _)
  rw [regsWork_update] at h8
  replace h8 := h8.mono_bound (setOneTime_le_arith _ B (Nat.le_of_lt (b7 _)))
  set V8 := Function.update V7 (rfSelf af 12) 1 with hV8
  have b8 : ∀ k, V8 k < B := by
    intro k; rw [hV8]; simp only [Function.update_apply]; split_ifs
    · omega
    · exact b7 _
  -- S9: the loop counter, an ambient register outside the block
  have h9 := copyIntoTM_hoareTime (R (rfSelf af 1)) l (hl _)
      (V8 (rfSelf af 1)) cl
      inp₀ (regsWork R w₀ V8) ys hinp₀ (fun i _ => hpv V8 i)
      (regsWork_apply R w₀ V8 _)
      (by rw [regsWork_of_ne _ _ _ hl]; exact hlc)
  rw [← regsWork_update_of_ne R w₀ V8 hl] at h9
  replace h9 := h9.mono_bound
    (copyIntoTime_le_arith _ cl B (Nat.le_of_lt (b8 _)) hclB)
  exact (seqEmit hinp₀ (hpv V1) h1 <|
    seqEmit hinp₀ (hpv V2) h2 <|
    seqEmit hinp₀ (hpv V3) h3 <|
    seqEmit hinp₀ (hpv V4) h4 <|
    seqEmit hinp₀ (hpv V5) h5 <|
    seqEmit hinp₀ (hpv V6) h6 <|
    seqEmit hinp₀ (hpv V7) h7 <|
    seqEmit hinp₀ (hpv V8) h8 h9).mono_bound (by omega)

/-! ### The finish -/

def rfFinishTM (af : ℕ) (R : Regs (32 + af) n) : TM n :=
  seqTM (copyIntoTM (R (rfSelf af 10)) (R (rfSelf af 2)))
        (copyIntoTM (R (rfSelf af 11)) (R (rfSelf af 3)))

noncomputable def rfFinishVals (af : ℕ) (W : Fin (32 + af) → ℕ) : Fin (32 + af) → ℕ :=
  let W1 := Function.update W (rfSelf af 2) (W (rfSelf af 10))
  Function.update W1 (rfSelf af 3) (W1 (rfSelf af 11))

lemma rfFinish_hoareTime (R : Regs (32 + af) n) (W : Fin (32 + af) → ℕ) (B : ℕ)
    (inp₀ : Tape) (w₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hpark : ∀ i, Parked (w₀ i)) (hW : ∀ k, W k < B) :
    (rfFinishTM af R).HoareTime
      (EmitPred inp₀ (regsWork R w₀ W) ys)
      (EmitPred inp₀ (regsWork R w₀ (rfFinishVals af W)) ys)
      (2 * evalnArithmeticCost B + 1) := by
  have hpv := parked_regsWork R hpark
  have hle : ∀ k, W k ≤ B := fun k => Nat.le_of_lt (hW k)
  have h1 := copyIntoTM_hoareTime (R (rfSelf af 10)) (R (rfSelf af 2))
      (Regs.ne R (rfSelf_ne_self 10 2 (by decide)))
      (W (rfSelf af 10)) (W (rfSelf af 2))
      inp₀ (regsWork R w₀ W) ys hinp₀ (fun i _ => hpv W i)
      (regsWork_apply R w₀ W _) (regsWork_apply R w₀ W _)
  rw [regsWork_update] at h1
  replace h1 := h1.mono_bound (copyIntoTime_le_arith _ _ B (hle _) (hle _))
  set W1 := Function.update W (rfSelf af 2) (W (rfSelf af 10)) with hW1
  have b1 : ∀ k, W1 k < B := by
    intro k; rw [hW1]; simp only [Function.update_apply]; split_ifs <;> exact hW _
  have h2 := copyIntoTM_hoareTime (R (rfSelf af 11)) (R (rfSelf af 3))
      (Regs.ne R (rfSelf_ne_self 11 3 (by decide)))
      (W1 (rfSelf af 11)) (W1 (rfSelf af 3))
      inp₀ (regsWork R w₀ W1) ys hinp₀ (fun i _ => hpv W1 i)
      (regsWork_apply R w₀ W1 _) (regsWork_apply R w₀ W1 _)
  rw [regsWork_update] at h2
  replace h2 := h2.mono_bound
    (copyIntoTime_le_arith _ _ B (Nat.le_of_lt (b1 _)) (Nat.le_of_lt (b1 _)))
  exact (seqEmit hinp₀ (hpv W1) h1 h2).mono_bound (by omega)

end RfindSetup

/-! ## `rfind'`, assembled

Setup, then a fixed-length loop of `fuel` levels off a counter outside the block, then the
finish. -/

section RfindCompose
variable {af : ℕ}

/-- The body's side conditions, at one loop state. -/
def RfBodyOK (af B : ℕ) (haf : 16 ≤ af) (V : Fin (32 + af) → ℕ) : Prop :=
  (∀ k, V k < B) ∧ Nat.pair (V (rfSelf af 6)) (V (rfSelf af 7)) < B ∧
    V (rfSelf af 9) ≤ 1 ∧ V (rfSelf af 7) + 1 < B ∧
    V (rfSelf af 11) + V (rfSelf af 7) < B ∧ V (rfSelf af 10) + 1 < B

/-- **The `rfind'` loop.** -/
lemma rfLoop_hoareTime (haf : 16 ≤ af)
    (R : Regs (32 + af) n) (l : Fin n) (hl : ∀ k, R k ≠ l) (Mf : TM n)
    (Ff : (Fin af → ℕ) → Fin af → ℕ) (tf B t : ℕ)
    (V₀ : Fin (32 + af) → ℕ)
    (inp₀ : Tape) (w₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hpark : ∀ i, Parked (w₀ i)) (hB2 : 2 ≤ B)
    (hw₀l : w₀ l = regTape t)
    (hFfB : ∀ u : Fin af → ℕ, (∀ k, u k < B) → ∀ k, Ff u k < B)
    (hFfTag : ∀ u : Fin af → ℕ, Ff u ⟨2, by omega⟩ ≤ 1)
    (hOK : ∀ i, i < t → RfBodyOK af B haf (rfLoopVals af haf Ff V₀ i))
    (hMf : ∀ (Wb : Fin n → Tape) (u : Fin af → ℕ), (∀ i, Parked (Wb i)) → (∀ k, u k < B) →
      Mf.HoareTime (EmitPred inp₀ (regsWork ((rfSub af).trans R) Wb u) ys)
                   (EmitPred inp₀ (regsWork ((rfSub af).trans R) Wb (Ff u)) ys) tf) :
    (forRegTM (rfBodyTM af haf R Mf) l).HoareTime
      (EmitPred inp₀ (regsWork R w₀ V₀) ys)
      (EmitPred inp₀ (regsWork R w₀ (rfLoopVals af haf Ff V₀ t)) ys)
      (t * ((22 * evalnArithmeticCost B + tf + 22) + 2) + (t + 2)) := by
  refine forRegs_hoareTime R (rfBodyTM af haf R Mf) l hl t
    (22 * evalnArithmeticCost B + tf + 22) (rfLoopVals af haf Ff V₀) inp₀ w₀ ys hinp₀
    hpark hw₀l ?_
  intro i hi w hw
  obtain ⟨hb, hp, hs, hm1, hres, hfound⟩ := hOK i hi
  rw [rfLoopVals_succ]
  exact rfBody_hoareTime haf R Mf Ff tf (rfLoopVals af haf Ff V₀ i) B inp₀ w ys hinp₀ hw
    hB2 hb hp hs hm1 hres hfound hFfB hFfTag hMf

def rfindTM (af : ℕ) (haf : 16 ≤ af) (R : Regs (32 + af) n) (l : Fin n) (Mf : TM n) :
    TM n :=
  seqTM (rfSetupTM af haf R l)
    (seqTM (forRegTM (rfBodyTM af haf R Mf) l) (rfFinishTM af R))

/-- The register vector the whole `rfind'` node produces. -/
noncomputable def rfindVals (af : ℕ) (haf : 16 ≤ af)
    (Ff : (Fin af → ℕ) → Fin af → ℕ) (V : Fin (32 + af) → ℕ) : Fin (32 + af) → ℕ :=
  rfFinishVals af
    (rfLoopVals af haf Ff (rfSetupVals af haf V) (rfSetupVals af haf V (rfSelf af 1)))

set_option maxHeartbeats 1000000 in
/-- **`rfind'`, complete.** -/
lemma rfindTM_hoareTime (haf : 16 ≤ af)
    (R : Regs (32 + af) n) (l : Fin n) (hl : ∀ k, R k ≠ l) (Mf : TM n)
    (Ff : (Fin af → ℕ) → Fin af → ℕ) (tf B : ℕ)
    (V : Fin (32 + af) → ℕ)
    (inp₀ : Tape) (w₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hpark : ∀ i, Parked (w₀ i))
    (cl : ℕ) (hlc : w₀ l = regTape cl) (hclB : cl ≤ B)
    (hB2 : 2 ≤ B) (hV : ∀ k, V k < B)
    (hFfB : ∀ u : Fin af → ℕ, (∀ k, u k < B) → ∀ k, Ff u k < B)
    (hFfTag : ∀ u : Fin af → ℕ, Ff u ⟨2, by omega⟩ ≤ 1)
    (hOK : ∀ i, i ≤ rfSetupVals af haf V (rfSelf af 1) →
      RfBodyOK af B haf (rfLoopVals af haf Ff (rfSetupVals af haf V) i))
    (hMf : ∀ (Wb : Fin n → Tape) (u : Fin af → ℕ), (∀ i, Parked (Wb i)) → (∀ k, u k < B) →
      Mf.HoareTime (EmitPred inp₀ (regsWork ((rfSub af).trans R) Wb u) ys)
                   (EmitPred inp₀ (regsWork ((rfSub af).trans R) Wb (Ff u)) ys) tf) :
    (rfindTM af haf R l Mf).HoareTime
      (EmitPred inp₀ (regsWork R w₀ V) ys)
      (EmitPred inp₀
        (regsWork R
          (Function.update w₀ l (regTape (rfSetupVals af haf V (rfSelf af 1))))
          (rfindVals af haf Ff V)) ys)
      ((9 * evalnArithmeticCost B + 8) + 1 +
        ((rfSetupVals af haf V (rfSelf af 1)) *
            ((22 * evalnArithmeticCost B + tf + 22) + 2) +
          ((rfSetupVals af haf V (rfSelf af 1)) + 2) + 1 +
          (2 * evalnArithmeticCost B + 1))) := by
  set S := rfSetupVals af haf V with hS
  set t := S (rfSelf af 1) with ht
  set w₁ := Function.update w₀ l (regTape t) with hw₁
  have hpark₁ : ∀ i, Parked (w₁ i) := by
    intro i; rw [hw₁]
    by_cases hi : i = l
    · subst hi; rw [Function.update_self]; exact parked_regTape _
    · rw [Function.update_of_ne hi]; exact hpark i
  have hsetup := rfSetup_hoareTime haf R l hl V B inp₀ w₀ ys hinp₀ hpark cl hlc hclB
    hB2 hV
  have hloop := rfLoop_hoareTime (af := af) haf R l hl Mf Ff tf B t S inp₀ w₁ ys hinp₀
    hpark₁ hB2 (by rw [hw₁, Function.update_self]) hFfB hFfTag
    (fun i hi => hOK i (Nat.le_of_lt hi)) hMf
  obtain ⟨hLb, -, -, -, -, -⟩ := hOK t le_rfl
  have hfin := rfFinish_hoareTime (af := af) R (rfLoopVals af haf Ff S t) B inp₀ w₁ ys
    hinp₀ hpark₁ hLb
  exact seqEmit hinp₀ (parked_regsWork R hpark₁ S) hsetup
    (seqEmit hinp₀ (parked_regsWork R hpark₁ _) hloop hfin)

end RfindCompose

/-! ### `rfind'`: the setup and finish, read off -/

section RfindCloseTwo
variable {af : ℕ}

lemma rfSetupVals_inp (haf : 16 ≤ af) (V : Fin (32 + af) → ℕ) :
    rfSetupVals af haf V (rfSelf af 0) = V (rfSelf af 0) := by
  simp only [rfSetupVals, rfSelf_update_apply, rfUnpairWin_selfW_apply]
  norm_num

lemma rfSetupVals_count (haf : 16 ≤ af) (V : Fin (32 + af) → ℕ) :
    rfSetupVals af haf V (rfSelf af 1) = V (rfSelf af 1) := by
  simp only [rfSetupVals, rfSelf_update_apply, rfUnpairWin_selfW_apply]
  norm_num

lemma rfSetupVals_a (haf : 16 ≤ af) (V : Fin (32 + af) → ℕ) :
    rfSetupVals af haf V (rfSelf af 6) = (Nat.unpair (V (rfSelf af 0))).1 := by
  simp only [rfSetupVals, rfSelf_update_apply, rfUnpairWin_selfW_apply]
  norm_num
  exact unpairVals_zero _ _

lemma rfSetupVals_m (haf : 16 ≤ af) (V : Fin (32 + af) → ℕ) :
    rfSetupVals af haf V (rfSelf af 7) = (Nat.unpair (V (rfSelf af 0))).2 := by
  simp only [rfSetupVals, rfSelf_update_apply, rfUnpairWin_selfW_apply]
  norm_num
  exact unpairVals_one _ _

lemma rfSetupVals_fuel (haf : 16 ≤ af) (V : Fin (32 + af) → ℕ) :
    rfSetupVals af haf V (rfSelf af 8) = V (rfSelf af 1) := by
  simp only [rfSetupVals, rfSelf_update_apply, rfUnpairWin_selfW_apply]
  norm_num

lemma rfSetupVals_search (haf : 16 ≤ af) (V : Fin (32 + af) → ℕ) :
    rfSetupVals af haf V (rfSelf af 9) = 1 := by
  simp only [rfSetupVals, rfSelf_update_apply]
  norm_num

lemma rfSetupVals_found (haf : 16 ≤ af) (V : Fin (32 + af) → ℕ) :
    rfSetupVals af haf V (rfSelf af 10) = 0 := by
  simp only [rfSetupVals, rfSelf_update_apply]
  norm_num

lemma rfSetupVals_result (haf : 16 ≤ af) (V : Fin (32 + af) → ℕ) :
    rfSetupVals af haf V (rfSelf af 11) = 0 := by
  simp only [rfSetupVals, rfSelf_update_apply]
  norm_num

lemma rfSetupVals_one (haf : 16 ≤ af) (V : Fin (32 + af) → ℕ) :
    rfSetupVals af haf V (rfSelf af 12) = 1 := by
  simp only [rfSetupVals, rfSelf_update_apply]
  norm_num

lemma rfFinishVals_tag (W : Fin (32 + af) → ℕ) :
    rfFinishVals af W (rfSelf af 2) = W (rfSelf af 10) := by
  simp only [rfFinishVals, rfSelf_update_apply]
  norm_num

lemma rfFinishVals_val (W : Fin (32 + af) → ℕ) :
    rfFinishVals af W (rfSelf af 3) = W (rfSelf af 11) := by
  simp only [rfFinishVals, rfSelf_update_apply]
  norm_num

/-- **`rfind'`, semantically complete.** Given a child that encodes `evaln`, the node's
    tag and value registers hold the tag and value of `evaln fuel (rfind' cf) inp`. -/
lemma rfindVals_encodes (haf : 16 ≤ af) (cf : Nat.Partrec.Code)
    (Ff : (Fin af → ℕ) → Fin af → ℕ) (hFf : ChildEncodes af haf cf Ff)
    (V : Fin (32 + af) → ℕ) :
    rfindVals af haf Ff V (rfSelf af 2)
        = resultTag (Nat.Partrec.Code.evaln (V (rfSelf af 1)) cf.rfind'
            (V (rfSelf af 0))) ∧
      rfindVals af haf Ff V (rfSelf af 3)
        = resultVal (Nat.Partrec.Code.evaln (V (rfSelf af 1)) cf.rfind'
            (V (rfSelf af 0))) := by
  have hS12 := rfSetupVals_one haf V
  obtain ⟨-, -, -, -, htriple⟩ :=
    rfLoopVals_spec haf cf Ff hFf (rfSetupVals af haf V) hS12
      (rfSetupVals af haf V (rfSelf af 1))
  rw [rfSetupVals_a, rfSetupVals_search, rfSetupVals_found, rfSetupVals_result,
    rfSetupVals_fuel, rfSetupVals_m, rfSetupVals_count] at htriple
  have hspec := rfIter_spec cf (Nat.unpair (V (rfSelf af 0))).1 (V (rfSelf af 1))
    (Nat.unpair (V (rfSelf af 0))).2 1 0 0
  rw [Nat.pair_unpair] at hspec
  constructor
  · rw [rfindVals, rfFinishVals_tag]
    have h10 := congrArg (fun p : ℕ × ℕ × ℕ => p.2.1) htriple
    simp only at h10
    rw [rfSetupVals_count, h10, hspec.1]
    omega
  · rw [rfindVals, rfFinishVals_val]
    have h11 := congrArg (fun p : ℕ × ℕ × ℕ => p.2.2) htriple
    simp only at h11
    rw [rfSetupVals_count, h11, hspec.2]
    omega

end RfindCloseTwo

section RfindBridge
variable {af : ℕ}

/-- **The block boundary**, as for `prec`: the parent's thirty-three-wide view and the
    node's thirty-two-wide working view agree, with the loop counter's value moving from
    the vector into the ambient tape family. -/
lemma regsWork_rfMain (R : Regs (33 + af) n) (w₀ : Fin n → Tape)
    (W : Fin (33 + af) → ℕ) :
    regsWork R w₀ W
      = regsWork ((rfMain af).trans R)
          (Function.update w₀ (R (rfLoopIdx af)) (regTape (W (rfLoopIdx af))))
          (fun k => W (rfMain af k)) := by
  have hmain : ∀ k : Fin (32 + af), (rfMain af k : ℕ) = (k : ℕ) := by
    intro k; simp [rfMain, shiftEmb_val]
  have hne : ∀ k : Fin (32 + af), ((rfMain af).trans R) k ≠ R (rfLoopIdx af) := by
    intro k h
    exact rfMain_ne_loopIdx k (R.injective h)
  funext j
  by_cases h : ∃ k : Fin (33 + af), R k = j
  · obtain ⟨k, rfl⟩ := h
    rw [regsWork_apply]
    by_cases hk : (k : ℕ) = 32 + af
    · have hkl : k = rfLoopIdx af := Fin.ext (by simpa [rfLoopIdx] using hk)
      subst hkl
      rw [regsWork_of_ne _ _ _ hne, Function.update_self]
    · have hlt : (k : ℕ) < 32 + af := by have := k.isLt; omega
      have hid : rfMain af ⟨(k : ℕ), hlt⟩ = k := Fin.ext (by rw [hmain])
      have hk' : ((rfMain af).trans R) ⟨(k : ℕ), hlt⟩ = R k := by
        show R (rfMain af ⟨(k : ℕ), hlt⟩) = R k
        rw [hid]
      rw [← hk', regsWork_apply, hid]
  · have h' : ∀ k : Fin (32 + af), ((rfMain af).trans R) k ≠ j :=
      fun k e => h ⟨rfMain af k, e⟩
    have hjl : j ≠ R (rfLoopIdx af) := fun e => h ⟨rfLoopIdx af, e.symm⟩
    rw [regsWork_of_ne _ _ _ (fun k e => h ⟨k, e⟩), regsWork_of_ne _ _ _ h',
      Function.update_of_ne hjl]

end RfindBridge

/-! ## `pair`: what the children see, and what the node leaves -/

section PairSemantics
variable {af ag : ℕ}

/-- The vector the left child sees: its own subtree, with the parent's input and fuel
    written into its interface. -/
noncomputable def pairLeftIn (af ag : ℕ) (haf : 16 ≤ af) (V : Fin (16 + af + ag) → ℕ) :
    Fin af → ℕ :=
  fun j =>
    Function.update (Function.update V (leftLoc af ag haf 0) (V (selfW af ag 0)))
      (leftLoc af ag haf 1) (V (selfW af ag 1)) (leftSub af ag j)

/-- The vector the right child sees. -/
noncomputable def pairRightIn (af ag : ℕ) (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (Ff : (Fin af → ℕ) → Fin af → ℕ) (V : Fin (16 + af + ag) → ℕ) : Fin ag → ℕ :=
  fun j =>
    Function.update
      (Function.update
        (writeWindow (leftSub af ag)
          (Function.update (Function.update V (leftLoc af ag haf 0) (V (selfW af ag 0)))
            (leftLoc af ag haf 1) (V (selfW af ag 1)))
          (Ff (pairLeftIn af ag haf V)))
        (rightLoc af ag hag 0) (V (selfW af ag 0)))
      (rightLoc af ag hag 1) (V (selfW af ag 1)) (rightSub af ag j)

lemma pairLeftIn_zero (haf : 16 ≤ af) (V : Fin (16 + af + ag) → ℕ) :
    pairLeftIn af ag haf V ⟨0, by omega⟩ = V (selfW af ag 0) := by
  have h : leftSub af ag ⟨0, by omega⟩ = leftLoc af ag haf 0 := by
    apply Fin.ext; simp [leftSub, leftLoc, shiftEmb_val]
  simp only [pairLeftIn, h]
  rw [leftLoc_update_apply haf]
  norm_num

lemma pairLeftIn_one (haf : 16 ≤ af) (V : Fin (16 + af + ag) → ℕ) :
    pairLeftIn af ag haf V ⟨1, by omega⟩ = V (selfW af ag 1) := by
  have h : leftSub af ag ⟨1, by omega⟩ = leftLoc af ag haf 1 := by
    apply Fin.ext; simp [leftSub, leftLoc, shiftEmb_val]
  simp only [pairLeftIn, h]
  rw [leftLoc_update_apply haf]
  norm_num

lemma pairRightIn_zero (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (Ff : (Fin af → ℕ) → Fin af → ℕ) (V : Fin (16 + af + ag) → ℕ) :
    pairRightIn af ag haf hag Ff V ⟨0, by omega⟩ = V (selfW af ag 0) := by
  have h : rightSub af ag ⟨0, by omega⟩ = rightLoc af ag hag 0 := by
    apply Fin.ext; simp [rightSub, rightLoc, shiftEmb_val]
  simp only [pairRightIn, h]
  rw [rightLoc_update_apply hag]
  norm_num

lemma pairRightIn_one (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (Ff : (Fin af → ℕ) → Fin af → ℕ) (V : Fin (16 + af + ag) → ℕ) :
    pairRightIn af ag haf hag Ff V ⟨1, by omega⟩ = V (selfW af ag 1) := by
  have h : rightSub af ag ⟨1, by omega⟩ = rightLoc af ag hag 1 := by
    apply Fin.ext; simp [rightSub, rightLoc, shiftEmb_val]
  simp only [pairRightIn, h]
  rw [rightLoc_update_apply hag]
  norm_num

/-! ### Phase A's read-offs -/

lemma pairPhaseAVec_selfW (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (Ff : (Fin af → ℕ) → Fin af → ℕ) (Fg : (Fin ag → ℕ) → Fin ag → ℕ)
    (V : Fin (16 + af + ag) → ℕ) (i : Fin 16) :
    pairPhaseAVec af ag haf hag Ff Fg V (selfW af ag i) = V (selfW af ag i) := by
  simp only [pairPhaseAVec, rightSub_win_selfW haf, leftSub_win_selfW,
    selfW_leftLoc_upd haf, selfW_rightLoc_upd hag haf]

lemma pairPhaseAVec_leftLoc (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (Ff : (Fin af → ℕ) → Fin af → ℕ) (Fg : (Fin ag → ℕ) → Fin ag → ℕ)
    (V : Fin (16 + af + ag) → ℕ) (j : Fin 16) :
    pairPhaseAVec af ag haf hag Ff Fg V (leftLoc af ag haf j)
      = Ff (pairLeftIn af ag haf V) ⟨(j : ℕ), by have := j.isLt; omega⟩ := by
  simp only [pairPhaseAVec, rightSub_win_leftLoc haf, leftLoc_rightLoc_upd haf hag,
    leftSub_win_leftLoc haf]
  rfl

lemma pairPhaseAVec_rightLoc (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (Ff : (Fin af → ℕ) → Fin af → ℕ) (Fg : (Fin ag → ℕ) → Fin ag → ℕ)
    (V : Fin (16 + af + ag) → ℕ) (j : Fin 16) :
    pairPhaseAVec af ag haf hag Ff Fg V (rightLoc af ag hag j)
      = Fg (pairRightIn af ag haf hag Ff V) ⟨(j : ℕ), by have := j.isLt; omega⟩ := by
  simp only [pairPhaseAVec, rightSub_win_rightLoc hag]
  rfl

/-! ### Phase B's read-offs -/

lemma pairPhaseBVec_tag (haf : 16 ≤ af) (hag : 16 ≤ ag) (W : Fin (16 + af + ag) → ℕ) :
    pairPhaseBVec af ag haf hag W (selfW af ag 2)
      = (if W (selfW af ag 0) < W (selfW af ag 1) then 1 else 0)
          * W (leftLoc af ag haf 2) * W (rightLoc af ag hag 2) := by
  simp only [pairPhaseBVec, selfW_update_apply, leftLoc_selfW_upd haf,
    rightLoc_selfW_upd hag haf, pairWin_leftLoc haf, pairWin_rightLoc hag haf,
    pairWin_selfW_apply]
  norm_num

lemma pairPhaseBVec_val (haf : 16 ≤ af) (hag : 16 ≤ ag) (W : Fin (16 + af + ag) → ℕ) :
    pairPhaseBVec af ag haf hag W (selfW af ag 3)
      = pairPhaseBVec af ag haf hag W (selfW af ag 2)
          * Nat.pair (W (leftLoc af ag haf 3)) (W (rightLoc af ag hag 3)) := by
  rw [pairPhaseBVec_tag]
  simp only [pairPhaseBVec, selfW_update_apply, leftLoc_selfW_upd haf,
    rightLoc_selfW_upd hag haf, pairWin_leftLoc haf, pairWin_rightLoc hag haf,
    pairWin_twelve, pairWin_selfW_apply, pairVals_apply, pairTrans_zero, pairTrans_one]
  norm_num

end PairSemantics

/-! ## `comp`: what the children see, and what the node leaves

`cg` runs on the parent's input; `cf` runs on `cg`'s *value*, which is the canonical `0`
when `cg` failed. -/

section CompSemantics
variable {af ag : ℕ}

/-- The vector the second child sees: the parent's input and fuel. -/
noncomputable def compRightIn (af ag : ℕ) (hag : 16 ≤ ag) (V : Fin (16 + af + ag) → ℕ) :
    Fin ag → ℕ :=
  fun j =>
    Function.update (Function.update V (rightLoc af ag hag 0) (V (selfW af ag 0)))
      (rightLoc af ag hag 1) (V (selfW af ag 1)) (rightSub af ag j)

/-- The vector the first child sees: `cg`'s value as its input, the parent's fuel. -/
noncomputable def compLeftIn (af ag : ℕ) (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (Fg : (Fin ag → ℕ) → Fin ag → ℕ) (V : Fin (16 + af + ag) → ℕ) : Fin af → ℕ :=
  fun j =>
    Function.update
      (Function.update
        (writeWindow (rightSub af ag)
          (Function.update (Function.update V (rightLoc af ag hag 0) (V (selfW af ag 0)))
            (rightLoc af ag hag 1) (V (selfW af ag 1)))
          (Fg (compRightIn af ag hag V)))
        (leftLoc af ag haf 0)
        (writeWindow (rightSub af ag)
          (Function.update (Function.update V (rightLoc af ag hag 0) (V (selfW af ag 0)))
            (rightLoc af ag hag 1) (V (selfW af ag 1)))
          (Fg (compRightIn af ag hag V)) (rightLoc af ag hag 3)))
      (leftLoc af ag haf 1) (V (selfW af ag 1)) (leftSub af ag j)

lemma compRightIn_zero (hag : 16 ≤ ag) (V : Fin (16 + af + ag) → ℕ) :
    compRightIn af ag hag V ⟨0, by omega⟩ = V (selfW af ag 0) := by
  have h : rightSub af ag ⟨0, by omega⟩ = rightLoc af ag hag 0 := by
    apply Fin.ext; simp [rightSub, rightLoc, shiftEmb_val]
  simp only [compRightIn, h]
  rw [rightLoc_update_apply hag]
  norm_num

lemma compRightIn_one (hag : 16 ≤ ag) (V : Fin (16 + af + ag) → ℕ) :
    compRightIn af ag hag V ⟨1, by omega⟩ = V (selfW af ag 1) := by
  have h : rightSub af ag ⟨1, by omega⟩ = rightLoc af ag hag 1 := by
    apply Fin.ext; simp [rightSub, rightLoc, shiftEmb_val]
  simp only [compRightIn, h]
  rw [rightLoc_update_apply hag]
  norm_num

lemma compLeftIn_zero (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (Fg : (Fin ag → ℕ) → Fin ag → ℕ) (V : Fin (16 + af + ag) → ℕ) :
    compLeftIn af ag haf hag Fg V ⟨0, by omega⟩
      = Fg (compRightIn af ag hag V) ⟨3, by omega⟩ := by
  have h : leftSub af ag ⟨0, by omega⟩ = leftLoc af ag haf 0 := by
    apply Fin.ext; simp [leftSub, leftLoc, shiftEmb_val]
  simp only [compLeftIn, h]
  rw [leftLoc_update_apply haf]
  norm_num
  rw [rightSub_win_rightLoc hag]
  congr 1

lemma compLeftIn_one (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (Fg : (Fin ag → ℕ) → Fin ag → ℕ) (V : Fin (16 + af + ag) → ℕ) :
    compLeftIn af ag haf hag Fg V ⟨1, by omega⟩ = V (selfW af ag 1) := by
  have h : leftSub af ag ⟨1, by omega⟩ = leftLoc af ag haf 1 := by
    apply Fin.ext; simp [leftSub, leftLoc, shiftEmb_val]
  simp only [compLeftIn, h]
  rw [leftLoc_update_apply haf]
  norm_num

/-! ### Phase A's read-offs -/

lemma compPhaseAVec_selfW (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (Ff : (Fin af → ℕ) → Fin af → ℕ) (Fg : (Fin ag → ℕ) → Fin ag → ℕ)
    (V : Fin (16 + af + ag) → ℕ) (i : Fin 16) :
    compPhaseAVec af ag haf hag Ff Fg V (selfW af ag i) = V (selfW af ag i) := by
  simp only [compPhaseAVec, leftSub_win_selfW, rightSub_win_selfW haf,
    selfW_leftLoc_upd haf, selfW_rightLoc_upd hag haf]

lemma compPhaseAVec_rightLoc (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (Ff : (Fin af → ℕ) → Fin af → ℕ) (Fg : (Fin ag → ℕ) → Fin ag → ℕ)
    (V : Fin (16 + af + ag) → ℕ) (j : Fin 16) :
    compPhaseAVec af ag haf hag Ff Fg V (rightLoc af ag hag j)
      = Fg (compRightIn af ag hag V) ⟨(j : ℕ), by have := j.isLt; omega⟩ := by
  simp only [compPhaseAVec, leftSub_win_rightLoc hag, rightLoc_leftLoc_upd haf hag,
    rightSub_win_rightLoc hag]
  rfl

lemma compPhaseAVec_leftLoc (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (Ff : (Fin af → ℕ) → Fin af → ℕ) (Fg : (Fin ag → ℕ) → Fin ag → ℕ)
    (V : Fin (16 + af + ag) → ℕ) (j : Fin 16) :
    compPhaseAVec af ag haf hag Ff Fg V (leftLoc af ag haf j)
      = Ff (compLeftIn af ag haf hag Fg V) ⟨(j : ℕ), by have := j.isLt; omega⟩ := by
  simp only [compPhaseAVec, leftSub_win_leftLoc haf]
  rfl

/-! ### Phase B's read-offs -/

lemma compPhaseBVec_tag (haf : 16 ≤ af) (hag : 16 ≤ ag) (W : Fin (16 + af + ag) → ℕ) :
    compPhaseBVec af ag haf hag W (selfW af ag 2)
      = (if W (selfW af ag 0) < W (selfW af ag 1) then 1 else 0)
          * W (rightLoc af ag hag 2) * W (leftLoc af ag haf 2) := by
  simp only [compPhaseBVec, selfW_update_apply, leftLoc_selfW_upd haf,
    rightLoc_selfW_upd hag haf]
  norm_num

lemma compPhaseBVec_val (haf : 16 ≤ af) (hag : 16 ≤ ag) (W : Fin (16 + af + ag) → ℕ) :
    compPhaseBVec af ag haf hag W (selfW af ag 3)
      = compPhaseBVec af ag haf hag W (selfW af ag 2) * W (leftLoc af ag haf 3) := by
  rw [compPhaseBVec_tag]
  simp only [compPhaseBVec, selfW_update_apply, leftLoc_selfW_upd haf,
    rightLoc_selfW_upd hag haf]
  norm_num

end CompSemantics

/-! ### `pair` and `comp`, semantically complete -/

section BinaryEncodes
variable {af ag : ℕ}

/-- **`pair`, semantically complete.** -/
lemma pairVals_encodes (haf : 16 ≤ af) (hag : 16 ≤ ag) (cf cg : Nat.Partrec.Code)
    (Ff : (Fin af → ℕ) → Fin af → ℕ) (Fg : (Fin ag → ℕ) → Fin ag → ℕ)
    (hFf : ChildEncodes af haf cf Ff) (hFg : ChildEncodes ag hag cg Fg)
    (V : Fin (16 + af + ag) → ℕ) :
    pairPhaseBVec af ag haf hag (pairPhaseAVec af ag haf hag Ff Fg V) (selfW af ag 2)
        = resultTag (Nat.Partrec.Code.evaln (V (selfW af ag 1)) (cf.pair cg)
            (V (selfW af ag 0))) ∧
      pairPhaseBVec af ag haf hag (pairPhaseAVec af ag haf hag Ff Fg V) (selfW af ag 3)
        = resultVal (Nat.Partrec.Code.evaln (V (selfW af ag 1)) (cf.pair cg)
            (V (selfW af ag 0))) := by
  obtain ⟨hft, hfv⟩ := hFf (pairLeftIn af ag haf V)
  obtain ⟨hgt, hgv⟩ := hFg (pairRightIn af ag haf hag Ff V)
  rw [pairLeftIn_zero, pairLeftIn_one] at hft hfv
  rw [pairRightIn_zero, pairRightIn_one] at hgt hgv
  have rF2 : pairPhaseAVec af ag haf hag Ff Fg V (leftLoc af ag haf 2)
      = resultTag (Nat.Partrec.Code.evaln (V (selfW af ag 1)) cf (V (selfW af ag 0))) := by
    rw [pairPhaseAVec_leftLoc]; exact hft
  have rF3 : pairPhaseAVec af ag haf hag Ff Fg V (leftLoc af ag haf 3)
      = resultVal (Nat.Partrec.Code.evaln (V (selfW af ag 1)) cf (V (selfW af ag 0))) := by
    rw [pairPhaseAVec_leftLoc]; exact hfv
  have rG2 : pairPhaseAVec af ag haf hag Ff Fg V (rightLoc af ag hag 2)
      = resultTag (Nat.Partrec.Code.evaln (V (selfW af ag 1)) cg (V (selfW af ag 0))) := by
    rw [pairPhaseAVec_rightLoc]; exact hgt
  have rG3 : pairPhaseAVec af ag haf hag Ff Fg V (rightLoc af ag hag 3)
      = resultVal (Nat.Partrec.Code.evaln (V (selfW af ag 1)) cg (V (selfW af ag 0))) := by
    rw [pairPhaseAVec_rightLoc]; exact hgv
  obtain ⟨ht, hv⟩ := pair_encodes (V (selfW af ag 1)) (V (selfW af ag 0))
    (resultTag (Nat.Partrec.Code.evaln (V (selfW af ag 1)) cf (V (selfW af ag 0))))
    (resultVal (Nat.Partrec.Code.evaln (V (selfW af ag 1)) cf (V (selfW af ag 0))))
    (resultTag (Nat.Partrec.Code.evaln (V (selfW af ag 1)) cg (V (selfW af ag 0))))
    (resultVal (Nat.Partrec.Code.evaln (V (selfW af ag 1)) cg (V (selfW af ag 0))))
    cf cg rfl rfl rfl rfl
  constructor
  · rw [pairPhaseBVec_tag, pairPhaseAVec_selfW, pairPhaseAVec_selfW, rF2, rG2, ht]
  · rw [pairPhaseBVec_val, pairPhaseBVec_tag, pairPhaseAVec_selfW, pairPhaseAVec_selfW,
      rF2, rG2, rF3, rG3]
    exact hv

/-- **`comp`, semantically complete.** -/
lemma compVals_encodes (haf : 16 ≤ af) (hag : 16 ≤ ag) (cf cg : Nat.Partrec.Code)
    (Ff : (Fin af → ℕ) → Fin af → ℕ) (Fg : (Fin ag → ℕ) → Fin ag → ℕ)
    (hFf : ChildEncodes af haf cf Ff) (hFg : ChildEncodes ag hag cg Fg)
    (V : Fin (16 + af + ag) → ℕ) :
    compPhaseBVec af ag haf hag (compPhaseAVec af ag haf hag Ff Fg V) (selfW af ag 2)
        = resultTag (Nat.Partrec.Code.evaln (V (selfW af ag 1)) (cf.comp cg)
            (V (selfW af ag 0))) ∧
      compPhaseBVec af ag haf hag (compPhaseAVec af ag haf hag Ff Fg V) (selfW af ag 3)
        = resultVal (Nat.Partrec.Code.evaln (V (selfW af ag 1)) (cf.comp cg)
            (V (selfW af ag 0))) := by
  obtain ⟨hgt, hgv⟩ := hFg (compRightIn af ag hag V)
  rw [compRightIn_zero, compRightIn_one] at hgt hgv
  obtain ⟨hft, hfv⟩ := hFf (compLeftIn af ag haf hag Fg V)
  rw [compLeftIn_zero, compLeftIn_one, hgv] at hft hfv
  have rG2 : compPhaseAVec af ag haf hag Ff Fg V (rightLoc af ag hag 2)
      = resultTag (Nat.Partrec.Code.evaln (V (selfW af ag 1)) cg (V (selfW af ag 0))) := by
    rw [compPhaseAVec_rightLoc]; exact hgt
  have rF2 : compPhaseAVec af ag haf hag Ff Fg V (leftLoc af ag haf 2)
      = resultTag (Nat.Partrec.Code.evaln (V (selfW af ag 1)) cf
          (resultVal (Nat.Partrec.Code.evaln (V (selfW af ag 1)) cg
            (V (selfW af ag 0))))) := by
    rw [compPhaseAVec_leftLoc]; exact hft
  have rF3 : compPhaseAVec af ag haf hag Ff Fg V (leftLoc af ag haf 3)
      = resultVal (Nat.Partrec.Code.evaln (V (selfW af ag 1)) cf
          (resultVal (Nat.Partrec.Code.evaln (V (selfW af ag 1)) cg
            (V (selfW af ag 0))))) := by
    rw [compPhaseAVec_leftLoc]; exact hfv
  obtain ⟨ht, hv⟩ := comp_encodes (V (selfW af ag 1)) (V (selfW af ag 0))
    (resultTag (Nat.Partrec.Code.evaln (V (selfW af ag 1)) cg (V (selfW af ag 0))))
    (resultVal (Nat.Partrec.Code.evaln (V (selfW af ag 1)) cg (V (selfW af ag 0))))
    (resultTag (Nat.Partrec.Code.evaln (V (selfW af ag 1)) cf
      (resultVal (Nat.Partrec.Code.evaln (V (selfW af ag 1)) cg (V (selfW af ag 0))))))
    (resultVal (Nat.Partrec.Code.evaln (V (selfW af ag 1)) cf
      (resultVal (Nat.Partrec.Code.evaln (V (selfW af ag 1)) cg (V (selfW af ag 0))))))
    cf cg rfl rfl rfl rfl
  constructor
  · rw [compPhaseBVec_tag, compPhaseAVec_selfW, compPhaseAVec_selfW, rF2, rG2, ht]
  · rw [compPhaseBVec_val, compPhaseBVec_tag, compPhaseAVec_selfW, compPhaseAVec_selfW,
      rF2, rG2, rF3]
    exact hv

end BinaryEncodes

/-! ## The register vector a compiled node produces

`codeVals c` mirrors `compileCodeAt c` exactly: one clause per constructor, each the
constructor's own phase vector with the children's `codeVals` substituted for the abstract
child semantics the phase specifications are parametric in. For the two looping
constructors the node's working block is thirty-two wide and the thirty-third register is
the loop counter, so the clause writes the working block back through `precMain` / `rfMain`
and sets the counter separately. -/

/-- The node's own interface block, uniformly at offset `0`. -/
def codeLocal (c : Nat.Partrec.Code) : Fin 16 ↪ Fin (codeRegs c) :=
  shiftEmb 0 (by have := codeRegs_ge c; omega)

/-- A `prec` node's thirty-three-wide vector: its working block written back through
    `precMain`, with the loop counter set separately. -/
noncomputable def precBlockVals (af ag : ℕ) (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (Ff : (Fin af → ℕ) → Fin af → ℕ) (Fg : (Fin ag → ℕ) → Fin ag → ℕ)
    (v : Fin (33 + af + ag) → ℕ) : Fin (33 + af + ag) → ℕ :=
  Function.update
    (writeWindow (precMain af ag) v
      (precVals af ag haf hag Ff Fg (fun k => v (precMain af ag k))))
    (precLoopIdx af ag)
    (precSetupVals af ag haf hag Ff (fun k => v (precMain af ag k)) (precSelf af ag 7))

/-- The same for an `rfind'` node. -/
noncomputable def rfBlockVals (af : ℕ) (haf : 16 ≤ af)
    (Ff : (Fin af → ℕ) → Fin af → ℕ) (v : Fin (33 + af) → ℕ) : Fin (33 + af) → ℕ :=
  Function.update
    (writeWindow (rfMain af) v (rfindVals af haf Ff (fun k => v (rfMain af k))))
    (rfLoopIdx af)
    (rfSetupVals af haf (fun k => v (rfMain af k)) (rfSelf af 1))

/-- A `prec` node's own registers, read out of its thirty-three-wide vector. -/
lemma precBlockVals_self {af ag : ℕ} (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (Ff : (Fin af → ℕ) → Fin af → ℕ) (Fg : (Fin ag → ℕ) → Fin ag → ℕ)
    (v : Fin (33 + af + ag) → ℕ) (j : Fin 32) :
    precBlockVals af ag haf hag Ff Fg v (precMain af ag (precSelf af ag j))
      = precVals af ag haf hag Ff Fg (fun k => v (precMain af ag k))
          (precSelf af ag j) := by
  rw [precBlockVals, Function.update_of_ne (precMain_ne_loopIdx _), writeWindow_apply]

/-- An `rfind'` node's own registers, read out of its thirty-three-wide vector. -/
lemma rfBlockVals_self {af : ℕ} (haf : 16 ≤ af) (Ff : (Fin af → ℕ) → Fin af → ℕ)
    (v : Fin (33 + af) → ℕ) (j : Fin 32) :
    rfBlockVals af haf Ff v (rfMain af (rfSelf af j))
      = rfindVals af haf Ff (fun k => v (rfMain af k)) (rfSelf af j) := by
  rw [rfBlockVals, Function.update_of_ne (rfMain_ne_loopIdx _), writeWindow_apply]

noncomputable def codeVals : (c : Nat.Partrec.Code) → (Fin (codeRegs c) → ℕ) →
    Fin (codeRegs c) → ℕ
  | .zero, v => zeroVals v
  | .succ, v => succVals v
  | .left, v => projVals v 0
  | .right, v => projVals v 1
  | .pair cf cg, v =>
      pairPhaseBVec (codeRegs cf) (codeRegs cg) (codeRegs_ge cf) (codeRegs_ge cg)
        (pairPhaseAVec (codeRegs cf) (codeRegs cg) (codeRegs_ge cf) (codeRegs_ge cg)
          (codeVals cf) (codeVals cg) v)
  | .comp cf cg, v =>
      compPhaseBVec (codeRegs cf) (codeRegs cg) (codeRegs_ge cf) (codeRegs_ge cg)
        (compPhaseAVec (codeRegs cf) (codeRegs cg) (codeRegs_ge cf) (codeRegs_ge cg)
          (codeVals cf) (codeVals cg) v)
  | .prec cf cg, v =>
      precBlockVals (codeRegs cf) (codeRegs cg) (codeRegs_ge cf) (codeRegs_ge cg)
        (codeVals cf) (codeVals cg) v
  | .rfind' cf, v =>
      rfBlockVals (codeRegs cf) (codeRegs_ge cf) (codeVals cf) v

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
  | .prec cf cg, R => do
      let Mf ← compileCodeAt cf
        ((precLeftSub (codeRegs cf) (codeRegs cg)).trans
          ((precMain (codeRegs cf) (codeRegs cg)).trans R))
      let Mg ← compileCodeAt cg
        ((precRightSub (codeRegs cf) (codeRegs cg)).trans
          ((precMain (codeRegs cf) (codeRegs cg)).trans R))
      some (precTM (codeRegs cf) (codeRegs cg) (codeRegs_ge cf) (codeRegs_ge cg)
        ((precMain (codeRegs cf) (codeRegs cg)).trans R)
        (R (precLoopIdx (codeRegs cf) (codeRegs cg))) Mf Mg)
  | .rfind' cf, R => do
      let Mf ← compileCodeAt cf
        ((rfSub (codeRegs cf)).trans ((rfMain (codeRegs cf)).trans R))
      some (rfindTM (codeRegs cf) (codeRegs_ge cf)
        ((rfMain (codeRegs cf)).trans R) (R (rfLoopIdx (codeRegs cf))) Mf)

/-- The per-constructor success lemmas. -/
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

lemma compileCodeAt_isSome_comp (cf cg : Nat.Partrec.Code)
    (R : Regs (codeRegs (cf.comp cg)) n)
    (hf : (compileCodeAt cf ((leftSub (codeRegs cf) (codeRegs cg)).trans R)).isSome)
    (hg : (compileCodeAt cg ((rightSub (codeRegs cf) (codeRegs cg)).trans R)).isSome) :
    (compileCodeAt (cf.comp cg) R).isSome := by
  rw [compileCodeAt]
  cases hF : compileCodeAt cf ((leftSub (codeRegs cf) (codeRegs cg)).trans R) with
  | none => rw [hF] at hf; exact absurd hf (by simp)
  | some Mf =>
    cases hG : compileCodeAt cg ((rightSub (codeRegs cf) (codeRegs cg)).trans R) with
    | none => rw [hG] at hg; exact absurd hg (by simp)
    | some Mg => simp

lemma compileCodeAt_isSome_prec (cf cg : Nat.Partrec.Code)
    (R : Regs (codeRegs (cf.prec cg)) n)
    (hf : (compileCodeAt cf ((precLeftSub (codeRegs cf) (codeRegs cg)).trans
      ((precMain (codeRegs cf) (codeRegs cg)).trans R))).isSome)
    (hg : (compileCodeAt cg ((precRightSub (codeRegs cf) (codeRegs cg)).trans
      ((precMain (codeRegs cf) (codeRegs cg)).trans R))).isSome) :
    (compileCodeAt (cf.prec cg) R).isSome := by
  rw [compileCodeAt]
  cases hF : compileCodeAt cf ((precLeftSub (codeRegs cf) (codeRegs cg)).trans
      ((precMain (codeRegs cf) (codeRegs cg)).trans R)) with
  | none => rw [hF] at hf; exact absurd hf (by simp)
  | some Mf =>
    cases hG : compileCodeAt cg ((precRightSub (codeRegs cf) (codeRegs cg)).trans
        ((precMain (codeRegs cf) (codeRegs cg)).trans R)) with
    | none => rw [hG] at hg; exact absurd hg (by simp)
    | some Mg => simp

lemma compileCodeAt_isSome_rfind' (cf : Nat.Partrec.Code)
    (R : Regs (codeRegs cf.rfind') n)
    (hf : (compileCodeAt cf ((rfSub (codeRegs cf)).trans
      ((rfMain (codeRegs cf)).trans R))).isSome) :
    (compileCodeAt cf.rfind' R).isSome := by
  rw [compileCodeAt]
  cases hF : compileCodeAt cf ((rfSub (codeRegs cf)).trans
      ((rfMain (codeRegs cf)).trans R)) with
  | none => rw [hF] at hf; exact absurd hf (by simp)
  | some Mf => simp

/-- **The compiler is total.** Every `Nat.Partrec.Code` compiles into the register file
    its `codeRegs` names — all eight constructors, `prec` and `rfind'` included. -/
lemma compileCodeAt_isSome : ∀ (c : Nat.Partrec.Code) (R : Regs (codeRegs c) n),
    (compileCodeAt c R).isSome
  | .zero, _ => rfl
  | .succ, _ => rfl
  | .left, _ => rfl
  | .right, _ => rfl
  | .pair cf cg, R =>
      compileCodeAt_isSome_pair cf cg R (compileCodeAt_isSome cf _) (compileCodeAt_isSome cg _)
  | .comp cf cg, R =>
      compileCodeAt_isSome_comp cf cg R (compileCodeAt_isSome cf _) (compileCodeAt_isSome cg _)
  | .prec cf cg, R =>
      compileCodeAt_isSome_prec cf cg R (compileCodeAt_isSome cf _) (compileCodeAt_isSome cg _)
  | .rfind' cf, R => compileCodeAt_isSome_rfind' cf R (compileCodeAt_isSome cf _)

/-! ## The compiler is correct

One structural theorem for every `Nat.Partrec.Code`: the register vector a compiled node
produces holds, in its tag and value registers, the canonical encoding of `evaln`. Every
constructor's own semantic lemma is parametric in `ChildEncodes` for its children, and the
induction is what discharges those.

The four base constructors and the two binary ones need no index bookkeeping — a node's
interface registers sit at offset `0` of its block in every layout, so the two views are
definitionally equal. The two looping constructors do: their block is thirty-three wide,
so the vector is written back through `precMain` / `rfMain` with the loop counter set
separately, and neither `writeWindow` nor `Function.update` reduces on a symbolic index. -/

section Structural

/-- **The compiler is correct.** For every code, its compiled register vector encodes
    `evaln` in the node's tag and value registers — all eight constructors. -/
lemma codeVals_encodes : ∀ c : Nat.Partrec.Code,
    ChildEncodes (codeRegs c) (codeRegs_ge c) c (codeVals c)
  | .zero => fun v => zeroVals_encodes v
  | .succ => fun v => succVals_encodes v
  | .left => fun v => leftVals_encodes v
  | .right => fun v => rightVals_encodes v
  | .pair cf cg => fun v =>
      pairVals_encodes (codeRegs_ge cf) (codeRegs_ge cg) cf cg
        (codeVals cf) (codeVals cg) (codeVals_encodes cf) (codeVals_encodes cg) v
  | .comp cf cg => fun v =>
      compVals_encodes (codeRegs_ge cf) (codeRegs_ge cg) cf cg
        (codeVals cf) (codeVals cg) (codeVals_encodes cf) (codeVals_encodes cg) v
  | .prec cf cg => by
      intro v
      have h := precVals_encodes (codeRegs_ge cf) (codeRegs_ge cg) cf cg
        (codeVals cf) (codeVals cg) (codeVals_encodes cf) (codeVals_encodes cg)
        (fun k => v (precMain (codeRegs cf) (codeRegs cg) k))
      constructor
      · show precBlockVals (codeRegs cf) (codeRegs cg) (codeRegs_ge cf) (codeRegs_ge cg)
            (codeVals cf) (codeVals cg) v
            (precMain (codeRegs cf) (codeRegs cg)
              (precSelf (codeRegs cf) (codeRegs cg) 2)) = _
        rw [precBlockVals_self]
        exact h.1
      · show precBlockVals (codeRegs cf) (codeRegs cg) (codeRegs_ge cf) (codeRegs_ge cg)
            (codeVals cf) (codeVals cg) v
            (precMain (codeRegs cf) (codeRegs cg)
              (precSelf (codeRegs cf) (codeRegs cg) 3)) = _
        rw [precBlockVals_self]
        exact h.2
  | .rfind' cf => by
      intro v
      have h := rfindVals_encodes (codeRegs_ge cf) cf (codeVals cf) (codeVals_encodes cf)
        (fun k => v (rfMain (codeRegs cf) k))
      constructor
      · show rfBlockVals (codeRegs cf) (codeRegs_ge cf) (codeVals cf) v
            (rfMain (codeRegs cf) (rfSelf (codeRegs cf) 2)) = _
        rw [rfBlockVals_self]
        exact h.1
      · show rfBlockVals (codeRegs cf) (codeRegs_ge cf) (codeVals cf) v
            (rfMain (codeRegs cf) (rfSelf (codeRegs cf) 3)) = _
        rw [rfBlockVals_self]
        exact h.2

end Structural

end LogicalInduction.EvalnCompiler
