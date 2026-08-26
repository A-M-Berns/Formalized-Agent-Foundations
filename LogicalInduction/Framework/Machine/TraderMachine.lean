/-
# The trader machine

Stage 2 item 5: the machine that computes an `EfficientlyComputable` trader's day-`n`
serialization, so that the trader lands in `Complexity.FP` and hence in
`MachineEfficientTrader`.

This file builds it out of the fork's register calculus. Three layers:

* **register operations as vector updates** — each of the fork's register machines
  restated over a `regsWork` state under the common arithmetic budget
  (`evalnArithmeticCost`), so that a stage of a straight-line register program is one
  line;
* **guarded emission** — `guardEmit_hoareTime`, the emitting counterpart of the fork's
  `guardTM` rule, which is how a data-dependent bit stream is built from fixed words;
* **the digit block** — ten registers turning a token value into the three bits
  `bitsToDigits` reads back as its clamp at the terminator `4` (see
  `Machine/DigitBits.lean` for why clamping is harmless).

Every bound here is deliberately loose: `Complexity.FP` quantifies the degree
existentially, so only the polynomial shape matters.
-/
import LogicalInduction.Framework.Machine.EvalnRegBound
import Complexitylib.Models.TuringMachine.Registers.Horner
import Complexitylib.Models.TuringMachine.Registers.InputLen
import Complexitylib.Classes.P.NormalForm
import LogicalInduction.Framework.Machine.DigitBits
import Mathlib.Tactic.IntervalCases

namespace LogicalInduction.TraderMachine

open Nat.Partrec (Code)
open Complexity Complexity.TM
open LogicalInduction.EvalnCompiler

variable {n m : ℕ}

/-- `setConstTM` under the common arithmetic cost. -/
lemma setConstTime_le_arith (c d B : ℕ) (hc : c ≤ B) (hd : d ≤ B) :
    (2 * d + 4) + 1 + (c * (2 * c + 5) + 1) ≤ evalnArithmeticCost B := by
  have h1 : c * (2 * c + 5) ≤ B * (2 * B + 5) := Nat.mul_le_mul hc (by omega)
  have hX : 1 ≤ (B + 1) * (B + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have h3 : (2 * d + 4) + 1 + (c * (2 * c + 5) + 1) ≤ 8 * ((B + 1) * (B + 1)) := by
    nlinarith
  have h4 : 8 * ((B + 1) * (B + 1))
      ≤ 500 * ((B + 1) * (B + 1) * ((B + 1) * (B + 1))) := by nlinarith
  have h2 : (B + 1) ^ 4 = (B + 1) * (B + 1) * ((B + 1) * (B + 1)) := by ring
  rw [evalnArithmeticCost, h2]
  omega

/-! ## Register operations, read as vector updates

Each of the fork's register machines, restated over a `regsWork` state as a
`Function.update` of the value vector under the common arithmetic budget. Every stage of a
straight-line register program is then one line. -/

section Ops
variable (r : Regs m n) (V : Fin m → ℕ) (B : ℕ) (inp₀ : Tape) (w₀ : Fin n → Tape)
  (ys : List Bool)

lemma update_le {q : Fin m} {x : ℕ} (hv : ∀ k, V k ≤ B) (hx : x ≤ B) :
    ∀ k, Function.update V q x k ≤ B := by
  intro k
  simp only [Function.update_apply]
  split_ifs
  · exact hx
  · exact hv k

lemma setConst_regsWork (q : Fin m) (c : ℕ)
    (hinp₀ : Parked inp₀) (hpark : ∀ i, Parked (w₀ i))
    (hv : ∀ k, V k ≤ B) (hc : c ≤ B) :
    (setConstTM (r q) c).HoareTime
      (EmitPred inp₀ (regsWork r w₀ V) ys)
      (EmitPred inp₀ (regsWork r w₀ (Function.update V q c)) ys)
      (evalnArithmeticCost B) := by
  have h := setConstTM_hoareTime (r q) c (V q) inp₀ (regsWork r w₀ V) ys hinp₀
    (parked_regsWork r hpark V) (regsWork_apply r w₀ V q)
  rw [regsWork_update] at h
  exact h.mono_bound (setConstTime_le_arith c (V q) B hc (hv q))

lemma copyInto_regsWork (src dst : Fin m) (hne : src ≠ dst)
    (hinp₀ : Parked inp₀) (hpark : ∀ i, Parked (w₀ i)) (hv : ∀ k, V k ≤ B) :
    (copyIntoTM (r src) (r dst)).HoareTime
      (EmitPred inp₀ (regsWork r w₀ V) ys)
      (EmitPred inp₀ (regsWork r w₀ (Function.update V dst (V src))) ys)
      (evalnArithmeticCost B) := by
  have h := copyIntoTM_hoareTime (r src) (r dst) (r.ne hne) (V src) (V dst) inp₀
    (regsWork r w₀ V) ys hinp₀ (fun i _ => parked_regsWork r hpark V i)
    (regsWork_apply r w₀ V src) (regsWork_apply r w₀ V dst)
  rw [regsWork_update] at h
  exact h.mono_bound (copyIntoTime_le_arith (V src) (V dst) B (hv src) (hv dst))

lemma subInto_regsWork (src dst : Fin m) (hne : src ≠ dst)
    (hinp₀ : Parked inp₀) (hpark : ∀ i, Parked (w₀ i)) (hv : ∀ k, V k ≤ B) :
    (subIntoTM (r src) (r dst)).HoareTime
      (EmitPred inp₀ (regsWork r w₀ V) ys)
      (EmitPred inp₀ (regsWork r w₀ (Function.update V dst (V dst - V src))) ys)
      (evalnArithmeticCost B) := by
  have h := subIntoTM_hoareTime (r src) (r dst) (r.ne hne) (V src) (V dst) inp₀
    (regsWork r w₀ V) ys hinp₀ (fun i _ => parked_regsWork r hpark V i)
    (regsWork_apply r w₀ V src) (regsWork_apply r w₀ V dst)
  rw [regsWork_update] at h
  exact h.mono_bound (subIntoTime_le_arith (V src) (V dst) B (hv src) (hv dst))

lemma addInto_regsWork (src dst : Fin m) (hne : src ≠ dst)
    (hinp₀ : Parked inp₀) (hpark : ∀ i, Parked (w₀ i)) (hv : ∀ k, V k ≤ B) :
    (addIntoTM (r src) (r dst)).HoareTime
      (EmitPred inp₀ (regsWork r w₀ V) ys)
      (EmitPred inp₀ (regsWork r w₀ (Function.update V dst (V dst + V src))) ys)
      (evalnArithmeticCost B) := by
  have h := addIntoTM_hoareTime (r src) (r dst) (r.ne hne) (V src) (V dst) inp₀
    (regsWork r w₀ V) ys hinp₀ (fun i _ => parked_regsWork r hpark V i)
    (regsWork_apply r w₀ V src) (regsWork_apply r w₀ V dst)
  rw [regsWork_update] at h
  exact h.mono_bound (addIntoTime_le_arith (V src) (V dst) B (hv src) (hv dst))

lemma mulAddInto_regsWork (src₁ src₂ dst : Fin m)
    (h₁ : src₁ ≠ src₂) (h₂ : src₁ ≠ dst) (h₃ : src₂ ≠ dst)
    (hinp₀ : Parked inp₀) (hpark : ∀ i, Parked (w₀ i)) (hv : ∀ k, V k ≤ B) :
    (mulAddIntoTM (r src₁) (r src₂) (r dst)).HoareTime
      (EmitPred inp₀ (regsWork r w₀ V) ys)
      (EmitPred inp₀
        (regsWork r w₀ (Function.update V dst (V dst + V src₁ * V src₂))) ys)
      (evalnArithmeticCost B) := by
  have h := mulAddIntoTM_hoareTime (r src₁) (r src₂) (r dst) (r.ne h₁) (r.ne h₂)
    (r.ne h₃) (V src₁) (V src₂) (V dst) inp₀ (regsWork r w₀ V) ys hinp₀
    (fun i _ => parked_regsWork r hpark V i)
    (regsWork_apply r w₀ V src₁) (regsWork_apply r w₀ V src₂)
    (regsWork_apply r w₀ V dst)
  rw [regsWork_update] at h
  exact h.mono_bound (mulAddTime_le_arith (V src₁) (V src₂) (V dst) B (hv src₁)
    (hv src₂) (hv dst))

lemma ltFlag_regsWork (ra rb sc flag : Fin m)
    (h₁ : ra ≠ sc) (h₂ : rb ≠ sc) (h₃ : sc ≠ flag)
    (hinp₀ : Parked inp₀) (hpark : ∀ i, Parked (w₀ i)) (hv : ∀ k, V k ≤ B) :
    (ltFlagTM (r ra) (r rb) (r sc) (r flag)).HoareTime
      (EmitPred inp₀ (regsWork r w₀ V) ys)
      (EmitPred inp₀
        (regsWork r w₀
          (Function.update (Function.update V sc (V rb - V ra)) flag
            (if V ra < V rb then 1 else 0))) ys)
      (evalnArithmeticCost B) := by
  have h := ltFlagTM_hoareTime (r ra) (r rb) (r sc) (r flag) (r.ne h₁) (r.ne h₂)
    (r.ne h₃) (V ra) (V rb) (V sc) (V flag) inp₀ (regsWork r w₀ V) ys hinp₀
    (parked_regsWork r hpark V)
    (regsWork_apply r w₀ V ra) (regsWork_apply r w₀ V rb)
    (regsWork_apply r w₀ V sc) (regsWork_apply r w₀ V flag)
  rw [regsWork_update, regsWork_update] at h
  exact h.mono_bound (ltFlagTime_le_arith (V ra) (V rb) (V sc) (V flag) B (hv ra)
    (hv rb) (hv sc) (hv flag))

end Ops

/-! ## Guarded emission -/

/-- `seqEmit` with the output accumulator allowed to grow across the join. -/
lemma seqEmitOut {tm₁ tm₂ : TM n} {inp₀ : Tape} {w₀ w₁ w₂ : Fin n → Tape}
    {ys₀ ys₁ ys₂ : List Bool} {b₁ b₂ : ℕ}
    (hinp₀ : Parked inp₀) (hw₁ : ∀ i, Parked (w₁ i))
    (h₁ : tm₁.HoareTime (EmitPred inp₀ w₀ ys₀) (EmitPred inp₀ w₁ ys₁) b₁)
    (h₂ : tm₂.HoareTime (EmitPred inp₀ w₁ ys₁) (EmitPred inp₀ w₂ ys₂) b₂) :
    (seqTM tm₁ tm₂).HoareTime (EmitPred inp₀ w₀ ys₀) (EmitPred inp₀ w₂ ys₂)
      (b₁ + 1 + b₂) :=
  seqTM_hoareTime _ _ h₁ (fun _ _ _ h => emitPred_transition hinp₀ hw₁ ys₁ _ _ _ h) h₂

/-- **Emit a fixed word under a `{0,1}` guard.** The fork's `guardTM` rule keeps the
    output accumulator fixed; this is the emitting variant, which is what a data-dependent
    bit stream is built from. -/
lemma guardEmit_hoareTime (w : List Bool) (flag : Fin n) (f : ℕ) (hf : f ≤ 1)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hP₀ : ∀ j, Parked (work₀ j))
    (hf₀ : work₀ flag = regTape f) :
    (guardTM (emitBitsTM w) flag).HoareTime
      (EmitPred inp₀ work₀ ys)
      (EmitPred inp₀ work₀ (ys ++ if f = 0 then [] else w))
      (f * (w.length + 2) + (f + 2)) := by
  have hloop := forRegTM_hoareTime (emitBitsTM w) flag f inp₀
    (fun _ => work₀) (fun i => if i = 0 then ys else ys ++ w) w.length hinp₀
    (fun _ => hf₀) (fun _ j _ => hP₀ j)
    (fun i hi => by
      have hi0 : i = 0 := by omega
      subst hi0
      have hpk : ∀ j, Parked (Function.update work₀ flag
          (⟨0 + 2, regCells f⟩ : Tape) j) := by
        intro j
        by_cases hj : j = flag
        · subst hj; rw [Function.update_self]; exact parked_regCells (by omega)
        · rw [Function.update_of_ne hj]; exact hP₀ j
      have h := emitBitsTM_hoareTime (n := n) w inp₀
        (Function.update work₀ flag ⟨0 + 2, regCells f⟩) ys hinp₀ hpk
      simpa using h)
  rcases Nat.eq_zero_or_pos f with rfl | hpos
  · simpa [guardTM] using hloop
  · have hf1 : f = 1 := by omega
    subst hf1
    simpa [guardTM] using hloop


/-! ## The digit block

Ten registers turn a token value into the three bits `bitsToDigits` reads back as its
clamp at the terminator `4`: `0` the token, `1` the clamp, `2` a constant, `3` scratch,
`4`–`8` the five equality flags, `9` scratch. -/

/-- The clamp's final register values: `k := 4`, `t := d - 4`, `g := min d 4`. -/
def clampVals (v : Fin 10 → ℕ) : Fin 10 → ℕ := fun k =>
  if (k : ℕ) = 1 then min (v 0) 4
  else if (k : ℕ) = 2 then 4
  else if (k : ℕ) = 9 then v 0 - 4
  else v k

/-- `g := min d 4`, through the identity `min a b = a - (a - b)`. -/
def clampTM (dr : Regs 10 n) : TM n :=
  seqTM (setConstTM (dr 2) 4)
    (seqTM (copyIntoTM (dr 0) (dr 9))
      (seqTM (subIntoTM (dr 2) (dr 9))
        (seqTM (copyIntoTM (dr 0) (dr 1)) (subIntoTM (dr 9) (dr 1)))))

lemma clampTM_hoareTime (dr : Regs 10 n) (v : Fin 10 → ℕ) (B : ℕ)
    (inp₀ : Tape) (w₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hpark : ∀ i, Parked (w₀ i)) (hB4 : 4 ≤ B)
    (hv : ∀ k, v k ≤ B) :
    (clampTM dr).HoareTime
      (EmitPred inp₀ (regsWork dr w₀ v) ys)
      (EmitPred inp₀ (regsWork dr w₀ (clampVals v)) ys)
      (5 * evalnArithmeticCost B + 4) := by
  have h1 := setConst_regsWork dr v B inp₀ w₀ ys 2 4 hinp₀ hpark hv (by omega)
  set V1 := Function.update v 2 4 with hV1
  have hv1 : ∀ k, V1 k ≤ B := update_le v B hv (by omega)
  have h2 := copyInto_regsWork dr V1 B inp₀ w₀ ys 0 9 (by decide) hinp₀ hpark hv1
  set V2 := Function.update V1 9 (V1 0) with hV2
  have hv2 : ∀ k, V2 k ≤ B := update_le V1 B hv1 (hv1 0)
  have h3 := subInto_regsWork dr V2 B inp₀ w₀ ys 2 9 (by decide) hinp₀ hpark hv2
  set V3 := Function.update V2 9 (V2 9 - V2 2) with hV3
  have hv3 : ∀ k, V3 k ≤ B := update_le V2 B hv2 (by have := hv2 9; omega)
  have h4 := copyInto_regsWork dr V3 B inp₀ w₀ ys 0 1 (by decide) hinp₀ hpark hv3
  set V4 := Function.update V3 1 (V3 0) with hV4
  have hv4 : ∀ k, V4 k ≤ B := update_le V3 B hv3 (hv3 0)
  have h5 := subInto_regsWork dr V4 B inp₀ w₀ ys 9 1 (by decide) hinp₀ hpark hv4
  set V5 := Function.update V4 1 (V4 1 - V4 9) with hV5
  have hv5 : ∀ k, V5 k ≤ B := update_le V4 B hv4 (by have := hv4 1; omega)
  have hfinal : V5 = clampVals v := by
    funext k
    fin_cases k <;>
      simp [clampVals, hV5, hV4, hV3, hV2, hV1] <;> omega
  rw [hfinal] at h5
  exact (seqEmit hinp₀ (parked_regsWork dr hpark V1) h1
    (seqEmit hinp₀ (parked_regsWork dr hpark V2) h2
      (seqEmit hinp₀ (parked_regsWork dr hpark V3) h3
        (seqEmit hinp₀ (parked_regsWork dr hpark V4) h4 h5)))).mono_bound (by omega)


/-- The flag block's final register values: `e_c := [g = c]` for `c = 0..4`, read off the
    four comparisons `[g < 1] … [g < 4]`. -/
def flagVals (u : Fin 10 → ℕ) : Fin 10 → ℕ := fun k =>
  if (k : ℕ) = 2 then 4
  else if (k : ℕ) = 3 then 4 - u 1
  else if (k : ℕ) = 4 then (if u 1 < 1 then 1 else 0)
  else if (k : ℕ) = 5 then (if u 1 < 2 then 1 else 0) - (if u 1 < 1 then 1 else 0)
  else if (k : ℕ) = 6 then (if u 1 < 3 then 1 else 0) - (if u 1 < 2 then 1 else 0)
  else if (k : ℕ) = 7 then (if u 1 < 4 then 1 else 0) - (if u 1 < 3 then 1 else 0)
  else if (k : ℕ) = 8 then 1 - (if u 1 < 4 then 1 else 0)
  else u k

/-- The five equality flags, from four comparisons and four differences. -/
def digitFlagsTM (dr : Regs 10 n) : TM n :=
  seqTM (setConstTM (dr 2) 1) (seqTM (ltFlagTM (dr 1) (dr 2) (dr 3) (dr 4))
  (seqTM (setConstTM (dr 2) 2) (seqTM (ltFlagTM (dr 1) (dr 2) (dr 3) (dr 5))
  (seqTM (setConstTM (dr 2) 3) (seqTM (ltFlagTM (dr 1) (dr 2) (dr 3) (dr 6))
  (seqTM (setConstTM (dr 2) 4) (seqTM (ltFlagTM (dr 1) (dr 2) (dr 3) (dr 7))
  (seqTM (setConstTM (dr 8) 1)
  (seqTM (subIntoTM (dr 7) (dr 8)) (seqTM (subIntoTM (dr 6) (dr 7))
  (seqTM (subIntoTM (dr 5) (dr 6)) (subIntoTM (dr 4) (dr 5)))))))))))))

lemma digitFlagsTM_hoareTime (dr : Regs 10 n) (u : Fin 10 → ℕ) (B : ℕ)
    (inp₀ : Tape) (w₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hpark : ∀ i, Parked (w₀ i)) (hB4 : 4 ≤ B)
    (hu : ∀ k, u k ≤ B) :
    (digitFlagsTM dr).HoareTime
      (EmitPred inp₀ (regsWork dr w₀ u) ys)
      (EmitPred inp₀ (regsWork dr w₀ (flagVals u)) ys)
      (13 * evalnArithmeticCost B + 12) := by
  have h1 := setConst_regsWork dr u B inp₀ w₀ ys 2 1 hinp₀ hpark hu (by omega)
  set W1 := Function.update u 2 1 with hW1
  have hw1 : ∀ k, W1 k ≤ B := update_le u B hu (by omega)
  have h2 := ltFlag_regsWork dr W1 B inp₀ w₀ ys 1 2 3 4 (by decide) (by decide) (by decide) hinp₀ hpark hw1
  set W2 := Function.update (Function.update W1 3 (W1 2 - W1 1)) 4
    (if W1 1 < W1 2 then 1 else 0) with hW2
  have hw2 : ∀ k, W2 k ≤ B :=
    update_le _ B (update_le W1 B hw1 (by have := hw1 2; omega)) (by split_ifs <;> omega)
  have h3 := setConst_regsWork dr W2 B inp₀ w₀ ys 2 2 hinp₀ hpark hw2 (by omega)
  set W3 := Function.update W2 2 2 with hW3
  have hw3 : ∀ k, W3 k ≤ B := update_le W2 B hw2 (by omega)
  have h4 := ltFlag_regsWork dr W3 B inp₀ w₀ ys 1 2 3 5 (by decide) (by decide) (by decide) hinp₀ hpark hw3
  set W4 := Function.update (Function.update W3 3 (W3 2 - W3 1)) 5
    (if W3 1 < W3 2 then 1 else 0) with hW4
  have hw4 : ∀ k, W4 k ≤ B :=
    update_le _ B (update_le W3 B hw3 (by have := hw3 2; omega)) (by split_ifs <;> omega)
  have h5 := setConst_regsWork dr W4 B inp₀ w₀ ys 2 3 hinp₀ hpark hw4 (by omega)
  set W5 := Function.update W4 2 3 with hW5
  have hw5 : ∀ k, W5 k ≤ B := update_le W4 B hw4 (by omega)
  have h6 := ltFlag_regsWork dr W5 B inp₀ w₀ ys 1 2 3 6 (by decide) (by decide) (by decide) hinp₀ hpark hw5
  set W6 := Function.update (Function.update W5 3 (W5 2 - W5 1)) 6
    (if W5 1 < W5 2 then 1 else 0) with hW6
  have hw6 : ∀ k, W6 k ≤ B :=
    update_le _ B (update_le W5 B hw5 (by have := hw5 2; omega)) (by split_ifs <;> omega)
  have h7 := setConst_regsWork dr W6 B inp₀ w₀ ys 2 4 hinp₀ hpark hw6 (by omega)
  set W7 := Function.update W6 2 4 with hW7
  have hw7 : ∀ k, W7 k ≤ B := update_le W6 B hw6 (by omega)
  have h8 := ltFlag_regsWork dr W7 B inp₀ w₀ ys 1 2 3 7 (by decide) (by decide) (by decide) hinp₀ hpark hw7
  set W8 := Function.update (Function.update W7 3 (W7 2 - W7 1)) 7
    (if W7 1 < W7 2 then 1 else 0) with hW8
  have hw8 : ∀ k, W8 k ≤ B :=
    update_le _ B (update_le W7 B hw7 (by have := hw7 2; omega)) (by split_ifs <;> omega)
  have h9 := setConst_regsWork dr W8 B inp₀ w₀ ys 8 1 hinp₀ hpark hw8 (by omega)
  set W9 := Function.update W8 8 1 with hW9
  have hw9 : ∀ k, W9 k ≤ B := update_le W8 B hw8 (by omega)
  have h10 := subInto_regsWork dr W9 B inp₀ w₀ ys 7 8 (by decide) hinp₀ hpark hw9
  set W10 := Function.update W9 8 (W9 8 - W9 7) with hW10
  have hw10 : ∀ k, W10 k ≤ B := update_le W9 B hw9 (by have := hw9 8; omega)
  have h11 := subInto_regsWork dr W10 B inp₀ w₀ ys 6 7 (by decide) hinp₀ hpark hw10
  set W11 := Function.update W10 7 (W10 7 - W10 6) with hW11
  have hw11 : ∀ k, W11 k ≤ B := update_le W10 B hw10 (by have := hw10 7; omega)
  have h12 := subInto_regsWork dr W11 B inp₀ w₀ ys 5 6 (by decide) hinp₀ hpark hw11
  set W12 := Function.update W11 6 (W11 6 - W11 5) with hW12
  have hw12 : ∀ k, W12 k ≤ B := update_le W11 B hw11 (by have := hw11 6; omega)
  have h13 := subInto_regsWork dr W12 B inp₀ w₀ ys 4 5 (by decide) hinp₀ hpark hw12
  set W13 := Function.update W12 5 (W12 5 - W12 4) with hW13
  have hw13 : ∀ k, W13 k ≤ B := update_le W12 B hw12 (by have := hw12 5; omega)
  have hfinal : W13 = flagVals u := by
    funext k
    fin_cases k <;>
      simp [flagVals, hW13, hW12, hW11, hW10, hW9, hW8, hW7, hW6, hW5, hW4, hW3, hW2, hW1, Function.update_apply] <;> omega
  rw [hfinal] at h13
  exact (seqEmit hinp₀ (parked_regsWork dr hpark W1) h1
    (seqEmit hinp₀ (parked_regsWork dr hpark W2) h2
    (seqEmit hinp₀ (parked_regsWork dr hpark W3) h3
    (seqEmit hinp₀ (parked_regsWork dr hpark W4) h4
    (seqEmit hinp₀ (parked_regsWork dr hpark W5) h5
    (seqEmit hinp₀ (parked_regsWork dr hpark W6) h6
    (seqEmit hinp₀ (parked_regsWork dr hpark W7) h7
    (seqEmit hinp₀ (parked_regsWork dr hpark W8) h8
    (seqEmit hinp₀ (parked_regsWork dr hpark W9) h9
    (seqEmit hinp₀ (parked_regsWork dr hpark W10) h10
    (seqEmit hinp₀ (parked_regsWork dr hpark W11) h11
    (seqEmit hinp₀ (parked_regsWork dr hpark W12) h12
    h13)))))))))))).mono_bound (by omega)


/-- Emit the clamped digit as three bits: five guards, exactly one of which fires. -/
def digitEmitTM (dr : Regs 10 n) : TM n :=
  seqTM (guardTM (emitBitsTM (digitBits 0)) (dr 4))
  (seqTM (guardTM (emitBitsTM (digitBits 1)) (dr 5))
  (seqTM (guardTM (emitBitsTM (digitBits 2)) (dr 6))
  (seqTM (guardTM (emitBitsTM (digitBits 3)) (dr 7))
         (guardTM (emitBitsTM (digitBits 4)) (dr 8)))))

lemma digitEmitTM_hoareTime (dr : Regs 10 n) (x : Fin 10 → ℕ) (g : ℕ) (hg : g ≤ 4)
    (inp₀ : Tape) (w₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hpark : ∀ i, Parked (w₀ i))
    (e0 : x 4 = if g = 0 then 1 else 0) (e1 : x 5 = if g = 1 then 1 else 0)
    (e2 : x 6 = if g = 2 then 1 else 0) (e3 : x 7 = if g = 3 then 1 else 0)
    (e4 : x 8 = if g = 4 then 1 else 0) :
    (digitEmitTM dr).HoareTime
      (EmitPred inp₀ (regsWork dr w₀ x) ys)
      (EmitPred inp₀ (regsWork dr w₀ x) (ys ++ digitBits g))
      44 := by
  have hpx := parked_regsWork dr hpark x
  have hb : ∀ (c : ℕ) (q : Fin 10) (zs : List Bool), x q = (if g = c then 1 else 0) →
      (guardTM (emitBitsTM (digitBits c)) (dr q)).HoareTime
        (EmitPred inp₀ (regsWork dr w₀ x) zs)
        (EmitPred inp₀ (regsWork dr w₀ x)
          (zs ++ if g = c then digitBits c else [])) 8 := by
    intro c q zs hq
    have hx1 : x q ≤ 1 := by rw [hq]; split_ifs <;> omega
    have hcase : (if x q = 0 then ([] : List Bool) else digitBits c)
        = if g = c then digitBits c else [] := by
      rw [hq]; split_ifs <;> simp_all
    refine ((guardEmit_hoareTime (digitBits c) (dr q) (x q) hx1
      inp₀ (regsWork dr w₀ x) zs hinp₀ hpx
      (regsWork_apply dr w₀ x q)).mono_bound ?_).consequence (fun _ _ _ h => h)
      (fun _ _ _ h => by rwa [hcase] at h) (le_refl _)
    simp only [length_digitBits]
    omega
  have hchain := seqEmitOut hinp₀ hpx (hb 0 4 ys e0)
    (seqEmitOut hinp₀ hpx (hb 1 5 _ e1)
      (seqEmitOut hinp₀ hpx (hb 2 6 _ e2)
        (seqEmitOut hinp₀ hpx (hb 3 7 _ e3) (hb 4 8 _ e4))))
  have hword : ((((ys ++ if g = 0 then digitBits 0 else [])
        ++ if g = 1 then digitBits 1 else [])
        ++ if g = 2 then digitBits 2 else [])
        ++ if g = 3 then digitBits 3 else [])
        ++ (if g = 4 then digitBits 4 else [])
      = ys ++ digitBits g := by
    interval_cases g <;> simp
  rw [hword] at hchain
  exact hchain.mono_bound (by omega)


lemma clampVals_one (v : Fin 10 → ℕ) : clampVals v 1 = min (v 0) 4 := rfl

lemma clampVals_le (v : Fin 10 → ℕ) (B : ℕ) (hB4 : 4 ≤ B) (hv : ∀ k, v k ≤ B) :
    ∀ k, clampVals v k ≤ B := by
  intro k
  simp only [clampVals]
  split_ifs
  · have := hv 0; omega
  · omega
  · have := hv 0; omega
  · exact hv k

lemma flagVals_le (u : Fin 10 → ℕ) (B : ℕ) (hB4 : 4 ≤ B) (hu : ∀ k, u k ≤ B) :
    ∀ k, flagVals u k ≤ B := by
  intro k
  simp only [flagVals]
  split_ifs <;> first | omega | exact hu k

/-- The digit block's final register values. -/
def digitVals (v : Fin 10 → ℕ) : Fin 10 → ℕ := flagVals (clampVals v)

/-- **The digit block.** Clamp the token at the terminator, compute the five equality
    flags, and emit the three bits `bitsToDigits` reads back as the clamp. -/
def digitTM (dr : Regs 10 n) : TM n :=
  seqTM (clampTM dr) (seqTM (digitFlagsTM dr) (digitEmitTM dr))

lemma digitTM_hoareTime (dr : Regs 10 n) (v : Fin 10 → ℕ) (B : ℕ)
    (inp₀ : Tape) (w₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hpark : ∀ i, Parked (w₀ i)) (hB4 : 4 ≤ B)
    (hv : ∀ k, v k ≤ B) :
    (digitTM dr).HoareTime
      (EmitPred inp₀ (regsWork dr w₀ v) ys)
      (EmitPred inp₀ (regsWork dr w₀ (digitVals v)) (ys ++ digitBits (min (v 0) 4)))
      (18 * evalnArithmeticCost B + 62) := by
  have hcl := clampTM_hoareTime dr v B inp₀ w₀ ys hinp₀ hpark hB4 hv
  have hclv := clampVals_le v B hB4 hv
  have hfl := digitFlagsTM_hoareTime dr (clampVals v) B inp₀ w₀ ys hinp₀ hpark hB4 hclv
  have hg4 : min (v 0) 4 ≤ 4 := Nat.min_le_right _ _
  have hone : clampVals v 1 = min (v 0) 4 := clampVals_one v
  have hem := digitEmitTM_hoareTime dr (flagVals (clampVals v)) (min (v 0) 4) hg4
    inp₀ w₀ ys hinp₀ hpark
    (by show flagVals (clampVals v) 4 = _
        simp only [flagVals, hone]
        norm_num
        try split_ifs <;> omega)
    (by show flagVals (clampVals v) 5 = _
        simp only [flagVals, hone]
        norm_num
        try split_ifs <;> omega)
    (by show flagVals (clampVals v) 6 = _
        simp only [flagVals, hone]
        norm_num
        try split_ifs <;> omega)
    (by show flagVals (clampVals v) 7 = _
        simp only [flagVals, hone]
        norm_num
        try split_ifs <;> omega)
    (by show flagVals (clampVals v) 8 = _
        simp only [flagVals, hone]
        norm_num
        try split_ifs <;> omega)
  exact (seqEmitOut hinp₀ (parked_regsWork dr hpark _) hcl
    (seqEmitOut hinp₀ (parked_regsWork dr hpark _) hfl hem)).mono_bound (by omega)

section Layout
variable (lc tc : Nat.Partrec.Code)

def totalRegs : ℕ := 32 + codeRegs lc + codeRegs tc

def selfW : Fin 32 ↪ Fin (totalRegs lc tc) := shiftEmb 0 (by rw [totalRegs]; omega)
def pairW : Fin 8 ↪ Fin (totalRegs lc tc) := shiftEmb 9 (by rw [totalRegs]; omega)
def digW : Fin 10 ↪ Fin (totalRegs lc tc) := shiftEmb 17 (by rw [totalRegs]; omega)
def lcW : Fin (codeRegs lc) ↪ Fin (totalRegs lc tc) :=
  shiftEmb 32 (by rw [totalRegs]; omega)
def tcW : Fin (codeRegs tc) ↪ Fin (totalRegs lc tc) :=
  shiftEmb (32 + codeRegs lc) (le_of_eq (by rw [totalRegs]))

lemma pairW_ne (i j : Fin 8) (h : (i : ℕ) ≠ (j : ℕ)) : pairW lc tc i ≠ pairW lc tc j :=
  amb_ne _ _ i j (by omega)

lemma selfW_ne (i j : Fin 32) (h : (i : ℕ) ≠ (j : ℕ)) : selfW lc tc i ≠ selfW lc tc j :=
  amb_ne _ _ i j (by omega)

lemma pairW_ne_selfW (i : Fin 8) (j : Fin 32) (h : 9 + (i : ℕ) ≠ (j : ℕ)) :
    pairW lc tc i ≠ selfW lc tc j := amb_ne _ _ i j (by omega)

lemma digW_ne_selfW (i : Fin 10) (j : Fin 32) (h : 17 + (i : ℕ) ≠ (j : ℕ)) :
    digW lc tc i ≠ selfW lc tc j := amb_ne _ _ i j (by omega)

lemma digW_ne_pairW (i : Fin 10) (j : Fin 8) : digW lc tc i ≠ pairW lc tc j :=
  amb_ne _ _ i j (by have := j.isLt; omega)

lemma lcW_ne_selfW (i : Fin (codeRegs lc)) (j : Fin 32) : lcW lc tc i ≠ selfW lc tc j :=
  amb_ne _ _ i j (by have := j.isLt; omega)

lemma tcW_ne_selfW (i : Fin (codeRegs tc)) (j : Fin 32) : tcW lc tc i ≠ selfW lc tc j :=
  amb_ne _ _ i j (by have := j.isLt; omega)

lemma lcW_ne_pairW (i : Fin (codeRegs lc)) (j : Fin 8) : lcW lc tc i ≠ pairW lc tc j :=
  amb_ne _ _ i j (by have := j.isLt; omega)

lemma tcW_ne_pairW (i : Fin (codeRegs tc)) (j : Fin 8) : tcW lc tc i ≠ pairW lc tc j :=
  amb_ne _ _ i j (by have := j.isLt; omega)

lemma lcW_ne_digW (i : Fin (codeRegs lc)) (j : Fin 10) : lcW lc tc i ≠ digW lc tc j :=
  amb_ne _ _ i j (by have := j.isLt; omega)

lemma tcW_ne_digW (i : Fin (codeRegs tc)) (j : Fin 10) : tcW lc tc i ≠ digW lc tc j :=
  amb_ne _ _ i j (by have := j.isLt; omega)

lemma tcW_ne_lcW (i : Fin (codeRegs tc)) (j : Fin (codeRegs lc)) :
    tcW lc tc i ≠ lcW lc tc j := amb_ne _ _ i j (by have := j.isLt; omega)

end Layout

section Body
variable (lc tc : Nat.Partrec.Code)

noncomputable def tokenBodyVals (V : Fin (totalRegs lc tc) → ℕ) :
    Fin (totalRegs lc tc) → ℕ :=
  let V1 := Function.update V (pairW lc tc 0) (V (selfW lc tc 0))
  let V2 := Function.update V1 (pairW lc tc 1) (V1 (selfW lc tc 5))
  let V3 := writeWindow (pairW lc tc) V2 (pairVals (fun j => V2 (pairW lc tc j)))
  let V4 := Function.update V3 (tcW lc tc (codeLocal tc 0)) (V3 (pairW lc tc 6))
  let V5 := Function.update V4 (tcW lc tc (codeLocal tc 1)) (V4 (selfW lc tc 1))
  let V6 := writeWindow (tcW lc tc) V5 (codeVals tc (fun j => V5 (tcW lc tc j)))
  let V7 := Function.update V6 (digW lc tc 0) (V6 (tcW lc tc (codeLocal tc 3)))
  let V8 := writeWindow (digW lc tc) V7 (digitVals (fun j => V7 (digW lc tc j)))
  Function.update V8 (selfW lc tc 5) (V8 (selfW lc tc 5) + 1)

set_option maxHeartbeats 1000000 in
/-- Every working register below the pairing block, other than the loop index, is left
    alone by an iteration. -/
lemma tokenBodyVals_selfW (V : Fin (totalRegs lc tc) → ℕ) (q : Fin 32)
    (hq : (q : ℕ) < 9) (hq5 : (q : ℕ) ≠ 5) :
    tokenBodyVals lc tc V (selfW lc tc q) = V (selfW lc tc q) := by
  simp only [tokenBodyVals]
  rw [Function.update_of_ne (selfW_ne lc tc q 5 (by simpa using hq5)),
    writeWindow_of_ne _ _ _ (fun j => digW_ne_selfW lc tc j q (by have := j.isLt; omega)),
    Function.update_of_ne (Ne.symm (digW_ne_selfW lc tc 0 q (by simp; omega))),
    writeWindow_of_ne _ _ _ (fun j => tcW_ne_selfW lc tc j q),
    Function.update_of_ne (Ne.symm (tcW_ne_selfW lc tc _ q)),
    Function.update_of_ne (Ne.symm (tcW_ne_selfW lc tc _ q)),
    writeWindow_of_ne _ _ _ (fun j => pairW_ne_selfW lc tc j q (by have := j.isLt; omega)),
    Function.update_of_ne (Ne.symm (pairW_ne_selfW lc tc 1 q (by simp; omega))),
    Function.update_of_ne (Ne.symm (pairW_ne_selfW lc tc 0 q (by simp; omega)))]

set_option maxHeartbeats 1000000 in
/-- The loop index advances by one. -/
lemma tokenBodyVals_index (V : Fin (totalRegs lc tc) → ℕ) :
    tokenBodyVals lc tc V (selfW lc tc 5) = V (selfW lc tc 5) + 1 := by
  simp only [tokenBodyVals]
  rw [Function.update_self,
    writeWindow_of_ne _ _ _ (fun j => digW_ne_selfW lc tc j 5 (by have := j.isLt; simp; omega)),
    Function.update_of_ne (Ne.symm (digW_ne_selfW lc tc 0 5 (by decide))),
    writeWindow_of_ne _ _ _ (fun j => tcW_ne_selfW lc tc j 5),
    Function.update_of_ne (Ne.symm (tcW_ne_selfW lc tc _ 5)),
    Function.update_of_ne (Ne.symm (tcW_ne_selfW lc tc _ 5)),
    writeWindow_of_ne _ _ _ (fun j => pairW_ne_selfW lc tc j 5 (by have := j.isLt; simp; omega)),
    Function.update_of_ne (Ne.symm (pairW_ne_selfW lc tc 1 5 (by decide))),
    Function.update_of_ne (Ne.symm (pairW_ne_selfW lc tc 0 5 (by decide)))]

end Body


lemma clampVals_lt (v : Fin 10 → ℕ) (B : ℕ) (hB4 : 4 < B) (hv : ∀ k, v k < B) :
    ∀ k, clampVals v k < B := by
  intro k
  have h0 := hv 0
  have hk := hv k
  simp only [clampVals]
  split_ifs <;> omega

lemma flagVals_lt (u : Fin 10 → ℕ) (B : ℕ) (hB4 : 4 < B) (hu : ∀ k, u k < B) :
    ∀ k, flagVals u k < B := by
  intro k
  have h1 := hu 1
  have hk := hu k
  simp only [flagVals]
  split_ifs <;> omega

/-- The digit block keeps every register inside the bound. -/
lemma digitVals_lt (v : Fin 10 → ℕ) (B : ℕ) (hB5 : 5 ≤ B) (hv : ∀ k, v k < B) :
    ∀ k, digitVals v k < B :=
  flagVals_lt _ B (by omega) (clampVals_lt v B (by omega) hv)

lemma incReg_regsWork (r : Regs m n) (V : Fin m → ℕ) (B : ℕ) (inp₀ : Tape)
    (w₀ : Fin n → Tape) (ys : List Bool) (q : Fin m)
    (hinp₀ : Parked inp₀) (hpark : ∀ i, Parked (w₀ i)) (hv : ∀ k, V k ≤ B) :
    (incRegTM (r q)).HoareTime
      (EmitPred inp₀ (regsWork r w₀ V) ys)
      (EmitPred inp₀ (regsWork r w₀ (Function.update V q (V q + 1))) ys)
      (evalnArithmeticCost B) := by
  have h := incRegTM_hoareTime (r q) (V q) inp₀ (regsWork r w₀ V) ys hinp₀
    (fun i _ => parked_regsWork r hpark V i) (regsWork_apply r w₀ V q)
  rw [regsWork_update] at h
  exact h.mono_bound (regOpTime_le_arith (V q) B (hv q))

lemma update_lt (V : Fin m → ℕ) (B : ℕ) {q : Fin m} {x : ℕ} (hv : ∀ k, V k < B)
    (hx : x < B) : ∀ k, Function.update V q x k < B := by
  intro k
  simp only [Function.update_apply]
  split_ifs
  · exact hx
  · exact hv k

section BodySpec
variable (lc tc : Nat.Partrec.Code)

/-- One iteration: pair the day with the index, run the token program on it under the
    clock, and emit its value as a clamped digit. -/
noncomputable def tokenBodyTM (R : Regs (totalRegs lc tc) n) : TM n :=
  seqTM (copyIntoTM (R (selfW lc tc 0)) (R (pairW lc tc 0))) <|
  seqTM (copyIntoTM (R (selfW lc tc 5)) (R (pairW lc tc 1))) <|
  seqTM (pairTM ((pairW lc tc).trans R)) <|
  seqTM (copyIntoTM (R (pairW lc tc 6)) (R (tcW lc tc (codeLocal tc 0)))) <|
  seqTM (copyIntoTM (R (selfW lc tc 1)) (R (tcW lc tc (codeLocal tc 1)))) <|
  seqTM (compiledTM tc ((tcW lc tc).trans R)) <|
  seqTM (copyIntoTM (R (tcW lc tc (codeLocal tc 3))) (R (digW lc tc 0))) <|
  seqTM (digitTM ((digW lc tc).trans R)) (incRegTM (R (selfW lc tc 5)))

/-- The digit one iteration emits: the token program's value at the paired index, or the
    canonical `0` when it does not return. -/
noncomputable def tokenDigit (V : Fin (totalRegs lc tc) → ℕ) : ℕ :=
  resultVal (Nat.Partrec.Code.evaln (V (selfW lc tc 1)) tc
    (Nat.pair (V (selfW lc tc 0)) (V (selfW lc tc 5))))

lemma tcW_local_ne (i j : Fin 16) (h : i ≠ j) :
    tcW lc tc (codeLocal tc i) ≠ tcW lc tc (codeLocal tc j) :=
  fun e => h ((codeLocal tc).injective ((tcW lc tc).injective e))

set_option maxHeartbeats 2000000 in
lemma tokenBodyTM_hoareTime (R : Regs (totalRegs lc tc) n)
    (V : Fin (totalRegs lc tc) → ℕ) (s B : ℕ)
    (inp₀ : Tape) (w₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hpark : ∀ i, Parked (w₀ i))
    (hB5 : 5 ≤ B) (hsB : s < B) (hV : ∀ k, V k < B)
    (hBtc : codeRegBound tc s ≤ B)
    (hpair : Nat.pair (V (selfW lc tc 0)) (V (selfW lc tc 5)) ≤ s)
    (hclock : V (selfW lc tc 1) ≤ s)
    (hinc : V (selfW lc tc 5) + 1 < B) :
    (tokenBodyTM lc tc R).HoareTime
      (EmitPred inp₀ (regsWork R w₀ V) ys)
      (EmitPred inp₀ (regsWork R w₀ (tokenBodyVals lc tc V))
        (ys ++ digitBits (min (tokenDigit lc tc V) 4)))
      (25 * evalnArithmeticCost B + codeMachineTime tc s (evalnArithmeticCost B) + 70) := by
  -- stage 1: the day into the pairing block
  have h1 := copyInto_regsWork R V B inp₀ w₀ ys (selfW lc tc 0) (pairW lc tc 0)
    (Ne.symm (pairW_ne_selfW lc tc 0 0 (by decide))) hinp₀ hpark (fun k => (hV k).le)
  set V1 := Function.update V (pairW lc tc 0) (V (selfW lc tc 0)) with hV1
  have hv1 : ∀ k, V1 k < B := update_lt V B hV (hV _)
  -- stage 2: the index into the pairing block
  have h2 := copyInto_regsWork R V1 B inp₀ w₀ ys (selfW lc tc 5) (pairW lc tc 1)
    (Ne.symm (pairW_ne_selfW lc tc 1 5 (by decide))) hinp₀ hpark (fun k => (hv1 k).le)
  set V2 := Function.update V1 (pairW lc tc 1) (V1 (selfW lc tc 5)) with hV2
  have hv2 : ∀ k, V2 k < B := update_lt V1 B hv1 (hv1 _)
  -- the two pairing inputs, read back
  have r2a : V2 (pairW lc tc 0) = V (selfW lc tc 0) := by
    rw [hV2, Function.update_of_ne (pairW_ne lc tc 0 1 (by decide)), hV1,
      Function.update_self]
  have r2b : V2 (pairW lc tc 1) = V (selfW lc tc 5) := by
    rw [hV2, Function.update_self, hV1,
      Function.update_of_ne (Ne.symm (pairW_ne_selfW lc tc 0 5 (by decide)))]
  -- stage 3: the pair
  have h3 := runChildFixed (pairW lc tc) R (pairTM ((pairW lc tc).trans R)) pairVals
    (evalnArithmeticCost B) w₀ hpark V2
    (fun Wb hWb => pairTM_hoareTime_arith ((pairW lc tc).trans R)
      (fun j => V2 (pairW lc tc j)) B inp₀ Wb ys hinp₀ hWb (fun k => (hv2 _).le))
  set V3 := writeWindow (pairW lc tc) V2 (pairVals (fun j => V2 (pairW lc tc j)))
    with hV3
  have hv3 : ∀ k, V3 k < B := by
    intro k
    rw [hV3]
    refine writeWindow_bounded _ _ _ B hv2 (fun j => ?_) k
    refine pairVals_lt _ B (by omega) (fun i => hv2 _) ?_ j
    show Nat.pair (V2 (pairW lc tc 0)) (V2 (pairW lc tc 1)) < B
    rw [r2a, r2b]
    omega
  have r3 : V3 (pairW lc tc 6) = Nat.pair (V (selfW lc tc 0)) (V (selfW lc tc 5)) := by
    rw [hV3, writeWindow_apply]
    have hp6 : pairVals (fun j => V2 (pairW lc tc j)) 6
        = Nat.pair (V2 (pairW lc tc 0)) (V2 (pairW lc tc 1)) := by simp [pairVals]
    rw [hp6, r2a, r2b]
  -- stage 4: the pair into the token program's input register
  have h4 := copyInto_regsWork R V3 B inp₀ w₀ ys (pairW lc tc 6)
    (tcW lc tc (codeLocal tc 0)) (Ne.symm (tcW_ne_pairW lc tc _ 6)) hinp₀ hpark
    (fun k => (hv3 k).le)
  set V4 := Function.update V3 (tcW lc tc (codeLocal tc 0)) (V3 (pairW lc tc 6)) with hV4
  have hv4 : ∀ k, V4 k < B := update_lt V3 B hv3 (hv3 _)
  have r4 : V4 (selfW lc tc 1) = V (selfW lc tc 1) := by
    rw [hV4, Function.update_of_ne (Ne.symm (tcW_ne_selfW lc tc _ 1)), hV3,
      writeWindow_of_ne _ _ _ (fun j => pairW_ne_selfW lc tc j 1 (by have := j.isLt; simp; omega)),
      hV2, Function.update_of_ne (Ne.symm (pairW_ne_selfW lc tc 1 1 (by decide))), hV1,
      Function.update_of_ne (Ne.symm (pairW_ne_selfW lc tc 0 1 (by decide)))]
  -- stage 5: the clock into the token program's fuel register
  have h5 := copyInto_regsWork R V4 B inp₀ w₀ ys (selfW lc tc 1)
    (tcW lc tc (codeLocal tc 1)) (Ne.symm (tcW_ne_selfW lc tc _ 1)) hinp₀ hpark
    (fun k => (hv4 k).le)
  set V5 := Function.update V4 (tcW lc tc (codeLocal tc 1)) (V4 (selfW lc tc 1)) with hV5
  have hv5 : ∀ k, V5 k < B := update_lt V4 B hv4 (hv4 _)
  have r5a : V5 (tcW lc tc (codeLocal tc 0))
      = Nat.pair (V (selfW lc tc 0)) (V (selfW lc tc 5)) := by
    rw [hV5, Function.update_of_ne (tcW_local_ne lc tc 0 1 (by decide)), hV4,
      Function.update_self, r3]
  have r5b : V5 (tcW lc tc (codeLocal tc 1)) = V (selfW lc tc 1) := by
    rw [hV5, Function.update_self, r4]
  -- stage 6: the token program
  have hin0 : (fun j => V5 (tcW lc tc j)) (codeLocal tc 0) ≤ s := by
    show V5 (tcW lc tc (codeLocal tc 0)) ≤ s
    rw [r5a]; exact hpair
  have hin1 : (fun j => V5 (tcW lc tc j)) (codeLocal tc 1) ≤ s := by
    show V5 (tcW lc tc (codeLocal tc 1)) ≤ s
    rw [r5b]; exact hclock
  have h6 := runChildFixed (tcW lc tc) R (compiledTM tc ((tcW lc tc).trans R))
    (codeVals tc) (codeMachineTime tc s (evalnArithmeticCost B)) w₀ hpark V5
    (fun Wb hWb => compiledTM_hoareTime tc ((tcW lc tc).trans R)
      (fun j => V5 (tcW lc tc j)) s B inp₀ Wb ys hinp₀ hWb hBtc (fun k => hv5 _)
      hin0 hin1)
  set V6 := writeWindow (tcW lc tc) V5 (codeVals tc (fun j => V5 (tcW lc tc j)))
    with hV6
  have hv6 : ∀ k, V6 k < B := by
    intro k
    rw [hV6]
    exact writeWindow_bounded _ _ _ B hv5
      (fun j => codeVals_lt tc s B _ hBtc (fun i => hv5 _) hin0 hin1 j) k
  have r6 : V6 (tcW lc tc (codeLocal tc 3)) = tokenDigit lc tc V := by
    rw [hV6, writeWindow_apply, tokenDigit, ← r5a, ← r5b]
    exact (codeVals_encodes tc (fun j => V5 (tcW lc tc j))).2
  -- stage 7: the value into the digit block
  have h7 := copyInto_regsWork R V6 B inp₀ w₀ ys (tcW lc tc (codeLocal tc 3))
    (digW lc tc 0) (tcW_ne_digW lc tc _ 0) hinp₀ hpark (fun k => (hv6 k).le)
  set V7 := Function.update V6 (digW lc tc 0) (V6 (tcW lc tc (codeLocal tc 3))) with hV7
  have hv7 : ∀ k, V7 k < B := update_lt V6 B hv6 (hv6 _)
  have r7 : V7 (digW lc tc 0) = tokenDigit lc tc V := by
    rw [hV7, Function.update_self, r6]
  -- stage 8: the digit block
  have h8 := runChildFixed (digW lc tc) R (digitTM ((digW lc tc).trans R)) digitVals
    (18 * evalnArithmeticCost B + 62) w₀ hpark V7
    (fun Wb hWb => digitTM_hoareTime ((digW lc tc).trans R) (fun j => V7 (digW lc tc j))
      B inp₀ Wb ys hinp₀ hWb (by omega) (fun k => (hv7 _).le))
  rw [r7] at h8
  set V8 := writeWindow (digW lc tc) V7 (digitVals (fun j => V7 (digW lc tc j))) with hV8
  have hv8 : ∀ k, V8 k < B := by
    intro k
    rw [hV8]
    exact writeWindow_bounded _ _ _ B hv7
      (fun j => digitVals_lt _ B hB5 (fun i => hv7 _) j) k
  have r8 : V8 (selfW lc tc 5) = V (selfW lc tc 5) := by
    rw [hV8,
      writeWindow_of_ne _ _ _ (fun j => digW_ne_selfW lc tc j 5 (by have := j.isLt; simp; omega)),
      hV7, Function.update_of_ne (Ne.symm (digW_ne_selfW lc tc 0 5 (by decide))), hV6,
      writeWindow_of_ne _ _ _ (fun j => tcW_ne_selfW lc tc j 5), hV5,
      Function.update_of_ne (Ne.symm (tcW_ne_selfW lc tc _ 5)), hV4,
      Function.update_of_ne (Ne.symm (tcW_ne_selfW lc tc _ 5)), hV3,
      writeWindow_of_ne _ _ _ (fun j => pairW_ne_selfW lc tc j 5 (by have := j.isLt; simp; omega)),
      hV2, Function.update_of_ne (Ne.symm (pairW_ne_selfW lc tc 1 5 (by decide))), hV1,
      Function.update_of_ne (Ne.symm (pairW_ne_selfW lc tc 0 5 (by decide)))]
  -- stage 9: advance the index
  have h9 := incReg_regsWork R V8 B inp₀ w₀ (ys ++ digitBits (min (tokenDigit lc tc V) 4))
    (selfW lc tc 5) hinp₀ hpark (fun k => (hv8 k).le)
  rw [r8] at h9
  have hfinal : Function.update V8 (selfW lc tc 5) (V (selfW lc tc 5) + 1)
      = tokenBodyVals lc tc V := by
    rw [← r8, hV8, hV7, hV6, hV5, hV4, hV3, hV2, hV1, tokenBodyVals]
  rw [hfinal] at h9
  exact (seqEmitOut hinp₀ (parked_regsWork R hpark V1) h1
    (seqEmitOut hinp₀ (parked_regsWork R hpark V2) h2
      (seqEmitOut hinp₀ (parked_regsWork R hpark V3) h3
        (seqEmitOut hinp₀ (parked_regsWork R hpark V4) h4
          (seqEmitOut hinp₀ (parked_regsWork R hpark V5) h5
            (seqEmitOut hinp₀ (parked_regsWork R hpark V6) h6
              (seqEmitOut hinp₀ (parked_regsWork R hpark V7) h7
                (seqEmitOut hinp₀ (parked_regsWork R hpark V8) h8
                  h9)))))))).mono_bound (by omega)

end BodySpec


section BodyBound
variable (lc tc : Nat.Partrec.Code)

set_option maxHeartbeats 1000000 in
/-- An iteration keeps every register inside the bound. -/
lemma tokenBodyVals_lt (V : Fin (totalRegs lc tc) → ℕ) (s B : ℕ)
    (hB5 : 5 ≤ B) (hsB : s < B) (hV : ∀ k, V k < B)
    (hBtc : codeRegBound tc s ≤ B)
    (hpair : Nat.pair (V (selfW lc tc 0)) (V (selfW lc tc 5)) ≤ s)
    (hclock : V (selfW lc tc 1) ≤ s)
    (hinc : V (selfW lc tc 5) + 1 < B) :
    ∀ k, tokenBodyVals lc tc V k < B := by
  simp only [tokenBodyVals]
  set V1 := Function.update V (pairW lc tc 0) (V (selfW lc tc 0)) with hV1
  have hv1 : ∀ k, V1 k < B := update_lt V B hV (hV _)
  set V2 := Function.update V1 (pairW lc tc 1) (V1 (selfW lc tc 5)) with hV2
  have hv2 : ∀ k, V2 k < B := update_lt V1 B hv1 (hv1 _)
  have r2a : V2 (pairW lc tc 0) = V (selfW lc tc 0) := by
    rw [hV2, Function.update_of_ne (pairW_ne lc tc 0 1 (by decide)), hV1,
      Function.update_self]
  have r2b : V2 (pairW lc tc 1) = V (selfW lc tc 5) := by
    rw [hV2, Function.update_self, hV1,
      Function.update_of_ne (Ne.symm (pairW_ne_selfW lc tc 0 5 (by decide)))]
  set V3 := writeWindow (pairW lc tc) V2 (pairVals (fun j => V2 (pairW lc tc j)))
    with hV3
  have hv3 : ∀ k, V3 k < B := by
    intro k
    rw [hV3]
    refine writeWindow_bounded _ _ _ B hv2 (fun j => ?_) k
    refine pairVals_lt _ B (by omega) (fun i => hv2 _) ?_ j
    show Nat.pair (V2 (pairW lc tc 0)) (V2 (pairW lc tc 1)) < B
    rw [r2a, r2b]
    omega
  have r3 : V3 (pairW lc tc 6) = Nat.pair (V (selfW lc tc 0)) (V (selfW lc tc 5)) := by
    rw [hV3, writeWindow_apply]
    have hp6 : pairVals (fun j => V2 (pairW lc tc j)) 6
        = Nat.pair (V2 (pairW lc tc 0)) (V2 (pairW lc tc 1)) := by simp [pairVals]
    rw [hp6, r2a, r2b]
  set V4 := Function.update V3 (tcW lc tc (codeLocal tc 0)) (V3 (pairW lc tc 6)) with hV4
  have hv4 : ∀ k, V4 k < B := update_lt V3 B hv3 (hv3 _)
  have r4 : V4 (selfW lc tc 1) = V (selfW lc tc 1) := by
    rw [hV4, Function.update_of_ne (Ne.symm (tcW_ne_selfW lc tc _ 1)), hV3,
      writeWindow_of_ne _ _ _
        (fun j => pairW_ne_selfW lc tc j 1 (by have := j.isLt; simp; omega)),
      hV2, Function.update_of_ne (Ne.symm (pairW_ne_selfW lc tc 1 1 (by decide))), hV1,
      Function.update_of_ne (Ne.symm (pairW_ne_selfW lc tc 0 1 (by decide)))]
  set V5 := Function.update V4 (tcW lc tc (codeLocal tc 1)) (V4 (selfW lc tc 1)) with hV5
  have hv5 : ∀ k, V5 k < B := update_lt V4 B hv4 (hv4 _)
  have r5a : V5 (tcW lc tc (codeLocal tc 0))
      = Nat.pair (V (selfW lc tc 0)) (V (selfW lc tc 5)) := by
    rw [hV5, Function.update_of_ne (tcW_local_ne lc tc 0 1 (by decide)), hV4,
      Function.update_self, r3]
  have r5b : V5 (tcW lc tc (codeLocal tc 1)) = V (selfW lc tc 1) := by
    rw [hV5, Function.update_self, r4]
  have hin0 : (fun j => V5 (tcW lc tc j)) (codeLocal tc 0) ≤ s := by
    show V5 (tcW lc tc (codeLocal tc 0)) ≤ s
    rw [r5a]; exact hpair
  have hin1 : (fun j => V5 (tcW lc tc j)) (codeLocal tc 1) ≤ s := by
    show V5 (tcW lc tc (codeLocal tc 1)) ≤ s
    rw [r5b]; exact hclock
  set V6 := writeWindow (tcW lc tc) V5 (codeVals tc (fun j => V5 (tcW lc tc j)))
    with hV6
  have hv6 : ∀ k, V6 k < B := by
    intro k
    rw [hV6]
    exact writeWindow_bounded _ _ _ B hv5
      (fun j => codeVals_lt tc s B _ hBtc (fun i => hv5 _) hin0 hin1 j) k
  set V7 := Function.update V6 (digW lc tc 0) (V6 (tcW lc tc (codeLocal tc 3))) with hV7
  have hv7 : ∀ k, V7 k < B := update_lt V6 B hv6 (hv6 _)
  set V8 := writeWindow (digW lc tc) V7 (digitVals (fun j => V7 (digW lc tc j))) with hV8
  have hv8 : ∀ k, V8 k < B := by
    intro k
    rw [hV8]
    exact writeWindow_bounded _ _ _ B hv7
      (fun j => digitVals_lt _ B hB5 (fun i => hv7 _) j) k
  have r8 : V8 (selfW lc tc 5) = V (selfW lc tc 5) := by
    rw [hV8,
      writeWindow_of_ne _ _ _
        (fun j => digW_ne_selfW lc tc j 5 (by have := j.isLt; simp; omega)),
      hV7, Function.update_of_ne (Ne.symm (digW_ne_selfW lc tc 0 5 (by decide))), hV6,
      writeWindow_of_ne _ _ _ (fun j => tcW_ne_selfW lc tc j 5), hV5,
      Function.update_of_ne (Ne.symm (tcW_ne_selfW lc tc _ 5)), hV4,
      Function.update_of_ne (Ne.symm (tcW_ne_selfW lc tc _ 5)), hV3,
      writeWindow_of_ne _ _ _
        (fun j => pairW_ne_selfW lc tc j 5 (by have := j.isLt; simp; omega)),
      hV2, Function.update_of_ne (Ne.symm (pairW_ne_selfW lc tc 1 5 (by decide))), hV1,
      Function.update_of_ne (Ne.symm (pairW_ne_selfW lc tc 0 5 (by decide)))]
  rw [r8]
  exact update_lt V8 B hv8 hinc

end BodyBound

/-! ## The emission loop -/

section Loop
variable (lc tc : Nat.Partrec.Code)

/-- The register values after `i` iterations. -/
noncomputable def tokenLoopVals (V₀ : Fin (totalRegs lc tc) → ℕ) :
    ℕ → Fin (totalRegs lc tc) → ℕ
  | 0 => V₀
  | i + 1 => tokenBodyVals lc tc (tokenLoopVals V₀ i)

/-- The output word after `i` iterations. -/
noncomputable def tokenLoopYs (V₀ : Fin (totalRegs lc tc) → ℕ) (ys : List Bool) :
    ℕ → List Bool
  | 0 => ys
  | i + 1 => tokenLoopYs V₀ ys i
      ++ digitBits (min (tokenDigit lc tc (tokenLoopVals lc tc V₀ i)) 4)

lemma tokenLoopVals_index (V₀ : Fin (totalRegs lc tc) → ℕ) :
    ∀ i, tokenLoopVals lc tc V₀ i (selfW lc tc 5) = V₀ (selfW lc tc 5) + i
  | 0 => rfl
  | i + 1 => by
      rw [tokenLoopVals, tokenBodyVals_index, tokenLoopVals_index V₀ i]
      omega

lemma tokenLoopVals_selfW (V₀ : Fin (totalRegs lc tc) → ℕ) (q : Fin 32)
    (hq : (q : ℕ) < 9) (hq5 : (q : ℕ) ≠ 5) :
    ∀ i, tokenLoopVals lc tc V₀ i (selfW lc tc q) = V₀ (selfW lc tc q)
  | 0 => rfl
  | i + 1 => by
      rw [tokenLoopVals, tokenBodyVals_selfW lc tc _ q hq hq5,
        tokenLoopVals_selfW V₀ q hq hq5 i]

/-- Every level of the loop keeps every register inside the bound. -/
lemma tokenLoopVals_lt (V₀ : Fin (totalRegs lc tc) → ℕ) (s B count : ℕ)
    (hB5 : 5 ≤ B) (hsB : s < B) (hBtc : codeRegBound tc s ≤ B)
    (hV₀ : ∀ k, V₀ k < B) (hidx : V₀ (selfW lc tc 5) = 0)
    (hs : Nat.pair (V₀ (selfW lc tc 0)) count ≤ s)
    (hCs : V₀ (selfW lc tc 1) ≤ s) (hcB : count < B) :
    ∀ i, i ≤ count → ∀ k, tokenLoopVals lc tc V₀ i k < B := by
  intro i
  induction i with
  | zero => intro _ k; exact hV₀ k
  | succ j ih =>
      intro hj k
      rw [tokenLoopVals]
      refine tokenBodyVals_lt lc tc _ s B hB5 hsB (ih (by omega)) hBtc ?_ ?_ ?_ k
      · rw [tokenLoopVals_selfW lc tc V₀ 0 (by decide) (by decide),
          tokenLoopVals_index, hidx]
        exact le_trans (natPair_mono (le_refl _) (by omega)) hs
      · rw [tokenLoopVals_selfW lc tc V₀ 1 (by decide) (by decide)]
        exact hCs
      · rw [tokenLoopVals_index, hidx]
        omega

lemma tokenLoop_hoareTime (R : Regs (totalRegs lc tc) n) (l : Fin n)
    (hl : ∀ k, R k ≠ l) (V₀ : Fin (totalRegs lc tc) → ℕ) (s B count : ℕ)
    (inp₀ : Tape) (w₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hpark : ∀ i, Parked (w₀ i)) (hw₀l : w₀ l = regTape count)
    (hB5 : 5 ≤ B) (hsB : s < B) (hBtc : codeRegBound tc s ≤ B)
    (hV₀ : ∀ k, V₀ k < B) (hidx : V₀ (selfW lc tc 5) = 0)
    (hs : Nat.pair (V₀ (selfW lc tc 0)) count ≤ s)
    (hCs : V₀ (selfW lc tc 1) ≤ s) (hcB : count < B) :
    (forRegTM (tokenBodyTM lc tc R) l).HoareTime
      (EmitPred inp₀ (regsWork R w₀ V₀) ys)
      (EmitPred inp₀ (regsWork R w₀ (tokenLoopVals lc tc V₀ count))
        (tokenLoopYs lc tc V₀ ys count))
      (count * ((25 * evalnArithmeticCost B
        + codeMachineTime tc s (evalnArithmeticCost B) + 70) + 2) + (count + 2)) := by
  have hlt := tokenLoopVals_lt lc tc V₀ s B count hB5 hsB hBtc hV₀ hidx hs hCs hcB
  refine forRegs_hoareTime R (tokenBodyTM lc tc R) l hl count _
    (tokenLoopVals lc tc V₀) inp₀ w₀ (tokenLoopYs lc tc V₀ ys) hinp₀ hpark hw₀l ?_
  intro i hi w hw
  have hbody := tokenBodyTM_hoareTime lc tc R (tokenLoopVals lc tc V₀ i) s B inp₀ w
    (tokenLoopYs lc tc V₀ ys i) hinp₀ hw hB5 hsB (hlt i (Nat.le_of_lt hi)) hBtc
    (by rw [tokenLoopVals_selfW lc tc V₀ 0 (by decide) (by decide),
          tokenLoopVals_index, hidx]
        exact le_trans (natPair_mono (le_refl _) (by omega)) hs)
    (by rw [tokenLoopVals_selfW lc tc V₀ 1 (by decide) (by decide)]; exact hCs)
    (by rw [tokenLoopVals_index, hidx]; omega)
  exact hbody

end Loop


/-! ## The clock, the length call, and the loop count -/

section Setup
variable (lc tc : Nat.Partrec.Code)

/-- The paper's day clock, as a polynomial. -/
noncomputable def clockPoly (a k : ℕ) : Polynomial ℕ :=
  Polynomial.C a * (Polynomial.X + 1) ^ k + Polynomial.C a

/-- The day clock at day `N`. -/
def clockOf (a k N : ℕ) : ℕ := a * (N + 1) ^ k + a

lemma clockPoly_eval (a k x : ℕ) : (clockPoly a k).eval x = clockOf a k x := by
  simp [clockPoly, clockOf]

/-- The Horner prefix bound `polyEvalTM` asks for, at the clock polynomial. -/
noncomputable def hornerCap (a k x : ℕ) : ℕ :=
  ((polyCoeffs (clockPoly a k)).sum + 1) * (x + 1) ^ (polyCoeffs (clockPoly a k)).length

lemma hornerCap_spec (a k x : ℕ) :
    ∀ j, j ≤ (clockPoly a k).natDegree + 1 →
      hornerFold x (List.take j (polyCoeffs (clockPoly a k))) 0 ≤ hornerCap a k x :=
  fun _ _ => hornerFold_take_le x _ _

/-- The setup's register values: the day, the clock, the length program's answer, the
    loop count, and the loop index. -/
noncomputable def setupVals (a k N : ℕ) (V : Fin (totalRegs lc tc) → ℕ) :
    Fin (totalRegs lc tc) → ℕ :=
  let V1 := Function.update V (selfW lc tc 0) N
  let V2 := Function.update (Function.update V1 (selfW lc tc 6)
    ((clockPoly a k).eval N)) (selfW lc tc 1) ((clockPoly a k).eval N)
  let V3 := Function.update V2 (lcW lc tc (codeLocal lc 0)) (V2 (selfW lc tc 0))
  let V4 := Function.update V3 (lcW lc tc (codeLocal lc 1)) (V3 (selfW lc tc 1))
  let V5 := writeWindow (lcW lc tc) V4 (codeVals lc (fun j => V4 (lcW lc tc j)))
  let V6 := Function.update V5 (selfW lc tc 2) (V5 (lcW lc tc (codeLocal lc 2)))
  let V7 := Function.update V6 (selfW lc tc 3) (V6 (lcW lc tc (codeLocal lc 3)))
  let V8 := Function.update V7 (selfW lc tc 6) (V7 (selfW lc tc 3))
  let V9 := Function.update V8 (selfW lc tc 6) (V8 (selfW lc tc 6) - V8 (selfW lc tc 1))
  let V10 := Function.update V9 (selfW lc tc 7) (V9 (selfW lc tc 3))
  let V11 := Function.update V10 (selfW lc tc 7)
    (V10 (selfW lc tc 7) - V10 (selfW lc tc 6))
  let V12 := Function.update V11 (selfW lc tc 4) 0
  let V13 := Function.update V12 (selfW lc tc 4)
    (V12 (selfW lc tc 4) + V12 (selfW lc tc 2) * V12 (selfW lc tc 7))
  Function.update V13 (selfW lc tc 5) 0

/-- The number of digits the machine emits: the length program's answer, clamped to the
    clock, and masked by its tag. -/
noncomputable def countOf (a k N : ℕ) : ℕ :=
  resultTag (Nat.Partrec.Code.evaln (clockOf a k N) lc N) *
    min (resultVal (Nat.Partrec.Code.evaln (clockOf a k N) lc N)) (clockOf a k N)

end Setup


section SetupSpec
variable (lc tc : Nat.Partrec.Code)

set_option maxHeartbeats 2000000 in
/-- The four registers the loop reads out of the setup. -/
lemma setupVals_spec (a k N : ℕ) (V : Fin (totalRegs lc tc) → ℕ) :
    setupVals lc tc a k N V (selfW lc tc 0) = N ∧
    setupVals lc tc a k N V (selfW lc tc 1) = clockOf a k N ∧
    setupVals lc tc a k N V (selfW lc tc 4) = countOf lc a k N ∧
    setupVals lc tc a k N V (selfW lc tc 5) = 0 := by
  have hne : ∀ i j : Fin 32, (i : ℕ) ≠ (j : ℕ) →
      selfW lc tc i ≠ selfW lc tc j := fun i j h => selfW_ne lc tc i j h
  simp only [setupVals]
  set V1 := Function.update V (selfW lc tc 0) N with hV1
  set V2 := Function.update (Function.update V1 (selfW lc tc 6)
    ((clockPoly a k).eval N)) (selfW lc tc 1) ((clockPoly a k).eval N) with hV2
  set V3 := Function.update V2 (lcW lc tc (codeLocal lc 0)) (V2 (selfW lc tc 0)) with hV3
  set V4 := Function.update V3 (lcW lc tc (codeLocal lc 1)) (V3 (selfW lc tc 1)) with hV4
  set V5 := writeWindow (lcW lc tc) V4 (codeVals lc (fun j => V4 (lcW lc tc j))) with hV5
  set V6 := Function.update V5 (selfW lc tc 2) (V5 (lcW lc tc (codeLocal lc 2))) with hV6
  set V7 := Function.update V6 (selfW lc tc 3) (V6 (lcW lc tc (codeLocal lc 3))) with hV7
  set V8 := Function.update V7 (selfW lc tc 6) (V7 (selfW lc tc 3)) with hV8
  set V9 := Function.update V8 (selfW lc tc 6) (V8 (selfW lc tc 6) - V8 (selfW lc tc 1))
    with hV9
  set V10 := Function.update V9 (selfW lc tc 7) (V9 (selfW lc tc 3)) with hV10
  set V11 := Function.update V10 (selfW lc tc 7)
    (V10 (selfW lc tc 7) - V10 (selfW lc tc 6)) with hV11
  set V12 := Function.update V11 (selfW lc tc 4) 0 with hV12
  set V13 := Function.update V12 (selfW lc tc 4)
    (V12 (selfW lc tc 4) + V12 (selfW lc tc 2) * V12 (selfW lc tc 7)) with hV13
  -- the day and the clock
  have e2day : V2 (selfW lc tc 0) = N := by
    rw [hV2, Function.update_of_ne (hne 0 1 (by decide)),
      Function.update_of_ne (hne 0 6 (by decide)), hV1, Function.update_self]
  have e2clock : V2 (selfW lc tc 1) = (clockPoly a k).eval N := by
    rw [hV2, Function.update_self]
  have e4in : V4 (lcW lc tc (codeLocal lc 0)) = N := by
    rw [hV4, Function.update_of_ne (fun e => (by decide : (0 : Fin 16) ≠ 1)
        ((codeLocal lc).injective ((lcW lc tc).injective e))), hV3,
      Function.update_self, e2day]
  have e4fuel : V4 (lcW lc tc (codeLocal lc 1)) = (clockPoly a k).eval N := by
    rw [hV4, Function.update_self, hV3,
      Function.update_of_ne (Ne.symm (lcW_ne_selfW lc tc _ 1)), e2clock]
  have e5tag : V5 (lcW lc tc (codeLocal lc 2))
      = resultTag (Nat.Partrec.Code.evaln (clockOf a k N) lc N) := by
    rw [hV5, writeWindow_apply, ← clockPoly_eval a k N, ← e4fuel, ← e4in]
    exact (codeVals_encodes lc (fun j => V4 (lcW lc tc j))).1
  have e6val : V6 (lcW lc tc (codeLocal lc 3))
      = resultVal (Nat.Partrec.Code.evaln (clockOf a k N) lc N) := by
    rw [hV6, Function.update_of_ne (lcW_ne_selfW lc tc _ 2), hV5, writeWindow_apply,
      ← clockPoly_eval a k N, ← e4fuel, ← e4in]
    exact (codeVals_encodes lc (fun j => V4 (lcW lc tc j))).2
  have e7clock : V7 (selfW lc tc 1) = clockOf a k N := by
    rw [hV7, Function.update_of_ne (hne 1 3 (by decide)), hV6,
      Function.update_of_ne (hne 1 2 (by decide)), hV5,
      writeWindow_of_ne _ _ _ (fun j => lcW_ne_selfW lc tc j 1), hV4,
      Function.update_of_ne (Ne.symm (lcW_ne_selfW lc tc _ 1)), hV3,
      Function.update_of_ne (Ne.symm (lcW_ne_selfW lc tc _ 1)), e2clock, clockPoly_eval]
  have e7len : V7 (selfW lc tc 3)
      = resultVal (Nat.Partrec.Code.evaln (clockOf a k N) lc N) := by
    rw [hV7, Function.update_self, e6val]
  have e7tag : V7 (selfW lc tc 2)
      = resultTag (Nat.Partrec.Code.evaln (clockOf a k N) lc N) := by
    rw [hV7, Function.update_of_ne (hne 2 3 (by decide)), hV6, Function.update_self, e5tag]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the day
    rw [Function.update_of_ne (hne 0 5 (by decide)), hV13,
      Function.update_of_ne (hne 0 4 (by decide)), hV12,
      Function.update_of_ne (hne 0 4 (by decide)), hV11,
      Function.update_of_ne (hne 0 7 (by decide)), hV10,
      Function.update_of_ne (hne 0 7 (by decide)), hV9,
      Function.update_of_ne (hne 0 6 (by decide)), hV8,
      Function.update_of_ne (hne 0 6 (by decide)), hV7,
      Function.update_of_ne (hne 0 3 (by decide)), hV6,
      Function.update_of_ne (hne 0 2 (by decide)), hV5,
      writeWindow_of_ne _ _ _ (fun j => lcW_ne_selfW lc tc j 0), hV4,
      Function.update_of_ne (Ne.symm (lcW_ne_selfW lc tc _ 0)), hV3,
      Function.update_of_ne (Ne.symm (lcW_ne_selfW lc tc _ 0)), e2day]
  · -- the clock
    rw [Function.update_of_ne (hne 1 5 (by decide)), hV13,
      Function.update_of_ne (hne 1 4 (by decide)), hV12,
      Function.update_of_ne (hne 1 4 (by decide)), hV11,
      Function.update_of_ne (hne 1 7 (by decide)), hV10,
      Function.update_of_ne (hne 1 7 (by decide)), hV9,
      Function.update_of_ne (hne 1 6 (by decide)), hV8,
      Function.update_of_ne (hne 1 6 (by decide)), e7clock]
  · -- the loop count
    have h4z : V12 (selfW lc tc 4) = 0 := by rw [hV12, Function.update_self]
    have h2 : V12 (selfW lc tc 2)
        = resultTag (Nat.Partrec.Code.evaln (clockOf a k N) lc N) := by
      rw [hV12, Function.update_of_ne (hne 2 4 (by decide)), hV11,
        Function.update_of_ne (hne 2 7 (by decide)), hV10,
        Function.update_of_ne (hne 2 7 (by decide)), hV9,
        Function.update_of_ne (hne 2 6 (by decide)), hV8,
        Function.update_of_ne (hne 2 6 (by decide)), e7tag]
    have h10a : V10 (selfW lc tc 7)
        = resultVal (Nat.Partrec.Code.evaln (clockOf a k N) lc N) := by
      rw [hV10, Function.update_self, hV9,
        Function.update_of_ne (hne 3 6 (by decide)), hV8,
        Function.update_of_ne (hne 3 6 (by decide)), e7len]
    have h10b : V10 (selfW lc tc 6)
        = resultVal (Nat.Partrec.Code.evaln (clockOf a k N) lc N) - clockOf a k N := by
      rw [hV10, Function.update_of_ne (hne 6 7 (by decide)), hV9, Function.update_self,
        hV8, Function.update_self, Function.update_of_ne (hne 1 6 (by decide)),
        e7len, e7clock]
    have h7 : V12 (selfW lc tc 7)
        = min (resultVal (Nat.Partrec.Code.evaln (clockOf a k N) lc N))
            (clockOf a k N) := by
      rw [hV12, Function.update_of_ne (hne 7 4 (by decide)), hV11, Function.update_self,
        h10a, h10b]
      omega
    rw [Function.update_of_ne (hne 4 5 (by decide)), hV13, Function.update_self, h4z,
      h2, h7, countOf]
    omega
  · -- the loop index
    rw [Function.update_self]

end SetupSpec

section SetupMachine
variable (lc tc : Nat.Partrec.Code)

/-- The setup: measure the day, compute the clock, run the length program, and derive the
    number of digits to emit. -/
noncomputable def setupTM (a k : ℕ) (R : Regs (totalRegs lc tc) n) : TM n :=
  seqTM (inputLenRegTM (R (selfW lc tc 0))) <|
  seqTM (polyEvalTM (R (selfW lc tc 0)) (R (selfW lc tc 1)) (R (selfW lc tc 6))
    (clockPoly a k)) <|
  seqTM (copyIntoTM (R (selfW lc tc 0)) (R (lcW lc tc (codeLocal lc 0)))) <|
  seqTM (copyIntoTM (R (selfW lc tc 1)) (R (lcW lc tc (codeLocal lc 1)))) <|
  seqTM (compiledTM lc ((lcW lc tc).trans R)) <|
  seqTM (copyIntoTM (R (lcW lc tc (codeLocal lc 2))) (R (selfW lc tc 2))) <|
  seqTM (copyIntoTM (R (lcW lc tc (codeLocal lc 3))) (R (selfW lc tc 3))) <|
  seqTM (copyIntoTM (R (selfW lc tc 3)) (R (selfW lc tc 6))) <|
  seqTM (subIntoTM (R (selfW lc tc 1)) (R (selfW lc tc 6))) <|
  seqTM (copyIntoTM (R (selfW lc tc 3)) (R (selfW lc tc 7))) <|
  seqTM (subIntoTM (R (selfW lc tc 6)) (R (selfW lc tc 7))) <|
  seqTM (setConstTM (R (selfW lc tc 4)) 0) <|
  seqTM (mulAddIntoTM (R (selfW lc tc 2)) (R (selfW lc tc 7)) (R (selfW lc tc 4)))
    (setConstTM (R (selfW lc tc 5)) 0)

set_option maxHeartbeats 4000000 in
lemma setupTM_hoareTime (a k : ℕ) (R : Regs (totalRegs lc tc) n)
    (x : List Bool) (V : Fin (totalRegs lc tc) → ℕ) (s B : ℕ)
    (w₀ : Fin n → Tape) (hpark : ∀ i, Parked (w₀ i))
    (hV : ∀ i, V i = 0) (hB5 : 5 ≤ B) (hsB : s < B)
    (hNs : x.length ≤ s) (hCs : clockOf a k x.length ≤ s)
    (hcap : hornerCap a k x.length ≤ B)
    (hBlc : codeRegBound lc s ≤ B) :
    (setupTM lc tc a k R).HoareTime
      (EmitPred ⟨1, (Tape.init (x.map Γ.ofBool)).cells⟩ (regsWork R w₀ V) [])
      (EmitPred ⟨1, (Tape.init (x.map Γ.ofBool)).cells⟩
        (regsWork R w₀ (setupVals lc tc a k x.length V)) [])
      (2 * x.length + opBudget B
        + ((clockPoly a k).natDegree + 1) * (layerBudget B + 1)
        + 12 * evalnArithmeticCost B
        + codeMachineTime lc s (evalnArithmeticCost B) + 30) := by
  set inp₀ : Tape := ⟨1, (Tape.init (x.map Γ.ofBool)).cells⟩ with hinp
  have hinp₀ : Parked inp₀ := parked_init_input x
  have hpv := parked_regsWork R hpark
  have hVlt : ∀ k, V k < B := fun k => by rw [hV k]; omega
  -- stage 1: the day
  have h1 := inputLenRegTM_hoareTime (R (selfW lc tc 0)) x (regsWork R w₀ V) []
    (fun i _ => hpv V i) (by rw [regsWork_apply, hV])
  rw [regsWork_update] at h1
  set V1 := Function.update V (selfW lc tc 0) x.length with hV1
  have hv1 : ∀ k, V1 k < B := update_lt V B hVlt (by omega)
  have r1 : V1 (selfW lc tc 0) = x.length := by rw [hV1, Function.update_self]
  -- stage 2: the clock
  have h2 := polyEvalTM_hoareTime (R (selfW lc tc 0)) (R (selfW lc tc 1))
    (R (selfW lc tc 6)) (R.ne (selfW_ne lc tc 0 1 (by decide)))
    (R.ne (selfW_ne lc tc 0 6 (by decide))) (R.ne (selfW_ne lc tc 1 6 (by decide)))
    (clockPoly a k) B (V1 (selfW lc tc 0)) (V1 (selfW lc tc 1)) (V1 (selfW lc tc 6))
    (by rw [r1]; omega) (hv1 _).le (hv1 _).le
    (fun j _ => le_trans (by rw [r1]; exact hornerFold_take_le _ _ _) hcap)
    inp₀ (regsWork R w₀ V1) [] hinp₀ (hpv V1)
    (by rw [regsWork_apply]) (by rw [regsWork_apply]) (by rw [regsWork_apply])
  rw [regsWork_update, regsWork_update, r1] at h2
  set V2 := Function.update (Function.update V1 (selfW lc tc 6)
    ((clockPoly a k).eval x.length)) (selfW lc tc 1)
    ((clockPoly a k).eval x.length) with hV2
  have hCB : (clockPoly a k).eval x.length < B := by
    rw [clockPoly_eval]; omega
  have hv2 : ∀ k, V2 k < B :=
    update_lt _ B (update_lt V1 B hv1 hCB) hCB
  have r2a : V2 (selfW lc tc 0) = x.length := by
    rw [hV2, Function.update_of_ne (selfW_ne lc tc 0 1 (by decide)),
      Function.update_of_ne (selfW_ne lc tc 0 6 (by decide)), r1]
  have r2b : V2 (selfW lc tc 1) = (clockPoly a k).eval x.length := by
    rw [hV2, Function.update_self]
  -- stages 3 and 4: the length program's input and fuel
  have h3 := copyInto_regsWork R V2 B inp₀ w₀ [] (selfW lc tc 0)
    (lcW lc tc (codeLocal lc 0)) (Ne.symm (lcW_ne_selfW lc tc _ 0)) hinp₀ hpark
    (fun k => (hv2 k).le)
  set V3 := Function.update V2 (lcW lc tc (codeLocal lc 0)) (V2 (selfW lc tc 0)) with hV3
  have hv3 : ∀ k, V3 k < B := update_lt V2 B hv2 (hv2 _)
  have h4 := copyInto_regsWork R V3 B inp₀ w₀ [] (selfW lc tc 1)
    (lcW lc tc (codeLocal lc 1)) (Ne.symm (lcW_ne_selfW lc tc _ 1)) hinp₀ hpark
    (fun k => (hv3 k).le)
  set V4 := Function.update V3 (lcW lc tc (codeLocal lc 1)) (V3 (selfW lc tc 1)) with hV4
  have hv4 : ∀ k, V4 k < B := update_lt V3 B hv3 (hv3 _)
  have e4in : (fun j => V4 (lcW lc tc j)) (codeLocal lc 0) ≤ s := by
    show V4 (lcW lc tc (codeLocal lc 0)) ≤ s
    rw [hV4, Function.update_of_ne (fun e => (by decide : (0 : Fin 16) ≠ 1)
        ((codeLocal lc).injective ((lcW lc tc).injective e))), hV3,
      Function.update_self, r2a]
    exact hNs
  have e4fuel : (fun j => V4 (lcW lc tc j)) (codeLocal lc 1) ≤ s := by
    show V4 (lcW lc tc (codeLocal lc 1)) ≤ s
    rw [hV4, Function.update_self, hV3,
      Function.update_of_ne (Ne.symm (lcW_ne_selfW lc tc _ 1)), r2b, clockPoly_eval]
    exact hCs
  -- stage 5: the length program
  have h5 := runChildFixed (lcW lc tc) R (compiledTM lc ((lcW lc tc).trans R))
    (codeVals lc) (codeMachineTime lc s (evalnArithmeticCost B)) w₀ hpark V4
    (fun Wb hWb => compiledTM_hoareTime lc ((lcW lc tc).trans R)
      (fun j => V4 (lcW lc tc j)) s B inp₀ Wb [] hinp₀ hWb hBlc (fun k => hv4 _)
      e4in e4fuel)
  set V5 := writeWindow (lcW lc tc) V4 (codeVals lc (fun j => V4 (lcW lc tc j)))
    with hV5
  have hv5 : ∀ k, V5 k < B := by
    intro k
    rw [hV5]
    exact writeWindow_bounded _ _ _ B hv4
      (fun j => codeVals_lt lc s B _ hBlc (fun i => hv4 _) e4in e4fuel j) k
  have e5tag : V5 (lcW lc tc (codeLocal lc 2)) ≤ 1 := by
    rw [hV5, writeWindow_apply]
    exact codeVals_tag_le lc _
  -- stages 6 and 7: the answer out of the block
  have h6 := copyInto_regsWork R V5 B inp₀ w₀ [] (lcW lc tc (codeLocal lc 2))
    (selfW lc tc 2) (lcW_ne_selfW lc tc _ 2) hinp₀ hpark (fun k => (hv5 k).le)
  set V6 := Function.update V5 (selfW lc tc 2) (V5 (lcW lc tc (codeLocal lc 2))) with hV6
  have hv6 : ∀ k, V6 k < B := update_lt V5 B hv5 (hv5 _)
  have h7 := copyInto_regsWork R V6 B inp₀ w₀ [] (lcW lc tc (codeLocal lc 3))
    (selfW lc tc 3) (lcW_ne_selfW lc tc _ 3) hinp₀ hpark (fun k => (hv6 k).le)
  set V7 := Function.update V6 (selfW lc tc 3) (V6 (lcW lc tc (codeLocal lc 3))) with hV7
  have hv7 : ∀ k, V7 k < B := update_lt V6 B hv6 (hv6 _)
  -- stages 8 to 11: the clamp `min lenVal clock`
  have h8 := copyInto_regsWork R V7 B inp₀ w₀ [] (selfW lc tc 3) (selfW lc tc 6)
    (selfW_ne lc tc 3 6 (by decide)) hinp₀ hpark (fun k => (hv7 k).le)
  set V8 := Function.update V7 (selfW lc tc 6) (V7 (selfW lc tc 3)) with hV8
  have hv8 : ∀ k, V8 k < B := update_lt V7 B hv7 (hv7 _)
  have h9 := subInto_regsWork R V8 B inp₀ w₀ [] (selfW lc tc 1) (selfW lc tc 6)
    (selfW_ne lc tc 1 6 (by decide)) hinp₀ hpark (fun k => (hv8 k).le)
  set V9 := Function.update V8 (selfW lc tc 6) (V8 (selfW lc tc 6) - V8 (selfW lc tc 1))
    with hV9
  have hv9 : ∀ k, V9 k < B := update_lt V8 B hv8 (by have := hv8 (selfW lc tc 6); omega)
  have h10 := copyInto_regsWork R V9 B inp₀ w₀ [] (selfW lc tc 3) (selfW lc tc 7)
    (selfW_ne lc tc 3 7 (by decide)) hinp₀ hpark (fun k => (hv9 k).le)
  set V10 := Function.update V9 (selfW lc tc 7) (V9 (selfW lc tc 3)) with hV10
  have hv10 : ∀ k, V10 k < B := update_lt V9 B hv9 (hv9 _)
  have h11 := subInto_regsWork R V10 B inp₀ w₀ [] (selfW lc tc 6) (selfW lc tc 7)
    (selfW_ne lc tc 6 7 (by decide)) hinp₀ hpark (fun k => (hv10 k).le)
  set V11 := Function.update V10 (selfW lc tc 7)
    (V10 (selfW lc tc 7) - V10 (selfW lc tc 6)) with hV11
  have hv11 : ∀ k, V11 k < B :=
    update_lt V10 B hv10 (by have := hv10 (selfW lc tc 7); omega)
  -- stages 12 and 13: the count
  have h12 := setConst_regsWork R V11 B inp₀ w₀ [] (selfW lc tc 4) 0 hinp₀ hpark
    (fun k => (hv11 k).le) (by omega)
  set V12 := Function.update V11 (selfW lc tc 4) 0 with hV12
  have hv12 : ∀ k, V12 k < B := update_lt V11 B hv11 (by omega)
  have h13 := mulAddInto_regsWork R V12 B inp₀ w₀ [] (selfW lc tc 2) (selfW lc tc 7)
    (selfW lc tc 4) (selfW_ne lc tc 2 7 (by decide)) (selfW_ne lc tc 2 4 (by decide))
    (selfW_ne lc tc 7 4 (by decide)) hinp₀ hpark (fun k => (hv12 k).le)
  set V13 := Function.update V12 (selfW lc tc 4)
    (V12 (selfW lc tc 4) + V12 (selfW lc tc 2) * V12 (selfW lc tc 7)) with hV13
  have htag12 : V12 (selfW lc tc 2) ≤ 1 := by
    rw [hV12, Function.update_of_ne (selfW_ne lc tc 2 4 (by decide)), hV11,
      Function.update_of_ne (selfW_ne lc tc 2 7 (by decide)), hV10,
      Function.update_of_ne (selfW_ne lc tc 2 7 (by decide)), hV9,
      Function.update_of_ne (selfW_ne lc tc 2 6 (by decide)), hV8,
      Function.update_of_ne (selfW_ne lc tc 2 6 (by decide)), hV7,
      Function.update_of_ne (selfW_ne lc tc 2 3 (by decide)), hV6,
      Function.update_self]
    exact e5tag
  have hzero12 : V12 (selfW lc tc 4) = 0 := by rw [hV12, Function.update_self]
  have hv13 : ∀ k, V13 k < B := by
    refine update_lt V12 B hv12 ?_
    have h7B := hv12 (selfW lc tc 7)
    have : V12 (selfW lc tc 2) * V12 (selfW lc tc 7) ≤ V12 (selfW lc tc 7) := by
      calc V12 (selfW lc tc 2) * V12 (selfW lc tc 7)
          ≤ 1 * V12 (selfW lc tc 7) := Nat.mul_le_mul_right _ htag12
        _ = V12 (selfW lc tc 7) := by omega
    omega
  -- stage 14: the loop index
  have h14 := setConst_regsWork R V13 B inp₀ w₀ [] (selfW lc tc 5) 0 hinp₀ hpark
    (fun k => (hv13 k).le) (by omega)
  have hfinal : Function.update V13 (selfW lc tc 5) 0
      = setupVals lc tc a k x.length V := by
    rw [hV13, hV12, hV11, hV10, hV9, hV8, hV7, hV6, hV5, hV4, hV3, hV2, hV1, setupVals]
  rw [hfinal] at h14
  exact (seqEmit hinp₀ (hpv V1) h1 (seqEmit hinp₀ (hpv V2) h2
    (seqEmit hinp₀ (hpv V3) h3 (seqEmit hinp₀ (hpv V4) h4
      (seqEmit hinp₀ (hpv V5) h5 (seqEmit hinp₀ (hpv V6) h6
        (seqEmit hinp₀ (hpv V7) h7 (seqEmit hinp₀ (hpv V8) h8
          (seqEmit hinp₀ (hpv V9) h9 (seqEmit hinp₀ (hpv V10) h10
            (seqEmit hinp₀ (hpv V11) h11 (seqEmit hinp₀ (hpv V12) h12
              (seqEmit hinp₀ (hpv V13) h13 h14))))))))))))).mono_bound (by omega)


set_option maxHeartbeats 2000000 in
/-- The setup keeps every register inside the bound. -/
lemma setupVals_lt (a k N : ℕ) (V : Fin (totalRegs lc tc) → ℕ) (s B : ℕ)
    (hV : ∀ i, V i = 0) (hB5 : 5 ≤ B) (hsB : s < B)
    (hNs : N ≤ s) (hCs : clockOf a k N ≤ s) (hBlc : codeRegBound lc s ≤ B) :
    ∀ j, setupVals lc tc a k N V j < B := by
  have hVlt : ∀ j, V j < B := fun j => by rw [hV j]; omega
  simp only [setupVals]
  set V1 := Function.update V (selfW lc tc 0) N with hV1
  have hv1 : ∀ j, V1 j < B := update_lt V B hVlt (by omega)
  have r1 : V1 (selfW lc tc 0) = N := by rw [hV1, Function.update_self]
  set V2 := Function.update (Function.update V1 (selfW lc tc 6)
    ((clockPoly a k).eval N)) (selfW lc tc 1) ((clockPoly a k).eval N) with hV2
  have hCB : (clockPoly a k).eval N < B := by rw [clockPoly_eval]; omega
  have hv2 : ∀ j, V2 j < B := update_lt _ B (update_lt V1 B hv1 hCB) hCB
  have r2a : V2 (selfW lc tc 0) = N := by
    rw [hV2, Function.update_of_ne (selfW_ne lc tc 0 1 (by decide)),
      Function.update_of_ne (selfW_ne lc tc 0 6 (by decide)), r1]
  have r2b : V2 (selfW lc tc 1) = (clockPoly a k).eval N := by
    rw [hV2, Function.update_self]
  set V3 := Function.update V2 (lcW lc tc (codeLocal lc 0)) (V2 (selfW lc tc 0)) with hV3
  have hv3 : ∀ j, V3 j < B := update_lt V2 B hv2 (hv2 _)
  set V4 := Function.update V3 (lcW lc tc (codeLocal lc 1)) (V3 (selfW lc tc 1)) with hV4
  have hv4 : ∀ j, V4 j < B := update_lt V3 B hv3 (hv3 _)
  have e4in : (fun j => V4 (lcW lc tc j)) (codeLocal lc 0) ≤ s := by
    show V4 (lcW lc tc (codeLocal lc 0)) ≤ s
    rw [hV4, Function.update_of_ne (fun e => (by decide : (0 : Fin 16) ≠ 1)
        ((codeLocal lc).injective ((lcW lc tc).injective e))), hV3,
      Function.update_self, r2a]
    exact hNs
  have e4fuel : (fun j => V4 (lcW lc tc j)) (codeLocal lc 1) ≤ s := by
    show V4 (lcW lc tc (codeLocal lc 1)) ≤ s
    rw [hV4, Function.update_self, hV3,
      Function.update_of_ne (Ne.symm (lcW_ne_selfW lc tc _ 1)), r2b, clockPoly_eval]
    exact hCs
  set V5 := writeWindow (lcW lc tc) V4 (codeVals lc (fun j => V4 (lcW lc tc j))) with hV5
  have hv5 : ∀ j, V5 j < B := by
    intro j
    rw [hV5]
    exact writeWindow_bounded _ _ _ B hv4
      (fun i => codeVals_lt lc s B _ hBlc (fun i => hv4 _) e4in e4fuel i) j
  have e5tag : V5 (lcW lc tc (codeLocal lc 2)) ≤ 1 := by
    rw [hV5, writeWindow_apply]
    exact codeVals_tag_le lc _
  set V6 := Function.update V5 (selfW lc tc 2) (V5 (lcW lc tc (codeLocal lc 2))) with hV6
  have hv6 : ∀ j, V6 j < B := update_lt V5 B hv5 (hv5 _)
  set V7 := Function.update V6 (selfW lc tc 3) (V6 (lcW lc tc (codeLocal lc 3))) with hV7
  have hv7 : ∀ j, V7 j < B := update_lt V6 B hv6 (hv6 _)
  set V8 := Function.update V7 (selfW lc tc 6) (V7 (selfW lc tc 3)) with hV8
  have hv8 : ∀ j, V8 j < B := update_lt V7 B hv7 (hv7 _)
  set V9 := Function.update V8 (selfW lc tc 6) (V8 (selfW lc tc 6) - V8 (selfW lc tc 1))
    with hV9
  have hv9 : ∀ j, V9 j < B := update_lt V8 B hv8 (by have := hv8 (selfW lc tc 6); omega)
  set V10 := Function.update V9 (selfW lc tc 7) (V9 (selfW lc tc 3)) with hV10
  have hv10 : ∀ j, V10 j < B := update_lt V9 B hv9 (hv9 _)
  set V11 := Function.update V10 (selfW lc tc 7)
    (V10 (selfW lc tc 7) - V10 (selfW lc tc 6)) with hV11
  have hv11 : ∀ j, V11 j < B :=
    update_lt V10 B hv10 (by have := hv10 (selfW lc tc 7); omega)
  set V12 := Function.update V11 (selfW lc tc 4) 0 with hV12
  have hv12 : ∀ j, V12 j < B := update_lt V11 B hv11 (by omega)
  have htag12 : V12 (selfW lc tc 2) ≤ 1 := by
    rw [hV12, Function.update_of_ne (selfW_ne lc tc 2 4 (by decide)), hV11,
      Function.update_of_ne (selfW_ne lc tc 2 7 (by decide)), hV10,
      Function.update_of_ne (selfW_ne lc tc 2 7 (by decide)), hV9,
      Function.update_of_ne (selfW_ne lc tc 2 6 (by decide)), hV8,
      Function.update_of_ne (selfW_ne lc tc 2 6 (by decide)), hV7,
      Function.update_of_ne (selfW_ne lc tc 2 3 (by decide)), hV6,
      Function.update_self]
    exact e5tag
  set V13 := Function.update V12 (selfW lc tc 4)
    (V12 (selfW lc tc 4) + V12 (selfW lc tc 2) * V12 (selfW lc tc 7)) with hV13
  have hv13 : ∀ j, V13 j < B := by
    refine update_lt V12 B hv12 ?_
    have h7B := hv12 (selfW lc tc 7)
    have hz : V12 (selfW lc tc 4) = 0 := by rw [hV12, Function.update_self]
    have hprod : V12 (selfW lc tc 2) * V12 (selfW lc tc 7) ≤ V12 (selfW lc tc 7) := by
      calc V12 (selfW lc tc 2) * V12 (selfW lc tc 7)
          ≤ 1 * V12 (selfW lc tc 7) := Nat.mul_le_mul_right _ htag12
        _ = V12 (selfW lc tc 7) := by omega
    omega
  exact update_lt V13 B hv13 (by omega)

end SetupMachine

/-! ## The word the machine emits -/

section Word
variable (lc tc : Nat.Partrec.Code)

lemma resultVal_eq_getD (o : Option ℕ) : resultVal o = o.getD 0 := by
  cases o <;> rfl

lemma ofFn_val_eq_map_range (m : ℕ) (f : ℕ → ℕ) :
    List.ofFn (fun i : Fin m => f i) = (List.range m).map f := by
  refine List.ext_getElem (by simp) (fun i h1 h2 => ?_)
  simp

/-- The digit stream `clockedTokens` produces, as a map over the count the machine
    computes. -/
lemma clockedTokens_eq_map_range (C N : ℕ) :
    clockedTokens lc tc C N
      = (List.range (resultTag (Nat.Partrec.Code.evaln C lc N)
          * min (resultVal (Nat.Partrec.Code.evaln C lc N)) C)).map
        (fun i => resultVal (Nat.Partrec.Code.evaln C tc (Nat.pair N i))) := by
  rw [clockedTokens]
  cases h : Nat.Partrec.Code.evaln C lc N with
  | none => simp [resultTag]
  | some len =>
      simp only [resultTag_some, resultVal_some, one_mul]
      rw [← ofFn_val_eq_map_range]
      congr 1
      funext i
      rw [resultVal_eq_getD]


/-- The output word after `i` iterations, in closed form. -/
lemma tokenLoopYs_eq (V₀ : Fin (totalRegs lc tc) → ℕ) (ys : List Bool) (N C : ℕ)
    (h0 : V₀ (selfW lc tc 0) = N) (h1 : V₀ (selfW lc tc 1) = C)
    (h5 : V₀ (selfW lc tc 5) = 0) :
    ∀ i, tokenLoopYs lc tc V₀ ys i
      = ys ++ digitsToBits ((List.range i).map
          (fun j => min (resultVal (Nat.Partrec.Code.evaln C tc (Nat.pair N j))) 4))
  | 0 => by simp [tokenLoopYs, digitsToBits]
  | i + 1 => by
      have hdig : tokenDigit lc tc (tokenLoopVals lc tc V₀ i)
          = resultVal (Nat.Partrec.Code.evaln C tc (Nat.pair N i)) := by
        rw [tokenDigit, tokenLoopVals_selfW lc tc V₀ 0 (by decide) (by decide),
          tokenLoopVals_selfW lc tc V₀ 1 (by decide) (by decide),
          tokenLoopVals_index, h0, h1, h5]
        norm_num
      rw [tokenLoopYs, tokenLoopYs_eq V₀ ys N C h0 h1 h5 i, hdig, List.range_succ]
      simp [digitsToBits]

/-- The word the machine emits, as a function of its input. -/
noncomputable def traderOutput (a k : ℕ) (x : List Bool) : List Bool :=
  digitsToBits (List.map (fun d => min d 4)
    (clockedTokens lc tc (clockOf a k x.length) x.length))

/-- Reading the emitted word back recovers the clamped digit stream. -/
lemma bitsToDigits_traderOutput (a k : ℕ) (x : List Bool) :
    bitsToDigits (traderOutput lc tc a k x)
      = List.map (fun d => min d 4)
        (clockedTokens lc tc (clockOf a k x.length) x.length) := by
  refine bitsToDigits_digitsToBits _ (fun d hd => ?_)
  obtain ⟨e, -, rfl⟩ := List.mem_map.mp hd
  omega


/-! ## The trader machine -/

section Top
variable {n : ℕ}

lemma regsWork_zero {m : ℕ} (R : Regs m n) :
    regsWork R (fun _ => regTape 0) (fun _ => 0) = fun _ => regTape 0 := by
  funext j
  by_cases h : ∃ q, R q = j
  · obtain ⟨q, rfl⟩ := h
    rw [regsWork_apply]
  · rw [regsWork_of_ne _ _ _ (fun q e => h ⟨q, e⟩)]

/-- **The trader machine.** Measure the day, compute the clock, run the length program,
    then emit one clamped digit per token the token program returns. -/
noncomputable def traderTM (a k : ℕ) (R : Regs (totalRegs lc tc) n) (l : Fin n) : TM n :=
  seqTM bumpTM <|
  seqTM (setupTM lc tc a k R) <|
  seqTM (copyIntoTM (R (selfW lc tc 4)) l) (forRegTM (tokenBodyTM lc tc R) l)

/-- A loose step bound for the trader machine. -/
noncomputable def traderCost (a k N s B count : ℕ) : ℕ :=
  2 * N + opBudget B + ((clockPoly a k).natDegree + 1) * (layerBudget B + 1)
    + 13 * evalnArithmeticCost B + codeMachineTime lc s (evalnArithmeticCost B)
    + count * (25 * evalnArithmeticCost B + codeMachineTime tc s (evalnArithmeticCost B)
      + 70 + 2) + count + 40

set_option maxHeartbeats 8000000 in
lemma traderTM_hoareTime (a k : ℕ) (R : Regs (totalRegs lc tc) n) (l : Fin n)
    (hl : ∀ q, R q ≠ l) (x : List Bool) (s B : ℕ)
    (hB5 : 5 ≤ B) (hsB : s < B)
    (hps : Nat.pair x.length (clockOf a k x.length) ≤ s)
    (hCs : clockOf a k x.length ≤ s)
    (hcap : hornerCap a k x.length ≤ B)
    (hBlc : codeRegBound lc s ≤ B) (hBtc : codeRegBound tc s ≤ B) :
    (traderTM lc tc a k R l).HoareTime
      (fun inp work out => inp = Tape.init (x.map Γ.ofBool) ∧
        (∀ i, work i = Tape.init []) ∧ out = Tape.init [])
      (fun _ _ out => OutAcc (traderOutput lc tc a k x) out)
      (traderCost lc tc a k x.length s B (countOf lc a k x.length)) := by
  set inp₀ : Tape := ⟨1, (Tape.init (x.map Γ.ofBool)).cells⟩ with hinp
  have hinp₀ : Parked inp₀ := parked_init_input x
  set Z : Fin n → Tape := fun _ => regTape 0 with hZdef
  have hparkZ : ∀ i, Parked (Z i) := fun i => parked_regTape 0
  have hNs : x.length ≤ s := le_trans (Nat.left_le_pair _ _) hps
  -- the entry adapter
  have hbump : (bumpTM (n := n)).HoareTime
      (fun inp work out => inp = Tape.init (x.map Γ.ofBool) ∧
        (∀ i, work i = Tape.init []) ∧ out = Tape.init [])
      (EmitPred inp₀ Z []) 1 := by
    refine (bumpTM_hoareTime (n := n) x).consequence (fun _ _ _ h => h)
      (fun inp work out h => ?_) (le_refl 1)
    obtain ⟨hi, hw, ho⟩ := h
    exact ⟨hi, funext (fun i => (hw i).eq_regT), ho⟩
  have hZ : regsWork R Z (fun _ => 0) = Z := regsWork_zero R
  rw [← hZ] at hbump
  -- the setup
  have hsetup := setupTM_hoareTime lc tc a k R x (fun _ => 0) s B Z hparkZ
    (fun _ => rfl) hB5 hsB hNs hCs hcap hBlc
  set V₀ := setupVals lc tc a k x.length (fun _ : Fin (totalRegs lc tc) => 0) with hV₀
  obtain ⟨e0, e1, e4, e5⟩ := setupVals_spec lc tc a k x.length
    (fun _ : Fin (totalRegs lc tc) => 0)
  rw [← hV₀] at e0 e1 e4 e5
  have hV₀lt : ∀ j, V₀ j < B :=
    setupVals_lt lc tc a k x.length _ s B (fun _ => rfl) hB5 hsB hNs hCs hBlc
  have hcountC : countOf lc a k x.length ≤ clockOf a k x.length := by
    rw [countOf]
    rcases Nat.eq_zero_or_pos (resultTag
      (Nat.Partrec.Code.evaln (clockOf a k x.length) lc x.length)) with h | h
    · rw [h]; omega
    · have h1 : resultTag (Nat.Partrec.Code.evaln (clockOf a k x.length) lc x.length) = 1 := by
        have := resultTag_le_one
          (Nat.Partrec.Code.evaln (clockOf a k x.length) lc x.length)
        omega
      rw [h1]
      omega
  -- the loop counter
  have hpZ := parked_regsWork R hparkZ
  have hcopy := copyIntoTM_hoareTime (R (selfW lc tc 4)) l (hl _)
    (V₀ (selfW lc tc 4)) 0 inp₀ (regsWork R Z V₀) [] hinp₀ (fun i _ => hpZ V₀ i)
    (regsWork_apply R Z V₀ _) (by rw [regsWork_of_ne _ _ _ hl])
  rw [e4] at hcopy
  replace hcopy := hcopy.mono_bound
    (copyIntoTime_le_arith (countOf lc a k x.length) 0 B
      (by rw [← e4]; exact (hV₀lt _).le) (by omega))
  set w₁ : Fin n → Tape :=
    Function.update Z l (regTape (countOf lc a k x.length)) with hw₁
  have hpark₁ : ∀ i, Parked (w₁ i) := by
    intro i
    rw [hw₁]
    by_cases hi : i = l
    · subst hi; rw [Function.update_self]; exact parked_regTape _
    · rw [Function.update_of_ne hi]; exact hparkZ i
  have hcopy₁ : (copyIntoTM (R (selfW lc tc 4)) l).HoareTime
      (EmitPred inp₀ (regsWork R Z V₀) [])
      (EmitPred inp₀ (regsWork R w₁ V₀) []) (evalnArithmeticCost B) := by
    rw [hw₁, regsWork_update_of_ne R Z V₀ hl]
    exact hcopy
  -- the loop
  have hloop := tokenLoop_hoareTime lc tc R l hl V₀ s B (countOf lc a k x.length)
    inp₀ w₁ [] hinp₀ hpark₁ (by rw [hw₁, Function.update_self]) hB5 hsB hBtc hV₀lt
    (by rw [e5])
    (by rw [e0]
        exact le_trans (natPair_mono (le_refl _) hcountC) hps)
    (by rw [e1]; exact hCs)
    (by omega)
  -- the emitted word
  have hword : tokenLoopYs lc tc V₀ [] (countOf lc a k x.length)
      = traderOutput lc tc a k x := by
    rw [tokenLoopYs_eq lc tc V₀ [] x.length (clockOf a k x.length) e0 e1 e5,
      traderOutput, clockedTokens_eq_map_range, List.map_map]
    rfl
  rw [hword] at hloop
  have hrest := seqEmitOut hinp₀ (hpZ V₀) hsetup
    (seqEmitOut hinp₀ (parked_regsWork R hpark₁ V₀) hcopy₁ hloop)
  refine ((seqTM_hoareTime bumpTM _ hbump
    (fun _ _ _ h => emitPred_transition hinp₀ (hpZ (fun _ => 0)) [] _ _ _ h)
    hrest).consequence (fun _ _ _ h => h) (fun _ _ out h => h.2.2) ?_)
  rw [traderCost]
  omega

end Top

end Word

/-! ## Polynomiality, and the machine at its own arity -/

lemma IsPolyBounded.monomial (c e : ℕ) : IsPolyBounded (fun x => c * (x + 1) ^ e) :=
  ⟨c, e, fun _ => by simp only []; omega⟩

lemma opBudget_poly : IsPolyBounded opBudget := by
  refine ⟨256, 3, fun x => ?_⟩
  have h : (x + 2) ≤ 2 * (x + 1) := by omega
  have h3 : (x + 2) * (x + 2) * (x + 2) ≤ 8 * ((x + 1) ^ 3) := by
    have : (x + 1) ^ 3 = (x + 1) * (x + 1) * (x + 1) := by ring
    rw [this]
    nlinarith
  rw [opBudget]
  omega

lemma opBudget_mono : Monotone opBudget := by
  intro p q hpq
  simp only [opBudget]
  have : (p + 2) * (p + 2) * (p + 2) ≤ (q + 2) * (q + 2) * (q + 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
  omega

lemma layerBudget_poly : IsPolyBounded layerBudget :=
  ((IsPolyBounded.const_mul opBudget_poly 4).add' (IsPolyBounded.const 3)).of_le
    (fun x => by rw [layerBudget])

section Poly
variable (lc tc : Nat.Partrec.Code) (a k : ℕ)

lemma clockOf_poly : IsPolyBounded (clockOf a k) := ⟨a, k, fun _ => by rw [clockOf]⟩

lemma clockOf_mono : Monotone (clockOf a k) := by
  intro p q hpq
  simp only [clockOf]
  have : (p + 1) ^ k ≤ (q + 1) ^ k := Nat.pow_le_pow_left (by omega) k
  have := Nat.mul_le_mul_left a this
  omega

lemma hornerCap_poly : IsPolyBounded (hornerCap a k) :=
  (IsPolyBounded.monomial ((polyCoeffs (clockPoly a k)).sum + 1)
    (polyCoeffs (clockPoly a k)).length).of_le (fun x => by rw [hornerCap])

lemma hornerCap_mono : Monotone (hornerCap a k) := by
  intro p q hpq
  simp only [hornerCap]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

/-- The size parameter: it dominates the day, the clock, and every paired index the
    machine forms. -/
noncomputable def sizeOf' : ℕ → ℕ := fun N => Nat.pair N (clockOf a k N) + clockOf a k N

/-- The register bound: it dominates every register value the machine holds. -/
noncomputable def boundOf : ℕ → ℕ := fun σ =>
  codeRegBound lc σ + codeRegBound tc σ + σ + hornerCap a k σ + 5

lemma sizeOf'_poly : IsPolyBounded (sizeOf' a k) :=
  ((isPolyBounded_id.pair (clockOf_poly a k)).add' (clockOf_poly a k)).of_le
    (fun x => by rw [sizeOf'])

lemma boundOf_poly : IsPolyBounded (boundOf lc tc a k) :=
  (((((codeRegBound_poly lc).add' (codeRegBound_poly tc)).add' isPolyBounded_id).add'
    (hornerCap_poly a k)).add' (IsPolyBounded.const 5)).of_le (fun x => by rw [boundOf])

lemma boundOf_mono : Monotone (boundOf lc tc a k) := by
  intro p q hpq
  simp only [boundOf]
  have h1 := codeRegBound_mono lc hpq
  have h2 := codeRegBound_mono tc hpq
  have h3 := hornerCap_mono a k hpq
  omega

/-- The arithmetic cost at the register bound, as a function of the size parameter. -/
noncomputable def arithOf : ℕ → ℕ := fun σ => evalnArithmeticCost (boundOf lc tc a k σ)

lemma arithOf_poly : IsPolyBounded (arithOf lc tc a k) :=
  evalnArithmeticCost_poly.comp (boundOf_poly lc tc a k)

lemma arithOf_mono : Monotone (arithOf lc tc a k) :=
  evalnArithmeticCost_mono.comp (boundOf_mono lc tc a k)

end Poly


/-! ## The machine, instantiated -/

section Final
variable (lc tc : Nat.Partrec.Code) (a k : ℕ)

/-- The trader machine's register file, with the loop counter one register beyond it. -/
noncomputable def traderRegs : Regs (totalRegs lc tc) (totalRegs lc tc + 1) :=
  shiftEmb 0 (by omega)

/-- The loop counter, outside the register file the blocks name. -/
def traderLoopIdx : Fin (totalRegs lc tc + 1) := ⟨totalRegs lc tc, by omega⟩

lemma traderRegs_ne (q : Fin (totalRegs lc tc)) :
    traderRegs lc tc q ≠ traderLoopIdx lc tc := by
  intro h
  have hv := congrArg Fin.val h
  simp only [traderRegs, traderLoopIdx, shiftEmb_val] at hv
  have := q.isLt
  omega

/-- **The trader machine at its own arity.** -/
noncomputable def traderMachine : TM (totalRegs lc tc + 1) :=
  traderTM lc tc a k (traderRegs lc tc) (traderLoopIdx lc tc)

/-- The machine's step bound, as a function of the day. -/
noncomputable def traderTime : ℕ → ℕ := fun N =>
  traderCost lc tc a k N (sizeOf' a k N) (boundOf lc tc a k (sizeOf' a k N))
    (countOf lc a k N)

lemma le_sizeOf' (N : ℕ) : N ≤ sizeOf' a k N :=
  le_trans (Nat.left_le_pair _ _) (Nat.le_add_right _ _)

lemma sizeOf'_lt_boundOf (σ : ℕ) : σ < boundOf lc tc a k σ := by
  rw [boundOf]; omega

lemma traderMachine_computesInTime :
    (traderMachine lc tc a k).ComputesInTime (traderOutput lc tc a k)
      (traderTime lc tc a k) := by
  intro x
  obtain ⟨c', t, ht, hreach, hhalt, hout⟩ :=
    traderTM_hoareTime lc tc a k (traderRegs lc tc) (traderLoopIdx lc tc)
      (traderRegs_ne lc tc) x (sizeOf' a k x.length)
      (boundOf lc tc a k (sizeOf' a k x.length))
      (by rw [boundOf]; omega)
      (sizeOf'_lt_boundOf lc tc a k _)
      (by rw [sizeOf']; omega)
      (by rw [sizeOf']; omega)
      (le_trans (hornerCap_mono a k (le_sizeOf' a k x.length)) (by rw [boundOf]; omega))
      (by rw [boundOf]; omega) (by rw [boundOf]; omega)
      (Tape.init (x.map Γ.ofBool)) (fun _ => Tape.init []) (Tape.init [])
      ⟨rfl, fun _ => rfl, rfl⟩
  exact ⟨c', t, ht, hreach, hhalt, hout.hasOutput⟩

lemma countOf_le_clockOf (N : ℕ) : countOf lc a k N ≤ clockOf a k N := by
  rw [countOf]
  have h1 := resultTag_le_one (Nat.Partrec.Code.evaln (clockOf a k N) lc N)
  rcases Nat.eq_zero_or_pos
    (resultTag (Nat.Partrec.Code.evaln (clockOf a k N) lc N)) with h | h
  · rw [h]; omega
  · have h2 : resultTag (Nat.Partrec.Code.evaln (clockOf a k N) lc N) = 1 := by omega
    rw [h2]
    omega

lemma traderTime_poly : IsPolyBounded (traderTime lc tc a k) := by
  have hs := sizeOf'_poly a k
  have hB : IsPolyBounded (fun N => boundOf lc tc a k (sizeOf' a k N)) :=
    (boundOf_poly lc tc a k).comp hs
  have hA : IsPolyBounded (fun N => arithOf lc tc a k (sizeOf' a k N)) :=
    (arithOf_poly lc tc a k).comp hs
  have hop : IsPolyBounded (fun N => opBudget (boundOf lc tc a k (sizeOf' a k N))) :=
    opBudget_poly.comp hB
  have hlayer : IsPolyBounded
      (fun N => ((clockPoly a k).natDegree + 1)
        * (layerBudget (boundOf lc tc a k (sizeOf' a k N)) + 1)) :=
    IsPolyBounded.const_mul ((layerBudget_poly.comp hB).add' (IsPolyBounded.const 1))
      ((clockPoly a k).natDegree + 1)
  have hlc : IsPolyBounded
      (fun N => codeMachineTime lc (sizeOf' a k N)
        (arithOf lc tc a k (sizeOf' a k N))) :=
    (codeMachineTime_poly lc (arithOf lc tc a k) (arithOf_poly lc tc a k)
      (arithOf_mono lc tc a k)).comp hs
  have htc : IsPolyBounded
      (fun N => codeMachineTime tc (sizeOf' a k N)
        (arithOf lc tc a k (sizeOf' a k N))) :=
    (codeMachineTime_poly tc (arithOf lc tc a k) (arithOf_poly lc tc a k)
      (arithOf_mono lc tc a k)).comp hs
  have hcount : IsPolyBounded (countOf lc a k) :=
    (clockOf_poly a k).of_le (countOf_le_clockOf lc a k)
  have hloop : IsPolyBounded (fun N => countOf lc a k N
      * (25 * arithOf lc tc a k (sizeOf' a k N)
        + codeMachineTime tc (sizeOf' a k N) (arithOf lc tc a k (sizeOf' a k N))
        + 70 + 2)) :=
    hcount.mul ((((IsPolyBounded.const_mul hA 25).add' htc).add'
      (IsPolyBounded.const 70)).add' (IsPolyBounded.const 2))
  refine ((((((IsPolyBounded.const_mul isPolyBounded_id 2).add' hop).add' hlayer).add'
    (IsPolyBounded.const_mul hA 13)).add' hlc).add' (hloop.add' (hcount.add'
      (IsPolyBounded.const 40)))).of_le (fun N => ?_)
  rw [traderTime, traderCost, arithOf]
  omega

/-- **The trader machine's output function is polynomial-time.** -/
lemma traderOutput_mem_FP : traderOutput lc tc a k ∈ Complexity.FP := by
  rw [Complexity.mem_FP_iff_computesInTime_polynomial]
  obtain ⟨c, e, hce⟩ := traderTime_poly lc tc a k
  refine ⟨_, traderMachine lc tc a k,
    Polynomial.C c * (Polynomial.X + 1) ^ e + Polynomial.C c, ?_⟩
  refine (traderMachine_computesInTime lc tc a k).mono (fun m => ?_)
  have := hce m
  simpa using this

end Final

end LogicalInduction.TraderMachine
