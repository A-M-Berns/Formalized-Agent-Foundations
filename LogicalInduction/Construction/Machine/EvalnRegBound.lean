/-
# A register bound for the compiled `evaln` interpreter

`codeEvalBound` (`Framework/Emission.lean`) bounds the value a *successful* `evaln` call
returns. That is not enough for the compiled machine, whose registers also hold
intermediate values larger than any node's own answer:

* `prec`'s body reconstructs `Nat.pair a (Nat.pair j acc)` before invoking `cg`, while
  `codeEvalBound (prec cf cg) k` is only `max (codeEvalBound cf k) (codeEvalBound cg k)`;
* `rfind'`'s body forms `Nat.pair a m` with `m` advancing one per level, so `m` can reach
  `m₀ + fuel` — past the input.

So the machine needs its own structural bound, and it must carry those pairs explicitly.
`codeRegBound c s` is that bound, with the single parameter `s` standing for a common
bound on the node's input *and* fuel registers. It is monotone in `s` and, for each fixed
code, polynomially bounded — which is what the runtime argument consumes.

Nothing here assumes an arbitrary bound is closed under `Nat.pair`: every pair the machine
forms appears in the definition.
-/
import LogicalInduction.Framework.Emission

namespace LogicalInduction.EvalnCompiler

open Nat.Partrec (Code)

/-- The value `prec`'s body pairs up before invoking `cg`: `Nat.pair a (Nat.pair j acc)`,
    with `a`, `j` bounded by the node's input and `acc` by either child's answer. -/
def precWindowBound (cf cg : Nat.Partrec.Code) (s : ℕ) : ℕ :=
  Nat.pair s (Nat.pair s (max (codeEvalBound cf s) (codeEvalBound cg s)))

/-- The value `rfind'`'s body pairs up: `Nat.pair a m`, with `m` advancing one level per
    unit of fuel, so bounded by input plus fuel. -/
def rfWindowBound (s : ℕ) : ℕ := Nat.pair s (s + s)

/-- **A bound on every register of a compiled node**, given a common bound `s` on its input
    and fuel registers. -/
def codeRegBound : Nat.Partrec.Code → ℕ → ℕ
  | .zero, s => s + 2
  | .succ, s => s + 2
  | .left, s => s + 2
  | .right, s => s + 2
  | .pair cf cg, s =>
      codeRegBound cf s + codeRegBound cg s
        + Nat.pair (codeEvalBound cf s) (codeEvalBound cg s) + 2
  | .comp cf cg, s =>
      codeRegBound cf (s + codeEvalBound cg s) + codeRegBound cg s + 2
  | .prec cf cg, s =>
      codeRegBound cf s + codeRegBound cg (s + precWindowBound cf cg s)
        + precWindowBound cf cg s + 2
  | .rfind' cf, s =>
      codeRegBound cf (s + rfWindowBound s) + rfWindowBound s + 2

lemma precWindowBound_mono (cf cg : Nat.Partrec.Code) :
    Monotone (precWindowBound cf cg) := by
  intro a b hab
  refine natPair_mono hab (natPair_mono hab ?_)
  exact max_le_max (codeEvalBound_mono cf hab) (codeEvalBound_mono cg hab)

lemma rfWindowBound_mono : Monotone rfWindowBound := by
  intro a b hab
  exact natPair_mono hab (Nat.add_le_add hab hab)

lemma codeRegBound_mono (c : Nat.Partrec.Code) : Monotone (codeRegBound c) := by
  induction c with
  | zero => intro a b hab; simpa [codeRegBound] using hab
  | succ => intro a b hab; simpa [codeRegBound] using hab
  | left => intro a b hab; simpa [codeRegBound] using hab
  | right => intro a b hab; simpa [codeRegBound] using hab
  | pair cf cg ihf ihg =>
      intro a b hab
      simp only [codeRegBound]
      exact Nat.add_le_add_right
        (Nat.add_le_add (Nat.add_le_add (ihf hab) (ihg hab))
          (natPair_mono (codeEvalBound_mono cf hab) (codeEvalBound_mono cg hab))) 2
  | comp cf cg ihf ihg =>
      intro a b hab
      simp only [codeRegBound]
      exact Nat.add_le_add_right
        (Nat.add_le_add (ihf (Nat.add_le_add hab (codeEvalBound_mono cg hab))) (ihg hab)) 2
  | prec cf cg ihf ihg =>
      intro a b hab
      simp only [codeRegBound]
      exact Nat.add_le_add_right
        (Nat.add_le_add
          (Nat.add_le_add (ihf hab)
            (ihg (Nat.add_le_add hab (precWindowBound_mono cf cg hab))))
          (precWindowBound_mono cf cg hab)) 2
  | rfind' cf ihf =>
      intro a b hab
      simp only [codeRegBound]
      exact Nat.add_le_add_right
        (Nat.add_le_add (ihf (Nat.add_le_add hab (rfWindowBound_mono hab)))
          (rfWindowBound_mono hab)) 2

lemma precWindowBound_poly (cf cg : Nat.Partrec.Code) :
    IsPolyBounded (precWindowBound cf cg) :=
  (IsPolyBounded.linear 0).pair
    ((IsPolyBounded.linear 0).pair
      ((codeEvalBound_poly cf).max (codeEvalBound_poly cg)))

lemma rfWindowBound_poly : IsPolyBounded rfWindowBound :=
  (IsPolyBounded.linear 0).pair ((IsPolyBounded.linear 0).add (IsPolyBounded.linear 0))

/-- **The register bound is polynomial for each fixed code.** -/
lemma codeRegBound_poly (c : Nat.Partrec.Code) : IsPolyBounded (codeRegBound c) := by
  induction c with
  | zero => exact (IsPolyBounded.linear 2).of_le (fun _ => by simp [codeRegBound])
  | succ => exact (IsPolyBounded.linear 2).of_le (fun _ => by simp [codeRegBound])
  | left => exact (IsPolyBounded.linear 2).of_le (fun _ => by simp [codeRegBound])
  | right => exact (IsPolyBounded.linear 2).of_le (fun _ => by simp [codeRegBound])
  | pair cf cg ihf ihg =>
      refine ((ihf.add ihg).add
        ((codeEvalBound_poly cf).pair (codeEvalBound_poly cg))).add
        (IsPolyBounded.linear 2) |>.of_le (fun s => ?_)
      simp only [codeRegBound, Nat.add_zero]
      omega
  | comp cf cg ihf ihg =>
      refine ((ihf.comp ((IsPolyBounded.linear 0).add (codeEvalBound_poly cg))).add
        ihg).add (IsPolyBounded.linear 2) |>.of_le (fun s => ?_)
      simp only [codeRegBound, Nat.add_zero]
      omega
  | prec cf cg ihf ihg =>
      refine ((ihf.add
        (ihg.comp ((IsPolyBounded.linear 0).add (precWindowBound_poly cf cg)))).add
        (precWindowBound_poly cf cg)).add (IsPolyBounded.linear 2) |>.of_le (fun s => ?_)
      simp only [codeRegBound, Nat.add_zero]
      omega
  | rfind' cf ihf =>
      refine ((ihf.comp ((IsPolyBounded.linear 0).add rfWindowBound_poly)).add
        rfWindowBound_poly).add (IsPolyBounded.linear 2) |>.of_le (fun s => ?_)
      simp only [codeRegBound, Nat.add_zero]
      omega

/-- The bound is at least two more than the size parameter, so it dominates the node's own
    input and fuel registers and leaves room for a flag. -/
lemma le_codeRegBound (c : Nat.Partrec.Code) (s : ℕ) : s + 2 ≤ codeRegBound c s := by
  induction c with
  | zero => simp [codeRegBound]
  | succ => simp [codeRegBound]
  | left => simp [codeRegBound]
  | right => simp [codeRegBound]
  | pair cf cg ihf ihg => simp only [codeRegBound]; omega
  | comp cf cg ihf ihg =>
      simp only [codeRegBound]
      have := ihg
      omega
  | prec cf cg ihf ihg => simp only [codeRegBound]; omega
  | rfind' cf ihf =>
      simp only [codeRegBound]
      have h : s ≤ s + rfWindowBound s := Nat.le_add_right _ _
      have := codeRegBound_mono cf h
      have := ihf
      omega

end LogicalInduction.EvalnCompiler
