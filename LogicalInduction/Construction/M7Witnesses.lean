import LogicalInduction.Construction.LIACompiler
import LogicalInduction.Properties

/-!
# Concrete post-M5 representation witnesses

This file hosts the conclusion-free compiler and syntax objects required by the M7
completion contract.  The constructions here contain no market-limit, exploitation, or
logical-inductor conclusions; those remain in the property files that consume the
interfaces.
-/

namespace LogicalInduction

/-! ## Polynomial bounded simulation -/

/-- A code-structural bound on the value returned by one successful `Code.evaln` call.
Recursive `prec`/`rfind'` calls are guarded by the interpreter clock; only the final
fixed-code constructor can enlarge the returned value. -/
def codeEvalBound : Nat.Partrec.Code → ℕ → ℕ
  | .zero, _ => 0
  | .succ, k => k
  | .left, k => k
  | .right, k => k
  | .pair cf cg, k => Nat.pair (codeEvalBound cf k) (codeEvalBound cg k)
  | .comp cf _, k => codeEvalBound cf k
  | .prec cf cg, k => max (codeEvalBound cf k) (codeEvalBound cg k)
  | .rfind' _, k => k

private theorem natPair_mono {a b c d : ℕ} (hab : a ≤ b) (hcd : c ≤ d) :
    Nat.pair a c ≤ Nat.pair b d := by
  calc
    Nat.pair a c ≤ Nat.pair b c := by
      rcases hab.eq_or_lt with h | h
      · rw [h]
      · exact (Nat.pair_lt_pair_left c h).le
    _ ≤ Nat.pair b d := by
      rcases hcd.eq_or_lt with h | h
      · rw [h]
      · exact (Nat.pair_lt_pair_right b h).le

theorem codeEvalBound_mono (code : Nat.Partrec.Code) :
    Monotone (codeEvalBound code) := by
  induction code with
  | zero => exact monotone_const
  | succ => exact monotone_id
  | left => exact monotone_id
  | right => exact monotone_id
  | pair cf cg ihf ihg =>
      intro a b hab
      exact natPair_mono (ihf hab) (ihg hab)
  | comp cf cg ihf _ => exact ihf
  | prec cf cg ihf ihg =>
      intro a b hab
      exact max_le_max (ihf hab) (ihg hab)
  | rfind' cf _ => exact monotone_id

theorem codeEvalBound_poly (code : Nat.Partrec.Code) :
    IsPolyBounded (codeEvalBound code) := by
  induction code with
  | zero =>
      exact (IsPolyBounded.linear 0).of_le fun _ => by simp [codeEvalBound]
  | succ => simpa [codeEvalBound] using IsPolyBounded.linear 0
  | left => simpa [codeEvalBound] using IsPolyBounded.linear 0
  | right => simpa [codeEvalBound] using IsPolyBounded.linear 0
  | pair cf cg ihf ihg =>
      simpa [codeEvalBound] using ihf.pair ihg
  | comp cf cg ihf _ => simpa [codeEvalBound] using ihf
  | prec cf cg ihf ihg =>
      simpa [codeEvalBound] using ihf.max ihg
  | rfind' cf _ => simpa [codeEvalBound] using IsPolyBounded.linear 0

/-- Every successful bounded interpreter result is bounded by a fixed polynomial whose
degree depends only on the simulated program. -/
theorem codeEvaln_result_le (code : Nat.Partrec.Code) :
    ∀ {k n x}, x ∈ Nat.Partrec.Code.evaln k code n →
      x ≤ codeEvalBound code k := by
  intro k n x h
  induction k generalizing code n x with
  | zero => simp [Nat.Partrec.Code.evaln] at h
  | succ k hk =>
      induction code generalizing n x with
      | zero =>
          by_cases hn : n ≤ k
          · simp [Nat.Partrec.Code.evaln, hn] at h
            subst x
            simp [codeEvalBound]
          · simp [Nat.Partrec.Code.evaln, hn] at h
      | succ =>
          by_cases hn : n ≤ k
          · simp [Nat.Partrec.Code.evaln, hn] at h
            subst x
            simp [codeEvalBound]
            omega
          · simp [Nat.Partrec.Code.evaln, hn] at h
      | left =>
          by_cases hn : n ≤ k
          · simp [Nat.Partrec.Code.evaln, hn] at h
            subst x
            simp [codeEvalBound]
            exact (Nat.unpair_left_le n).trans (by omega)
          · simp [Nat.Partrec.Code.evaln, hn] at h
      | right =>
          by_cases hn : n ≤ k
          · simp [Nat.Partrec.Code.evaln, hn] at h
            subst x
            simp [codeEvalBound]
            exact (Nat.unpair_right_le n).trans (by omega)
          · simp [Nat.Partrec.Code.evaln, hn] at h
      | pair cf cg ihf ihg =>
          by_cases hn : n ≤ k
          · cases hf : Nat.Partrec.Code.evaln (k + 1) cf n with
            | none => simp [Nat.Partrec.Code.evaln, hn, hf, Seq.seq] at h
            | some y =>
                cases hg : Nat.Partrec.Code.evaln (k + 1) cg n with
                | none =>
                    simp [Nat.Partrec.Code.evaln, hn, hf, hg, Seq.seq] at h
                | some z =>
                    simp [Nat.Partrec.Code.evaln, hn, hf, hg] at h
                    subst x
                    simp only [codeEvalBound]
                    exact natPair_mono (ihf hf) (ihg hg)
          · simp [Nat.Partrec.Code.evaln, hn] at h
      | comp cf cg ihf ihg =>
          by_cases hn : n ≤ k
          · cases hg : Nat.Partrec.Code.evaln (k + 1) cg n with
            | none => simp [Nat.Partrec.Code.evaln, hn, hg] at h
            | some y =>
                simp [Nat.Partrec.Code.evaln, hn, hg] at h
                simpa [codeEvalBound] using ihf h
          · simp [Nat.Partrec.Code.evaln, hn] at h
      | prec cf cg ihf ihg =>
          by_cases hn : n ≤ k
          · cases hy : n.unpair.2 with
            | zero =>
                simp [Nat.Partrec.Code.evaln, hn, hy] at h
                exact (ihf h).trans (le_max_left _ _)
            | succ y =>
                cases hr : Nat.Partrec.Code.evaln k (.prec cf cg)
                    (Nat.pair n.unpair.1 y) with
                | none =>
                    simp [Nat.Partrec.Code.evaln, hn, hy, hr] at h
                | some prior =>
                    cases hg : Nat.Partrec.Code.evaln (k + 1) cg
                        (Nat.pair n.unpair.1 (Nat.pair y prior)) with
                    | none =>
                        simp [Nat.Partrec.Code.evaln, hn, hy, hr, hg] at h
                    | some out =>
                        simp [Nat.Partrec.Code.evaln, hn, hy, hr, hg] at h
                        subst x
                        exact (ihg hg).trans (le_max_right _ _)
          · simp [Nat.Partrec.Code.evaln, hn] at h
      | rfind' cf ihf =>
          by_cases hn : n ≤ k
          · cases hf : Nat.Partrec.Code.evaln (k + 1) cf n with
            | none => simp [Nat.Partrec.Code.evaln, hn, hf] at h
            | some y =>
                by_cases hy : y = 0
                · simp [Nat.Partrec.Code.evaln, hn, hf, hy] at h
                  subst x
                  simp only [codeEvalBound]
                  exact (Nat.unpair_right_le n).trans (by omega)
                · simp [Nat.Partrec.Code.evaln, hn, hf, hy] at h
                  exact (hk (.rfind' cf) h).trans (by simp [codeEvalBound])
          · simp [Nat.Partrec.Code.evaln, hn] at h

/-- Natural normalization of a bounded interpreter result (`none ↦ 0`, `some x ↦ x+1`). -/
def codeEvalnNat (code : Nat.Partrec.Code) (z : ℕ) : ℕ :=
  match Nat.Partrec.Code.evaln z.unpair.1 code z.unpair.2 with
  | none => 0
  | some out => out + 1

theorem codeEvalnNat_le (code : Nat.Partrec.Code) (z : ℕ) :
    codeEvalnNat code z ≤ codeEvalBound code z.unpair.1 + 1 := by
  unfold codeEvalnNat
  cases h : Nat.Partrec.Code.evaln z.unpair.1 code z.unpair.2 with
  | none => simp
  | some out =>
      simpa using Nat.add_le_add_right (codeEvaln_result_le code h) 1

theorem codeEvalnNat_output_poly (code : Nat.Partrec.Code) :
    IsPolyBounded (codeEvalnNat code) := by
  have hclock : IsPolyBounded fun z => codeEvalBound code z.unpair.1 :=
    (codeEvalBound_poly code).comp isPolyBounded_fst
  exact hclock.add_one.of_le (codeEvalnNat_le code)

/-- Shared M7 compiler hub: a polynomial-clock program for the total bounded interpreter.
It stores only exact finite simulation and complexity data.  The construction of this
object is the common operational core of `M7-HIST-EVALN`, `M7-CE-REPETITION`,
`M7-DUS-APPROX`, and the computation-syntax witnesses. -/
structure BoundedEvalnCompiler (simulated : Nat.Partrec.Code) where
  code : Nat.Partrec.Code
  poly : PolyFueled code (codeEvalnNat simulated)

/-- Direct iterative presentation of the clocked `prec` interpreter clause.  Fixing the
target recursion depth `total`, iteration `j` uses exactly the residual clock
`clock - total + j`; this avoids the exponentially encoded strong-recursion table used by
the generic primitive-recursive proof of `Code.primrec_evaln`. -/
def precEvalState (cf cg : Nat.Partrec.Code) (clock a total : ℕ) :
    ℕ → Option ℕ
  | 0 =>
      let fuel := clock - total
      if Nat.pair a 0 < fuel then Nat.Partrec.Code.evaln fuel cf a else none
  | j + 1 =>
      let fuel := clock - total + j + 1
      if Nat.pair a (j + 1) < fuel then do
        let prior ← precEvalState cf cg clock a total j
        Nat.Partrec.Code.evaln fuel cg (Nat.pair a (Nat.pair j prior))
      else none

theorem precEvalState_eq_evaln (cf cg : Nat.Partrec.Code)
    {clock a total j : ℕ} (htotal : total ≤ clock) (hj : j ≤ total) :
    precEvalState cf cg clock a total j =
      Nat.Partrec.Code.evaln (clock - total + j) (.prec cf cg)
        (Nat.pair a j) := by
  induction j with
  | zero =>
      unfold precEvalState
      set fuel := clock - total
      cases fuel with
      | zero => simp [Nat.Partrec.Code.evaln]
      | succ k =>
          by_cases hguard : Nat.pair a 0 < k + 1
          · have hle : Nat.pair a 0 ≤ k := by omega
            simp [Nat.Partrec.Code.evaln, hguard, hle]
          · have hnle : ¬Nat.pair a 0 ≤ k := by omega
            simp [Nat.Partrec.Code.evaln, hguard, hnle]
  | succ j ih =>
      have hj' : j ≤ total := by omega
      rw [precEvalState]
      rw [ih hj']
      set fuel := clock - total + j + 1
      have hfuel : clock - total + (j + 1) = fuel := by omega
      rw [hfuel]
      by_cases hguard : Nat.pair a (j + 1) < fuel
      · cases hf : fuel with
        | zero => omega
        | succ k =>
            have hle : Nat.pair a (j + 1) ≤ k := by omega
            have hprev : clock - total + j = k := by
              unfold fuel at hf
              omega
            rw [hprev]
            simp [Nat.Partrec.Code.evaln, hle]
      · cases hf : fuel with
        | zero => simp [Nat.Partrec.Code.evaln, hguard, hf]
        | succ k =>
            have hprev : clock - total + j = k := by
              unfold fuel at hf
              omega
            have hnle : ¬Nat.pair a (j + 1) ≤ k := by
              intro hle
              apply hguard
              rw [hf]
              exact Nat.lt_succ_of_le hle
            rw [hprev]
            simp [Nat.Partrec.Code.evaln, hguard, hnle]

theorem precEvalState_final (cf cg : Nat.Partrec.Code)
    {clock a total : ℕ} :
    (if Nat.pair a total < clock then
        precEvalState cf cg clock a total total else none) =
      Nat.Partrec.Code.evaln clock (.prec cf cg) (Nat.pair a total) := by
  by_cases hguard : Nat.pair a total < clock
  · have htotal : total ≤ clock :=
      (Nat.right_le_pair a total).trans hguard.le
    rw [if_pos hguard, precEvalState_eq_evaln cf cg htotal le_rfl]
    congr 2
    omega
  · rw [if_neg hguard]
    cases clock with
    | zero => simp [Nat.Partrec.Code.evaln]
    | succ k =>
        have hnle : ¬Nat.pair a total ≤ k := by omega
        simp [Nat.Partrec.Code.evaln, hnle]

/-! ## Universal bounded simulator — the `M7-HIST-EVALN` linchpin

Target: for every fixed `simulated : Code`, the total normalized bounded interpreter
`codeEvalnNat simulated : ℕ → ℕ` is computable in the project's own polynomial-fuel model
(`PolyFueled`). This is the reusable universal-simulation theorem flagged in the M5 notes
as the piece neither Mathlib (`Code.primrec_evaln` is only primitive recursive, not
poly-fuel) nor this repo previously supplied. The proof is a structural induction on
`simulated`. Every `evaln` clause self-guards its input (`guard (n ≤ k)`), so a failed
guard already forces the sub-code interpreter to `none`; that makes the `pair`/`comp`
cases pure combinations of the sub-code compilers, while only `prec`/`rfind'` require
genuine fuel-decrement iteration. -/

/-- The interpreter returns `none` once the input exceeds the clock. -/
theorem evaln_eq_none_of_gt {k : ℕ} (c : Nat.Partrec.Code) {n : ℕ} (h : k ≤ n) :
    Nat.Partrec.Code.evaln k c n = none := by
  rcases hx : Nat.Partrec.Code.evaln k c n with _ | x
  · rfl
  · exact absurd (Nat.Partrec.Code.evaln_bound hx) (by omega)

open Nat.Partrec.Code in
/-- Base-code interpreters `zero/succ/left/right` share the shape
`if z.1 ≤ z.2 then 0 else rawValue + 1`: the guard fails exactly when `z.1 ≤ z.2`
(`z.2 ≥ fuel`, incl. `fuel = 0`). Compiles via one `ifzSel` over `subc` (`z.1 - z.2`). -/
theorem polyFueled_baseGuard {bv : ℕ → ℕ} {c : Nat.Partrec.Code} (h : PolyFueled c bv) :
    ∃ prog, PolyFueled prog (fun z => if z.unpair.1 ≤ z.unpair.2 then 0 else bv z + 1) := by
  refine ⟨_, (ifzSel_polyFueled.comp
    (((PolyFueled.const 0).pair h.succ_comp).pair subc_polyFueled)).of_eq (fun z => ?_)⟩
  simp only [Nat.unpair_pair, ifzSelFn]
  by_cases hle : z.unpair.1 ≤ z.unpair.2
  · rw [if_pos hle, if_pos (Nat.sub_eq_zero_of_le hle)]
  · rw [if_neg hle, if_neg (by omega : ¬ z.unpair.1 - z.unpair.2 = 0)]

theorem codeEvalnNat_zero_eq (z : ℕ) :
    codeEvalnNat .zero z = if z.unpair.1 ≤ z.unpair.2 then 0 else 0 + 1 := by
  rw [codeEvalnNat]
  cases hk : z.unpair.1 with
  | zero => simp [Nat.Partrec.Code.evaln]
  | succ k =>
    by_cases hle : z.unpair.2 ≤ k
    · simp [Nat.Partrec.Code.evaln, hle, Option.guard, (by omega : ¬ k + 1 ≤ z.unpair.2)]
    · simp [Nat.Partrec.Code.evaln, hle, Option.guard, (by omega : k + 1 ≤ z.unpair.2)]

theorem codeEvalnNat_succ_eq (z : ℕ) :
    codeEvalnNat .succ z = if z.unpair.1 ≤ z.unpair.2 then 0 else z.unpair.2 + 1 + 1 := by
  rw [codeEvalnNat]
  cases hk : z.unpair.1 with
  | zero => simp [Nat.Partrec.Code.evaln]
  | succ k =>
    by_cases hle : z.unpair.2 ≤ k
    · simp [Nat.Partrec.Code.evaln, hle, Option.guard, (by omega : ¬ k + 1 ≤ z.unpair.2)]
    · simp [Nat.Partrec.Code.evaln, hle, Option.guard, (by omega : k + 1 ≤ z.unpair.2)]

theorem codeEvalnNat_left_eq (z : ℕ) :
    codeEvalnNat .left z = if z.unpair.1 ≤ z.unpair.2 then 0 else z.unpair.2.unpair.1 + 1 := by
  rw [codeEvalnNat]
  cases hk : z.unpair.1 with
  | zero => simp [Nat.Partrec.Code.evaln]
  | succ k =>
    by_cases hle : z.unpair.2 ≤ k
    · simp [Nat.Partrec.Code.evaln, hle, Option.guard, (by omega : ¬ k + 1 ≤ z.unpair.2)]
    · simp [Nat.Partrec.Code.evaln, hle, Option.guard, (by omega : k + 1 ≤ z.unpair.2)]

theorem codeEvalnNat_right_eq (z : ℕ) :
    codeEvalnNat .right z = if z.unpair.1 ≤ z.unpair.2 then 0 else z.unpair.2.unpair.2 + 1 := by
  rw [codeEvalnNat]
  cases hk : z.unpair.1 with
  | zero => simp [Nat.Partrec.Code.evaln]
  | succ k =>
    by_cases hle : z.unpair.2 ≤ k
    · simp [Nat.Partrec.Code.evaln, hle, Option.guard, (by omega : ¬ k + 1 ≤ z.unpair.2)]
    · simp [Nat.Partrec.Code.evaln, hle, Option.guard, (by omega : k + 1 ≤ z.unpair.2)]

/-- `pair`: with both sub-code interpreters at the *same* fuel/input `z`, the whole clause is
`none` iff either sub-result is (the guard-fail case is subsumed, since a failed guard sends
each sub-interpreter to `0`). -/
theorem codeEvalnNat_pair_eq (cf cg : Nat.Partrec.Code) (z : ℕ) :
    codeEvalnNat (.pair cf cg) z =
      if codeEvalnNat cf z = 0 ∨ codeEvalnNat cg z = 0 then 0
      else Nat.pair (codeEvalnNat cf z - 1) (codeEvalnNat cg z - 1) + 1 := by
  simp only [codeEvalnNat]
  cases hk : z.unpair.1 with
  | zero => simp [Nat.Partrec.Code.evaln]
  | succ k =>
    by_cases hle : z.unpair.2 ≤ k
    · cases hf : Nat.Partrec.Code.evaln (k + 1) cf z.unpair.2 with
      | none => simp [Nat.Partrec.Code.evaln, hle, Option.guard, hf, Seq.seq]
      | some vf =>
        cases hg : Nat.Partrec.Code.evaln (k + 1) cg z.unpair.2 with
        | none => simp [Nat.Partrec.Code.evaln, hle, Option.guard, hf, hg, Seq.seq]
        | some vg =>
          simp [Nat.Partrec.Code.evaln, hle, Option.guard, hf, hg, Seq.seq]
    · have hf : Nat.Partrec.Code.evaln (k + 1) cf z.unpair.2 = none :=
        evaln_eq_none_of_gt cf (by omega)
      simp [Nat.Partrec.Code.evaln, hle, Option.guard, hf, Seq.seq]

/-- `comp`: the outer interpreter feeds `cf` the *output* of `cg`, at the same fuel `z.1`. -/
theorem codeEvalnNat_comp_eq (cf cg : Nat.Partrec.Code) (z : ℕ) :
    codeEvalnNat (.comp cf cg) z =
      if codeEvalnNat cg z = 0 then 0
      else codeEvalnNat cf (Nat.pair z.unpair.1 (codeEvalnNat cg z - 1)) := by
  simp only [codeEvalnNat, Nat.unpair_pair]
  cases hk : z.unpair.1 with
  | zero => simp [Nat.Partrec.Code.evaln]
  | succ k =>
    by_cases hle : z.unpair.2 ≤ k
    · cases hg : Nat.Partrec.Code.evaln (k + 1) cg z.unpair.2 with
      | none => simp [Nat.Partrec.Code.evaln, hle, Option.guard, hg]
      | some vg =>
        simp [Nat.Partrec.Code.evaln, hle, Option.guard, hg, Nat.add_sub_cancel]
    · have hg : Nat.Partrec.Code.evaln (k + 1) cg z.unpair.2 = none :=
        evaln_eq_none_of_gt cg (by omega)
      simp [Nat.Partrec.Code.evaln, hle, Option.guard, hg]

theorem codeEvalnNat_pair_polyFueled {cf cg : Nat.Partrec.Code}
    (hf : ∃ prog, PolyFueled prog (codeEvalnNat cf))
    (hg : ∃ prog, PolyFueled prog (codeEvalnNat cg)) :
    ∃ prog, PolyFueled prog (codeEvalnNat (.pair cf cg)) := by
  obtain ⟨_, hf⟩ := hf
  obtain ⟨_, hg⟩ := hg
  -- pairVal z = ⟨cf z - 1, cg z - 1⟩ + 1
  have pairVal := ((predc_polyFueled.comp hf).pair (predc_polyFueled.comp hg)).succ_comp
  -- inner z = if cg z = 0 then 0 else pairVal z
  have inner := ifzSel_polyFueled.comp (((PolyFueled.const 0).pair pairVal).pair hg)
  -- outer z = if cf z = 0 then 0 else inner z
  have outer := ifzSel_polyFueled.comp (((PolyFueled.const 0).pair inner).pair hf)
  refine ⟨_, outer.of_eq (fun z => ?_)⟩
  rw [codeEvalnNat_pair_eq]
  simp only [Nat.unpair_pair, ifzSelFn]
  by_cases h0f : codeEvalnNat cf z = 0
  · rw [if_pos h0f, if_pos (Or.inl h0f)]
  · rw [if_neg h0f]
    by_cases h0g : codeEvalnNat cg z = 0
    · rw [if_pos h0g, if_pos (Or.inr h0g)]
    · rw [if_neg h0g, if_neg (by tauto : ¬(codeEvalnNat cf z = 0 ∨ codeEvalnNat cg z = 0))]
      simp only [Nat.pred_eq_sub_one]

theorem codeEvalnNat_comp_polyFueled {cf cg : Nat.Partrec.Code}
    (hf : ∃ prog, PolyFueled prog (codeEvalnNat cf))
    (hg : ∃ prog, PolyFueled prog (codeEvalnNat cg)) :
    ∃ prog, PolyFueled prog (codeEvalnNat (.comp cf cg)) := by
  obtain ⟨_, hf⟩ := hf
  obtain ⟨_, hg⟩ := hg
  -- cfCall z = cf ⟨z.1, cg z - 1⟩
  have cfCall := hf.comp (PolyFueled.left.pair (predc_polyFueled.comp hg))
  have outer := ifzSel_polyFueled.comp (((PolyFueled.const 0).pair cfCall).pair hg)
  refine ⟨_, outer.of_eq (fun z => ?_)⟩
  rw [codeEvalnNat_comp_eq]
  simp only [Nat.unpair_pair, ifzSelFn]
  by_cases h0g : codeEvalnNat cg z = 0
  · rw [if_pos h0g, if_pos h0g]
  · rw [if_neg h0g, if_neg h0g]
    simp only [Nat.pred_eq_sub_one]

/-- **Universal bounded simulator (`M7-HIST-EVALN`).** For every fixed `simulated`, the total
normalized bounded interpreter is computable in the project polynomial-fuel model. -/
theorem codeEvalnNat_polyFueled :
    ∀ c : Nat.Partrec.Code, ∃ prog, PolyFueled prog (codeEvalnNat c)
  | .zero =>
    (polyFueled_baseGuard (PolyFueled.const 0)).imp fun _ h =>
      h.of_eq fun z => (codeEvalnNat_zero_eq z).symm
  | .succ =>
    (polyFueled_baseGuard PolyFueled.right.succ_comp).imp fun _ h =>
      h.of_eq fun z => (codeEvalnNat_succ_eq z).symm
  | .left =>
    (polyFueled_baseGuard (PolyFueled.left.comp PolyFueled.right)).imp fun _ h =>
      h.of_eq fun z => (codeEvalnNat_left_eq z).symm
  | .right =>
    (polyFueled_baseGuard (PolyFueled.right.comp PolyFueled.right)).imp fun _ h =>
      h.of_eq fun z => (codeEvalnNat_right_eq z).symm
  | .pair cf cg =>
    codeEvalnNat_pair_polyFueled (codeEvalnNat_polyFueled cf) (codeEvalnNat_polyFueled cg)
  | .comp cf cg =>
    codeEvalnNat_comp_polyFueled (codeEvalnNat_polyFueled cf) (codeEvalnNat_polyFueled cg)
  | .prec cf cg =>
    -- TODO(blueprint:M7-HIST-EVALN): the fuel-decrement recursion. `evaln (k+1) (prec cf cg)`
    -- recurses on the depth `i = z.2.2` at fuel `k`, so this is a `PolyFueled.prec` iteration
    -- over `i` whose step calls the `cg` compiler at the residual fuel `(k+1) - i + j`
    -- (the `precEvalState` bookkeeping above), with state bounded by `codeEvalBound`.
    sorry
  | .rfind' cf =>
    -- TODO(blueprint:M7-HIST-EVALN): bounded minimization. `evaln (k+1) (rfind' cf)` searches
    -- `m, m+1, …` at decreasing fuel until `cf` returns 0 or fuel is exhausted — a
    -- `PolyFueled.prec` bounded search of length ≤ fuel calling the `cf` compiler per step.
    sorry

/-- The `M7-HIST-EVALN` hub is inhabited for every simulated code (modulo the two
`prec`/`rfind'` iteration cases marked above). -/
noncomputable def boundedEvalnCompiler (simulated : Nat.Partrec.Code) :
    BoundedEvalnCompiler simulated :=
  ⟨_, (codeEvalnNat_polyFueled simulated).choose_spec⟩

/-! ## Efficient repeated enumeration -/

/-- Triangular repetition of an already polynomial sentence stream.  The second pairing
coordinate is pure padding, so every source index occurs arbitrarily late. -/
def triangularRepeat (source : ℕ → Sentence) (n : ℕ) : Sentence :=
  source n.unpair.1

theorem triangularRepeat_codes (source : ℕ → Sentence)
    (hsource : PolySentenceCodes source) :
    PolySentenceCodes (triangularRepeat source) := by
  obtain ⟨code, hcode⟩ := hsource
  exact ⟨code.comp Nat.Partrec.Code.left,
    hcode.comp PolyFueled.left⟩

theorem triangularRepeat_repeats (source : ℕ → Sentence) :
    RepeatsEveryMember (triangularRepeat source) := by
  intro i N
  refine ⟨Nat.pair i.unpair.1 N, Nat.right_le_pair _ _, ?_⟩
  simp [triangularRepeat]

/-- The exact efficient-repetition witness when the supplied enumeration is already a
polynomial stream.  The bounded universal-emulator extension below removes this stronger
clock assumption for arbitrary computable/c.e. source programs. -/
def EfficientRepeatedEnumeration.ofPoly (source : ℕ → Sentence)
    (hsource : PolySentenceCodes source) :
    EfficientRepeatedEnumeration source where
  sequence := triangularRepeat source
  sequence_poly := triangularRepeat_codes source hsource
  repeats := triangularRepeat_repeats source
  sound j := ⟨j.unpair.1, rfl⟩
  covers i := ⟨Nat.pair i 0, by simp [triangularRepeat]⟩

#print axioms triangularRepeat_codes
#print axioms triangularRepeat_repeats
#print axioms EfficientRepeatedEnumeration.ofPoly

end LogicalInduction
