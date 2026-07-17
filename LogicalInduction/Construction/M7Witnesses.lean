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

/-- `none ↦ 0`, `some x ↦ x+1`; the normalization shared by `codeEvalnNat`. -/
def optNat : Option ℕ → ℕ
  | none => 0
  | some x => x + 1

theorem codeEvalnNat_eq_optNat (c : Nat.Partrec.Code) (z : ℕ) :
    codeEvalnNat c z = optNat (Nat.Partrec.Code.evaln z.unpair.1 c z.unpair.2) := rfl

theorem optNat_if {P : Prop} [Decidable P] (o : Option ℕ) :
    optNat (if P then o else none) = if P then optNat o else 0 := by
  by_cases h : P <;> simp [h, optNat]

/-- Normalized version of `precEvalState`, written through the sub-code compilers
`codeEvalnNat cf/cg` (not the raw `evaln`), so it can be handed to `PolyFueled.prec`.
`A` packs the prec input `⟨clock, ⟨a, i⟩⟩ = z`; iteration `j` runs the residual clock
`clock - i + j`. -/
def precNat (cf cg : Nat.Partrec.Code) (A : ℕ) : ℕ → ℕ
  | 0 =>
      if Nat.pair A.unpair.2.unpair.1 0 < A.unpair.1 - A.unpair.2.unpair.2 then
        codeEvalnNat cf (Nat.pair (A.unpair.1 - A.unpair.2.unpair.2) A.unpair.2.unpair.1)
      else 0
  | j + 1 =>
      if Nat.pair A.unpair.2.unpair.1 (j + 1) < A.unpair.1 - A.unpair.2.unpair.2 + j + 1 ∧
          precNat cf cg A j ≠ 0 then
        codeEvalnNat cg (Nat.pair (A.unpair.1 - A.unpair.2.unpair.2 + j + 1)
          (Nat.pair A.unpair.2.unpair.1 (Nat.pair j (precNat cf cg A j - 1))))
      else 0

theorem precNat_eq (cf cg : Nat.Partrec.Code) (A : ℕ) :
    ∀ j, precNat cf cg A j =
      optNat (precEvalState cf cg A.unpair.1 A.unpair.2.unpair.1 A.unpair.2.unpair.2 j) := by
  intro j
  induction j with
  | zero =>
      rw [precNat, precEvalState, optNat_if, codeEvalnNat_eq_optNat, Nat.unpair_pair]
  | succ j ih =>
      rw [precNat, precEvalState]
      rcases hp : precEvalState cf cg A.unpair.1 A.unpair.2.unpair.1 A.unpair.2.unpair.2 j
        with _ | p
      · have hp0 : precNat cf cg A j = 0 := by rw [ih, hp]; rfl
        rw [if_neg (by simp [hp0]), optNat_if]
        simp [hp, optNat]
      · have hp1 : precNat cf cg A j = p + 1 := by rw [ih, hp]; rfl
        by_cases hguard : Nat.pair A.unpair.2.unpair.1 (j + 1) <
            A.unpair.1 - A.unpair.2.unpair.2 + j + 1
        · rw [if_pos ⟨hguard, by simp [hp1]⟩, if_pos hguard, hp1,
            Nat.add_sub_cancel, codeEvalnNat_eq_optNat, Nat.unpair_pair]
          simp [hp]
        · rw [if_neg (by tauto), if_neg hguard]
          simp [optNat]

/-- `prec`: the fuel-decrement recursion, packaged as the guarded final value of `precNat`. -/
theorem codeEvalnNat_prec_eq (cf cg : Nat.Partrec.Code) (z : ℕ) :
    codeEvalnNat (.prec cf cg) z =
      if z.unpair.2 < z.unpair.1 then precNat cf cg z z.unpair.2.unpair.2 else 0 := by
  rw [codeEvalnNat_eq_optNat, precNat_eq]
  have hfin := precEvalState_final cf cg
    (clock := z.unpair.1) (a := z.unpair.2.unpair.1) (total := z.unpair.2.unpair.2)
  simp only [Nat.pair_unpair] at hfin
  rw [← hfin, optNat_if]

/-- Normalized `rfind'` search state.  Iteration `j` mirrors the interpreter at fuel `j`
and search position `m0 + (clock - j)`; the fuel and the search index move together, so the
answer is `rfindNat cf z clock` with no outer guard. -/
def rfindNat (cf : Nat.Partrec.Code) (A : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 =>
      let m := A.unpair.2.unpair.2 + (A.unpair.1 - (j + 1))
      let cfval := codeEvalnNat cf (Nat.pair (j + 1) (Nat.pair A.unpair.2.unpair.1 m))
      if cfval = 0 then 0 else if cfval = 1 then m + 1 else rfindNat cf A j

theorem rfindNat_eq (cf : Nat.Partrec.Code) (A : ℕ) :
    ∀ j, j ≤ A.unpair.1 →
      rfindNat cf A j =
        optNat (Nat.Partrec.Code.evaln j (.rfind' cf)
          (Nat.pair A.unpair.2.unpair.1 (A.unpair.2.unpair.2 + (A.unpair.1 - j)))) := by
  intro j
  induction j with
  | zero => intro _; simp [rfindNat, Nat.Partrec.Code.evaln, optNat]
  | succ j ih =>
      intro hj
      have hIH := ih (by omega)
      have hM1 : A.unpair.2.unpair.2 + (A.unpair.1 - (j + 1)) + 1
          = A.unpair.2.unpair.2 + (A.unpair.1 - j) := by omega
      rw [rfindNat]
      rcases hx : Nat.Partrec.Code.evaln (j + 1) cf
          (Nat.pair A.unpair.2.unpair.1 (A.unpair.2.unpair.2 + (A.unpair.1 - (j + 1))))
          with _ | x
      · have hcf0 : codeEvalnNat cf (Nat.pair (j + 1) (Nat.pair A.unpair.2.unpair.1
            (A.unpair.2.unpair.2 + (A.unpair.1 - (j + 1))))) = 0 := by
          simp only [codeEvalnNat, Nat.unpair_pair, hx]
        rw [hcf0, if_pos rfl, Nat.Partrec.Code.evaln]
        simp [Nat.unpaired, Nat.unpair_pair, hx, optNat, Option.guard]
      · have hguard : Nat.pair A.unpair.2.unpair.1
            (A.unpair.2.unpair.2 + (A.unpair.1 - (j + 1))) ≤ j := by
          have := Nat.Partrec.Code.evaln_bound hx; omega
        have hcfv : codeEvalnNat cf (Nat.pair (j + 1) (Nat.pair A.unpair.2.unpair.1
            (A.unpair.2.unpair.2 + (A.unpair.1 - (j + 1))))) = x + 1 := by
          simp only [codeEvalnNat, Nat.unpair_pair, hx]
        rw [hcfv, Nat.Partrec.Code.evaln]
        rcases x with _ | y
        · simp [Nat.unpaired, Nat.unpair_pair, hx, hguard, optNat, Option.guard]
        · rw [if_neg (by omega : y + 1 + 1 ≠ 0), if_neg (by omega : y + 1 + 1 ≠ 1)]
          simp [Nat.unpaired, Nat.unpair_pair, hx, hguard, optNat, Option.guard,
            Nat.succ_ne_zero, hM1, hIH]

/-- `rfind'`: normalized bounded minimization is the final search state at `j = clock`. -/
theorem codeEvalnNat_rfind_eq (cf : Nat.Partrec.Code) (z : ℕ) :
    codeEvalnNat (.rfind' cf) z = rfindNat cf z z.unpair.1 := by
  rw [rfindNat_eq cf z z.unpair.1 le_rfl, codeEvalnNat_eq_optNat]
  simp only [Nat.sub_self, Nat.add_zero, Nat.pair_unpair]

/-- Every `rfindNat` value is `0` or a returned search position `≤ m0 + clock`. -/
theorem rfindNat_le (cf : Nat.Partrec.Code) (A : ℕ) :
    ∀ j, rfindNat cf A j ≤ A.unpair.2.unpair.2 + A.unpair.1 + 1 := by
  intro j
  induction j with
  | zero => simp [rfindNat]
  | succ j ih =>
      rw [rfindNat]
      split_ifs
      · exact Nat.zero_le _
      · omega
      · exact ih

section PrecCompile
attribute [local irreducible] Nat.sqrt

/-- Compile the `prec` case: `precNat` is a primitive recursion whose base/step call the
sub-code compilers, so `PolyFueled.prec` applies; a poly bound on the state comes from
`codeEvalnNat_le` (each value is `0`, a `cf`-call, or a `cg`-call). -/
theorem codeEvalnNat_prec_polyFueled {cf cg : Nat.Partrec.Code}
    (hf : ∃ prog, PolyFueled prog (codeEvalnNat cf))
    (hg : ∃ prog, PolyFueled prog (codeEvalnNat cg)) :
    ∃ prog, PolyFueled prog (codeEvalnNat (.prec cf cg)) := by
  obtain ⟨_, hf⟩ := hf
  obtain ⟨_, hg⟩ := hg
  obtain ⟨_, hadd⟩ := addc_polyFueled
  -- Base program `f A = precNat cf cg A 0`.
  have LclockP := PolyFueled.left
  have LaP := PolyFueled.left.comp PolyFueled.right
  have LiP := PolyFueled.right.comp PolyFueled.right
  have LcmiP := subc_polyFueled.comp (LclockP.pair LiP)
  have Lpa0P := LaP.pair (PolyFueled.const 0)
  have LtestP := subc_polyFueled.comp (LcmiP.pair Lpa0P)
  have LcfCallP := hf.comp (LcmiP.pair LaP)
  have fPF : PolyFueled _ (fun A => precNat cf cg A 0) :=
    (ifzSel_polyFueled.comp (((PolyFueled.const 0).pair LcfCallP).pair LtestP)).of_eq
      (fun A => by
        simp only [Nat.unpair_pair, ifzSelFn, precNat]
        by_cases h : A.unpair.2.unpair.1.pair 0 < A.unpair.1 - A.unpair.2.unpair.2
        · rw [if_pos h, if_neg (by omega : ¬ A.unpair.1 - A.unpair.2.unpair.2 -
            A.unpair.2.unpair.1.pair 0 = 0)]
        · rw [if_neg h, if_pos (by omega : A.unpair.1 - A.unpair.2.unpair.2 -
            A.unpair.2.unpair.1.pair 0 = 0)])
  -- Step program `g` (spec via projections of `X = ⟨A, ⟨j, prior⟩⟩`).
  have SAP := PolyFueled.left
  have SjP := PolyFueled.left.comp PolyFueled.right
  have SpriorP := PolyFueled.right.comp PolyFueled.right
  have SclockP := PolyFueled.left.comp SAP
  have SaP := (PolyFueled.left.comp PolyFueled.right).comp SAP
  have SiP := (PolyFueled.right.comp PolyFueled.right).comp SAP
  have ScmiP := subc_polyFueled.comp (SclockP.pair SiP)
  have SfuelP := (hadd.comp (ScmiP.pair SjP)).succ_comp
  have Spaj1P := SaP.pair SjP.succ_comp
  have Stest1P := subc_polyFueled.comp (SfuelP.pair Spaj1P)
  have Spm1P := predc_polyFueled.comp SpriorP
  have ScgInP := SfuelP.pair (SaP.pair (SjP.pair Spm1P))
  have ScgCallP := hg.comp ScgInP
  have SinnerP := ifzSel_polyFueled.comp (((PolyFueled.const 0).pair ScgCallP).pair SpriorP)
  set gspec : ℕ → ℕ := fun X =>
    if X.unpair.1.unpair.2.unpair.1.pair (X.unpair.2.unpair.1 + 1) <
        X.unpair.1.unpair.1 - X.unpair.1.unpair.2.unpair.2 + X.unpair.2.unpair.1 + 1 ∧
        X.unpair.2.unpair.2 ≠ 0 then
      codeEvalnNat cg (Nat.pair
        (X.unpair.1.unpair.1 - X.unpair.1.unpair.2.unpair.2 + X.unpair.2.unpair.1 + 1)
        (Nat.pair X.unpair.1.unpair.2.unpair.1
          (Nat.pair X.unpair.2.unpair.1 (X.unpair.2.unpair.2 - 1))))
    else 0 with hgspec
  have gPF : PolyFueled _ gspec :=
    (ifzSel_polyFueled.comp (((PolyFueled.const 0).pair SinnerP).pair Stest1P)).of_eq
      (fun X => by
        simp only [Nat.unpair_pair, ifzSelFn, hgspec, Nat.pred_eq_sub_one]
        by_cases hlt : X.unpair.1.unpair.2.unpair.1.pair (X.unpair.2.unpair.1 + 1) <
            X.unpair.1.unpair.1 - X.unpair.1.unpair.2.unpair.2 + X.unpair.2.unpair.1 + 1
        · rw [if_neg (show X.unpair.1.unpair.1 - X.unpair.1.unpair.2.unpair.2 +
              X.unpair.2.unpair.1 + 1 -
              X.unpair.1.unpair.2.unpair.1.pair (X.unpair.2.unpair.1 + 1) ≠ 0 by omega)]
          by_cases h2 : X.unpair.2.unpair.2 = 0
          · rw [if_pos h2, if_neg (fun h => h.2 h2)]
          · rw [if_neg h2, if_pos ⟨hlt, h2⟩]
        · rw [if_pos (show X.unpair.1.unpair.1 - X.unpair.1.unpair.2.unpair.2 +
              X.unpair.2.unpair.1 + 1 -
              X.unpair.1.unpair.2.unpair.1.pair (X.unpair.2.unpair.1 + 1) = 0 by omega),
            if_neg (fun h => hlt h.1)])
  -- State bound: each `precNat` value is `0`, a `cf`-call, or a `cg`-call.
  have hst : IsPolyBounded (fun m => precNat cf cg m.unpair.1 m.unpair.2) := by
    refine (((codeEvalBound_poly cf).comp isPolyBounded_fst).add
      ((codeEvalBound_poly cg).comp
        ((isPolyBounded_fst.add isPolyBounded_snd).add_one))).add_one.of_le (fun m => ?_)
    show precNat cf cg m.unpair.1 m.unpair.2 ≤
      codeEvalBound cf m.unpair.1 + codeEvalBound cg (m.unpair.1 + m.unpair.2 + 1) + 1
    have hcl : m.unpair.1.unpair.1 ≤ m.unpair.1 := Nat.unpair_left_le _
    cases hj : m.unpair.2 with
    | zero =>
      rw [precNat]
      split_ifs with hc
      · refine le_trans (codeEvalnNat_le cf _) ?_
        simp only [Nat.unpair_pair]
        have := codeEvalBound_mono cf (le_trans (Nat.sub_le m.unpair.1.unpair.1
          m.unpair.1.unpair.2.unpair.2) hcl)
        omega
      · exact Nat.zero_le _
    | succ j =>
      rw [precNat]
      split_ifs with hc
      · refine le_trans (codeEvalnNat_le cg _) ?_
        simp only [Nat.unpair_pair]
        have := codeEvalBound_mono cg (show m.unpair.1.unpair.1 -
          m.unpair.1.unpair.2.unpair.2 + j + 1 ≤ m.unpair.1 + (j + 1) + 1 by omega)
        omega
      · exact Nat.zero_le _
  have hprec := PolyFueled.prec fPF gPF (st := precNat cf cg) (fun _ => rfl)
    (fun A j => by rw [precNat]; simp only [hgspec, Nat.unpair_pair]) hst
  -- Feed `⟨z, z.2.2⟩`, then guard by `z.2 < z.1`.
  have hval := hprec.comp (PolyFueled.id.pair (PolyFueled.right.comp PolyFueled.right))
  refine ⟨_, (ifzSel_polyFueled.comp
    (((PolyFueled.const 0).pair hval).pair subc_polyFueled)).of_eq (fun z => ?_)⟩
  rw [codeEvalnNat_prec_eq]
  simp only [Nat.unpair_pair, ifzSelFn]
  by_cases h : z.unpair.2 < z.unpair.1
  · rw [if_pos h, if_neg (by omega : ¬ z.unpair.1 - z.unpair.2 = 0)]
  · rw [if_neg h, if_pos (by omega : z.unpair.1 - z.unpair.2 = 0)]

end PrecCompile

section RfindCompile
attribute [local irreducible] Nat.sqrt

/-- Compile the `rfind'` case via `PolyFueled.prec` over `rfindNat`. -/
theorem codeEvalnNat_rfind_polyFueled {cf : Nat.Partrec.Code}
    (hf : ∃ prog, PolyFueled prog (codeEvalnNat cf)) :
    ∃ prog, PolyFueled prog (codeEvalnNat (.rfind' cf)) := by
  obtain ⟨_, hf⟩ := hf
  obtain ⟨_, hadd⟩ := addc_polyFueled
  -- Step program `g` (spec via projections of `X = ⟨A, ⟨j, prior⟩⟩`).
  have SAP := PolyFueled.left
  have SjP := PolyFueled.left.comp PolyFueled.right
  have SpriorP := PolyFueled.right.comp PolyFueled.right
  have SclockP := PolyFueled.left.comp SAP
  have SaP := (PolyFueled.left.comp PolyFueled.right).comp SAP
  have Sm0P := (PolyFueled.right.comp PolyFueled.right).comp SAP
  have Sj1P := SjP.succ_comp
  have ScmjP := subc_polyFueled.comp (SclockP.pair Sj1P)
  have SmP := hadd.comp (Sm0P.pair ScmjP)
  have ScfInP := Sj1P.pair (SaP.pair SmP)
  have ScfvalP := hf.comp ScfInP
  have SinnerP := ifzSel_polyFueled.comp
    ((SmP.succ_comp.pair SpriorP).pair (predc_polyFueled.comp ScfvalP))
  set gspec : ℕ → ℕ := fun X =>
    if codeEvalnNat cf (Nat.pair (X.unpair.2.unpair.1 + 1) (Nat.pair X.unpair.1.unpair.2.unpair.1
        (X.unpair.1.unpair.2.unpair.2 + (X.unpair.1.unpair.1 - (X.unpair.2.unpair.1 + 1))))) = 0
    then 0
    else if codeEvalnNat cf (Nat.pair (X.unpair.2.unpair.1 + 1) (Nat.pair
        X.unpair.1.unpair.2.unpair.1 (X.unpair.1.unpair.2.unpair.2 +
        (X.unpair.1.unpair.1 - (X.unpair.2.unpair.1 + 1))))) = 1
    then X.unpair.1.unpair.2.unpair.2 + (X.unpair.1.unpair.1 - (X.unpair.2.unpair.1 + 1)) + 1
    else X.unpair.2.unpair.2 with hgspec
  have gPF : PolyFueled _ gspec :=
    (ifzSel_polyFueled.comp (((PolyFueled.const 0).pair SinnerP).pair ScfvalP)).of_eq
      (fun X => by
        simp only [Nat.unpair_pair, ifzSelFn, hgspec, Nat.pred_eq_sub_one]
        set c := codeEvalnNat cf (Nat.pair (X.unpair.2.unpair.1 + 1) (Nat.pair
          X.unpair.1.unpair.2.unpair.1 (X.unpair.1.unpair.2.unpair.2 +
          (X.unpair.1.unpair.1 - (X.unpair.2.unpair.1 + 1)))))
        by_cases h0 : c = 0
        · simp [h0]
        · rw [if_neg h0, if_neg h0]
          by_cases h1 : c = 1
          · rw [if_pos h1, if_pos (by omega : c - 1 = 0)]
          · rw [if_neg h1, if_neg (by omega : c - 1 ≠ 0)])
  have hst : IsPolyBounded (fun m => rfindNat cf m.unpair.1 m.unpair.2) :=
    ((isPolyBounded_fst.add isPolyBounded_fst).add_one).of_le (fun m => by
      have := rfindNat_le cf m.unpair.1 m.unpair.2
      have h1 : m.unpair.1.unpair.2.unpair.2 ≤ m.unpair.1 :=
        le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _)
      have h2 : m.unpair.1.unpair.1 ≤ m.unpair.1 := Nat.unpair_left_le _
      omega)
  have hprec := PolyFueled.prec (PolyFueled.const 0) gPF (st := rfindNat cf)
    (fun _ => rfl) (fun A j => by rw [rfindNat]; simp only [hgspec, Nat.unpair_pair]) hst
  have hval := hprec.comp (PolyFueled.id.pair PolyFueled.left)
  refine ⟨_, hval.of_eq (fun z => ?_)⟩
  rw [codeEvalnNat_rfind_eq]
  simp only [Nat.unpair_pair]

end RfindCompile

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
    codeEvalnNat_prec_polyFueled (codeEvalnNat_polyFueled cf) (codeEvalnNat_polyFueled cg)
  | .rfind' cf =>
    codeEvalnNat_rfind_polyFueled (codeEvalnNat_polyFueled cf)

/-- The `M7-HIST-EVALN` hub is inhabited for every simulated code. -/
noncomputable def boundedEvalnCompiler (simulated : Nat.Partrec.Code) :
    BoundedEvalnCompiler simulated :=
  ⟨_, (codeEvalnNat_polyFueled simulated).choose_spec⟩

/-! ## The bounded dovetail

The paper's `app:prandaff` clock is built from an *arbitrary-runtime* decider run under a
growing budget:

> `DefinitelySettled(n, m) :↔ ∃ i ≤ m: settled(n, i)` returns true within `m` steps

with the three properties it needs: poly in `m`; `DefinitelySettled → Settled`; and if
`Settled(n,m)` then `DefinitelySettled(n,M)` for some `M ≥ m`.  Nothing here is specific to
settlement — this is the generic move that turns *any* code into a polynomial Boolean table
that is monotone in the budget and eventually fires.  It is what
`PatientSettlementClock.active_codes` and `HistoricalVerifiedMaturitySchedule.check_poly`
both need (`M7-PATIENT-CLOCK`, `M7-FEEDBACK-EMIT`), so it is stated once, generically.

The simulator (`codeEvalnNat_polyFueled`, `M7-HIST-EVALN`) is what makes the budgeted run
polynomial; `polyFueled_boundedAny` supplies the bounded search. -/

/-- `c` returns `1` on input `x` within `fuel` steps of the clocked interpreter.
(`codeEvalnNat` normalizes `none ↦ 0` and `some out ↦ out+1`, so acceptance is `2`.) -/
def acceptsWithin (c : Nat.Partrec.Code) (fuel x : ℕ) : Bool :=
  decide (codeEvalnNat c (Nat.pair fuel x) = 2)

/-- The dovetail's inner predicate, indexed as `⟨⟨i,n⟩, j⟩`. -/
private def dovetailStep (c : Nat.Partrec.Code) (z j : ℕ) : Bool :=
  acceptsWithin c z.unpair.2 (Nat.pair z.unpair.1 j)

/-- `dovetailFound c i n`: some `j ≤ n` is accepted for `i` within budget `n`. -/
def dovetailFound (c : Nat.Partrec.Code) (i n : ℕ) : Bool :=
  boundedAny (dovetailStep c) (Nat.pair i n) n

theorem dovetailFound_eq_true_iff (c : Nat.Partrec.Code) (i n : ℕ) :
    dovetailFound c i n = true ↔ ∃ j ≤ n, acceptsWithin c n (Nat.pair i j) = true := by
  simp [dovetailFound, boundedAny_eq_true_iff, dovetailStep]

section
-- The documented `dd:fuel` gotcha: `whnf` loops on `Nat.sqrt` (reached via `Nat.unpair`'s
-- `Primcodable` instance), not on any domain math.  Scope it irreducible rather than
-- raising heartbeats.
attribute [local irreducible] Nat.sqrt

/-- A test for equality against a fixed constant, as a polynomial Boolean table. -/
private theorem polyFueled_eqConst {cf : Nat.Partrec.Code} {f : ℕ → ℕ}
    (hf : PolyFueled cf f) (K : ℕ) :
    ∃ c, PolyFueled c (fun z => if f z = K then 1 else 0) := by
  obtain ⟨cad, had⟩ := addc_polyFueled
  -- `f z = K` iff truncated `(f z - K) + (K - f z) = 0`.
  obtain ⟨c1, h1⟩ : ∃ c, PolyFueled c (fun z => f z - K) :=
    ⟨_, (subc_polyFueled.comp (hf.pair (PolyFueled.const K))).of_eq (fun z => by simp)⟩
  obtain ⟨c2, h2⟩ : ∃ c, PolyFueled c (fun z => K - f z) :=
    ⟨_, (subc_polyFueled.comp ((PolyFueled.const K).pair hf)).of_eq (fun z => by simp)⟩
  obtain ⟨cgap, hgapc⟩ : ∃ c, PolyFueled c (fun z => (f z - K) + (K - f z)) :=
    ⟨_, (had.comp (h1.pair h2)).of_eq (fun z => by simp)⟩
  refine ⟨_, (ifzSel_polyFueled.comp
    (((PolyFueled.const 1).pair (PolyFueled.const 0)).pair hgapc)).of_eq (fun z => ?_)⟩
  simp only [ifzSelFn, Nat.unpair_pair]
  by_cases h : f z = K
  · have hz : (f z - K) + (K - f z) = 0 := by omega
    rw [if_pos hz, if_pos h]
  · have hne : (f z - K) + (K - f z) ≠ 0 := by omega
    rw [if_neg hne, if_neg h]

/-- **The bounded dovetail is polynomial.**  For *any* code `c` — no runtime assumption —
the predicate "`c` accepts `⟨i,j⟩` within `n` steps, for some `j ≤ n`" has a polynomial
Boolean table in `⟨i,n⟩`.

This is the paper's first bullet ("`DefinitelySettled(n,m)` can be decided in time
polynomial in `m`") discharged. -/
theorem polyFueled_dovetailFound (c : Nat.Partrec.Code) :
    ∃ prog, PolyFueled prog
      (fun z => if dovetailFound c z.unpair.1 z.unpair.2 then 1 else 0) := by
  obtain ⟨sim, hsim⟩ := codeEvalnNat_polyFueled c
  -- The inner step, at input `⟨⟨i,n⟩, j⟩`, simulates `c` on `⟨i,j⟩` with budget `n`.
  have hstep : ∃ p, PolyFueled p
      (fun w => if dovetailStep c w.unpair.1 w.unpair.2 then 1 else 0) := by
    obtain ⟨carg, harg⟩ : ∃ p, PolyFueled p (fun w : ℕ =>
        codeEvalnNat c (Nat.pair w.unpair.1.unpair.2
          (Nat.pair w.unpair.1.unpair.1 w.unpair.2))) :=
      ⟨_, (hsim.comp ((PolyFueled.right.comp PolyFueled.left).pair
        ((PolyFueled.left.comp PolyFueled.left).pair PolyFueled.right))).of_eq
          (fun w => by simp)⟩
    obtain ⟨p, hp⟩ := polyFueled_eqConst harg 2
    exact ⟨p, hp.of_eq (fun w => by simp [dovetailStep, acceptsWithin])⟩
  obtain ⟨ca, ha⟩ := polyFueled_boundedAny (dovetailStep c) hstep
  -- Re-index: the table at `z = ⟨i,n⟩` is the search table at `⟨z, n⟩`.
  refine ⟨_, (ha.comp (PolyFueled.id.pair PolyFueled.right)).of_eq (fun z => ?_)⟩
  simp [dovetailFound, Nat.unpair_pair]

/-- Select between two constants on a zero test. -/
theorem polyFueled_selectConst {cf : Nat.Partrec.Code} {f : ℕ → ℕ}
    (hf : PolyFueled cf f) (A B : ℕ) :
    ∃ c, PolyFueled c (fun z => if f z = 0 then A else B) := by
  refine ⟨_, (ifzSel_polyFueled.comp
    (((PolyFueled.const A).pair (PolyFueled.const B)).pair hf)).of_eq (fun z => ?_)⟩
  simp only [ifzSelFn, Nat.unpair_pair]

/-! ### The deadline under-approximation

`PatientSettlementClock` must keep component `i` active through `deferralEnvelope f i`, and
may only go inactive once that deadline has *provably* passed.  But `DeferralFunction`
guarantees only fuel polynomial in `f n` — **not** in `n` (the paper's "time polynomial in
`f(n)`", deliberately weaker since `f` may grow fast).  So `deferralEnvelope f i` is not
polynomial-time computable and the clock cannot decide the deadline exactly.

It does not need to.  `active_through_envelope` only requires activity to be *true* before
the deadline, so a **sound under-approximation** suffices: run `f`'s code on each `k ≤ i`
with budget `n` and certify only when every one halts with `f k < n`.  That is sound
(a halting run returns the true `f k`), monotone in `n` (`evaln_mono`), and eventually
fires (each `f k`, `k ≤ i`, is a fixed finite number). -/

/-- `f`'s clocked run on `k` with budget `n`, normalized: `0` if it has not halted, else
`f k + 1`. -/
def deadlineRun (f : DeferralFunction) (n k : ℕ) : ℕ :=
  codeEvalnNat f.code (Nat.pair n k)

/-- A halting clocked run of a deferral code returns exactly `f k`. -/
theorem deadlineRun_eq (f : DeferralFunction) {n k : ℕ} (h : 0 < deadlineRun f n k) :
    deadlineRun f n k = f.f k + 1 := by
  obtain ⟨a, kk, hspec⟩ := f.fueled
  cases hev : Nat.Partrec.Code.evaln n f.code k with
  | none => simp [deadlineRun, codeEvalnNat, hev] at h
  | some out =>
      have h1 : out ∈ Nat.Partrec.Code.eval f.code k :=
        Nat.Partrec.Code.evaln_sound hev
      have h2 : f.f k ∈ Nat.Partrec.Code.eval f.code k :=
        Nat.Partrec.Code.evaln_sound (hspec k)
      simp [deadlineRun, codeEvalnNat, hev, Part.mem_unique h1 h2]

/-- A halting clocked run is unchanged by a larger budget. -/
theorem deadlineRun_mono (f : DeferralFunction) {n m k : ℕ} (hm : n ≤ m)
    (h : 0 < deadlineRun f n k) : deadlineRun f m k = deadlineRun f n k := by
  cases hev : Nat.Partrec.Code.evaln n f.code k with
  | none => simp [deadlineRun, codeEvalnNat, hev] at h
  | some out =>
      have hmono : Nat.Partrec.Code.evaln m f.code k = some out :=
        Nat.Partrec.Code.evaln_mono hm hev
      simp [deadlineRun, codeEvalnNat, hev, hmono]

/-- The per-`k` failure test of the deadline check, indexed as `⟨⟨i,n⟩,k⟩`. -/
def deadlineStep (f : DeferralFunction) (z k : ℕ) : Bool :=
  decide ((1 - deadlineRun f z.unpair.2 k)
    + (deadlineRun f z.unpair.2 k - z.unpair.2) ≠ 0)

/-- Every `k ≤ i` has been certified `f k < n` within budget `n`. -/
def deadlinePassed (f : DeferralFunction) (i n : ℕ) : Bool :=
  boundedNone (deadlineStep f) (Nat.pair i n) i

theorem deadlinePassed_eq_true_iff (f : DeferralFunction) (i n : ℕ) :
    deadlinePassed f i n = true ↔
      ∀ k ≤ i, 0 < deadlineRun f n k ∧ deadlineRun f n k ≤ n := by
  rw [deadlinePassed, boundedNone_eq_true_iff]
  simp only [deadlineStep, Nat.unpair_pair, decide_eq_false_iff_not, not_not]
  constructor
  · intro h k hk; have := h k hk; omega
  · intro h k hk; have := h k hk; omega

theorem deferralEnvelope_lt_of_forall (f : DeferralFunction) (i n : ℕ)
    (h : ∀ k ≤ i, f.f k < n) : deferralEnvelope f i < n := by
  induction i with
  | zero => simpa [deferralEnvelope] using h 0 le_rfl
  | succ i ih =>
      simp only [deferralEnvelope, max_lt_iff]
      exact ⟨ih (fun k hk => h k (by omega)), h (i + 1) le_rfl⟩

/-- **Soundness**: certification implies the deadline really has passed. -/
theorem deadlinePassed_sound (f : DeferralFunction) {i n : ℕ}
    (h : deadlinePassed f i n = true) : deferralEnvelope f i < n := by
  refine deferralEnvelope_lt_of_forall f i n (fun k hk => ?_)
  obtain ⟨hpos, hle⟩ := (deadlinePassed_eq_true_iff f i n).1 h k hk
  rw [deadlineRun_eq f hpos] at hle
  omega

/-- **Monotone**: a larger budget preserves certification. -/
theorem deadlinePassed_mono (f : DeferralFunction) {i n : ℕ}
    (h : deadlinePassed f i n = true) : deadlinePassed f i (n + 1) = true := by
  rw [deadlinePassed_eq_true_iff] at h ⊢
  intro k hk
  obtain ⟨hpos, hle⟩ := h k hk
  rw [deadlineRun_mono f (Nat.le_succ n) hpos]
  exact ⟨hpos, by omega⟩

/-- **Eventual completion**: every component's deadline is eventually certified. -/
theorem deadlinePassed_eventually (f : DeferralFunction) (i : ℕ) :
    ∃ N, ∀ n, N ≤ n → deadlinePassed f i n = true := by
  obtain ⟨a, kk, hspec⟩ := f.fueled
  refine ⟨(Finset.range (i + 1)).sup
    (fun k => max (a * (f.f k + 1) ^ kk + a) (f.f k + 1)), fun n hn => ?_⟩
  rw [deadlinePassed_eq_true_iff]
  intro k hk
  have hmem : k ∈ Finset.range (i + 1) := Finset.mem_range.mpr (by omega)
  have hsup := Finset.le_sup (f := fun k => max (a * (f.f k + 1) ^ kk + a) (f.f k + 1)) hmem
  have hmono : Nat.Partrec.Code.evaln n f.code k = some (f.f k) :=
    Nat.Partrec.Code.evaln_mono (le_trans (le_trans (le_max_left _ _) hsup) hn) (hspec k)
  have hrun : deadlineRun f n k = f.f k + 1 := by
    simp [deadlineRun, codeEvalnNat, hmono]
  rw [hrun]
  have : f.f k + 1 ≤ n := le_trans (le_trans (le_max_right _ _) hsup) hn
  omega

/-- The deadline under-approximation is a polynomial Boolean table. -/
theorem polyFueled_deadlinePassed (f : DeferralFunction) :
    ∃ prog, PolyFueled prog
      (fun z => if deadlinePassed f z.unpair.1 z.unpair.2 then 1 else 0) := by
  obtain ⟨sim, hsim⟩ := codeEvalnNat_polyFueled f.code
  obtain ⟨cad, had⟩ := addc_polyFueled
  -- Inner step at `w = ⟨⟨i,n⟩,k⟩`: run `f` on `k` with budget `n`, then test `1 ≤ r ≤ n`.
  have hstep : ∃ p, PolyFueled p (fun w =>
      if deadlineStep f w.unpair.1 w.unpair.2 then 1 else 0) := by
    obtain ⟨cr, hr⟩ : ∃ p, PolyFueled p (fun w =>
        deadlineRun f w.unpair.1.unpair.2 w.unpair.2) :=
      ⟨_, (hsim.comp ((PolyFueled.right.comp PolyFueled.left).pair
        PolyFueled.right)).of_eq (fun w => by simp [deadlineRun])⟩
    obtain ⟨c1, h1⟩ : ∃ p, PolyFueled p (fun w =>
        1 - deadlineRun f w.unpair.1.unpair.2 w.unpair.2) :=
      ⟨_, (subc_polyFueled.comp ((PolyFueled.const 1).pair hr)).of_eq (fun w => by simp)⟩
    obtain ⟨c2, h2⟩ : ∃ p, PolyFueled p (fun w =>
        deadlineRun f w.unpair.1.unpair.2 w.unpair.2 - w.unpair.1.unpair.2) :=
      ⟨_, (subc_polyFueled.comp
        (hr.pair (PolyFueled.right.comp PolyFueled.left))).of_eq (fun w => by simp)⟩
    obtain ⟨cgap, hgap⟩ : ∃ p, PolyFueled p (fun w =>
        (1 - deadlineRun f w.unpair.1.unpair.2 w.unpair.2)
          + (deadlineRun f w.unpair.1.unpair.2 w.unpair.2 - w.unpair.1.unpair.2)) :=
      ⟨_, (had.comp (h1.pair h2)).of_eq (fun w => by simp)⟩
    obtain ⟨p, hp⟩ := polyFueled_selectConst hgap 0 1
    refine ⟨p, hp.of_eq (fun w => ?_)⟩
    by_cases hz : (1 - deadlineRun f w.unpair.1.unpair.2 w.unpair.2)
        + (deadlineRun f w.unpair.1.unpair.2 w.unpair.2 - w.unpair.1.unpair.2) = 0
    · have hf : deadlineStep f w.unpair.1 w.unpair.2 = false :=
        decide_eq_false (not_not_intro hz)
      rw [hf, if_pos hz]
      simp
    · have ht : deadlineStep f w.unpair.1 w.unpair.2 = true := decide_eq_true hz
      rw [ht, if_neg hz]
      simp
  obtain ⟨cn, hn⟩ := polyFueled_boundedNone (deadlineStep f) hstep
  refine ⟨_, (hn.comp (PolyFueled.id.pair PolyFueled.left)).of_eq (fun z => ?_)⟩
  simp [deadlinePassed, Nat.unpair_pair]

/-! ### Assembling the clock

Everything the clock needs is now in hand except one thing: a *code* semi-deciding
settlement.  That is isolated as `SettlementSemiDecider` — a pure computability
obligation with no market, economic or limit content — and the clock is constructed from
it.  The remaining M7 work for `M7-PATIENT-CLOCK` is exactly to inhabit that structure. -/

theorem acceptsWithin_mono (c : Nat.Partrec.Code) {F F' x : ℕ} (h : F ≤ F')
    (ha : acceptsWithin c F x = true) : acceptsWithin c F' x = true := by
  cases hev : Nat.Partrec.Code.evaln F c x with
  | none => simp [acceptsWithin, codeEvalnNat, hev] at ha
  | some out =>
      have hm : Nat.Partrec.Code.evaln F' c x = some out :=
        Nat.Partrec.Code.evaln_mono h hev
      simp only [acceptsWithin, codeEvalnNat, Nat.unpair_pair, hev, decide_eq_true_iff] at ha
      simp [acceptsWithin, codeEvalnNat, hm, ha]

theorem dovetailFound_mono (c : Nat.Partrec.Code) {i n : ℕ}
    (h : dovetailFound c i n = true) : dovetailFound c i (n + 1) = true := by
  rw [dovetailFound_eq_true_iff] at h ⊢
  obtain ⟨j, hj, ha⟩ := h
  exact ⟨j, by omega, acceptsWithin_mono c (Nat.le_succ n) ha⟩

/-- A code semi-deciding settlement, stated **semantically**.

Prefer `SettlementChecker` and `PatientSettlementClock.ofChecker` below.  This structure's
`sound` field *states* settlement, so a clock built from it has its `settled_of_inactive`
transported from an assumption rather than derived — a conclusion-in-hypothesis shape.  It
is kept because it is the honest general interface (any semi-decider will do, however
obtained), and because `ofChecker` factors through it; but the concrete route derives both
fields as theorems.  See `settlementTest_iff_settled`. -/
structure SettlementSemiDecider (As : ℕ → AffineCombination) (P : History)
    (DP : DeductiveProcess) (truth : ℕ → ℝ) where
  code : Nat.Partrec.Code
  sound : ∀ i j F, acceptsWithin code F (Nat.pair i j) = true →
    ∀ v : PCWorld, v.ConsistentWith (DP.D j) → (As i).value P v.payout = truth i
  complete : ∀ i j, (∀ v : PCWorld, v.ConsistentWith (DP.D j) →
      (As i).value P v.payout = truth i) →
    ∃ F, acceptsWithin code F (Nat.pair i j) = true

private theorem orNot_eq_false_iff (a b : Bool) :
    ((!a) || (!b)) = false ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp

/-- **The patient settlement clock, constructed.**  Given a settlement semi-decider and
completed-theory determination, the clock exists: activity is the deadline
under-approximation OR'd with the dovetail's failure to certify settlement. -/
noncomputable def PatientSettlementClock.ofSemiDecider
    {As : ℕ → AffineCombination} {P : History} {DP : DeductiveProcess} {truth : ℕ → ℝ}
    (d : SettlementSemiDecider As P DP truth)
    (hdet : AffineCombination.DeterminedViaTheory As P DP truth)
    (f : DeferralFunction) : PatientSettlementClock As P DP truth f where
  active i n := (!(deadlinePassed f i n)) || (!(dovetailFound d.code i n))
  active_codes := by
    obtain ⟨cdp, hdp⟩ := polyFueled_deadlinePassed f
    obtain ⟨cdf, hdf⟩ := polyFueled_dovetailFound d.code
    obtain ⟨cml, hml⟩ := mul_polyFueled
    obtain ⟨cprod, hprod⟩ : ∃ c, PolyFueled c (fun w =>
        (if deadlinePassed f w.unpair.1 w.unpair.2 then 1 else 0) *
        (if dovetailFound d.code w.unpair.1 w.unpair.2 then 1 else 0)) :=
      ⟨_, (hml.comp (hdp.pair hdf)).of_eq (fun w => by simp)⟩
    obtain ⟨cswap, hswap⟩ : ∃ c, PolyFueled c (fun z =>
        (if deadlinePassed f z.unpair.2 z.unpair.1 then 1 else 0) *
        (if dovetailFound d.code z.unpair.2 z.unpair.1 then 1 else 0)) :=
      ⟨_, (hprod.comp (PolyFueled.right.pair PolyFueled.left)).of_eq (fun z => by simp)⟩
    obtain ⟨c, hc⟩ := polyFueled_selectConst hswap
      (Encodable.encode (1 : ℚ)) (Encodable.encode (0 : ℚ))
    refine ⟨c, hc.of_eq (fun z => ?_)⟩
    by_cases h1 : deadlinePassed f z.unpair.2 z.unpair.1 = true <;>
      by_cases h2 : dovetailFound d.code z.unpair.2 z.unpair.1 = true <;>
      simp [h1, h2]
  antitone := by
    intro i n hactive
    by_contra hcon
    rw [Bool.not_eq_true] at hcon
    obtain ⟨hdp, hdf⟩ := (orNot_eq_false_iff _ _).1 hcon
    rw [(orNot_eq_false_iff _ _).2 ⟨deadlinePassed_mono f hdp,
      dovetailFound_mono d.code hdf⟩] at hactive
    exact Bool.false_ne_true hactive
  active_through_envelope := by
    intro i n hn
    by_contra hcon
    rw [Bool.not_eq_true] at hcon
    obtain ⟨hdp, -⟩ := (orNot_eq_false_iff _ _).1 hcon
    exact absurd hn (not_le.mpr (deadlinePassed_sound f hdp))
  eventually_inactive := by
    intro i
    obtain ⟨N1, hN1⟩ := deadlinePassed_eventually f i
    obtain ⟨m, hm⟩ := hdet.exists_settled_stage i
    obtain ⟨F, hF⟩ := d.complete i m hm
    refine ⟨max N1 (max F m), fun n hn => ?_⟩
    refine (orNot_eq_false_iff _ _).2 ⟨hN1 n (le_trans (le_max_left _ _) hn), ?_⟩
    rw [dovetailFound_eq_true_iff]
    exact ⟨m, le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn,
      acceptsWithin_mono d.code
        (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn) hF⟩
  settled_of_inactive := by
    intro i n hinactive
    obtain ⟨hdp, hdf⟩ := (orNot_eq_false_iff _ _).1 hinactive
    refine ⟨deadlinePassed_sound f hdp, fun v hv => ?_⟩
    obtain ⟨j, hj, ha⟩ := (dovetailFound_eq_true_iff d.code i n).1 hdf
    exact d.sound i j n ha v (fun φ hφ => hv φ (DP.mono_le hj hφ))

/-! ### The purely computational checker

`SettlementSemiDecider` above assumes a *semantic* property of a code.  The honest route
assumes only that a code recognizes a **named decidable function** — `SettlementTest`,
which mentions no market, no `truth`, no worlds beyond the finite enumeration — and then
*derives* soundness and completeness from `settlementTest_iff_settled`.

What is left assumed is then irreducible plumbing: "this program recognizes this decidable
predicate."  It carries no semantics at all. -/

/-- A code recognizing the concrete decidable settlement test.

**Purely computational**: the spec relates a program to a `Bool`-valued function of
`⟨i,j⟩` and nothing else — no history, no `truth`, no market conclusion.
`SettlementTestBool` is exponential (it enumerates every bit list of length `B`), which is
exactly what the dovetail absorbs, so no efficiency is asked of `code`.

The **Bool** presentation is deliberate and load-bearing.  The equivalent `SettlementTest`
quantifies over `FiniteWorld B = Fin B → Bool` with `B` computed from the input — a
dependent family that `Computable` cannot decompose, so no code could be shown to
recognize it in that form.  `SettlementTestBool` ranges over `List Bool`, one
non-dependent `Primcodable` type; `settlementTestBool_iff` bridges them.

Inhabiting this is the sole remaining obligation of `M7-PATIENT-CLOCK`: exhibit a
`Nat.Partrec.Code` for a non-dependent decidable function, i.e. `Computable` plumbing
through `MarketComputation.quoteAtFuel`, `DeductiveProcessComputation.stageAtFuel` and
`PolySequence`. -/
structure SettlementChecker (As : ℕ → AffineCombination) (Q : ℕ → Sentence → ℚ)
    (DP : DeductiveProcess) where
  code : Nat.Partrec.Code
  spec : ∀ i j, (∃ F, acceptsWithin code F (Nat.pair i j) = true) ↔
    (As i).SettlementTestBool Q (DP.D j) = true

/-- A concrete checker yields a semi-decider: soundness and completeness are **derived**
from `settlementTest_iff_settled`, not assumed. -/
def SettlementChecker.toSemiDecider
    {As : ℕ → AffineCombination} {P : History} {DP : DeductiveProcess} {truth : ℕ → ℝ}
    {Q : ℕ → Sentence → ℚ} (chk : SettlementChecker As Q DP)
    (hdet : AffineCombination.DeterminedViaTheory As P DP truth)
    (hQ : ∀ d φ, P d φ = (Q d φ : ℝ))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    SettlementSemiDecider As P DP truth where
  code := chk.code
  sound i j F ha :=
    (hdet.settlementTest_iff_settled Q hQ hworld i j).1
      (((As i).settlementTestBool_iff Q (DP.D j)).1 ((chk.spec i j).1 ⟨F, ha⟩))
  complete i j hsettled :=
    (chk.spec i j).2 (((As i).settlementTestBool_iff Q (DP.D j)).2
      ((hdet.settlementTest_iff_settled Q hQ hworld i j).2 hsettled))

/-- **The patient settlement clock from a concrete checker.**  The only assumption is that
one program recognizes one decidable predicate; every semantic field of the clock —
including `settled_of_inactive` — is proved. -/
noncomputable def PatientSettlementClock.ofChecker
    {As : ℕ → AffineCombination} {P : History} {DP : DeductiveProcess} {truth : ℕ → ℝ}
    {Q : ℕ → Sentence → ℚ} (chk : SettlementChecker As Q DP)
    (hdet : AffineCombination.DeterminedViaTheory As P DP truth)
    (hQ : ∀ d φ, P d φ = (Q d φ : ℝ))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (f : DeferralFunction) : PatientSettlementClock As P DP truth f :=
  PatientSettlementClock.ofSemiDecider (chk.toSemiDecider hdet hQ hworld) hdet f

end

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

/-! ### General (c.e.) efficient repetition via the universal simulator

`ofPoly` requires the source stream to already be polynomially codeable. The paper's Uniform
Non-Dogmatism preprocesses an arbitrary **c.e.** stream, which need not be poly. With the
`M7-HIST-EVALN` simulator this is now inhabitable: a code-enumerable source is dovetailed —
on `⟨i, fuel⟩` we run the enumerator on `i` for `fuel` steps (the bounded interpreter
`codeEvalnNat`, poly by `codeEvalnNat_polyFueled`) and emit the decoded output, padding with
`source 0` before it halts. The emitted stream is poly regardless of how expensive `source`
itself is. -/

/-- The result at fuel `fuel` is stable under larger fuel (bounded interpreter monotonicity). -/
theorem codeEvalnNat_pair_mono {code : Nat.Partrec.Code} {i fuel fuel' v : ℕ}
    (hle : fuel ≤ fuel')
    (hv : codeEvalnNat code (Nat.pair fuel i) = v + 1) :
    codeEvalnNat code (Nat.pair fuel' i) = v + 1 := by
  simp only [codeEvalnNat, Nat.unpair_pair] at hv ⊢
  cases hx : Nat.Partrec.Code.evaln fuel code i with
  | none => rw [hx] at hv; simp at hv
  | some w =>
      rw [hx] at hv
      have h2 : Nat.Partrec.Code.evaln fuel' code i = some w :=
        Nat.Partrec.Code.evaln_mono hle hx
      rw [h2]; omega

/-- A code-enumerable ("c.e.") sentence source: a program that halts on every index `i`
returning `⌜source i⌝`, and whose every output lies in `source`'s range. -/
structure CEEnumeration (source : ℕ → Sentence) where
  code : Nat.Partrec.Code
  halts : ∀ i, ∃ fuel,
    codeEvalnNat code (Nat.pair fuel i) = Encodable.encode (source i) + 1
  outputs_sound : ∀ z, codeEvalnNat code z ≠ 0 →
    ∃ i, codeEvalnNat code z = Encodable.encode (source i) + 1

/-- Dovetailed stream: `n = ⟨i, fuel⟩ ↦` decoded enumerator output, or `source 0` before it
halts. -/
noncomputable def ceRepeatSeq {source : ℕ → Sentence} (h : CEEnumeration source)
    (n : ℕ) : Sentence :=
  let r := codeEvalnNat h.code (Nat.pair n.unpair.2 n.unpair.1)
  if r = 0 then source 0 else (Encodable.decode (r - 1)).getD (source 0)

theorem ceRepeatSeq_eq_source {source : ℕ → Sentence} (h : CEEnumeration source)
    {n i : ℕ} (hr : codeEvalnNat h.code (Nat.pair n.unpair.2 n.unpair.1)
      = Encodable.encode (source i) + 1) :
    ceRepeatSeq h n = source i := by
  simp only [ceRepeatSeq, hr, Nat.add_sub_cancel, Encodable.encodek, Option.getD_some,
    Nat.add_one_ne_zero, if_false]

theorem ceRepeatSeq_encode {source : ℕ → Sentence} (h : CEEnumeration source) (n : ℕ) :
    Encodable.encode (ceRepeatSeq h n) =
      if codeEvalnNat h.code (Nat.pair n.unpair.2 n.unpair.1) = 0 then
        Encodable.encode (source 0)
      else codeEvalnNat h.code (Nat.pair n.unpair.2 n.unpair.1) - 1 := by
  by_cases hz : codeEvalnNat h.code (Nat.pair n.unpair.2 n.unpair.1) = 0
  · simp [ceRepeatSeq, hz]
  · obtain ⟨i, hi⟩ := h.outputs_sound _ hz
    rw [ceRepeatSeq_eq_source h hi, if_neg hz, hi, Nat.add_sub_cancel]

theorem ceRepeatSeq_codes {source : ℕ → Sentence} (h : CEEnumeration source) :
    PolySentenceCodes (ceRepeatSeq h) := by
  obtain ⟨prog, hprog⟩ := codeEvalnNat_polyFueled h.code
  have rP := hprog.comp (PolyFueled.right.pair PolyFueled.left)
  refine ⟨_, (ifzSel_polyFueled.comp
    (((PolyFueled.const (Encodable.encode (source 0))).pair
      (predc_polyFueled.comp rP)).pair rP)).of_eq (fun n => ?_)⟩
  rw [ceRepeatSeq_encode]
  simp only [Nat.unpair_pair, ifzSelFn, Nat.pred_eq_sub_one]

/-- **General efficient repetition (`M7-CE-REPETITION`).** Every code-enumerable source has an
efficient-repetition witness — no polynomial-clock assumption on the source itself. -/
noncomputable def EfficientRepeatedEnumeration.ofCE {source : ℕ → Sentence}
    (h : CEEnumeration source) : EfficientRepeatedEnumeration source where
  sequence := ceRepeatSeq h
  sequence_poly := ceRepeatSeq_codes h
  repeats := by
    intro i N
    -- `ceRepeatSeq h i` is some `source i'`; that member recurs at arbitrarily large fuel.
    have hsi : ∃ i', ceRepeatSeq h i = source i' := by
      by_cases hz : codeEvalnNat h.code (Nat.pair i.unpair.2 i.unpair.1) = 0
      · exact ⟨0, by simp [ceRepeatSeq, hz]⟩
      · obtain ⟨i', hi'⟩ := h.outputs_sound _ hz
        exact ⟨i', ceRepeatSeq_eq_source h hi'⟩
    obtain ⟨i', hi'⟩ := hsi
    obtain ⟨fuel, hfuel⟩ := h.halts i'
    refine ⟨Nat.pair i' (max fuel N), le_trans (le_max_right _ _) (Nat.right_le_pair _ _), ?_⟩
    rw [hi']
    apply ceRepeatSeq_eq_source h
    simp only [Nat.unpair_pair]
    exact codeEvalnNat_pair_mono (le_max_left _ _) hfuel
  sound j := by
    by_cases hz : codeEvalnNat h.code (Nat.pair j.unpair.2 j.unpair.1) = 0
    · exact ⟨0, by simp [ceRepeatSeq, hz]⟩
    · obtain ⟨i, hi⟩ := h.outputs_sound _ hz
      exact ⟨i, ceRepeatSeq_eq_source h hi⟩
  covers i := by
    obtain ⟨fuel, hfuel⟩ := h.halts i
    refine ⟨Nat.pair i fuel, ceRepeatSeq_eq_source h ?_⟩
    simp only [Nat.unpair_pair]
    exact hfuel

/-! ## Compiling the settlement test

`SettlementChecker` needs a code recognizing `SettlementTestBool`.  The leaves below are
the `Primrec` facts about its components.

Recursions over `Sentence` cannot be done directly: `Sentence`'s recursor is not a
`Primrec` combinator.  They go instead by course-of-values recursion on the Gödel code,
via `Primrec.nat_strong_rec`, following the `sentencePrimcodable` template in
`LIACompiler.lean`.  Every such quantity is `Option`-encoded — `0` for "the code does not
decode", `v + 1` for "it decodes with value `v`".  That encoding is load-bearing rather
than cosmetic: for a binary code whose left child decodes and whose right child does not,
the code itself does not decode, so the answer must be `0`, and a plain fold over child
values could not distinguish that from a genuine value of `0`.  (`formulaBinaryNorm` in
`LIACompiler.lean` uses the same `left = 0 ∨ right = 0` guard for the same reason.)

Foundation's tags: `0 = ⊥`, `1 = atom`, `2 = 🡒`, `3 = ⋏`, `4 = ⋎`. -/

section SettlementCompile

open LO.Propositional

/-- `atomBound` on a Gödel code, `Option`-encoded (`0` = does not decode). -/
private def atomBoundNorm (n : ℕ) : ℕ :=
  match (@LO.Propositional.Formula.ofNat ℕ inferInstance n : Option Sentence) with
  | none => 0
  | some φ => BoolPCWorld.atomBound φ + 1

/-- All three binary connectives take the `max` of their children's bounds, so unlike
`formulaBinaryNorm` this needs no tag argument. -/
private def atomBoundBinary (prior : List ℕ) (children : ℕ) : ℕ :=
  let left := prior.getD children.unpair.1 0
  let right := prior.getD children.unpair.2 0
  if left = 0 ∨ right = 0 then 0
  else max (left - 1) (right - 1) + 1

private theorem atomBoundBinary_prim : Primrec₂ atomBoundBinary := by
  let childLeft : List ℕ × ℕ → ℕ := fun p => p.1.getD p.2.unpair.1 0
  let childRight : List ℕ × ℕ → ℕ := fun p => p.1.getD p.2.unpair.2 0
  have hleft : Primrec childLeft :=
    (Primrec.list_getD 0).comp Primrec.fst
      (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))
  have hright : Primrec childRight :=
    (Primrec.list_getD 0).comp Primrec.fst
      (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))
  have hbad : PrimrecPred fun p : List ℕ × ℕ =>
      childLeft p = 0 ∨ childRight p = 0 :=
    (Primrec.eq.comp hleft (Primrec.const 0)).or
      (Primrec.eq.comp hright (Primrec.const 0))
  have hmax : Primrec fun p : List ℕ × ℕ =>
      max (childLeft p - 1) (childRight p - 1) + 1 :=
    Primrec.nat_add.comp
      (Primrec.nat_max.comp
        (Primrec.nat_sub.comp hleft (Primrec.const 1))
        (Primrec.nat_sub.comp hright (Primrec.const 1)))
      (Primrec.const 1)
  exact (Primrec.ite hbad (Primrec.const 0) hmax).to₂.of_eq fun prior children => by
    simp only [atomBoundBinary, childLeft, childRight]

private def atomBoundSucc (prior : List ℕ) (e : ℕ) : ℕ :=
  let tag := e.unpair.1
  let payload := e.unpair.2
  if tag = 0 then 1
  else if tag = 1 then payload + 2
  else if tag = 2 then atomBoundBinary prior payload
  else if tag = 3 then atomBoundBinary prior payload
  else if tag = 4 then atomBoundBinary prior payload
  else 0

private theorem atomBoundSucc_prim : Primrec₂ atomBoundSucc := by
  let tag : List ℕ × ℕ → ℕ := fun p => p.2.unpair.1
  let payload : List ℕ × ℕ → ℕ := fun p => p.2.unpair.2
  have htag : Primrec tag := Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have hpayload : Primrec payload := Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)
  have hatom : Primrec fun p : List ℕ × ℕ => payload p + 2 :=
    Primrec.nat_add.comp hpayload (Primrec.const 2)
  have hbin : Primrec fun p : List ℕ × ℕ => atomBoundBinary p.1 (payload p) :=
    atomBoundBinary_prim.comp Primrec.fst hpayload
  have htagEq (k : ℕ) : PrimrecPred fun p : List ℕ × ℕ => tag p = k :=
    Primrec.eq.comp htag (Primrec.const k)
  have h4 := Primrec.ite (htagEq 4) hbin (Primrec.const 0)
  have h3 := Primrec.ite (htagEq 3) hbin h4
  have h2 := Primrec.ite (htagEq 2) hbin h3
  have h1 := Primrec.ite (htagEq 1) hatom h2
  exact (Primrec.ite (htagEq 0) (Primrec.const 1) h1).to₂.of_eq fun prior e => by
    simp only [atomBoundSucc, tag, payload]

private def atomBoundList (prior : List ℕ) : ℕ :=
  prior.length.casesOn 0 (atomBoundSucc prior)

private theorem atomBoundList_prim : Primrec atomBoundList :=
  (Primrec.nat_casesOn Primrec.list_length (Primrec.const 0)
    atomBoundSucc_prim).of_eq fun prior => by simp only [atomBoundList]

private theorem atomBoundNorm_zero : atomBoundNorm 0 = 0 := by
  simp [atomBoundNorm, LO.Propositional.Formula.ofNat]

private theorem atomBoundHistory_getD {n k : ℕ} (hk : k < n) :
    ((List.range n).map atomBoundNorm).getD k 0 = atomBoundNorm k := by
  rw [← atomBoundNorm_zero, List.getD_map]
  simp [List.getD_eq_getElem, hk]

/-- The binary step reads both children out of the history correctly.  Shared by all three
connectives: `atomBound` maxes its children regardless of which one it is. -/
private theorem atomBoundBinary_history (payload n : ℕ)
    (hleft : payload.unpair.1 < n) (hright : payload.unpair.2 < n) :
    atomBoundBinary ((List.range n).map atomBoundNorm) payload =
      match (@LO.Propositional.Formula.ofNat ℕ inferInstance payload.unpair.1 : Option Sentence),
          (@LO.Propositional.Formula.ofNat ℕ inferInstance payload.unpair.2 : Option Sentence) with
      | some φ, some ψ => max (BoolPCWorld.atomBound φ) (BoolPCWorld.atomBound ψ) + 1
      | _, _ => 0 := by
  unfold atomBoundBinary
  rw [atomBoundHistory_getD hleft, atomBoundHistory_getD hright]
  cases hL : (@LO.Propositional.Formula.ofNat ℕ inferInstance
      payload.unpair.1 : Option Sentence) <;>
    cases hR : (@LO.Propositional.Formula.ofNat ℕ inferInstance
      payload.unpair.2 : Option Sentence) <;>
    simp [atomBoundNorm, hL, hR]

private theorem atomBoundList_history (n : ℕ) :
    atomBoundList ((List.range n).map atomBoundNorm) = atomBoundNorm n := by
  cases n with
  | zero => simp [atomBoundList, atomBoundNorm, LO.Propositional.Formula.ofNat]
  | succ e =>
      have hleft : e.unpair.2.unpair.1 < e + 1 :=
        Nat.lt_succ_iff.mpr <|
          le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _)
      have hright : e.unpair.2.unpair.2 < e + 1 :=
        Nat.lt_succ_iff.mpr <|
          le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _)
      have hbin := atomBoundBinary_history e.unpair.2 (e + 1) hleft hright
      by_cases h0 : e.unpair.1 = 0
      · simp [atomBoundList, atomBoundSucc, atomBoundNorm, BoolPCWorld.atomBound,
          LO.Propositional.Formula.ofNat, h0]
      by_cases h1 : e.unpair.1 = 1
      · simp [atomBoundList, atomBoundSucc, atomBoundNorm, BoolPCWorld.atomBound,
          LO.Propositional.Formula.ofNat, h0, h1]
      -- The three binary tags: identical modulo the constructor `ofNat` rebuilds.
      by_cases h2 : e.unpair.1 = 2
      · simp only [atomBoundList, List.length_map, List.length_range, atomBoundSucc,
          h0, h1, h2, ↓reduceIte]
        rw [hbin]
        simp only [atomBoundNorm, LO.Propositional.Formula.ofNat, h2]
        cases (@LO.Propositional.Formula.ofNat ℕ inferInstance
            e.unpair.2.unpair.1 : Option Sentence) <;>
          cases (@LO.Propositional.Formula.ofNat ℕ inferInstance
            e.unpair.2.unpair.2 : Option Sentence) <;>
          simp [BoolPCWorld.atomBound]
      by_cases h3 : e.unpair.1 = 3
      · simp only [atomBoundList, List.length_map, List.length_range, atomBoundSucc,
          h0, h1, h2, h3, ↓reduceIte]
        rw [hbin]
        simp only [atomBoundNorm, LO.Propositional.Formula.ofNat, h3]
        cases (@LO.Propositional.Formula.ofNat ℕ inferInstance
            e.unpair.2.unpair.1 : Option Sentence) <;>
          cases (@LO.Propositional.Formula.ofNat ℕ inferInstance
            e.unpair.2.unpair.2 : Option Sentence) <;>
          simp [BoolPCWorld.atomBound]
      by_cases h4 : e.unpair.1 = 4
      · simp only [atomBoundList, List.length_map, List.length_range, atomBoundSucc,
          h0, h1, h2, h3, h4, ↓reduceIte]
        rw [hbin]
        simp only [atomBoundNorm, LO.Propositional.Formula.ofNat, h4]
        cases (@LO.Propositional.Formula.ofNat ℕ inferInstance
            e.unpair.2.unpair.1 : Option Sentence) <;>
          cases (@LO.Propositional.Formula.ofNat ℕ inferInstance
            e.unpair.2.unpair.2 : Option Sentence) <;>
          simp [BoolPCWorld.atomBound]
      · have htag : 5 ≤ e.unpair.1 := by omega
        simp [atomBoundList, atomBoundSucc, atomBoundNorm,
          LO.Propositional.Formula.ofNat, h0, h1, h2, h3, h4, htag]

private theorem atomBoundNorm_prim : Primrec atomBoundNorm := by
  have hstep : Primrec₂ (fun (_ : Unit) (prior : List ℕ) =>
      some (atomBoundList prior)) :=
    Primrec₂.option_some_iff.mpr (atomBoundList_prim.comp Primrec₂.right)
  have hrec := Primrec.nat_strong_rec (fun (_ : Unit) n => atomBoundNorm n)
    hstep (fun _ n => by simpa using congrArg some (atomBoundList_history n))
  exact (hrec.comp (Primrec.const ()) Primrec.id).of_eq fun n => rfl

/-- **`atomBound` is primitive recursive.**  The first of the two `Sentence` recursions the
settlement test needs; `evalBits_prim` below is the other. -/
theorem atomBound_prim : Primrec BoolPCWorld.atomBound := by
  have h : Primrec fun φ : Sentence => atomBoundNorm (Encodable.encode φ) - 1 :=
    Primrec.nat_sub.comp (atomBoundNorm_prim.comp Primrec.encode) (Primrec.const 1)
  exact h.of_eq fun φ => by
    simp only [atomBoundNorm, Encodable.encode,
      LO.Propositional.Formula.ofNat_toNat φ, Nat.add_sub_cancel]

/-! ### Evaluation

`eval` is the second `Sentence` recursion, and the one the whole test rests on.  Two things
make it harder than `atomBound`:

* the recursion is **parameterized by the world** (`α := List Bool` in `nat_strong_rec`,
  where `atomBound` used `Unit`), and the atom case is where that parameter is consumed —
  `eval (bitsWorld l) (.atom a) = l.getD a false`, i.e. `Primrec.list_getD` on the
  parameter;
* the three binary tags genuinely differ (`🡒`/`⋏`/`⋎`), where `atomBound` maxed all three
  alike.  The second costs nothing in the end: `Bool` is finite, so `Primrec.dom_bool₂`
  gives *every* `Bool → Bool → Bool` for free, and `evalOp` dispatches on the tag.

The `Option` encoding carries a Boolean, so it is three-valued: `0` = does not decode,
`1` = decodes to `false`, `2` = decodes to `true`. -/

/-- The connective a tag denotes.  `Primrec₂` for free by `Primrec.dom_bool₂`. -/
private def evalOp (tag : ℕ) (a b : Bool) : Bool :=
  if tag = 2 then (!a || b) else if tag = 3 then (a && b) else (a || b)

/-- `eval` on a Gödel code, `Option`-encoded (`0` = does not decode, `1` = false,
`2` = true). -/
private def evalNorm (l : List Bool) (n : ℕ) : ℕ :=
  match (@LO.Propositional.Formula.ofNat ℕ inferInstance n : Option Sentence) with
  | none => 0
  | some φ => if BoolPCWorld.eval (BoolPCWorld.bitsWorld l) φ then 2 else 1

private def evalBinary (tag : ℕ) (prior : List ℕ) (children : ℕ) : ℕ :=
  let left := prior.getD children.unpair.1 0
  let right := prior.getD children.unpair.2 0
  if left = 0 ∨ right = 0 then 0
  else if evalOp tag (decide (left = 2)) (decide (right = 2)) then 2 else 1

private theorem evalBinary_prim (tag : ℕ) : Primrec₂ (evalBinary tag) := by
  let childLeft : List ℕ × ℕ → ℕ := fun p => p.1.getD p.2.unpair.1 0
  let childRight : List ℕ × ℕ → ℕ := fun p => p.1.getD p.2.unpair.2 0
  have hleft : Primrec childLeft :=
    (Primrec.list_getD 0).comp Primrec.fst
      (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))
  have hright : Primrec childRight :=
    (Primrec.list_getD 0).comp Primrec.fst
      (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))
  have hbad : PrimrecPred fun p : List ℕ × ℕ =>
      childLeft p = 0 ∨ childRight p = 0 :=
    (Primrec.eq.comp hleft (Primrec.const 0)).or
      (Primrec.eq.comp hright (Primrec.const 0))
  -- `PrimrecPred p` is `∃ _ : DecidablePred p, Primrec fun a => decide (p a)` — an
  -- existential over the instance, so it never unfolds to `Primrec` on its own.
  -- `PrimrecPred.decide`/`Primrec.primrecPred` are the two directions.
  have ha : Primrec fun p : List ℕ × ℕ => decide (childLeft p = 2) :=
    (Primrec.eq.comp hleft (Primrec.const 2)).decide
  have hb : Primrec fun p : List ℕ × ℕ => decide (childRight p = 2) :=
    (Primrec.eq.comp hright (Primrec.const 2)).decide
  have hop : Primrec fun p : List ℕ × ℕ =>
      evalOp tag (decide (childLeft p = 2)) (decide (childRight p = 2)) :=
    (Primrec.dom_bool₂ (evalOp tag)).comp ha hb
  have hcondp : PrimrecPred fun p : List ℕ × ℕ =>
      evalOp tag (decide (childLeft p = 2)) (decide (childRight p = 2)) = true :=
    Primrec.primrecPred (by simpa using hop)
  have hres := Primrec.ite hcondp (Primrec.const 2) (Primrec.const 1)
  exact (Primrec.ite hbad (Primrec.const 0) hres).to₂.of_eq fun prior children => by
    simp only [evalBinary, childLeft, childRight]

private def evalSucc (l : List Bool) (prior : List ℕ) (e : ℕ) : ℕ :=
  let tag := e.unpair.1
  let payload := e.unpair.2
  if tag = 0 then 1
  else if tag = 1 then (if l.getD payload false then 2 else 1)
  else if tag = 2 then evalBinary 2 prior payload
  else if tag = 3 then evalBinary 3 prior payload
  else if tag = 4 then evalBinary 4 prior payload
  else 0

private theorem evalSucc_prim :
    Primrec fun p : List Bool × List ℕ × ℕ => evalSucc p.1 p.2.1 p.2.2 := by
  let tag : List Bool × List ℕ × ℕ → ℕ := fun p => p.2.2.unpair.1
  let payload : List Bool × List ℕ × ℕ → ℕ := fun p => p.2.2.unpair.2
  have htag : Primrec tag :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.snd))
  have hpayload : Primrec payload :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.snd))
  -- The atom case: this is where the world parameter is consumed, by `list_getD` on the
  -- parameter rather than on the recursion history.  It is the one move `atomBound` (whose
  -- `nat_strong_rec` parameter was `Unit`) did not need.
  have hatom : Primrec fun p : List Bool × List ℕ × ℕ =>
      cond (p.1.getD (payload p) false) 2 1 :=
    Primrec.cond ((Primrec.list_getD false).comp Primrec.fst hpayload)
      (Primrec.const 2) (Primrec.const 1)
  have hbin (k : ℕ) : Primrec fun p : List Bool × List ℕ × ℕ =>
      evalBinary k p.2.1 (payload p) :=
    (evalBinary_prim k).comp (Primrec.fst.comp Primrec.snd) hpayload
  have htagEq (k : ℕ) : PrimrecPred fun p : List Bool × List ℕ × ℕ => tag p = k :=
    Primrec.eq.comp htag (Primrec.const k)
  have h4 := Primrec.ite (htagEq 4) (hbin 4) (Primrec.const 0)
  have h3 := Primrec.ite (htagEq 3) (hbin 3) h4
  have h2 := Primrec.ite (htagEq 2) (hbin 2) h3
  have h1 := Primrec.ite (htagEq 1) hatom h2
  exact (Primrec.ite (htagEq 0) (Primrec.const 1) h1).of_eq fun p => by
    simp only [evalSucc, tag, payload]
    by_cases hc0 : p.2.2.unpair.1 = 0
    · simp [hc0]
    by_cases hc1 : p.2.2.unpair.1 = 1
    · simp only [hc1, if_true]
      cases p.1.getD p.2.2.unpair.2 false <;> simp
    · simp [hc0, hc1]

private def evalList (l : List Bool) (prior : List ℕ) : ℕ :=
  prior.length.casesOn 0 (evalSucc l prior)

private theorem evalList_prim :
    Primrec fun p : List Bool × List ℕ => evalList p.1 p.2 := by
  have h := Primrec.nat_casesOn (Primrec.list_length.comp Primrec.snd)
    (Primrec.const 0)
    (evalSucc_prim.comp
      ((Primrec.fst.comp Primrec.fst).pair
        ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))).to₂
  exact h.of_eq fun p => by simp only [evalList]

private theorem evalNorm_zero (l : List Bool) : evalNorm l 0 = 0 := by
  simp [evalNorm, LO.Propositional.Formula.ofNat]

private theorem evalHistory_getD (l : List Bool) {n k : ℕ} (hk : k < n) :
    ((List.range n).map (evalNorm l)).getD k 0 = evalNorm l k := by
  rw [← evalNorm_zero l, List.getD_map]
  simp [List.getD_eq_getElem, hk]

private theorem evalBinary_history (tag : ℕ) (l : List Bool) (payload n : ℕ)
    (hleft : payload.unpair.1 < n) (hright : payload.unpair.2 < n) :
    evalBinary tag ((List.range n).map (evalNorm l)) payload =
      match (@LO.Propositional.Formula.ofNat ℕ inferInstance payload.unpair.1 : Option Sentence),
          (@LO.Propositional.Formula.ofNat ℕ inferInstance payload.unpair.2 : Option Sentence) with
      | some φ, some ψ =>
          if evalOp tag (BoolPCWorld.eval (BoolPCWorld.bitsWorld l) φ)
            (BoolPCWorld.eval (BoolPCWorld.bitsWorld l) ψ) then 2 else 1
      | _, _ => 0 := by
  unfold evalBinary
  rw [evalHistory_getD l hleft, evalHistory_getD l hright]
  cases hL : (@LO.Propositional.Formula.ofNat ℕ inferInstance
      payload.unpair.1 : Option Sentence) <;>
    cases hR : (@LO.Propositional.Formula.ofNat ℕ inferInstance
      payload.unpair.2 : Option Sentence) <;>
    simp only [evalNorm, hL, hR] <;>
    [skip; skip; skip;
      (cases BoolPCWorld.eval (BoolPCWorld.bitsWorld l) _ <;>
        cases BoolPCWorld.eval (BoolPCWorld.bitsWorld l) _ <;> simp)] <;>
    simp

private theorem evalList_history (l : List Bool) (n : ℕ) :
    evalList l ((List.range n).map (evalNorm l)) = evalNorm l n := by
  cases n with
  | zero => simp [evalList, evalNorm, LO.Propositional.Formula.ofNat]
  | succ e =>
      have hleft : e.unpair.2.unpair.1 < e + 1 :=
        Nat.lt_succ_iff.mpr <| le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _)
      have hright : e.unpair.2.unpair.2 < e + 1 :=
        Nat.lt_succ_iff.mpr <| le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _)
      by_cases h0 : e.unpair.1 = 0
      · simp [evalList, evalSucc, evalNorm, BoolPCWorld.eval,
          LO.Propositional.Formula.ofNat, h0]
      by_cases h1 : e.unpair.1 = 1
      · simp [evalList, evalSucc, evalNorm, BoolPCWorld.eval, BoolPCWorld.bitsWorld,
          LO.Propositional.Formula.ofNat, h0, h1]
      by_cases h2 : e.unpair.1 = 2
      · simp only [evalList, List.length_map, List.length_range, evalSucc,
          h0, h1, h2, ↓reduceIte]
        rw [evalBinary_history 2 l e.unpair.2 (e + 1) hleft hright]
        simp only [evalNorm, LO.Propositional.Formula.ofNat, h2]
        cases (@LO.Propositional.Formula.ofNat ℕ inferInstance
            e.unpair.2.unpair.1 : Option Sentence) <;>
          cases (@LO.Propositional.Formula.ofNat ℕ inferInstance
            e.unpair.2.unpair.2 : Option Sentence) <;>
          simp [BoolPCWorld.eval, evalOp]
      by_cases h3 : e.unpair.1 = 3
      · simp only [evalList, List.length_map, List.length_range, evalSucc,
          h0, h1, h2, h3, ↓reduceIte]
        rw [evalBinary_history 3 l e.unpair.2 (e + 1) hleft hright]
        simp only [evalNorm, LO.Propositional.Formula.ofNat, h3]
        cases (@LO.Propositional.Formula.ofNat ℕ inferInstance
            e.unpair.2.unpair.1 : Option Sentence) <;>
          cases (@LO.Propositional.Formula.ofNat ℕ inferInstance
            e.unpair.2.unpair.2 : Option Sentence) <;>
          simp [BoolPCWorld.eval, evalOp]
      by_cases h4 : e.unpair.1 = 4
      · simp only [evalList, List.length_map, List.length_range, evalSucc,
          h0, h1, h2, h3, h4, ↓reduceIte]
        rw [evalBinary_history 4 l e.unpair.2 (e + 1) hleft hright]
        simp only [evalNorm, LO.Propositional.Formula.ofNat, h4]
        cases (@LO.Propositional.Formula.ofNat ℕ inferInstance
            e.unpair.2.unpair.1 : Option Sentence) <;>
          cases (@LO.Propositional.Formula.ofNat ℕ inferInstance
            e.unpair.2.unpair.2 : Option Sentence) <;>
          simp [BoolPCWorld.eval, evalOp]
      · have htag : 5 ≤ e.unpair.1 := by omega
        simp [evalList, evalSucc, evalNorm,
          LO.Propositional.Formula.ofNat, h0, h1, h2, h3, h4, htag]

private theorem evalNorm_prim : Primrec₂ evalNorm := by
  have hstep : Primrec₂ (fun (l : List Bool) (prior : List ℕ) =>
      some (evalList l prior)) :=
    Primrec₂.option_some_iff.mpr evalList_prim.to₂
  exact Primrec.nat_strong_rec evalNorm hstep
    (fun l n => by simpa using congrArg some (evalList_history l n))

/-- **Evaluation is primitive recursive**, as a function of the bit list denoting the world
and the sentence.  The world never appears as an argument — `bitsWorld` is applied and
beta-reduced in place — which is what makes the statement well-typed at all: `BoolPCWorld`
is `ℕ → Bool` and has no `Primcodable` instance. -/
theorem evalBits_prim : Primrec₂ fun (l : List Bool) (φ : Sentence) =>
    BoolPCWorld.eval (BoolPCWorld.bitsWorld l) φ := by
  have h : Primrec fun p : List Bool × Sentence =>
      decide (evalNorm p.1 (Encodable.encode p.2) = 2) :=
    (Primrec.eq.comp
      (evalNorm_prim.comp Primrec.fst (Primrec.encode.comp Primrec.snd))
      (Primrec.const 2)).decide
  exact h.to₂.of_eq fun l φ => by
    simp only [evalNorm, Encodable.encode, LO.Propositional.Formula.ofNat_toNat φ]
    cases BoolPCWorld.eval (BoolPCWorld.bitsWorld l) φ <;> simp

/-! ### The stage quantifier

`stageSort` was chosen to be `Finset.sort` under `sentenceCodeLE` precisely because that is
the order the stock `Finset Sentence` encoding already sorts by (Mathlib's `encodeMultiset`
sorts by its private `enle = encode ⁻¹'o (· ≤ ·)`, which `sentenceCodeLE` matches
definitionally, instances included).  So a stage's code *is* the code of its `stageSort`,
by `rfl`, and the compiled test recovers the list by decoding — no sorting is performed and
no `Finset` operation needs compiling.

None of this is semantic: `mem_stageSort` pins `stageSatBits` to `∀ φ ∈ stage` regardless
of the order, so the choice buys compilability only. -/

/-- A stage's Gödel code is exactly the code of its sorted sentence list. -/
theorem encode_eq_encode_stageSort (stage : Finset Sentence) :
    Encodable.encode stage = Encodable.encode (stageSort stage) := rfl

theorem stageSort_prim : Primrec stageSort := by
  have h : Primrec fun stage : Finset Sentence =>
      (Encodable.decode (α := List Sentence) (Encodable.encode stage)).getD [] :=
    Primrec.option_getD.comp (Primrec.decode.comp Primrec.encode) (Primrec.const [])
  exact h.of_eq fun stage => by
    rw [encode_eq_encode_stageSort, Encodable.encodek, Option.getD_some]

private theorem list_all_eq_foldr {α : Type} (l : List α) (p : α → Bool) :
    l.all p = l.foldr (fun a r => p a && r) true := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [List.all_cons, ih]

/-- **The stage quantifier is primitive recursive.**  Closes `evalBits_prim` over the
stage's sentence list. -/
theorem stageSatBits_prim : Primrec₂ stageSatBits := by
  have hstep : Primrec₂ fun (p : Finset Sentence × List Bool) (x : Sentence × Bool) =>
      BoolPCWorld.eval (BoolPCWorld.bitsWorld p.2) x.1 && x.2 :=
    (Primrec.and.comp
      (evalBits_prim.comp (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  have h := Primrec.list_foldr
    (f := fun p : Finset Sentence × List Bool => stageSort p.1)
    (g := fun _ : Finset Sentence × List Bool => true)
    (stageSort_prim.comp Primrec.fst) (Primrec.const true) hstep
  exact h.to₂.of_eq fun stage l => by
    simp only [stageSatBits, list_all_eq_foldr]

/-! ### The world enumeration -/

/-- **The bit-list enumeration is primitive recursive.**  A plain `Nat.rec` — this is the
one leaf that needed no `Sentence` machinery at all. -/
theorem allBitLists_prim : Primrec allBitLists := by
  have hstep : Primrec₂ fun (_ : ℕ) (prev : List (List Bool)) =>
      prev.flatMap (fun l => [false :: l, true :: l]) := by
    have hg : Primrec₂ fun (_ : ℕ × List (List Bool)) (l : List Bool) =>
        [false :: l, true :: l] :=
      (Primrec.list_cons.comp
        (Primrec.list_cons.comp (Primrec.const false) Primrec.snd)
        (Primrec.list_cons.comp
          (Primrec.list_cons.comp (Primrec.const true) Primrec.snd)
          (Primrec.const []))).to₂
    exact (Primrec.list_flatMap Primrec.snd hg).to₂
  have h : Primrec (Nat.rec (motive := fun _ => List (List Bool)) [[]]
      (fun _ prev => prev.flatMap (fun l => [false :: l, true :: l]))) :=
    Primrec.nat_rec₁ _ hstep
  exact h.of_eq fun n => by
    induction n with
    | zero => rfl
    | succ k ih => simp only [allBitLists, ← ih]

/-! ### The affine combination and its support bound -/

/-- `AffineCombination` is a plain pair of its two fields; `EF`, `Sentence` and `List`
already have `Primcodable` instances, so the structure inherits one through the equiv. -/
def affineEquiv : AffineCombination ≃ EF × List (EF × Sentence) where
  toFun A := (A.const, A.terms)
  invFun p := ⟨p.1, p.2⟩
  left_inv := fun ⟨_, _⟩ => rfl
  right_inv := fun ⟨_, _⟩ => rfl

instance affineCombinationPrimcodable : Primcodable AffineCombination :=
  Primcodable.ofEquiv _ affineEquiv

theorem affineEquiv_prim : Primrec affineEquiv := Primrec.of_equiv

theorem affineConst_prim : Primrec AffineCombination.const :=
  Primrec.fst.comp affineEquiv_prim

theorem affineTerms_prim : Primrec AffineCombination.terms :=
  Primrec.snd.comp affineEquiv_prim

/-- A `Finset` sum is the sum over `stageSort`: `Finset.sort_eq` says the sorted list is a
list representation of the underlying multiset, so no reordering argument is needed. -/
theorem finset_sum_eq_stageSort_sum (stage : Finset Sentence) (f : Sentence → ℕ) :
    stage.sum f = ((stageSort stage).map f).sum := by
  have h : (stageSort stage : Multiset Sentence) = stage.val := Finset.sort_eq _ _
  rw [Finset.sum_eq_multiset_sum, ← h]
  simp

/-- `settlementAtomLimit` over the sorted stage list rather than the `Finset`. -/
theorem settlementAtomLimit_eq_stageSort (A : AffineCombination) (stage : Finset Sentence) :
    A.settlementAtomLimit stage =
      ((stageSort stage).map BoolPCWorld.atomBound).sum +
        (A.terms.map (fun p => BoolPCWorld.atomBound p.2)).sum := by
  rw [AffineCombination.settlementAtomLimit,
    finset_sum_eq_stageSort_sum stage BoolPCWorld.atomBound]

/-- Mathlib's `Primrec` API has no `list_sum`; `List.sum` is a `foldr`. -/
private theorem list_sum_prim : Primrec (fun l : List ℕ => l.sum) := by
  have h := Primrec.list_foldr (f := fun l : List ℕ => l) (g := fun _ : List ℕ => 0)
    Primrec.id (Primrec.const 0)
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂
  exact h.of_eq fun l => by
    induction l with
    | nil => rfl
    | cons a t ih => simp [List.sum_cons, ← ih]

/-- **The support bound is primitive recursive.** -/
theorem settlementAtomLimit_prim :
    Primrec₂ AffineCombination.settlementAtomLimit := by
  have hstage : Primrec fun p : AffineCombination × Finset Sentence =>
      ((stageSort p.2).map BoolPCWorld.atomBound).sum :=
    list_sum_prim.comp
      (Primrec.list_map (stageSort_prim.comp Primrec.snd)
        (atomBound_prim.comp Primrec.snd).to₂)
  have hterms : Primrec fun p : AffineCombination × Finset Sentence =>
      (p.1.terms.map (fun q => BoolPCWorld.atomBound q.2)).sum :=
    list_sum_prim.comp
      (Primrec.list_map (affineTerms_prim.comp Primrec.fst)
        (atomBound_prim.comp (Primrec.snd.comp Primrec.snd)).to₂)
  exact (Primrec.nat_add.comp hstage hterms).to₂.of_eq fun A stage =>
    (settlementAtomLimit_eq_stageSort A stage).symm

/-! ### The fuel layer

Everything above is `Primrec`.  `valueRat` is not, and cannot be: it calls `EF.denoteRat Q`
where `Q` is the *market*, which a program reaches only through `market.quoteAtFuel`.  So
the checker is a fuel-clocked program rather than a primitive recursive function — which is
exactly the shape `SettlementChecker.spec` asks for (`∃ F, acceptsWithin code F ⟨i,j⟩`).

This mirrors `Strategy.valueRatListAtFuel` (`ROI.lean`) exactly: a three-part
sound/mono/exists-fuel contract over the existing `EF.denoteRatWithAtFuel`. -/

/-- Bounded exact evaluator for an affine combination's term list. -/
def affineTermsRatAtFuel {P : History} (market : MarketComputation P)
    (fuel : ℕ) (w : Sentence → ℚ) : List (EF × Sentence) → Option ℚ
  | [] => some 0
  | p :: rest => do
      let coefficient ← p.1.denoteRatWithAtFuel market fuel []
      let tail ← affineTermsRatAtFuel market fuel w rest
      pure (coefficient * w p.2 + tail)

/-- Bounded exact evaluator for `AffineCombination.valueRat`. -/
def AffineCombination.valueRatAtFuel (A : AffineCombination)
    {P : History} (market : MarketComputation P) (fuel : ℕ)
    (w : Sentence → ℚ) : Option ℚ := do
  let c ← A.const.denoteRatWithAtFuel market fuel []
  let ts ← affineTermsRatAtFuel market fuel w A.terms
  pure (c + ts)

theorem affineTermsRatAtFuel_sound {P : History} (market : MarketComputation P)
    (fuel : ℕ) (w : Sentence → ℚ) (terms : List (EF × Sentence)) {q : ℚ}
    (h : affineTermsRatAtFuel market fuel w terms = some q) :
    q = (terms.map (fun p =>
      p.1.denoteRat (fun d φ => market.quote d (Encodable.encode φ)) * w p.2)).sum := by
  induction terms generalizing q with
  | nil => simpa [affineTermsRatAtFuel] using h.symm
  | cons p rest ih =>
      simp only [affineTermsRatAtFuel, Option.bind_eq_bind] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨coefficient, hcoefficient, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨tail, htail, hq⟩ := h
      change some (coefficient * w p.2 + tail) = some q at hq
      injection hq with hq
      subst q
      simp only [List.map_cons, List.sum_cons, EF.denoteRat]
      rw [p.1.denoteRatWithAtFuel_sound market fuel [] hcoefficient, ih htail]
      rfl

theorem affineTermsRatAtFuel_mono {P : History} (market : MarketComputation P)
    {fuel fuel' : ℕ} (w : Sentence → ℚ) (terms : List (EF × Sentence)) {q : ℚ}
    (hff : fuel ≤ fuel')
    (h : affineTermsRatAtFuel market fuel w terms = some q) :
    affineTermsRatAtFuel market fuel' w terms = some q := by
  induction terms generalizing q with
  | nil => simpa [affineTermsRatAtFuel] using h
  | cons p rest ih =>
      simp only [affineTermsRatAtFuel, Option.bind_eq_bind] at h ⊢
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨coefficient, hcoefficient, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨tail, htail, hq⟩ := h
      rw [p.1.denoteRatWithAtFuel_mono market [] hff hcoefficient, Option.bind_eq_some_iff]
      exact ⟨coefficient, rfl, by rw [ih htail, Option.bind_eq_some_iff]; exact ⟨tail, rfl, hq⟩⟩

theorem exists_fuel_affineTermsRatAtFuel {P : History} (market : MarketComputation P)
    (w : Sentence → ℚ) (terms : List (EF × Sentence)) :
    ∃ fuel, affineTermsRatAtFuel market fuel w terms = some ((terms.map (fun p =>
      p.1.denoteRat (fun d φ => market.quote d (Encodable.encode φ)) * w p.2)).sum) := by
  induction terms with
  | nil => exact ⟨0, rfl⟩
  | cons p rest ih =>
      obtain ⟨f1, h1⟩ := EF.exists_fuel_denoteRatWithAtFuel market p.1 []
      obtain ⟨f2, h2⟩ := ih
      refine ⟨max f1 f2, ?_⟩
      simp only [affineTermsRatAtFuel, Option.bind_eq_bind]
      rw [EF.denoteRatWithAtFuel_mono market p.1 [] (le_max_left _ _) h1,
        Option.bind_eq_some_iff]
      refine ⟨_, rfl, ?_⟩
      rw [affineTermsRatAtFuel_mono market w rest (le_max_right _ _) h2,
        Option.bind_eq_some_iff]
      exact ⟨_, rfl, by simp [EF.denoteRat]⟩

theorem AffineCombination.valueRatAtFuel_sound (A : AffineCombination) {P : History}
    (market : MarketComputation P) (fuel : ℕ) (w : Sentence → ℚ) {q : ℚ}
    (h : A.valueRatAtFuel market fuel w = some q) :
    q = A.valueRat (fun d φ => market.quote d (Encodable.encode φ)) w := by
  simp only [AffineCombination.valueRatAtFuel, Option.bind_eq_bind] at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨c, hc, h⟩ := h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨ts, hts, hq⟩ := h
  change some (c + ts) = some q at hq
  injection hq with hq
  subst q
  rw [AffineCombination.valueRat, EF.denoteRat,
    A.const.denoteRatWithAtFuel_sound market fuel [] hc,
    affineTermsRatAtFuel_sound market fuel w A.terms hts]

theorem AffineCombination.valueRatAtFuel_mono (A : AffineCombination) {P : History}
    (market : MarketComputation P) {fuel fuel' : ℕ} (w : Sentence → ℚ) {q : ℚ}
    (hff : fuel ≤ fuel') (h : A.valueRatAtFuel market fuel w = some q) :
    A.valueRatAtFuel market fuel' w = some q := by
  simp only [AffineCombination.valueRatAtFuel, Option.bind_eq_bind] at h ⊢
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨c, hc, h⟩ := h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨ts, hts, hq⟩ := h
  rw [A.const.denoteRatWithAtFuel_mono market [] hff hc, Option.bind_eq_some_iff]
  exact ⟨c, rfl, by
    rw [affineTermsRatAtFuel_mono market w A.terms hff hts, Option.bind_eq_some_iff]
    exact ⟨ts, rfl, hq⟩⟩

theorem AffineCombination.exists_fuel_valueRatAtFuel (A : AffineCombination) {P : History}
    (market : MarketComputation P) (w : Sentence → ℚ) :
    ∃ fuel, A.valueRatAtFuel market fuel w =
      some (A.valueRat (fun d φ => market.quote d (Encodable.encode φ)) w) := by
  obtain ⟨f1, h1⟩ := EF.exists_fuel_denoteRatWithAtFuel market A.const []
  obtain ⟨f2, h2⟩ := exists_fuel_affineTermsRatAtFuel market w A.terms
  refine ⟨max f1 f2, ?_⟩
  simp only [AffineCombination.valueRatAtFuel, Option.bind_eq_bind]
  rw [EF.denoteRatWithAtFuel_mono market A.const [] (le_max_left _ _) h1,
    Option.bind_eq_some_iff]
  refine ⟨_, rfl, ?_⟩
  rw [affineTermsRatAtFuel_mono market w A.terms (le_max_right _ _) h2,
    Option.bind_eq_some_iff]
  exact ⟨_, rfl, by simp [AffineCombination.valueRat, EF.denoteRat]⟩

end SettlementCompile

#print axioms polyFueled_dovetailFound
#print axioms polyFueled_deadlinePassed
#print axioms PatientSettlementClock.ofSemiDecider
#print axioms PatientSettlementClock.ofChecker
#print axioms SettlementChecker.toSemiDecider
#print axioms AffineCombination.DeterminedViaTheory.settlementTest_iff_settled
#print axioms AffineCombination.settlementTestBool_iff
#print axioms mem_allBitLists
#print axioms AffineCombination.finiteWorlds_agree_of_agree
#print axioms acceptsWithin_mono
#print axioms dovetailFound_mono
#print axioms deadlinePassed_sound
#print axioms deadlinePassed_eventually
#print axioms deadlinePassed_mono
#print axioms dovetailFound_eq_true_iff
#print axioms triangularRepeat_codes
#print axioms triangularRepeat_repeats
#print axioms EfficientRepeatedEnumeration.ofPoly
#print axioms EfficientRepeatedEnumeration.ofCE

end LogicalInduction

