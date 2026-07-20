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

private lemma natPair_mono {a b c d : ℕ} (hab : a ≤ b) (hcd : c ≤ d) :
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

lemma codeEvalBound_mono (code : Nat.Partrec.Code) :
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

lemma codeEvalBound_poly (code : Nat.Partrec.Code) :
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
lemma codeEvaln_result_le (code : Nat.Partrec.Code) :
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

lemma codeEvalnNat_le (code : Nat.Partrec.Code) (z : ℕ) :
    codeEvalnNat code z ≤ codeEvalBound code z.unpair.1 + 1 := by
  unfold codeEvalnNat
  cases h : Nat.Partrec.Code.evaln z.unpair.1 code z.unpair.2 with
  | none => simp
  | some out =>
      simpa using Nat.add_le_add_right (codeEvaln_result_le code h) 1

lemma codeEvalnNat_output_poly (code : Nat.Partrec.Code) :
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

lemma precEvalState_eq_evaln (cf cg : Nat.Partrec.Code)
    {clock a total j : ℕ} (_htotal : total ≤ clock) (hj : j ≤ total) :
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
        | zero => simp [Nat.Partrec.Code.evaln]
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
            simp [Nat.Partrec.Code.evaln, hnle]

lemma precEvalState_final (cf cg : Nat.Partrec.Code)
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
lemma evaln_eq_none_of_gt {k : ℕ} (c : Nat.Partrec.Code) {n : ℕ} (h : k ≤ n) :
    Nat.Partrec.Code.evaln k c n = none := by
  rcases hx : Nat.Partrec.Code.evaln k c n with _ | x
  · rfl
  · exact absurd (Nat.Partrec.Code.evaln_bound hx) (by omega)

open Nat.Partrec.Code in
/-- Base-code interpreters `zero/succ/left/right` share the shape
`if z.1 ≤ z.2 then 0 else rawValue + 1`: the guard fails exactly when `z.1 ≤ z.2`
(`z.2 ≥ fuel`, incl. `fuel = 0`). Compiles via one `ifzSel` over `subc` (`z.1 - z.2`). -/
lemma polyFueled_baseGuard {bv : ℕ → ℕ} {c : Nat.Partrec.Code} (h : PolyFueled c bv) :
    ∃ prog, PolyFueled prog (fun z => if z.unpair.1 ≤ z.unpair.2 then 0 else bv z + 1) := by
  refine ⟨_, (ifzSel_polyFueled.comp
    (((PolyFueled.const 0).pair h.succ_comp).pair subc_polyFueled)).of_eq (fun z => ?_)⟩
  simp only [Nat.unpair_pair, ifzSelFn]
  by_cases hle : z.unpair.1 ≤ z.unpair.2
  · rw [if_pos hle, if_pos (Nat.sub_eq_zero_of_le hle)]
  · rw [if_neg hle, if_neg (by omega : ¬ z.unpair.1 - z.unpair.2 = 0)]

lemma codeEvalnNat_zero_eq (z : ℕ) :
    codeEvalnNat .zero z = if z.unpair.1 ≤ z.unpair.2 then 0 else 0 + 1 := by
  rw [codeEvalnNat]
  cases hk : z.unpair.1 with
  | zero => simp [Nat.Partrec.Code.evaln]
  | succ k =>
    by_cases hle : z.unpair.2 ≤ k
    · simp [Nat.Partrec.Code.evaln, hle]
    · simp [Nat.Partrec.Code.evaln, hle, (by omega : k + 1 ≤ z.unpair.2)]

lemma codeEvalnNat_succ_eq (z : ℕ) :
    codeEvalnNat .succ z = if z.unpair.1 ≤ z.unpair.2 then 0 else z.unpair.2 + 1 + 1 := by
  rw [codeEvalnNat]
  cases hk : z.unpair.1 with
  | zero => simp [Nat.Partrec.Code.evaln]
  | succ k =>
    by_cases hle : z.unpair.2 ≤ k
    · simp [Nat.Partrec.Code.evaln, hle]
    · simp [Nat.Partrec.Code.evaln, hle, (by omega : k + 1 ≤ z.unpair.2)]

lemma codeEvalnNat_left_eq (z : ℕ) :
    codeEvalnNat .left z = if z.unpair.1 ≤ z.unpair.2 then 0 else z.unpair.2.unpair.1 + 1 := by
  rw [codeEvalnNat]
  cases hk : z.unpair.1 with
  | zero => simp [Nat.Partrec.Code.evaln]
  | succ k =>
    by_cases hle : z.unpair.2 ≤ k
    · simp [Nat.Partrec.Code.evaln, hle]
    · simp [Nat.Partrec.Code.evaln, hle, (by omega : k + 1 ≤ z.unpair.2)]

lemma codeEvalnNat_right_eq (z : ℕ) :
    codeEvalnNat .right z = if z.unpair.1 ≤ z.unpair.2 then 0 else z.unpair.2.unpair.2 + 1 := by
  rw [codeEvalnNat]
  cases hk : z.unpair.1 with
  | zero => simp [Nat.Partrec.Code.evaln]
  | succ k =>
    by_cases hle : z.unpair.2 ≤ k
    · simp [Nat.Partrec.Code.evaln, hle]
    · simp [Nat.Partrec.Code.evaln, hle, (by omega : k + 1 ≤ z.unpair.2)]

/-- `pair`: with both sub-code interpreters at the *same* fuel/input `z`, the whole clause is
`none` iff either sub-result is (the guard-fail case is subsumed, since a failed guard sends
each sub-interpreter to `0`). -/
lemma codeEvalnNat_pair_eq (cf cg : Nat.Partrec.Code) (z : ℕ) :
    codeEvalnNat (.pair cf cg) z =
      if codeEvalnNat cf z = 0 ∨ codeEvalnNat cg z = 0 then 0
      else Nat.pair (codeEvalnNat cf z - 1) (codeEvalnNat cg z - 1) + 1 := by
  simp only [codeEvalnNat]
  cases hk : z.unpair.1 with
  | zero => simp [Nat.Partrec.Code.evaln]
  | succ k =>
    by_cases hle : z.unpair.2 ≤ k
    · cases hf : Nat.Partrec.Code.evaln (k + 1) cf z.unpair.2 with
      | none => simp [Nat.Partrec.Code.evaln, hle, hf, Seq.seq]
      | some vf =>
        cases hg : Nat.Partrec.Code.evaln (k + 1) cg z.unpair.2 with
        | none => simp [Nat.Partrec.Code.evaln, hle, hf, hg, Seq.seq]
        | some vg =>
          simp [Nat.Partrec.Code.evaln, hle, hf, hg, Seq.seq]
    · have hf : Nat.Partrec.Code.evaln (k + 1) cf z.unpair.2 = none :=
        evaln_eq_none_of_gt cf (by omega)
      simp [Nat.Partrec.Code.evaln, hle, hf, Seq.seq]

/-- `comp`: the outer interpreter feeds `cf` the *output* of `cg`, at the same fuel `z.1`. -/
lemma codeEvalnNat_comp_eq (cf cg : Nat.Partrec.Code) (z : ℕ) :
    codeEvalnNat (.comp cf cg) z =
      if codeEvalnNat cg z = 0 then 0
      else codeEvalnNat cf (Nat.pair z.unpair.1 (codeEvalnNat cg z - 1)) := by
  simp only [codeEvalnNat, Nat.unpair_pair]
  cases hk : z.unpair.1 with
  | zero => simp [Nat.Partrec.Code.evaln]
  | succ k =>
    by_cases hle : z.unpair.2 ≤ k
    · cases hg : Nat.Partrec.Code.evaln (k + 1) cg z.unpair.2 with
      | none => simp [Nat.Partrec.Code.evaln, hle, hg]
      | some vg =>
        simp [Nat.Partrec.Code.evaln, hle, hg]
    · have hg : Nat.Partrec.Code.evaln (k + 1) cg z.unpair.2 = none :=
        evaln_eq_none_of_gt cg (by omega)
      simp [Nat.Partrec.Code.evaln, hle, hg]

lemma codeEvalnNat_pair_polyFueled {cf cg : Nat.Partrec.Code}
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

lemma codeEvalnNat_comp_polyFueled {cf cg : Nat.Partrec.Code}
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

lemma codeEvalnNat_eq_optNat (c : Nat.Partrec.Code) (z : ℕ) :
    codeEvalnNat c z = optNat (Nat.Partrec.Code.evaln z.unpair.1 c z.unpair.2) := rfl

lemma optNat_if {P : Prop} [Decidable P] (o : Option ℕ) :
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

lemma precNat_eq (cf cg : Nat.Partrec.Code) (A : ℕ) :
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
        simp [optNat]
      · have hp1 : precNat cf cg A j = p + 1 := by rw [ih, hp]; rfl
        by_cases hguard : Nat.pair A.unpair.2.unpair.1 (j + 1) <
            A.unpair.1 - A.unpair.2.unpair.2 + j + 1
        · rw [if_pos ⟨hguard, by simp [hp1]⟩, if_pos hguard, hp1,
            Nat.add_sub_cancel, codeEvalnNat_eq_optNat, Nat.unpair_pair]
          simp
        · rw [if_neg (by tauto), if_neg hguard]
          simp [optNat]

/-- `prec`: the fuel-decrement recursion, packaged as the guarded final value of `precNat`. -/
lemma codeEvalnNat_prec_eq (cf cg : Nat.Partrec.Code) (z : ℕ) :
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

lemma rfindNat_eq (cf : Nat.Partrec.Code) (A : ℕ) :
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
        simp [Nat.unpaired, Nat.unpair_pair, hx, optNat]
      · have hguard : Nat.pair A.unpair.2.unpair.1
            (A.unpair.2.unpair.2 + (A.unpair.1 - (j + 1))) ≤ j := by
          have := Nat.Partrec.Code.evaln_bound hx; omega
        have hcfv : codeEvalnNat cf (Nat.pair (j + 1) (Nat.pair A.unpair.2.unpair.1
            (A.unpair.2.unpair.2 + (A.unpair.1 - (j + 1))))) = x + 1 := by
          simp only [codeEvalnNat, Nat.unpair_pair, hx]
        rw [hcfv, Nat.Partrec.Code.evaln]
        rcases x with _ | y
        · simp [Nat.unpaired, Nat.unpair_pair, hx, hguard, optNat]
        · rw [if_neg (by omega : y + 1 + 1 ≠ 0), if_neg (by omega : y + 1 + 1 ≠ 1)]
          simp [Nat.unpaired, Nat.unpair_pair, hx, hguard, optNat,
            hM1, hIH]

/-- `rfind'`: normalized bounded minimization is the final search state at `j = clock`. -/
lemma codeEvalnNat_rfind_eq (cf : Nat.Partrec.Code) (z : ℕ) :
    codeEvalnNat (.rfind' cf) z = rfindNat cf z z.unpair.1 := by
  rw [rfindNat_eq cf z z.unpair.1 le_rfl, codeEvalnNat_eq_optNat]
  simp only [Nat.sub_self, Nat.add_zero, Nat.pair_unpair]

/-- Every `rfindNat` value is `0` or a returned search position `≤ m0 + clock`. -/
lemma rfindNat_le (cf : Nat.Partrec.Code) (A : ℕ) :
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
lemma codeEvalnNat_prec_polyFueled {cf cg : Nat.Partrec.Code}
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
lemma codeEvalnNat_rfind_polyFueled {cf : Nat.Partrec.Code}
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
lemma codeEvalnNat_polyFueled :
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

lemma dovetailFound_eq_true_iff (c : Nat.Partrec.Code) (i n : ℕ) :
    dovetailFound c i n = true ↔ ∃ j ≤ n, acceptsWithin c n (Nat.pair i j) = true := by
  simp [dovetailFound, boundedAny_eq_true_iff, dovetailStep]

section
-- The documented `dd:fuel` gotcha: `whnf` loops on `Nat.sqrt` (reached via `Nat.unpair`'s
-- `Primcodable` instance), not on any domain math.  Scope it irreducible rather than
-- raising heartbeats.
attribute [local irreducible] Nat.sqrt

/-- Equality against a fixed natural constant as a polynomial `0`/`1` table. -/
lemma polyFueled_eqConst {cf : Nat.Partrec.Code} {f : ℕ → ℕ}
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
lemma polyFueled_dovetailFound (c : Nat.Partrec.Code) :
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
lemma polyFueled_selectConst {cf : Nat.Partrec.Code} {f : ℕ → ℕ}
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
lemma deadlineRun_eq (f : DeferralFunction) {n k : ℕ} (h : 0 < deadlineRun f n k) :
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
lemma deadlineRun_mono (f : DeferralFunction) {n m k : ℕ} (hm : n ≤ m)
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

lemma deadlinePassed_eq_true_iff (f : DeferralFunction) (i n : ℕ) :
    deadlinePassed f i n = true ↔
      ∀ k ≤ i, 0 < deadlineRun f n k ∧ deadlineRun f n k ≤ n := by
  rw [deadlinePassed, boundedNone_eq_true_iff]
  simp only [deadlineStep, Nat.unpair_pair, decide_eq_false_iff_not, not_not]
  constructor
  · intro h k hk; have := h k hk; omega
  · intro h k hk; have := h k hk; omega

lemma deferralEnvelope_lt_of_forall (f : DeferralFunction) (i n : ℕ)
    (h : ∀ k ≤ i, f.f k < n) : deferralEnvelope f i < n := by
  induction i with
  | zero => simpa [deferralEnvelope] using h 0 le_rfl
  | succ i ih =>
      simp only [deferralEnvelope, max_lt_iff]
      exact ⟨ih (fun k hk => h k (by omega)), h (i + 1) le_rfl⟩

/-- **Soundness**: certification implies the deadline really has passed. -/
lemma deadlinePassed_sound (f : DeferralFunction) {i n : ℕ}
    (h : deadlinePassed f i n = true) : deferralEnvelope f i < n := by
  refine deferralEnvelope_lt_of_forall f i n (fun k hk => ?_)
  obtain ⟨hpos, hle⟩ := (deadlinePassed_eq_true_iff f i n).1 h k hk
  rw [deadlineRun_eq f hpos] at hle
  omega

/-- **Monotone**: a larger budget preserves certification. -/
lemma deadlinePassed_mono (f : DeferralFunction) {i n : ℕ}
    (h : deadlinePassed f i n = true) : deadlinePassed f i (n + 1) = true := by
  rw [deadlinePassed_eq_true_iff] at h ⊢
  intro k hk
  obtain ⟨hpos, hle⟩ := h k hk
  rw [deadlineRun_mono f (Nat.le_succ n) hpos]
  exact ⟨hpos, by omega⟩

/-- **Eventual completion**: every component's deadline is eventually certified. -/
lemma deadlinePassed_eventually (f : DeferralFunction) (i : ℕ) :
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
lemma polyFueled_deadlinePassed (f : DeferralFunction) :
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

lemma acceptsWithin_mono (c : Nat.Partrec.Code) {F F' x : ℕ} (h : F ≤ F')
    (ha : acceptsWithin c F x = true) : acceptsWithin c F' x = true := by
  cases hev : Nat.Partrec.Code.evaln F c x with
  | none => simp [acceptsWithin, codeEvalnNat, hev] at ha
  | some out =>
      have hm : Nat.Partrec.Code.evaln F' c x = some out :=
        Nat.Partrec.Code.evaln_mono h hev
      simp only [acceptsWithin, codeEvalnNat, Nat.unpair_pair, hev, decide_eq_true_iff] at ha
      simp [acceptsWithin, codeEvalnNat, hm, ha]

lemma dovetailFound_mono (c : Nat.Partrec.Code) {i n : ℕ}
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

private lemma orNot_eq_false_iff (a b : Bool) :
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

lemma triangularRepeat_codes (source : ℕ → Sentence)
    (hsource : PolySentenceCodes source) :
    PolySentenceCodes (triangularRepeat source) := by
  obtain ⟨code, hcode⟩ := hsource
  exact ⟨code.comp Nat.Partrec.Code.left,
    hcode.comp PolyFueled.left⟩

lemma triangularRepeat_repeats (source : ℕ → Sentence) :
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
lemma codeEvalnNat_pair_mono {code : Nat.Partrec.Code} {i fuel fuel' v : ℕ}
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

lemma ceRepeatSeq_eq_source {source : ℕ → Sentence} (h : CEEnumeration source)
    {n i : ℕ} (hr : codeEvalnNat h.code (Nat.pair n.unpair.2 n.unpair.1)
      = Encodable.encode (source i) + 1) :
    ceRepeatSeq h n = source i := by
  simp only [ceRepeatSeq, hr, Nat.add_sub_cancel, Encodable.encodek, Option.getD_some,
    Nat.add_one_ne_zero, if_false]

lemma ceRepeatSeq_encode {source : ℕ → Sentence} (h : CEEnumeration source) (n : ℕ) :
    Encodable.encode (ceRepeatSeq h n) =
      if codeEvalnNat h.code (Nat.pair n.unpair.2 n.unpair.1) = 0 then
        Encodable.encode (source 0)
      else codeEvalnNat h.code (Nat.pair n.unpair.2 n.unpair.1) - 1 := by
  by_cases hz : codeEvalnNat h.code (Nat.pair n.unpair.2 n.unpair.1) = 0
  · simp [ceRepeatSeq, hz]
  · obtain ⟨i, hi⟩ := h.outputs_sound _ hz
    rw [ceRepeatSeq_eq_source h hi, if_neg hz, hi, Nat.add_sub_cancel]

lemma ceRepeatSeq_codes {source : ℕ → Sentence} (h : CEEnumeration source) :
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

private lemma atomBoundBinary_prim : Primrec₂ atomBoundBinary := by
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

private lemma atomBoundSucc_prim : Primrec₂ atomBoundSucc := by
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

private lemma atomBoundList_prim : Primrec atomBoundList :=
  (Primrec.nat_casesOn Primrec.list_length (Primrec.const 0)
    atomBoundSucc_prim).of_eq fun prior => by simp only [atomBoundList]

private lemma atomBoundNorm_zero : atomBoundNorm 0 = 0 := by
  simp [atomBoundNorm, LO.Propositional.Formula.ofNat]

private lemma atomBoundHistory_getD {n k : ℕ} (hk : k < n) :
    ((List.range n).map atomBoundNorm).getD k 0 = atomBoundNorm k := by
  rw [← atomBoundNorm_zero, List.getD_map]
  simp [hk]

/-- The binary step reads both children out of the history correctly.  Shared by all three
connectives: `atomBound` maxes its children regardless of which one it is. -/
private lemma atomBoundBinary_history (payload n : ℕ)
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

private lemma atomBoundList_history (n : ℕ) :
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
          LO.Propositional.Formula.ofNat, h1]
      -- The three binary tags: identical modulo the constructor `ofNat` rebuilds.
      by_cases h2 : e.unpair.1 = 2
      · simp only [atomBoundList, List.length_map, List.length_range, atomBoundSucc,
          h2, ↓reduceIte]
        rw [hbin]
        simp only [atomBoundNorm, LO.Propositional.Formula.ofNat, h2]
        cases (@LO.Propositional.Formula.ofNat ℕ inferInstance
            e.unpair.2.unpair.1 : Option Sentence) <;>
          cases (@LO.Propositional.Formula.ofNat ℕ inferInstance
            e.unpair.2.unpair.2 : Option Sentence) <;>
          simp [BoolPCWorld.atomBound]
      by_cases h3 : e.unpair.1 = 3
      · simp only [atomBoundList, List.length_map, List.length_range, atomBoundSucc,
          h3, ↓reduceIte]
        rw [hbin]
        simp only [atomBoundNorm, LO.Propositional.Formula.ofNat, h3]
        cases (@LO.Propositional.Formula.ofNat ℕ inferInstance
            e.unpair.2.unpair.1 : Option Sentence) <;>
          cases (@LO.Propositional.Formula.ofNat ℕ inferInstance
            e.unpair.2.unpair.2 : Option Sentence) <;>
          simp [BoolPCWorld.atomBound]
      by_cases h4 : e.unpair.1 = 4
      · simp only [atomBoundList, List.length_map, List.length_range, atomBoundSucc,
          h4, ↓reduceIte]
        rw [hbin]
        simp only [atomBoundNorm, LO.Propositional.Formula.ofNat, h4]
        cases (@LO.Propositional.Formula.ofNat ℕ inferInstance
            e.unpair.2.unpair.1 : Option Sentence) <;>
          cases (@LO.Propositional.Formula.ofNat ℕ inferInstance
            e.unpair.2.unpair.2 : Option Sentence) <;>
          simp [BoolPCWorld.atomBound]
      · have htag : 5 ≤ e.unpair.1 := by omega
        simp [atomBoundList, atomBoundSucc, atomBoundNorm,
          LO.Propositional.Formula.ofNat, h0, h1, h2, h3, h4]

private lemma atomBoundNorm_prim : Primrec atomBoundNorm := by
  have hstep : Primrec₂ (fun (_ : Unit) (prior : List ℕ) =>
      some (atomBoundList prior)) :=
    Primrec₂.option_some_iff.mpr (atomBoundList_prim.comp Primrec₂.right)
  have hrec := Primrec.nat_strong_rec (fun (_ : Unit) n => atomBoundNorm n)
    hstep (fun _ n => by simpa using congrArg some (atomBoundList_history n))
  exact (hrec.comp (Primrec.const ()) Primrec.id).of_eq fun n => rfl

/-- **`atomBound` is primitive recursive.**  The first of the two `Sentence` recursions the
settlement test needs; `evalBits_prim` below is the other. -/
lemma atomBound_prim : Primrec BoolPCWorld.atomBound := by
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

private lemma evalBinary_prim (tag : ℕ) : Primrec₂ (evalBinary tag) := by
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

private lemma evalSucc_prim :
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

private lemma evalList_prim :
    Primrec fun p : List Bool × List ℕ => evalList p.1 p.2 := by
  have h := Primrec.nat_casesOn (Primrec.list_length.comp Primrec.snd)
    (Primrec.const 0)
    (evalSucc_prim.comp
      ((Primrec.fst.comp Primrec.fst).pair
        ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))).to₂
  exact h.of_eq fun p => by simp only [evalList]

private lemma evalNorm_zero (l : List Bool) : evalNorm l 0 = 0 := by
  simp [evalNorm, LO.Propositional.Formula.ofNat]

private lemma evalHistory_getD (l : List Bool) {n k : ℕ} (hk : k < n) :
    ((List.range n).map (evalNorm l)).getD k 0 = evalNorm l k := by
  rw [← evalNorm_zero l, List.getD_map]
  simp [hk]

private lemma evalBinary_history (tag : ℕ) (l : List Bool) (payload n : ℕ)
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

private lemma evalList_history (l : List Bool) (n : ℕ) :
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
          LO.Propositional.Formula.ofNat, h1]
      by_cases h2 : e.unpair.1 = 2
      · simp only [evalList, List.length_map, List.length_range, evalSucc,
          h2, ↓reduceIte]
        rw [evalBinary_history 2 l e.unpair.2 (e + 1) hleft hright]
        simp only [evalNorm, LO.Propositional.Formula.ofNat, h2]
        cases (@LO.Propositional.Formula.ofNat ℕ inferInstance
            e.unpair.2.unpair.1 : Option Sentence) <;>
          cases (@LO.Propositional.Formula.ofNat ℕ inferInstance
            e.unpair.2.unpair.2 : Option Sentence) <;>
          simp [BoolPCWorld.eval, evalOp]
      by_cases h3 : e.unpair.1 = 3
      · simp only [evalList, List.length_map, List.length_range, evalSucc,
          h3, ↓reduceIte]
        rw [evalBinary_history 3 l e.unpair.2 (e + 1) hleft hright]
        simp only [evalNorm, LO.Propositional.Formula.ofNat, h3]
        cases (@LO.Propositional.Formula.ofNat ℕ inferInstance
            e.unpair.2.unpair.1 : Option Sentence) <;>
          cases (@LO.Propositional.Formula.ofNat ℕ inferInstance
            e.unpair.2.unpair.2 : Option Sentence) <;>
          simp [BoolPCWorld.eval, evalOp]
      by_cases h4 : e.unpair.1 = 4
      · simp only [evalList, List.length_map, List.length_range, evalSucc,
          h4, ↓reduceIte]
        rw [evalBinary_history 4 l e.unpair.2 (e + 1) hleft hright]
        simp only [evalNorm, LO.Propositional.Formula.ofNat, h4]
        cases (@LO.Propositional.Formula.ofNat ℕ inferInstance
            e.unpair.2.unpair.1 : Option Sentence) <;>
          cases (@LO.Propositional.Formula.ofNat ℕ inferInstance
            e.unpair.2.unpair.2 : Option Sentence) <;>
          simp [BoolPCWorld.eval, evalOp]
      · have htag : 5 ≤ e.unpair.1 := by omega
        simp [evalList, evalSucc, evalNorm,
          LO.Propositional.Formula.ofNat, h0, h1, h2, h3, h4]

private lemma evalNorm_prim : Primrec₂ evalNorm := by
  have hstep : Primrec₂ (fun (l : List Bool) (prior : List ℕ) =>
      some (evalList l prior)) :=
    Primrec₂.option_some_iff.mpr evalList_prim.to₂
  exact Primrec.nat_strong_rec evalNorm hstep
    (fun l n => by simpa using congrArg some (evalList_history l n))

/-- **Evaluation is primitive recursive**, as a function of the bit list denoting the world
and the sentence.  The world never appears as an argument — `bitsWorld` is applied and
beta-reduced in place — which is what makes the statement well-typed at all: `BoolPCWorld`
is `ℕ → Bool` and has no `Primcodable` instance. -/
lemma evalBits_prim : Primrec₂ fun (l : List Bool) (φ : Sentence) =>
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
lemma encode_eq_encode_stageSort (stage : Finset Sentence) :
    Encodable.encode stage = Encodable.encode (stageSort stage) := rfl

lemma stageSort_prim : Primrec stageSort := by
  have h : Primrec fun stage : Finset Sentence =>
      (Encodable.decode (α := List Sentence) (Encodable.encode stage)).getD [] :=
    Primrec.option_getD.comp (Primrec.decode.comp Primrec.encode) (Primrec.const [])
  exact h.of_eq fun stage => by
    rw [encode_eq_encode_stageSort, Encodable.encodek, Option.getD_some]

private lemma list_all_eq_foldr {α : Type} (l : List α) (p : α → Bool) :
    l.all p = l.foldr (fun a r => p a && r) true := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [List.all_cons, ih]

/-- **The stage quantifier is primitive recursive.**  Closes `evalBits_prim` over the
stage's sentence list. -/
lemma stageSatBits_prim : Primrec₂ stageSatBits := by
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
lemma allBitLists_prim : Primrec allBitLists := by
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

lemma affineEquiv_prim : Primrec affineEquiv := Primrec.of_equiv

lemma affineConst_prim : Primrec AffineCombination.const :=
  Primrec.fst.comp affineEquiv_prim

lemma affineTerms_prim : Primrec AffineCombination.terms :=
  Primrec.snd.comp affineEquiv_prim

/-! ### Polynomial affine sequences are primitive recursive

`PolySequence` exposes each feature as a polynomially emitted serialization rather than an
opaque encoded `EF`.  Reconstruct the token list via `PolySegStream.primrec`, then reuse the
existing primitive-recursive trade-stream decoder to invert `EF.serialize`. -/

private def serializationMarkerSentence : Sentence :=
  LO.Propositional.Formula.atom 0

/-- Decode one serialized feature by appending a dummy trade frame and reusing the canonical
trade-stream decoder.  Malformed streams totalize to the zero feature. -/
def efFromSerializedTokens (tokens : List ℕ) : EF :=
  match deserializeTrades
      (tokens ++ [6, Encodable.encode serializationMarkerSentence]) with
  | some ((e, _) :: _) => e
  | _ => EF.const 0

lemma efFromSerializedTokens_prim : Primrec efFromSerializedTokens := by
  have hframe : Primrec fun tokens : List ℕ =>
      tokens ++ [6, Encodable.encode serializationMarkerSentence] :=
    Primrec.list_append.comp Primrec.id
      (Primrec.const [6, Encodable.encode serializationMarkerSentence])
  have hdecode : Primrec fun tokens : List ℕ =>
      deserializeTrades (tokens ++ [6, Encodable.encode serializationMarkerSentence]) :=
    deserializeTrades_prim.comp hframe
  have hsome : Primrec₂ fun (_ : List ℕ) (trades : List (EF × Sentence)) =>
      match trades with
      | [] => EF.const 0
      | (e, _) :: _ => e :=
    (Primrec.list_casesOn Primrec.snd (Primrec.const (EF.const 0))
      (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)).to₂).to₂.of_eq
        fun _ trades => by cases trades <;> rfl
  exact (Primrec.option_casesOn hdecode (Primrec.const (EF.const 0)) hsome).of_eq
    fun tokens => by
      unfold efFromSerializedTokens
      cases deserializeTrades
          (tokens ++ [6, Encodable.encode serializationMarkerSentence]) with
      | none => rfl
      | some trades => cases trades <;> rfl

lemma efFromSerializedTokens_serialize (e : EF) :
    efFromSerializedTokens e.serialize = e := by
  unfold efFromSerializedTokens
  rw [show e.serialize ++ [6, Encodable.encode serializationMarkerSentence] =
      serializeTrades [(e, serializationMarkerSentence)] by
    simp [serializeTrades]]
  rw [deserializeTrades_serializeTrades]

/-- The operational polynomial interface on an affine family entails ordinary primitive
recursiveness of the family.  This closes the representation bridge needed by concrete
settlement and maturity checkers. -/
lemma AffineCombination.PolySequence.primrec {As : ℕ → AffineCombination}
    (h : PolySequence As) : Primrec As := by
  have hcount : Primrec h.termCount := by
    obtain ⟨c, hc⟩ := h.termCount_poly
    exact hc.primrec
  have hconstTokens : Primrec fun n => (As n).const.serialize :=
    h.const_poly.primrec
  have hconst : Primrec fun n => (As n).const :=
    (efFromSerializedTokens_prim.comp hconstTokens).of_eq fun n =>
      efFromSerializedTokens_serialize (As n).const
  have hcoefficientTokens : Primrec fun z => (h.coefficient z).serialize :=
    h.coefficient_poly.primrec
  have hcoefficient : Primrec h.coefficient :=
    (efFromSerializedTokens_prim.comp hcoefficientTokens).of_eq fun z =>
      efFromSerializedTokens_serialize (h.coefficient z)
  have hsentenceCode : Primrec fun z => Encodable.encode (h.sentence z) := by
    obtain ⟨c, hc⟩ := h.sentence_poly
    exact hc.primrec
  have hsentence : Primrec h.sentence := by
    have hdecode : Primrec fun z =>
        (Encodable.decode (Encodable.encode (h.sentence z))).getD
          serializationMarkerSentence :=
      Primrec.option_getD.comp (Primrec.decode.comp hsentenceCode)
        (Primrec.const serializationMarkerSentence)
    exact hdecode.of_eq fun z => by rw [Encodable.encodek]; rfl
  have hrange : Primrec fun n => List.range (h.termCount n) :=
    Primrec.list_range.comp hcount
  have hterm : Primrec₂ fun n j =>
      (h.coefficient (Nat.pair n j), h.sentence (Nat.pair n j)) :=
    ((hcoefficient.comp Primrec₂.natPair).pair
      (hsentence.comp Primrec₂.natPair)).to₂
  have htermsRaw : Primrec fun n =>
      (List.range (h.termCount n)).map fun j =>
        (h.coefficient (Nat.pair n j), h.sentence (Nat.pair n j)) :=
    Primrec.list_map hrange hterm
  have hterms : Primrec fun n => (As n).terms :=
    htermsRaw.of_eq fun n => (h.terms_eq n).symm
  exact (Primrec.of_equiv_symm.comp (hconst.pair hterms)).of_eq fun n => by
    exact affineEquiv.left_inv (As n)

/-- A `Finset` sum is the sum over `stageSort`: `Finset.sort_eq` says the sorted list is a
list representation of the underlying multiset, so no reordering argument is needed. -/
lemma finset_sum_eq_stageSort_sum (stage : Finset Sentence) (f : Sentence → ℕ) :
    stage.sum f = ((stageSort stage).map f).sum := by
  have h : (stageSort stage : Multiset Sentence) = stage.val := Finset.sort_eq _ _
  rw [Finset.sum_eq_multiset_sum, ← h]
  simp

/-- `settlementAtomLimit` over the sorted stage list rather than the `Finset`. -/
lemma settlementAtomLimit_eq_stageSort (A : AffineCombination) (stage : Finset Sentence) :
    A.settlementAtomLimit stage =
      ((stageSort stage).map BoolPCWorld.atomBound).sum +
        (A.terms.map (fun p => BoolPCWorld.atomBound p.2)).sum := by
  rw [AffineCombination.settlementAtomLimit,
    finset_sum_eq_stageSort_sum stage BoolPCWorld.atomBound]

/-- Mathlib's `Primrec` API has no `list_sum`; `List.sum` is a `foldr`. -/
private lemma list_sum_prim : Primrec (fun l : List ℕ => l.sum) := by
  have h := Primrec.list_foldr (f := fun l : List ℕ => l) (g := fun _ : List ℕ => 0)
    Primrec.id (Primrec.const 0)
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂
  exact h.of_eq fun l => by
    induction l with
    | nil => rfl
    | cons a t ih => simp [List.sum_cons, ← ih]

/-- **The support bound is primitive recursive.** -/
lemma settlementAtomLimit_prim :
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

/-! ### The computable bounded EF evaluator (the `readyAtFuel` guard)

`AffineCombination.valueRatAtFuel` folds `EF.denoteRatWithAtFuel` — an `EF` recursion that
hits the market at each `price` leaf — so the settlement check is computable only once that
evaluator is.  Rather than compile a fourth `EF`-code recursion, we reuse the total EF
rational stack machine (`efRatCompiledEval`, `LIACompiler.lean`) with the **total** quote
table `totalQuote fuel n φ := (market.quoteAtFuel fuel n φ).getD 0`.

That table is total: it reads `0` for an *unanswered* query, so on its own it cannot tell a
timeout from a genuine `0`.  The `readyAtFuel` guard — every syntactic `priceQueries` cell
of `e` has terminated — is what makes it sound: behind the guard `denoteRatComp` agrees
exactly with the partial `denoteRatWithAtFuel` (`denoteRatComp_eq`); without it, two worlds
could spuriously agree at `0` and certify a false settlement test.  This is why
`efPriceQueries_prim` (`LIACompiler.lean`) is load-bearing, not bookkeeping. -/

/-- Congruence: `denoteRatWith` depends on the price table only at its own price queries. -/
lemma EF.denoteRatWith_congr (e : EF) (ρ : List ℚ) (V₁ V₂ : ℕ → Sentence → ℚ)
    (h : ∀ q ∈ e.priceQueries, V₁ q.1 q.2 = V₂ q.1 q.2) :
    e.denoteRatWith ρ V₁ = e.denoteRatWith ρ V₂ := by
  induction e generalizing ρ with
  | price φ n => exact h (n, φ) (by simp [EF.priceQueries])
  | const q => rfl
  | add a b iha ihb =>
      have ha := iha ρ (fun q hq => h q (by
        simp only [EF.priceQueries, List.mem_append]; exact Or.inl hq))
      have hb := ihb ρ (fun q hq => h q (by
        simp only [EF.priceQueries, List.mem_append]; exact Or.inr hq))
      simp [EF.denoteRatWith, ha, hb]
  | mul a b iha ihb =>
      have ha := iha ρ (fun q hq => h q (by
        simp only [EF.priceQueries, List.mem_append]; exact Or.inl hq))
      have hb := ihb ρ (fun q hq => h q (by
        simp only [EF.priceQueries, List.mem_append]; exact Or.inr hq))
      simp [EF.denoteRatWith, ha, hb]
  | max a b iha ihb =>
      have ha := iha ρ (fun q hq => h q (by
        simp only [EF.priceQueries, List.mem_append]; exact Or.inl hq))
      have hb := ihb ρ (fun q hq => h q (by
        simp only [EF.priceQueries, List.mem_append]; exact Or.inr hq))
      simp [EF.denoteRatWith, ha, hb]
  | safeRecip a iha =>
      have ha := iha ρ (fun q hq => h q (by simpa only [EF.priceQueries] using hq))
      simp [EF.denoteRatWith, ha]
  | var i => rfl
  | letE value body ihvalue ihbody =>
      have hvalue := ihvalue ρ (fun q hq => h q (by
        simp only [EF.priceQueries, List.mem_append]; exact Or.inl hq))
      have hbody := ihbody (value.denoteRatWith ρ V₁ :: ρ)
        (fun q hq => h q (by simp only [EF.priceQueries, List.mem_append]; exact Or.inr hq))
      simp only [EF.denoteRatWith]
      rw [hbody, hvalue]

/-- Success of bounded evaluation implies every price query terminated at that clock. -/
lemma EF.denoteRatWithAtFuel_isSome_of_some {P : History}
    (market : MarketComputation P) (fuel : ℕ) (e : EF) (ρ : List ℚ) {q : ℚ}
    (h : e.denoteRatWithAtFuel market fuel ρ = some q) :
    ∀ query ∈ e.priceQueries, (market.quoteAtFuel fuel query.1 query.2).isSome := by
  induction e generalizing ρ q with
  | price φ n =>
      intro query hq
      simp only [EF.priceQueries, List.mem_singleton] at hq
      subst hq
      simp only [EF.denoteRatWithAtFuel] at h
      rw [h]; rfl
  | const c => intro query hq; simp [EF.priceQueries] at hq
  | add a b iha ihb =>
      simp only [EF.denoteRatWithAtFuel, Option.bind_eq_bind] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨qa, ha, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨qb, hb, _⟩ := h
      intro query hq
      simp only [EF.priceQueries, List.mem_append] at hq
      rcases hq with hq | hq
      · exact iha ρ ha query hq
      · exact ihb ρ hb query hq
  | mul a b iha ihb =>
      simp only [EF.denoteRatWithAtFuel, Option.bind_eq_bind] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨qa, ha, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨qb, hb, _⟩ := h
      intro query hq
      simp only [EF.priceQueries, List.mem_append] at hq
      rcases hq with hq | hq
      · exact iha ρ ha query hq
      · exact ihb ρ hb query hq
  | max a b iha ihb =>
      simp only [EF.denoteRatWithAtFuel, Option.bind_eq_bind] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨qa, ha, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨qb, hb, _⟩ := h
      intro query hq
      simp only [EF.priceQueries, List.mem_append] at hq
      rcases hq with hq | hq
      · exact iha ρ ha query hq
      · exact ihb ρ hb query hq
  | safeRecip a iha =>
      simp only [EF.denoteRatWithAtFuel, Option.bind_eq_bind] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨qa, ha, _⟩ := h
      intro query hq
      simp only [EF.priceQueries] at hq
      exact iha ρ ha query hq
  | var i => intro query hq; simp [EF.priceQueries] at hq
  | letE value body ihvalue ihbody =>
      simp only [EF.denoteRatWithAtFuel, Option.bind_eq_bind] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨qv, hv, hbody⟩ := h
      intro query hq
      simp only [EF.priceQueries, List.mem_append] at hq
      rcases hq with hq | hq
      · exact ihvalue ρ hv query hq
      · exact ihbody (qv :: ρ) hbody query hq

/-- The total quote table: substitutes `0` for an unanswered query (safe only behind the
`readyAtFuel` guard). -/
def MarketComputation.totalQuote {P : History} (market : MarketComputation P) (fuel : ℕ) :
    ℕ → Sentence → ℚ :=
  fun n φ => (market.quoteAtFuel fuel n φ).getD 0

/-- Every price query of `e` has terminated at this clock. -/
def MarketComputation.readyAtFuel {P : History} (market : MarketComputation P) (fuel : ℕ)
    (e : EF) : Bool :=
  e.priceQueries.all fun q => (market.quoteAtFuel fuel q.1 q.2).isSome

/-- Computable bounded EF evaluator: the total EF rational machine, gated by readiness. -/
def MarketComputation.denoteRatComp {P : History} (market : MarketComputation P) (fuel : ℕ)
    (e : EF) : Option ℚ :=
  if market.readyAtFuel fuel e then
    some (efRatCompiledEval market.totalQuote fuel e)
  else none

/-- **The bridge.**  The gated total machine computes exactly the partial bounded semantics
(at `ρ = []`). -/
lemma MarketComputation.denoteRatComp_eq {P : History} (market : MarketComputation P)
    (fuel : ℕ) (e : EF) :
    market.denoteRatComp fuel e = e.denoteRatWithAtFuel market fuel [] := by
  unfold MarketComputation.denoteRatComp
  by_cases hready : market.readyAtFuel fuel e
  · rw [if_pos hready]
    unfold MarketComputation.readyAtFuel at hready
    rw [List.all_eq_true] at hready
    have hready' : ∀ query ∈ e.priceQueries,
        market.quoteAtFuel fuel query.1 query.2 =
          some (market.quote query.1 (Encodable.encode query.2)) := by
      intro query hq
      have hs := hready query hq
      rw [Option.isSome_iff_exists] at hs
      obtain ⟨v, hv⟩ := hs
      rw [hv, market.quoteAtFuel_sound hv]
    rw [e.denoteRatWithAtFuel_complete market fuel [] hready', efRatCompiledEval_eq]
    congr 1
    rw [EF.denoteRat]
    apply EF.denoteRatWith_congr
    intro query hq
    unfold MarketComputation.totalQuote
    rw [hready' query hq]; rfl
  · rw [if_neg hready]
    unfold MarketComputation.readyAtFuel at hready
    rw [List.all_eq_true] at hready
    cases hd : e.denoteRatWithAtFuel market fuel [] with
    | none => rfl
    | some q =>
        exact absurd (fun query hq =>
          e.denoteRatWithAtFuel_isSome_of_some market fuel [] hd query hq) hready

/-- `readyAtFuel` is primitive recursive in `(fuel, e)` for a fixed market. -/
lemma MarketComputation.readyAtFuel_prim {P : History} (market : MarketComputation P) :
    Primrec₂ fun fuel e => market.readyAtFuel fuel e := by
  have hstep : Primrec₂ fun (p : ℕ × EF) (x : (ℕ × Sentence) × Bool) =>
      (market.quoteAtFuel p.1 x.1.1 x.1.2).isSome && x.2 :=
    (Primrec.and.comp
      (Primrec.option_isSome.comp
        ((quoteAtFuel_prim market).comp
          ((Primrec.fst.comp Primrec.fst).pair (Primrec.fst.comp Primrec.snd))))
      (Primrec.snd.comp Primrec.snd)).to₂
  have h := Primrec.list_foldr
    (f := fun p : ℕ × EF => p.2.priceQueries)
    (g := fun _ : ℕ × EF => true)
    (efPriceQueries_prim.comp Primrec.snd) (Primrec.const true) hstep
  exact h.to₂.of_eq fun fuel e => by
    simp only [MarketComputation.readyAtFuel, list_all_eq_foldr]

/-- `denoteRatComp` is primitive recursive in `(fuel, e)` for a fixed market. -/
lemma MarketComputation.denoteRatComp_prim {P : History} (market : MarketComputation P) :
    Primrec₂ fun fuel e => market.denoteRatComp fuel e := by
  have hV : Primrec fun p : ℕ × (ℕ × Sentence) =>
      market.totalQuote p.1 p.2.1 p.2.2 :=
    Primrec.option_getD.comp
      ((quoteAtFuel_prim market).comp (Primrec.fst.pair Primrec.snd)) (Primrec.const 0)
  have heval : Primrec fun p : ℕ × EF =>
      efRatCompiledEval market.totalQuote p.1 p.2 :=
    efRatCompiledEval_prim market.totalQuote hV
  have hite : Primrec fun p : ℕ × EF =>
      if market.readyAtFuel p.1 p.2 = true then
        some (efRatCompiledEval market.totalQuote p.1 p.2) else none :=
    Primrec.ite (Primrec.eq.comp
        ((market.readyAtFuel_prim).comp Primrec.fst Primrec.snd) (Primrec.const true))
      (Primrec.option_some.comp heval) (Primrec.const none)
  exact hite.to₂.of_eq fun fuel e => by
    simp only [MarketComputation.denoteRatComp]

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

lemma affineTermsRatAtFuel_sound {P : History} (market : MarketComputation P)
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

lemma affineTermsRatAtFuel_mono {P : History} (market : MarketComputation P)
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

lemma exists_fuel_affineTermsRatAtFuel {P : History} (market : MarketComputation P)
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

lemma AffineCombination.valueRatAtFuel_sound (A : AffineCombination) {P : History}
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

lemma AffineCombination.valueRatAtFuel_mono (A : AffineCombination) {P : History}
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

lemma AffineCombination.exists_fuel_valueRatAtFuel (A : AffineCombination) {P : History}
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

/-- A single fuel serving finitely many payout tables at once. -/
lemma AffineCombination.exists_fuel_valueRatAtFuel_list (A : AffineCombination)
    {P : History} (market : MarketComputation P) (ws : List (Sentence → ℚ)) :
    ∃ fuel, ∀ w ∈ ws, A.valueRatAtFuel market fuel w =
      some (A.valueRat (fun d φ => market.quote d (Encodable.encode φ)) w) := by
  induction ws with
  | nil => exact ⟨0, by simp⟩
  | cons w rest ih =>
      obtain ⟨f1, h1⟩ := A.exists_fuel_valueRatAtFuel market w
      obtain ⟨f2, h2⟩ := ih
      refine ⟨max f1 f2, fun x hx => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact A.valueRatAtFuel_mono market x (le_max_left _ _) h1
      · exact A.valueRatAtFuel_mono market x (le_max_right _ _) (h2 x hx)

/-! ### The computable value evaluator at a bit-list world

`settlementCheckAtFuel` compares `valueRatAtFuel market fuel (bitsPayoutRat l)` across the
enumerated worlds `l`.  These recast that quantity through the computable `denoteRatComp`
(so the whole check is primitive recursive), with a proved equality back to the original. -/

/-- `bitsPayoutRat` is primitive recursive. -/
lemma bitsPayoutRat_prim :
    Primrec₂ fun (l : List Bool) (φ : Sentence) => BoolPCWorld.bitsPayoutRat l φ := by
  have heval : PrimrecPred fun p : List Bool × Sentence =>
      BoolPCWorld.eval (BoolPCWorld.bitsWorld p.1) p.2 = true :=
    Primrec.eq.comp (evalBits_prim.comp Primrec.fst Primrec.snd) (Primrec.const true)
  exact (Primrec.ite heval (Primrec.const 1) (Primrec.const 0)).to₂.of_eq
    fun l φ => rfl

/-- Computable form of the affine term fold at `w := bitsPayoutRat l`, using the gated
evaluator `denoteRatComp` in place of the partial `denoteRatWithAtFuel`. -/
def affineTermsRatComp {P : History} (market : MarketComputation P) (fuel : ℕ)
    (l : List Bool) (terms : List (EF × Sentence)) : Option ℚ :=
  terms.foldr (fun p acc =>
    (market.denoteRatComp fuel p.1).bind fun cf =>
      acc.map fun t => cf * BoolPCWorld.bitsPayoutRat l p.2 + t) (some 0)

lemma affineTermsRatComp_eq {P : History} (market : MarketComputation P) (fuel : ℕ)
    (l : List Bool) (terms : List (EF × Sentence)) :
    affineTermsRatComp market fuel l terms =
      affineTermsRatAtFuel market fuel (BoolPCWorld.bitsPayoutRat l) terms := by
  induction terms with
  | nil => rfl
  | cons p rest ih =>
      rw [affineTermsRatComp, List.foldr_cons, ← affineTermsRatComp, ih,
        market.denoteRatComp_eq, affineTermsRatAtFuel]
      cases EF.denoteRatWithAtFuel market fuel p.1 [] with
      | none => rfl
      | some cf =>
          cases affineTermsRatAtFuel market fuel (BoolPCWorld.bitsPayoutRat l) rest <;> rfl

/-- Computable form of `valueRatAtFuel` at `w := bitsPayoutRat l`. -/
def valueRatCompAt {P : History} (A : AffineCombination) (market : MarketComputation P)
    (fuel : ℕ) (l : List Bool) : Option ℚ :=
  (market.denoteRatComp fuel A.const).bind fun c =>
    (affineTermsRatComp market fuel l A.terms).map fun ts => c + ts

lemma valueRatCompAt_eq {P : History} (A : AffineCombination)
    (market : MarketComputation P) (fuel : ℕ) (l : List Bool) :
    valueRatCompAt A market fuel l =
      A.valueRatAtFuel market fuel (BoolPCWorld.bitsPayoutRat l) := by
  rw [valueRatCompAt, market.denoteRatComp_eq, affineTermsRatComp_eq,
    AffineCombination.valueRatAtFuel]
  cases A.const.denoteRatWithAtFuel market fuel [] with
  | none => rfl
  | some c =>
      cases affineTermsRatAtFuel market fuel (BoolPCWorld.bitsPayoutRat l) A.terms <;> rfl

section
attribute [local irreducible] Nat.sqrt

/-- The affine term fold is primitive recursive in `((A, fuel), l)`. -/
lemma affineTermsRatComp_prim {P : History} (market : MarketComputation P) :
    Primrec fun q : (AffineCombination × ℕ) × List Bool =>
      affineTermsRatComp market q.1.2 q.2 q.1.1.terms := by
  have hcf : Primrec fun z : ((AffineCombination × ℕ) × List Bool) ×
      ((EF × Sentence) × Option ℚ) =>
      market.denoteRatComp z.1.1.2 z.2.1.1 :=
    (market.denoteRatComp_prim).comp
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
  have hbody : Primrec₂ fun (w : (((AffineCombination × ℕ) × List Bool) ×
      ((EF × Sentence) × Option ℚ)) × ℚ) (t : ℚ) =>
      w.2 * BoolPCWorld.bitsPayoutRat w.1.1.2 w.1.2.1.2 + t :=
    (ratAdd_prim.comp
      (ratMul_prim.comp (Primrec.snd.comp Primrec.fst)
        (bitsPayoutRat_prim.comp
          (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
          (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))))
      Primrec.snd).to₂
  have hmap : Primrec₂ fun (z : ((AffineCombination × ℕ) × List Bool) ×
      ((EF × Sentence) × Option ℚ)) (cf : ℚ) =>
      z.2.2.map fun t => cf * BoolPCWorld.bitsPayoutRat z.1.2 z.2.1.2 + t :=
    (Primrec.option_map (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) hbody).to₂
  have hstep : Primrec₂ fun (q : (AffineCombination × ℕ) × List Bool)
      (x : (EF × Sentence) × Option ℚ) =>
      (market.denoteRatComp q.1.2 x.1.1).bind fun cf =>
        x.2.map fun t => cf * BoolPCWorld.bitsPayoutRat q.2 x.1.2 + t :=
    (Primrec.option_bind hcf hmap).to₂
  exact Primrec.list_foldr (affineTerms_prim.comp (Primrec.fst.comp Primrec.fst))
    (Primrec.const (some 0)) hstep

/-- `valueRatCompAt` is primitive recursive in `((A, fuel), l)`. -/
lemma valueRatCompAt_prim {P : History} (market : MarketComputation P) :
    Primrec fun q : (AffineCombination × ℕ) × List Bool =>
      valueRatCompAt q.1.1 market q.1.2 q.2 := by
  have hconst : Primrec fun q : (AffineCombination × ℕ) × List Bool =>
      market.denoteRatComp q.1.2 q.1.1.const :=
    (market.denoteRatComp_prim).comp (Primrec.snd.comp Primrec.fst)
      (affineConst_prim.comp (Primrec.fst.comp Primrec.fst))
  have hmap : Primrec₂ fun (q : (AffineCombination × ℕ) × List Bool) (c : ℚ) =>
      (affineTermsRatComp market q.1.2 q.2 q.1.1.terms).map fun ts => c + ts :=
    (Primrec.option_map ((affineTermsRatComp_prim market).comp Primrec.fst)
      (ratAdd_prim.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂).to₂
  exact (Primrec.option_bind hconst hmap).of_eq fun q => rfl

end

/-! ### The bounded settlement check

The analogue of `unitMaturityCheckAtFuel` (`Calibration.lean`) for settlement, and — unlike
that one — carried through to a `Primrec`-backed code below.  It is conservative: any
timeout (of the process program or of any market call) reads as `false`, so a `true` result
always certifies the real test. -/

/-- The executable bounded settlement check.  Accepts only once the certified process
program has produced stage `j` and every market call needed by both worlds' values has
terminated. -/
def AffineCombination.settlementCheckAtFuel (A : AffineCombination)
    {P : History} {DP : DeductiveProcess}
    (market : MarketComputation P) (process : DeductiveProcessComputation DP)
    (j fuel : ℕ) : Bool :=
  match process.stageAtFuel fuel j with
  | none => false
  | some stage =>
      (allBitLists (A.settlementAtomLimit stage)).all fun l =>
        (allBitLists (A.settlementAtomLimit stage)).all fun l' =>
          !(stageSatBits stage l) || !(stageSatBits stage l') ||
            (match A.valueRatAtFuel market fuel (BoolPCWorld.bitsPayoutRat l),
                 A.valueRatAtFuel market fuel (BoolPCWorld.bitsPayoutRat l') with
             | some v, some v' => decide (v = v')
             | _, _ => false)

section
attribute [local irreducible] Nat.sqrt

/-- The bounded settlement check is primitive recursive in `(A, j, fuel)` for fixed
market and deductive-process computations.  The unbounded search for a successful fuel is
kept outside this function and is supplied by `Partrec.rfindOpt` below. -/
lemma AffineCombination.settlementCheckAtFuel_prim
    {P : History} {DP : DeductiveProcess}
    (market : MarketComputation P) (process : DeductiveProcessComputation DP) :
    Primrec fun q : AffineCombination × ℕ × ℕ =>
      q.1.settlementCheckAtFuel market process q.2.1 q.2.2 := by
  let Q := AffineCombination × ℕ × ℕ
  let S := Q × Finset Sentence
  let R := S × List Bool
  have hlimit : Primrec fun p : S => p.1.1.settlementAtomLimit p.2 :=
    settlementAtomLimit_prim.comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  have hworlds : Primrec fun p : S => allBitLists (p.1.1.settlementAtomLimit p.2) :=
    allBitLists_prim.comp hlimit
  have hsat : Primrec fun p : R => stageSatBits p.1.2 p.2 :=
    stageSatBits_prim.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  have hvalue : Primrec fun p : R =>
      valueRatCompAt p.1.1.1 market p.1.1.2.2 p.2 :=
    (valueRatCompAt_prim market).comp
      (((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))).pair
        Primrec.snd)
  have hagree : Primrec fun p : R × List Bool =>
      let v := valueRatCompAt p.1.1.1.1 market p.1.1.1.2.2 p.1.2
      let v' := valueRatCompAt p.1.1.1.1 market p.1.1.1.2.2 p.2
      v.isSome && decide (v = v') := by
    have hv : Primrec fun p : R × List Bool =>
        valueRatCompAt p.1.1.1.1 market p.1.1.1.2.2 p.1.2 :=
      hvalue.comp Primrec.fst
    have hv' : Primrec fun p : R × List Bool =>
        valueRatCompAt p.1.1.1.1 market p.1.1.1.2.2 p.2 :=
      hvalue.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)
    exact Primrec.and.comp (Primrec.option_isSome.comp hv)
      (Primrec.eq.comp hv hv').decide
  have hcondition : Primrec fun p : R × List Bool =>
      (!stageSatBits p.1.1.2 p.1.2) || (!stageSatBits p.1.1.2 p.2) ||
        (let v := valueRatCompAt p.1.1.1.1 market p.1.1.1.2.2 p.1.2
         let v' := valueRatCompAt p.1.1.1.1 market p.1.1.1.2.2 p.2
         v.isSome && decide (v = v')) := by
    have hs1 : Primrec fun p : R × List Bool => stageSatBits p.1.1.2 p.1.2 :=
      hsat.comp Primrec.fst
    have hs2 : Primrec fun p : R × List Bool => stageSatBits p.1.1.2 p.2 :=
      hsat.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)
    exact Primrec.or.comp
      (Primrec.or.comp (Primrec.not.comp hs1) (Primrec.not.comp hs2)) hagree
  have hinnerStep : Primrec₂ fun (r : R) (x : List Bool × Bool) =>
      ((!stageSatBits r.1.2 r.2) || (!stageSatBits r.1.2 x.1) ||
        (let v := valueRatCompAt r.1.1.1 market r.1.1.2.2 r.2
         let v' := valueRatCompAt r.1.1.1 market r.1.1.2.2 x.1
         v.isSome && decide (v = v'))) && x.2 :=
    (Primrec.and.comp
      (hcondition.comp (Primrec.fst.pair (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd)).to₂
  have hinner : Primrec fun r : R =>
      (allBitLists (r.1.1.1.settlementAtomLimit r.1.2)).foldr
        (fun l' acc =>
          ((!stageSatBits r.1.2 r.2) || (!stageSatBits r.1.2 l') ||
            (let v := valueRatCompAt r.1.1.1 market r.1.1.2.2 r.2
             let v' := valueRatCompAt r.1.1.1 market r.1.1.2.2 l'
             v.isSome && decide (v = v'))) && acc) true :=
    Primrec.list_foldr (hworlds.comp Primrec.fst) (Primrec.const true) hinnerStep
  have houterStep : Primrec₂ fun (s : S) (x : List Bool × Bool) =>
      ((allBitLists (s.1.1.settlementAtomLimit s.2)).foldr
        (fun l' acc =>
          ((!stageSatBits s.2 x.1) || (!stageSatBits s.2 l') ||
            (let v := valueRatCompAt s.1.1 market s.1.2.2 x.1
             let v' := valueRatCompAt s.1.1 market s.1.2.2 l'
             v.isSome && decide (v = v'))) && acc) true) && x.2 :=
    (Primrec.and.comp
      (hinner.comp (Primrec.fst.pair (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd)).to₂
  have houter : Primrec fun s : S =>
      (allBitLists (s.1.1.settlementAtomLimit s.2)).foldr
        (fun l acc =>
          ((allBitLists (s.1.1.settlementAtomLimit s.2)).foldr
            (fun l' acc' =>
              ((!stageSatBits s.2 l) || (!stageSatBits s.2 l') ||
                (let v := valueRatCompAt s.1.1 market s.1.2.2 l
                 let v' := valueRatCompAt s.1.1 market s.1.2.2 l'
                 v.isSome && decide (v = v'))) && acc') true) && acc) true :=
    Primrec.list_foldr hworlds (Primrec.const true) houterStep
  have hstage : Primrec fun q : Q => process.stageAtFuel q.2.2 q.2.1 :=
    processStageAtFuel_prim process |>.comp
      (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.snd)
  have hcompiled : Primrec fun q : Q =>
      match process.stageAtFuel q.2.2 q.2.1 with
      | none => false
      | some stage =>
          (allBitLists (q.1.settlementAtomLimit stage)).foldr
            (fun l acc =>
              ((allBitLists (q.1.settlementAtomLimit stage)).foldr
                (fun l' acc' =>
                  ((!stageSatBits stage l) || (!stageSatBits stage l') ||
                    (let v := valueRatCompAt q.1 market q.2.2 l
                     let v' := valueRatCompAt q.1 market q.2.2 l'
                     v.isSome && decide (v = v'))) && acc') true) && acc) true :=
    (Primrec.option_casesOn hstage (Primrec.const false)
      (houter.comp (Primrec.fst.pair Primrec.snd)).to₂).of_eq fun q => by
        cases process.stageAtFuel q.2.2 q.2.1 <;> rfl
  exact hcompiled.of_eq fun q => by
    unfold AffineCombination.settlementCheckAtFuel
    cases hst : process.stageAtFuel q.2.2 q.2.1 with
    | none => rfl
    | some stage =>
        simp only
        rw [list_all_eq_foldr]
        apply congrArg (fun f : List Bool → Bool → Bool =>
          List.foldr f true (allBitLists (q.1.settlementAtomLimit stage)))
        funext l acc
        rw [list_all_eq_foldr]
        apply congrArg₂ (fun x y => x && y) _ rfl
        apply congrArg (fun f : List Bool → Bool → Bool =>
          List.foldr f true (allBitLists (q.1.settlementAtomLimit stage)))
        funext l' acc'
        rw [valueRatCompAt_eq, valueRatCompAt_eq]
        cases hs : stageSatBits stage l <;>
          cases hs' : stageSatBits stage l' <;>
          cases hv : q.1.valueRatAtFuel market q.2.2 (BoolPCWorld.bitsPayoutRat l) <;>
          cases hv' : q.1.valueRatAtFuel market q.2.2 (BoolPCWorld.bitsPayoutRat l') <;>
          simp

end

lemma AffineCombination.settlementCheckAtFuel_sound (A : AffineCombination)
    {P : History} {DP : DeductiveProcess}
    (market : MarketComputation P) (process : DeductiveProcessComputation DP)
    {j fuel : ℕ}
    (h : A.settlementCheckAtFuel market process j fuel = true) :
    A.SettlementTestBool (fun d φ => market.quote d (Encodable.encode φ)) (DP.D j) = true := by
  unfold AffineCombination.settlementCheckAtFuel at h
  cases hstage : process.stageAtFuel fuel j with
  | none => rw [hstage] at h; exact absurd h (by simp)
  | some stage =>
      rw [hstage] at h
      obtain rfl : stage = DP.D j := process.stageAtFuel_sound hstage
      rw [List.all_eq_true] at h
      rw [AffineCombination.SettlementTestBool, List.all_eq_true]
      intro l hl
      rw [List.all_eq_true]
      intro l' hl'
      have hb := List.all_eq_true.mp (h l hl) l' hl'
      -- Both worlds satisfy the stage, or the disjunction is already discharged.
      cases ha : stageSatBits (DP.D j) l
      · simp
      cases ha' : stageSatBits (DP.D j) l'
      · simp
      rw [ha, ha'] at hb
      simp only [Bool.not_true, Bool.false_or] at hb ⊢
      -- The check's match certifies both market evaluations terminated and agreed.
      cases hv : A.valueRatAtFuel market fuel (BoolPCWorld.bitsPayoutRat l) with
      | none => rw [hv] at hb; exact absurd hb (by simp)
      | some v =>
          cases hv' : A.valueRatAtFuel market fuel (BoolPCWorld.bitsPayoutRat l') with
          | none => rw [hv, hv'] at hb; exact absurd hb (by simp)
          | some v' =>
              rw [hv, hv'] at hb
              simp only [decide_eq_true_iff] at hb ⊢
              rw [← A.valueRatAtFuel_sound market fuel _ hv,
                ← A.valueRatAtFuel_sound market fuel _ hv']
              exact hb

lemma AffineCombination.settlementCheckAtFuel_complete (A : AffineCombination)
    {P : History} {DP : DeductiveProcess}
    (market : MarketComputation P) (process : DeductiveProcessComputation DP)
    (j : ℕ)
    (h : A.SettlementTestBool (fun d φ => market.quote d (Encodable.encode φ))
      (DP.D j) = true) :
    ∃ fuel, A.settlementCheckAtFuel market process j fuel = true := by
  obtain ⟨f0, h0⟩ := process.stageAtFuel_complete j
  obtain ⟨f1, h1⟩ := A.exists_fuel_valueRatAtFuel_list market
    ((allBitLists (A.settlementAtomLimit (DP.D j))).map BoolPCWorld.bitsPayoutRat)
  refine ⟨max f0 f1, ?_⟩
  unfold AffineCombination.settlementCheckAtFuel
  rw [process.stageAtFuel_mono (le_max_left _ _) h0]
  rw [AffineCombination.SettlementTestBool, List.all_eq_true] at h
  rw [List.all_eq_true]
  intro l hl
  rw [List.all_eq_true]
  intro l' hl'
  have hb := List.all_eq_true.mp (h l hl) l' hl'
  -- Both payout tables are in the list the common fuel was chosen for.
  have hv := A.valueRatAtFuel_mono market (fuel := f1) (fuel' := max f0 f1)
    (BoolPCWorld.bitsPayoutRat l) (le_max_right f0 f1)
    (h1 _ (List.mem_map_of_mem hl))
  have hv' := A.valueRatAtFuel_mono market (fuel := f1) (fuel' := max f0 f1)
    (BoolPCWorld.bitsPayoutRat l') (le_max_right f0 f1)
    (h1 _ (List.mem_map_of_mem hl'))
  rw [hv, hv']
  exact hb

/-! ### Extracting the settlement checker code -/

/-- Market and deductive-process computations determine a concrete code semi-deciding the
named settlement predicate for every polynomial affine family.  The only unbounded operation
is `rfindOpt` over fuel; soundness and completeness come from the bounded check above. -/
noncomputable def SettlementChecker.ofComputations
    {As : ℕ → AffineCombination} {P : History} {DP : DeductiveProcess}
    (hpoly : AffineCombination.PolySequence As)
    (market : MarketComputation P) (process : DeductiveProcessComputation DP) :
    SettlementChecker As (fun d φ => market.quote d (Encodable.encode φ)) DP := by
  have hAs : Primrec As := hpoly.primrec
  have hcheck : Primrec₂ fun (z fuel : ℕ) =>
      (As z.unpair.1).settlementCheckAtFuel market process z.unpair.2 fuel := by
    have hinput : Primrec fun p : ℕ × ℕ =>
        (As p.1.unpair.1, p.1.unpair.2, p.2) :=
      (hAs.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst))).pair
        ((Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)).pair Primrec.snd)
    exact ((AffineCombination.settlementCheckAtFuel_prim market process).comp hinput).to₂
  let guard : ℕ → ℕ → Option ℕ := fun z fuel =>
    if (As z.unpair.1).settlementCheckAtFuel market process z.unpair.2 fuel then
      some 1
    else
      none
  have hguard : Computable₂ guard := by
    have hp : Primrec fun p : ℕ × ℕ =>
        if (As p.1.unpair.1).settlementCheckAtFuel market process p.1.unpair.2 p.2 then
          some 1
        else
          none := by
      exact Primrec.ite
        (Primrec.eq.comp hcheck (Primrec.const true))
        (Primrec.const (some 1)) (Primrec.const (none : Option ℕ))
    exact hp.to₂.to_comp
  have hpart : Partrec fun z => Nat.rfindOpt (guard z) :=
    Partrec.rfindOpt hguard
  have hnat : Nat.Partrec fun z => Nat.rfindOpt (guard z) :=
    Partrec.nat_iff.mp hpart
  let code := Classical.choose (Nat.Partrec.Code.exists_code.mp hnat)
  have hcode : Nat.Partrec.Code.eval code = fun z => Nat.rfindOpt (guard z) :=
    Classical.choose_spec (Nat.Partrec.Code.exists_code.mp hnat)
  refine ⟨code, fun i j => ?_⟩
  constructor
  · rintro ⟨fuel, haccept⟩
    have hevaln : Nat.Partrec.Code.evaln fuel code (Nat.pair i j) = some 1 := by
      cases he : Nat.Partrec.Code.evaln fuel code (Nat.pair i j) with
      | none =>
          simp [acceptsWithin, codeEvalnNat, he] at haccept
      | some out =>
          simp [acceptsWithin, codeEvalnNat, he] at haccept
          obtain rfl : out = 1 := by omega
          rfl
    have hmem : 1 ∈ Nat.rfindOpt (guard (Nat.pair i j)) := by
      have : 1 ∈ Nat.Partrec.Code.eval code (Nat.pair i j) :=
        Nat.Partrec.Code.evaln_sound hevaln
      rw [hcode] at this
      exact this
    obtain ⟨fuel', hfuel'⟩ := Nat.rfindOpt_spec hmem
    have hcheckTrue :
        (As i).settlementCheckAtFuel market process j fuel' = true := by
      simpa [guard] using hfuel'
    exact (As i).settlementCheckAtFuel_sound market process hcheckTrue
  · intro htest
    obtain ⟨fuel, hfuel⟩ :=
      (As i).settlementCheckAtFuel_complete market process j htest
    have hdom : (Nat.rfindOpt (guard (Nat.pair i j))).Dom := by
      rw [Nat.rfindOpt_dom]
      exact ⟨fuel, 1, by simp [guard, hfuel]⟩
    have hone : 1 ∈ Nat.rfindOpt (guard (Nat.pair i j)) := by
      have hout := Part.get_mem hdom
      obtain ⟨fuel', hfuel'⟩ := Nat.rfindOpt_spec hout
      have houtEq : (Nat.rfindOpt (guard (Nat.pair i j))).get hdom = 1 := by
        have hp : (As i).settlementCheckAtFuel market process j fuel' = true ∧
            1 = (Nat.rfindOpt (guard (Nat.pair i j))).get hdom := by
          simpa [guard] using hfuel'
        exact hp.2.symm
      rw [houtEq] at hout
      exact hout
    have hmem : 1 ∈ Nat.Partrec.Code.eval code (Nat.pair i j) := by
      rw [hcode]
      exact hone
    obtain ⟨fuel', hevaln⟩ := Nat.Partrec.Code.evaln_complete.mp hmem
    refine ⟨fuel', ?_⟩
    change Nat.Partrec.Code.evaln fuel' code (Nat.pair i j) = some 1 at hevaln
    simp [acceptsWithin, codeEvalnNat, hevaln]

/-- The patient settlement clock with its checker constructed from the supplied market and
deductive-process programs.  No computability bridge or checker remains as a hypothesis. -/
noncomputable def PatientSettlementClock.ofComputations
    {As : ℕ → AffineCombination} {P : History} {DP : DeductiveProcess} {truth : ℕ → ℝ}
    (hpoly : AffineCombination.PolySequence As)
    (market : MarketComputation P) (process : DeductiveProcessComputation DP)
    (hdet : AffineCombination.DeterminedViaTheory As P DP truth)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (f : DeferralFunction) : PatientSettlementClock As P DP truth f :=
  PatientSettlementClock.ofChecker
    (SettlementChecker.ofComputations hpoly market process) hdet market.quote_exact hworld f

end SettlementCompile

/-! ## M7-PREFIX-PATCH: polynomial flat-token transduction -/

namespace PrefixPatchCompile

-- Deep `PolyFueled`/segment compositions carry nested `Primcodable` products.  Prevent
-- elaboration from reducing their `Nat.unpair` implementation through `Nat.sqrt`.
attribute [local irreducible] Nat.sqrt

/-- The polynomial clock carried by an `EfficientlyComputableTok` certificate. -/
def ecClock (a k n : ℕ) : ℕ := a * (n + 1) ^ k + a

/-- The standard polynomial evaluator clock is itself polynomially emitted. -/
lemma ecClock_polyFueled (a k : ℕ) :
    ∃ c, PolyFueled c (ecClock a k) := by
  obtain ⟨cmul, hmul⟩ := mul_polyFueled
  obtain ⟨cadd, hadd⟩ := addc_polyFueled
  have hpow : ∀ d : ℕ, ∃ c, PolyFueled c (fun n => (n + 1) ^ d) := by
    intro d
    induction d with
    | zero => exact ⟨_, PolyFueled.const 1⟩
    | succ d ih =>
        obtain ⟨cpow, hpow⟩ := ih
        refine ⟨_, (hmul.comp (hpow.pair PolyFueled.id.succ_comp)).of_eq (fun n => ?_)⟩
        simp [pow_succ]
  obtain ⟨cpow, hpow⟩ := hpow k
  have hscaled := hmul.comp ((PolyFueled.const a).pair hpow)
  refine ⟨_, (hadd.comp (hscaled.pair (PolyFueled.const a))).of_eq (fun n => ?_)⟩
  simp [ecClock]

/-- Actual clamped length requested by one clocked trader program. -/
def clockedRawLength (lengthCode : Nat.Partrec.Code) (a k n : ℕ) : ℕ :=
  min (Nat.pred (codeEvalnNat lengthCode (Nat.pair (ecClock a k n) n)))
    (ecClock a k n)

/-- Total source-token oracle of one clocked trader program. -/
def clockedRawToken (tokenCode : Nat.Partrec.Code) (a k z : ℕ) : ℕ :=
  Nat.pred (codeEvalnNat tokenCode
    (Nat.pair (ecClock a k z.unpair.1) z))

private lemma clockedRawLength_polyFueled
    (lengthCode : Nat.Partrec.Code) (a k : ℕ) :
    ∃ c, PolyFueled c (clockedRawLength lengthCode a k) := by
  obtain ⟨csim, hsim⟩ := codeEvalnNat_polyFueled lengthCode
  obtain ⟨cclock, hclock⟩ := ecClock_polyFueled a k
  have hrun := hsim.comp (hclock.pair PolyFueled.id)
  have hrequested := predc_polyFueled.comp hrun
  have hgap := subc_polyFueled.comp (hrequested.pair hclock)
  refine ⟨_, (subc_polyFueled.comp (hrequested.pair hgap)).of_eq (fun n => ?_)⟩
  simp only [Nat.unpair_pair, Nat.pred_eq_sub_one]
  unfold clockedRawLength
  let requested := codeEvalnNat lengthCode (Nat.pair (ecClock a k n) n) - 1
  let clock := ecClock a k n
  change requested - (requested - clock) = min requested clock
  by_cases h : requested ≤ clock
  · rw [Nat.sub_eq_zero_of_le h, Nat.sub_zero, min_eq_left h]
  · have h' : clock ≤ requested := Nat.le_of_lt (Nat.lt_of_not_ge h)
    rw [Nat.sub_sub_self h', min_eq_right h']

private lemma clockedRawToken_polyFueled
    (tokenCode : Nat.Partrec.Code) (a k : ℕ) :
    ∃ c, PolyFueled c (clockedRawToken tokenCode a k) := by
  obtain ⟨csim, hsim⟩ := codeEvalnNat_polyFueled tokenCode
  obtain ⟨cclock, hclock⟩ := ecClock_polyFueled a k
  refine ⟨_, (predc_polyFueled.comp
    (hsim.comp ((hclock.comp PolyFueled.left).pair PolyFueled.id))).of_eq (fun z => ?_)⟩
  simp [clockedRawToken]

lemma clockedRawLength_eq (lengthCode tokenCode : Nat.Partrec.Code)
    (a k n : ℕ) :
    (clockedTokens lengthCode tokenCode (ecClock a k n) n).length =
      clockedRawLength lengthCode a k n := by
  unfold clockedTokens clockedRawLength codeEvalnNat
  simp only [Nat.unpair_pair]
  cases h : Nat.Partrec.Code.evaln (ecClock a k n) lengthCode n <;> simp

lemma clockedRawToken_eq (lengthCode tokenCode : Nat.Partrec.Code)
    (a k n i : ℕ)
    (hi : i < (clockedTokens lengthCode tokenCode (ecClock a k n) n).length) :
    clockedRawToken tokenCode a k (Nat.pair n i) =
      (clockedTokens lengthCode tokenCode (ecClock a k n) n).getD i 0 := by
  unfold clockedRawToken clockedTokens
  simp only [Nat.unpair_pair]
  cases hl : Nat.Partrec.Code.evaln (ecClock a k n) lengthCode n with
  | none =>
      have hi' : i < 0 := by simp [clockedTokens, hl] at hi
      omega
  | some length =>
      have hi' : i < min length (ecClock a k n) := by
        simpa [clockedTokens, hl] using hi
      have hiList : i < (List.ofFn fun j : Fin (min length (ecClock a k n)) =>
          (Nat.Partrec.Code.evaln (ecClock a k n) tokenCode (Nat.pair n j)).getD 0).length := by
        simpa using hi'
      rw [List.getD_eq_getElem (l := List.ofFn fun j : Fin (min length (ecClock a k n)) =>
        (Nat.Partrec.Code.evaln (ecClock a k n) tokenCode (Nat.pair n j)).getD 0)
        (d := 0) hiList]
      simp only [List.getElem_ofFn]
      unfold codeEvalnNat
      simp only [Nat.unpair_pair]
      cases ht : Nat.Partrec.Code.evaln (ecClock a k n) tokenCode (Nat.pair n i) <;>
        simp

/-- Every raw clocked token list is itself a polynomial segment stream. -/
lemma clockedTokens_polySegStream (lengthCode tokenCode : Nat.Partrec.Code)
    (a k : ℕ) :
    PolySegStream (fun n => clockedTokens lengthCode tokenCode (ecClock a k n) n) := by
  obtain ⟨ct, ht⟩ := clockedRawToken_polyFueled tokenCode a k
  obtain ⟨cl, hl⟩ := clockedRawLength_polyFueled lengthCode a k
  exact ⟨ct, cl, clockedRawToken tokenCode a k, clockedRawLength lengthCode a k,
    ht, hl, fun n => clockedRawLength_eq lengthCode tokenCode a k n,
    fun n i hi => clockedRawToken_eq lengthCode tokenCode a k n i
      (by rwa [clockedRawLength_eq lengthCode tokenCode a k n])⟩

/-! ### Polynomial parser control -/

/-- Numeric form of the small parser-control transition. -/
def freezeNextNat (z : ℕ) : ℕ :=
  let mode := z.unpair.1.unpair.1
  let token := z.unpair.2
  if mode = 0 then
    if token = 0 then Nat.pair 1 0
    else if token = 1 then Nat.pair 3 0
    else if token = 6 then Nat.pair 4 0
    else if token = 7 then Nat.pair 5 0
    else 0
  else if mode = 1 then Nat.pair 2 token
  else 0

private lemma freezeNextNat_eq (state : EF.FreezeTokenState) (token : ℕ) :
    freezeNextNat (Nat.pair (Nat.pair state.1 state.2) token) =
      Nat.pair (EF.freezeTokenNext state token).1 (EF.freezeTokenNext state token).2 := by
  rcases state with ⟨mode, pending⟩
  simp only [freezeNextNat, Nat.unpair_pair]
  cases mode with
  | zero =>
      simp only [EF.freezeTokenNext]
      by_cases h0 : token = 0
      · simp [h0]
      by_cases h1 : token = 1
      · simp [h1]
      by_cases h6 : token = 6
      · simp [h6]
      by_cases h7 : token = 7
      · simp [h7]
      · simp [h0, h1, h6, h7]
        rfl
  | succ mode =>
      cases mode with
      | zero => simp [EF.freezeTokenNext]
      | succ mode =>
          simp [EF.freezeTokenNext]
          rfl

/-- Closure of polynomial fuel under a zero-test branch. -/
lemma polyFueled_ifZero {ct c₀ c₁ : Nat.Partrec.Code}
    {test f₀ f₁ : ℕ → ℕ} (ht : PolyFueled ct test)
    (h₀ : PolyFueled c₀ f₀) (h₁ : PolyFueled c₁ f₁) :
    ∃ c, PolyFueled c (fun z => if test z = 0 then f₀ z else f₁ z) := by
  exact ⟨_, (ifzSel_polyFueled.comp ((h₀.pair h₁).pair ht)).of_eq (fun z => by
    simp only [ifzSelFn, Nat.unpair_pair])⟩

private lemma freezeNextNat_polyFueled : ∃ c, PolyFueled c freezeNextNat := by
  have hmode := PolyFueled.left.comp PolyFueled.left
  have htoken := PolyFueled.right
  obtain ⟨eq0, heq0⟩ := polyFueled_eqConst htoken 0
  obtain ⟨eq1, heq1⟩ := polyFueled_eqConst htoken 1
  obtain ⟨eq6, heq6⟩ := polyFueled_eqConst htoken 6
  obtain ⟨eq7, heq7⟩ := polyFueled_eqConst htoken 7
  obtain ⟨out7, hout7⟩ := polyFueled_ifZero heq7 (PolyFueled.const 0)
    (PolyFueled.const (Nat.pair 5 0))
  obtain ⟨out6, hout6⟩ := polyFueled_ifZero heq6 hout7
    (PolyFueled.const (Nat.pair 4 0))
  obtain ⟨out1, hout1⟩ := polyFueled_ifZero heq1 hout6
    (PolyFueled.const (Nat.pair 3 0))
  obtain ⟨out0, hout0⟩ := polyFueled_ifZero heq0 hout1
    (PolyFueled.const (Nat.pair 1 0))
  have hmode1 : PolyFueled ((Nat.Partrec.Code.const 2).pair Nat.Partrec.Code.right)
      (fun z => Nat.pair 2 z.unpair.2) :=
    (PolyFueled.const 2).pair PolyFueled.right
  obtain ⟨modeEq1, hmodeEq1⟩ := polyFueled_eqConst hmode 1
  obtain ⟨other, hother⟩ := polyFueled_ifZero hmodeEq1 (PolyFueled.const 0) hmode1
  obtain ⟨modeEq0, hmodeEq0⟩ := polyFueled_eqConst hmode 0
  obtain ⟨result, hresult⟩ := polyFueled_ifZero hmodeEq0 hother hout0
  refine ⟨result, hresult.of_eq (fun z => ?_)⟩
  simp only [freezeNextNat]
  by_cases hm0 : z.unpair.1.unpair.1 = 0
  · simp [hm0]
  · by_cases hm1 : z.unpair.1.unpair.1 = 1 <;> simp [hm0, hm1]

private lemma freezeTokenNext_mode_le (state : EF.FreezeTokenState) (token : ℕ) :
    (EF.freezeTokenNext state token).1 ≤ 5 := by
  rcases state with ⟨mode, pending⟩
  cases mode with
  | zero =>
      by_cases h0 : token = 0 <;> by_cases h1 : token = 1 <;>
        by_cases h6 : token = 6 <;> by_cases h7 : token = 7 <;>
        simp [EF.freezeTokenNext, h0, h1, h6, h7]
  | succ mode =>
      cases mode <;> simp [EF.freezeTokenNext]

private lemma freezeTokenNext_pending (state : EF.FreezeTokenState) (token : ℕ) :
    (EF.freezeTokenNext state token).2 = 0 ∨
      (EF.freezeTokenNext state token).2 = token := by
  rcases state with ⟨mode, pending⟩
  cases mode with
  | zero =>
      by_cases h0 : token = 0 <;> by_cases h1 : token = 1 <;>
        by_cases h6 : token = 6 <;> by_cases h7 : token = 7 <;>
        simp [EF.freezeTokenNext, h0, h1, h6, h7]
  | succ mode =>
      cases mode <;> simp [EF.freezeTokenNext]

private lemma freezeTokenControlAt_mode_le (tokenFn : ℕ → ℕ) (n j : ℕ) :
    (EF.freezeTokenControlAt tokenFn n j).1 ≤ 5 := by
  cases j with
  | zero => simp [EF.freezeTokenControlAt]
  | succ j =>
      simp only [EF.freezeTokenControlAt]
      exact freezeTokenNext_mode_le _ _

private lemma freezeTokenControlAt_pending (tokenFn : ℕ → ℕ) (n j : ℕ) :
    (EF.freezeTokenControlAt tokenFn n j).2 = 0 ∨
      ∃ i < j, (EF.freezeTokenControlAt tokenFn n j).2 = tokenFn (Nat.pair n i) := by
  cases j with
  | zero => simp [EF.freezeTokenControlAt]
  | succ j =>
      rcases freezeTokenNext_pending (EF.freezeTokenControlAt tokenFn n j)
          (tokenFn (Nat.pair n j)) with h | h
      · exact Or.inl (by simpa only [EF.freezeTokenControlAt] using h)
      · exact Or.inr ⟨j, Nat.lt_succ_self j,
          by simpa only [EF.freezeTokenControlAt] using h⟩

/-- Encoded parser control before the token index carried in `z = ⟨n,j⟩`. -/
def freezeControlNat (tokenFn : ℕ → ℕ) (z : ℕ) : ℕ :=
  let state := EF.freezeTokenControlAt tokenFn z.unpair.1 z.unpair.2
  Nat.pair state.1 state.2

/-- The parser control before a token of a polynomial stream is itself polynomially fueled. -/
lemma freezeControlNat_polyFueled {ct : Nat.Partrec.Code} {tokenFn : ℕ → ℕ}
    (htoken : PolyFueled ct tokenFn) :
    ∃ c, PolyFueled c (freezeControlNat tokenFn) := by
  obtain ⟨cnext, hnext⟩ := freezeNextNat_polyFueled
  have hn := PolyFueled.left
  have hj := PolyFueled.left.comp PolyFueled.right
  have hprev := PolyFueled.right.comp PolyFueled.right
  have hsource := htoken.comp (hn.pair hj)
  have hstep := hnext.comp (hprev.pair hsource)
  obtain ⟨_, _, htokenBounded, _⟩ := htoken
  obtain ⟨a, k, hbound⟩ := htokenBounded
  have hmajor : IsPolyBounded (fun m => Nat.pair 5 (a * (m + 1) ^ k + a)) :=
    ((IsPolyBounded.linear 5).of_le (fun _ => by omega)).pair
      ⟨a, k, fun _ => le_rfl⟩
  have hstate : IsPolyBounded (fun m => freezeControlNat tokenFn m) :=
    hmajor.of_le (fun m => by
      simp only [freezeControlNat]
      have hmode := freezeTokenControlAt_mode_le tokenFn m.unpair.1 m.unpair.2
      rcases freezeTokenControlAt_pending tokenFn m.unpair.1 m.unpair.2 with hpending | hpending
      · rw [hpending]
        exact (pair_le_pair_left' 0 hmode).trans
          (pair_le_pair_right' 5 (Nat.zero_le _))
      · obtain ⟨i, hi, hpending⟩ := hpending
        rw [hpending]
        have hpair : Nat.pair m.unpair.1 i ≤ m := by
          calc Nat.pair m.unpair.1 i ≤ Nat.pair m.unpair.1 m.unpair.2 :=
              pair_le_pair_right' _ (le_of_lt hi)
            _ = m := Nat.pair_unpair m
        have htok : tokenFn (Nat.pair m.unpair.1 i) ≤ a * (m + 1) ^ k + a :=
          (hbound _).trans (by gcongr)
        exact (pair_le_pair_right' _ htok).trans (pair_le_pair_left' _ hmode))
  have hstate' : IsPolyBounded (fun m =>
      freezeControlNat tokenFn (Nat.pair m.unpair.1 m.unpair.2)) :=
    hstate.of_le (fun m => by rw [Nat.pair_unpair])
  refine ⟨_, (PolyFueled.prec (PolyFueled.const 0) hstep
    (st := fun n j => freezeControlNat tokenFn (Nat.pair n j)) (fun n => ?_)
    (fun n j => ?_) hstate').of_eq (fun z => ?_)⟩
  · simp only [freezeControlNat, Nat.unpair_pair, EF.freezeTokenControlAt]
    rfl
  · simp only [freezeControlNat, Nat.unpair_pair, EF.freezeTokenControlAt]
    exact (freezeNextNat_eq (EF.freezeTokenControlAt tokenFn n j)
      (tokenFn (Nat.pair n j))).symm
  · rw [Nat.pair_unpair]

/-! ### Variable-width freeze emission -/

/-- A polynomial quote-code lookup makes the parser-transparent prefix rewrite polynomial on
every polynomial raw source stream. -/
lemma freezeTokenRun_polySegStream {source : ℕ → List ℕ}
    (hsource : PolySegStream source) (quoteCode : ℕ → ℕ → ℕ) (cutoff : ℕ)
    {cq : Nat.Partrec.Code}
    (hquote : PolyFueled cq (fun z => quoteCode z.unpair.1 z.unpair.2)) :
    PolySegStream (fun n =>
      (EF.freezeTokenRun quoteCode cutoff (0, 0) (source n)).2) := by
  obtain ⟨ct, cl, tokenFn, lenFn, htoken, hlen, hslen, hget⟩ := hsource
  obtain ⟨ccontrol, hcontrol⟩ := freezeControlNat_polyFueled htoken
  have hmode := PolyFueled.left.comp hcontrol
  have hpending := PolyFueled.right.comp hcontrol
  have hquoteAt := hquote.comp (htoken.pair hpending)
  have hquoteAt' : PolyFueled _ (fun z =>
      quoteCode (tokenFn z) (freezeControlNat tokenFn z).unpair.2) :=
    hquoteAt.of_eq (fun z => by simp only [Nat.unpair_pair])
  have hshort : PolySegStream (fun z => [tokenFn z]) :=
    PolySegStream.ofTokenStream (PolyTokenStream.polyTok htoken)
  have hlong : PolySegStream (fun z => [tokenFn z, 1,
      quoteCode (tokenFn z) (freezeControlNat tokenFn z).unpair.2, 8]) := by
    exact PolySegStream.ofTokenStream
      (((PolyTokenStream.polyTok htoken).append (PolyTokenStream.const 1)).append
        ((PolyTokenStream.polyTok hquoteAt').append (PolyTokenStream.const 8)))
  obtain ⟨cmode, hmodeEq⟩ := polyFueled_eqConst hmode 2
  have hdayGap := subc_polyFueled.comp ((PolyFueled.const cutoff).pair htoken)
  have hdayGap' : PolyFueled _ (fun z => cutoff - tokenFn z) :=
    hdayGap.of_eq (fun z => by simp only [Nat.unpair_pair])
  have hday : PolySegStream (fun z =>
      if cutoff - tokenFn z = 0 then [tokenFn z]
      else [tokenFn z, 1,
        quoteCode (tokenFn z) (freezeControlNat tokenFn z).unpair.2, 8]) :=
    hshort.ifZero hlong hdayGap'
  have hsegmentRaw : PolySegStream (fun z =>
      if (if (freezeControlNat tokenFn z).unpair.1 = 2 then 1 else 0) = 0 then
        [tokenFn z]
      else if cutoff - tokenFn z = 0 then [tokenFn z]
      else [tokenFn z, 1,
        quoteCode (tokenFn z) (freezeControlNat tokenFn z).unpair.2, 8]) :=
    hshort.ifZero hday hmodeEq
  have hsegment : PolySegStream (fun z =>
      EF.freezeTokenEmit quoteCode cutoff
        ((freezeControlNat tokenFn z).unpair.1,
          (freezeControlNat tokenFn z).unpair.2) (tokenFn z)) :=
    hsegmentRaw.of_eq (fun z => by
      simp only [EF.freezeTokenEmit]
      by_cases hm : (freezeControlNat tokenFn z).unpair.1 = 2
      · by_cases hd : tokenFn z < cutoff
        · have hgap : cutoff - tokenFn z ≠ 0 := by omega
          simp [hm, hd, hgap]
        · have hgap : cutoff - tokenFn z = 0 := Nat.sub_eq_zero_of_le (by omega)
          simp [hm, hd, hgap]
      · simp [hm])
  have hconcat := hsegment.concatVar hlen
  refine hconcat.of_eq (fun n => ?_)
  have hsourceEq : source n =
      (List.range (lenFn n)).map (fun j => tokenFn (Nat.pair n j)) := by
    apply List.ext_getElem
    · simp [hslen n]
    · intro i hleft hright
      rw [List.getElem_map]
      simp only [List.getElem_range]
      rw [hget n i (by simpa [hslen n] using hleft)]
      exact (List.getD_eq_getElem (l := source n) (d := 0) hleft).symm
  have hrun := congrArg Prod.snd
    (EF.freezeTokenRun_range quoteCode cutoff tokenFn n (lenFn n))
  simp only at hrun
  rw [hsourceEq]
  simpa [freezeControlNat] using hrun.symm

/-- Generic compiler theorem behind the concrete prefix patch: a polynomial encoded quote
lookup closes the administrative freeze under `EfficientlyComputableTok`. -/
lemma freezeBefore_preserves_ec
    (quote : ℕ → Sentence → ℚ) (quoteCode : ℕ → ℕ → ℕ) (cutoff : ℕ)
    (hquoteExact : ∀ day code φ, Encodable.decode (α := Sentence) code = some φ →
      quoteCode day code = Encodable.encode (quote day φ))
    {cq : Nat.Partrec.Code}
    (hquotePoly : PolyFueled cq (fun z => quoteCode z.unpair.1 z.unpair.2))
    (Tr : Trader) (hTr : EfficientlyComputableTok Tr) :
    EfficientlyComputableTok (Tr.freezeBefore quote cutoff) := by
  obtain ⟨lengthCode, tokenCode, a, k, hcert⟩ := hTr
  let raw : ℕ → List ℕ := fun n =>
    clockedTokens lengthCode tokenCode (ecClock a k n) n
  have hraw : PolySegStream raw :=
    clockedTokens_polySegStream lengthCode tokenCode a k
  have hfrozen : PolySegStream (fun n =>
      (EF.freezeTokenRun quoteCode cutoff (0, 0) (raw n)).2) :=
    freezeTokenRun_polySegStream hraw quoteCode cutoff hquotePoly
  apply hfrozen.ecTok (Tr.freezeBefore quote cutoff)
  intro n
  have hcomm := EF.strategyOfTokens_freezeTokenRun_trades quote quoteCode cutoff n
    hquoteExact (raw n)
  simp only at hcomm
  have horig : strategyOfTokens n (raw n) = Tr.strat n := by
    have hs := congrFun (congrArg Trader.strat hcert) n
    exact hs
  rw [congrArg Strategy.trades horig] at hcomm
  have htrades :
      (strategyOfTokens n
        (EF.freezeTokenRun quoteCode cutoff (0, 0) (raw n)).2).trades =
        ((Tr.freezeBefore quote cutoff).strat n).trades := by
    simpa [Trader.freezeBefore, Strategy.freezeBefore] using hcomm
  cases hleft : strategyOfTokens n
      (EF.freezeTokenRun quoteCode cutoff (0, 0) (raw n)).2 with
  | mk leftTrades leftRank =>
      cases hright : (Tr.freezeBefore quote cutoff).strat n with
      | mk rightTrades rightRank =>
          simp only [hleft, hright] at htrades ⊢
          subst rightTrades
          rfl

/-! ### Finite LIA prefix lookup -/

/-- Decide whether an arbitrary raw sentence token decodes to one fixed sentence.  Unlike
comparison with `Encodable.encode`, this accepts every noncanonical token accepted by the
Foundation decoder. -/
def sentenceMatches : Sentence → ℕ → ℕ
  | ⊥, code =>
      if code = 0 then 0
      else if code.pred.unpair.1 = 0 then 1 else 0
  | .atom a, code =>
      if code = 0 then 0
      else if code.pred.unpair.1 = 1 then
        if code.pred.unpair.2 = a then 1 else 0
      else 0
  | φ 🡒 ψ, code =>
      if code = 0 then 0
      else if code.pred.unpair.1 = 2 then
        sentenceMatches φ code.pred.unpair.2.unpair.1 *
          sentenceMatches ψ code.pred.unpair.2.unpair.2
      else 0
  | φ ⋏ ψ, code =>
      if code = 0 then 0
      else if code.pred.unpair.1 = 3 then
        sentenceMatches φ code.pred.unpair.2.unpair.1 *
          sentenceMatches ψ code.pred.unpair.2.unpair.2
      else 0
  | φ ⋎ ψ, code =>
      if code = 0 then 0
      else if code.pred.unpair.1 = 4 then
        sentenceMatches φ code.pred.unpair.2.unpair.1 *
          sentenceMatches ψ code.pred.unpair.2.unpair.2
      else 0

lemma sentenceMatches_eq_one_iff (target : Sentence) (code : ℕ) :
    sentenceMatches target code = 1 ↔
      Encodable.decode (α := Sentence) code = some target := by
  induction target using LO.Propositional.Formula.rec' generalizing code with
  | hfalsum =>
      cases code with
      | zero => simp [sentenceMatches, LO.Propositional.Formula.instEncodable,
          LO.Propositional.Formula.ofNat]
      | succ e =>
          rcases htag : e.unpair.1 with _ | tag
          · simp [sentenceMatches, LO.Propositional.Formula.instEncodable,
              LO.Propositional.Formula.ofNat, htag]
          · rcases tag with _ | _ | _ | _ | tag <;>
              simp [sentenceMatches, LO.Propositional.Formula.instEncodable,
                LO.Propositional.Formula.ofNat, htag, Option.bind_eq_some_iff]
  | hatom a =>
      cases code with
      | zero => simp [sentenceMatches, LO.Propositional.Formula.instEncodable,
          LO.Propositional.Formula.ofNat]
      | succ e =>
          rcases htag : e.unpair.1 with _ | _ | tag
          · simp [sentenceMatches, LO.Propositional.Formula.instEncodable,
              LO.Propositional.Formula.ofNat, htag]
          · simp [sentenceMatches, LO.Propositional.Formula.instEncodable,
              LO.Propositional.Formula.ofNat, htag]
          · rcases tag with _ | _ | _ | tag <;>
              simp [sentenceMatches, LO.Propositional.Formula.instEncodable,
                LO.Propositional.Formula.ofNat, htag, Option.bind_eq_some_iff]
  | himp φ ψ ihφ ihψ =>
      cases code with
      | zero => simp [sentenceMatches, LO.Propositional.Formula.instEncodable,
          LO.Propositional.Formula.ofNat]
      | succ e =>
          rcases htag : e.unpair.1 with _ | _ | _ | tag
          · simp [sentenceMatches, LO.Propositional.Formula.instEncodable,
              LO.Propositional.Formula.ofNat, htag]
          · simp [sentenceMatches, LO.Propositional.Formula.instEncodable,
              LO.Propositional.Formula.ofNat, htag]
          · simp [sentenceMatches, LO.Propositional.Formula.instEncodable,
              LO.Propositional.Formula.ofNat, htag, ihφ, ihψ,
              Option.bind_eq_some_iff]
            cases hleft : LO.Propositional.Formula.ofNat (α := ℕ) e.unpair.2.unpair.1 <;>
              cases hright : LO.Propositional.Formula.ofNat (α := ℕ)
                e.unpair.2.unpair.2 <;>
              simp [LO.Propositional.Formula.imp_inj]
          · rcases tag with _ | _ | tag <;>
              simp [sentenceMatches, LO.Propositional.Formula.instEncodable,
                LO.Propositional.Formula.ofNat, htag, Option.bind_eq_some_iff]
  | hand φ ψ ihφ ihψ =>
      cases code with
      | zero => simp [sentenceMatches, LO.Propositional.Formula.instEncodable,
          LO.Propositional.Formula.ofNat]
      | succ e =>
          rcases htag : e.unpair.1 with _ | _ | _ | _ | tag
          · simp [sentenceMatches, LO.Propositional.Formula.instEncodable,
              LO.Propositional.Formula.ofNat, htag]
          · simp [sentenceMatches, LO.Propositional.Formula.instEncodable,
              LO.Propositional.Formula.ofNat, htag]
          · simp [sentenceMatches, LO.Propositional.Formula.instEncodable,
              LO.Propositional.Formula.ofNat, htag, Option.bind_eq_some_iff]

          · simp [sentenceMatches, LO.Propositional.Formula.instEncodable,
              LO.Propositional.Formula.ofNat, htag, ihφ, ihψ]
            cases hleft : LO.Propositional.Formula.ofNat (α := ℕ) e.unpair.2.unpair.1 <;>
              cases hright : LO.Propositional.Formula.ofNat (α := ℕ)
                e.unpair.2.unpair.2 <;>
              simp [LO.Propositional.Formula.and_inj]
          · rcases tag with _ | tag <;>
              simp [sentenceMatches, LO.Propositional.Formula.instEncodable,
                LO.Propositional.Formula.ofNat, htag, Option.bind_eq_some_iff]
  | hor φ ψ ihφ ihψ =>
      cases code with
      | zero => simp [sentenceMatches, LO.Propositional.Formula.instEncodable,
          LO.Propositional.Formula.ofNat]
      | succ e =>
          rcases htag : e.unpair.1 with _ | _ | _ | _ | _ | tag
          · simp [sentenceMatches, LO.Propositional.Formula.instEncodable,
              LO.Propositional.Formula.ofNat, htag]
          · simp [sentenceMatches, LO.Propositional.Formula.instEncodable,
              LO.Propositional.Formula.ofNat, htag]
          · simp [sentenceMatches, LO.Propositional.Formula.instEncodable,
              LO.Propositional.Formula.ofNat, htag, Option.bind_eq_some_iff]
          · simp [sentenceMatches, LO.Propositional.Formula.instEncodable,
              LO.Propositional.Formula.ofNat, htag, Option.bind_eq_some_iff]
          · simp [sentenceMatches, LO.Propositional.Formula.instEncodable,
              LO.Propositional.Formula.ofNat, htag, ihφ, ihψ]
            cases hleft : LO.Propositional.Formula.ofNat (α := ℕ) e.unpair.2.unpair.1 <;>
              cases hright : LO.Propositional.Formula.ofNat (α := ℕ)
                e.unpair.2.unpair.2 <;>
              simp [LO.Propositional.Formula.or_inj]
          · simp [sentenceMatches, LO.Propositional.Formula.instEncodable,
              LO.Propositional.Formula.ofNat, htag]

private lemma sentenceMatches_polyFueled (target : Sentence) :
    ∃ c, PolyFueled c (sentenceMatches target) := by
  obtain ⟨cmul, hmul⟩ := mul_polyFueled
  induction target using LO.Propositional.Formula.rec' with
  | hfalsum =>
      have htag := PolyFueled.left.comp predc_polyFueled
      obtain ⟨ceq, heq⟩ := polyFueled_eqConst htag 0
      obtain ⟨c, hc⟩ := polyFueled_ifZero PolyFueled.id (PolyFueled.const 0) heq
      exact ⟨c, hc.of_eq (fun code => by simp [sentenceMatches])⟩
  | hatom a =>
      have hpred := predc_polyFueled
      have htag := PolyFueled.left.comp hpred
      have hpayload := PolyFueled.right.comp hpred
      obtain ⟨cpayload, hpayloadEq⟩ := polyFueled_eqConst hpayload a
      obtain ⟨ctag, htagEq⟩ := polyFueled_eqConst htag 1
      obtain ⟨cbody, hbody⟩ := polyFueled_ifZero htagEq (PolyFueled.const 0) hpayloadEq
      obtain ⟨c, hc⟩ := polyFueled_ifZero PolyFueled.id (PolyFueled.const 0) hbody
      exact ⟨c, hc.of_eq (fun code => by simp [sentenceMatches])⟩

  | himp φ ψ ihφ ihψ =>
      have hpred := predc_polyFueled
      have htag := PolyFueled.left.comp hpred
      have hpayload := PolyFueled.right.comp hpred
      obtain ⟨cφ, hφ⟩ := ihφ
      obtain ⟨cψ, hψ⟩ := ihψ
      have hleft := hφ.comp (PolyFueled.left.comp hpayload)
      have hright := hψ.comp (PolyFueled.right.comp hpayload)
      have hproduct := hmul.comp (hleft.pair hright)
      have hproduct' : PolyFueled _ (fun code =>
          sentenceMatches φ code.pred.unpair.2.unpair.1 *
            sentenceMatches ψ code.pred.unpair.2.unpair.2) :=
        hproduct.of_eq (fun code => by simp only [Nat.unpair_pair])
      obtain ⟨ctag, htagEq⟩ := polyFueled_eqConst htag 2
      obtain ⟨cbody, hbody⟩ := polyFueled_ifZero htagEq (PolyFueled.const 0) hproduct'
      obtain ⟨c, hc⟩ := polyFueled_ifZero PolyFueled.id (PolyFueled.const 0) hbody
      exact ⟨c, hc.of_eq (fun code => by simp [sentenceMatches])⟩
  | hand φ ψ ihφ ihψ =>
      have hpred := predc_polyFueled
      have htag := PolyFueled.left.comp hpred
      have hpayload := PolyFueled.right.comp hpred
      obtain ⟨cφ, hφ⟩ := ihφ
      obtain ⟨cψ, hψ⟩ := ihψ
      have hleft := hφ.comp (PolyFueled.left.comp hpayload)
      have hright := hψ.comp (PolyFueled.right.comp hpayload)
      have hproduct := hmul.comp (hleft.pair hright)
      have hproduct' : PolyFueled _ (fun code =>
          sentenceMatches φ code.pred.unpair.2.unpair.1 *
            sentenceMatches ψ code.pred.unpair.2.unpair.2) :=
        hproduct.of_eq (fun code => by simp only [Nat.unpair_pair])
      obtain ⟨ctag, htagEq⟩ := polyFueled_eqConst htag 3
      obtain ⟨cbody, hbody⟩ := polyFueled_ifZero htagEq (PolyFueled.const 0) hproduct'
      obtain ⟨c, hc⟩ := polyFueled_ifZero PolyFueled.id (PolyFueled.const 0) hbody
      exact ⟨c, hc.of_eq (fun code => by simp [sentenceMatches])⟩
  | hor φ ψ ihφ ihψ =>
      have hpred := predc_polyFueled
      have htag := PolyFueled.left.comp hpred
      have hpayload := PolyFueled.right.comp hpred
      obtain ⟨cφ, hφ⟩ := ihφ
      obtain ⟨cψ, hψ⟩ := ihψ
      have hleft := hφ.comp (PolyFueled.left.comp hpayload)
      have hright := hψ.comp (PolyFueled.right.comp hpayload)
      have hproduct := hmul.comp (hleft.pair hright)
      have hproduct' : PolyFueled _ (fun code =>
          sentenceMatches φ code.pred.unpair.2.unpair.1 *
            sentenceMatches ψ code.pred.unpair.2.unpair.2) :=
        hproduct.of_eq (fun code => by simp only [Nat.unpair_pair])
      obtain ⟨ctag, htagEq⟩ := polyFueled_eqConst htag 4
      obtain ⟨cbody, hbody⟩ := polyFueled_ifZero htagEq (PolyFueled.const 0) hproduct'
      obtain ⟨c, hc⟩ := polyFueled_ifZero PolyFueled.id (PolyFueled.const 0) hbody
      exact ⟨c, hc.of_eq (fun code => by simp [sentenceMatches])⟩

private lemma sentenceMatches_le_one (target : Sentence) (code : ℕ) :
    sentenceMatches target code ≤ 1 := by
  induction target using LO.Propositional.Formula.rec' generalizing code with
  | hfalsum =>
      cases code with
      | zero => simp [sentenceMatches]
      | succ e =>
          simp only [sentenceMatches, Nat.succ_ne_zero, if_false, Nat.pred_succ]
          split <;> omega
  | hatom a =>
      cases code with
      | zero => simp [sentenceMatches]
      | succ e =>
          simp only [sentenceMatches, Nat.succ_ne_zero, if_false, Nat.pred_succ]
          by_cases htag : e.unpair.1 = 1
          · by_cases hpayload : e.unpair.2 = a <;> simp [htag, hpayload]
          · simp [htag]
  | himp φ ψ ihφ ihψ =>
      cases code with
      | zero => simp [sentenceMatches]
      | succ e =>
          simp only [sentenceMatches, Nat.succ_ne_zero, if_false, Nat.pred_succ]
          by_cases htag : e.unpair.1 = 2
          · simp only [htag, if_true]
            nlinarith [ihφ e.unpair.2.unpair.1, ihψ e.unpair.2.unpair.2]
          · simp [htag]
  | hand φ ψ ihφ ihψ =>
      cases code with
      | zero => simp [sentenceMatches]
      | succ e =>
          simp only [sentenceMatches, Nat.succ_ne_zero, if_false, Nat.pred_succ]
          by_cases htag : e.unpair.1 = 3
          · simp only [htag, if_true]
            nlinarith [ihφ e.unpair.2.unpair.1, ihψ e.unpair.2.unpair.2]
          · simp [htag]
  | hor φ ψ ihφ ihψ =>
      cases code with
      | zero => simp [sentenceMatches]
      | succ e =>
          simp only [sentenceMatches, Nat.succ_ne_zero, if_false, Nat.pred_succ]
          by_cases htag : e.unpair.1 = 4
          · simp only [htag, if_true]
            nlinarith [ihφ e.unpair.2.unpair.1, ihψ e.unpair.2.unpair.2]
          · simp [htag]

private lemma sentenceMatches_eq_zero_iff (target : Sentence) (code : ℕ) :
    sentenceMatches target code = 0 ↔
      Encodable.decode (α := Sentence) code ≠ some target := by
  constructor
  · intro hzero hdecode
    have hone := (sentenceMatches_eq_one_iff target code).mpr hdecode
    omega
  · intro hdecode
    have hne : sentenceMatches target code ≠ 1 :=
      fun hone => hdecode ((sentenceMatches_eq_one_iff target code).mp hone)
    have hle := sentenceMatches_le_one target code
    omega

/-- Encoded exact lookup in one fixed rational-belief entry list. -/
def encodedQuoteFromEntries : List (Sentence × ℚ) → ℕ → ℕ
  | [], _ => Encodable.encode (0 : ℚ)
  | (target, q) :: entries, code =>
      if sentenceMatches target code = 0 then encodedQuoteFromEntries entries code
      else Encodable.encode q

private lemma encodedQuoteFromEntries_exact
    (entries : List (Sentence × ℚ)) (code : ℕ) (target : Sentence)
    (hdecode : Encodable.decode (α := Sentence) code = some target) :
    encodedQuoteFromEntries entries code =
      Encodable.encode (quoteFromEntries entries target) := by
  induction entries with
  | nil => simp [encodedQuoteFromEntries, quoteFromEntries]
  | cons entry entries ih =>
      rcases entry with ⟨ψ, q⟩
      by_cases htarget : target = ψ
      · subst ψ
        have hone := (sentenceMatches_eq_one_iff target code).mpr hdecode
        simp [encodedQuoteFromEntries, quoteFromEntries, hone]
      · have hdecNe : Encodable.decode (α := Sentence) code ≠ some ψ := by
          rw [hdecode]
          simpa using htarget
        have hzero := (sentenceMatches_eq_zero_iff ψ code).mpr hdecNe
        simp [encodedQuoteFromEntries, quoteFromEntries, htarget, hzero, ih]

private lemma encodedQuoteFromEntries_polyFueled
    (entries : List (Sentence × ℚ)) :
    ∃ c, PolyFueled c (encodedQuoteFromEntries entries) := by
  induction entries with
  | nil => exact ⟨_, PolyFueled.const (Encodable.encode (0 : ℚ))⟩
  | cons entry entries ih =>
      rcases entry with ⟨target, q⟩
      obtain ⟨cmatch, hmatch⟩ := sentenceMatches_polyFueled target
      obtain ⟨crest, hrest⟩ := ih
      obtain ⟨c, hc⟩ := polyFueled_ifZero hmatch hrest
        (PolyFueled.const (Encodable.encode q))
      exact ⟨c, hc.of_eq (fun code => by simp [encodedQuoteFromEntries])⟩

/-- Quote from the state at one fixed position of a finite belief-state prefix, with zero
after the end of the prefix. -/
def prefixQuoteFromStates : List RationalBeliefState → ℕ → Sentence → ℚ
  | [], _, _ => 0
  | state :: _, 0, φ => state.quote φ
  | _ :: states, day + 1, φ => prefixQuoteFromStates states day φ

/-- Raw-code form of `prefixQuoteFromStates`.  Each fixed state uses the exhaustive decoder
matcher above, so noncanonical sentence tokens receive the same quote as canonical ones. -/
def encodedPrefixQuoteFromStates : List RationalBeliefState → ℕ → ℕ → ℕ
  | [], _, _ => Encodable.encode (0 : ℚ)
  | state :: _, 0, code => encodedQuoteFromEntries state.entries code
  | _ :: states, day + 1, code => encodedPrefixQuoteFromStates states day code

lemma encodedPrefixQuoteFromStates_exact
    (states : List RationalBeliefState) (day code : ℕ) (φ : Sentence)
    (hdecode : Encodable.decode (α := Sentence) code = some φ) :
    encodedPrefixQuoteFromStates states day code =
      Encodable.encode (prefixQuoteFromStates states day φ) := by
  induction states generalizing day with
  | nil => simp [encodedPrefixQuoteFromStates, prefixQuoteFromStates]
  | cons state states ih =>
      cases day with
      | zero =>
          simpa [encodedPrefixQuoteFromStates, prefixQuoteFromStates,
            RationalBeliefState.quote] using
            encodedQuoteFromEntries_exact state.entries code φ hdecode
      | succ day =>
          simpa [encodedPrefixQuoteFromStates, prefixQuoteFromStates] using ih day

lemma encodedPrefixQuoteFromStates_polyFueled
    (states : List RationalBeliefState) :
    ∃ c, PolyFueled c (fun z =>
      encodedPrefixQuoteFromStates states z.unpair.1 z.unpair.2) := by
  induction states with
  | nil => exact ⟨_, PolyFueled.const (Encodable.encode (0 : ℚ))⟩
  | cons state states ih =>
      obtain ⟨centry, hentry⟩ := encodedQuoteFromEntries_polyFueled state.entries
      obtain ⟨crest, hrest⟩ := ih
      have hdayZero := hentry.comp PolyFueled.right
      have hdaySucc := hrest.comp
        ((predc_polyFueled.comp PolyFueled.left).pair PolyFueled.right)
      obtain ⟨c, hc⟩ := polyFueled_ifZero PolyFueled.left hdayZero hdaySucc
      refine ⟨c, hc.of_eq (fun z => ?_)⟩
      cases hday : z.unpair.1 with
      | zero =>
          simp [encodedPrefixQuoteFromStates]
      | succ day =>
          simp [encodedPrefixQuoteFromStates]

private lemma prefixQuoteFromStates_eq_getD
    (states : List RationalBeliefState) (fallback : RationalBeliefState)
    {day : ℕ} (hday : day < states.length) (φ : Sentence) :
    prefixQuoteFromStates states day φ = (states.getD day fallback).quote φ := by
  induction states generalizing day with
  | nil => simp at hday
  | cons state states ih =>
      cases day with
      | zero => simp [prefixQuoteFromStates]
      | succ day =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at hday
          simpa [prefixQuoteFromStates] using ih hday

/-- The finite rational quote table used by the LIA prefix patch. -/
noncomputable def liaPrefixQuote (DP : DeductiveProcess) (cutoff : ℕ) :
    ℕ → Sentence → ℚ :=
  prefixQuoteFromStates (liaStatePrefix DP cutoff)

/-- Polynomial raw-code implementation of `liaPrefixQuote`. -/
noncomputable def liaPrefixQuoteCode (DP : DeductiveProcess) (cutoff : ℕ) :
    ℕ → ℕ → ℕ :=
  encodedPrefixQuoteFromStates (liaStatePrefix DP cutoff)

lemma liaPrefixQuote_exact (DP : DeductiveProcess) (cutoff : ℕ)
    (day : ℕ) (hday : day < cutoff) (φ : Sentence) :
    liaHistory DP day φ = (liaPrefixQuote DP cutoff day φ : ℝ) := by
  have hprefix :
      liaPrefixQuote DP cutoff day φ = (liaStates DP day).quote φ := by
    rw [liaPrefixQuote,
      prefixQuoteFromStates_eq_getD (liaStatePrefix DP cutoff) (liaStates DP 0)
        (by simpa [liaStatePrefix_length] using hday) φ,
      liaStatePrefix_getD DP hday]
  simp [liaHistory, RationalBeliefState.toValuation, hprefix]

lemma liaPrefixQuoteCode_exact (DP : DeductiveProcess) (cutoff day code : ℕ)
    (φ : Sentence) (hdecode : Encodable.decode (α := Sentence) code = some φ) :
    liaPrefixQuoteCode DP cutoff day code =
      Encodable.encode (liaPrefixQuote DP cutoff day φ) := by
  exact encodedPrefixQuoteFromStates_exact (liaStatePrefix DP cutoff) day code φ hdecode

lemma liaPrefixQuoteCode_polyFueled (DP : DeductiveProcess) (cutoff : ℕ) :
    ∃ c, PolyFueled c (fun z =>
      liaPrefixQuoteCode DP cutoff z.unpair.1 z.unpair.2) :=
  encodedPrefixQuoteFromStates_polyFueled (liaStatePrefix DP cutoff)

end PrefixPatchCompile

/-- **Concrete finite-prefix compiler (`M7-PREFIX-PATCH`).**  The LIA's first `cutoff`
rational belief states form a fixed finite table.  Exhaustive raw sentence matching and the
flat administrative freeze transducer compile that table into a polynomial token emitter. -/
noncomputable def liaEfficientPrefixPatch (DP : DeductiveProcess) (cutoff : ℕ) :
    EfficientPrefixPatch (liaHistory DP) cutoff where
  quote := PrefixPatchCompile.liaPrefixQuote DP cutoff
  quote_exact := PrefixPatchCompile.liaPrefixQuote_exact DP cutoff
  preserves_ec := by
    intro Tr hTr
    obtain ⟨cq, hquotePoly⟩ :=
      PrefixPatchCompile.liaPrefixQuoteCode_polyFueled DP cutoff
    exact PrefixPatchCompile.freezeBefore_preserves_ec
      (PrefixPatchCompile.liaPrefixQuote DP cutoff)
      (PrefixPatchCompile.liaPrefixQuoteCode DP cutoff) cutoff
      (PrefixPatchCompile.liaPrefixQuoteCode_exact DP cutoff)
      hquotePoly Tr hTr

#print axioms polyFueled_dovetailFound
#print axioms polyFueled_deadlinePassed
#print axioms AffineCombination.PolySequence.primrec
#print axioms AffineCombination.settlementCheckAtFuel_prim
#print axioms SettlementChecker.ofComputations
#print axioms PatientSettlementClock.ofSemiDecider
#print axioms PatientSettlementClock.ofChecker
#print axioms PatientSettlementClock.ofComputations
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
#print axioms PrefixPatchCompile.freezeBefore_preserves_ec
#print axioms liaEfficientPrefixPatch

end LogicalInduction
