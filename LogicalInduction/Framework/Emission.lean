import LogicalInduction.Framework.Computable

/-!
# Polynomial emission machinery (`dd:fuel`)

Conclusion-free bounded-simulation compilers over `Nat.Partrec.Code`
(`codeEvalBound`, `codeEvalnNat`, dovetailing) and the
clocked token-emission layer (`PrefixPatchCompile.ecClock` …
`clockedTokens_polySegStream`), together with the token→digit inclusion
`EfficientlyComputableTok.toDigit`.  No market-limit, exploitation, or
logical-inductor conclusions appear here; property files consume the interfaces.
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

/-! ## Universal bounded simulator

Target: for every fixed `simulated : Code`, the total normalized bounded interpreter
`codeEvalnNat simulated : ℕ → ℕ` is computable in the project's own polynomial-fuel model
(`PolyFueled`). Mathlib does not supply this: `Code.primrec_evaln` gives only primitive
recursion, with no polynomial fuel certificate. The proof is a structural induction on
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
-- `Nat.sqrt` is made locally irreducible here and in every other section doing deep
-- `Primrec`/`PolyFueled` work over `Nat.pair`-encoded products: `Nat.pair`'s definition
-- mentions `Nat.sqrt`, whose well-founded recursion makes `whnf` unfold it endlessly
-- during defeq checks on nested pair codes, hanging elaboration. The attribute is scoped,
-- so no global reasoning about `Nat.sqrt` is affected. This is the one recurring
-- elaboration workaround in the repo; every `attribute [local irreducible] Nat.sqrt`
-- below and in other files is this same fix.
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

/-- **Universal bounded simulator.** For every fixed `simulated`, the total normalized
bounded interpreter is computable in the project polynomial-fuel model.
Paper node: `def:ec` -/
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

/-! ## The bounded dovetail

The paper's `app:prandaff` clock is built from an *arbitrary-runtime* decider run under a
growing budget:

> `DefinitelySettled(n, m) :↔ ∃ i ≤ m: settled(n, i)` returns true within `m` steps

with the three properties it needs: poly in `m`; `DefinitelySettled → Settled`; and if
`Settled(n,m)` then `DefinitelySettled(n,M)` for some `M ≥ m`.  Nothing here is specific to
settlement — this is the generic move that turns *any* code into a polynomial Boolean table
that is monotone in the budget and eventually fires.  It is what
`PatientSettlementClock.active_codes` (`Properties/Pseudorandomness.lean`) and
`HistoricalVerifiedMaturitySchedule.check_poly` (`Framework/ROI.lean`) both need, so it is
stated once, generically.

The simulator (`codeEvalnNat_polyFueled`) is what makes the budgeted run polynomial;
`polyFueled_boundedAny` supplies the bounded search. -/

/-- `c` returns `1` on input `x` within `fuel` steps of the clocked interpreter.
(`codeEvalnNat` normalizes `none ↦ 0` and `some out ↦ out+1`, so acceptance is `2`.) -/
def acceptsWithin (c : Nat.Partrec.Code) (fuel x : ℕ) : Bool :=
  decide (codeEvalnNat c (Nat.pair fuel x) = 2)

/-- The dovetail's inner predicate, indexed as `⟨⟨i,n⟩, j⟩`. -/
def dovetailStep (c : Nat.Partrec.Code) (z j : ℕ) : Bool :=
  acceptsWithin c z.unpair.2 (Nat.pair z.unpair.1 j)

/-- `dovetailFound c i n`: some `j ≤ n` is accepted for `i` within budget `n`. -/
def dovetailFound (c : Nat.Partrec.Code) (i n : ℕ) : Bool :=
  boundedAny (dovetailStep c) (Nat.pair i n) n

lemma dovetailFound_eq_true_iff (c : Nat.Partrec.Code) (i n : ℕ) :
    dovetailFound c i n = true ↔ ∃ j ≤ n, acceptsWithin c n (Nat.pair i j) = true := by
  simp [dovetailFound, boundedAny_eq_true_iff, dovetailStep]

/-! ## Polynomial flat-token transduction

The evaluator clock `ecClock` carried by an `EfficientlyComputableTok` certificate,
together with the total length/token oracles of one clocked trader program and the proof
that the resulting raw token stream is a `PolySegStream`. -/

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

end PrefixPatchCompile

/-! ### The digit-model inclusion (`dd:fuel`) -/

/-- **Every token-model certificate is a digit-model certificate.**  A clocked token
stream is a `PolySegStream` (`clockedTokens_polySegStream`), its digit stream is again one
(`PolySegStream.digitizeStream`), and any `PolySegStream` realizes a digit-model
certificate whose undigitized decode is the same trader (`ecDigit_of_rawSegStream` +
`undigitize_digitize`).  This transfers an `EfficientlyComputableTok` certificate into the
wider digit-metered class unchanged.
Paper node: `def:ec` -/
theorem EfficientlyComputableTok.toDigit {Tr : Trader}
    (h : EfficientlyComputableTok Tr) : EfficientlyComputableDigit Tr := by
  obtain ⟨lc, tc, a, k, hTr⟩ := h
  have hdig := PolySegStream.digitizeStream
    (PrefixPatchCompile.clockedTokens_polySegStream lc tc a k)
  refine ecDigit_of_rawSegStream Tr hdig (fun n => ?_)
  rw [undigitize_digitize, ← hTr]
  rfl

#print axioms EfficientlyComputableTok.toDigit

end LogicalInduction
