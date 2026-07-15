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
