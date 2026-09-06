import LogicalInduction.Construction.Freeze.Oracle
import LogicalInduction.Construction.LIACompiler

/-!
# An informative instance: perturbing the constructed logical inductor

`thm:ifp` (tex:1521) doing visible work.  `FreezeOracle.machine_lic_iff_twoPoint` exhibits
satisfiable hypotheses for the corrected theorem, but at a pair of markets that are almost
certainly exploitable, so the equivalence there may hold because both sides are false.  The
instance built here closes that gap.

`liaHistory DP` is a machine logical inductor (`Construction/LIA.lean`, from its market
program and a computable deductive process).  Moving one price — the coordinate
`(0, atom 0)` — gives a market that is computable, agrees with `liaHistory` everywhere else,
and is therefore *also* a machine logical inductor, **by the corrected theorem**.  Nothing
else derives that: the perturbed market is the output of no construction here, and its
inductor-hood is exactly what `thm:ifp` buys.  Market computability of `liaHistory DP` is not
a premise either — it is a field of `LIA_isMachineLogicalInductor DP hDP`, so a computable
deductive process is the only input.

Objects defined: `atomCode`, `perturbedQuote` (a rational quote table with one entry
overridden) and `liaPerturbed DP r` (`liaHistory DP` with the coordinate `(0, atom 0)` moved
to `r`).

Main results: `computableMarket_liaPerturbed` (`app:ifp`), `machineLogicalInductor_liaPerturbed`
and `exists_informative_liaPerturbation` (`thm:ifp`).

The instance is not degenerate: `exists_perturbation_value` picks a legal quote the market's
own single real value cannot equal, and `liaPerturbed_ne` proves the price actually moves.
-/

namespace LogicalInduction.LIAPerturbation

open LogicalInduction.FreezeOracle

/-- The frozen coordinate's sentence code. -/
abbrev atomCode : ℕ := Encodable.encode (LO.Propositional.Formula.atom 0 : Sentence)

/-! ## The perturbed market -/

/-- A rational quote table with one entry overridden. -/
def perturbedQuote (mq : ℕ → ℕ → ℚ) (r : ℚ) : ℕ → ℕ → ℚ :=
  fun n c => if n = 0 ∧ c = atomCode then r else mq n c

/-- `liaHistory DP` with the single coordinate `(0, atom 0)` moved to `r`. -/
noncomputable def liaPerturbed (DP : DeductiveProcess) (r : ℚ) : History :=
  fun n φ =>
    if n = 0 ∧ φ = (LO.Propositional.Formula.atom 0 : Sentence) then (r : ℝ)
    else liaHistory DP n φ

@[simp] lemma liaPerturbed_at (DP : DeductiveProcess) (r : ℚ) :
    liaPerturbed DP r 0 (LO.Propositional.Formula.atom 0 : Sentence) = (r : ℝ) := by
  rw [liaPerturbed, if_pos ⟨rfl, rfl⟩]

/-- Off the moved coordinate the two markets agree. -/
lemma liaPerturbed_agree (DP : DeductiveProcess) (r : ℚ) :
    ∀ d φ, (d, φ) ∉ exampleS → liaHistory DP d φ = liaPerturbed DP r d φ := by
  intro d φ hmem
  have hne : ¬(d = 0 ∧ φ = (LO.Propositional.Formula.atom 0 : Sentence)) := by
    intro hc
    exact hmem (by simp [exampleS, hc.1, hc.2])
  rw [liaPerturbed, if_neg hne]

/-! ## Computability of the perturbed market -/

/-- The market program promised by `ComputableMarket` is a computable function, not merely
a code: `Part` membership pins the code's value at every input. -/
lemma computable_of_marketCode {mq : ℕ → ℕ → ℚ} {code : Nat.Partrec.Code}
    (hcode : ∀ z, Encodable.encode (mq z.unpair.1 z.unpair.2) ∈ code.eval z) :
    Computable (fun z : ℕ => Encodable.encode (mq z.unpair.1 z.unpair.2)) := by
  have hev : code.eval
      = fun z => Part.some (Encodable.encode (mq z.unpair.1 z.unpair.2)) := by
    funext z
    exact Part.eq_some_iff.mpr (hcode z)
  have hpart : Nat.Partrec (fun z : ℕ =>
      Part.some (Encodable.encode (mq z.unpair.1 z.unpair.2))) := by
    rw [← hev]
    exact Nat.Partrec.Code.exists_code.mpr ⟨code, rfl⟩
  exact Partrec.nat_iff.mpr hpart

/-- Overriding one entry keeps the table computable. -/
lemma computable_perturbedQuote {mq : ℕ → ℕ → ℚ} (r : ℚ)
    (h : Computable (fun z : ℕ => Encodable.encode (mq z.unpair.1 z.unpair.2))) :
    Computable (fun z : ℕ =>
      Encodable.encode (perturbedQuote mq r z.unpair.1 z.unpair.2)) := by
  have h1 : Computable (fun z : ℕ => decide (z.unpair.1 = 0)) :=
    (Primrec.eq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 0)).decide.to_comp
  have h2 : Computable (fun z : ℕ => decide (z.unpair.2 = atomCode)) :=
    (Primrec.eq.comp (Primrec.snd.comp Primrec.unpair) (Primrec.const _)).decide.to_comp
  refine (Computable.cond h1
    (Computable.cond h2 (Computable.const (Encodable.encode r)) h) h).of_eq (fun z => ?_)
  rw [perturbedQuote]
  by_cases ha : z.unpair.1 = 0
  · by_cases hb : z.unpair.2 = atomCode
    · simp [ha, hb]
    · simp [ha, hb]
  · simp [ha]

/-- **The perturbed market is computable.**

Kind `N+` non-vacuity witness.  Provenance: (a) `computable_of_marketCode`,
`computable_perturbedQuote`; (b) `ComputableMarket.ofComputableTable`.
Paper node: `app:ifp` -/
theorem computableMarket_liaPerturbed (DP : DeductiveProcess)
    (hmarket : ComputableMarket (liaHistory DP)) (r : ℚ) (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    ComputableMarket (liaPerturbed DP r) := by
  obtain ⟨hrange, mq, code, hexact, hcode⟩ := hmarket
  have hrange' : ∀ n φ, 0 ≤ liaPerturbed DP r n φ ∧ liaPerturbed DP r n φ ≤ 1 := by
    intro n φ
    rw [liaPerturbed]
    split_ifs
    · constructor
      · exact_mod_cast h0
      · exact_mod_cast h1
    · exact hrange n φ
  refine ComputableMarket.ofComputableTable (perturbedQuote mq r) hrange' (fun n φ => ?_)
    (computable_perturbedQuote r (computable_of_marketCode hcode))
  rw [liaPerturbed, perturbedQuote]
  by_cases hc : n = 0 ∧ φ = (LO.Propositional.Formula.atom 0 : Sentence)
  · rw [if_pos hc, if_pos ⟨hc.1, by rw [hc.2]⟩]
  · rw [if_neg hc, if_neg ?_, hexact n φ]
    intro hd
    exact hc ⟨hd.1, Encodable.encode_injective hd.2⟩

/-! ## The perturbation is real -/

/-- A legal quote value that actually moves the price: `liaHistory`'s own value there is a
single real, so it cannot equal both `0` and `1`. -/
lemma exists_perturbation_value (DP : DeductiveProcess) :
    ∃ r : ℚ, 0 ≤ r ∧ r ≤ 1 ∧
      ((r : ℝ) ≠ liaHistory DP 0 (LO.Propositional.Formula.atom 0 : Sentence)) := by
  by_cases h : ((0 : ℚ) : ℝ) = liaHistory DP 0 (LO.Propositional.Formula.atom 0 : Sentence)
  · refine ⟨1, by norm_num, le_refl 1, ?_⟩
    rw [← h]
    norm_num
  · exact ⟨0, le_refl 0, by norm_num, h⟩

/-- The moved coordinate really moves: at a quote value the market's own single real value
cannot equal. -/
lemma liaPerturbed_ne (DP : DeductiveProcess) {r : ℚ}
    (hr : (r : ℝ) ≠ liaHistory DP 0 (LO.Propositional.Formula.atom 0 : Sentence)) :
    liaPerturbed DP r 0 (LO.Propositional.Formula.atom 0 : Sentence)
      ≠ liaHistory DP 0 (LO.Propositional.Formula.atom 0 : Sentence) := by
  rw [liaPerturbed_at]
  exact hr

/-! ## The informative instance -/

/-- **The perturbed inductor.**  `liaHistory DP` is a machine logical inductor; move one
price and the result is one too — a consequence of the corrected `thm:ifp`, and of no
construction here.  Market computability of `liaHistory DP` is not a premise: it is a field
of `LIA_isMachineLogicalInductor DP hDP`, so the computable deductive process is the only
input.

Kind `C`; hypotheses `(a)`.
Paper node: `thm:ifp` -/
theorem machineLogicalInductor_liaPerturbed (DP : DeductiveProcess)
    (hDP : ComputableDeductiveProcess DP) (r : ℚ) (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    IsMachineLogicalInductor (liaPerturbed DP r) DP := by
  have hLIA : IsMachineLogicalInductor (liaHistory DP) DP :=
    LIA_isMachineLogicalInductor DP hDP
  have hmarket : ComputableMarket (liaHistory DP) := hLIA.marketComputable
  refine (machine_lic_iff_of_finiteSupport (liaHistory DP) (liaPerturbed DP r) DP
    hmarket (computableMarket_liaPerturbed DP hmarket r h0 h1) ?_).mp hLIA
  exact ⟨exampleS, liaPerturbed_agree DP r⟩

/-- **The informative instance, packaged.**  A computable market that is a machine logical
inductor, differs from the constructed one at exactly one coordinate, and differs there by a
nonzero amount.

Its inductor-hood comes from `thm:ifp` and nowhere else, so this is the corrected theorem
doing visible work rather than merely having satisfiable hypotheses.

Kind `N+` non-vacuity witness.
Paper node: `thm:ifp` -/
theorem exists_informative_liaPerturbation (DP : DeductiveProcess)
    (hDP : ComputableDeductiveProcess DP) :
    ∃ P' : History,
      ComputableMarket P' ∧
      IsMachineLogicalInductor P' DP ∧
      P' 0 (LO.Propositional.Formula.atom 0 : Sentence)
        ≠ liaHistory DP 0 (LO.Propositional.Formula.atom 0 : Sentence) ∧
      (∀ d φ, (d, φ) ∉ exampleS → liaHistory DP d φ = P' d φ) := by
  obtain ⟨r, h0, h1, hr⟩ := exists_perturbation_value DP
  have hmarket : ComputableMarket (liaHistory DP) :=
    (LIA_isMachineLogicalInductor DP hDP).marketComputable
  exact ⟨liaPerturbed DP r, computableMarket_liaPerturbed DP hmarket r h0 h1,
    machineLogicalInductor_liaPerturbed DP hDP r h0 h1,
    liaPerturbed_ne DP hr, liaPerturbed_agree DP r⟩

end LogicalInduction.LIAPerturbation
