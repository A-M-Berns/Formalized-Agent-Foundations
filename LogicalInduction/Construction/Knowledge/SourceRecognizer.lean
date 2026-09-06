import LogicalInduction.Construction.LUV.ArithmeticSource
import LogicalInduction.Construction.Primcodable

/-!
# Recognizing the token runs that are genuinely *written sources*

`Framework/Criterion.lean`'s `parseStructuredArithmeticFormula` is a *numeric* parser: it
turns a token run into a Foundation Gödel code.  It is deliberately permissive, and two of
its liberties are fatal if it is used as a *gate* on what a machine may present as an
axiom:

* it threads a `depth` argument but never reads it, so a bound-variable token may carry an
  index larger than the number of enclosing quantifiers;
* it accepts the free-variable tag `4`, whose formulas are not sentences at all.

Either way the code it returns can be the code of a formula that is not `↑σ` for any
`σ : ArithmeticSemisentence k`, so a `thm:incons` window gated on "the numeric parser
succeeds" is not a window on a *theory*.

This module supplies the gate the window actually needs.  `sourceRun` is a recognizer for
exactly the runs of the form `ArithSource.sourceTokens s ++ rest` with
`ArithSource.compile s` the embedding of a semisentence, and it is

* **sound** (`exists_source_of_sourceRun`): every accepted run *is* such a run;
* **complete** (`sourceRun_sourceTokens`): every such run is accepted;
* **primitive recursive** (`sourceRun_prim`), so the gate can sit inside the emission
  calculus rather than in the metatheory.

`sourceRun_full_prim` is the single entry point out of the module: `admissibleName_primrec`
(`Construction/Knowledge/SourceWindow.lean`) uses it to make `AdmissibleName` a decidable
primitive-recursive test.  Nothing outside this file uses the recognizers themselves.

The alphabet recognized is the paper's own source alphabet — `ArithSource.sourceTokens`
tags, the normal-form expansion tags `20`/`21`/`22` among them — and not Foundation's
negation normal form (`dd:nnf`).  No paper node renders here: this is representation
infrastructure for `thm:incons`, whose statement lives in
`Construction/Knowledge/Endpoints.lean`.

## Why the nat sub-recognizer is not `parseStructuredNat`

`parseStructuredNat` is *not injective on token runs*: `[1, 0]` and `[0]` both decode to
`0`, because the "double" tag `1` accepts a zero sub-value while `encodeStructuredNat`
never emits one.  So `parseStructuredNat fuel ts = some (n, rest)` does **not** entail
`ts = encodeStructuredNat n ++ rest`, and a recognizer built on it could not be sound in
the exact-token sense above.  `structuredNatRun` is the canonical-only variant: it is the
same automaton with the single side condition that a `1` tag must cover a nonzero value,
which is exactly the image of `encodeStructuredNat`.
-/

namespace LogicalInduction

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

/-! ## Canonical structured naturals -/

/-- Recognizer for a *canonically* written structured natural; returns the value and the
unread suffix.  The guard `p.1 ≠ 0` on the doubling tag `1` is what
`parseStructuredNat` lacks, and is exactly what makes the token run recoverable from the
value (`structuredNatRun_shape`).

*Proof kind:* `Def`. -/
def structuredNatRun : ℕ → List ℕ → Option (ℕ × List ℕ)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, t :: rest =>
      if t = 0 then some (0, rest)
      else if t = 1 then
        (structuredNatRun fuel rest).bind fun p =>
          if p.1 = 0 then none else some (2 * p.1, p.2)
      else if t = 2 then
        (structuredNatRun fuel rest).map fun p => (2 * p.1 + 1, p.2)
      else none

private lemma encodeStructuredNat_two_mul (m : ℕ) (hm : m ≠ 0) :
    encodeStructuredNat (2 * m) = 1 :: encodeStructuredNat m := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  have hrw : 2 * (j + 1) = (2 * j + 1) + 1 := by ring
  rw [hrw, encodeStructuredNat]
  have h1 : ((2 * j + 1) + 1) % 2 = 0 := by omega
  have h2 : ((2 * j + 1) + 1) / 2 = j + 1 := by omega
  simp [h1, h2]

private lemma encodeStructuredNat_two_mul_succ (m : ℕ) :
    encodeStructuredNat (2 * m + 1) = 2 :: encodeStructuredNat m := by
  rw [encodeStructuredNat]
  have h1 : (2 * m + 1) % 2 = 1 := by omega
  have h2 : (2 * m + 1) / 2 = m := by omega
  simp [h1, h2]

/-- **Soundness of the canonical nat recognizer**: an accepted prefix is literally the
`encodeStructuredNat` writing of the value it returns.

*Proof kind:* `P` proved. -/
lemma structuredNatRun_shape : ∀ {fuel : ℕ} {ts : List ℕ} {n : ℕ} {rest : List ℕ},
    structuredNatRun fuel ts = some (n, rest) → ts = encodeStructuredNat n ++ rest := by
  intro fuel
  induction fuel with
  | zero => intro ts n rest h; simp [structuredNatRun] at h
  | succ fuel ih =>
      intro ts n rest h
      rcases ts with _ | ⟨t, ts⟩
      · simp [structuredNatRun] at h
      rw [structuredNatRun] at h
      split_ifs at h with h0 h1 h2
      · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
        simp [h0, encodeStructuredNat]
      · rcases hp : structuredNatRun fuel ts with _ | p
        · rw [hp] at h; simp at h
        rw [hp] at h
        simp only [Option.bind_some] at h
        split_ifs at h with hz
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [h1, ih hp, encodeStructuredNat_two_mul _ hz]
        rfl
      · rcases hp : structuredNatRun fuel ts with _ | p
        · rw [hp] at h; simp at h
        rw [hp] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [h2, ih hp, encodeStructuredNat_two_mul_succ]
        rfl

/-- **Completeness of the canonical nat recognizer**.

*Proof kind:* `P` proved. -/
lemma structuredNatRun_encode (n : ℕ) (tail : List ℕ) {fuel : ℕ}
    (hfuel : (encodeStructuredNat n).length ≤ fuel) :
    structuredNatRun fuel (encodeStructuredNat n ++ tail) = some (n, tail) := by
  induction n using Nat.strong_induction_on generalizing fuel tail with
  | h n ih =>
      cases n with
      | zero =>
          cases fuel with
          | zero => simp [encodeStructuredNat] at hfuel
          | succ fuel => simp [encodeStructuredNat, structuredNatRun]
      | succ n =>
          have hdiv : (n + 1) / 2 < n + 1 := Nat.div_lt_self (Nat.succ_pos n) (by norm_num)
          rw [encodeStructuredNat]
          split <;> rename_i hpar
          · cases fuel with
            | zero => simp [encodeStructuredNat, hpar] at hfuel
            | succ fuel =>
                simp only [List.cons_append, structuredNatRun]
                rw [ih _ hdiv tail (fuel := fuel)
                  (by simpa [encodeStructuredNat, hpar] using hfuel)]
                have hnz : (n + 1) / 2 ≠ 0 := by omega
                have heven : 2 * ((n + 1) / 2) = n + 1 := by omega
                simp [hnz, heven]
          · cases fuel with
            | zero => simp [encodeStructuredNat, hpar] at hfuel
            | succ fuel =>
                simp only [List.cons_append, structuredNatRun]
                rw [ih _ hdiv tail (fuel := fuel)
                  (by simpa [encodeStructuredNat, hpar] using hfuel)]
                have hodd : 2 * ((n + 1) / 2) + 1 = n + 1 := by omega
                simp [hodd]

/-! ## The recognizers -/

/-- Recognizer for a written arithmetic *term* at binder depth `k`; returns the unread
suffix.  Free variables (tag `4`) are rejected, and a bound-variable index is checked
against the binder depth — the two things `parseStructuredArithmeticTerm` does not do.

*Proof kind:* `Def`. -/
def sourceTermRun : ℕ → ℕ → List ℕ → Option (List ℕ)
  | 0, _, _ => none
  | _ + 1, _, [] => none
  | fuel + 1, k, t :: rest =>
      if t = 3 then
        (structuredNatRun fuel rest).bind fun p => if p.1 < k then some p.2 else none
      else if t = 5 then some rest
      else if t = 6 then some rest
      else if t = 7 ∨ t = 8 then
        (sourceTermRun fuel k rest).bind fun r => sourceTermRun fuel k r
      else none

/-- Recognizer for a written *source* at binder depth `k`; returns the unread suffix.

*Proof kind:* `Def`. -/
def sourceRun : ℕ → ℕ → List ℕ → Option (List ℕ)
  | 0, _, _ => none
  | _ + 1, _, [] => none
  | fuel + 1, k, t :: rest =>
      if t = 9 ∨ t = 10 then some rest
      else if t = 11 ∨ t = 12 ∨ t = 13 ∨ t = 14 then
        (sourceTermRun fuel k rest).bind fun r => sourceTermRun fuel k r
      else if t = 15 ∨ t = 16 ∨ t = 21 ∨ t = 22 then
        (sourceRun fuel k rest).bind fun r => sourceRun fuel k r
      else if t = 17 ∨ t = 18 then sourceRun fuel (k + 1) rest
      else if t = 20 then sourceRun fuel k rest
      else none

/-! ## Soundness -/

/-- **Term soundness**: every run the term recognizer accepts is the written form of a
term with *no free variables* whose bound indices all lie below the binder depth — that
is, of the embedding of a `Semiterm ℒₒᵣ Empty k`.

*Proof kind:* `P` proved. -/
lemma exists_semiterm_of_sourceTermRun : ∀ {fuel k : ℕ} {ts rest : List ℕ},
    sourceTermRun fuel k ts = some rest →
      ∃ u : Semiterm ℒₒᵣ Empty k,
        ts = encodeArithmeticTermSymbols (Rew.emb u : ArithmeticSemiterm ℕ k) ++ rest := by
  intro fuel
  induction fuel with
  | zero => intro k ts rest h; simp [sourceTermRun] at h
  | succ fuel ih =>
      intro k ts rest h
      rcases ts with _ | ⟨t, ts⟩
      · simp [sourceTermRun] at h
      rw [sourceTermRun] at h
      split_ifs at h with h3 h5 h6 h78
      · rcases hp : structuredNatRun fuel ts with _ | p
        · rw [hp] at h; simp at h
        rw [hp] at h
        simp only [Option.bind_some] at h
        split_ifs at h with hlt
        obtain rfl := Option.some.inj h
        refine ⟨(#(⟨p.1, hlt⟩ : Fin k) : Semiterm ℒₒᵣ Empty k), ?_⟩
        rw [h3, structuredNatRun_shape hp]
        simp [encodeArithmeticTermSymbols]
      · obtain rfl := Option.some.inj h
        exact ⟨Semiterm.func Language.ORing.Func.zero ![], by
          simp [h5, encodeArithmeticTermSymbols]⟩
      · obtain rfl := Option.some.inj h
        exact ⟨Semiterm.func Language.ORing.Func.one ![], by
          simp [h6, encodeArithmeticTermSymbols]⟩
      · rcases hr : sourceTermRun fuel k ts with _ | r
        · rw [hr] at h; simp at h
        rw [hr] at h
        simp only [Option.bind_some] at h
        obtain ⟨u₀, hu₀⟩ := ih hr
        obtain ⟨u₁, hu₁⟩ := ih h
        rcases h78 with rfl | rfl
        · exact ⟨Semiterm.func Language.ORing.Func.add ![u₀, u₁], by
            rw [hu₀, hu₁]; simp [encodeArithmeticTermSymbols]⟩
        · exact ⟨Semiterm.func Language.ORing.Func.mul ![u₀, u₁], by
            rw [hu₀, hu₁]; simp [encodeArithmeticTermSymbols]⟩

/-- **Source soundness — the load-bearing statement.**  Every run the recognizer accepts
is literally the emitted run of some `ArithSource` whose compilation is the embedding of a
semisentence.  This is what `parseStructuredArithmeticFormula` alone does *not* give: it
ignores its `depth` argument and accepts the free-variable tag `4`, so the formula whose
code it returns need not be a sentence.

*Proof kind:* `P` proved.  The source and the semisentence are built in lockstep, so the
`compile s = ↑τ` half falls out of `Rewriting.emb` being a homomorphism. -/
lemma exists_source_of_sourceRun : ∀ {fuel k : ℕ} {ts rest : List ℕ},
    sourceRun fuel k ts = some rest →
      ∃ (s : ArithSource k) (τ : ArithmeticSemisentence k),
        ts = ArithSource.sourceTokens s ++ rest ∧
        ArithSource.compile s = (↑τ : ArithmeticSemiformula ℕ k) := by
  intro fuel
  induction fuel with
  | zero => intro k ts rest h; simp [sourceRun] at h
  | succ fuel ih =>
      intro k ts rest h
      rcases ts with _ | ⟨t, ts⟩
      · simp [sourceRun] at h
      rw [sourceRun] at h
      split_ifs at h with h910 hrel hbin hq h20
      · obtain rfl := Option.some.inj h
        rcases h910 with rfl | rfl
        · exact ⟨.leaf ⊤, ⊤, by simp [ArithSource.sourceTokens,
            encodeArithmeticFormulaSymbols], rfl⟩
        · exact ⟨.leaf ⊥, ⊥, by simp [ArithSource.sourceTokens,
            encodeArithmeticFormulaSymbols], rfl⟩
      · rcases hr : sourceTermRun fuel k ts with _ | r
        · rw [hr] at h; simp at h
        rw [hr] at h
        simp only [Option.bind_some] at h
        obtain ⟨u₀, hu₀⟩ := exists_semiterm_of_sourceTermRun hr
        obtain ⟨u₁, hu₁⟩ := exists_semiterm_of_sourceTermRun h
        rcases hrel with rfl | rfl | rfl | rfl
        · refine ⟨.leaf ↑(Semiformula.rel Language.ORing.Rel.eq ![u₀, u₁]),
            Semiformula.rel Language.ORing.Rel.eq ![u₀, u₁], ?_, rfl⟩
          rw [hu₀, hu₁]
          simp [ArithSource.sourceTokens, encodeArithmeticFormulaSymbols]
        · refine ⟨.leaf ↑(Semiformula.nrel Language.ORing.Rel.eq ![u₀, u₁]),
            Semiformula.nrel Language.ORing.Rel.eq ![u₀, u₁], ?_, rfl⟩
          rw [hu₀, hu₁]
          simp [ArithSource.sourceTokens, encodeArithmeticFormulaSymbols]
        · refine ⟨.leaf ↑(Semiformula.rel Language.ORing.Rel.lt ![u₀, u₁]),
            Semiformula.rel Language.ORing.Rel.lt ![u₀, u₁], ?_, rfl⟩
          rw [hu₀, hu₁]
          simp [ArithSource.sourceTokens, encodeArithmeticFormulaSymbols]
        · refine ⟨.leaf ↑(Semiformula.nrel Language.ORing.Rel.lt ![u₀, u₁]),
            Semiformula.nrel Language.ORing.Rel.lt ![u₀, u₁], ?_, rfl⟩
          rw [hu₀, hu₁]
          simp [ArithSource.sourceTokens, encodeArithmeticFormulaSymbols]
      · rcases hr : sourceRun fuel k ts with _ | r
        · rw [hr] at h; simp at h
        rw [hr] at h
        simp only [Option.bind_some] at h
        obtain ⟨a, τa, ha, hca⟩ := ih hr
        obtain ⟨b, τb, hb, hcb⟩ := ih h
        rcases hbin with rfl | rfl | rfl | rfl
        · exact ⟨.and a b, τa ⋏ τb, by rw [ha, hb]; simp [ArithSource.sourceTokens],
            by simp [ArithSource.compile, hca, hcb]⟩
        · exact ⟨.or a b, τa ⋎ τb, by rw [ha, hb]; simp [ArithSource.sourceTokens],
            by simp [ArithSource.compile, hca, hcb]⟩
        · exact ⟨.imp a b, τa 🡒 τb, by rw [ha, hb]; simp [ArithSource.sourceTokens],
            by simp [ArithSource.compile, hca, hcb, Semiformula.imp_eq,
              LogicalConnective.HomClass.map_neg]⟩
        · exact ⟨.iff a b, τa 🡘 τb, by rw [ha, hb]; simp [ArithSource.sourceTokens],
            by simp [ArithSource.compile, hca, hcb, Semiformula.iff_eq,
              LogicalConnective.HomClass.map_neg]⟩
      · obtain ⟨a, τa, ha, hca⟩ := ih h
        rcases hq with rfl | rfl
        · exact ⟨.all a, ∀⁰ τa, by rw [ha]; simp [ArithSource.sourceTokens],
            by simp only [ArithSource.compile, hca, Rewriting.app_all, Rew.q_emb]; rfl⟩
        · exact ⟨.exs a, ∃⁰ τa, by rw [ha]; simp [ArithSource.sourceTokens],
            by simp only [ArithSource.compile, hca, Rewriting.app_exs, Rew.q_emb]; rfl⟩
      · obtain ⟨a, τa, ha, hca⟩ := ih h
        exact ⟨.not a, ∼τa, by rw [ha, h20]; simp [ArithSource.sourceTokens],
          by simp [ArithSource.compile, hca, LogicalConnective.HomClass.map_neg]⟩

/-! ## Completeness -/

/-- **Term completeness at a leaf**: the writing of an embedded `Empty`-variable term is
accepted.  Free variables cannot occur (`Empty.elim`), and a bound index is a `Fin k`
value, hence below the binder depth.

*Proof kind:* `P` proved. -/
lemma sourceTermRun_emb : ∀ {k : ℕ} (u : Semiterm ℒₒᵣ Empty k) (tail : List ℕ) {fuel : ℕ},
    (encodeArithmeticTermSymbols (Rew.emb u : ArithmeticSemiterm ℕ k)).length ≤ fuel →
    sourceTermRun fuel k
        (encodeArithmeticTermSymbols (Rew.emb u : ArithmeticSemiterm ℕ k) ++ tail) =
      some tail := by
  intro k u
  induction u with
  | bvar x =>
      intro tail fuel hfuel
      cases fuel with
      | zero => simp [encodeArithmeticTermSymbols] at hfuel
      | succ fuel =>
          simp only [Rew.emb_bvar, encodeArithmeticTermSymbols, List.cons_append,
            sourceTermRun, if_pos]
          rw [structuredNatRun_encode (x : ℕ) tail
            (by simpa [encodeArithmeticTermSymbols] using hfuel)]
          simp [x.isLt]
  | fvar x => exact x.elim
  | func f v ih =>
      rcases f with _ | _ | _ | _
      · intro tail fuel hfuel
        cases fuel with
        | zero => simp [encodeArithmeticTermSymbols] at hfuel
        | succ fuel => simp [encodeArithmeticTermSymbols, sourceTermRun]
      · intro tail fuel hfuel
        cases fuel with
        | zero => simp [encodeArithmeticTermSymbols] at hfuel
        | succ fuel => simp [encodeArithmeticTermSymbols, sourceTermRun]
      · intro tail fuel hfuel
        cases fuel with
        | zero => simp [encodeArithmeticTermSymbols] at hfuel
        | succ fuel =>
            simp only [Rew.func, Function.comp_apply, encodeArithmeticTermSymbols,
              List.cons_append, List.append_assoc, sourceTermRun]
            rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
              if_pos (by norm_num)]
            rw [ih 0 (encodeArithmeticTermSymbols
                (Rew.emb (v 1) : ArithmeticSemiterm ℕ k) ++ tail)
              (by
                simp [Rew.func, Function.comp_apply, encodeArithmeticTermSymbols] at hfuel
                omega),
              Option.bind_some,
              ih 1 tail (by
                simp [Rew.func, Function.comp_apply, encodeArithmeticTermSymbols] at hfuel
                omega)]
      · intro tail fuel hfuel
        cases fuel with
        | zero => simp [encodeArithmeticTermSymbols] at hfuel
        | succ fuel =>
            simp only [Rew.func, Function.comp_apply, encodeArithmeticTermSymbols,
              List.cons_append, List.append_assoc, sourceTermRun]
            rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
              if_pos (by norm_num)]
            rw [ih 0 (encodeArithmeticTermSymbols
                (Rew.emb (v 1) : ArithmeticSemiterm ℕ k) ++ tail)
              (by
                simp [Rew.func, Function.comp_apply, encodeArithmeticTermSymbols] at hfuel
                omega),
              Option.bind_some,
              ih 1 tail (by
                simp [Rew.func, Function.comp_apply, encodeArithmeticTermSymbols] at hfuel
                omega)]

/-! ### Pushing the semisentence embedding through the constructors

`Rewriting.emb` is a `LogicalConnective` hom that commutes with the quantifiers, so it
distributes over every normal-form constructor.  These are stated in constructor form
(rather than in notation) so that `simp` can fire on the shapes the `Semiformula`
recursor produces. -/

private lemma coe_verum {k : ℕ} :
    (Rewriting.emb (Semiformula.verum : ArithmeticSemisentence k) :
      ArithmeticSemiformula ℕ k) = Semiformula.verum := rfl

private lemma coe_falsum {k : ℕ} :
    (Rewriting.emb (Semiformula.falsum : ArithmeticSemisentence k) :
      ArithmeticSemiformula ℕ k) = Semiformula.falsum := rfl

private lemma coe_and {k : ℕ} (τ σ : ArithmeticSemisentence k) :
    (Rewriting.emb (Semiformula.and τ σ) : ArithmeticSemiformula ℕ k) =
      Semiformula.and (Rewriting.emb τ : ArithmeticSemiformula ℕ k)
        (Rewriting.emb σ : ArithmeticSemiformula ℕ k) := rfl

private lemma coe_or {k : ℕ} (τ σ : ArithmeticSemisentence k) :
    (Rewriting.emb (Semiformula.or τ σ) : ArithmeticSemiformula ℕ k) =
      Semiformula.or (Rewriting.emb τ : ArithmeticSemiformula ℕ k)
        (Rewriting.emb σ : ArithmeticSemiformula ℕ k) := rfl

private lemma coe_all' {k : ℕ} (τ : ArithmeticSemisentence (k + 1)) :
    (Rewriting.emb (Semiformula.all τ) : ArithmeticSemiformula ℕ k) =
      Semiformula.all (Rewriting.emb τ : ArithmeticSemiformula ℕ (k + 1)) := by
  rw [show Semiformula.all τ = ∀⁰ τ from rfl, Rewriting.app_all, Rew.q_emb]
  rfl

private lemma coe_exs' {k : ℕ} (τ : ArithmeticSemisentence (k + 1)) :
    (Rewriting.emb (Semiformula.exs τ) : ArithmeticSemiformula ℕ k) =
      Semiformula.exs (Rewriting.emb τ : ArithmeticSemiformula ℕ (k + 1)) := by
  rw [show Semiformula.exs τ = ∃⁰ τ from rfl, Rewriting.app_exs, Rew.q_emb]
  rfl

private lemma encodeArithmeticFormulaSymbols_ne_nil {k : ℕ}
    (φ : ArithmeticSemiformula ℕ k) : encodeArithmeticFormulaSymbols φ ≠ [] := by
  induction φ with
  | verum => simp [encodeArithmeticFormulaSymbols]
  | falsum => simp [encodeArithmeticFormulaSymbols]
  | rel r v => rcases r with _ | _ <;> simp [encodeArithmeticFormulaSymbols]
  | nrel r v => rcases r with _ | _ <;> simp [encodeArithmeticFormulaSymbols]
  | and => simp [encodeArithmeticFormulaSymbols]
  | or => simp [encodeArithmeticFormulaSymbols]
  | all => simp [encodeArithmeticFormulaSymbols]
  | exs => simp [encodeArithmeticFormulaSymbols]

private lemma formulaSymbols_length_pos {k : ℕ} {φ : ArithmeticSemiformula ℕ k}
    (h : (encodeArithmeticFormulaSymbols φ).length ≤ 0) : False :=
  encodeArithmeticFormulaSymbols_ne_nil φ
    (List.eq_nil_of_length_eq_zero (Nat.le_zero.mp h))

/-- **Formula completeness at a leaf**: the writing of an embedded semisentence is
accepted at its own binder depth.

*Proof kind:* `P` proved. -/
lemma sourceRun_emb : ∀ {k : ℕ} (τ : ArithmeticSemisentence k) (tail : List ℕ) {fuel : ℕ},
    (encodeArithmeticFormulaSymbols (↑τ : ArithmeticSemiformula ℕ k)).length ≤ fuel →
    sourceRun fuel k
        (encodeArithmeticFormulaSymbols (↑τ : ArithmeticSemiformula ℕ k) ++ tail) =
      some tail := by
  intro k τ
  induction τ with
  | verum =>
      intro tail fuel hfuel
      cases fuel with
      | zero => exact (formulaSymbols_length_pos hfuel).elim
      | succ fuel => simp [coe_verum, encodeArithmeticFormulaSymbols, sourceRun]
  | falsum =>
      intro tail fuel hfuel
      cases fuel with
      | zero => exact (formulaSymbols_length_pos hfuel).elim
      | succ fuel => simp [coe_falsum, encodeArithmeticFormulaSymbols, sourceRun]
  | rel r v =>
      intro tail fuel hfuel
      rcases r with _ | _
      all_goals
        cases fuel with
        | zero => exact (formulaSymbols_length_pos hfuel).elim
        | succ fuel =>
            have hlen :
                (encodeArithmeticTermSymbols
                    (Rew.emb (v 0) : ArithmeticSemiterm ℕ _)).length +
                  (encodeArithmeticTermSymbols
                    (Rew.emb (v 1) : ArithmeticSemiterm ℕ _)).length ≤ fuel := by
              simpa [Semiformula.coe_rel, encodeArithmeticFormulaSymbols] using hfuel
            simp only [Semiformula.coe_rel, encodeArithmeticFormulaSymbols,
              List.cons_append, List.append_assoc, sourceRun]
            rw [if_neg (by norm_num), if_pos (by norm_num),
              sourceTermRun_emb (v 0) _ (by omega), Option.bind_some,
              sourceTermRun_emb (v 1) tail (by omega)]
  | nrel r v =>
      intro tail fuel hfuel
      rcases r with _ | _
      all_goals
        cases fuel with
        | zero => exact (formulaSymbols_length_pos hfuel).elim
        | succ fuel =>
            have hlen :
                (encodeArithmeticTermSymbols
                    (Rew.emb (v 0) : ArithmeticSemiterm ℕ _)).length +
                  (encodeArithmeticTermSymbols
                    (Rew.emb (v 1) : ArithmeticSemiterm ℕ _)).length ≤ fuel := by
              simpa [Semiformula.coe_nrel, encodeArithmeticFormulaSymbols] using hfuel
            simp only [Semiformula.coe_nrel, encodeArithmeticFormulaSymbols,
              List.cons_append, List.append_assoc, sourceRun]
            rw [if_neg (by norm_num), if_pos (by norm_num),
              sourceTermRun_emb (v 0) _ (by omega), Option.bind_some,
              sourceTermRun_emb (v 1) tail (by omega)]
  | and φ ψ ihφ ihψ =>
      intro tail fuel hfuel
      cases fuel with
      | zero => exact (formulaSymbols_length_pos hfuel).elim
      | succ fuel =>
          have hlen :
              (encodeArithmeticFormulaSymbols
                  (Rewriting.emb φ : ArithmeticSemiformula ℕ _)).length +
                (encodeArithmeticFormulaSymbols
                  (Rewriting.emb ψ : ArithmeticSemiformula ℕ _)).length ≤ fuel := by
            simpa [coe_and, encodeArithmeticFormulaSymbols] using hfuel
          simp only [coe_and, encodeArithmeticFormulaSymbols, List.cons_append,
            List.append_assoc, sourceRun]
          rw [if_neg (by norm_num), if_neg (by norm_num), if_pos (by norm_num),
            ihφ _ (by omega), Option.bind_some, ihψ tail (by omega)]
  | or φ ψ ihφ ihψ =>
      intro tail fuel hfuel
      cases fuel with
      | zero => exact (formulaSymbols_length_pos hfuel).elim
      | succ fuel =>
          have hlen :
              (encodeArithmeticFormulaSymbols
                  (Rewriting.emb φ : ArithmeticSemiformula ℕ _)).length +
                (encodeArithmeticFormulaSymbols
                  (Rewriting.emb ψ : ArithmeticSemiformula ℕ _)).length ≤ fuel := by
            simpa [coe_or, encodeArithmeticFormulaSymbols] using hfuel
          simp only [coe_or, encodeArithmeticFormulaSymbols, List.cons_append,
            List.append_assoc, sourceRun]
          rw [if_neg (by norm_num), if_neg (by norm_num), if_pos (by norm_num),
            ihφ _ (by omega), Option.bind_some, ihψ tail (by omega)]
  | all φ ih =>
      intro tail fuel hfuel
      cases fuel with
      | zero => exact (formulaSymbols_length_pos hfuel).elim
      | succ fuel =>
          have hlen :
              (encodeArithmeticFormulaSymbols
                (Rewriting.emb φ : ArithmeticSemiformula ℕ _)).length ≤ fuel := by
            simpa [coe_all', encodeArithmeticFormulaSymbols] using hfuel
          simp only [coe_all', encodeArithmeticFormulaSymbols, List.cons_append, sourceRun]
          rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
            if_pos (by norm_num)]
          exact ih tail hlen
  | exs φ ih =>
      intro tail fuel hfuel
      cases fuel with
      | zero => exact (formulaSymbols_length_pos hfuel).elim
      | succ fuel =>
          have hlen :
              (encodeArithmeticFormulaSymbols
                (Rewriting.emb φ : ArithmeticSemiformula ℕ _)).length ≤ fuel := by
            simpa [coe_exs', encodeArithmeticFormulaSymbols] using hfuel
          simp only [coe_exs', encodeArithmeticFormulaSymbols, List.cons_append, sourceRun]
          rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
            if_pos (by norm_num)]
          exact ih tail hlen

/-- **Source completeness — the gate does not reject genuine axioms.**  Every emitted run
of a source whose compilation is the embedding of a semisentence is accepted, with the
same fuel budget the numeric parser uses
(`ArithSource.parseStructuredArithmeticFormula_sourceTokens`).

*Proof kind:* `P` proved.  The work is propagating `compile s = ↑τ` into the subterms;
`Rewriting.emb` commutes with every connective, and Foundation's `Semiformula.eq_and_iff`
/ `eq_or_iff` / `eq_neg_iff` / `eq_all_iff` invert it. -/
lemma sourceRun_sourceTokens : ∀ {k : ℕ} (s : ArithSource k)
    {τ : ArithmeticSemisentence k},
    ArithSource.compile s = (↑τ : ArithmeticSemiformula ℕ k) →
    ∀ (tail : List ℕ) {fuel : ℕ}, (ArithSource.sourceTokens s).length ≤ fuel →
      sourceRun fuel k (ArithSource.sourceTokens s ++ tail) = some tail := by
  intro k s
  induction s with
  | leaf φ =>
      intro τ hτ tail fuel hfuel
      subst hτ
      exact sourceRun_emb τ tail hfuel
  | and a b iha ihb =>
      intro τ hτ tail fuel hfuel
      obtain ⟨τ₁, τ₂, h₁, h₂, -⟩ := (Semiformula.eq_and_iff Rew.emb).mp hτ.symm
      cases fuel with
      | zero => simp [ArithSource.sourceTokens] at hfuel
      | succ fuel =>
          have hlen : (ArithSource.sourceTokens a).length +
              (ArithSource.sourceTokens b).length ≤ fuel := by
            simpa [ArithSource.sourceTokens] using hfuel
          simp only [ArithSource.sourceTokens, List.cons_append, List.append_assoc, sourceRun]
          rw [if_neg (by norm_num), if_neg (by norm_num), if_pos (by norm_num),
            iha h₁.symm _ (by omega), Option.bind_some, ihb h₂.symm tail (by omega)]
  | or a b iha ihb =>
      intro τ hτ tail fuel hfuel
      obtain ⟨τ₁, τ₂, h₁, h₂, -⟩ := (Semiformula.eq_or_iff Rew.emb).mp hτ.symm
      cases fuel with
      | zero => simp [ArithSource.sourceTokens] at hfuel
      | succ fuel =>
          have hlen : (ArithSource.sourceTokens a).length +
              (ArithSource.sourceTokens b).length ≤ fuel := by
            simpa [ArithSource.sourceTokens] using hfuel
          simp only [ArithSource.sourceTokens, List.cons_append, List.append_assoc, sourceRun]
          rw [if_neg (by norm_num), if_neg (by norm_num), if_pos (by norm_num),
            iha h₁.symm _ (by omega), Option.bind_some, ihb h₂.symm tail (by omega)]
  | all a ih =>
      intro τ hτ tail fuel hfuel
      obtain ⟨τ', h', -⟩ := (Semiformula.eq_all_iff Rew.emb).mp hτ.symm
      rw [Rew.q_emb] at h'
      cases fuel with
      | zero => simp [ArithSource.sourceTokens] at hfuel
      | succ fuel =>
          have hlen : (ArithSource.sourceTokens a).length ≤ fuel := by
            simpa [ArithSource.sourceTokens] using hfuel
          simp only [ArithSource.sourceTokens, List.cons_append, sourceRun]
          rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
            if_pos (by norm_num)]
          exact ih h'.symm tail hlen
  | exs a ih =>
      intro τ hτ tail fuel hfuel
      obtain ⟨τ', h', -⟩ := (Semiformula.eq_exs_iff Rew.emb).mp hτ.symm
      rw [Rew.q_emb] at h'
      cases fuel with
      | zero => simp [ArithSource.sourceTokens] at hfuel
      | succ fuel =>
          have hlen : (ArithSource.sourceTokens a).length ≤ fuel := by
            simpa [ArithSource.sourceTokens] using hfuel
          simp only [ArithSource.sourceTokens, List.cons_append, sourceRun]
          rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
            if_pos (by norm_num)]
          exact ih h'.symm tail hlen
  | not a ih =>
      intro τ hτ tail fuel hfuel
      have ha : ArithSource.compile a = (↑(∼τ) : ArithmeticSemiformula ℕ _) := by
        simp only [LogicalConnective.HomClass.map_neg, ← hτ]
        simp [ArithSource.compile]
      cases fuel with
      | zero => simp [ArithSource.sourceTokens] at hfuel
      | succ fuel =>
          have hlen : (ArithSource.sourceTokens a).length ≤ fuel := by
            simpa [ArithSource.sourceTokens] using hfuel
          simp only [ArithSource.sourceTokens, List.cons_append, sourceRun]
          rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
            if_neg (by norm_num), if_pos (by norm_num)]
          exact ih ha tail hlen
  | imp a b iha ihb =>
      intro τ hτ tail fuel hfuel
      obtain ⟨τ₁, τ₂, h₁, h₂, -⟩ := (Semiformula.eq_neg_iff Rew.emb).mp hτ.symm
      cases fuel with
      | zero => simp [ArithSource.sourceTokens] at hfuel
      | succ fuel =>
          have hlen : (ArithSource.sourceTokens a).length +
              (ArithSource.sourceTokens b).length ≤ fuel := by
            simpa [ArithSource.sourceTokens] using hfuel
          simp only [ArithSource.sourceTokens, List.cons_append, List.append_assoc, sourceRun]
          rw [if_neg (by norm_num), if_neg (by norm_num), if_pos (by norm_num),
            iha h₁.symm _ (by omega), Option.bind_some, ihb h₂.symm tail (by omega)]
  | iff a b iha ihb =>
      intro τ hτ tail fuel hfuel
      rw [ArithSource.compile, Semiformula.iff_eq] at hτ
      obtain ⟨γ₁, γ₂, hg₁, -, -⟩ := (Semiformula.eq_and_iff Rew.emb).mp hτ.symm
      obtain ⟨δ₁, δ₂, hd₁, hd₂, -⟩ := (Semiformula.eq_or_iff Rew.emb).mp hg₁
      have ha : ArithSource.compile a = (↑(∼δ₁) : ArithmeticSemiformula ℕ _) := by
        simp only [LogicalConnective.HomClass.map_neg, hd₁]
        simp
      cases fuel with
      | zero => simp [ArithSource.sourceTokens] at hfuel
      | succ fuel =>
          have hlen : (ArithSource.sourceTokens a).length +
              (ArithSource.sourceTokens b).length ≤ fuel := by
            simpa [ArithSource.sourceTokens] using hfuel
          simp only [ArithSource.sourceTokens, List.cons_append, List.append_assoc, sourceRun]
          rw [if_neg (by norm_num), if_neg (by norm_num), if_pos (by norm_num),
            iha ha _ (by omega), Option.bind_some, ihb hd₂.symm tail (by omega)]

/-! ## Binder levels, and the depth-free reformulation

The primitive-recursion proof below is a single strong recursion on the packed index
`Nat.pair fuel (Encodable.encode ts)`, and the binder depth cannot travel in that index:
it *grows* at a quantifier while the fuel shrinks, and `Nat.pair` is monotone in neither
argument against the other, so the recursive call would not land at a smaller index.  So
the depth is eliminated from the recursion altogether: `termLevelRun` / `sourceLevelRun`
compute, bottom-up, the number of enclosing binders a run *requires* — a quantifier
decrements the level rather than incrementing a depth — and the depth test becomes one
comparison at the top (`sourceTermRun_eq`, `sourceRun_eq`). -/

/-- The bottom-up *level* of a written term: one more than the largest bound-variable
index it uses, `0` if it uses none.  A run is a term at depth `k` exactly when its level
is at most `k`.

*Proof kind:* `Def`. -/
def termLevelRun : ℕ → List ℕ → Option (ℕ × List ℕ)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, t :: rest =>
      if t = 3 then (structuredNatRun fuel rest).map fun p => (p.1 + 1, p.2)
      else if t = 5 then some (0, rest)
      else if t = 6 then some (0, rest)
      else if t = 7 ∨ t = 8 then
        (termLevelRun fuel rest).bind fun p =>
          (termLevelRun fuel p.2).map fun q => (max p.1 q.1, q.2)
      else none

/-- The bottom-up *level* of a written source.  A quantifier consumes one binder, so it
decrements the level of its body.

*Proof kind:* `Def`. -/
def sourceLevelRun : ℕ → List ℕ → Option (ℕ × List ℕ)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, t :: rest =>
      if t = 9 ∨ t = 10 then some (0, rest)
      else if t = 11 ∨ t = 12 ∨ t = 13 ∨ t = 14 then
        (termLevelRun fuel rest).bind fun p =>
          (termLevelRun fuel p.2).map fun q => (max p.1 q.1, q.2)
      else if t = 15 ∨ t = 16 ∨ t = 21 ∨ t = 22 then
        (sourceLevelRun fuel rest).bind fun p =>
          (sourceLevelRun fuel p.2).map fun q => (max p.1 q.1, q.2)
      else if t = 17 ∨ t = 18 then
        (sourceLevelRun fuel rest).map fun p => (p.1 - 1, p.2)
      else if t = 20 then sourceLevelRun fuel rest
      else none

/-- **The depth test commutes with a binary node.**  At a two-child tag both recognizers
have the same shape — run the child, then run the sibling on what it left — so checking
`≤ k` after each child agrees with checking it once against the maximum of the two levels.
This is the only step of `sourceTermRun_eq` and `sourceRun_eq` that does any work, and it
is used three times: at the binary term tags, at the relation tags, and at the binary
source tags.

*Proof kind:* `P` proved. -/
private lemma bind_ite_le_binary {L : List ℕ → Option (ℕ × List ℕ)} {k : ℕ}
    (ts : List ℕ) :
    (((L ts).bind fun p => if p.1 ≤ k then some p.2 else none).bind fun r =>
        (L r).bind fun p => if p.1 ≤ k then some p.2 else none) =
      ((L ts).bind fun p => (L p.2).map fun q => (max p.1 q.1, q.2)).bind fun p =>
        if p.1 ≤ k then some p.2 else none := by
  rcases hp : L ts with _ | p
  · simp
  simp only [Option.bind_some]
  by_cases hpk : p.1 ≤ k
  · simp only [hpk, if_true, Option.bind_some]
    rcases hq : L p.2 with _ | q
    · simp
    simp only [Option.bind_some, Option.map_some]
    by_cases hqk : q.1 ≤ k <;> simp [hqk, hpk]
  · simp only [hpk, if_false, Option.bind_none]
    rcases hq : L p.2 with _ | q
    · simp
    simp only [Option.map_some, Option.bind_some]
    rw [if_neg (by simp; omega)]

/-- **The depth test factors through the level.**

*Proof kind:* `P` proved. -/
lemma sourceTermRun_eq : ∀ (fuel k : ℕ) (ts : List ℕ),
    sourceTermRun fuel k ts =
      (termLevelRun fuel ts).bind fun p => if p.1 ≤ k then some p.2 else none := by
  intro fuel
  induction fuel with
  | zero => intro k ts; simp [sourceTermRun, termLevelRun]
  | succ fuel ih =>
      intro k ts
      rcases ts with _ | ⟨t, rest⟩
      · simp [sourceTermRun, termLevelRun]
      rw [sourceTermRun, termLevelRun]
      by_cases h3 : t = 3
      · simp only [h3, if_true]
        rcases hp : structuredNatRun fuel rest with _ | p <;> simp
      by_cases h5 : t = 5
      · simp [h5]
      by_cases h6 : t = 6
      · simp [h6]
      by_cases h78 : t = 7 ∨ t = 8
      · simp only [h3, h5, h6, h78, if_true, if_false, ih]
        exact bind_ite_le_binary (L := termLevelRun fuel) rest
      · simp [h3, h5, h6, h78]

/-- **The depth test factors through the level**, at the source level.

*Proof kind:* `P` proved. -/
lemma sourceRun_eq : ∀ (fuel k : ℕ) (ts : List ℕ),
    sourceRun fuel k ts =
      (sourceLevelRun fuel ts).bind fun p => if p.1 ≤ k then some p.2 else none := by
  intro fuel
  induction fuel with
  | zero => intro k ts; simp [sourceRun, sourceLevelRun]
  | succ fuel ih =>
      intro k ts
      rcases ts with _ | ⟨t, rest⟩
      · simp [sourceRun, sourceLevelRun]
      rw [sourceRun, sourceLevelRun]
      by_cases h910 : t = 9 ∨ t = 10
      · simp [h910]
      by_cases hrel : t = 11 ∨ t = 12 ∨ t = 13 ∨ t = 14
      · simp only [h910, hrel, if_true, if_false, sourceTermRun_eq]
        exact bind_ite_le_binary (L := termLevelRun fuel) rest
      by_cases hbin : t = 15 ∨ t = 16 ∨ t = 21 ∨ t = 22
      · simp only [h910, hrel, hbin, if_true, if_false, ih]
        exact bind_ite_le_binary (L := sourceLevelRun fuel) rest
      by_cases hq : t = 17 ∨ t = 18
      · simp only [h910, hrel, hbin, hq, if_true, if_false]
        rw [ih (k + 1) rest]
        rcases hp : sourceLevelRun fuel rest with _ | p
        · simp
        simp only [Option.bind_some, Option.map_some]
        by_cases hpk : p.1 ≤ k + 1 <;> simp [hpk]
      by_cases h20 : t = 20
      · simp only [h20, if_true]
        exact ih k rest
      · simp [h910, hrel, hbin, hq, h20]

/-! ## Primitive recursiveness

Each recognizer is metered by fuel, so each is a single strong recursion on the packed
index `Nat.pair fuel (Encodable.encode ts)`, in the shape `Primrec.nat_strong_rec` accepts
(the pattern `Construction/LIACompiler.lean` uses for the numeric parsers). -/

/-! ### Suffix bookkeeping

Each recognizer only ever hands back a suffix of its input, which is what puts the second
lookup of a binary node at a smaller strong-recursion index. -/

private lemma structuredNatRun_suffix : ∀ {fuel : ℕ} {ts : List ℕ} {n : ℕ} {rest : List ℕ},
    structuredNatRun fuel ts = some (n, rest) → rest <:+ ts := fun h => by
  rw [structuredNatRun_shape h]; exact List.suffix_append _ _

private lemma termLevelRun_suffix : ∀ {fuel : ℕ} {ts : List ℕ} {n : ℕ} {rest : List ℕ},
    termLevelRun fuel ts = some (n, rest) → rest <:+ ts := by
  intro fuel
  induction fuel with
  | zero => intro ts n rest h; simp [termLevelRun] at h
  | succ fuel ih =>
      intro ts n rest h
      rcases ts with _ | ⟨t, ts⟩
      · simp [termLevelRun] at h
      rw [termLevelRun] at h
      split_ifs at h with h3 h5 h6 h78
      · rcases hp : structuredNatRun fuel ts with _ | p <;> rw [hp] at h <;> simp at h
        obtain ⟨-, rfl⟩ := h
        exact (structuredNatRun_suffix hp).trans (List.suffix_cons t ts)
      · obtain ⟨-, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
        exact List.suffix_cons t ts
      · obtain ⟨-, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
        exact List.suffix_cons t ts
      · rcases hp : termLevelRun fuel ts with _ | p
        · rw [hp] at h; simp at h
        rw [hp] at h
        simp only [Option.bind_some] at h
        rcases hq : termLevelRun fuel p.2 with _ | q
        · rw [hq] at h; simp at h
        rw [hq] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact ((ih hq).trans (ih hp)).trans (List.suffix_cons t ts)

private lemma sourceLevelRun_suffix : ∀ {fuel : ℕ} {ts : List ℕ} {n : ℕ} {rest : List ℕ},
    sourceLevelRun fuel ts = some (n, rest) → rest <:+ ts := by
  intro fuel
  induction fuel with
  | zero => intro ts n rest h; simp [sourceLevelRun] at h
  | succ fuel ih =>
      intro ts n rest h
      rcases ts with _ | ⟨t, ts⟩
      · simp [sourceLevelRun] at h
      rw [sourceLevelRun] at h
      split_ifs at h with h910 hrel hbin hquant h20
      · obtain ⟨-, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
        exact List.suffix_cons t ts
      · rcases hp : termLevelRun fuel ts with _ | p
        · rw [hp] at h; simp at h
        rw [hp] at h
        simp only [Option.bind_some] at h
        rcases hq : termLevelRun fuel p.2 with _ | q
        · rw [hq] at h; simp at h
        rw [hq] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact ((termLevelRun_suffix hq).trans (termLevelRun_suffix hp)).trans
          (List.suffix_cons t ts)
      · rcases hp : sourceLevelRun fuel ts with _ | p
        · rw [hp] at h; simp at h
        rw [hp] at h
        simp only [Option.bind_some] at h
        rcases hq : sourceLevelRun fuel p.2 with _ | q
        · rw [hq] at h; simp at h
        rw [hq] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact ((ih hq).trans (ih hp)).trans (List.suffix_cons t ts)
      · rcases hp : sourceLevelRun fuel ts with _ | p <;> rw [hp] at h <;> simp at h
        obtain ⟨-, rfl⟩ := h
        exact (ih hp).trans (List.suffix_cons t ts)
      · exact (ih h).trans (List.suffix_cons t ts)

/-! ### Strong recursion -/

attribute [local irreducible] Nat.sqrt

private lemma level_smaller_index {m fuel t : ℕ} {rest : List ℕ}
    (hfuel : m.unpair.1 = fuel + 1)
    (hts : Denumerable.ofNat (List ℕ) m.unpair.2 = t :: rest) :
    Nat.pair fuel (Encodable.encode rest) < m := by
  have hm2 : Encodable.encode (t :: rest) = m.unpair.2 := by
    rw [← hts]; exact Denumerable.encode_ofNat _
  calc
    Nat.pair fuel (Encodable.encode rest) ≤
        Nat.pair fuel (Encodable.encode (t :: rest)) :=
      pair_le_pair_right' fuel (le_of_lt (encode_lt_encode_cons t rest))
    _ < Nat.pair (fuel + 1) (Encodable.encode (t :: rest)) :=
      Nat.pair_lt_pair_left _ (Nat.lt_succ_self fuel)
    _ = m := by rw [hm2, ← hfuel, Nat.pair_unpair]

private abbrev RCtx := (List (Option (ℕ × List ℕ)) × ℕ) × (ℕ × List ℕ)

private def natRunF (m : ℕ) : Option (ℕ × List ℕ) :=
  structuredNatRun m.unpair.1 (Denumerable.ofNat (List ℕ) m.unpair.2)

private def natRunGCore (m : ℕ) (look : ℕ → Option (ℕ × List ℕ)) :
    Option (ℕ × List ℕ) :=
  match m.unpair.1, Denumerable.ofNat (List ℕ) m.unpair.2 with
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, t :: rest =>
      if t = 0 then some (0, rest)
      else if t = 1 then
        (look (Nat.pair fuel (Encodable.encode rest))).bind fun p =>
          if p.1 = 0 then none else some (2 * p.1, p.2)
      else if t = 2 then
        (look (Nat.pair fuel (Encodable.encode rest))).map fun p => (2 * p.1 + 1, p.2)
      else none

private lemma natRunGCore_spec (m : ℕ) (look : ℕ → Option (ℕ × List ℕ))
    (hlook : ∀ i, i < m → look i = natRunF i) : natRunGCore m look = natRunF m := by
  rw [natRunGCore, natRunF]
  rcases hf : m.unpair.1 with _ | fuel
  · rfl
  rcases hs : Denumerable.ofNat (List ℕ) m.unpair.2 with _ | ⟨t, rest⟩
  · rfl
  simp only [structuredNatRun]
  by_cases h0 : t = 0 <;> simp only [h0, if_true, if_false]
  by_cases h1 : t = 1 <;> simp only [h1, if_true, if_false]
  · rw [hlook _ (level_smaller_index hf hs), natRunF, Nat.unpair_pair,
      Denumerable.ofNat_encode]
  by_cases h2 : t = 2 <;> simp only [h2, if_true, if_false]
  rw [hlook _ (level_smaller_index hf hs), natRunF, Nat.unpair_pair,
    Denumerable.ofNat_encode]

private def natRunG (prev : List (Option (ℕ × List ℕ))) :
    Option (Option (ℕ × List ℕ)) :=
  some (natRunGCore prev.length fun i => (prev[i]?).getD none)

private lemma natRunG_spec (m : ℕ) :
    natRunG ((List.range m).map natRunF) = some (natRunF m) := by
  rw [natRunG, show ((List.range m).map natRunF).length = m from by simp]
  congr 1
  refine natRunGCore_spec m _ fun i hi => ?_
  have hib : i < ((List.range m).map natRunF).length := by simpa using hi
  rw [List.getElem?_eq_getElem hib, Option.getD_some, List.getElem_map,
    List.getElem_range]

private lemma natRunG_prim : Primrec natRunG := by
  have hfuel : Primrec fun prev : List (Option (ℕ × List ℕ)) =>
      prev.length.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.list_length)
  have hts0 : Primrec fun p : List (Option (ℕ × List ℕ)) × ℕ =>
      Denumerable.ofNat (List ℕ) p.1.length.unpair.2 :=
    (Primrec.ofNat (List ℕ)).comp
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.list_length.comp Primrec.fst)))
  have hprev : Primrec fun x : RCtx => x.1.1 := Primrec.fst.comp Primrec.fst
  have hfuel' : Primrec fun x : RCtx => x.1.2 := Primrec.snd.comp Primrec.fst
  have ht : Primrec fun x : RCtx => x.2.1 := Primrec.fst.comp Primrec.snd
  have hrest : Primrec fun x : RCtx => x.2.2 := Primrec.snd.comp Primrec.snd
  have hlook : Primrec fun x : RCtx =>
      ((x.1.1[Nat.pair x.1.2 (Encodable.encode x.2.2)]?).getD none) :=
    Primrec.option_getD.comp
      (Primrec.list_getElem?.comp hprev
        (Primrec₂.natPair.comp hfuel' (Primrec.encode.comp hrest)))
      (Primrec.const none)
  have hzero : Primrec fun x : RCtx => (some (0, x.2.2) : Option (ℕ × List ℕ)) :=
    Primrec.option_some.comp ((Primrec.const 0).pair hrest)
  have heven : Primrec fun x : RCtx =>
      ((x.1.1[Nat.pair x.1.2 (Encodable.encode x.2.2)]?).getD none).bind
        fun p => if p.1 = 0 then none else some (2 * p.1, p.2) := by
    refine Primrec.option_bind hlook ?_
    exact (Primrec.ite
      (PrimrecRel.comp Primrec.eq (Primrec.fst.comp Primrec.snd) (Primrec.const 0))
      (Primrec.const none)
      (Primrec.option_some.comp
        ((Primrec.nat_mul.comp (Primrec.const 2)
          (Primrec.fst.comp Primrec.snd)).pair (Primrec.snd.comp Primrec.snd)))).to₂
  have hodd : Primrec fun x : RCtx =>
      ((x.1.1[Nat.pair x.1.2 (Encodable.encode x.2.2)]?).getD none).map
        fun p => (2 * p.1 + 1, p.2) :=
    Primrec.option_map hlook
      ((Primrec.succ.comp
        (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.fst.comp Primrec.snd))).pair
        (Primrec.snd.comp Primrec.snd)).to₂
  have heqt : ∀ k : ℕ, PrimrecPred fun x : RCtx => x.2.1 = k := fun k =>
    PrimrecRel.comp Primrec.eq ht (Primrec.const k)
  have hbody : Primrec fun x : RCtx =>
      if x.2.1 = 0 then some (0, x.2.2)
      else if x.2.1 = 1 then
        ((x.1.1[Nat.pair x.1.2 (Encodable.encode x.2.2)]?).getD none).bind
          fun p => if p.1 = 0 then none else some (2 * p.1, p.2)
      else if x.2.1 = 2 then
        ((x.1.1[Nat.pair x.1.2 (Encodable.encode x.2.2)]?).getD none).map
          fun p => (2 * p.1 + 1, p.2)
      else none :=
    Primrec.ite (heqt 0) hzero <|
      Primrec.ite (heqt 1) heven <| Primrec.ite (heqt 2) hodd (Primrec.const none)
  have hinner : Primrec fun p : List (Option (ℕ × List ℕ)) × ℕ =>
      match Denumerable.ofNat (List ℕ) p.1.length.unpair.2 with
      | [] => (none : Option (ℕ × List ℕ))
      | t :: rest =>
          if t = 0 then some (0, rest)
          else if t = 1 then
            ((p.1[Nat.pair p.2 (Encodable.encode rest)]?).getD none).bind
              fun (q : ℕ × List ℕ) => if q.1 = 0 then none else some (2 * q.1, q.2)
          else if t = 2 then
            ((p.1[Nat.pair p.2 (Encodable.encode rest)]?).getD none).map
              fun (q : ℕ × List ℕ) => (2 * q.1 + 1, q.2)
          else none :=
    (Primrec.list_casesOn hts0 (Primrec.const none) hbody.to₂).of_eq fun p => by
      rcases Denumerable.ofNat (List ℕ) p.1.length.unpair.2 with _ | ⟨t, rest⟩ <;> rfl
  refine (Primrec.option_some.comp
    (Primrec.nat_casesOn hfuel (Primrec.const none) hinner.to₂)).of_eq fun prev => ?_
  rw [natRunG]
  rcases hf : prev.length.unpair.1 with _ | fuel
  · simp [natRunGCore, hf]
  rcases hs : Denumerable.ofNat (List ℕ) prev.length.unpair.2 with _ | ⟨t, rest⟩
  · simp [natRunGCore, hf, hs]
  simp [natRunGCore, hf, hs]

/-- **The canonical nat recognizer is primitive recursive.**

*Proof kind:* `C` composition, over `Primrec.nat_strong_rec`. -/
lemma structuredNatRun_prim : Primrec₂ structuredNatRun := by
  have hF : Primrec₂ (fun (_ : Unit) => natRunF) :=
    Primrec.nat_strong_rec _ (natRunG_prim.comp Primrec.snd).to₂ fun _ n => natRunG_spec n
  have hF1 : Primrec natRunF := hF.comp (Primrec.const ()) Primrec.id
  have h2 : Primrec fun p : ℕ × List ℕ =>
      natRunF (Nat.pair p.1 (Encodable.encode p.2)) :=
    hF1.comp (Primrec₂.natPair.comp Primrec.fst (Primrec.encode.comp Primrec.snd))
  exact h2.to₂.of_eq fun fuel ts => by
    rw [natRunF, Nat.unpair_pair, Denumerable.ofNat_encode]

private def termLevelF (m : ℕ) : Option (ℕ × List ℕ) :=
  termLevelRun m.unpair.1 (Denumerable.ofNat (List ℕ) m.unpair.2)

private def termLevelGCore (m : ℕ) (look : ℕ → Option (ℕ × List ℕ)) :
    Option (ℕ × List ℕ) :=
  match m.unpair.1, Denumerable.ofNat (List ℕ) m.unpair.2 with
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, t :: rest =>
      if t = 3 then (structuredNatRun fuel rest).map fun p => (p.1 + 1, p.2)
      else if t = 5 then some (0, rest)
      else if t = 6 then some (0, rest)
      else if t = 7 ∨ t = 8 then
        (look (Nat.pair fuel (Encodable.encode rest))).bind fun p =>
          (look (Nat.pair fuel (Encodable.encode p.2))).map fun q => (max p.1 q.1, q.2)
      else none

private lemma termLevelGCore_spec (m : ℕ) (look : ℕ → Option (ℕ × List ℕ))
    (hlook : ∀ i, i < m → look i = termLevelF i) :
    termLevelGCore m look = termLevelF m := by
  rw [termLevelGCore, termLevelF]
  rcases hf : m.unpair.1 with _ | fuel
  · rfl
  rcases hs : Denumerable.ofNat (List ℕ) m.unpair.2 with _ | ⟨t, rest⟩
  · rfl
  simp only [termLevelRun]
  by_cases h3 : t = 3 <;> simp only [h3, if_true, if_false]
  by_cases h5 : t = 5 <;> simp only [h5, if_true, if_false]
  by_cases h6 : t = 6 <;> simp only [h6, if_true, if_false]
  by_cases hb : t = 7 ∨ t = 8 <;> simp only [hb, if_true, if_false]
  rw [hlook _ (level_smaller_index hf hs), termLevelF, Nat.unpair_pair,
    Denumerable.ofNat_encode]
  rcases hp : termLevelRun fuel rest with _ | p
  · rfl
  simp only [Option.bind_some]
  have hpSuffix := termLevelRun_suffix hp
  have hidx : Nat.pair fuel (Encodable.encode p.2) < m := by
    calc
      Nat.pair fuel (Encodable.encode p.2) ≤ Nat.pair fuel (Encodable.encode rest) :=
        pair_le_pair_right' fuel (encode_le_of_suffix hpSuffix)
      _ < m := level_smaller_index hf hs
  rw [hlook _ hidx, termLevelF, Nat.unpair_pair, Denumerable.ofNat_encode]

private def termLevelG (prev : List (Option (ℕ × List ℕ))) :
    Option (Option (ℕ × List ℕ)) :=
  some (termLevelGCore prev.length fun i => (prev[i]?).getD none)

private lemma termLevelG_spec (m : ℕ) :
    termLevelG ((List.range m).map termLevelF) = some (termLevelF m) := by
  rw [termLevelG, show ((List.range m).map termLevelF).length = m from by simp]
  congr 1
  refine termLevelGCore_spec m _ fun i hi => ?_
  have hib : i < ((List.range m).map termLevelF).length := by simpa using hi
  rw [List.getElem?_eq_getElem hib, Option.getD_some, List.getElem_map,
    List.getElem_range]

private lemma termLevelG_prim : Primrec termLevelG := by
  have hfuel : Primrec fun prev : List (Option (ℕ × List ℕ)) =>
      prev.length.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.list_length)
  have hts0 : Primrec fun p : List (Option (ℕ × List ℕ)) × ℕ =>
      Denumerable.ofNat (List ℕ) p.1.length.unpair.2 :=
    (Primrec.ofNat (List ℕ)).comp
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.list_length.comp Primrec.fst)))
  have hprev : Primrec fun x : RCtx => x.1.1 := Primrec.fst.comp Primrec.fst
  have hfuel' : Primrec fun x : RCtx => x.1.2 := Primrec.snd.comp Primrec.fst
  have ht : Primrec fun x : RCtx => x.2.1 := Primrec.fst.comp Primrec.snd
  have hrest : Primrec fun x : RCtx => x.2.2 := Primrec.snd.comp Primrec.snd
  have hnat : Primrec fun x : RCtx =>
      (structuredNatRun x.1.2 x.2.2).map fun p => (p.1 + 1, p.2) :=
    Primrec.option_map (structuredNatRun_prim.comp hfuel' hrest)
      ((Primrec.succ.comp (Primrec.fst.comp Primrec.snd)).pair
        (Primrec.snd.comp Primrec.snd)).to₂
  have hconst : Primrec fun x : RCtx => (some (0, x.2.2) : Option (ℕ × List ℕ)) :=
    Primrec.option_some.comp ((Primrec.const 0).pair hrest)
  have hlook1 : Primrec fun x : RCtx =>
      ((x.1.1[Nat.pair x.1.2 (Encodable.encode x.2.2)]?).getD none) :=
    Primrec.option_getD.comp
      (Primrec.list_getElem?.comp hprev
        (Primrec₂.natPair.comp hfuel' (Primrec.encode.comp hrest)))
      (Primrec.const none)
  have hlook2 : Primrec fun y : RCtx × (ℕ × List ℕ) =>
      ((y.1.1.1[Nat.pair y.1.1.2 (Encodable.encode y.2.2)]?).getD none) :=
    Primrec.option_getD.comp
      (Primrec.list_getElem?.comp (hprev.comp Primrec.fst)
        (Primrec₂.natPair.comp (hfuel'.comp Primrec.fst)
          (Primrec.encode.comp (Primrec.snd.comp Primrec.snd))))
      (Primrec.const none)
  have hmax : Primrec fun z : (RCtx × (ℕ × List ℕ)) × (ℕ × List ℕ) =>
      (max z.1.2.1 z.2.1, z.2.2) :=
    (Primrec.nat_max.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.fst.comp Primrec.snd)).pair (Primrec.snd.comp Primrec.snd)
  have hbin : Primrec fun x : RCtx =>
      ((x.1.1[Nat.pair x.1.2 (Encodable.encode x.2.2)]?).getD none).bind fun p =>
        ((x.1.1[Nat.pair x.1.2 (Encodable.encode p.2)]?).getD none).map fun q =>
          (max p.1 q.1, q.2) :=
    Primrec.option_bind hlook1 (Primrec.option_map hlook2 hmax.to₂).to₂
  have heqt : ∀ k : ℕ, PrimrecPred fun x : RCtx => x.2.1 = k := fun k =>
    PrimrecRel.comp Primrec.eq ht (Primrec.const k)
  have hbody : Primrec fun x : RCtx =>
      if x.2.1 = 3 then (structuredNatRun x.1.2 x.2.2).map fun p => (p.1 + 1, p.2)
      else if x.2.1 = 5 then some (0, x.2.2)
      else if x.2.1 = 6 then some (0, x.2.2)
      else if x.2.1 = 7 ∨ x.2.1 = 8 then
        ((x.1.1[Nat.pair x.1.2 (Encodable.encode x.2.2)]?).getD none).bind fun p =>
          ((x.1.1[Nat.pair x.1.2 (Encodable.encode p.2)]?).getD none).map fun q =>
            (max p.1 q.1, q.2)
      else none :=
    Primrec.ite (heqt 3) hnat <| Primrec.ite (heqt 5) hconst <|
      Primrec.ite (heqt 6) hconst <|
        Primrec.ite ((heqt 7).or (heqt 8)) hbin (Primrec.const none)
  have hinner : Primrec fun p : List (Option (ℕ × List ℕ)) × ℕ =>
      match Denumerable.ofNat (List ℕ) p.1.length.unpair.2 with
      | [] => (none : Option (ℕ × List ℕ))
      | t :: rest =>
          if t = 3 then
            (structuredNatRun p.2 rest).map fun (q : ℕ × List ℕ) => (q.1 + 1, q.2)
          else if t = 5 then some (0, rest)
          else if t = 6 then some (0, rest)
          else if t = 7 ∨ t = 8 then
            ((p.1[Nat.pair p.2 (Encodable.encode rest)]?).getD none).bind
                fun (q : ℕ × List ℕ) =>
              ((p.1[Nat.pair p.2 (Encodable.encode q.2)]?).getD none).map
                fun (r : ℕ × List ℕ) => (max q.1 r.1, r.2)
          else none :=
    (Primrec.list_casesOn hts0 (Primrec.const none) hbody.to₂).of_eq fun p => by
      rcases Denumerable.ofNat (List ℕ) p.1.length.unpair.2 with _ | ⟨t, rest⟩ <;> rfl
  refine (Primrec.option_some.comp
    (Primrec.nat_casesOn hfuel (Primrec.const none) hinner.to₂)).of_eq fun prev => ?_
  rw [termLevelG]
  rcases hf : prev.length.unpair.1 with _ | fuel
  · simp [termLevelGCore, hf]
  rcases hs : Denumerable.ofNat (List ℕ) prev.length.unpair.2 with _ | ⟨t, rest⟩
  · simp [termLevelGCore, hf, hs]
  simp [termLevelGCore, hf, hs]

/-- **The term-level recognizer is primitive recursive.**

*Proof kind:* `C` composition, over `Primrec.nat_strong_rec`. -/
lemma termLevelRun_prim : Primrec₂ termLevelRun := by
  have hF : Primrec₂ (fun (_ : Unit) => termLevelF) :=
    Primrec.nat_strong_rec _ (termLevelG_prim.comp Primrec.snd).to₂
      fun _ n => termLevelG_spec n
  have hF1 : Primrec termLevelF := hF.comp (Primrec.const ()) Primrec.id
  have h2 : Primrec fun p : ℕ × List ℕ =>
      termLevelF (Nat.pair p.1 (Encodable.encode p.2)) :=
    hF1.comp (Primrec₂.natPair.comp Primrec.fst (Primrec.encode.comp Primrec.snd))
  exact h2.to₂.of_eq fun fuel ts => by
    rw [termLevelF, Nat.unpair_pair, Denumerable.ofNat_encode]

private def sourceLevelF (m : ℕ) : Option (ℕ × List ℕ) :=
  sourceLevelRun m.unpair.1 (Denumerable.ofNat (List ℕ) m.unpair.2)

private def sourceLevelGCore (m : ℕ) (look : ℕ → Option (ℕ × List ℕ)) :
    Option (ℕ × List ℕ) :=
  match m.unpair.1, Denumerable.ofNat (List ℕ) m.unpair.2 with
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, t :: rest =>
      if t = 9 ∨ t = 10 then some (0, rest)
      else if t = 11 ∨ t = 12 ∨ t = 13 ∨ t = 14 then
        (termLevelRun fuel rest).bind fun p =>
          (termLevelRun fuel p.2).map fun q => (max p.1 q.1, q.2)
      else if t = 15 ∨ t = 16 ∨ t = 21 ∨ t = 22 then
        (look (Nat.pair fuel (Encodable.encode rest))).bind fun p =>
          (look (Nat.pair fuel (Encodable.encode p.2))).map fun q => (max p.1 q.1, q.2)
      else if t = 17 ∨ t = 18 then
        (look (Nat.pair fuel (Encodable.encode rest))).map fun p => (p.1 - 1, p.2)
      else if t = 20 then look (Nat.pair fuel (Encodable.encode rest))
      else none

private lemma sourceLevelGCore_spec (m : ℕ) (look : ℕ → Option (ℕ × List ℕ))
    (hlook : ∀ i, i < m → look i = sourceLevelF i) :
    sourceLevelGCore m look = sourceLevelF m := by
  rw [sourceLevelGCore, sourceLevelF]
  rcases hf : m.unpair.1 with _ | fuel
  · rfl
  rcases hs : Denumerable.ofNat (List ℕ) m.unpair.2 with _ | ⟨t, rest⟩
  · rfl
  simp only [sourceLevelRun]
  by_cases h910 : t = 9 ∨ t = 10 <;> simp only [h910, if_true, if_false]
  by_cases hrel : t = 11 ∨ t = 12 ∨ t = 13 ∨ t = 14 <;>
    simp only [hrel, if_true, if_false]
  by_cases hbin : t = 15 ∨ t = 16 ∨ t = 21 ∨ t = 22 <;>
    simp only [hbin, if_true, if_false]
  · rw [hlook _ (level_smaller_index hf hs), sourceLevelF, Nat.unpair_pair,
      Denumerable.ofNat_encode]
    rcases hp : sourceLevelRun fuel rest with _ | p
    · rfl
    simp only [Option.bind_some]
    have hidx : Nat.pair fuel (Encodable.encode p.2) < m := by
      calc
        Nat.pair fuel (Encodable.encode p.2) ≤
            Nat.pair fuel (Encodable.encode rest) :=
          pair_le_pair_right' fuel (encode_le_of_suffix (sourceLevelRun_suffix hp))
        _ < m := level_smaller_index hf hs
    rw [hlook _ hidx, sourceLevelF, Nat.unpair_pair, Denumerable.ofNat_encode]
  by_cases hq : t = 17 ∨ t = 18 <;> simp only [hq, if_true, if_false]
  · rw [hlook _ (level_smaller_index hf hs), sourceLevelF, Nat.unpair_pair,
      Denumerable.ofNat_encode]
  by_cases h20 : t = 20 <;> simp only [h20, if_true, if_false]
  rw [hlook _ (level_smaller_index hf hs), sourceLevelF, Nat.unpair_pair,
    Denumerable.ofNat_encode]

private def sourceLevelG (prev : List (Option (ℕ × List ℕ))) :
    Option (Option (ℕ × List ℕ)) :=
  some (sourceLevelGCore prev.length fun i => (prev[i]?).getD none)

private lemma sourceLevelG_spec (m : ℕ) :
    sourceLevelG ((List.range m).map sourceLevelF) = some (sourceLevelF m) := by
  rw [sourceLevelG, show ((List.range m).map sourceLevelF).length = m from by simp]
  congr 1
  refine sourceLevelGCore_spec m _ fun i hi => ?_
  have hib : i < ((List.range m).map sourceLevelF).length := by simpa using hi
  rw [List.getElem?_eq_getElem hib, Option.getD_some, List.getElem_map,
    List.getElem_range]

private lemma sourceLevelG_prim : Primrec sourceLevelG := by
  have hfuel : Primrec fun prev : List (Option (ℕ × List ℕ)) =>
      prev.length.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.list_length)
  have hts0 : Primrec fun p : List (Option (ℕ × List ℕ)) × ℕ =>
      Denumerable.ofNat (List ℕ) p.1.length.unpair.2 :=
    (Primrec.ofNat (List ℕ)).comp
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.list_length.comp Primrec.fst)))
  have hprev : Primrec fun x : RCtx => x.1.1 := Primrec.fst.comp Primrec.fst
  have hfuel' : Primrec fun x : RCtx => x.1.2 := Primrec.snd.comp Primrec.fst
  have ht : Primrec fun x : RCtx => x.2.1 := Primrec.fst.comp Primrec.snd
  have hrest : Primrec fun x : RCtx => x.2.2 := Primrec.snd.comp Primrec.snd
  have hconst : Primrec fun x : RCtx => (some (0, x.2.2) : Option (ℕ × List ℕ)) :=
    Primrec.option_some.comp ((Primrec.const 0).pair hrest)
  have hlook1 : Primrec fun x : RCtx =>
      ((x.1.1[Nat.pair x.1.2 (Encodable.encode x.2.2)]?).getD none) :=
    Primrec.option_getD.comp
      (Primrec.list_getElem?.comp hprev
        (Primrec₂.natPair.comp hfuel' (Primrec.encode.comp hrest)))
      (Primrec.const none)
  have hlook2 : Primrec fun y : RCtx × (ℕ × List ℕ) =>
      ((y.1.1.1[Nat.pair y.1.1.2 (Encodable.encode y.2.2)]?).getD none) :=
    Primrec.option_getD.comp
      (Primrec.list_getElem?.comp (hprev.comp Primrec.fst)
        (Primrec₂.natPair.comp (hfuel'.comp Primrec.fst)
          (Primrec.encode.comp (Primrec.snd.comp Primrec.snd))))
      (Primrec.const none)
  have hmax : Primrec fun z : (RCtx × (ℕ × List ℕ)) × (ℕ × List ℕ) =>
      (max z.1.2.1 z.2.1, z.2.2) :=
    (Primrec.nat_max.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.fst.comp Primrec.snd)).pair (Primrec.snd.comp Primrec.snd)
  have hterm1 : Primrec fun x : RCtx => termLevelRun x.1.2 x.2.2 :=
    termLevelRun_prim.comp hfuel' hrest
  have hterm2 : Primrec fun y : RCtx × (ℕ × List ℕ) => termLevelRun y.1.1.2 y.2.2 :=
    termLevelRun_prim.comp (hfuel'.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)
  have hrelb : Primrec fun x : RCtx =>
      (termLevelRun x.1.2 x.2.2).bind fun p =>
        (termLevelRun x.1.2 p.2).map fun q => (max p.1 q.1, q.2) :=
    Primrec.option_bind hterm1 (Primrec.option_map hterm2 hmax.to₂).to₂
  have hbin : Primrec fun x : RCtx =>
      ((x.1.1[Nat.pair x.1.2 (Encodable.encode x.2.2)]?).getD none).bind fun p =>
        ((x.1.1[Nat.pair x.1.2 (Encodable.encode p.2)]?).getD none).map fun q =>
          (max p.1 q.1, q.2) :=
    Primrec.option_bind hlook1 (Primrec.option_map hlook2 hmax.to₂).to₂
  have hquant : Primrec fun x : RCtx =>
      ((x.1.1[Nat.pair x.1.2 (Encodable.encode x.2.2)]?).getD none).map
        fun p => (p.1 - 1, p.2) :=
    Primrec.option_map hlook1
      ((Primrec.nat_sub.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1)).pair
        (Primrec.snd.comp Primrec.snd)).to₂
  have heqt : ∀ k : ℕ, PrimrecPred fun x : RCtx => x.2.1 = k := fun k =>
    PrimrecRel.comp Primrec.eq ht (Primrec.const k)
  have hbody : Primrec fun x : RCtx =>
      if x.2.1 = 9 ∨ x.2.1 = 10 then some (0, x.2.2)
      else if x.2.1 = 11 ∨ x.2.1 = 12 ∨ x.2.1 = 13 ∨ x.2.1 = 14 then
        (termLevelRun x.1.2 x.2.2).bind fun p =>
          (termLevelRun x.1.2 p.2).map fun q => (max p.1 q.1, q.2)
      else if x.2.1 = 15 ∨ x.2.1 = 16 ∨ x.2.1 = 21 ∨ x.2.1 = 22 then
        ((x.1.1[Nat.pair x.1.2 (Encodable.encode x.2.2)]?).getD none).bind fun p =>
          ((x.1.1[Nat.pair x.1.2 (Encodable.encode p.2)]?).getD none).map fun q =>
            (max p.1 q.1, q.2)
      else if x.2.1 = 17 ∨ x.2.1 = 18 then
        ((x.1.1[Nat.pair x.1.2 (Encodable.encode x.2.2)]?).getD none).map
          fun p => (p.1 - 1, p.2)
      else if x.2.1 = 20 then
        ((x.1.1[Nat.pair x.1.2 (Encodable.encode x.2.2)]?).getD none)
      else none :=
    Primrec.ite ((heqt 9).or (heqt 10)) hconst <|
      Primrec.ite ((heqt 11).or ((heqt 12).or ((heqt 13).or (heqt 14)))) hrelb <|
        Primrec.ite ((heqt 15).or ((heqt 16).or ((heqt 21).or (heqt 22)))) hbin <|
          Primrec.ite ((heqt 17).or (heqt 18)) hquant <|
            Primrec.ite (heqt 20) hlook1 (Primrec.const none)
  have hinner : Primrec fun p : List (Option (ℕ × List ℕ)) × ℕ =>
      match Denumerable.ofNat (List ℕ) p.1.length.unpair.2 with
      | [] => (none : Option (ℕ × List ℕ))
      | t :: rest =>
          if t = 9 ∨ t = 10 then some (0, rest)
          else if t = 11 ∨ t = 12 ∨ t = 13 ∨ t = 14 then
            (termLevelRun p.2 rest).bind fun (q : ℕ × List ℕ) =>
              (termLevelRun p.2 q.2).map fun (r : ℕ × List ℕ) => (max q.1 r.1, r.2)
          else if t = 15 ∨ t = 16 ∨ t = 21 ∨ t = 22 then
            ((p.1[Nat.pair p.2 (Encodable.encode rest)]?).getD none).bind
                fun (q : ℕ × List ℕ) =>
              ((p.1[Nat.pair p.2 (Encodable.encode q.2)]?).getD none).map
                fun (r : ℕ × List ℕ) => (max q.1 r.1, r.2)
          else if t = 17 ∨ t = 18 then
            ((p.1[Nat.pair p.2 (Encodable.encode rest)]?).getD none).map
              fun (q : ℕ × List ℕ) => (q.1 - 1, q.2)
          else if t = 20 then ((p.1[Nat.pair p.2 (Encodable.encode rest)]?).getD none)
          else none :=
    (Primrec.list_casesOn hts0 (Primrec.const none) hbody.to₂).of_eq fun p => by
      rcases Denumerable.ofNat (List ℕ) p.1.length.unpair.2 with _ | ⟨t, rest⟩ <;> rfl
  refine (Primrec.option_some.comp
    (Primrec.nat_casesOn hfuel (Primrec.const none) hinner.to₂)).of_eq fun prev => ?_
  rw [sourceLevelG]
  rcases hf : prev.length.unpair.1 with _ | fuel
  · simp [sourceLevelGCore, hf]
  rcases hs : Denumerable.ofNat (List ℕ) prev.length.unpair.2 with _ | ⟨t, rest⟩
  · simp [sourceLevelGCore, hf, hs]
  simp [sourceLevelGCore, hf, hs]

/-- **The source-level recognizer is primitive recursive.**

*Proof kind:* `C` composition, over `Primrec.nat_strong_rec`. -/
lemma sourceLevelRun_prim : Primrec₂ sourceLevelRun := by
  have hF : Primrec₂ (fun (_ : Unit) => sourceLevelF) :=
    Primrec.nat_strong_rec _ (sourceLevelG_prim.comp Primrec.snd).to₂
      fun _ n => sourceLevelG_spec n
  have hF1 : Primrec sourceLevelF := hF.comp (Primrec.const ()) Primrec.id
  have h2 : Primrec fun p : ℕ × List ℕ =>
      sourceLevelF (Nat.pair p.1 (Encodable.encode p.2)) :=
    hF1.comp (Primrec₂.natPair.comp Primrec.fst (Primrec.encode.comp Primrec.snd))
  exact h2.to₂.of_eq fun fuel ts => by
    rw [sourceLevelF, Nat.unpair_pair, Denumerable.ofNat_encode]

/-- **The source recognizer is primitive recursive**, jointly in its fuel, its binder
depth and its input.  This is what lets the `thm:incons` window gate a machine's output on
"this run really writes a sentence" inside the emission calculus.

*Proof kind:* `C` composition, through `sourceRun_eq`. -/
lemma sourceRun_prim :
    Primrec fun x : (ℕ × ℕ) × List ℕ => sourceRun x.1.1 x.1.2 x.2 := by
  have h : Primrec fun x : (ℕ × ℕ) × List ℕ =>
      (sourceLevelRun x.1.1 x.2).bind fun p =>
        if p.1 ≤ x.1.2 then some p.2 else none := by
    refine Primrec.option_bind
      (sourceLevelRun_prim.comp (Primrec.fst.comp Primrec.fst) Primrec.snd) ?_
    exact (Primrec.ite
      (PrimrecRel.comp Primrec.nat_le (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.option_some.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.const none)).to₂
  exact h.of_eq fun x => (sourceRun_eq x.1.1 x.1.2 x.2).symm

/-- The decision "this whole run is a written closed source", in the form the gate uses:
own length as fuel, binder depth `0`, nothing left over.

*Proof kind:* `C` composition. -/
lemma sourceRun_full_prim :
    Primrec fun ts : List ℕ => decide (sourceRun ts.length 0 ts = some []) := by
  have h : PrimrecPred fun ts : List ℕ => sourceRun ts.length 0 ts = some [] :=
    PrimrecRel.comp Primrec.eq
      (sourceRun_prim.comp
        ((Primrec.list_length.pair (Primrec.const 0)).pair Primrec.id))
      (Primrec.const (some []))
  exact (Primrec.ite h (Primrec.const true) (Primrec.const false)).of_eq fun ts => by
    by_cases hh : sourceRun ts.length 0 ts = some [] <;> simp [hh]

end LogicalInduction
