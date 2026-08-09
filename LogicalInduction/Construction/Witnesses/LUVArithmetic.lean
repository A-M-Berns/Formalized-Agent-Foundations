import LogicalInduction.Framework.Expectations
import LogicalInduction.Construction.Witnesses.ComputationSyntax

/-!
# First-order arithmetic LUVs (`def:luv`, the certified threshold bridge)

This file replaces the raw threshold-sentence abstraction (`Framework/Expectations.lean`'s
`LUV.gt : ℚ → Sentence`, which carries no internal meaning) by a *certified* first-order
object, for the paper's own primary LUV class.

## Design decision `dd:luv-arith` (disclosed type-`(c)`)

The paper's `def:luv` is *any* one-variable formula `X` that `Θ` proves defines a unique value
in `[0,1]`.  Its own worked example (`main.tex:1660`) is the canonical class we reconstruct:

> if `f : ℕ⁺ → [0,1]` is computable then `⌜f(7)⌝` is a LUV, because `⌜f(7)⌝` abbreviates
> `⌜γ_f(7,ν)⌝` where `γ_f` is the predicate of `Θ` representing `f`.

Concretely a **computable `[0,1]`-valued function** LUV is given by computable `num, den : ℕ → ℕ`
with `0 < den i` and `num i ≤ den i`; the value of the `i`-th LUV is the rational
`num i / den i ∈ ℚ ∩ [0,1]`.  The threshold `⌜X_i > r⌝` for `r : ℚ` is arithmetized as the FFL
schema `codeOfREPred` of the **decidable** predicate "`r < num i / den i`", exactly as
`ComputationSyntax` arithmetizes halting.

**Why the nonstandard-world subtlety of `def:luv` collapses here.**  The paper's world value is
the *supremum* `sup {x | W(⌜X ≥ x⌝)=1}`, a roundabout definition it needs "in cases where `W`
assigns `X` a non-standard value".  Because our threshold predicate is *decidable* (`Δ₁`), FFL's
`re_complete` makes `Θ` **prove** every true threshold and **refute** every false one (via the
complementary schema).  Hence every world consistent with a deductive process that reveals those
`Θ`-theorems pins the cut exactly at the standard rational `num i / den i` — no nonstandard slack,
and the sup collapses to that rational.  This is what lets the downstream presentation interfaces
(`ExactTheoryPresentation`, `WorldValued`, `ValuesAt`) be *derived* rather than *assumed*
(`LUVPresentation.lean`).

**What is not reconstructed.**  The fully general `def:luv` (an *arbitrary* value-defining
formula, with rationals encoded inside `ℒₒᵣ` and its genuinely nonstandard world values) is *not*
built: Mathlib/Foundation expose no arithmetic-internal rational order.  Public claims must say the
expectation tail is faithful to `def:luv` **for computable `[0,1]`-valued functions**, the class
the paper's expectation development actually uses ("we assume `Θ` represents computations").

All comparisons inside the r.e. predicate are over `ℕ` (this Mathlib has no `Primrec`/`Computable`
arithmetic on `ℤ`/`ℚ`); the rational threshold's sign and magnitude are decoded from its canonical
`num`/`den` at the propositional naming layer.
-/

namespace LogicalInduction

open LO.FirstOrder LO.FirstOrder.Arithmetic

/-! ## The computable `[0,1]`-valued function family -/

/-- A family of computable `[0,1]`-valued function LUVs: the `i`-th LUV has value
`num i / den i ∈ ℚ ∩ [0,1]`.  This is `dd:luv-arith`'s concrete carrier for `def:luv`.
Paper node: `def:luv` -/
structure ComputableLUV where
  /-- Numerator of the `i`-th LUV's value. -/
  num : ℕ → ℕ
  /-- Denominator of the `i`-th LUV's value. -/
  den : ℕ → ℕ
  den_pos : ∀ i, 0 < den i
  num_le_den : ∀ i, num i ≤ den i
  num_computable : Computable num
  den_computable : Computable den

namespace ComputableLUV

variable (L : ComputableLUV)

/-- The rational value `num i / den i` of the `i`-th LUV. -/
def value (i : ℕ) : ℚ := (L.num i : ℚ) / (L.den i : ℚ)

lemma value_nonneg (i : ℕ) : 0 ≤ L.value i := by
  unfold value; positivity

lemma value_le_one (i : ℕ) : L.value i ≤ 1 := by
  unfold value
  rw [div_le_one (by exact_mod_cast L.den_pos i)]
  exact_mod_cast L.num_le_den i

/-! ## The decidable threshold predicate and its FFL schema -/

/-- The compact natural code naming the query "`r < X_i`": pairs the LUV index `i` with the
threshold's sign (`0` for `0 ≤ r`, `1` for `r < 0`) and canonical magnitude `|r.num|`, `r.den`. -/
def thresholdCode (i : ℕ) (r : ℚ) : ℕ :=
  Nat.pair i (Nat.pair (if 0 ≤ r then 0 else 1) (Nat.pair r.num.natAbs r.den))

/-- Index component of a threshold code. -/
def codeIdx (m : ℕ) : ℕ := m.unpair.1
/-- Sign tag of a threshold code (`0` iff `0 ≤ r`). -/
def codeSgn (m : ℕ) : ℕ := m.unpair.2.unpair.1
/-- Magnitude numerator `|r.num|` of a threshold code. -/
def codeAbsNum (m : ℕ) : ℕ := m.unpair.2.unpair.2.unpair.1
/-- Denominator `r.den` of a threshold code. -/
def codeDen (m : ℕ) : ℕ := m.unpair.2.unpair.2.unpair.2

/-- Left side of the threshold comparison: `|r.num| * den i`. -/
def lhs (m : ℕ) : ℕ := codeAbsNum m * L.den (codeIdx m)
/-- Right side of the threshold comparison: `num i * r.den` plus a sign offset that dominates
the left side exactly when `r < 0` (`sgn ≠ 0`), making the predicate vacuously true there. -/
def rhs (m : ℕ) : ℕ :=
  L.num (codeIdx m) * codeDen m + codeSgn m * (codeAbsNum m * L.den (codeIdx m) + 1)

/-- The decidable threshold predicate on codes, comparing the decoded rational `r` against
`num i / den i` by a single `ℕ` cross-multiplication.  A negative `r` (`sgn ≠ 0`) is below every
`[0,1]` value, and the additive offset forces the predicate true there. -/
def ThresholdPred (m : ℕ) : Prop := L.lhs m < L.rhs m

instance : DecidablePred L.ThresholdPred := fun m => by
  unfold ThresholdPred; infer_instance

attribute [local irreducible] Nat.sqrt in
/-- The threshold predicate is computable (a single `ℕ` cross-multiplication comparison). -/
lemma thresholdPred_computable : ComputablePred L.ThresholdPred := by
  have hidx : Computable (fun m : ℕ => codeIdx m) :=
    (Primrec.fst.comp Primrec.unpair).to_comp
  have hsgn : Computable (fun m : ℕ => codeSgn m) :=
    (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))).to_comp
  have han : Computable (fun m : ℕ => codeAbsNum m) :=
    (Primrec.fst.comp (Primrec.unpair.comp
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))).to_comp
  have hb : Computable (fun m : ℕ => codeDen m) :=
    (Primrec.snd.comp (Primrec.unpair.comp
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))).to_comp
  have hden : Computable (fun m : ℕ => L.den (codeIdx m)) := L.den_computable.comp hidx
  have hnum : Computable (fun m : ℕ => L.num (codeIdx m)) := L.num_computable.comp hidx
  have hlhs : Computable (fun m : ℕ => codeAbsNum m * L.den (codeIdx m)) :=
    Computable₂.comp Primrec.nat_mul.to_comp han hden
  have hoff : Computable (fun m : ℕ => codeAbsNum m * L.den (codeIdx m) + 1) :=
    Computable₂.comp Primrec.nat_add.to_comp hlhs (Computable.const 1)
  have hrhs : Computable
      (fun m : ℕ => L.num (codeIdx m) * codeDen m
        + codeSgn m * (codeAbsNum m * L.den (codeIdx m) + 1)) :=
    Computable₂.comp Primrec.nat_add.to_comp
      (Computable₂.comp Primrec.nat_mul.to_comp hnum hb)
      (Computable₂.comp Primrec.nat_mul.to_comp hsgn hoff)
  have hdec : Computable (fun m : ℕ => decide
      (codeAbsNum m * L.den (codeIdx m)
        < L.num (codeIdx m) * codeDen m
          + codeSgn m * (codeAbsNum m * L.den (codeIdx m) + 1))) :=
    Computable₂.comp Primrec.nat_lt.decide.to_comp hlhs hrhs
  exact (Computable.computablePred hdec).of_eq (fun m => Iff.rfl)

/-- The threshold predicate is r.e. -/
lemma thresholdPred_re : REPred L.ThresholdPred := L.thresholdPred_computable.to_re

/-- The complement threshold predicate is r.e. (used for the refutation schema: because
thresholds are decidable, `Θ` refutes every false one). -/
lemma thresholdPred_compl_re : REPred (fun m => ¬ L.ThresholdPred m) :=
  L.thresholdPred_computable.not.to_re

/-! ### Code projections -/

@[simp] lemma codeIdx_thresholdCode (i : ℕ) (r : ℚ) : codeIdx (thresholdCode i r) = i := by
  simp [codeIdx, thresholdCode]
@[simp] lemma codeSgn_thresholdCode (i : ℕ) (r : ℚ) :
    codeSgn (thresholdCode i r) = (if 0 ≤ r then 0 else 1) := by
  simp [codeSgn, thresholdCode]
@[simp] lemma codeAbsNum_thresholdCode (i : ℕ) (r : ℚ) :
    codeAbsNum (thresholdCode i r) = r.num.natAbs := by
  simp [codeAbsNum, thresholdCode]
@[simp] lemma codeDen_thresholdCode (i : ℕ) (r : ℚ) :
    codeDen (thresholdCode i r) = r.den := by
  simp [codeDen, thresholdCode]

/-- **The correspondence.** The `ℕ` threshold predicate on the code of query `⌜X_i > r⌝` holds
exactly when the rational threshold `r` is strictly below the LUV's value.  This is what makes
the decidable arithmetic faithful to `def:luv`. -/
lemma thresholdPred_code_iff (i : ℕ) (r : ℚ) :
    L.ThresholdPred (thresholdCode i r) ↔ r < L.value i := by
  have hden : (0 : ℚ) < (L.den i : ℚ) := by exact_mod_cast L.den_pos i
  unfold ThresholdPred lhs rhs value
  simp only [codeIdx_thresholdCode, codeSgn_thresholdCode, codeAbsNum_thresholdCode,
    codeDen_thresholdCode]
  rw [lt_div_iff₀ hden]
  by_cases hr : 0 ≤ r
  · simp only [if_pos hr, zero_mul, add_zero]
    -- both sides nonneg: nat `<` matches ℚ cross-multiplication
    have hrnum : (r.num.natAbs : ℚ) = r * (r.den : ℚ) := by
      have h1 : (r.num.natAbs : ℚ) = (r.num : ℚ) := by
        rw [Nat.cast_natAbs, abs_of_nonneg (by exact_mod_cast Rat.num_nonneg.mpr hr)]
      have h2 := Rat.num_div_den r
      have hd : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_nz
      field_simp at h2
      rw [h1]; linear_combination h2
    constructor
    · intro h
      have : (r.num.natAbs : ℚ) * (L.den i : ℚ) < (L.num i : ℚ) * (r.den : ℚ) := by
        exact_mod_cast h
      rw [hrnum] at this
      nlinarith [this, hden, (by exact_mod_cast (r.den_pos) : (0:ℚ) < (r.den:ℚ))]
    · intro h
      have hden' : (0 : ℚ) < (r.den : ℚ) := by exact_mod_cast r.den_pos
      have : (r.num.natAbs : ℚ) * (L.den i : ℚ) < (L.num i : ℚ) * (r.den : ℚ) := by
        rw [hrnum]; nlinarith [h, hden, hden']
      exact_mod_cast this
  · push_neg at hr
    simp only [if_neg (not_le.mpr hr)]
    constructor
    · intro _
      nlinarith [hr, hden, (by positivity : (0:ℚ) ≤ (L.num i : ℚ))]
    · intro _
      -- rhs has the `+ 1 * (lhs + 1)` offset, strictly dominating lhs
      have : r.num.natAbs * L.den i
          < L.num i * r.den + 1 * (r.num.natAbs * L.den i + 1) := by omega
      exact_mod_cast this

/-! ### FFL threshold schemas and their spec -/

/-- FFL's arithmetic schema quoting "`r < X_i`" (positive threshold). -/
noncomputable def thresholdSchema : ArithmeticSemisentence 1 :=
  codeOfREPred L.ThresholdPred

/-- The complementary schema quoting "`¬ (r < X_i)`", i.e. `X_i ≤ r`. -/
noncomputable def thresholdFailureSchema : ArithmeticSemisentence 1 :=
  codeOfREPred (fun m => ¬ L.ThresholdPred m)

lemma thresholdSchema_spec (m : ℕ) :
    ℕ ⊧ₘ L.thresholdSchema/[↑m] ↔ L.ThresholdPred m := by
  simpa [thresholdSchema, models_iff, Semiformula.eval_substs,
    Matrix.constant_eq_singleton] using (codeOfREPred_spec L.thresholdPred_re (x := m))

lemma thresholdFailureSchema_spec (m : ℕ) :
    ℕ ⊧ₘ L.thresholdFailureSchema/[↑m] ↔ ¬ L.ThresholdPred m := by
  simpa [thresholdFailureSchema, models_iff, Semiformula.eval_substs,
    Matrix.constant_eq_singleton] using (codeOfREPred_spec L.thresholdPred_compl_re (x := m))

section Provability
variable {T : ArithmeticTheory} [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1]

/-- **Provable decidedness (positive).**  For a Σ₁-sound theory, a true threshold is provable. -/
lemma threshold_provable (i : ℕ) (r : ℚ) (h : r < L.value i) :
    T ⊢ L.thresholdSchema/[‘↑(thresholdCode i r)’] :=
  (re_complete L.thresholdPred_re).mp ((L.thresholdPred_code_iff i r).mpr h)

/-- **Provable decidedness (negative).**  A false threshold is refuted through the
complementary schema. -/
lemma threshold_refutable (i : ℕ) (r : ℚ) (h : ¬ r < L.value i) :
    T ⊢ L.thresholdFailureSchema/[‘↑(thresholdCode i r)’] :=
  (re_complete L.thresholdPred_compl_re).mp (fun hp => h ((L.thresholdPred_code_iff i r).mp hp))

end Provability

/-! ### The propositional LUV -/

/-- The public propositional sentence naming the query `⌜X_i > r⌝`. -/
def thresholdSentence (i : ℕ) (r : ℚ) : Sentence :=
  LO.Propositional.Formula.atom (thresholdCode i r)

/-- The `Framework.LUV` for the `i`-th computable-function LUV: its threshold sentences are the
propositional names of the arithmetic queries.
Paper node: `def:luv` -/
def toLUV (i : ℕ) : LUV where
  gt r := thresholdSentence i r

@[simp] lemma toLUV_gt (i : ℕ) (r : ℚ) : (toLUV i).gt r = thresholdSentence i r := rfl

/-! ### The threshold-code efficiency certificate (`dd:fuel` discharged for `dd:luv-arith`)

`PolyThresholdCodes` asks for one poly-fueled program emitting the encoded threshold sentence
`⌜Xᵢ > b/k⌝` from the query `⟨k, b⟩`.  The sentence's atom code carries the *reduced*
numerator/denominator of `b/k`, so the program is `gcdc` (the runtime Euclid iteration) followed
by two `divmod1` divisions and the fixed pairing shell — with an `ifzSel` fallback to `0/1` for
the everywhere-zero `k = 0` query. -/

/-- Reduced numerator of a natural-cast quotient: `((b : ℚ) / k).num = b / gcd b k`. -/
lemma natCast_div_num {b k : ℕ} (hk : k ≠ 0) :
    ((b : ℚ) / (k : ℚ)).num = (b / Nat.gcd b k : ℕ) := by
  have hg : 0 < Nat.gcd b k := Nat.gcd_pos_of_pos_right b (Nat.pos_of_ne_zero hk)
  have hb' : (b / Nat.gcd b k) * Nat.gcd b k = b := Nat.div_mul_cancel (Nat.gcd_dvd_left b k)
  have hk' : (k / Nat.gcd b k) * Nat.gcd b k = k := Nat.div_mul_cancel (Nat.gcd_dvd_right b k)
  have hkg : 0 < k / Nat.gcd b k :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hk) (Nat.gcd_dvd_right b k)) hg
  have hgQ : (Nat.gcd b k : ℚ) ≠ 0 := by exact_mod_cast hg.ne'
  have hbQ : (b : ℚ) = ((b / Nat.gcd b k : ℕ) : ℚ) * (Nat.gcd b k : ℚ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℚ) hb'.symm
  have hkQ : (k : ℚ) = ((k / Nat.gcd b k : ℕ) : ℚ) * (Nat.gcd b k : ℚ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℚ) hk'.symm
  have heq : (b : ℚ) / (k : ℚ)
      = (((b / Nat.gcd b k : ℕ) : ℤ) : ℚ) / (((k / Nat.gcd b k : ℕ) : ℤ) : ℚ) := by
    rw [hbQ, hkQ, mul_div_mul_right _ _ hgQ, Int.cast_natCast, Int.cast_natCast]
  rw [heq, Rat.num_div_eq_of_coprime (a := ((b / Nat.gcd b k : ℕ) : ℤ))
    (b := ((k / Nat.gcd b k : ℕ) : ℤ)) (by exact_mod_cast hkg)
    (by simpa using Nat.coprime_div_gcd_div_gcd hg)]

/-- Reduced denominator of a natural-cast quotient: `((b : ℚ) / k).den = k / gcd b k`. -/
lemma natCast_div_den {b k : ℕ} (hk : k ≠ 0) :
    ((b : ℚ) / (k : ℚ)).den = k / Nat.gcd b k := by
  have hg : 0 < Nat.gcd b k := Nat.gcd_pos_of_pos_right b (Nat.pos_of_ne_zero hk)
  have hb' : (b / Nat.gcd b k) * Nat.gcd b k = b := Nat.div_mul_cancel (Nat.gcd_dvd_left b k)
  have hk' : (k / Nat.gcd b k) * Nat.gcd b k = k := Nat.div_mul_cancel (Nat.gcd_dvd_right b k)
  have hkg : 0 < k / Nat.gcd b k :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hk) (Nat.gcd_dvd_right b k)) hg
  have hgQ : (Nat.gcd b k : ℚ) ≠ 0 := by exact_mod_cast hg.ne'
  have hbQ : (b : ℚ) = ((b / Nat.gcd b k : ℕ) : ℚ) * (Nat.gcd b k : ℚ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℚ) hb'.symm
  have hkQ : (k : ℚ) = ((k / Nat.gcd b k : ℕ) : ℚ) * (Nat.gcd b k : ℚ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℚ) hk'.symm
  have heq : (b : ℚ) / (k : ℚ)
      = (((b / Nat.gcd b k : ℕ) : ℤ) : ℚ) / (((k / Nat.gcd b k : ℕ) : ℤ) : ℚ) := by
    rw [hbQ, hkQ, mul_div_mul_right _ _ hgQ, Int.cast_natCast, Int.cast_natCast]
  have hden := Rat.den_div_eq_of_coprime (a := ((b / Nat.gcd b k : ℕ) : ℤ))
    (b := ((k / Nat.gcd b k : ℕ) : ℤ))
    (by exact_mod_cast hkg) (by simpa using Nat.coprime_div_gcd_div_gcd hg)
  rw [heq]
  exact_mod_cast hden

private lemma encode_thresholdSentence (i : ℕ) (r : ℚ) :
    Encodable.encode (thresholdSentence i r) = Nat.pair 1 (thresholdCode i r) + 1 := rfl

/-- Runtime gcd is primitive recursive (extracted from the fuel certificate). -/
lemma nat_gcd_primrec : Primrec₂ Nat.gcd := by
  obtain ⟨c, hc⟩ := gcdc_polyFueled
  exact Primrec₂.unpaired'.mp ((Primrec.nat_iff.mp hc.primrec).of_eq (fun n => rfl))

/-- `thresholdCode` of a natural quotient query, in purely `ℕ` terms: the reduced pair via
`gcd`, with the `0/1` fallback at denominator zero. -/
def thresholdCodeNat (i j m : ℕ) : ℕ :=
  Nat.pair i (Nat.pair 0
    (if m = 0 then Nat.pair 0 1
     else Nat.pair (j / Nat.gcd j m) (m / Nat.gcd j m)))

lemma thresholdCodeNat_eq (i j m : ℕ) :
    thresholdCodeNat i j m = thresholdCode i ((j : ℚ) / (m : ℚ)) := by
  unfold thresholdCodeNat thresholdCode
  have hsign : (if 0 ≤ (j : ℚ) / (m : ℚ) then (0 : ℕ) else 1) = 0 :=
    if_pos (div_nonneg (Nat.cast_nonneg j) (Nat.cast_nonneg m))
  rw [hsign]
  by_cases hm : m = 0
  · subst hm
    norm_num
  · rw [if_neg hm]
    have hnum : ((j : ℚ) / (m : ℚ)).num.natAbs = j / Nat.gcd j m := by
      rw [natCast_div_num hm]; exact Int.natAbs_natCast _
    have hden : ((j : ℚ) / (m : ℚ)).den = m / Nat.gcd j m := natCast_div_den hm
    rw [hnum, hden]

/-- The `ℕ`-level threshold code is primitive recursive in the packed query
`⟨i, ⟨m, j⟩⟩`. -/
lemma thresholdCodeNat_primrec :
    Primrec (fun e : ℕ => thresholdCodeNat e.unpair.1 e.unpair.2.unpair.2 e.unpair.2.unpair.1) := by
  have hi : Primrec (fun e : ℕ => e.unpair.1) := Primrec.fst.comp Primrec.unpair
  have hm : Primrec (fun e : ℕ => e.unpair.2.unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  have hj : Primrec (fun e : ℕ => e.unpair.2.unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  have hg : Primrec (fun e : ℕ => Nat.gcd e.unpair.2.unpair.2 e.unpair.2.unpair.1) :=
    nat_gcd_primrec.comp hj hm
  have hnum : Primrec (fun e : ℕ => e.unpair.2.unpair.2
      / Nat.gcd e.unpair.2.unpair.2 e.unpair.2.unpair.1) :=
    Primrec.nat_div.comp hj hg
  have hden : Primrec (fun e : ℕ => e.unpair.2.unpair.1
      / Nat.gcd e.unpair.2.unpair.2 e.unpair.2.unpair.1) :=
    Primrec.nat_div.comp hm hg
  have hred : Primrec (fun e : ℕ =>
      if e.unpair.2.unpair.1 = 0 then Nat.pair 0 1
      else Nat.pair (e.unpair.2.unpair.2 / Nat.gcd e.unpair.2.unpair.2 e.unpair.2.unpair.1)
        (e.unpair.2.unpair.1 / Nat.gcd e.unpair.2.unpair.2 e.unpair.2.unpair.1)) :=
    Primrec.ite (Primrec.eq.comp hm (Primrec.const 0))
      (Primrec.const (Nat.pair 0 1)) (Primrec₂.natPair.comp hnum hden)
  exact Primrec₂.natPair.comp hi
    (Primrec₂.natPair.comp (Primrec.const 0) hred)

attribute [local irreducible] Nat.sqrt in
/-- **`dd:fuel` discharged for `dd:luv-arith` thresholds.**  The threshold presentation of every
`toLUV i` is polynomially codeable: one poly-fueled program — the runtime Euclid `gcdc`, two
`divmod1` reductions, an `ifzSel` zero-denominator fallback, and the fixed atom shell — emits
the encoded sentence `⌜Xᵢ > b/k⌝` from `⟨k, b⟩`.  This is the first `PolyThresholdCodes`
certificate *proved* rather than assumed in the repository.
Paper node: `def:ec` -/
theorem toLUV_polyThresholdCodes (i : ℕ) : (toLUV i).PolyThresholdCodes := by
  obtain ⟨cg, hgcd⟩ := gcdc_polyFueled
  obtain ⟨cdm, hdm⟩ := divmod1_polyFueled
  -- Query `m = ⟨k, b⟩`: denominator `k = m.unpair.1`, numerator `b = m.unpair.2`.
  have gPF := hgcd.comp (PolyFueled.right.pair PolyFueled.left)
  have pgPF := predc_polyFueled.comp gPF
  have numPF := PolyFueled.left.comp (hdm.comp (pgPF.pair PolyFueled.right))
  have denPF := PolyFueled.left.comp (hdm.comp (pgPF.pair PolyFueled.left))
  have selPF := ifzSel_polyFueled.comp
    (((PolyFueled.const (Nat.pair 0 1)).pair (numPF.pair denPF)).pair PolyFueled.left)
  have fullPF := ((PolyFueled.const 1).pair
    ((PolyFueled.const i).pair ((PolyFueled.const 0).pair selPF))).succ_comp
  refine ⟨_, fullPF.of_eq (fun m => ?_)⟩
  rw [toLUV_gt, encode_thresholdSentence]
  simp only [Nat.unpair_pair, ifzSelFn]
  set k := m.unpair.1 with hkdef
  set b := m.unpair.2 with hbdef
  set r := (b : ℚ) / (k : ℚ) with hr
  have hsign : (if 0 ≤ r then (0 : ℕ) else 1) = 0 :=
    if_pos (div_nonneg (Nat.cast_nonneg b) (Nat.cast_nonneg k))
  unfold thresholdCode
  rw [hsign]
  by_cases hk : k = 0
  · rw [if_pos hk]
    have hr0 : r = 0 := by rw [hr, hk]; simp
    rw [hr0]
    norm_num
  · rw [if_neg hk]
    have hg : 0 < Nat.gcd b k := Nat.gcd_pos_of_pos_right b (Nat.pos_of_ne_zero hk)
    have h1 : Nat.pred (Nat.gcd b k) + 1 = Nat.gcd b k :=
      Nat.succ_pred_eq_of_pos hg
    rw [h1]
    have hnum : r.num.natAbs = b / Nat.gcd b k := by
      rw [hr, natCast_div_num hk]; exact Int.natAbs_natCast _
    have hden : r.den = k / Nat.gcd b k := by
      rw [hr]; exact natCast_div_den hk
    rw [hnum, hden]

end ComputableLUV

end LogicalInduction
