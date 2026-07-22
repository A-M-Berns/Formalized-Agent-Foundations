/-
# Occam Bounds (`thm:ob`)

The paper allocates one unit of risk across sentences according to the Kraft weights
`2^{-κ(φ)}` and uses an efficiently emulatable family indexed by the desired inverse
constant.  In the repository's single-trader criterion we diagonalize that family into
one trader: rung `j` has purchase capacity `j⁴` and is scaled by `1/j²`.  Thus its total
risk is at most `1/j²`, while a full purchase has plausible payout of order `j²`.
-/
import LogicalInduction.Properties.UniformNonDogmatism
import LogicalInduction.Properties.Relationships

namespace LogicalInduction

open Filter Topology

/-- The real Kraft weight associated with prefix complexity `κ`. -/
noncomputable def prefixWeight (κ : Sentence → ℕ) (φ : Sentence) : ℝ :=
  1 / (2 : ℝ) ^ κ φ

lemma prefixWeight_pos (κ : Sentence → ℕ) (φ : Sentence) :
    0 < prefixWeight κ φ := by
  simp only [prefixWeight]
  positivity

/-- A syntax-level presentation of the fixed prefix machine used by Occam Bounds.

`sentence` is an efficient enumeration of all sentences. `approximation n i` is the
paper's polynomial-time, rational, from-below approximation to `2^{-κ(sentence i)}`.
The finite Kraft bound is stated on this enumeration, so duplicates cannot silently spend
the same code weight twice.  This structure contains no market prices or Occam conclusion.
Paper node: `thm:ob` -/
structure PrefixMachinePresentation (κ : Sentence → ℕ) where
  sentence : ℕ → Sentence
  sentence_codes : PolySentenceCodes sentence
  approximation : ℕ → ℕ → ℚ
  approximation_codes : PolyRatCodes
    (fun z ↦ approximation z.unpair.1 z.unpair.2)
  approximation_nonneg : ∀ n i, 0 ≤ approximation n i
  approximation_le : ∀ n i,
    ((approximation n i : ℚ) : ℝ) ≤ prefixWeight κ (sentence i)
  approximation_tendsto : ∀ i,
    Tendsto (fun n ↦ ((approximation n i : ℚ) : ℝ)) atTop
      (𝓝 (prefixWeight κ (sentence i)))
  kraft : ∀ N,
    ∑ i ∈ Finset.range N, prefixWeight κ (sentence i) ≤ 1
  covers : ∀ φ, ∃ i, sentence i = φ

/-- Rung `j` starts only after both the rung and sentence index are available. -/
def obStart (j i : ℕ) : ℕ := max j (i + 1)

/-- Unscaled purchase capacity of rung `j`. -/
def obCapacity (j : ℕ) : ℚ := (j : ℚ) ^ 4

/-- Half-width used by the continuous low-price gate. Its support ends at
`approximation / j⁴`. -/
def obBase {κ : Sentence → ℕ} (U : PrefixMachinePresentation κ)
    (j n i : ℕ) : ℚ :=
  U.approximation n i / (2 * obCapacity j)

/-- Flattened base-width input used only by the token compiler: `z = ⟨j', ⟨n,i⟩⟩`
represents rung `j'+1`, day `n`, and sentence index `i`. -/
def obEmitBase {κ : Sentence → ℕ} (U : PrefixMachinePresentation κ)
    (z : ℕ) : ℚ :=
  obBase U (z.unpair.1 + 1) z.unpair.2.unpair.1 z.unpair.2.unpair.2

/-- The two derived rational-token streams consumed by the Occam gate compiler.

This is a syntax-only representation boundary: it says that rational arithmetic on the
prefix approximation can emit the gate's threshold-sum and reciprocal-width tokens in
polynomial fuel. It contains no market prices, worlds, exploitation, or limiting bound.
Paper node: `thm:ob` -/
structure OccamThresholdEmission {κ : Sentence → ℕ}
    (U : PrefixMachinePresentation κ) : Prop where
  threshold_sum_codes : PolyRatCodes (fun z ↦ obEmitBase U z + obEmitBase U z)
  inverse_width_codes : PolyRatCodes (fun z ↦ 1 / obEmitBase U z)

/-- A fixed prefix program that negates the decoded sentence. The sole semantic content is
the standard additive complexity overhead; it contains no prices or Occam conclusion.
Paper node: `thm:ob` -/
structure PrefixNegationCompiler (κ : Sentence → ℕ) where
  overhead : ℕ
  complexity_neg_le : ∀ φ, κ (∼φ) ≤ κ φ + overhead

/-- Negation loses at most the compiler's fixed multiplicative Kraft factor. -/
lemma PrefixNegationCompiler.weight_div_le_neg
    {κ : Sentence → ℕ} (neg : PrefixNegationCompiler κ) (φ : Sentence) :
    prefixWeight κ φ / (2 : ℝ) ^ neg.overhead ≤
      prefixWeight κ (∼φ) := by
  have hpow : (2 : ℝ) ^ κ (∼φ) ≤ (2 : ℝ) ^ (κ φ + neg.overhead) := by
    exact pow_le_pow_right₀ (by norm_num) (neg.complexity_neg_le φ)
  have hpos : 0 < (2 : ℝ) ^ κ (∼φ) := by positivity
  rw [prefixWeight, prefixWeight]
  calc
    1 / (2 : ℝ) ^ κ φ / (2 : ℝ) ^ neg.overhead =
        1 / ((2 : ℝ) ^ κ φ * (2 : ℝ) ^ neg.overhead) := by
          field_simp
    _ = 1 / (2 : ℝ) ^ (κ φ + neg.overhead) := by rw [pow_add]
    _ ≤ 1 / (2 : ℝ) ^ κ (∼φ) := one_div_le_one_div_of_le hpos hpow

/-- Limit coherence for a sentence and its propositional negation, obtained from the
audited exclusive–exhaustive lemma rather than assumed as a valuation identity.
Paper node: `thm:lc` -/
theorem lic_limitingBelief_add_neg
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hP : ∀ n ψ, 0 ≤ P n ψ ∧ P n ψ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (φ : Sentence) :
    limitingBelief P φ + limitingBelief P (∼φ) = 1 := by
  let pair : ℕ → ℕ → Sentence := fun j _ ↦ if j = 0 then φ else ∼φ
  have hcodes : ∀ j < 2, PolySentenceCodes (pair j) := by
    intro j hj
    by_cases h0 : j = 0
    · subst j
      exact ⟨_, PolyFueled.const (Encodable.encode φ)⟩
    · have h1 : j = 1 := by omega
      subst j
      exact ⟨_, PolyFueled.const (Encodable.encode (∼φ))⟩
  have hsemantic : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ((List.range 2).map (fun j ↦ v.payout (pair j n))).sum = 1 := by
    intro n v hv
    have hrange : List.range 2 = [0, 1] := by decide
    rw [hrange]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    simp only [pair, if_pos rfl, if_neg (by omega : (1 : ℕ) ≠ 0)]
    by_cases hφ : v.Holds φ
    · have hn : ¬ v.Holds (∼φ) := by
        rw [PCWorld.holds_neg]
        exact not_not_intro hφ
      rw [PCWorld.payout, if_pos hφ, PCWorld.payout, if_neg hn]
      norm_num
    · have hn : v.Holds (∼φ) := (PCWorld.holds_neg v φ).2 hφ
      rw [PCWorld.payout, if_neg hφ, PCWorld.payout, if_pos hn]
      norm_num
  have hlex0 := lic_learning_exclusive_exhaustive P DP 2 (by omega)
    pair hcodes hP hworld hsemantic
  have hlex : (fun n ↦ P n φ + P n (∼φ)) ≈ₙ (fun _ ↦ (1 : ℝ)) := by
    have hrange : List.range 2 = [0, 1] := by decide
    simpa [hrange, pair] using hlex0
  have hsum := (lic_limitingBelief_tendsto P DP hworld φ).add
    (lic_limitingBelief_tendsto P DP hworld (∼φ))
  have hone : ConvergesTo (fun n ↦ P n φ + P n (∼φ)) 1 :=
    convergesTo_iff_asympEq_const.mpr hlex
  exact tendsto_nhds_unique hsum hone

/-- Low-price gate for sentence `i` on rung `j`, padded to zero before `obStart j i`. -/
def obBuySig {κ : Sentence → ℕ} (U : PrefixMachinePresentation κ)
    (j i n : ℕ) : EF :=
  if n < obStart j i then .const 0
  else buyIndEF (U.sentence i) (obBase U j n i) (obBase U j n i) n

lemma obBuySig_denote_pad {κ : Sentence → ℕ}
    (U : PrefixMachinePresentation κ) (P : History) {j i n : ℕ}
    (h : n < obStart j i) :
    (obBuySig U j i n).denote P = 0 := by
  simp [obBuySig, h]

lemma obBuySig_live {κ : Sentence → ℕ}
    (U : PrefixMachinePresentation κ) {j i n : ℕ}
    (h : obStart j i ≤ n) :
    obBuySig U j i n =
      buyIndEF (U.sentence i) (obBase U j n i) (obBase U j n i) n := by
  rw [obBuySig, if_neg (by omega)]

lemma obBuySig_mem {κ : Sentence → ℕ}
    (U : PrefixMachinePresentation κ) (P : History) (j i n : ℕ) :
    0 ≤ (obBuySig U j i n).denote P ∧
      (obBuySig U j i n).denote P ≤ 1 := by
  by_cases h : n < obStart j i
  · simp [obBuySig, h]
  · rw [obBuySig, if_neg h]
    exact buyInd_mem _ _ _ _ P

lemma obBuySig_rank_le {κ : Sentence → ℕ}
    (U : PrefixMachinePresentation κ) (j i n : ℕ) :
    (obBuySig U j i n).rank ≤ n := by
  by_cases h : n < obStart j i
  · simp [obBuySig, h]
  · simp [obBuySig, h]

/-- A varying sentence index and a separately varying quotation day still form a
polynomial segment stream when both selectors and the sentence progression are fueled. -/
lemma PolySegStream.serialize_price_sequence_at_comp
    {φ : ℕ → Sentence} (hφ : PolySentenceCodes φ)
    {cs cd : Nat.Partrec.Code} {sf df : ℕ → ℕ}
    (hs : PolyFueled cs sf) (hd : PolyFueled cd df) :
    PolySegStream (fun x ↦ (EF.price (φ (sf x)) (df x)).serialize) := by
  obtain ⟨cφ, hφc⟩ := hφ
  have htok : PolyTokenStream (fun x ↦
      [0, Encodable.encode (φ (sf x)), df x]) :=
    (PolyTokenStream.const 0).append
      ((PolyTokenStream.polyTok (hφc.comp hs)).append
        (PolyTokenStream.polyTok hd))
  exact PolySegStream.of_eq (PolySegStream.ofTokenStream htok) (fun x ↦ by
    simp [EF.serialize])

/-- Literal polynomial segment emission for the padded Occam buy gate. -/
lemma obBuySig_polySegStream {κ : Sentence → ℕ}
    (U : PrefixMachinePresentation κ) (emit : OccamThresholdEmission U)
    {cj ci cn : Nat.Partrec.Code} {jf if_ nf : ℕ → ℕ}
    (hj : PolyFueled cj jf) (hi : PolyFueled ci if_) (hn : PolyFueled cn nf) :
    PolySegStream (fun x ↦
      (obBuySig U (jf x + 1) (if_ x) (nf x)).serialize) := by
  have hinput : PolyFueled _ (fun x ↦ Nat.pair (jf x) (Nat.pair (nf x) (if_ x))) :=
    hj.pair (hn.pair hi)
  have hsumCodes : PolyRatCodes (fun x ↦
      obBase U (jf x + 1) (nf x) (if_ x) +
        obBase U (jf x + 1) (nf x) (if_ x)) := by
    obtain ⟨c, hc⟩ := emit.threshold_sum_codes
    exact ⟨_, (hc.comp hinput).of_eq (fun x ↦ by
      simp [obEmitBase])⟩
  have hinvCodes : PolyRatCodes (fun x ↦
      1 / obBase U (jf x + 1) (nf x) (if_ x)) := by
    obtain ⟨c, hc⟩ := emit.inverse_width_codes
    exact ⟨_, (hc.comp hinput).of_eq (fun x ↦ by
      simp [obEmitBase])⟩
  have hprice := PolySegStream.serialize_price_sequence_at_comp
    U.sentence_codes hi hn
  have hsum : PolySegStream (fun x ↦
      (EF.const (obBase U (jf x + 1) (nf x) (if_ x) +
        obBase U (jf x + 1) (nf x) (if_ x))).serialize) :=
    PolySegStream.ofTokenStream
      (PolyTokenStream.serialize_const_comp hsumCodes)
  have hinv : PolySegStream (fun x ↦
      (EF.const (1 / obBase U (jf x + 1) (nf x) (if_ x))).serialize) :=
    PolySegStream.ofTokenStream
      (PolyTokenStream.serialize_const_comp hinvCodes)
  have hlive : PolySegStream (fun x ↦
      (buyIndEF (U.sentence (if_ x))
        (obBase U (jf x + 1) (nf x) (if_ x))
        (obBase U (jf x + 1) (nf x) (if_ x)) (nf x)).serialize) := by
    have hraw := PolySegStream.serialize_mul
      (PolySegStream.serialize_add hsum
        (PolySegStream.serialize_mul
          (PolySegStream.ofTokenStream (PolyTokenStream.serialize_const (-1)))
          hprice)) hinv
    simpa [buyIndEF] using PolySegStream.serialize_clip01 hraw
  have hzero : PolySegStream (fun _ : ℕ ↦ (EF.const 0).serialize) :=
    PolySegStream.ofTokenStream (PolyTokenStream.serialize_const 0)
  obtain ⟨cadd, hadd⟩ := addc_polyFueled
  have hstart : PolyFueled _ (fun x ↦ obStart (jf x + 1) (if_ x)) :=
    (hadd.comp (hj.succ_comp.pair
      (subc_polyFueled.comp (hi.succ_comp.pair hj.succ_comp)))).of_eq
        (fun x ↦ by
          simp only [Nat.unpair_pair, obStart]
          omega)
  have htest : PolyFueled _ (fun x ↦
      nf x + 1 - obStart (jf x + 1) (if_ x)) :=
    (subc_polyFueled.comp (hn.succ_comp.pair hstart)).of_eq
      (fun x ↦ by simp only [Nat.unpair_pair])
  refine PolySegStream.of_eq (PolySegStream.ifZero hzero hlive htest) ?_
  intro x
  by_cases hpad : nf x < obStart (jf x + 1) (if_ x)
  · have ht : nf x + 1 - obStart (jf x + 1) (if_ x) = 0 := by omega
    simp [ht, obBuySig, hpad]
  · have ht : nf x + 1 - obStart (jf x + 1) (if_ x) ≠ 0 := by omega
    simp [ht, obBuySig, hpad]

lemma obBase_cast {κ : Sentence → ℕ} (U : PrefixMachinePresentation κ)
    (j n i : ℕ) :
    ((obBase U j n i : ℚ) : ℝ) =
      ((U.approximation n i : ℚ) : ℝ) / (2 * (j : ℝ) ^ 4) := by
  rw [obBase, obCapacity]
  push_cast
  ring

lemma obBase_pos {κ : Sentence → ℕ} (U : PrefixMachinePresentation κ)
    {j n i : ℕ} (hj : 1 ≤ j) (ha : 0 < U.approximation n i) :
    0 < ((obBase U j n i : ℚ) : ℝ) := by
  rw [obBase_cast]
  have haR : 0 < ((U.approximation n i : ℚ) : ℝ) := by exact_mod_cast ha
  have hjR : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
  positivity

/-- Fraction of sentence `i`'s rung-`j` capacity purchased on day `n`. -/
noncomputable def obShares {κ : Sentence → ℕ}
    (U : PrefixMachinePresentation κ) (P : History)
    (j i n : ℕ) : ℝ :=
  (armChain (obBuySig U j i) n).denote P * (obBuySig U j i n).denote P

lemma obShares_nonneg {κ : Sentence → ℕ}
    (U : PrefixMachinePresentation κ) (P : History) (j i n : ℕ) :
    0 ≤ obShares U P j i n :=
  mul_nonneg (armChain_mem _ P (fun m ↦ obBuySig_mem U P j i m) n).1
    (obBuySig_mem U P j i n).1

lemma obShares_pos_sig {κ : Sentence → ℕ}
    {U : PrefixMachinePresentation κ} {P : History} {j i n : ℕ}
    (h : 0 < obShares U P j i n) :
    0 < (obBuySig U j i n).denote P := by
  rcases (obBuySig_mem U P j i n).1.lt_or_eq with hs | hs
  · exact hs
  · rw [obShares, ← hs, mul_zero] at h
    exact absurd h (lt_irrefl 0)

/-- Positive purchases occur only below the from-below Kraft approximation divided by
the rung capacity `j⁴`. -/
lemma obBuySig_pos_imp {κ : Sentence → ℕ}
    (U : PrefixMachinePresentation κ) (P : History)
    {j i n : ℕ} (hj : 1 ≤ j)
    (h : 0 < (obBuySig U j i n).denote P) :
    P n (U.sentence i) <
      ((U.approximation n i : ℚ) : ℝ) / (j : ℝ) ^ 4 := by
  have hlive : obStart j i ≤ n := by
    by_contra hn
    rw [obBuySig_denote_pad U P (by omega)] at h
    exact (lt_irrefl 0 h)
  rw [obBuySig_live U hlive] at h
  have ha0 : 0 ≤ ((U.approximation n i : ℚ) : ℝ) := by
    exact_mod_cast U.approximation_nonneg n i
  have hjR : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
  have hb0 : 0 ≤ ((obBase U j n i : ℚ) : ℝ) := by
    rw [obBase_cast]
    positivity
  have hb : 0 < ((obBase U j n i : ℚ) : ℝ) := by
    rcases hb0.eq_or_lt with hb | hb
    · rw [buyIndEF_denote, ← hb] at h
      norm_num at h
    · exact hb
  have hlt := buyInd_pos_imp hb h
  rw [obBase_cast] at hlt
  calc
    P n (U.sentence i) <
        ((U.approximation n i : ℚ) : ℝ) / (2 * (j : ℝ) ^ 4) +
          ((U.approximation n i : ℚ) : ℝ) / (2 * (j : ℝ) ^ 4) := hlt
    _ = ((U.approximation n i : ℚ) : ℝ) / (j : ℝ) ^ 4 := by
      field_simp
      ring

/-- A strict dip below the half-threshold purchases the entire remaining capacity. -/
lemma obBuySig_eq_one {κ : Sentence → ℕ}
    (U : PrefixMachinePresentation κ) (P : History)
    {j i n : ℕ} (hj : 1 ≤ j) (hlive : obStart j i ≤ n)
    (ha : 0 < U.approximation n i)
    (hprice : P n (U.sentence i) < ((obBase U j n i : ℚ) : ℝ)) :
    (obBuySig U j i n).denote P = 1 := by
  rw [obBuySig_live U hlive]
  exact buyInd_eq_one (obBase_pos U hj ha) hprice

lemma obShares_sum {κ : Sentence → ℕ}
    (U : PrefixMachinePresentation κ) (P : History)
    {j i N : ℕ} (h : obStart j i ≤ N) :
    ∑ n ∈ Finset.Ico (obStart j i) N, obShares U P j i n =
      1 - (armChain (obBuySig U j i) N).denote P := by
  simp only [obShares]
  rw [armChain_shares_sum (obBuySig U j i) P h,
    armChain_denote_of_le (obBuySig U j i) P
      (fun n hn ↦ obBuySig_denote_pad U P hn) (obStart j i) le_rfl]

lemma obShares_sum_le_one {κ : Sentence → ℕ}
    (U : PrefixMachinePresentation κ) (P : History)
    {j i N : ℕ} (h : obStart j i ≤ N) :
    ∑ n ∈ Finset.Ico (obStart j i) N, obShares U P j i n ≤ 1 := by
  rw [obShares_sum U P h]
  have hnonneg := (armChain_mem (obBuySig U j i) P
    (fun n ↦ obBuySig_mem U P j i n) N).1
  linarith

/-- The scaled coefficient is `j²`: capacity `j⁴` times rung weight `1/j²`. -/
def obCoef {κ : Sentence → ℕ} (U : PrefixMachinePresentation κ)
    (j i n : ℕ) : EF :=
  .mul (.const ((j ^ 2 : ℕ) : ℚ))
    (.mul (armChain (obBuySig U j i) n) (obBuySig U j i n))

lemma obCoef_denote {κ : Sentence → ℕ}
    (U : PrefixMachinePresentation κ) (P : History) (j i n : ℕ) :
    (obCoef U j i n).denote P = (j : ℝ) ^ 2 * obShares U P j i n := by
  simp only [obCoef, EF.denote_mul, EF.denote_const, Pi.mul_apply, obShares]
  push_cast
  norm_num

lemma obCoef_rank_le {κ : Sentence → ℕ}
    (U : PrefixMachinePresentation κ) (j i n : ℕ) :
    (obCoef U j i n).rank ≤ n := by
  have hchain := armChain_rank (obBuySig U j i)
    (fun m ↦ obBuySig_rank_le U j i m) n
  have hsig := obBuySig_rank_le U j i n
  simp only [obCoef, EF.rank, max_le_iff]
  omega

/-- Sum of rung coefficients `1, …, m` for one sentence on day `n`. -/
def obSentenceEF {κ : Sentence → ℕ} (U : PrefixMachinePresentation κ)
    (n i : ℕ) : ℕ → EF
  | 0 => .const 0
  | (m + 1) => .add (obSentenceEF U n i m) (obCoef U (m + 1) i n)

lemma obSentenceEF_denote {κ : Sentence → ℕ}
    (U : PrefixMachinePresentation κ) (P : History) (n i : ℕ) : ∀ m,
    (obSentenceEF U n i m).denote P =
      ∑ k ∈ Finset.range m,
        ((k + 1 : ℕ) : ℝ) ^ 2 * obShares U P (k + 1) i n
  | 0 => by simp [obSentenceEF]
  | (m + 1) => by
      rw [obSentenceEF]
      simp only [EF.denote_add, Pi.add_apply]
      rw [obSentenceEF_denote U P n i m, Finset.sum_range_succ,
        obCoef_denote]

lemma obSentenceEF_rank_le {κ : Sentence → ℕ}
    (U : PrefixMachinePresentation κ) (n i : ℕ) : ∀ m,
    (obSentenceEF U n i m).rank ≤ n
  | 0 => by simp [obSentenceEF]
  | (m + 1) => by
      have hprev := obSentenceEF_rank_le U n i m
      have hcoef := obCoef_rank_le U (m + 1) i n
      simp only [obSentenceEF, EF.rank, max_le_iff]
      omega

/-! ## Literal token emission -/

/-- Any polynomially fueled natural stream has polynomially fueled rational-cast tokens. -/
lemma ratNatCast_codes_of_polyFueled {cf : Nat.Partrec.Code} {f : ℕ → ℕ}
    (hf : PolyFueled cf f) : PolyRatCodes (fun x ↦ ((f x : ℕ) : ℚ)) := by
  obtain ⟨cadd, hadd⟩ := addc_polyFueled
  have hdouble := hadd.comp (hf.pair hf)
  refine ⟨_, (hdouble.pair (PolyFueled.const 1)).of_eq (fun x ↦ ?_)⟩
  rw [encode_rat_natCast]
  simp only [Nat.unpair_pair]
  congr 1
  omega

/-- One historical arm-chain multiplication block. -/
def obArmBlock {κ : Sentence → ℕ} (U : PrefixMachinePresentation κ)
    (j i d : ℕ) : List ℕ :=
  (oneMinus (obBuySig U j i d)).serialize ++ [3]

lemma serialize_armChain_obBuy {κ : Sentence → ℕ}
    (U : PrefixMachinePresentation κ) (j i : ℕ) : ∀ n,
    (armChain (obBuySig U j i) n).serialize =
      [1, Encodable.encode ((1 : ℚ))] ++
        (List.range n).flatMap (fun d ↦ obArmBlock U j i d)
  | 0 => by simp [armChain, EF.serialize]
  | (n + 1) => by
      rw [armChain]
      simp only [EF.serialize]
      rw [serialize_armChain_obBuy U j i n, List.range_succ,
        List.flatMap_append, List.flatMap_singleton, obArmBlock]
      simp [List.append_assoc]

lemma serialize_obCoef {κ : Sentence → ℕ}
    (U : PrefixMachinePresentation κ) (j i n : ℕ) :
    (obCoef U j i n).serialize =
      [1, Encodable.encode (((j ^ 2 : ℕ) : ℚ))] ++
        (armChain (obBuySig U j i) n).serialize ++
        (obBuySig U j i n).serialize ++ [3, 3] := by
  simp [obCoef, EF.serialize, List.append_assoc]

lemma serialize_obSentenceEF {κ : Sentence → ℕ}
    (U : PrefixMachinePresentation κ) (n i : ℕ) : ∀ m,
    (obSentenceEF U n i m).serialize =
      [1, Encodable.encode ((0 : ℚ))] ++
        (List.range m).flatMap
          (fun j' ↦ (obCoef U (j' + 1) i n).serialize ++ [2])
  | 0 => by simp [obSentenceEF, EF.serialize]
  | (m + 1) => by
      rw [obSentenceEF]
      simp only [EF.serialize]
      rw [serialize_obSentenceEF U n i m, List.range_succ,
        List.flatMap_append, List.flatMap_singleton]
      simp [List.append_assoc]

/-- Segment emitter for the variable-width padded historical arm block. The input is
`⟨⟨⟨n,i⟩,j'⟩,d⟩`; only `i`, `j'`, and historical day `d` enter the block. -/
lemma obArmBlock_polySegStream {κ : Sentence → ℕ}
    (U : PrefixMachinePresentation κ) (emit : OccamThresholdEmission U) :
    PolySegStream (fun x ↦ obArmBlock U
      (x.unpair.1.unpair.2 + 1)
      x.unpair.1.unpair.1.unpair.2 x.unpair.2) := by
  have hz : PolyFueled _ (fun x ↦ x.unpair.1.unpair.1) :=
    PolyFueled.left.comp PolyFueled.left
  have hsig := obBuySig_polySegStream U emit
    (PolyFueled.right.comp PolyFueled.left)
    (PolyFueled.right.comp hz) PolyFueled.right
  have hone := PolySegStream.serialize_oneMinus hsig
  refine PolySegStream.of_eq
    (hone.append (PolySegStream.ofTokenStream (PolyTokenStream.const 3))) ?_
  intro x
  simp [obArmBlock]

/-- Segment emitter for one rung chunk of one sentence trade. The input is
`⟨⟨n,i⟩,j'⟩`. -/
lemma obRungChunk_polySegStream {κ : Sentence → ℕ}
    (U : PrefixMachinePresentation κ) (emit : OccamThresholdEmission U) :
    PolySegStream (fun m ↦
      (obCoef U (m.unpair.2 + 1) m.unpair.1.unpair.2
        m.unpair.1.unpair.1).serialize ++ [2]) := by
  have hday : PolyFueled _ (fun m ↦ m.unpair.1.unpair.1) :=
    PolyFueled.left.comp PolyFueled.left
  have hidx : PolyFueled _ (fun m ↦ m.unpair.1.unpair.2) :=
    PolyFueled.right.comp PolyFueled.left
  obtain ⟨cmul, hmul⟩ := mul_polyFueled
  have hj1 := PolyFueled.right.succ_comp
  have hsq : PolyFueled _ (fun m ↦ (m.unpair.2 + 1) ^ 2) :=
    (hmul.comp (hj1.pair hj1)).of_eq (fun m ↦ by
      simp only [Nat.unpair_pair]
      ring)
  have segA : PolySegStream (fun m ↦
      (EF.const ((((m.unpair.2 + 1) ^ 2 : ℕ) : ℚ))).serialize) :=
    PolySegStream.ofTokenStream
      (PolyTokenStream.serialize_const_comp
        (ratNatCast_codes_of_polyFueled hsq))
  have segB : PolySegStream (fun _ : ℕ ↦
      [1, Encodable.encode ((1 : ℚ))]) :=
    PolySegStream.ofTokenStream
      ((PolyTokenStream.const 1).append (PolyTokenStream.const _))
  have segC := PolySegStream.concatVar (obArmBlock_polySegStream U emit) hday
  have segD := obBuySig_polySegStream U emit PolyFueled.right hidx hday
  have segE : PolySegStream (fun _ : ℕ ↦ [3, 3, 2]) :=
    PolySegStream.ofTokenStream ((PolyTokenStream.const 3).append
      ((PolyTokenStream.const 3).append (PolyTokenStream.const 2)))
  refine PolySegStream.of_eq
    ((((segA.append segB).append segC).append segD).append segE) ?_
  intro m
  rw [serialize_obCoef, serialize_armChain_obBuy]
  simp [Nat.unpair_pair, EF.serialize, Nat.cast_add, Nat.cast_pow,
    List.append_assoc]

/-- One fully framed sentence trade `⟨coefficient, sentence⟩`, indexed by `⟨n,i⟩`. -/
lemma obTradeChunk_polySegStream {κ : Sentence → ℕ}
    (U : PrefixMachinePresentation κ) (emit : OccamThresholdEmission U) :
    PolySegStream (fun z ↦ serializeTrades
      [(obSentenceEF U z.unpair.1 z.unpair.2 z.unpair.1,
        U.sentence z.unpair.2)]) := by
  have seg0 : PolySegStream (fun _ : ℕ ↦
      [1, Encodable.encode ((0 : ℚ))]) :=
    PolySegStream.ofTokenStream
      ((PolyTokenStream.const 1).append (PolyTokenStream.const _))
  have segRungs := PolySegStream.concatVar
    (obRungChunk_polySegStream U emit) PolyFueled.left
  obtain ⟨cs, hs⟩ := U.sentence_codes
  have segTail : PolySegStream (fun z ↦
      [6, Encodable.encode (U.sentence z.unpair.2)]) :=
    PolySegStream.ofTokenStream
      ((PolyTokenStream.const 6).append
        (PolyTokenStream.polyTok (hs.comp PolyFueled.right)))
  refine PolySegStream.of_eq ((seg0.append segRungs).append segTail) ?_
  intro z
  rw [serializeTrades, serializeTrades, serialize_obSentenceEF]
  simp [Nat.unpair_pair]

/-- The concrete Occam scale ladder. On day `n`, it considers the first `n` sentences and
the first `n` risk rungs. -/
def obTrader {κ : Sentence → ℕ} (U : PrefixMachinePresentation κ) : Trader where
  strat n := {
    trades := (List.range n).map (fun i ↦ (obSentenceEF U n i n, U.sentence i))
    rank_le := by
      intro p hp
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
      exact obSentenceEF_rank_le U n i n }

/-- The actual Occam trader has a token-indexed polynomial emitter. Both nested triangular
runs use the repository's proved variable-width prefix scanner, so padding branches and
varying rational tokens are handled literally rather than by a whole-strategy oracle. -/
lemma obTrader_ecTok {κ : Sentence → ℕ}
    (U : PrefixMachinePresentation κ) (emit : OccamThresholdEmission U) :
    EfficientlyComputableTok (obTrader U) := by
  have chunks := PolySegStream.concatVar
    (obTradeChunk_polySegStream U emit) PolyFueled.id
  refine ecTok_of_segStream _ (PolySegStream.of_eq chunks ?_)
  intro n
  show _ = serializeTrades ((obTrader U).strat n).trades
  rw [show ((obTrader U).strat n).trades =
      (List.range n).map (fun i ↦
        (obSentenceEF U n i n, U.sentence i)) from rfl,
    serializeTrades_map_singleton]
  simp [Nat.unpair_pair]

#print axioms obTrader_ecTok

lemma obTrader_value {κ : Sentence → ℕ}
    (U : PrefixMachinePresentation κ) (P : History) (v : Valuation) (n : ℕ) :
    ((obTrader U).strat n).value P v =
      ∑ i ∈ Finset.range n, ∑ k ∈ Finset.range n,
        ((k + 1 : ℕ) : ℝ) ^ 2 * obShares U P (k + 1) i n *
          (v (U.sentence i) - P n (U.sentence i)) := by
  simp only [obTrader, Strategy.value, List.map_map, Function.comp_def,
    obSentenceEF_denote, Finset.sum_mul]
  rfl

lemma obTrader_netWorth {κ : Sentence → ℕ}
    (U : PrefixMachinePresentation κ) (P : History) (v : PCWorld) (m : ℕ) :
    (obTrader U).netWorth P v m =
      ∑ n ∈ Finset.range (m + 1),
        ∑ i ∈ Finset.range n, ∑ k ∈ Finset.range n,
          ((k + 1 : ℕ) : ℝ) ^ 2 * obShares U P (k + 1) i n *
            (v.payout (U.sentence i) - P n (U.sentence i)) := by
  simp only [Trader.netWorth, obTrader_value]

lemma PrefixMachinePresentation.weight_le_one {κ : Sentence → ℕ}
    (U : PrefixMachinePresentation κ) (i : ℕ) :
    prefixWeight κ (U.sentence i) ≤ 1 := by
  have hmem : i ∈ Finset.range (i + 1) := Finset.mem_range.mpr (by omega)
  have hsingle : prefixWeight κ (U.sentence i) ≤
      ∑ r ∈ Finset.range (i + 1), prefixWeight κ (U.sentence r) :=
    Finset.single_le_sum
      (fun r _ ↦ (prefixWeight_pos κ (U.sentence r)).le) hmem
  exact hsingle.trans (U.kraft (i + 1))

/-- Any-world loss of one Occam position is bounded by its allocated Kraft risk. -/
lemma obTerm_ge {κ : Sentence → ℕ}
    (U : PrefixMachinePresentation κ) (P : History) (v : PCWorld)
    {j i : ℕ} (hj : 1 ≤ j) (n : ℕ) :
    -(obShares U P j i n *
        (prefixWeight κ (U.sentence i) / (j : ℝ) ^ 2)) ≤
      (j : ℝ) ^ 2 * obShares U P j i n *
        (v.payout (U.sentence i) - P n (U.sentence i)) := by
  have hs := obShares_nonneg U P j i n
  rcases hs.lt_or_eq with hspos | hs0
  · have hsig := obShares_pos_sig hspos
    have hprice0 := obBuySig_pos_imp U P hj hsig
    have hjR : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
    have happ := U.approximation_le n i
    have hprice : P n (U.sentence i) <
        prefixWeight κ (U.sentence i) / (j : ℝ) ^ 4 :=
      hprice0.trans_le (div_le_div_of_nonneg_right happ (by positivity))
    have hpayout : 0 ≤ v.payout (U.sentence i) := by
      rw [PCWorld.payout]
      split <;> norm_num
    have hdiff : -(prefixWeight κ (U.sentence i) / (j : ℝ) ^ 4) ≤
        v.payout (U.sentence i) - P n (U.sentence i) := by
      linarith
    have hmul0 : 0 ≤ (j : ℝ) ^ 2 * obShares U P j i n :=
      mul_nonneg (sq_nonneg _) hspos.le
    calc
      -(obShares U P j i n *
          (prefixWeight κ (U.sentence i) / (j : ℝ) ^ 2)) =
          (j : ℝ) ^ 2 * obShares U P j i n *
            (-(prefixWeight κ (U.sentence i) / (j : ℝ) ^ 4)) := by
              field_simp [ne_of_gt hjR]
      _ ≤ _ := mul_le_mul_of_nonneg_left hdiff hmul0
  · rw [← hs0]
    norm_num

/-- In a world satisfying the selected sentence, its Occam position earns the remaining
capacity minus its Kraft-priced acquisition cost. -/
lemma obTerm_profit {κ : Sentence → ℕ}
    (U : PrefixMachinePresentation κ) (P : History) (v : PCWorld)
    {j i : ℕ} (hv : v.Holds (U.sentence i)) (hj : 1 ≤ j) (n : ℕ) :
    (j : ℝ) ^ 2 * obShares U P j i n *
        (1 - prefixWeight κ (U.sentence i) / (j : ℝ) ^ 4) ≤
      (j : ℝ) ^ 2 * obShares U P j i n *
        (v.payout (U.sentence i) - P n (U.sentence i)) := by
  have hs := obShares_nonneg U P j i n
  rcases hs.lt_or_eq with hspos | hs0
  · have hsig := obShares_pos_sig hspos
    have hprice0 := obBuySig_pos_imp U P hj hsig
    have hjR : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
    have happ := U.approximation_le n i
    have hprice : P n (U.sentence i) <
        prefixWeight κ (U.sentence i) / (j : ℝ) ^ 4 :=
      hprice0.trans_le (div_le_div_of_nonneg_right happ (by positivity))
    have hpayout : v.payout (U.sentence i) = 1 := by
      rw [PCWorld.payout, if_pos hv]
    rw [hpayout]
    exact mul_le_mul_of_nonneg_left (by linarith)
      (mul_nonneg (sq_nonneg _) hspos.le)
  · rw [← hs0]
    norm_num

lemma obShares_sum_range_le_one {κ : Sentence → ℕ}
    (U : PrefixMachinePresentation κ) (P : History) (j i N : ℕ) :
    ∑ n ∈ Finset.range N, obShares U P j i n ≤ 1 := by
  by_cases hstart : obStart j i ≤ N
  · have hsplit := Finset.sum_range_add_sum_Ico
      (fun n ↦ obShares U P j i n) hstart
    have hzero : ∑ n ∈ Finset.range (obStart j i), obShares U P j i n = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      simp only [Finset.mem_range] at hn
      rw [obShares, obBuySig_denote_pad U P hn, mul_zero]
    rw [hzero, zero_add] at hsplit
    rw [← hsplit]
    exact obShares_sum_le_one U P hstart
  · have hall : ∀ n ∈ Finset.range N, obShares U P j i n = 0 := by
      intro n hn
      simp only [Finset.mem_range] at hn
      rw [obShares, obBuySig_denote_pad U P (by omega), mul_zero]
    rw [Finset.sum_eq_zero hall]
    norm_num

lemma obShares_sum_range_eq_one_of_fire {κ : Sentence → ℕ}
    (U : PrefixMachinePresentation κ) (P : History)
    {j i n : ℕ} (hj : 1 ≤ j) (hlive : obStart j i ≤ n)
    (ha : 0 < U.approximation n i)
    (hprice : P n (U.sentence i) < ((obBase U j n i : ℚ) : ℝ)) :
    ∑ d ∈ Finset.range (n + 1), obShares U P j i d = 1 := by
  have harm0 : (armChain (obBuySig U j i) (n + 1)).denote P = 0 := by
    rw [armChain_denote_succ, obBuySig_eq_one U P hj hlive ha hprice]
    ring
  have hIco : ∑ d ∈ Finset.Ico (obStart j i) (n + 1),
      obShares U P j i d = 1 := by
    rw [obShares_sum U P (by omega), harm0, sub_zero]
  have hsplit := Finset.sum_range_add_sum_Ico
    (fun d ↦ obShares U P j i d) (show obStart j i ≤ n + 1 by omega)
  have hzero : ∑ d ∈ Finset.range (obStart j i), obShares U P j i d = 0 := by
    apply Finset.sum_eq_zero
    intro d hd
    simp only [Finset.mem_range] at hd
    rw [obShares, obBuySig_denote_pad U P hd, mul_zero]
  linarith

/-- A limiting belief below one quarter of rung `j`'s capacity-adjusted Kraft mass forces
one later full continuous-gate trigger. -/
lemma exists_ob_fire_of_low_limit
    {κ : Sentence → ℕ} (U : PrefixMachinePresentation κ)
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    {j i : ℕ} (hj : 1 ≤ j)
    (hlow : limitingBelief P (U.sentence i) <
      prefixWeight κ (U.sentence i) / (4 * (j : ℝ) ^ 4)) :
    ∃ n, obStart j i ≤ n ∧ 0 < U.approximation n i ∧
      P n (U.sentence i) < ((obBase U j n i : ℚ) : ℝ) := by
  have hjR : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
  have hconv := lic_limitingBelief_tendsto P DP hworld (U.sentence i)
  have happ := U.approximation_tendsto i
  have hscale : Tendsto
      (fun n ↦ (1 / (2 * (j : ℝ) ^ 4)) *
        ((U.approximation n i : ℚ) : ℝ)) atTop
      (𝓝 ((1 / (2 * (j : ℝ) ^ 4)) * prefixWeight κ (U.sentence i))) :=
    happ.const_mul _
  have hdiff := hconv.sub hscale
  have hlimneg : limitingBelief P (U.sentence i) -
      (1 / (2 * (j : ℝ) ^ 4)) * prefixWeight κ (U.sentence i) < 0 := by
    have hwpos := prefixWeight_pos κ (U.sentence i)
    calc
      limitingBelief P (U.sentence i) -
          (1 / (2 * (j : ℝ) ^ 4)) * prefixWeight κ (U.sentence i) <
          prefixWeight κ (U.sentence i) / (4 * (j : ℝ) ^ 4) -
            (1 / (2 * (j : ℝ) ^ 4)) * prefixWeight κ (U.sentence i) := by
              linarith
      _ < 0 := by
        field_simp [ne_of_gt hjR]
        nlinarith
  have hgap : ∀ᶠ n in atTop,
      P n (U.sentence i) -
        (1 / (2 * (j : ℝ) ^ 4)) * ((U.approximation n i : ℚ) : ℝ) < 0 :=
    (tendsto_order.1 hdiff).2 _ hlimneg
  have hapos : ∀ᶠ n in atTop, 0 < ((U.approximation n i : ℚ) : ℝ) :=
    (tendsto_order.1 happ).1 0 (prefixWeight_pos κ (U.sentence i))
  have hevent : ∀ᶠ n in atTop,
      0 < U.approximation n i ∧
        P n (U.sentence i) < ((obBase U j n i : ℚ) : ℝ) := by
    filter_upwards [hgap, hapos] with n hgn han
    constructor
    · exact_mod_cast han
    · rw [obBase_cast]
      calc
        P n (U.sentence i) <
            (1 / (2 * (j : ℝ) ^ 4)) * ((U.approximation n i : ℚ) : ℝ) := by
              linarith
        _ = ((U.approximation n i : ℚ) : ℝ) / (2 * (j : ℝ) ^ 4) := by
          ring
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hevent
  let n := max (obStart j i) N
  exact ⟨n, le_max_left _ _, (hN n (le_max_right _ _)).1,
    (hN n (le_max_right _ _)).2⟩

/-- Actual cumulative Kraft risk through day `N-1`. -/
noncomputable def obCumulativeRisk {κ : Sentence → ℕ}
    (U : PrefixMachinePresentation κ) (P : History) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, ∑ i ∈ Finset.range n, ∑ k ∈ Finset.range n,
    obShares U P (k + 1) i n *
      (prefixWeight κ (U.sentence i) / ((k + 1 : ℕ) : ℝ) ^ 2)

/-- The Occam ladder risks at most `Σ_j 1/j² ≤ 2` over its entire history. -/
lemma obCumulativeRisk_le_two {κ : Sentence → ℕ}
    (U : PrefixMachinePresentation κ) (P : History) (N : ℕ) :
    obCumulativeRisk U P N ≤ 2 := by
  have hnonneg : ∀ j i n,
      0 ≤ obShares U P j i n *
        (prefixWeight κ (U.sentence i) / (j : ℝ) ^ 2) := by
    intro j i n
    exact mul_nonneg (obShares_nonneg U P j i n)
      (div_nonneg (prefixWeight_pos κ (U.sentence i)).le (sq_nonneg _))
  have hextend : obCumulativeRisk U P N ≤
      ∑ n ∈ Finset.range N, ∑ i ∈ Finset.range N, ∑ k ∈ Finset.range N,
        obShares U P (k + 1) i n *
          (prefixWeight κ (U.sentence i) / ((k + 1 : ℕ) : ℝ) ^ 2) := by
    apply Finset.sum_le_sum
    intro n hn
    have hnN : n ≤ N := (Finset.mem_range.mp hn).le
    calc
      (∑ i ∈ Finset.range n, ∑ k ∈ Finset.range n,
          obShares U P (k + 1) i n *
            (prefixWeight κ (U.sentence i) / ((k + 1 : ℕ) : ℝ) ^ 2)) ≤
          ∑ i ∈ Finset.range n, ∑ k ∈ Finset.range N,
            obShares U P (k + 1) i n *
              (prefixWeight κ (U.sentence i) / ((k + 1 : ℕ) : ℝ) ^ 2) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.mpr hnN)
        intro k hkN hkn
        exact hnonneg (k + 1) i n
      _ ≤ ∑ i ∈ Finset.range N, ∑ k ∈ Finset.range N,
            obShares U P (k + 1) i n *
              (prefixWeight κ (U.sentence i) / ((k + 1 : ℕ) : ℝ) ^ 2) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.mpr hnN)
        intro i hiN hin
        exact Finset.sum_nonneg (fun k _ ↦ hnonneg (k + 1) i n)
  calc
    obCumulativeRisk U P N ≤
        ∑ n ∈ Finset.range N, ∑ i ∈ Finset.range N, ∑ k ∈ Finset.range N,
          obShares U P (k + 1) i n *
            (prefixWeight κ (U.sentence i) / ((k + 1 : ℕ) : ℝ) ^ 2) := hextend
    _ = ∑ i ∈ Finset.range N, ∑ n ∈ Finset.range N, ∑ k ∈ Finset.range N,
          obShares U P (k + 1) i n *
            (prefixWeight κ (U.sentence i) / ((k + 1 : ℕ) : ℝ) ^ 2) :=
      Finset.sum_comm
    _ = ∑ i ∈ Finset.range N, ∑ k ∈ Finset.range N, ∑ n ∈ Finset.range N,
          obShares U P (k + 1) i n *
            (prefixWeight κ (U.sentence i) / ((k + 1 : ℕ) : ℝ) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = ∑ k ∈ Finset.range N, ∑ i ∈ Finset.range N, ∑ n ∈ Finset.range N,
          obShares U P (k + 1) i n *
            (prefixWeight κ (U.sentence i) / ((k + 1 : ℕ) : ℝ) ^ 2) :=
      Finset.sum_comm
    _ ≤ ∑ k ∈ Finset.range N, (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk
      have hkpos : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
      calc
        (∑ i ∈ Finset.range N, ∑ n ∈ Finset.range N,
            obShares U P (k + 1) i n *
              (prefixWeight κ (U.sentence i) / ((k + 1 : ℕ) : ℝ) ^ 2)) =
            (1 / ((k + 1 : ℕ) : ℝ) ^ 2) *
              ∑ i ∈ Finset.range N,
                prefixWeight κ (U.sentence i) *
                  ∑ n ∈ Finset.range N, obShares U P (k + 1) i n := by
          calc
            (∑ i ∈ Finset.range N, ∑ n ∈ Finset.range N,
                obShares U P (k + 1) i n *
                  (prefixWeight κ (U.sentence i) / ((k + 1 : ℕ) : ℝ) ^ 2)) =
                ∑ i ∈ Finset.range N,
                  (1 / ((k + 1 : ℕ) : ℝ) ^ 2) *
                    (prefixWeight κ (U.sentence i) *
                      ∑ n ∈ Finset.range N, obShares U P (k + 1) i n) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [Finset.mul_sum, Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro n hn
              ring
            _ = _ := by rw [Finset.mul_sum]
        _ ≤ (1 / ((k + 1 : ℕ) : ℝ) ^ 2) *
              ∑ i ∈ Finset.range N, prefixWeight κ (U.sentence i) := by
          apply mul_le_mul_of_nonneg_left
          · apply Finset.sum_le_sum
            intro i hi
            exact mul_le_of_le_one_right
              (prefixWeight_pos κ (U.sentence i)).le
              (obShares_sum_range_le_one U P (k + 1) i N)
          · positivity
        _ ≤ (1 / ((k + 1 : ℕ) : ℝ) ^ 2) * 1 := by
          gcongr
          exact U.kraft N
        _ = (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2 := mul_one _
    _ ≤ 2 := sum_inv_sq_le_two N

/-- Every plausible-world assessment of the Occam ladder is bounded below by `-2`. -/
lemma obTrader_netWorth_ge_neg_two {κ : Sentence → ℕ}
    (U : PrefixMachinePresentation κ) (P : History) (v : PCWorld) (m : ℕ) :
    -2 ≤ (obTrader U).netWorth P v m := by
  rw [obTrader_netWorth]
  have hterms :
      -(obCumulativeRisk U P (m + 1)) ≤
        ∑ n ∈ Finset.range (m + 1),
          ∑ i ∈ Finset.range n, ∑ k ∈ Finset.range n,
            ((k + 1 : ℕ) : ℝ) ^ 2 * obShares U P (k + 1) i n *
              (v.payout (U.sentence i) - P n (U.sentence i)) := by
    rw [obCumulativeRisk, ← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro n hn
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro i hi
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum (fun k hk ↦ obTerm_ge U P v (by omega) n)
  linarith [obCumulativeRisk_le_two U P (m + 1)]

/-- Market value plus its charged Kraft risk. Every adjusted position is nonnegative in
every world. -/
noncomputable def obAdjustedTerm {κ : Sentence → ℕ}
    (U : PrefixMachinePresentation κ) (P : History) (v : PCWorld)
    (j i n : ℕ) : ℝ :=
  (j : ℝ) ^ 2 * obShares U P j i n *
      (v.payout (U.sentence i) - P n (U.sentence i)) +
    obShares U P j i n *
      (prefixWeight κ (U.sentence i) / (j : ℝ) ^ 2)

lemma obAdjustedTerm_nonneg {κ : Sentence → ℕ}
    (U : PrefixMachinePresentation κ) (P : History) (v : PCWorld)
    {j : ℕ} (hj : 1 ≤ j) (i n : ℕ) :
    0 ≤ obAdjustedTerm U P v j i n := by
  dsimp [obAdjustedTerm]
  linarith [obTerm_ge U P v (j := j) (i := i) hj n]

lemma obTargetAdjusted_sum_ge {κ : Sentence → ℕ}
    (U : PrefixMachinePresentation κ) (P : History) (v : PCWorld)
    {j i n : ℕ} (hj : 1 ≤ j) (hv : v.Holds (U.sentence i))
    (hlive : obStart j i ≤ n) (ha : 0 < U.approximation n i)
    (hprice : P n (U.sentence i) < ((obBase U j n i : ℚ) : ℝ)) :
    (j : ℝ) ^ 2 *
        (1 - prefixWeight κ (U.sentence i) / (j : ℝ) ^ 4) ≤
      ∑ d ∈ Finset.range (n + 1), obAdjustedTerm U P v j i d := by
  have hshares := obShares_sum_range_eq_one_of_fire U P hj hlive ha hprice
  calc
    (j : ℝ) ^ 2 *
        (1 - prefixWeight κ (U.sentence i) / (j : ℝ) ^ 4) =
        ∑ d ∈ Finset.range (n + 1),
          (j : ℝ) ^ 2 * obShares U P j i d *
            (1 - prefixWeight κ (U.sentence i) / (j : ℝ) ^ 4) := by
      have hfac : ∑ d ∈ Finset.range (n + 1),
            (j : ℝ) ^ 2 * obShares U P j i d *
              (1 - prefixWeight κ (U.sentence i) / (j : ℝ) ^ 4) =
          ((j : ℝ) ^ 2 *
            (1 - prefixWeight κ (U.sentence i) / (j : ℝ) ^ 4)) *
              ∑ d ∈ Finset.range (n + 1), obShares U P j i d := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun d hd ↦ by ring)
      rw [hfac, hshares, mul_one]
    _ ≤ _ := Finset.sum_le_sum (fun d hd ↦ by
      have hprofit := obTerm_profit U P v hv hj d
      have hrisk : 0 ≤ obShares U P j i d *
          (prefixWeight κ (U.sentence i) / (j : ℝ) ^ 2) :=
        mul_nonneg (obShares_nonneg U P j i d)
          (div_nonneg (prefixWeight_pos κ (U.sentence i)).le (sq_nonneg _))
      dsimp [obAdjustedTerm]
      linarith)

/-- The selected target's adjusted lifetime value is contained in the full triangular
portfolio sum. -/
lemma obTargetAdjusted_le_triangle {κ : Sentence → ℕ}
    (U : PrefixMachinePresentation κ) (P : History) (v : PCWorld)
    {j i n : ℕ} (hj : 1 ≤ j) :
    ∑ d ∈ Finset.range (n + 1), obAdjustedTerm U P v j i d ≤
      ∑ d ∈ Finset.range (n + 1), ∑ r ∈ Finset.range d,
        ∑ k ∈ Finset.range d, obAdjustedTerm U P v (k + 1) r d := by
  apply Finset.sum_le_sum
  intro d hd
  by_cases hactive : obStart j i ≤ d
  · have hi : i ∈ Finset.range d := Finset.mem_range.mpr (by
      dsimp [obStart] at hactive
      omega)
    have hk : j - 1 ∈ Finset.range d := Finset.mem_range.mpr (by
      dsimp [obStart] at hactive
      omega)
    have hinner : obAdjustedTerm U P v j i d ≤
        ∑ k ∈ Finset.range d, obAdjustedTerm U P v (k + 1) i d := by
      have hs : obAdjustedTerm U P v ((j - 1) + 1) i d ≤
          ∑ k ∈ Finset.range d, obAdjustedTerm U P v (k + 1) i d :=
        Finset.single_le_sum
          (s := Finset.range d)
          (f := fun k ↦ obAdjustedTerm U P v (k + 1) i d)
          (fun k _ ↦ obAdjustedTerm_nonneg U P v
            (j := k + 1) (by omega) i d) hk
      simpa [Nat.sub_add_cancel hj] using hs
    have houter : (∑ k ∈ Finset.range d,
        obAdjustedTerm U P v (k + 1) i d) ≤
        ∑ r ∈ Finset.range d, ∑ k ∈ Finset.range d,
          obAdjustedTerm U P v (k + 1) r d :=
      Finset.single_le_sum
        (fun r _ ↦ Finset.sum_nonneg
          (fun k _ ↦ obAdjustedTerm_nonneg U P v
            (j := k + 1) (by omega) r d)) hi
    exact hinner.trans houter
  · have hdstart : d < obStart j i := by omega
    have hs0 : obShares U P j i d = 0 := by
      rw [obShares, obBuySig_denote_pad U P hdstart, mul_zero]
    rw [obAdjustedTerm, hs0]
    norm_num
    exact Finset.sum_nonneg (fun r _ ↦ Finset.sum_nonneg
      (fun k _ ↦ obAdjustedTerm_nonneg U P v (by omega) r d))

lemma obNetWorth_add_risk {κ : Sentence → ℕ}
    (U : PrefixMachinePresentation κ) (P : History) (v : PCWorld) (m : ℕ) :
    (obTrader U).netWorth P v m + obCumulativeRisk U P (m + 1) =
      ∑ n ∈ Finset.range (m + 1), ∑ i ∈ Finset.range n,
        ∑ k ∈ Finset.range n, obAdjustedTerm U P v (k + 1) i n := by
  rw [obTrader_netWorth, obCumulativeRisk]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  dsimp [obAdjustedTerm]

/-- The Occam ladder genuinely exploits whenever every rung finds one sufficiently
underpriced sentence that remains propositionally possible. -/
lemma obTrader_exploits {κ : Sentence → ℕ}
    (U : PrefixMachinePresentation κ) (P : History) (DP : DeductiveProcess)
    (hfire : ∀ j, 1 ≤ j → ∃ i n, ∃ v : PCWorld,
      obStart j i ≤ n ∧ 0 < U.approximation n i ∧
      P n (U.sentence i) < ((obBase U j n i : ℚ) : ℝ) ∧
      v.ConsistentWith (DP.D n) ∧ v.Holds (U.sentence i)) :
    (obTrader U).Exploits P DP := by
  refine exploits_of_bddBelow_of_unbounded _ _ _ 2 ?_ ?_
  · rintro x ⟨m, v, hv, rfl⟩
    exact obTrader_netWorth_ge_neg_two U P v m
  · intro B
    obtain ⟨j, hjB⟩ := exists_nat_gt (max B 2)
    have hj : 1 ≤ j := by
      have : (2 : ℝ) < (j : ℝ) := lt_of_le_of_lt (le_max_right B 2) hjB
      exact_mod_cast (show (1 : ℝ) ≤ j by linarith)
    obtain ⟨i, n, v, hlive, ha, hprice, hvcons, hv⟩ := hfire j hj
    refine ⟨(obTrader U).netWorth P v n, ⟨n, v, hvcons, rfl⟩, ?_⟩
    have htarget := obTargetAdjusted_sum_ge U P v hj hv hlive ha hprice
    have hcontained := obTargetAdjusted_le_triangle U P v
      (j := j) (i := i) (n := n) hj
    have hcombine := obNetWorth_add_risk U P v n
    have hrisk := obCumulativeRisk_le_two U P (n + 1)
    have hw := U.weight_le_one i
    have hjR : (2 : ℝ) < (j : ℝ) :=
      lt_of_le_of_lt (le_max_right B 2) hjB
    have hbase : (j : ℝ) ^ 2 - 1 ≤
        (j : ℝ) ^ 2 *
          (1 - prefixWeight κ (U.sentence i) / (j : ℝ) ^ 4) := by
      have hjpos : 0 < (j : ℝ) := by linarith
      have hdiv : prefixWeight κ (U.sentence i) / (j : ℝ) ^ 2 ≤ 1 := by
        calc
          prefixWeight κ (U.sentence i) / (j : ℝ) ^ 2 ≤
              1 / (j : ℝ) ^ 2 := div_le_div_of_nonneg_right hw (sq_nonneg _)
          _ ≤ 1 := by
            rw [div_le_one (sq_pos_of_pos hjpos)]
            nlinarith
      field_simp [ne_of_gt hjpos]
      nlinarith
    have hB : B < (j : ℝ) ^ 2 - 3 := by
      have hjgtB : B < (j : ℝ) := lt_of_le_of_lt (le_max_left B 2) hjB
      have hjNat : 2 < j := by exact_mod_cast hjR
      have hj3Nat : 3 ≤ j := by omega
      have hj3R : (3 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj3Nat
      nlinarith
    linarith

#print axioms obTrader_exploits

/-! ## Paper-facing Occam bounds -/

/-- Lower half of `thm:ob`: one fixed constant works for every sentence that remains
propositionally possible at every deductive stage.
Paper node: `thm:ob` -/
theorem lic_occam_lower
    {κ : Sentence → ℕ} (U : PrefixMachinePresentation κ)
    (emit : OccamThresholdEmission U)
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ∃ C : ℝ, 0 < C ∧ ∀ φ,
      (∀ n, ∃ v : PCWorld,
        v.ConsistentWith (DP.D n) ∧ v.Holds φ) →
      C * prefixWeight κ φ ≤ limitingBelief P φ := by
  by_cases hscale : ∃ j : ℕ, 1 ≤ j ∧ ∀ φ,
      (∀ n, ∃ v : PCWorld,
        v.ConsistentWith (DP.D n) ∧ v.Holds φ) →
      prefixWeight κ φ / (4 * (j : ℝ) ^ 4) ≤ limitingBelief P φ
  · obtain ⟨j, hj, hall⟩ := hscale
    have hjR : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
    refine ⟨1 / (4 * (j : ℝ) ^ 4), by positivity, fun φ hφ ↦ ?_⟩
    have h := hall φ hφ
    convert h using 1
    ring
  · exfalso
    have hfire : ∀ j, 1 ≤ j → ∃ i n, ∃ v : PCWorld,
        obStart j i ≤ n ∧ 0 < U.approximation n i ∧
        P n (U.sentence i) < ((obBase U j n i : ℚ) : ℝ) ∧
        v.ConsistentWith (DP.D n) ∧ v.Holds (U.sentence i) := by
      intro j hj
      have hbad : ∃ φ,
          (∀ n, ∃ v : PCWorld,
            v.ConsistentWith (DP.D n) ∧ v.Holds φ) ∧
          limitingBelief P φ <
            prefixWeight κ φ / (4 * (j : ℝ) ^ 4) := by
        by_contra hnone
        apply hscale
        refine ⟨j, hj, fun φ hφ ↦ ?_⟩
        exact le_of_not_gt (fun hlt ↦ hnone ⟨φ, hφ, hlt⟩)
      obtain ⟨φ, hpossible, hlow⟩ := hbad
      obtain ⟨i, hi⟩ := U.covers φ
      have hlowi : limitingBelief P (U.sentence i) <
          prefixWeight κ (U.sentence i) / (4 * (j : ℝ) ^ 4) := by
        simpa only [hi] using hlow
      obtain ⟨n, hlive, ha, hprice⟩ :=
        exists_ob_fire_of_low_limit U P DP hworld hj hlowi
      obtain ⟨v, hvcons, hv⟩ := hpossible n
      exact ⟨i, n, v, hlive, ha, hprice, hvcons, by simpa only [hi] using hv⟩
    exact IsLogicalInductor.noExploit (P := P) (DP := DP)
      (obTrader U) (obTrader_ecTok U emit)
      (obTrader_exploits U P DP hfire)

#print axioms lic_occam_lower

/-- `thm:ob` (Occam Bounds). One fixed positive constant simultaneously supplies the
lower bound for every unrefutable sentence and the upper bound for every unprovable
sentence. The upper half uses only the fixed syntax overhead for negation and the already
verified exclusive–exhaustive limit law.
Paper node: `thm:ob` -/
theorem lic_occamBounds
    {κ : Sentence → ℕ} (U : PrefixMachinePresentation κ)
    (emit : OccamThresholdEmission U) (neg : PrefixNegationCompiler κ)
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hP : ∀ n ψ, 0 ≤ P n ψ ∧ P n ψ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ∃ C : ℝ, 0 < C ∧
      (∀ φ,
        (∀ n, ∃ v : PCWorld,
          v.ConsistentWith (DP.D n) ∧ v.Holds φ) →
        C * prefixWeight κ φ ≤ limitingBelief P φ) ∧
      (∀ φ,
        (∀ n, ∃ v : PCWorld,
          v.ConsistentWith (DP.D n) ∧ ¬ v.Holds φ) →
        limitingBelief P φ ≤ 1 - C * prefixWeight κ φ) := by
  obtain ⟨C₀, hC₀, hlower⟩ := lic_occam_lower U emit P DP hworld
  let d : ℝ := (2 : ℝ) ^ neg.overhead
  have hdpos : 0 < d := by dsimp [d]; positivity
  have hdone : 1 ≤ d := by
    dsimp [d]
    exact one_le_pow₀ (by norm_num)
  refine ⟨C₀ / d, div_pos hC₀ hdpos, ?_, ?_⟩
  · intro φ hpossible
    have hCle : C₀ / d ≤ C₀ := div_le_self hC₀.le hdone
    have hw0 := (prefixWeight_pos κ φ).le
    exact (mul_le_mul_of_nonneg_right hCle hw0).trans (hlower φ hpossible)
  · intro φ hfalsifiable
    have hpossibleNeg : ∀ n, ∃ v : PCWorld,
        v.ConsistentWith (DP.D n) ∧ v.Holds (∼φ) := by
      intro n
      obtain ⟨v, hvcons, hvfalse⟩ := hfalsifiable n
      exact ⟨v, hvcons, (PCWorld.holds_neg v φ).2 hvfalse⟩
    have hnegLower := hlower (∼φ) hpossibleNeg
    have hweight := neg.weight_div_le_neg φ
    have hscaled := mul_le_mul_of_nonneg_left hweight hC₀.le
    have hcomplement := lic_limitingBelief_add_neg P DP hP hworld φ
    have hfactor : (C₀ / d) * prefixWeight κ φ =
        C₀ * (prefixWeight κ φ / (2 : ℝ) ^ neg.overhead) := by
      dsimp [d]
      ring
    rw [hfactor]
    linarith

#print axioms PrefixNegationCompiler.weight_div_le_neg
#print axioms lic_limitingBelief_add_neg
#print axioms lic_occamBounds

end LogicalInduction
