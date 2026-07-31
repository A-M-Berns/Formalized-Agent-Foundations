/-
# Non-Dogmatism: the universal semimeasure (paper §4.6)

Renders `thm:dus` (Domination of the Universal Semimeasure) and `thm:strict` (Strict
Domination), together with the semimeasure substrate and the unit-budget trader they need.

A continuous semimeasure is not a discrete a-priori semimeasure: one path may retain mass
`1` through infinitely many prefixes, so `thm:dus` does not reduce to ordinary sentence
prefix complexity with a fixed coding constant.
-/
import LogicalInduction.Properties.OccamBounds
import LogicalInduction.Properties.LimitCoherence

namespace LogicalInduction

open Filter Topology

/-- A continuous semimeasure on finite bitstrings. Mass can disappear but cannot be
created when a node is split into its two children.
Paper node: `thm:dus` -/
structure ContinuousSemimeasure where
  mass : List Bool → ℝ
  nonneg : ∀ σ, 0 ≤ mass σ
  root_le_one : mass [] ≤ 1
  children_le : ∀ σ,
    mass (σ ++ [false]) + mass (σ ++ [true]) ≤ mass σ

/-- A lower-semicomputable continuous semimeasure, presented by rational approximations
from below. No polynomial clock is required by this mathematical definition.
Paper node: `thm:dus` -/
structure LowerSemicomputableContinuousSemimeasure extends ContinuousSemimeasure where
  approximation : ℕ → List Bool → ℚ
  approximation_code : Nat.Partrec.Code
  approximation_computes : ∀ n σ, ∃ fuel,
    approximation_code.evaln fuel
      (Nat.pair n (Encodable.encode σ)) =
        some (Encodable.encode (approximation n σ))
  approximation_nonneg : ∀ n σ, 0 ≤ approximation n σ
  approximation_mono : ∀ σ, Monotone (fun n ↦ approximation n σ)
  approximation_le : ∀ n σ, ((approximation n σ : ℚ) : ℝ) ≤ mass σ
  approximation_tendsto : ∀ σ,
    Tendsto (fun n ↦ ((approximation n σ : ℚ) : ℝ)) atTop (𝓝 (mass σ))

/-- Universality is the usual multiplicative domination of every lower-semicomputable
continuous semimeasure.
Paper node: `thm:dus` -/
structure UniversalContinuousSemimeasure extends
    LowerSemicomputableContinuousSemimeasure where
  universal : ∀ ν : LowerSemicomputableContinuousSemimeasure,
    ∃ c : ℝ, 0 < c ∧ ∀ σ, c * ν.mass σ ≤ mass σ

/-- The semantic premise behind the independent zero-arity predicates used in `thm:dus`:
every finite Boolean assignment to the atoms remains compatible with every finite deductive
stage.  It carries no preassembled prefix sentence, syntax semantics, market data, or
domination conclusion.
Paper node: `thm:dus` -/
structure IndependentBitAtoms (DP : DeductiveProcess) where
  atom : ℕ → Sentence
  realizable : ∀ (n : ℕ) (f : ℕ → Bool), ∃ v : PCWorld,
    v.ConsistentWith (DP.D n) ∧ ∀ k, (v.Holds (atom k) ↔ f k = true)

/-- Propositional syntax for the independent zero-arity predicates and their finite-prefix
conjunctions from `thm:dus`. `holds_prefix` fixes the exact Boolean semantics, while
`finite_realizable` records compatibility with each finite deductive stage.  The
enumeration/code fields record the paper's efficient list of all finite strings.

`prefix_codes` is the paper's efficient naming of the prefix sentences, metered in
**symbols** (`RpnSentenceCodes`, `dd:ec`) rather than in the whole pair-code value.  That
choice is forced: a literal prefix conjunction's Gödel code grows as `2 ^ 4 ^ m` against an
enumeration index `≤ 5 ^ 2 ^ m`, so the whole-value form of this field is *unsatisfiable*
(`not_polySentenceCodes_bitPrefixSentence`, `Construction/Witnesses/BitPrefixSyntax.lean`)
while its canonical Polish run is `Θ(m)` tiny tokens.  The structure is inhabited over the
repo's concrete atoms by `ordinaryBitPrefixSentences`.
Paper node: `thm:dus` -/
structure BitPrefixSentences (DP : DeductiveProcess) where
  atom : ℕ → Sentence
  prefixSentence : List Bool → Sentence
  enumeration : ℕ → List Bool
  enumeration_covers : ∀ σ, ∃ i, enumeration i = σ
  prefix_codes : RpnSentenceCodes (fun i ↦ prefixSentence (enumeration i))
  holds_prefix : ∀ (v : PCWorld) (σ : List Bool), v.Holds (prefixSentence σ) ↔
    ∀ k : Fin σ.length, (v.Holds (atom k) ↔ σ.get k = true)
  realizable : ∀ (n : ℕ) (f : ℕ → Bool), ∃ v : PCWorld,
    v.ConsistentWith (DP.D n) ∧ ∀ k, (v.Holds (atom k) ↔ f k = true)

/-- The finite-prefix form of realizability: every finite bit string is compatible with
every finite deductive stage.  Specialization of the total field, which is what a theory
constraining infinitely many bits (`thm:strict`) needs. -/
lemma IndependentBitAtoms.finite_realizable {DP : DeductiveProcess}
    (I : IndependentBitAtoms DP) (n : ℕ) (σ : List Bool) : ∃ v : PCWorld,
      v.ConsistentWith (DP.D n) ∧
        ∀ k : Fin σ.length, (v.Holds (I.atom k) ↔ σ.get k = true) := by
  obtain ⟨v, hv, hbits⟩ := I.realizable n (fun k ↦ σ.getD k false)
  refine ⟨v, hv, fun k ↦ ?_⟩
  rw [hbits k, List.getD_eq_getElem _ _ k.isLt]
  simp

/-- The finite-prefix form of realizability for an assembled prefix presentation. -/
lemma BitPrefixSentences.finite_realizable {DP : DeductiveProcess}
    (B : BitPrefixSentences DP) (n : ℕ) (σ : List Bool) : ∃ v : PCWorld,
      v.ConsistentWith (DP.D n) ∧
        ∀ k : Fin σ.length, (v.Holds (B.atom k) ↔ σ.get k = true) := by
  obtain ⟨v, hv, hbits⟩ := B.realizable n (fun k ↦ σ.getD k false)
  refine ⟨v, hv, fun k ↦ ?_⟩
  rw [hbits k, List.getD_eq_getElem _ _ k.isLt]
  simp

lemma BitPrefixSentences.prefix_possible
    {DP : DeductiveProcess} (B : BitPrefixSentences DP) (σ : List Bool) :
    ∀ n, ∃ v : PCWorld,
      v.ConsistentWith (DP.D n) ∧ v.Holds (B.prefixSentence σ) := by
  intro n
  obtain ⟨v, hv, hbits⟩ := B.finite_realizable n σ
  exact ⟨v, hv, (B.holds_prefix v σ).2 hbits⟩

/-! ## Finite semimeasure purchase trees -/

/-- Semimeasure-weighted value of purchases in the binary subtree rooted at `σ`, through
`depth` further bits. -/
noncomputable def semimeasureMean (M : ContinuousSemimeasure)
    (w : List Bool → ℝ) (σ : List Bool) : ℕ → ℝ
  | 0 => M.mass σ * w σ
  | depth + 1 =>
      M.mass σ * w σ +
        semimeasureMean M w (σ ++ [false]) depth +
        semimeasureMean M w (σ ++ [true]) depth

/-- Maximum prefix-purchase payout along a branch, allowing the semimeasure to stop at
any node. With nonnegative purchases, extending a branch can only increase payout. -/
noncomputable def prefixPurchaseMax (w : List Bool → ℝ)
    (σ : List Bool) : ℕ → ℝ
  | 0 => w σ
  | depth + 1 =>
      w σ + max
        (prefixPurchaseMax w (σ ++ [false]) depth)
        (prefixPurchaseMax w (σ ++ [true]) depth)

lemma prefixPurchaseMax_nonneg
    {w : List Bool → ℝ} (hw : ∀ σ, 0 ≤ w σ) :
    ∀ σ depth, 0 ≤ prefixPurchaseMax w σ depth
  | σ, 0 => by simp [prefixPurchaseMax, hw]
  | σ, depth + 1 => by
      rw [prefixPurchaseMax]
      exact add_nonneg (hw σ) (le_max_of_le_left
        (prefixPurchaseMax_nonneg hw (σ ++ [false]) depth))

/-- Preorder enumeration of the finite binary subtree rooted at `σ`. -/
def bitTreeNodes (σ : List Bool) : ℕ → List (List Bool)
  | 0 => [σ]
  | depth + 1 =>
      σ :: (bitTreeNodes (σ ++ [false]) depth ++
        bitTreeNodes (σ ++ [true]) depth)

lemma semimeasureMean_eq_bitTree_sum
    (M : ContinuousSemimeasure) (w : List Bool → ℝ) :
    ∀ σ depth, semimeasureMean M w σ depth =
      ((bitTreeNodes σ depth).map (fun τ ↦ M.mass τ * w τ)).sum
  | σ, 0 => by simp [semimeasureMean, bitTreeNodes]
  | σ, depth + 1 => by
      rw [semimeasureMean, bitTreeNodes]
      simp only [List.map_cons, List.sum_cons, List.map_append, List.sum_append]
      rw [semimeasureMean_eq_bitTree_sum M w (σ ++ [false]) depth,
        semimeasureMean_eq_bitTree_sum M w (σ ++ [true]) depth]
      ring

/-- Every extension by at most `depth` bits occurs in the corresponding finite tree. -/
lemma append_mem_bitTreeNodes (σ ρ : List Bool) :
    ∀ {depth}, ρ.length ≤ depth → σ ++ ρ ∈ bitTreeNodes σ depth := by
  intro depth hlen
  induction depth generalizing σ ρ with
  | zero =>
      have hρ : ρ = [] := List.length_eq_zero_iff.mp (by omega)
      subst ρ
      simp [bitTreeNodes]
  | succ depth ih =>
      cases ρ with
      | nil => simp [bitTreeNodes]
      | cons b ρ =>
          have htail : ρ.length ≤ depth := by simp at hlen; omega
          cases b <;>
            simp only [bitTreeNodes, List.mem_cons, List.mem_append] <;>
            right
          · left
            simpa [List.append_assoc] using ih (σ := σ ++ [false]) (ρ := ρ) htail
          · right
            simpa [List.append_assoc] using ih (σ := σ ++ [true]) (ρ := ρ) htail

/-- Payout accumulated along one branch, including both root and terminal node. -/
noncomputable def prefixPathPayout (w : List Bool → ℝ)
    (σ : List Bool) : List Bool → ℝ
  | [] => w σ
  | b :: bits => w σ + prefixPathPayout w (σ ++ [b]) bits

/-- Nodes visited by `prefixPathPayout`. -/
def prefixPathNodes (σ : List Bool) : List Bool → List (List Bool)
  | [] => [σ]
  | b :: bits => σ :: prefixPathNodes (σ ++ [b]) bits

lemma prefixPathPayout_eq_sum (w : List Bool → ℝ) (σ bits : List Bool) :
    prefixPathPayout w σ bits =
      ((prefixPathNodes σ bits).map w).sum := by
  induction bits generalizing σ with
  | nil => simp [prefixPathPayout, prefixPathNodes]
  | cons b bits ih =>
      simp only [prefixPathPayout, prefixPathNodes, List.map_cons, List.sum_cons]
      rw [ih]

lemma prefixPathNodes_length_ge {σ bits τ : List Bool}
    (hτ : τ ∈ prefixPathNodes σ bits) : σ.length ≤ τ.length := by
  induction bits generalizing σ with
  | nil =>
      simp only [prefixPathNodes, List.mem_singleton] at hτ
      subst τ
      exact le_rfl
  | cons b bits ih =>
      simp only [prefixPathNodes, List.mem_cons] at hτ
      rcases hτ with rfl | hτ
      · exact le_rfl
      · exact (by simp : σ.length ≤ (σ ++ [b]).length) |>.trans (ih hτ)

lemma prefixPathNodes_nodup (σ bits : List Bool) :
    (prefixPathNodes σ bits).Nodup := by
  induction bits generalizing σ with
  | nil => simp [prefixPathNodes]
  | cons b bits ih =>
      rw [prefixPathNodes, List.nodup_cons]
      constructor
      · intro hmem
        have hlen := prefixPathNodes_length_ge hmem
        simp at hlen
      · exact ih (σ ++ [b])

/-- Every path node is a prefix of the terminal string. -/
lemma prefixPathNode_isPrefix {σ bits τ : List Bool}
    (hτ : τ ∈ prefixPathNodes σ bits) :
    ∃ rest, σ ++ bits = τ ++ rest := by
  induction bits generalizing σ with
  | nil =>
      simp only [prefixPathNodes, List.mem_singleton] at hτ
      subst τ
      exact ⟨[], by simp⟩
  | cons b bits ih =>
      simp only [prefixPathNodes, List.mem_cons] at hτ
      rcases hτ with rfl | hτ
      · exact ⟨b :: bits, by simp⟩
      · obtain ⟨rest, hrest⟩ := ih hτ
        refine ⟨rest, ?_⟩
        simpa [List.append_assoc] using hrest

/-- The recursive maximum is attained by an explicit branch of the advertised depth. -/
lemma exists_prefixPathPayout_eq_max (w : List Bool → ℝ) :
    ∀ σ depth, ∃ bits, bits.length = depth ∧
      prefixPathPayout w σ bits = prefixPurchaseMax w σ depth
  | σ, 0 => ⟨[], rfl, by simp [prefixPathPayout, prefixPurchaseMax]⟩
  | σ, depth + 1 => by
      let σ0 := σ ++ [false]
      let σ1 := σ ++ [true]
      obtain ⟨bits0, hlen0, hmax0⟩ :=
        exists_prefixPathPayout_eq_max w σ0 depth
      obtain ⟨bits1, hlen1, hmax1⟩ :=
        exists_prefixPathPayout_eq_max w σ1 depth
      by_cases h : prefixPurchaseMax w σ1 depth ≤ prefixPurchaseMax w σ0 depth
      · refine ⟨false :: bits0, by simp [hlen0], ?_⟩
        simp only [prefixPathPayout, prefixPurchaseMax]
        rw [hmax0, max_eq_left h]
      · have h' : prefixPurchaseMax w σ0 depth ≤ prefixPurchaseMax w σ1 depth :=
          le_of_lt (lt_of_not_ge h)
        refine ⟨true :: bits1, by simp [hlen1], ?_⟩
        simp only [prefixPathPayout, prefixPurchaseMax]
        rw [hmax1, max_eq_right h']

/-- Finite Fubini for a list/finset rectangle. -/
lemma list_sum_finset_comm {α ι : Type*} [DecidableEq ι]
    (nodes : List α) (s : Finset ι) (c : α → ι → ℝ) :
    ((nodes.map (fun x ↦ ∑ i ∈ s, c x i)).sum) =
      ∑ i ∈ s, (nodes.map (fun x ↦ c x i)).sum := by
  induction nodes with
  | nil => simp
  | cons x nodes ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      rw [← Finset.sum_add_distrib]

/-- In a duplicate-free node list, matching one key contributes at most one copy. -/
lemma sum_match_eq_if_mem {α : Type*} [DecidableEq α]
    (nodes : List α) (hnodes : nodes.Nodup) (key : α) (a : ℝ) :
    ((nodes.map (fun x ↦ if key = x then a else 0)).sum) =
      if key ∈ nodes then a else 0 := by
  induction nodes with
  | nil => simp
  | cons x nodes ih =>
      rw [List.nodup_cons] at hnodes
      simp only [List.map_cons, List.sum_cons, ih hnodes.2, List.mem_cons]
      by_cases h : key = x
      · subst key
        simp [hnodes.1]
      · simp [h]

/-- The paper's `MeanPayout ≤ MaxPayout` fact, proved by finite-tree induction directly
from the semimeasure split inequality. Leaked mass is exactly the option to stop at an
internal node. -/
lemma semimeasureMean_le_mass_mul_max
    (M : ContinuousSemimeasure) {w : List Bool → ℝ}
    (hw : ∀ σ, 0 ≤ w σ) : ∀ σ depth,
    semimeasureMean M w σ depth ≤
      M.mass σ * prefixPurchaseMax w σ depth
  | σ, 0 => by simp [semimeasureMean, prefixPurchaseMax]
  | σ, depth + 1 => by
      let σ0 := σ ++ [false]
      let σ1 := σ ++ [true]
      let m0 := prefixPurchaseMax w σ0 depth
      let m1 := prefixPurchaseMax w σ1 depth
      have h0 := semimeasureMean_le_mass_mul_max M hw σ0 depth
      have h1 := semimeasureMean_le_mass_mul_max M hw σ1 depth
      have hm0 : 0 ≤ m0 := prefixPurchaseMax_nonneg hw σ0 depth
      have hm1 : 0 ≤ m1 := prefixPurchaseMax_nonneg hw σ1 depth
      have hweighted : M.mass σ0 * m0 + M.mass σ1 * m1 ≤
          (M.mass σ0 + M.mass σ1) * max m0 m1 := by
        have h0max := mul_le_mul_of_nonneg_left (le_max_left m0 m1) (M.nonneg σ0)
        have h1max := mul_le_mul_of_nonneg_left (le_max_right m0 m1) (M.nonneg σ1)
        nlinarith
      have hsplit := M.children_le σ
      have hmax0 : 0 ≤ max m0 m1 := le_max_of_le_left hm0
      have hsplitScaled :
          (M.mass σ0 + M.mass σ1) * max m0 m1 ≤
            M.mass σ * max m0 m1 :=
        mul_le_mul_of_nonneg_right hsplit hmax0
      rw [semimeasureMean, prefixPurchaseMax]
      change M.mass σ * w σ + semimeasureMean M w σ0 depth +
          semimeasureMean M w σ1 depth ≤
        M.mass σ * (w σ + max m0 m1)
      calc
        M.mass σ * w σ + semimeasureMean M w σ0 depth +
            semimeasureMean M w σ1 depth ≤
          M.mass σ * w σ + M.mass σ0 * m0 + M.mass σ1 * m1 := by
            linarith
        _ ≤ M.mass σ * w σ +
            (M.mass σ0 + M.mass σ1) * max m0 m1 := by linarith
        _ ≤ M.mass σ * w σ + M.mass σ * max m0 m1 := by linarith
        _ = M.mass σ * (w σ + max m0 m1) := by ring

lemma semimeasureMean_root_le_max
    (M : ContinuousSemimeasure) {w : List Bool → ℝ}
    (hw : ∀ σ, 0 ≤ w σ) (depth : ℕ) :
    semimeasureMean M w [] depth ≤ prefixPurchaseMax w [] depth := by
  have hmain := semimeasureMean_le_mass_mul_max M hw [] depth
  have hmax0 := prefixPurchaseMax_nonneg hw [] depth
  have hroot := M.root_le_one
  nlinarith [mul_le_mul_of_nonneg_right hroot hmax0]

/-! ## The direct unit-budget purchase family

Deviation from the appendix, which considers every prefix on every sufficiently late day:
the dovetail below considers one prefix per day, visiting enumeration index `n.unpair.2`
on day `n`, so every index `i` recurs on the unbounded subsequence `Nat.pair m i`.  The
economic argument is unchanged.

The paper first slows an arbitrary lower approximation down to a polynomial-time table.
That compiler fact is kept separate from the mathematical semimeasure presentation: the
structure below carries only the rational table and its syntax-level polynomial
certificate — no prices, purchases, or domination conclusion. -/

/-- Polynomially emitted from-below approximation used by the DUS trader.
Paper node: `thm:dus` -/
structure DUSApproximationPresentation {DP : DeductiveProcess}
    (M : LowerSemicomputableContinuousSemimeasure)
    (B : BitPrefixSentences DP) where
  approximation : ℕ → ℕ → ℚ
  approximation_codes : PolyRatCodes
    (fun z ↦ approximation z.unpair.1 z.unpair.2)
  nonneg : ∀ n i, 0 ≤ approximation n i
  le_mass : ∀ n i,
    ((approximation n i : ℚ) : ℝ) ≤ M.mass (B.enumeration i)
  tendsto : ∀ i,
    Tendsto (fun n ↦ ((approximation n i : ℚ) : ℝ)) atTop
      (𝓝 (M.mass (B.enumeration i)))

/-- Prefix visited on day `n`. Pairing makes every enumeration index recur
infinitely often without changing the polynomial sentence interface. -/
def dusPrefix {DP : DeductiveProcess} (B : BitPrefixSentences DP) (n : ℕ) : List Bool :=
  B.enumeration n.unpair.2

/-- Sentence traded on day `n`. -/
def dusSentence {DP : DeductiveProcess} (B : BitPrefixSentences DP) (n : ℕ) : Sentence :=
  B.prefixSentence (dusPrefix B n)

/-- Half of the support threshold for scale `k`. -/
def dusBase {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (k n : ℕ) : ℚ :=
  A.approximation n n.unpair.2 / (4 * (k + 1))

/-- Flattened base stream used by the uniform family emitter. -/
def dusEmitBase {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (z : ℕ) : ℚ :=
  dusBase A z.unpair.1 z.unpair.2

/-- Derived rational tokens used by the continuous low-price gate. This is a
syntax-only compiler boundary: it contains neither market data nor a domination claim.
Paper node: `thm:dus` -/
structure DUSThresholdEmission {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B) : Prop where
  threshold_sum_codes : PolyRatCodes
    (fun z ↦ dusEmitBase A z + dusEmitBase A z)
  inverse_width_codes : PolyRatCodes (fun z ↦ 1 / dusEmitBase A z)

/-- Dovetailed low-price signal for scale `k`. -/
def dusSignal {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (k n : ℕ) : EF :=
  if n < k then .const 0
  else buyIndEF (dusSentence B n) (dusBase A k n) (dusBase A k n) n

lemma dusSignal_rank_le {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (k n : ℕ) :
    (dusSignal A k n).rank ≤ n := by
  by_cases h : n < k
  · simp [dusSignal, h]
  · simp [dusSignal, h]

lemma dusSignal_mem {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (P : History) (k n : ℕ) :
    0 ≤ (dusSignal A k n).denote P ∧
      (dusSignal A k n).denote P ≤ 1 := by
  by_cases h : n < k
  · simp [dusSignal, h]
  · simpa [dusSignal, h] using
      buyInd_mem (dusSentence B n) (dusBase A k n) (dusBase A k n) n P

lemma dusBase_cast {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (k n : ℕ) :
    ((dusBase A k n : ℚ) : ℝ) =
      ((A.approximation n n.unpair.2 : ℚ) : ℝ) /
        (4 * ((k + 1 : ℕ) : ℝ)) := by
  rw [dusBase]
  push_cast
  ring

lemma dusBase_nonneg {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (k n : ℕ) :
    0 ≤ ((dusBase A k n : ℚ) : ℝ) := by
  rw [dusBase_cast]
  have ha : 0 ≤ ((A.approximation n n.unpair.2 : ℚ) : ℝ) := by
    exact_mod_cast A.nonneg n n.unpair.2
  positivity

lemma dusBase_pos {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    {k n : ℕ} (ha : 0 < A.approximation n n.unpair.2) :
    0 < ((dusBase A k n : ℚ) : ℝ) := by
  rw [dusBase_cast]
  have haR : 0 < ((A.approximation n n.unpair.2 : ℚ) : ℝ) := by
    exact_mod_cast ha
  positivity

/-- A positive signal certifies the paper's price-to-semimeasure ratio bound. -/
lemma dusSignal_pos_imp_price_lt_mass {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (P : History) {k n : ℕ}
    (hsig : 0 < (dusSignal A k n).denote P) :
    P n (dusSentence B n) <
      M.mass (dusPrefix B n) / (2 * ((k + 1 : ℕ) : ℝ)) := by
  have hlive : ¬ n < k := by
    intro h
    simp [dusSignal, h] at hsig
  have ha0 : 0 ≤ A.approximation n n.unpair.2 := A.nonneg n n.unpair.2
  have ha : 0 < A.approximation n n.unpair.2 := by
    rcases ha0.eq_or_lt with ha | ha
    · have hb : ((dusBase A k n : ℚ) : ℝ) = 0 := by
        rw [dusBase_cast]
        have haR : ((A.approximation n n.unpair.2 : ℚ) : ℝ) = 0 := by
          exact_mod_cast ha.symm
        rw [haR]
        simp
      rw [dusSignal, if_neg hlive, buyIndEF_denote, hb] at hsig
      norm_num at hsig
    · exact_mod_cast ha
  rw [dusSignal, if_neg hlive] at hsig
  have hlt := buyInd_pos_imp (dusBase_pos A ha) hsig
  have happ := A.le_mass n n.unpair.2
  have hkpos : 0 < (2 * ((k + 1 : ℕ) : ℝ)) := by positivity
  rw [dusBase_cast] at hlt
  change P n (dusSentence B n) <
    ((A.approximation n n.unpair.2 : ℚ) : ℝ) /
        (4 * ((k + 1 : ℕ) : ℝ)) +
      ((A.approximation n n.unpair.2 : ℚ) : ℝ) /
        (4 * ((k + 1 : ℕ) : ℝ)) at hlt
  calc
    P n (dusSentence B n) <
        ((A.approximation n n.unpair.2 : ℚ) : ℝ) /
          (2 * ((k + 1 : ℕ) : ℝ)) := by
            have heq :
                ((A.approximation n n.unpair.2 : ℚ) : ℝ) /
                    (2 * ((k + 1 : ℕ) : ℝ)) =
                  ((A.approximation n n.unpair.2 : ℚ) : ℝ) /
                      (4 * ((k + 1 : ℕ) : ℝ)) +
                    ((A.approximation n n.unpair.2 : ℚ) : ℝ) /
                      (4 * ((k + 1 : ℕ) : ℝ)) := by ring
            rw [heq]
            exact hlt
    _ ≤ M.mass (dusPrefix B n) /
          (2 * ((k + 1 : ℕ) : ℝ)) := by
      exact div_le_div_of_nonneg_right (by simpa [dusPrefix] using happ) hkpos.le

/-- A strict quarter-threshold dip spends the entire remaining budget. -/
lemma dusSignal_eq_one {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (P : History) {k n : ℕ} (hlive : k ≤ n)
    (ha : 0 < A.approximation n n.unpair.2)
    (hprice : P n (dusSentence B n) < ((dusBase A k n : ℚ) : ℝ)) :
    (dusSignal A k n).denote P = 1 := by
  rw [dusSignal, if_neg (by omega)]
  exact buyInd_eq_one (dusBase_pos A ha) hprice

lemma dusSignal_closed {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (k n : ℕ) (ρ : List ℝ) (P : History) :
    (dusSignal A k n).denoteWith ρ P = (dusSignal A k n).denote P := by
  by_cases h : n < k
  · simp [dusSignal, h, EF.denote]
  · simp [dusSignal, h, buyIndEF, clip01, efMin, EF.denote]

/-- Fraction of the unit budget spent by event `n`, before multiplying by the
remaining-budget coefficient. -/
def dusCostEF {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (k n : ℕ) : EF :=
  .mul (dusSignal A k n) (.price (dusSentence B n) n)

lemma dusCostEF_rank_le {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (k n : ℕ) :
    (dusCostEF A k n).rank ≤ n := by
  simp only [dusCostEF, EF.rank_mul, EF.rank_price, max_le_iff]
  exact ⟨dusSignal_rank_le A k n, le_rfl⟩

lemma dusCostEF_closed {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (k n : ℕ) (ρ : List ℝ) (P : History) :
    (dusCostEF A k n).denoteWith ρ P = (dusCostEF A k n).denote P := by
  simp only [dusCostEF, EF.denoteWith, EF.denote_mul, EF.denote_price, Pi.mul_apply]
  rw [dusSignal_closed A k n ρ P]

/-! ### Uniform syntax emission for the purchase inputs -/

/-- Segment emission for the padded, scale-varying low-price signal. -/
lemma dusSignal_rpnSpliceStream
    {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (emit : DUSThresholdEmission A)
    {ck cn : Nat.Partrec.Code} {kf nf : ℕ → ℕ}
    (hk : PolyFueled ck kf) (hn : PolyFueled cn nf) :
    RpnSpliceStream (fun x ↦ (dusSignal A (kf x) (nf x)).serialize) := by
  have hinput : PolyFueled _ (fun x ↦ Nat.pair (kf x) (nf x)) := hk.pair hn
  have hsumCodes : PolyRatCodes (fun x ↦
      dusBase A (kf x) (nf x) + dusBase A (kf x) (nf x)) := by
    obtain ⟨c, hc⟩ := emit.threshold_sum_codes
    exact ⟨_, (hc.comp hinput).of_eq (fun x ↦ by simp [dusEmitBase])⟩
  have hinvCodes : PolyRatCodes (fun x ↦ 1 / dusBase A (kf x) (nf x)) := by
    obtain ⟨c, hc⟩ := emit.inverse_width_codes
    exact ⟨_, (hc.comp hinput).of_eq (fun x ↦ by simp [dusEmitBase])⟩
  have hidx : PolyFueled _ (fun x ↦ (nf x).unpair.2) :=
    PolyFueled.right.comp hn
  have hprice := RpnSpliceStream.serialize_price B.prefix_codes hidx hn
  have hsum : RpnSpliceStream (fun x ↦
      (EF.const (dusBase A (kf x) (nf x) +
        dusBase A (kf x) (nf x))).serialize) :=
    RpnSpliceStream.serialize_const_comp hsumCodes
  have hinv : RpnSpliceStream (fun x ↦
      (EF.const (1 / dusBase A (kf x) (nf x))).serialize) :=
    RpnSpliceStream.serialize_const_comp hinvCodes
  have hlive : RpnSpliceStream (fun x ↦
      (buyIndEF (dusSentence B (nf x))
        (dusBase A (kf x) (nf x)) (dusBase A (kf x) (nf x))
        (nf x)).serialize) := by
    have hraw := RpnSpliceStream.serialize_mul
      (RpnSpliceStream.serialize_add hsum
        (RpnSpliceStream.serialize_mul
          (RpnSpliceStream.serialize_const (-1))
          hprice)) hinv
    simpa [buyIndEF, dusSentence, dusPrefix] using
      RpnSpliceStream.serialize_clip01 hraw
  have hzero : RpnSpliceStream (fun _ : ℕ ↦ (EF.const 0).serialize) :=
    RpnSpliceStream.serialize_const 0
  have htest : PolyFueled _ (fun x ↦ nf x + 1 - kf x) :=
    (subc_polyFueled.comp (hn.succ_comp.pair hk)).of_eq
      (fun x ↦ by simp only [Nat.unpair_pair])
  refine RpnSpliceStream.of_eq (RpnSpliceStream.ifZero hzero hlive htest) ?_
  intro x
  by_cases hpad : nf x < kf x
  · have ht : nf x + 1 - kf x = 0 := by omega
    simp [ht, dusSignal, hpad]
  · have ht : nf x + 1 - kf x ≠ 0 := by omega
    simp [ht, dusSignal, hpad]

/-- Uniform emission of the per-event spent-fraction feature. -/
lemma dusCostEF_rpnSpliceStream
    {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (emit : DUSThresholdEmission A) :
    RpnSpliceStream (fun z ↦ (dusCostEF A z.unpair.1 z.unpair.2).serialize) := by
  have hsignal := dusSignal_rpnSpliceStream A emit PolyFueled.left PolyFueled.right
  have hidx : PolyFueled _ (fun z ↦ z.unpair.2.unpair.2) :=
    PolyFueled.right.comp PolyFueled.right
  have hprice := RpnSpliceStream.serialize_price B.prefix_codes hidx PolyFueled.right
  exact RpnSpliceStream.serialize_mul hsignal hprice

/-- All earlier purchases remain charged to the one unit of cash. -/
def dusActive (_ _ : ℕ) : Bool := true

lemma dusActive_closing : ROIBudget.ClosingSchedule dusActive := by
  intro i n h
  rfl

/-- Remaining unit budget immediately before the day-`n` purchase. -/
def dusRemainingEF {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (k n : ℕ) : EF :=
  ROIBudget.sharedFeatureWeight dusActive (dusCostEF A k) n

/-- Actual shares purchased on day `n`: remaining cash times the low-price gate. -/
def dusSharesEF {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (k n : ℕ) : EF :=
  .mul (dusRemainingEF A k n) (dusSignal A k n)

/- Uniform emission of the all-open budget-recurrence body for input `⟨k,j⟩`. -/
attribute [local irreducible] Nat.sqrt in
lemma dusWeightBody_rpnSpliceStream
    {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (emit : DUSThresholdEmission A) :
    RpnSpliceStream (fun z ↦
      (ROIBudget.featureWeightBody dusActive (dusCostEF A z.unpair.1)
        z.unpair.2).serialize) := by
  have hk : PolyFueled _ (fun z ↦ z.unpair.1.unpair.1) :=
    PolyFueled.left.comp PolyFueled.left
  have hj : PolyFueled _ (fun z ↦ z.unpair.1.unpair.2) :=
    PolyFueled.right.comp PolyFueled.left
  have hi : PolyFueled _ (fun z ↦ z.unpair.2) := PolyFueled.right
  have hidx : PolyFueled _ (fun z ↦ z.unpair.1.unpair.2 - 1 - z.unpair.2) :=
    (subc_polyFueled.comp
      ((predc_polyFueled.comp hj).pair hi)).of_eq
        (fun z ↦ by simp [Nat.pred_eq_sub_one])
  have hvar : RpnSpliceStream (fun z ↦
      (EF.var (z.unpair.1.unpair.2 - 1 - z.unpair.2)).serialize) :=
    RpnSpliceStream.serialize_var hidx
  have hcanonical : PolyFueled _ (fun z ↦
      Nat.pair z.unpair.1.unpair.1 z.unpair.2) := hk.pair hi
  have hcost : RpnSpliceStream (fun z ↦
      (dusCostEF A z.unpair.1.unpair.1 z.unpair.2).serialize) := by
    refine RpnSpliceStream.of_eq
      ((dusCostEF_rpnSpliceStream A emit).comp hcanonical) ?_
    intro z
    simp only [Nat.unpair_pair]
  have hterm : RpnSpliceStream (fun z ↦
      (EF.mul (EF.var (z.unpair.1.unpair.2 - 1 - z.unpair.2))
        (dusCostEF A z.unpair.1.unpair.1 z.unpair.2)).serialize) :=
    RpnSpliceStream.serialize_mul hvar hcost
  have hterms : RpnSpliceStream (fun z ↦
      (List.range z.unpair.2).flatMap (fun i ↦
        (EF.mul (EF.var (z.unpair.2 - 1 - i))
          (dusCostEF A z.unpair.1 i)).serialize)) := by
    refine RpnSpliceStream.of_eq
      (RpnSpliceStream.concatVar hterm PolyFueled.right) ?_
    intro z
    simp only [Nat.unpair_pair]
  have hzero : RpnSpliceStream (fun _ : ℕ ↦ (EF.const 0).serialize) :=
    RpnSpliceStream.serialize_const 0
  have htags : RpnSpliceStream (fun z ↦ List.replicate z.unpair.2 2) :=
    RpnSpliceStream.repeatTag 2 (by norm_num) PolyFueled.right
  have hsumRaw := (hterms.append hzero).append htags
  have hsum : RpnSpliceStream (fun z ↦
      (ROIBudget.sumFeatures (List.ofFn (fun i : Fin z.unpair.2 ↦
        EF.mul (EF.var (z.unpair.2 - 1 - i))
          (dusCostEF A z.unpair.1 i)))).serialize) := by
    refine RpnSpliceStream.of_eq hsumRaw ?_
    intro z
    rw [ROIBudget.serialize_sumFeatures]
    simp only [List.length_ofFn]
    congr 2
    rw [← List.map_coe_finRange_eq_range, List.flatMap_map]
    simp only [List.ofFn_eq_map, List.flatMap_map]
  have hone : RpnSpliceStream (fun _ : ℕ ↦ (EF.const 1).serialize) :=
    RpnSpliceStream.serialize_const 1
  have hneg : RpnSpliceStream (fun _ : ℕ ↦ (EF.const (-1)).serialize) :=
    RpnSpliceStream.serialize_const (-1)
  have hbody := RpnSpliceStream.serialize_add hone
    (RpnSpliceStream.serialize_mul hneg hsum)
  refine RpnSpliceStream.of_eq hbody ?_
  intro z
  simp only [ROIBudget.featureWeightBody, dusActive, if_true]

/-- The shared remaining-budget feature is uniformly polynomial across both scale and
day; previous recurrence values are referenced by `EF.var`, not duplicated. -/
lemma dusRemainingEF_rpnSpliceStream
    {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (emit : DUSThresholdEmission A) :
    RpnSpliceStream (fun z ↦ (dusRemainingEF A z.unpair.1 z.unpair.2).serialize) := by
  have hbody := dusWeightBody_rpnSpliceStream A emit
  have hcanonical : PolyFueled _ (fun q ↦
      Nat.pair q.unpair.1.unpair.1 q.unpair.2) :=
    (PolyFueled.left.comp PolyFueled.left).pair PolyFueled.right
  have hbodies : RpnSpliceStream (fun z ↦
      (List.range (z.unpair.2 + 1)).flatMap (fun j ↦
        (ROIBudget.featureWeightBody dusActive (dusCostEF A z.unpair.1) j).serialize)) := by
    refine RpnSpliceStream.of_eq
      (RpnSpliceStream.concatVar (hbody.comp hcanonical)
        PolyFueled.right.succ_comp) ?_
    intro z
    simp only [Nat.unpair_pair]
  have hvar : RpnSpliceStream (fun _ : ℕ ↦ (EF.var 0).serialize) :=
    RpnSpliceStream.serialize_var (PolyFueled.const 0)
  have htags : RpnSpliceStream (fun z ↦ List.replicate (z.unpair.2 + 1) 8) :=
    RpnSpliceStream.repeatTag 8 (by norm_num) PolyFueled.right.succ_comp
  refine RpnSpliceStream.of_eq ((hbodies.append hvar).append htags) ?_
  intro z
  rw [dusRemainingEF, ROIBudget.sharedFeatureWeight,
    ROIBudget.sharedWeights_serialize, List.range_eq_range']

/-- Uniform emission of the share coefficient. -/
lemma dusSharesEF_rpnSpliceStream
    {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (emit : DUSThresholdEmission A) :
    RpnSpliceStream (fun z ↦ (dusSharesEF A z.unpair.1 z.unpair.2).serialize) :=
  RpnSpliceStream.serialize_mul (dusRemainingEF_rpnSpliceStream A emit)
    (dusSignal_rpnSpliceStream A emit PolyFueled.left PolyFueled.right)

lemma dusRemainingEF_rank_le {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (k n : ℕ) :
    (dusRemainingEF A k n).rank ≤ n := by
  exact ROIBudget.sharedFeatureWeight_rank_le dusActive (dusCostEF A k)
    (dusCostEF_rank_le A k) n

lemma dusSharesEF_rank_le {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (k n : ℕ) :
    (dusSharesEF A k n).rank ≤ n := by
  simp only [dusSharesEF, EF.rank_mul, max_le_iff]
  exact ⟨dusRemainingEF_rank_le A k n, dusSignal_rank_le A k n⟩

/-- Semantic shares, named separately for the economic accounting. -/
noncomputable def dusShares {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (P : History) (k n : ℕ) : ℝ :=
  (dusSharesEF A k n).denote P

lemma dusRemainingEF_denote {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (P : History) (k n : ℕ) :
    (dusRemainingEF A k n).denote P =
      ROIBudget.weight dusActive (fun i ↦ (dusCostEF A k i).denote P) n := by
  exact ROIBudget.sharedFeatureWeight_denote dusActive (dusCostEF A k)
    (fun i ρ V ↦ dusCostEF_closed A k i ρ V) P n

lemma dusShares_eq {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (P : History) (k n : ℕ) :
    dusShares A P k n =
      ROIBudget.weight dusActive (fun i ↦ (dusCostEF A k i).denote P) n *
        (dusSignal A k n).denote P := by
  rw [dusShares, dusSharesEF, EF.denote_mul, Pi.mul_apply,
    dusRemainingEF_denote]

lemma dusCostEF_denote {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (P : History) (k n : ℕ) :
    (dusCostEF A k n).denote P =
      (dusSignal A k n).denote P * P n (dusSentence B n) := by
  simp [dusCostEF]

lemma dusCostEF_mem
    {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (P : History) (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (k n : ℕ) :
    0 ≤ (dusCostEF A k n).denote P ∧
      (dusCostEF A k n).denote P ≤ 1 := by
  rw [dusCostEF_denote]
  have hs := dusSignal_mem A P k n
  have hp := hP n (dusSentence B n)
  constructor
  · exact mul_nonneg hs.1 hp.1
  · have hprod : 0 ≤
        (1 - (dusSignal A k n).denote P) *
          (1 - P n (dusSentence B n)) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith

lemma dusShares_nonneg
    {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (P : History) (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (k n : ℕ) :
    0 ≤ dusShares A P k n := by
  rw [dusShares_eq]
  exact mul_nonneg
    (ROIBudget.weight_nonneg dusActive _ dusActive_closing
      (fun i ↦ (dusCostEF_mem A P hP k i).1)
      (fun i ↦ (dusCostEF_mem A P hP k i).2) n)
    (dusSignal_mem A P k n).1

/-- Total cash spent by scale `k` through day `n`. -/
noncomputable def dusSpendThrough
    {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (P : History) (k n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), dusShares A P k i * P i (dusSentence B i)

/-- Semimeasure-weighted value of all shares purchased through day `n`. -/
noncomputable def dusMeanPayoutThrough
    {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (P : History) (k n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    M.mass (dusPrefix B i) * dusShares A P k i

/-- A simple depth bound containing every prefix purchased through day `n`. -/
def dusPurchaseDepth {DP : DeductiveProcess}
    (B : BitPrefixSentences DP) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), (dusPrefix B i).length

/-- Aggregate all repeated visits to the same bit prefix. -/
noncomputable def dusPurchaseWeight
    {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (P : History) (k n : ℕ) (σ : List Bool) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    if dusPrefix B i = σ then dusShares A P k i else 0

lemma dusPurchaseWeight_nonneg
    {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (P : History) (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (k n : ℕ) (σ : List Bool) :
    0 ≤ dusPurchaseWeight A P k n σ := by
  exact Finset.sum_nonneg (fun i hi ↦ by
    split
    · exact dusShares_nonneg A P hP k i
    · exact le_rfl)

lemma dusPrefix_length_le_purchaseDepth
    {DP : DeductiveProcess} (B : BitPrefixSentences DP)
    {i n : ℕ} (hi : i ≤ n) :
    (dusPrefix B i).length ≤ dusPurchaseDepth B n := by
  rw [dusPurchaseDepth]
  have himem : i ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  exact Finset.single_le_sum (fun j _ ↦
    Nat.zero_le (dusPrefix B j).length) himem

/-- The event-list mean is contained in the explicit finite binary-tree mean after
aggregating repeated visits by prefix. -/
lemma dusMeanPayoutThrough_le_semimeasureMean
    {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (P : History) (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (k n : ℕ) :
    dusMeanPayoutThrough A P k n ≤
      semimeasureMean M.toContinuousSemimeasure
        (dusPurchaseWeight A P k n) []
        (dusPurchaseDepth B n) := by
  let nodes := bitTreeNodes [] (dusPurchaseDepth B n)
  let events := Finset.range (n + 1)
  let c : List Bool → ℕ → ℝ := fun σ i ↦
    if dusPrefix B i = σ then
      M.mass σ * dusShares A P k i else 0
  have hnode : ∀ σ,
      M.mass σ * dusPurchaseWeight A P k n σ = ∑ i ∈ events, c σ i := by
    intro σ
    rw [dusPurchaseWeight, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : dusPrefix B i = σ
    · subst σ
      simp [c]
    · simp [c, h]
  have htree :
      ((nodes.map (fun σ ↦ M.mass σ * dusPurchaseWeight A P k n σ)).sum) =
        ∑ i ∈ events, (nodes.map (fun σ ↦ c σ i)).sum := by
    calc
      ((nodes.map (fun σ ↦ M.mass σ * dusPurchaseWeight A P k n σ)).sum) =
          (nodes.map (fun σ ↦ ∑ i ∈ events, c σ i)).sum := by
        congr 1
        apply List.map_congr_left
        intro σ hσ
        exact hnode σ
      _ = _ := list_sum_finset_comm nodes events c
  rw [semimeasureMean_eq_bitTree_sum]
  change dusMeanPayoutThrough A P k n ≤
    (nodes.map (fun σ ↦ M.mass σ * dusPurchaseWeight A P k n σ)).sum
  rw [htree, dusMeanPayoutThrough]
  apply Finset.sum_le_sum
  intro i hi
  have hmem : dusPrefix B i ∈ nodes := by
    dsimp only [nodes]
    simpa using append_mem_bitTreeNodes [] (dusPrefix B i)
      (dusPrefix_length_le_purchaseDepth B (n := n) (by
        have := Finset.mem_range.mp hi
        omega))
  apply List.single_le_sum
  · intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨σ, hσ, rfl⟩ := hx
    by_cases h : dusPrefix B i = σ
    · simp only [c, h, if_true]
      exact mul_nonneg (M.nonneg σ) (dusShares_nonneg A P hP k i)
    · simp [c, h]
  · exact List.mem_map.mpr ⟨dusPrefix B i, hmem, by simp [c]⟩

lemma dusMeanPayoutThrough_le_prefixPurchaseMax
    {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (P : History) (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (k n : ℕ) :
    dusMeanPayoutThrough A P k n ≤
      prefixPurchaseMax (dusPurchaseWeight A P k n) []
        (dusPurchaseDepth B n) :=
  (dusMeanPayoutThrough_le_semimeasureMean A P hP k n).trans
    (semimeasureMean_root_le_max M.toContinuousSemimeasure
      (dusPurchaseWeight_nonneg A P hP k n) (dusPurchaseDepth B n))

/-- A world satisfying a longer bit prefix satisfies every shorter initial segment. -/
lemma BitPrefixSentences.holds_prefix_of_append
    {DP : DeductiveProcess} (B : BitPrefixSentences DP)
    (v : PCWorld) (σ rest : List Bool)
    (h : v.Holds (B.prefixSentence (σ ++ rest))) :
    v.Holds (B.prefixSentence σ) := by
  rw [B.holds_prefix] at h ⊢
  intro k
  have hk : (k : ℕ) < (σ ++ rest).length := by simp; omega
  have hfull := h ⟨k, hk⟩
  simpa using hfull

lemma BitPrefixSentences.holds_prefix_of_pathNode
    {DP : DeductiveProcess} (B : BitPrefixSentences DP)
    (v : PCWorld) {bits τ : List Bool}
    (hbits : v.Holds (B.prefixSentence bits))
    (hτ : τ ∈ prefixPathNodes [] bits) :
    v.Holds (B.prefixSentence τ) := by
  obtain ⟨rest, hrest⟩ := prefixPathNode_isPrefix hτ
  have hrest' : bits = τ ++ rest := by simpa using hrest
  rw [hrest'] at hbits
  exact B.holds_prefix_of_append v τ rest hbits

/-- Gross payout of every prefix share purchased through day `n` in one world. -/
noncomputable def dusGrossPayoutThrough
    {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (P : History) (v : PCWorld) (k n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    dusShares A P k i * v.payout (dusSentence B i)

/-- If a world realizes the terminal bits of a path, its gross payout dominates all
aggregated purchases along that path. -/
lemma prefixPathPayout_dusPurchaseWeight_le_gross
    {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (P : History) (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (v : PCWorld) (k n : ℕ) (bits : List Bool)
    (hbits : v.Holds (B.prefixSentence bits)) :
    prefixPathPayout (dusPurchaseWeight A P k n) [] bits ≤
      dusGrossPayoutThrough A P v k n := by
  rw [prefixPathPayout_eq_sum, dusGrossPayoutThrough]
  change
    (((prefixPathNodes [] bits).map (fun σ ↦
      ∑ i ∈ Finset.range (n + 1),
        if dusPrefix B i = σ then dusShares A P k i else 0)).sum) ≤ _
  rw [list_sum_finset_comm]
  apply Finset.sum_le_sum
  intro i hi
  rw [sum_match_eq_if_mem _ (prefixPathNodes_nodup [] bits)]
  by_cases hmem : dusPrefix B i ∈ prefixPathNodes [] bits
  · have hholds : v.Holds (B.prefixSentence (dusPrefix B i)) :=
      B.holds_prefix_of_pathNode v hbits hmem
    have hpayout : v.payout (dusSentence B i) = 1 := by
      rw [PCWorld.payout, if_pos]
      simpa [dusSentence] using hholds
    simp [hmem, hpayout]
  · rw [if_neg hmem]
    exact mul_nonneg (dusShares_nonneg A P hP k i) (by
      rw [PCWorld.payout]
      split <;> norm_num)

/-- The semimeasure mean through any finite day is attained or exceeded as gross payout
in a world consistent with that day's deductive state. -/
lemma exists_consistent_dusGrossPayout_ge_mean
    {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (P : History) (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (k n : ℕ) :
    ∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧
      dusMeanPayoutThrough A P k n ≤ dusGrossPayoutThrough A P v k n := by
  obtain ⟨bits, hlen, hmax⟩ := exists_prefixPathPayout_eq_max
    (dusPurchaseWeight A P k n) [] (dusPurchaseDepth B n)
  obtain ⟨v, hv, hbits⟩ := B.prefix_possible bits n
  refine ⟨v, hv, ?_⟩
  calc
    dusMeanPayoutThrough A P k n ≤
        prefixPurchaseMax (dusPurchaseWeight A P k n) []
          (dusPurchaseDepth B n) :=
      dusMeanPayoutThrough_le_prefixPurchaseMax A P hP k n
    _ = prefixPathPayout (dusPurchaseWeight A P k n) [] bits := hmax.symm
    _ ≤ dusGrossPayoutThrough A P v k n :=
      prefixPathPayout_dusPurchaseWeight_le_gross A P hP v k n bits hbits

/-- Prefix form of the paper's cost-to-mean-payout inequality. -/
lemma dusSpendPrefix_mul_le_meanPrefix
    {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (P : History) (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (k N : ℕ) :
    (2 * ((k + 1 : ℕ) : ℝ)) *
        (∑ i ∈ Finset.range N,
          dusShares A P k i * P i (dusSentence B i)) ≤
      ∑ i ∈ Finset.range N,
        M.mass (dusPrefix B i) * dusShares A P k i := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hshares := dusShares_nonneg A P hP k i
  rcases hshares.eq_or_lt with hzero | hpos
  · rw [← hzero]
    norm_num
  · have hsig : 0 < (dusSignal A k i).denote P := by
      rw [dusShares_eq] at hpos
      have hw : 0 ≤ ROIBudget.weight dusActive
          (fun j ↦ (dusCostEF A k j).denote P) i :=
        ROIBudget.weight_nonneg dusActive _ dusActive_closing
          (fun j ↦ (dusCostEF_mem A P hP k j).1)
          (fun j ↦ (dusCostEF_mem A P hP k j).2) i
      nlinarith
    have hprice := dusSignal_pos_imp_price_lt_mass A P hsig
    have hkpos : 0 < (2 * ((k + 1 : ℕ) : ℝ)) := by positivity
    have hscaled :
        P i (dusSentence B i) * (2 * ((k + 1 : ℕ) : ℝ)) <
          M.mass (dusPrefix B i) :=
      (lt_div_iff₀ hkpos).mp hprice
    nlinarith

/-- Every dollar spent increases semimeasure-weighted payout by at least the paper's
factor `2(k+1)`. -/
lemma dusSpend_mul_le_meanPayout
    {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (P : History) (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (k n : ℕ) :
    (2 * ((k + 1 : ℕ) : ℝ)) * dusSpendThrough A P k n ≤
      dusMeanPayoutThrough A P k n := by
  simpa [dusSpendThrough, dusMeanPayoutThrough] using
    dusSpendPrefix_mul_le_meanPrefix A P hP k (n + 1)

lemma dusSpendThrough_eq
    {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (P : History) (k n : ℕ) :
    dusSpendThrough A P k n =
      ROIBudget.outstanding dusActive
          (fun i ↦ (dusCostEF A k i).denote P)
          (ROIBudget.weight dusActive
            (fun i ↦ (dusCostEF A k i).denote P)) n +
        ROIBudget.weight dusActive
            (fun i ↦ (dusCostEF A k i).denote P) n *
          (dusCostEF A k n).denote P := by
  rw [dusSpendThrough, Finset.sum_range_succ, ROIBudget.outstanding]
  simp only [dusActive, if_true]
  rw [← Fin.sum_univ_eq_sum_range]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    rw [dusShares_eq, dusCostEF_denote]
    ring
  · rw [dusShares_eq, dusCostEF_denote]
    ring

/-- The reified recurrence is exactly one minus all earlier purchase costs. -/
lemma dusRemainingEF_denote_eq_one_sub_spendBefore
    {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (P : History) (k n : ℕ) :
    (dusRemainingEF A k n).denote P =
      1 - ∑ i ∈ Finset.range n,
        dusShares A P k i * P i (dusSentence B i) := by
  rw [dusRemainingEF_denote, ROIBudget.weight_eq, ROIBudget.outstanding]
  simp only [dusActive, if_true]
  rw [← Fin.sum_univ_eq_sum_range]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [dusShares_eq, dusCostEF_denote]
  ring

/-- If mean payout before a purchase is still below `k+1`, more than half of the unit
budget remains. This is the quantitative hinge in the paper's divergence argument. -/
lemma dusRemainingEF_denote_gt_half_of_meanPrefix_lt
    {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (P : History) (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (k n : ℕ)
    (hmean : (∑ i ∈ Finset.range n,
        M.mass (dusPrefix B i) * dusShares A P k i) < (k + 1 : ℕ)) :
    (1 / 2 : ℝ) < (dusRemainingEF A k n).denote P := by
  have hcost := dusSpendPrefix_mul_le_meanPrefix A P hP k n
  have hkpos : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
  rw [dusRemainingEF_denote_eq_one_sub_spendBefore]
  nlinarith

lemma dusShares_gt_half_of_signal_eq_one
    {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (P : History) (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (k n : ℕ)
    (hmean : (∑ i ∈ Finset.range n,
        M.mass (dusPrefix B i) * dusShares A P k i) < (k + 1 : ℕ))
    (hsig : (dusSignal A k n).denote P = 1) :
    (1 / 2 : ℝ) < dusShares A P k n := by
  have hrem := dusRemainingEF_denote_gt_half_of_meanPrefix_lt A P hP k n hmean
  rw [dusShares, dusSharesEF, EF.denote_mul, Pi.mul_apply, hsig, mul_one]
  exact hrem

@[simp] theorem dusPrefix_pair {DP : DeductiveProcess}
    (B : BitPrefixSentences DP) (m i : ℕ) :
    dusPrefix B (Nat.pair m i) = B.enumeration i := by
  rw [dusPrefix, Nat.unpair_pair]

@[simp] theorem dusSentence_pair {DP : DeductiveProcess}
    (B : BitPrefixSentences DP) (m i : ℕ) :
    dusSentence B (Nat.pair m i) = B.prefixSentence (B.enumeration i) := by
  simp [dusSentence]

/-- The one-prefix-per-day schedule revisits every enumeration index cofinally. -/
lemma tendsto_pair_left_atTop (i : ℕ) :
    Tendsto (fun m ↦ Nat.pair m i) atTop atTop := by
  apply tendsto_atTop.2
  intro N
  filter_upwards [eventually_ge_atTop N] with m hm
  exact hm.trans (Nat.left_le_pair m i)

/-- A prefix violating the scale-`k` domination bound eventually fires at full strength
on every sufficiently late revisit. -/
lemma eventually_dusSignal_eq_one_of_low_limit
    {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (P : History) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (k i : ℕ)
    (hlow : limitingBelief P (B.prefixSentence (B.enumeration i)) <
      M.mass (B.enumeration i) / (8 * ((k + 1 : ℕ) : ℝ))) :
    ∀ᶠ m in atTop,
      (dusSignal A k (Nat.pair m i)).denote P = 1 := by
  have hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 :=
    fun n φ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ
  let φ := B.prefixSentence (B.enumeration i)
  have hvisit := tendsto_pair_left_atTop i
  have hconv0 := lic_limitingBelief_tendsto P DP hworld φ
  have hconv : Tendsto (fun m ↦ P (Nat.pair m i) φ) atTop
      (𝓝 (limitingBelief P φ)) := hconv0.comp hvisit
  have happ : Tendsto
      (fun m ↦ ((A.approximation (Nat.pair m i) i : ℚ) : ℝ)) atTop
      (𝓝 (M.mass (B.enumeration i))) := (A.tendsto i).comp hvisit
  have hlim0 : 0 ≤ limitingBelief P φ :=
    ge_of_tendsto hconv0 (Filter.Eventually.of_forall (fun n ↦ (hP n φ).1))
  have hmass : 0 < M.mass (B.enumeration i) := by
    have hlow' : limitingBelief P φ < M.mass (B.enumeration i) /
        (8 * ((k + 1 : ℕ) : ℝ)) := by simpa only [φ] using hlow
    have hkpos : 0 < (8 * ((k + 1 : ℕ) : ℝ)) := by positivity
    by_contra h
    push_neg at h
    have hdivle : M.mass (B.enumeration i) /
        (8 * ((k + 1 : ℕ) : ℝ)) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg h hkpos.le
    linarith
  have hscale : Tendsto
      (fun m ↦ (1 / (4 * ((k + 1 : ℕ) : ℝ))) *
        ((A.approximation (Nat.pair m i) i : ℚ) : ℝ)) atTop
      (𝓝 ((1 / (4 * ((k + 1 : ℕ) : ℝ))) *
        M.mass (B.enumeration i))) :=
    happ.const_mul _
  have hdiff := hconv.sub hscale
  have hlimneg : limitingBelief P φ -
      (1 / (4 * ((k + 1 : ℕ) : ℝ))) * M.mass (B.enumeration i) < 0 := by
    have hkpos : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
    calc
      limitingBelief P φ -
          (1 / (4 * ((k + 1 : ℕ) : ℝ))) * M.mass (B.enumeration i) <
        M.mass (B.enumeration i) / (8 * ((k + 1 : ℕ) : ℝ)) -
          (1 / (4 * ((k + 1 : ℕ) : ℝ))) * M.mass (B.enumeration i) := by
            simpa only [φ] using sub_lt_sub_right hlow _
      _ < 0 := by
        field_simp [ne_of_gt hkpos]
        nlinarith
  have hgap : ∀ᶠ m in atTop,
      P (Nat.pair m i) φ -
        (1 / (4 * ((k + 1 : ℕ) : ℝ))) *
          ((A.approximation (Nat.pair m i) i : ℚ) : ℝ) < 0 :=
    (tendsto_order.1 hdiff).2 _ hlimneg
  have hapos : ∀ᶠ m in atTop,
      0 < ((A.approximation (Nat.pair m i) i : ℚ) : ℝ) :=
    (tendsto_order.1 happ).1 0 hmass
  have hlive : ∀ᶠ m in atTop, k ≤ Nat.pair m i := by
    filter_upwards [eventually_ge_atTop k] with m hm
    exact hm.trans (Nat.left_le_pair m i)
  filter_upwards [hgap, hapos, hlive] with m hgap hapos hlive
  have ha : 0 < A.approximation (Nat.pair m i) i := by exact_mod_cast hapos
  have hprice :
      P (Nat.pair m i) (dusSentence B (Nat.pair m i)) <
        ((dusBase A k (Nat.pair m i) : ℚ) : ℝ) := by
    rw [dusSentence_pair]
    change P (Nat.pair m i) φ < _
    rw [dusBase_cast, Nat.unpair_pair]
    have hkpos : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
    calc
      P (Nat.pair m i) φ <
          (1 / (4 * ((k + 1 : ℕ) : ℝ))) *
            ((A.approximation (Nat.pair m i) i : ℚ) : ℝ) := by linarith
      _ = ((A.approximation (Nat.pair m i) i : ℚ) : ℝ) /
          (4 * ((k + 1 : ℕ) : ℝ)) := by
        field_simp [ne_of_gt hkpos]
  exact dusSignal_eq_one A P hlive (by simpa using ha) hprice

/-- Failed domination at one prefix forces the scale member's mean payout to reach
`k+1`. The proof counts the cofinal full-strength revisits; while the target has not yet
been reached, each buys more than half a share. -/
lemma exists_dusMeanPayout_ge_of_low_limit
    {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (P : History) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (k i : ℕ)
    (hlow : limitingBelief P (B.prefixSentence (B.enumeration i)) <
      M.mass (B.enumeration i) / (8 * ((k + 1 : ℕ) : ℝ))) :
    ∃ n, (k + 1 : ℕ) ≤ dusMeanPayoutThrough A P k n := by
  have hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 :=
    fun n φ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ
  have hevent := eventually_dusSignal_eq_one_of_low_limit A P hworld k i hlow
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hevent
  have hmass : 0 < M.mass (B.enumeration i) := by
    let φ := B.prefixSentence (B.enumeration i)
    have hconv := lic_limitingBelief_tendsto P DP hworld φ
    have hlim0 : 0 ≤ limitingBelief P φ :=
      ge_of_tendsto hconv (Filter.Eventually.of_forall (fun n ↦ (hP n φ).1))
    have hlow' : limitingBelief P φ < M.mass (B.enumeration i) /
        (8 * ((k + 1 : ℕ) : ℝ)) := by simpa only [φ] using hlow
    have hkpos : 0 < (8 * ((k + 1 : ℕ) : ℝ)) := by positivity
    by_contra h
    push_neg at h
    have hdivle : M.mass (B.enumeration i) /
        (8 * ((k + 1 : ℕ) : ℝ)) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg h hkpos.le
    linarith
  by_contra hreach
  push_neg at hreach
  let g : ℕ → ℕ := fun r ↦ Nat.pair (N + r) i
  have hg : StrictMono g := by
    intro a b hab
    exact Nat.pair_lt_pair_left i (by omega)
  have hterm0 : ∀ d, 0 ≤
      M.mass (dusPrefix B d) * dusShares A P k d := fun d ↦
    mul_nonneg (M.nonneg _) (dusShares_nonneg A P hP k d)
  have hmeanBefore : ∀ r,
      (∑ d ∈ Finset.range (g r),
        M.mass (dusPrefix B d) * dusShares A P k d) < (k + 1 : ℕ) := by
    intro r
    have hsub : Finset.range (g r) ⊆ Finset.range (g r + 1) :=
      Finset.range_subset_range.mpr (by omega)
    have hle : (∑ d ∈ Finset.range (g r),
        M.mass (dusPrefix B d) * dusShares A P k d) ≤
        dusMeanPayoutThrough A P k (g r) := by
      rw [dusMeanPayoutThrough]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun d _ _ ↦ hterm0 d)
    exact hle.trans_lt (hreach (g r))
  have hshare : ∀ r, (1 / 2 : ℝ) < dusShares A P k (g r) := by
    intro r
    apply dusShares_gt_half_of_signal_eq_one A P hP k (g r) (hmeanBefore r)
    exact hN (N + r) (by omega)
  obtain ⟨L, hL⟩ := exists_nat_gt
    ((2 * ((k + 1 : ℕ) : ℝ)) / M.mass (B.enumeration i))
  have hlarge : (k + 1 : ℕ) <
      (L + 1 : ℕ) * (M.mass (B.enumeration i) / 2) := by
    rw [div_lt_iff₀ hmass] at hL
    have hinc : (L : ℝ) * M.mass (B.enumeration i) <
        (L + 1 : ℝ) * M.mass (B.enumeration i) :=
      mul_lt_mul_of_pos_right (by norm_num) hmass
    have htwo : 2 * (((k + 1 : ℕ) : ℝ)) <
        (L + 1 : ℝ) * M.mass (B.enumeration i) := hL.trans hinc
    calc
      (((k + 1 : ℕ) : ℝ)) <
          ((L + 1 : ℝ) * M.mass (B.enumeration i)) / 2 :=
        (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2 (by
          simpa [mul_comm] using htwo)
      _ = (((L + 1 : ℕ) : ℝ)) *
          (M.mass (B.enumeration i) / 2) := by
        push_cast
        ring
  have hsub : (Finset.range (L + 1)).image g ⊆ Finset.range (g L + 1) := by
    intro d hd
    simp only [Finset.mem_image, Finset.mem_range] at hd
    obtain ⟨r, hr, rfl⟩ := hd
    exact Finset.mem_range.mpr (by
      have := hg.monotone (Nat.lt_succ_iff.mp hr)
      omega)
  have hsum : (L + 1 : ℕ) * (M.mass (B.enumeration i) / 2) ≤
      dusMeanPayoutThrough A P k (g L) := by
    rw [dusMeanPayoutThrough]
    calc
      ((L + 1 : ℕ) : ℝ) * (M.mass (B.enumeration i) / 2) =
          ∑ _r ∈ Finset.range (L + 1),
            M.mass (B.enumeration i) / 2 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ r ∈ Finset.range (L + 1),
          M.mass (dusPrefix B (g r)) * dusShares A P k (g r) := by
        apply Finset.sum_le_sum
        intro r hr
        rw [show dusPrefix B (g r) = B.enumeration i by simp [g]]
        nlinarith [hshare r]
      _ = ∑ d ∈ (Finset.range (L + 1)).image g,
          M.mass (dusPrefix B d) * dusShares A P k d := by
        symm
        apply Finset.sum_image
        exact hg.injective.injOn
      _ ≤ ∑ d ∈ Finset.range (g L + 1),
          M.mass (dusPrefix B d) * dusShares A P k d :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun d _ _ ↦ hterm0 d)
  linarith [hreach (g L)]

/-- The family member spends at most one dollar in total. -/
lemma dusSpendThrough_le_one
    {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (P : History) (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (k n : ℕ) :
    dusSpendThrough A P k n ≤ 1 := by
  rw [dusSpendThrough_eq]
  exact (ROIBudget.weight_nonneg_and_postAllocation_le dusActive
    (fun i ↦ (dusCostEF A k i).denote P) dusActive_closing
    (fun i ↦ (dusCostEF_mem A P hP k i).1)
    (fun i ↦ (dusCostEF_mem A P hP k i).2) n).2

/-- The paper's unit-budget family member. -/
def dusScaleTrader
    {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (k : ℕ) : Trader where
  strat n := if h : n < k then ⟨[], by simp⟩ else {
    trades := [(dusSharesEF A k n, dusSentence B n)]
    rank_le := by
      intro p hp
      simp only [List.mem_singleton] at hp
      subst p
      exact dusSharesEF_rank_le A k n }

lemma dusScaleTrader_zero_before
    {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    {k n : ℕ} (h : n < k) :
    ((dusScaleTrader A k).strat n).trades = [] := by
  simp [dusScaleTrader, h]

/-- The scale family carries the structured emulation witness: trade boundaries, coefficient
segments and sentence blocks are all polynomially emittable, and members trade nothing before
launch. -/
def dusScaleTrader_polyTradeEmulatable
    {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (emit : DUSThresholdEmission A) :
    PolyTradeEmulatable (dusScaleTrader A) where
  launchGated := fun _ _ h ↦ dusScaleTrader_zero_before A h
  tradeCount w := if w.unpair.2 < w.unpair.1 then 0 else 1
  coefficient z := dusSharesEF A z.unpair.1.unpair.1 z.unpair.1.unpair.2
  sentence z := dusSentence B z.unpair.1.unpair.2
  tradeCount_poly := by
    have htest : PolyFueled _ (fun w ↦ w.unpair.2 + 1 - w.unpair.1) :=
      (subc_polyFueled.comp
        (PolyFueled.right.succ_comp.pair PolyFueled.left)).of_eq
          (fun w ↦ by simp only [Nat.unpair_pair])
    refine ⟨_, (ifzSel_polyFueled.comp
      ((PolyFueled.const (Nat.pair 0 1)).pair htest)).of_eq (fun w ↦ ?_)⟩
    simp only [Nat.unpair_pair, ifzSelFn]
    by_cases h : w.unpair.2 < w.unpair.1
    · rw [if_pos (by omega), if_pos h]
    · rw [if_neg (by omega), if_neg h]
  coefficient_poly :=
    ((dusSharesEF_rpnSpliceStream A emit).comp PolyFueled.left).of_eq
      (fun z ↦ by simp only [Nat.unpair_pair])
  sentence_poly :=
    (B.prefix_codes.comp
      (PolyFueled.right.comp (PolyFueled.right.comp PolyFueled.left))).of_eq
      (fun z ↦ by simp only [dusSentence, dusPrefix])
  trades_eq := by
    intro k n
    by_cases h : n < k
    · simp [dusScaleTrader, h]
    · simp only [dusScaleTrader, dif_neg h, Nat.unpair_pair, if_neg h]
      simp [Nat.unpair_pair]

/-- Uniform token stream for the entire scale family. -/
lemma dusScaleTrader_family_rpnSpliceStream
    {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (emit : DUSThresholdEmission A) :
    RpnSpliceStream (fun z ↦
      serializeTrades ((dusScaleTrader A z.unpair.1).strat z.unpair.2).trades) :=
  (dusScaleTrader_polyTradeEmulatable A emit).polySeg

/-- Every fixed scale member is efficiently computable. -/
lemma dusScaleTrader_ec
    {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (emit : DUSThresholdEmission A) (k : ℕ) :
    EfficientlyComputable (dusScaleTrader A k) := by
  have hinput : PolyFueled _ (fun n ↦ Nat.pair k n) :=
    (PolyFueled.const k).pair PolyFueled.id
  have hseg : RpnSpliceStream (fun n ↦
      serializeTrades ((dusScaleTrader A k).strat n).trades) := by
    refine RpnSpliceStream.of_eq
      ((dusScaleTrader_family_rpnSpliceStream A emit).comp hinput) ?_
    intro n
    rw [Nat.unpair_pair k n]
  exact RpnSpliceStream.ec _ hseg

lemma dusScaleTrader_value
    {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (P : History) (v : Valuation) (k n : ℕ) :
    ((dusScaleTrader A k).strat n).value P v =
      dusShares A P k n * (v (dusSentence B n) - P n (dusSentence B n)) := by
  by_cases h : n < k
  · have hsig : (dusSignal A k n).denote P = 0 := by simp [dusSignal, h]
    have hshares : dusShares A P k n = 0 := by
      rw [dusShares_eq, hsig, mul_zero]
    simp [dusScaleTrader, h, hshares, Strategy.value]
  · simp [dusScaleTrader, h, Strategy.value, dusShares]

lemma dusScaleTrader_netWorth
    {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (P : History) (v : PCWorld) (k n : ℕ) :
    (dusScaleTrader A k).netWorth P v n =
      ∑ i ∈ Finset.range (n + 1),
        dusShares A P k i *
          (v.payout (dusSentence B i) - P i (dusSentence B i)) := by
  simp only [Trader.netWorth, dusScaleTrader_value]

lemma dusScaleTrader_netWorth_eq_gross_sub_spend
    {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (P : History) (v : PCWorld) (k n : ℕ) :
    (dusScaleTrader A k).netWorth P v n =
      dusGrossPayoutThrough A P v k n - dusSpendThrough A P k n := by
  rw [dusScaleTrader_netWorth, dusGrossPayoutThrough, dusSpendThrough,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Every finite semimeasure mean has a same-day plausible net-worth witness, losing at
most the member's one-dollar budget to purchase costs. -/
lemma exists_consistent_dusScaleTrader_netWorth_ge_mean_sub_one
    {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (P : History) (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (k n : ℕ) :
    ∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧
      dusMeanPayoutThrough A P k n - 1 ≤
        (dusScaleTrader A k).netWorth P v n := by
  obtain ⟨v, hv, hgross⟩ := exists_consistent_dusGrossPayout_ge_mean A P hP k n
  refine ⟨v, hv, ?_⟩
  rw [dusScaleTrader_netWorth_eq_gross_sub_spend]
  have hspend := dusSpendThrough_le_one A P hP k n
  linarith

/-- If the domination constant for scale `k` fails at one prefix, that scale member has
a plausible world with net worth at least `k`. -/
lemma exists_consistent_dusScaleTrader_netWorth_ge_of_low_limit
    {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (P : History) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (k i : ℕ)
    (hlow : limitingBelief P (B.prefixSentence (B.enumeration i)) <
      M.mass (B.enumeration i) / (8 * ((k + 1 : ℕ) : ℝ))) :
    ∃ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧
      (k : ℝ) ≤ (dusScaleTrader A k).netWorth P v n := by
  have hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 :=
    fun n φ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ
  obtain ⟨n, hmean⟩ :=
    exists_dusMeanPayout_ge_of_low_limit A P hworld k i hlow
  obtain ⟨v, hv, hnet⟩ :=
    exists_consistent_dusScaleTrader_netWorth_ge_mean_sub_one A P hP k n
  refine ⟨n, v, hv, ?_⟩
  norm_num at hmean ⊢
  linarith

/-- Bounded downside: nonnegative prefix shares can lose only their purchase cost, and
cumulative purchase cost is at most one. -/
lemma dusScaleTrader_netWorth_ge_neg_one
    {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (P : History) (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (v : PCWorld) (k n : ℕ) :
    -(1 : ℝ) ≤ (dusScaleTrader A k).netWorth P v n := by
  rw [dusScaleTrader_netWorth]
  have hpayout : 0 ≤ ∑ i ∈ Finset.range (n + 1),
      dusShares A P k i * v.payout (dusSentence B i) := by
    exact Finset.sum_nonneg (fun i hi ↦ mul_nonneg
      (dusShares_nonneg A P hP k i) (by
        rw [PCWorld.payout]
        split <;> norm_num))
  have hspend := dusSpendThrough_le_one A P hP k n
  rw [dusSpendThrough] at hspend
  calc
    -(1 : ℝ) ≤
        (∑ i ∈ Finset.range (n + 1),
          dusShares A P k i * v.payout (dusSentence B i)) -
        (∑ i ∈ Finset.range (n + 1),
          dusShares A P k i * P i (dusSentence B i)) := by linarith
    _ = ∑ i ∈ Finset.range (n + 1),
          dusShares A P k i *
            (v.payout (dusSentence B i) - P i (dusSentence B i)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-! ### The summable scale diagonal -/

/-- Rung `j` tests a polynomially larger domination scale. -/
def dusDiagonalScale (j : ℕ) : ℕ := (j + 1) ^ 4

/-- Summable rational weight of rung `j`. -/
def dusDiagonalWeight (j : ℕ) : ℚ :=
  1 / ((((j + 1) ^ 2 : ℕ) : ℚ))

lemma dusDiagonalWeight_cast (j : ℕ) :
    ((dusDiagonalWeight j : ℚ) : ℝ) =
      1 / (((j + 1 : ℕ) : ℝ) ^ 2) := by
  rw [dusDiagonalWeight]
  push_cast
  rfl

lemma dusDiagonalScale_gt (j : ℕ) : j < dusDiagonalScale j := by
  have hpow : j + 1 ≤ (j + 1) ^ 4 := Nat.le_pow (by norm_num)
  dsimp [dusDiagonalScale]
  omega

/-- The single DUS trader joins all diagonal rungs visible by the current day. -/
def dusTrader
    {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B) : Trader where
  strat n := Strategy.join ((List.range (n + 1)).map (fun j ↦
    Strategy.scaleBy (.const (dusDiagonalWeight j)) (by simp [EF.rank])
      ((dusScaleTrader A (dusDiagonalScale j)).strat n)))

lemma dusTrader_strat_value
    {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (P : History) (w : Valuation) (n : ℕ) :
    ((dusTrader A).strat n).value P w =
      ∑ j ∈ Finset.range (n + 1),
        (1 / (((j + 1 : ℕ) : ℝ) ^ 2)) *
          ((dusScaleTrader A (dusDiagonalScale j)).strat n).value P w := by
  rw [dusTrader, Strategy.join_value]
  rw [List.map_map, list_range_map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Function.comp_apply]
  rw [Strategy.scaleBy_value, EF.denote_const, dusDiagonalWeight_cast]

lemma dusDiagonalComponent_value_zero_of_day_lt_index
    {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (P : History) (w : Valuation) {n j : ℕ} (hnj : n < j) :
    ((dusScaleTrader A (dusDiagonalScale j)).strat n).value P w = 0 := by
  rw [Strategy.value, dusScaleTrader_zero_before A
    (hnj.trans (dusDiagonalScale_gt j))]
  simp

lemma dusTrader_strat_value_full_prefix
    {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (P : History) (w : Valuation) {n N : ℕ} (hnN : n ≤ N) :
    ((dusTrader A).strat n).value P w =
      ∑ j ∈ Finset.range (N + 1),
        (1 / (((j + 1 : ℕ) : ℝ) ^ 2)) *
          ((dusScaleTrader A (dusDiagonalScale j)).strat n).value P w := by
  rw [dusTrader_strat_value]
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro j hjN hjn
  simp only [Finset.mem_range] at hjN hjn
  rw [dusDiagonalComponent_value_zero_of_day_lt_index A P w (by omega), mul_zero]

/-- Exact finite accounting: the joined trader's wealth is the weighted sum of its
component traders' wealth in the same world. -/
lemma dusTrader_netWorth
    {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (P : History) (v : PCWorld) (N : ℕ) :
    (dusTrader A).netWorth P v N =
      ∑ j ∈ Finset.range (N + 1),
        (1 / (((j + 1 : ℕ) : ℝ) ^ 2)) *
          (dusScaleTrader A (dusDiagonalScale j)).netWorth P v N := by
  rw [Trader.netWorth]
  calc
    ∑ n ∈ Finset.range (N + 1), ((dusTrader A).strat n).value P v.payout =
        ∑ n ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
          (1 / (((j + 1 : ℕ) : ℝ) ^ 2)) *
            ((dusScaleTrader A (dusDiagonalScale j)).strat n).value P v.payout := by
      apply Finset.sum_congr rfl
      intro n hn
      exact dusTrader_strat_value_full_prefix A P v.payout
        (by simpa using hn)
    _ = ∑ j ∈ Finset.range (N + 1), ∑ n ∈ Finset.range (N + 1),
          (1 / (((j + 1 : ℕ) : ℝ) ^ 2)) *
            ((dusScaleTrader A (dusDiagonalScale j)).strat n).value P v.payout := by
      rw [Finset.sum_comm]
    _ = ∑ j ∈ Finset.range (N + 1),
          (1 / (((j + 1 : ℕ) : ℝ) ^ 2)) *
            (dusScaleTrader A (dusDiagonalScale j)).netWorth P v N := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Trader.netWorth, Finset.mul_sum]

/-- The inverse-square weights keep the diagonal's downside uniformly bounded, by two. -/
lemma dusTrader_netWorth_ge_neg_two
    {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (P : History) (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (v : PCWorld) (N : ℕ) :
    -(2 : ℝ) ≤ (dusTrader A).netWorth P v N := by
  rw [dusTrader_netWorth]
  have hterm : ∀ j ∈ Finset.range (N + 1),
      -(1 / (((j + 1 : ℕ) : ℝ) ^ 2)) ≤
        (1 / (((j + 1 : ℕ) : ℝ) ^ 2)) *
          (dusScaleTrader A (dusDiagonalScale j)).netWorth P v N := by
    intro j hj
    have hscale := dusScaleTrader_netWorth_ge_neg_one A P hP v
      (dusDiagonalScale j) N
    have hw : 0 ≤ (1 / (((j + 1 : ℕ) : ℝ) ^ 2)) := by positivity
    have := mul_le_mul_of_nonneg_left hscale hw
    simpa using this
  calc
    -(2 : ℝ) ≤ -∑ j ∈ Finset.range (N + 1),
        (1 : ℝ) / (((j + 1 : ℕ) : ℝ) ^ 2) := by
      have := sum_inv_sq_le_two (N + 1)
      linarith
    _ = ∑ j ∈ Finset.range (N + 1),
        -(1 / (((j + 1 : ℕ) : ℝ) ^ 2)) := by
      rw [Finset.sum_neg_distrib]
    _ ≤ _ := Finset.sum_le_sum hterm

lemma dusScaleTrader_netWorth_zero_before
    {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (P : History) (v : PCWorld) {k n : ℕ} (hnk : n < k) :
    (dusScaleTrader A k).netWorth P v n = 0 := by
  rw [Trader.netWorth]
  apply Finset.sum_eq_zero
  intro i hi
  rw [Strategy.value, dusScaleTrader_zero_before A (by
    simp only [Finset.mem_range] at hi
    omega)]
  simp

/-- The high-wealth witness produced by a failed positive scale occurs after that scale
has launched. -/
lemma exists_live_consistent_dusScaleTrader_netWorth_ge_of_low_limit
    {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (P : History) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    {k i : ℕ} (hk : 0 < k)
    (hlow : limitingBelief P (B.prefixSentence (B.enumeration i)) <
      M.mass (B.enumeration i) / (8 * ((k + 1 : ℕ) : ℝ))) :
    ∃ n, ∃ v : PCWorld, k ≤ n ∧ v.ConsistentWith (DP.D n) ∧
      (k : ℝ) ≤ (dusScaleTrader A k).netWorth P v n := by
  have hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 :=
    fun n φ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ
  obtain ⟨n, v, hv, hnet⟩ :=
    exists_consistent_dusScaleTrader_netWorth_ge_of_low_limit
      A P hworld k i hlow
  have hkn : k ≤ n := by
    by_contra h
    have hzero := dusScaleTrader_netWorth_zero_before A P v
      (k := k) (n := n) (by omega)
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    linarith
  exact ⟨n, v, hkn, hv, hnet⟩

/-- Failure of every polynomially spaced domination scale makes the concrete diagonal
trader exploit: rung `j` contributes at least `(j+1)²`, while all rungs together can
lose at most two dollars. -/
lemma dusTrader_exploits_of_failed_scales
    {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (P : History) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hfail : ∀ j, ∃ i,
      limitingBelief P (B.prefixSentence (B.enumeration i)) <
        M.mass (B.enumeration i) /
          (8 * ((dusDiagonalScale j + 1 : ℕ) : ℝ))) :
    (dusTrader A).Exploits P DP := by
  have hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 :=
    fun n φ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ
  refine exploits_of_bddBelow_of_unbounded _ _ _ 2 ?_ ?_
  · rintro x ⟨N, v, hv, rfl⟩
    exact dusTrader_netWorth_ge_neg_two A P hP v N
  · intro C
    obtain ⟨j, hj⟩ := exists_nat_gt (max C 2)
    obtain ⟨i, hlow⟩ := hfail j
    have hscalePos : 0 < dusDiagonalScale j := by
      exact (Nat.zero_le j).trans_lt (dusDiagonalScale_gt j)
    obtain ⟨N, v, hscaleN, hv, htargetNet⟩ :=
      exists_live_consistent_dusScaleTrader_netWorth_ge_of_low_limit
        A P hworld hscalePos hlow
    refine ⟨(dusTrader A).netWorth P v N, ⟨N, v, hv, rfl⟩, ?_⟩
    let weight : ℕ → ℝ := fun r ↦
      1 / (((r + 1 : ℕ) : ℝ) ^ 2)
    let worth : ℕ → ℝ := fun r ↦
      (dusScaleTrader A (dusDiagonalScale r)).netWorth P v N
    have hadjustNonneg : ∀ r ∈ Finset.range (N + 1),
        0 ≤ weight r * worth r + weight r := by
      intro r hr
      have hfloor := dusScaleTrader_netWorth_ge_neg_one A P hP v
        (dusDiagonalScale r) N
      have hw : 0 ≤ weight r := by dsimp [weight]; positivity
      have hscaled := mul_le_mul_of_nonneg_left hfloor hw
      nlinarith
    have hjmem : j ∈ Finset.range (N + 1) := by
      apply Finset.mem_range.mpr
      have := dusDiagonalScale_gt j
      omega
    have hweightScale :
        weight j * (dusDiagonalScale j : ℝ) =
          (((j + 1 : ℕ) : ℝ) ^ 2) := by
      have hjpos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
      dsimp [weight, dusDiagonalScale]
      push_cast
      field_simp [ne_of_gt hjpos]
    have hscaledTarget :
        weight j * (dusDiagonalScale j : ℝ) ≤ weight j * worth j := by
      apply mul_le_mul_of_nonneg_left
      · simpa [worth] using htargetNet
      · dsimp [weight]
        positivity
    have htargetAdjusted :
        (((j + 1 : ℕ) : ℝ) ^ 2) ≤ weight j * worth j + weight j := by
      rw [← hweightScale]
      have hw : 0 ≤ weight j := by dsimp [weight]; positivity
      linarith
    have hsingle : weight j * worth j + weight j ≤
        ∑ r ∈ Finset.range (N + 1), (weight r * worth r + weight r) :=
      Finset.single_le_sum hadjustNonneg hjmem
    have hadjust : (((j + 1 : ℕ) : ℝ) ^ 2) ≤
        ∑ r ∈ Finset.range (N + 1), (weight r * worth r + weight r) :=
      htargetAdjusted.trans hsingle
    have hsumWeight :
        ∑ r ∈ Finset.range (N + 1), weight r ≤ 2 := by
      simpa [weight] using sum_inv_sq_le_two (N + 1)
    have hadjustEq :
        (∑ r ∈ Finset.range (N + 1), (weight r * worth r + weight r)) =
          (dusTrader A).netWorth P v N +
            ∑ r ∈ Finset.range (N + 1), weight r := by
      rw [Finset.sum_add_distrib, dusTrader_netWorth]
    have hjC : C < (j : ℝ) := lt_of_le_of_lt (le_max_left C 2) hj
    have hj2 : (2 : ℝ) < j := lt_of_le_of_lt (le_max_right C 2) hj
    rw [hadjustEq] at hadjust
    push_cast at hadjust ⊢
    nlinarith [sq_nonneg ((j : ℝ) + 1)]

/-! ### Uniform token emission for the diagonal -/

lemma dusDiagonalSquare_polyFueled
    {cj : Nat.Partrec.Code} {jf : ℕ → ℕ} (hj : PolyFueled cj jf) :
    ∃ c, PolyFueled c (fun x ↦ (jf x + 1) ^ 2) := by
  obtain ⟨cmul, hmul⟩ := mul_polyFueled
  have hj1 := hj.succ_comp
  exact ⟨_, (hmul.comp (hj1.pair hj1)).of_eq (fun x ↦ by
    simp only [Nat.unpair_pair]
    ring)⟩

lemma dusDiagonalScale_polyFueled
    {cj : Nat.Partrec.Code} {jf : ℕ → ℕ} (hj : PolyFueled cj jf) :
    ∃ c, PolyFueled c (fun x ↦ dusDiagonalScale (jf x)) := by
  obtain ⟨csq, hsq⟩ := dusDiagonalSquare_polyFueled hj
  obtain ⟨cmul, hmul⟩ := mul_polyFueled
  exact ⟨_, (hmul.comp (hsq.pair hsq)).of_eq (fun x ↦ by
    simp only [Nat.unpair_pair]
    simp [dusDiagonalScale]
    ring)⟩

lemma encode_dusDiagonalWeight (j : ℕ) :
    Encodable.encode (dusDiagonalWeight j) = Nat.pair 2 ((j + 1) ^ 2) := by
  have hpos : 0 < (j + 1) ^ 2 := by positivity
  have heq : dusDiagonalWeight j = ((((j + 1) ^ 2 : ℕ) : ℚ))⁻¹ := by
    rw [dusDiagonalWeight, one_div]
  rw [heq, encode_rat_inv_natCast hpos]

lemma dusDiagonalWeight_polyRatCodes
    {cj : Nat.Partrec.Code} {jf : ℕ → ℕ} (hj : PolyFueled cj jf) :
    PolyRatCodes (fun x ↦ dusDiagonalWeight (jf x)) := by
  obtain ⟨csq, hsq⟩ := dusDiagonalSquare_polyFueled hj
  refine ⟨_, ((PolyFueled.const 2).pair hsq).of_eq (fun x ↦ ?_)⟩
  rw [encode_dusDiagonalWeight]

/-- Symbol-metered emitter for the inverse-square diagonal trader. -/
lemma dusTrader_rpnSpliceStream
    {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (emit : DUSThresholdEmission A) :
    RpnSpliceStream (fun n ↦ serializeTrades ((dusTrader A).strat n).trades) := by
  have hday : PolyFueled _ (fun q ↦ q.unpair.1) := PolyFueled.left
  have hrung : PolyFueled _ (fun q ↦ q.unpair.2) := PolyFueled.right
  obtain ⟨cscale, hscale⟩ := dusDiagonalScale_polyFueled hrung
  have hcanonical : PolyFueled _ (fun q ↦
      Nat.pair (dusDiagonalScale q.unpair.2) q.unpair.1) :=
    hscale.pair hday
  have hshares : RpnSpliceStream (fun q ↦
      (dusSharesEF A (dusDiagonalScale q.unpair.2) q.unpair.1).serialize) := by
    refine RpnSpliceStream.of_eq
      ((dusSharesEF_rpnSpliceStream A emit).comp hcanonical) ?_
    intro q
    simp only [Nat.unpair_pair]
  have hweight : RpnSpliceStream (fun q ↦
      (EF.const (dusDiagonalWeight q.unpair.2)).serialize) :=
    RpnSpliceStream.serialize_const_comp
      (dusDiagonalWeight_polyRatCodes hrung)
  have hscaled : RpnSpliceStream (fun q ↦
      (EF.mul (EF.const (dusDiagonalWeight q.unpair.2))
        (dusSharesEF A (dusDiagonalScale q.unpair.2) q.unpair.1)).serialize) :=
    RpnSpliceStream.serialize_mul hweight hshares
  have hidx : PolyFueled _ (fun q ↦ q.unpair.1.unpair.2) :=
    PolyFueled.right.comp hday
  have hframe : RpnSpliceStream (fun q ↦
      [6, Encodable.encode (dusSentence B q.unpair.1)]) :=
    (RpnSpliceStream.tradeSlot B.prefix_codes hidx).of_eq
      (fun q ↦ by simp [dusSentence, dusPrefix])
  have hlive : RpnSpliceStream (fun q ↦ serializeTrades [
      (EF.mul (EF.const (dusDiagonalWeight q.unpair.2))
        (dusSharesEF A (dusDiagonalScale q.unpair.2) q.unpair.1),
      dusSentence B q.unpair.1)]) := by
    refine RpnSpliceStream.of_eq (hscaled.append hframe) ?_
    intro q
    simp [serializeTrades]
  have hzero : RpnSpliceStream (fun _ : ℕ ↦ serializeTrades []) :=
    RpnSpliceStream.ofTransparent
      (PolySegStream.ofTokenStream PolyTokenStream.trades_nil)
      (fun _ ↦ by simpa [serializeTrades] using UnRpnTransparent.nil)
  have htest : PolyFueled _ (fun q ↦
      q.unpair.1 + 1 - dusDiagonalScale q.unpair.2) :=
    (subc_polyFueled.comp (hday.succ_comp.pair hscale)).of_eq
      (fun q ↦ by simp only [Nat.unpair_pair])
  have hone : RpnSpliceStream (fun q ↦
      serializeTrades
        ((Strategy.scaleBy (EF.const (dusDiagonalWeight q.unpair.2))
          (by simp [EF.rank])
          ((dusScaleTrader A (dusDiagonalScale q.unpair.2)).strat q.unpair.1)).trades)) := by
    refine RpnSpliceStream.of_eq (RpnSpliceStream.ifZero hzero hlive htest) ?_
    intro q
    by_cases hpad : q.unpair.1 < dusDiagonalScale q.unpair.2
    · have ht : q.unpair.1 + 1 - dusDiagonalScale q.unpair.2 = 0 := by omega
      simp [ht, Strategy.scaleBy, dusScaleTrader, hpad]
    · have ht : q.unpair.1 + 1 - dusDiagonalScale q.unpair.2 ≠ 0 := by omega
      simp [ht, Strategy.scaleBy, dusScaleTrader, hpad]
  have hall := RpnSpliceStream.concatVar hone PolyFueled.id.succ_comp
  refine RpnSpliceStream.of_eq hall ?_
  intro n
  rw [dusTrader]
  simp only [Strategy.join]
  rw [serializeTrades_flatMap, List.flatMap_map]
  apply List.flatMap_congr
  intro j hj
  have hdayeq : (Nat.pair n j).unpair.1 = n := by
    rw [Nat.unpair_pair]
  rw [hdayeq]
  simp

/-- The diagonal trader is efficiently computable. -/
lemma dusTrader_ec
    {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (emit : DUSThresholdEmission A) :
    EfficientlyComputable (dusTrader A) :=
  RpnSpliceStream.ec _ (dusTrader_rpnSpliceStream A emit)

/-! ### Paper-facing domination theorem -/

/-- **Domination of the Universal Semimeasure** (`thm:dus`). One positive constant
simultaneously lower-bounds the limiting probability of every finite bit prefix by its
continuous-semimeasure mass.
Paper node: `thm:dus` -/
theorem lic_domination_universalSemimeasure
    {DP : DeductiveProcess}
    {M : LowerSemicomputableContinuousSemimeasure}
    {B : BitPrefixSentences DP} (A : DUSApproximationPresentation M B)
    (emit : DUSThresholdEmission A)
    (P : History) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ,
      C * M.mass σ ≤ limitingBelief P (B.prefixSentence σ) := by
  have hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 :=
    fun n φ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ
  by_cases hscale : ∃ j : ℕ, ∀ σ,
      M.mass σ / (8 * ((dusDiagonalScale j + 1 : ℕ) : ℝ)) ≤
        limitingBelief P (B.prefixSentence σ)
  · obtain ⟨j, hall⟩ := hscale
    have hden : (0 : ℝ) < 8 * ((dusDiagonalScale j + 1 : ℕ) : ℝ) := by
      positivity
    refine ⟨1 / (8 * ((dusDiagonalScale j + 1 : ℕ) : ℝ)),
      by positivity, fun σ ↦ ?_⟩
    convert hall σ using 1
    ring
  · exfalso
    have hfail : ∀ j, ∃ i,
        limitingBelief P (B.prefixSentence (B.enumeration i)) <
          M.mass (B.enumeration i) /
            (8 * ((dusDiagonalScale j + 1 : ℕ) : ℝ)) := by
      intro j
      have hbad : ∃ σ,
          limitingBelief P (B.prefixSentence σ) <
            M.mass σ /
              (8 * ((dusDiagonalScale j + 1 : ℕ) : ℝ)) := by
        by_contra hnone
        apply hscale
        refine ⟨j, fun σ ↦ ?_⟩
        exact le_of_not_gt (fun hlt ↦ hnone ⟨σ, hlt⟩)
      obtain ⟨σ, hlow⟩ := hbad
      obtain ⟨i, hi⟩ := B.enumeration_covers σ
      refine ⟨i, ?_⟩
      simpa only [hi] using hlow
    exact IsLogicalInductor.noExploit (P := P) (DP := DP)
      (dusTrader A) (dusTrader_ec A emit)
      (dusTrader_exploits_of_failed_scales A P hworld hfail)


#print axioms semimeasureMean_root_le_max
#print axioms dusSpendThrough_le_one
#print axioms dusScaleTrader_netWorth_ge_neg_one
#print axioms dusScaleTrader_ec
#print axioms exists_dusMeanPayout_ge_of_low_limit
#print axioms exists_consistent_dusGrossPayout_ge_mean
#print axioms dusTrader_netWorth_ge_neg_two
#print axioms dusTrader_exploits_of_failed_scales
#print axioms dusTrader_ec
#print axioms lic_domination_universalSemimeasure

/-! ## Strict Domination of the Universal Semimeasure (`thm:strict`)

Only the market half is proved here.  It is factored over
`StrictSeparatorPresentation`, an interface holding the computability-theory data, and
that interface mentions no market price and no strict-domination conclusion — it cannot
smuggle the theorem in as a hypothesis.  The interface is discharged by
`strictSeparatorPresentationOfKleene` in `Construction/Witnesses/StrictSeparators.lean`,
which builds it from Kleene's recursively inseparable pair.

The separator data is the paper's (`app:strict`): a **c.e. constraint theory** — one
single-bit constraint for each code enumerated into one half of a recursively inseparable
pair — together with, at each stage, the finite class of bit strings still consistent with
the constraints decided so far.  Undecided bits stay free, so the constraints never
assemble into a single nested prefix family, and no such family would do: by
`no_ce_null_prefix_family` (same construction file), a nested prefix family with a
computable enumeration always keeps positive universal-semimeasure mass. -/

open Filter Topology

/-- Interface to the recursively-inseparable separator class used in the paper's proof of
Strict Domination.  `mass_class_tendsto_zero` is the computability-theory fact it exists
to carry — for disjoint c.e. sets with no computable separator, the universal semimeasure
gives the stage-`n` separator class vanishing total mass.  The remaining fields expose the
constraint theory, its enumeration, and the finite class data.
Paper node: `thm:strict` -/
structure StrictSeparatorPresentation
    (M : UniversalContinuousSemimeasure) {DP : DeductiveProcess}
    (B : BitPrefixSentences DP) where
  /-- Stage-`n` conjunction of the separator constraints decided by stage `n`. -/
  constraint : ℕ → Sentence
  /-- The constraint theory is computably enumerable, in the paper's preprocessed form. -/
  repetition : EfficientRepeatedEnumeration constraint
  /-- Every finite deductive stage admits a world satisfying the whole constraint theory. -/
  jointly_possible : ∀ n, ∃ v : PCWorld,
    v.ConsistentWith (DP.D n) ∧ ∀ i, v.Holds (constraint i)
  /-- The finite class of bit strings consistent with the stage-`n` constraints. -/
  consistentAt : ℕ → List (List Bool)
  /-- Every world satisfying the stage-`n` constraint realizes a member of that class. -/
  class_covers : ∀ n (v : PCWorld), v.Holds (constraint n) →
    ∃ σ ∈ consistentAt n, v.Holds (B.prefixSentence σ)
  /-- The universal semimeasure gives the separator classes vanishing total mass. -/
  mass_class_tendsto_zero :
    Tendsto (fun n ↦ ((consistentAt n).map M.mass).sum) atTop (𝓝 0)

/-- General market half of the strict-domination proof.  Uniform Non-Dogmatism puts a fixed
positive floor under every stage of the constraint theory; limit coherence spreads that
floor over the stage's finite consistent class; and vanishing class mass then forces some
member of the class to beat any fixed multiple of its semimeasure mass. -/
lemma strict_domination_of_null_separator_class
    {DP : DeductiveProcess}
    {M : UniversalContinuousSemimeasure}
    {B : BitPrefixSentences DP}
    (P : History) [IsLogicalInductor P DP]
    (S : StrictSeparatorPresentation M B) :
    ∀ C : ℝ, 0 < C → ∃ σ : List Bool,
      C * M.mass σ < limitingBelief P (B.prefixSentence σ) := by
  have hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n) := by
    intro n
    obtain ⟨v, hv, -⟩ := S.jointly_possible n
    exact ⟨v, hv⟩
  have hgaif := lic_limitingBelief_gaifman P DP hworld
  obtain ⟨ε, hε, hlower⟩ := lic_uniform_nonDogmatism P DP
    S.constraint S.repetition S.jointly_possible
  intro C hC
  by_contra hno
  push_neg at hno
  have hscaled : Tendsto (fun n ↦ C * ((S.consistentAt n).map M.mass).sum) atTop (𝓝 0) := by
    simpa using S.mass_class_tendsto_zero.const_mul C
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 ((tendsto_order.1 hscaled).2 ε hε)
  have hsmall : C * ((S.consistentAt N).map M.mass).sum < ε := hN N le_rfl
  -- Limit coherence: the stage-`N` constraint is covered by its consistent class.
  have hcover : limitingBelief P (S.constraint N) ≤
      (((S.consistentAt N).map (fun σ ↦ B.prefixSentence σ)).map (limitingBelief P)).sum :=
    GaifmanCoherent.le_sum_of_covers hgaif (by
      intro v hv
      obtain ⟨σ, hσ, hvσ⟩ := S.class_covers N v hv
      exact ⟨B.prefixSentence σ, List.mem_map_of_mem hσ, hvσ⟩)
  rw [List.map_map] at hcover
  -- Each member is dominated by its scaled semimeasure mass, by assumption.
  have hterm : ((S.consistentAt N).map
      (limitingBelief P ∘ fun σ ↦ B.prefixSentence σ)).sum ≤
      ((S.consistentAt N).map (fun σ ↦ C * M.mass σ)).sum :=
    List.sum_le_sum (fun σ _ ↦ hno σ)
  have hscale : ((S.consistentAt N).map (fun σ ↦ C * M.mass σ)).sum =
      C * ((S.consistentAt N).map M.mass).sum := by
    induction S.consistentAt N with
    | nil => simp
    | cons σ l ih => simp [ih, mul_add]
  have hfloor : ε ≤ limitingBelief P (S.constraint N) := hlower N
  rw [hscale] at hterm
  linarith

/-- **Strict Domination of the Universal Semimeasure** (`thm:strict`). The universal
continuous semimeasure does not dominate the logical inductor's limiting prefix beliefs.
Paper node: `thm:strict` -/
theorem lic_strict_domination_universalSemimeasure
    {DP : DeductiveProcess}
    {M : UniversalContinuousSemimeasure}
    {B : BitPrefixSentences DP}
    (P : History) [IsLogicalInductor P DP]
    (S : StrictSeparatorPresentation M B) :
    ∀ C : ℝ, 0 < C → ∃ σ : List Bool,
      limitingBelief P (B.prefixSentence σ) > C * M.mass σ := by
  intro C hC
  obtain ⟨σ, hσ⟩ := strict_domination_of_null_separator_class P S C hC
  exact ⟨σ, hσ⟩

#print axioms strict_domination_of_null_separator_class
#print axioms lic_strict_domination_universalSemimeasure

end LogicalInduction
