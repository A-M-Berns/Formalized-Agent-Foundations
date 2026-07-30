import LogicalInduction.Framework.Affine

namespace LogicalInduction
namespace AffineCombination

open Filter Topology

/-- Zero-coefficient padding entry. -/
def padEntry (pad : Sentence) : EF × Sentence := (EF.const 0, pad)

private lemma eq_map_range_getD {α : Type*} (t : List α) (d : α) :
    t = (List.range t.length).map (fun o => t.getD o d) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [List.getElem_map, List.getElem_range, List.getD_eq_getElem _ _ h1]

private lemma padded_map_sum {α : Type*} [AddCommMonoid α]
    {β : Type*} (t : List β) (d : β) (W : ℕ) (hW : t.length ≤ W)
    (F : β → α) (hF : F d = 0) :
    ((List.range W).map (fun o => F (t.getD o d))).sum = (t.map F).sum := by
  obtain ⟨r, hr⟩ : ∃ r, W = t.length + r := ⟨W - t.length, by omega⟩
  subst hr
  rw [List.range_add]
  simp only [List.map_append, List.sum_append, List.map_map, Function.comp_def]
  have h1 : ((List.range t.length).map (fun o => F (t.getD o d))).sum = (t.map F).sum := by
    conv_rhs => rw [eq_map_range_getD t d]
    simp [Function.comp_def]
  have h2 : ((List.range r).map (fun o => F (t.getD (t.length + o) d))).sum = 0 := by
    have hz : ∀ o, F (t.getD (t.length + o) d) = 0 := by
      intro o
      rw [List.getD_eq_default _ _ (by omega), hF]
    rw [List.map_congr_left (fun o _ => hz o)]
    simp
  rw [h1, h2, add_zero]

private lemma sum_map_flatMap {α β γ : Type*} [AddCommMonoid γ]
    (L : List α) (g : α → List β) (F : β → γ) :
    ((L.flatMap g).map F).sum = (L.map (fun x => ((g x).map F).sum)).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [List.flatMap_cons, ih]

private lemma sum_map_add' {α γ : Type*} [AddCommMonoid γ] (L : List α) (u v : α → γ) :
    (L.map fun x => u x + v x).sum = (L.map u).sum + (L.map v).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, ih]; abel

/-- Rectangular flattening: a block/offset double range is the plain range of the product,
read through division and remainder by the block width. -/
private lemma flatMap_range_map_range {α : Type*} (a b : ℕ) (hb : 0 < b) (G : ℕ → ℕ → α) :
    ((List.range a).flatMap fun k => (List.range b).map fun o => G k o)
      = (List.range (a * b)).map fun j => G (j / b) (j % b) := by
  induction a with
  | zero => simp
  | succ a ih =>
      rw [List.range_succ, List.flatMap_append, ih]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [show (a + 1) * b = a * b + b by ring, List.range_add, List.map_append]
      congr 1
      · rw [List.map_map]
        refine List.map_congr_left fun o ho => ?_
        simp only [Function.comp_apply, List.mem_range] at ho ⊢
        have hd : (a * b + o) / b = a := by
          rw [Nat.mul_comm, Nat.mul_add_div hb, Nat.div_eq_of_lt ho, Nat.add_zero]
        have hm : (a * b + o) % b = o := by
          rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt ho]
        rw [hd, hm]

/-- `blockSum Bs coeff cnt width pad m = Σ_{k < cnt m} coeff⟨m,k⟩ · Bs⟨m,k⟩`, each block's
term list padded with zero coefficients out to the uniform width `width m`. -/
noncomputable def blockSum (Bs : ℕ → AffineCombination) (coeff : ℕ → EF)
    (cnt width : ℕ → ℕ) (pad : Sentence) (m : ℕ) : AffineCombination where
  const := (List.range (cnt m)).foldr
    (fun k acc => .add (.mul (coeff (Nat.pair m k)) (Bs (Nat.pair m k)).const) acc)
    (.const 0)
  terms := (List.range (cnt m)).flatMap fun k =>
    (List.range (width m)).map fun o =>
      (EF.mul (coeff (Nat.pair m k))
          ((Bs (Nat.pair m k)).terms.getD o (padEntry pad)).1,
        ((Bs (Nat.pair m k)).terms.getD o (padEntry pad)).2)

private lemma foldr_addMul_denote (L : List ℕ) (c v : ℕ → EF) (V : History) :
    ((L.foldr (fun k acc => EF.add (EF.mul (c k) (v k)) acc) (EF.const 0)).denote V)
      = (L.map fun k => (c k).denote V * (v k).denote V).sum := by
  induction L with
  | nil => simp
  | cons k L ih => simp [ih]

lemma blockSum_value (Bs : ℕ → AffineCombination) (coeff : ℕ → EF)
    (cnt width : ℕ → ℕ) (pad : Sentence) (m : ℕ) (V : History) (w : Valuation)
    (hw : ∀ k < cnt m, (Bs (Nat.pair m k)).terms.length ≤ width m) :
    (blockSum Bs coeff cnt width pad m).value V w =
      ((List.range (cnt m)).map fun k =>
        (coeff (Nat.pair m k)).denote V * (Bs (Nat.pair m k)).value V w).sum := by
  rw [value, blockSum]
  rw [foldr_addMul_denote, sum_map_flatMap, ← sum_map_add']
  refine congrArg List.sum (List.map_congr_left fun k hk => ?_)
  simp only [List.mem_range] at hk
  have hblock := padded_map_sum ((Bs (Nat.pair m k)).terms) (padEntry pad) (width m)
    (hw k hk) (fun p : EF × Sentence =>
      (EF.mul (coeff (Nat.pair m k)) p.1).denote V * w p.2) (by simp [padEntry])
  rw [List.map_map]
  simp only [Function.comp_def]
  rw [hblock, value]
  simp only [EF.denote_mul, Pi.mul_apply]
  have hpull : ((Bs (Nat.pair m k)).terms.map fun p =>
      (coeff (Nat.pair m k)).denote V * p.1.denote V * w p.2).sum
      = (coeff (Nat.pair m k)).denote V *
        ((Bs (Nat.pair m k)).terms.map fun p => p.1.denote V * w p.2).sum := by
    induction (Bs (Nat.pair m k)).terms with
    | nil => simp
    | cons p ps ih => simp only [List.map_cons, List.sum_cons, ih]; ring
  rw [hpull]
  ring

lemma blockSum_price (Bs : ℕ → AffineCombination) (coeff : ℕ → EF)
    (cnt width : ℕ → ℕ) (pad : Sentence) (m : ℕ) (V : History) (day : ℕ)
    (hw : ∀ k < cnt m, (Bs (Nat.pair m k)).terms.length ≤ width m) :
    (blockSum Bs coeff cnt width pad m).price V day =
      ((List.range (cnt m)).map fun k =>
        (coeff (Nat.pair m k)).denote V * (Bs (Nat.pair m k)).price V day).sum := by
  simpa only [price] using blockSum_value Bs coeff cnt width pad m V (V day) hw

lemma blockSum_magnitude (Bs : ℕ → AffineCombination) (coeff : ℕ → EF)
    (cnt width : ℕ → ℕ) (pad : Sentence) (m : ℕ) (V : History)
    (hw : ∀ k < cnt m, (Bs (Nat.pair m k)).terms.length ≤ width m) :
    (blockSum Bs coeff cnt width pad m).magnitude V =
      ((List.range (cnt m)).map fun k =>
        |(coeff (Nat.pair m k)).denote V| * (Bs (Nat.pair m k)).magnitude V).sum := by
  rw [magnitude, blockSum]
  rw [sum_map_flatMap]
  refine congrArg List.sum (List.map_congr_left fun k hk => ?_)
  simp only [List.mem_range] at hk
  have hblock := padded_map_sum ((Bs (Nat.pair m k)).terms) (padEntry pad) (width m)
    (hw k hk) (fun p : EF × Sentence =>
      |(EF.mul (coeff (Nat.pair m k)) p.1).denote V|) (by simp [padEntry])
  rw [List.map_map]
  simp only [Function.comp_def]
  rw [hblock, magnitude]
  simp only [EF.denote_mul, Pi.mul_apply, abs_mul]
  induction (Bs (Nat.pair m k)).terms with
  | nil => simp
  | cons p ps ih => simp only [List.map_cons, List.sum_cons, ih]; ring

lemma PolySequence.terms_length {As : ℕ → AffineCombination} (h : PolySequence As)
    (n : ℕ) : (As n).terms.length = h.termCount n := by
  rw [h.terms_eq]; simp

private lemma getD_map_range {α : Type*} (n : ℕ) (g : ℕ → α) (o : ℕ) (d : α) :
    ((List.range n).map g).getD o d = if o < n then g o else d := by
  by_cases ho : o < n
  · rw [if_pos ho, List.getD_eq_getElem _ _ (by simpa using ho)]
    simp
  · rw [if_neg ho, List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt ho)]

/-- Serialization of a `Σ uₖ · vₖ` fold: one `coefficient/value/multiply` block per
summand, closed by a run of `add` tags. -/
private lemma foldr_addMul_serialize (L : List ℕ) (u v : ℕ → EF) :
    (L.foldr (fun k acc => EF.add (EF.mul (u k) (v k)) acc) (EF.const 0)).serialize =
      (L.flatMap fun k => (u k).serialize ++ (v k).serialize ++ [3]) ++
        (EF.const 0).serialize ++ List.replicate L.length 2 := by
  induction L with
  | nil => simp
  | cons k L ih =>
      simp only [List.foldr_cons, List.flatMap_cons, List.length_cons]
      rw [show (EF.add (EF.mul (u k) (v k))
            (L.foldr (fun k acc => EF.add (EF.mul (u k) (v k)) acc) (EF.const 0))).serialize =
          ((u k).serialize ++ (v k).serialize ++ [3]) ++
            (L.foldr (fun k acc => EF.add (EF.mul (u k) (v k)) acc)
              (EF.const 0)).serialize ++ [2] by
        simp [EF.serialize, List.append_assoc]]
      rw [ih]
      simp [List.replicate_succ', List.append_assoc]

private lemma foldr_addMul_rank (L : List ℕ) (u v : ℕ → EF) (n : ℕ)
    (hu : ∀ k ∈ L, (u k).rank ≤ n) (hv : ∀ k ∈ L, (v k).rank ≤ n) :
    (L.foldr (fun k acc => EF.add (EF.mul (u k) (v k)) acc) (EF.const 0)).rank ≤ n := by
  induction L with
  | nil => simp [EF.rank]
  | cons k L ih =>
      simp only [List.foldr_cons, EF.rank]
      refine Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨hu k (by simp), hv k (by simp)⟩,
        ih (fun j hj => hu j (by simp [hj])) (fun j hj => hv j (by simp [hj]))⟩

private lemma foldr_addMul_closed (L : List ℕ) (u v : ℕ → EF) (ρ : List ℝ) (V : History)
    (hu : ∀ k ∈ L, (u k).denoteWith ρ V = (u k).denote V)
    (hv : ∀ k ∈ L, (v k).denoteWith ρ V = (v k).denote V) :
    (L.foldr (fun k acc => EF.add (EF.mul (u k) (v k)) acc) (EF.const 0)).denoteWith ρ V =
      (L.foldr (fun k acc => EF.add (EF.mul (u k) (v k)) acc) (EF.const 0)).denote V := by
  induction L with
  | nil => simp [EF.denoteWith, EF.denote]
  | cons k L ih =>
      simp only [List.foldr_cons, EF.denoteWith, EF.denote_add, EF.denote_mul,
        Pi.add_apply, Pi.mul_apply]
      rw [hu k (by simp), hv k (by simp),
        ih (fun j hj => hu j (by simp [hj])) (fun j hj => hv j (by simp [hj]))]

/-- **Variable-width affine combinator.**  A polynomially emitted *block* family `Bs`
(indexed by `⟨m,k⟩`: evaluation day `m`, source day `k`) and a day-`m`-legal coefficient
family combine into a polynomially emitted affine sequence whose day-`m` member is
`Σ_{k < cnt m} coeff⟨m,k⟩ · Bs⟨m,k⟩`.  Blocks are padded to the common width `width m`, so
the flat term index stays a plain `range` and the block/offset inverse is division and
remainder rather than an inverse prefix-sum. -/
noncomputable def PolySequence.blockSum
    {Bs : ℕ → AffineCombination} (hB : PolySequence Bs)
    {coeff : ℕ → EF} (hcoeff : RpnSpliceStream fun z => (coeff z).serialize)
    (hcoeffClosed : ∀ z ρ V, (coeff z).denoteWith ρ V = (coeff z).denote V)
    (hcoeffRank : ∀ m k, (coeff (Nat.pair m k)).rank ≤ m)
    {cnt width : ℕ → ℕ}
    (hcnt : ∃ c, PolyFueled c cnt) (hwidth : ∃ c, PolyFueled c width)
    (hwidthPos : ∀ m, 0 < width m)
    (hBconstRank : ∀ m k, (Bs (Nat.pair m k)).const.rank ≤ m)
    (hBcoeffRank : ∀ m k o, o < hB.termCount (Nat.pair m k) →
      (hB.coefficient (Nat.pair (Nat.pair m k) o)).rank ≤ m)
    (pad : Sentence) (hpad : RpnSentenceCodes fun _ : ℕ => pad) :
    PolySequence (AffineCombination.blockSum Bs coeff cnt width pad) := by
  have hcntPF := Classical.choose_spec hcnt
  have hwidthPF := Classical.choose_spec hwidth
  have hmulPF := Classical.choose_spec mul_polyFueled
  have hdmPF := Classical.choose_spec divmod1_polyFueled
  have htcPF0 := Classical.choose_spec hB.termCount_poly
  -- block index and offset of a flat term index
  have hdm0 := hdmPF.comp ((subc_polyFueled.comp ((hwidthPF.comp PolyFueled.left).pair
    (PolyFueled.const 1))).pair PolyFueled.right)
  have hdm : PolyFueled _ (fun z : ℕ ↦
      Nat.pair (z.unpair.2 / width z.unpair.1) (z.unpair.2 % width z.unpair.1)) :=
    hdm0.of_eq (fun z ↦ by
      have hw := hwidthPos z.unpair.1
      simp only [Nat.unpair_pair]
      rw [show width z.unpair.1 - 1 + 1 = width z.unpair.1 from by omega])
  have hblk : PolyFueled _ (fun z : ℕ ↦ z.unpair.2 / width z.unpair.1) :=
    (PolyFueled.left.comp hdm).of_eq (fun z ↦ by simp)
  have hoff : PolyFueled _ (fun z : ℕ ↦ z.unpair.2 % width z.unpair.1) :=
    (PolyFueled.right.comp hdm).of_eq (fun z ↦ by simp)
  have hkey : PolyFueled _ (fun z : ℕ ↦ Nat.pair z.unpair.1 (z.unpair.2 / width z.unpair.1)) :=
    PolyFueled.left.pair hblk
  have hq : PolyFueled _ (fun z : ℕ ↦
      Nat.pair (Nat.pair z.unpair.1 (z.unpair.2 / width z.unpair.1))
        (z.unpair.2 % width z.unpair.1)) := hkey.pair hoff
  have htest : PolyFueled _ (fun z : ℕ ↦
      (z.unpair.2 % width z.unpair.1 + 1) -
        hB.termCount (Nat.pair z.unpair.1 (z.unpair.2 / width z.unpair.1))) :=
    (subc_polyFueled.comp (hoff.succ_comp.pair (htcPF0.comp hkey))).of_eq
      (fun z ↦ by simp)
  have htermCount : ∃ c, PolyFueled c (fun m ↦ cnt m * width m) :=
    ⟨_, (hmulPF.comp (hcntPF.pair hwidthPF)).of_eq (fun m ↦ by simp)⟩
  refine
    { termCount := fun m ↦ cnt m * width m
      coefficient := fun z ↦ EF.mul
        (coeff (Nat.pair z.unpair.1 (z.unpair.2 / width z.unpair.1)))
        (if z.unpair.2 % width z.unpair.1 <
            hB.termCount (Nat.pair z.unpair.1 (z.unpair.2 / width z.unpair.1)) then
          hB.coefficient (Nat.pair (Nat.pair z.unpair.1 (z.unpair.2 / width z.unpair.1))
            (z.unpair.2 % width z.unpair.1))
        else EF.const 0)
      sentence := fun z ↦
        if z.unpair.2 % width z.unpair.1 <
            hB.termCount (Nat.pair z.unpair.1 (z.unpair.2 / width z.unpair.1)) then
          hB.sentence (Nat.pair (Nat.pair z.unpair.1 (z.unpair.2 / width z.unpair.1))
            (z.unpair.2 % width z.unpair.1))
        else pad
      termCount_poly := htermCount
      const_poly := ?_
      coefficient_poly := ?_
      sentence_poly := ?_
      terms_eq := ?_
      const_rank := ?_
      coefficient_rank := ?_
      const_closed := ?_
      coefficient_closed := ?_ }
  · refine RpnSpliceStream.of_eq
      ((((hcoeff.append hB.const_poly).append (RpnSpliceStream.tag 3 (by norm_num))).concatVar
        hcntPF).append ((RpnSpliceStream.serialize_const 0).append
          (RpnSpliceStream.repeatTag 2 (by norm_num) hcntPF))) (fun m ↦ ?_)
    rw [AffineCombination.blockSum, foldr_addMul_serialize]
    simp [List.append_assoc]
  · have hif : RpnSpliceStream (fun z ↦
        (if z.unpair.2 % width z.unpair.1 <
            hB.termCount (Nat.pair z.unpair.1 (z.unpair.2 / width z.unpair.1)) then
          hB.coefficient (Nat.pair (Nat.pair z.unpair.1 (z.unpair.2 / width z.unpair.1))
            (z.unpair.2 % width z.unpair.1))
        else EF.const 0).serialize) := by
      refine RpnSpliceStream.of_eq (RpnSpliceStream.ifZero (hB.coefficient_poly.comp hq)
        (RpnSpliceStream.serialize_const 0) htest) (fun z ↦ ?_)
      by_cases hlt : z.unpair.2 % width z.unpair.1 <
          hB.termCount (Nat.pair z.unpair.1 (z.unpair.2 / width z.unpair.1))
      · rw [if_pos hlt, if_pos (show _ = 0 from by omega)]
      · rw [if_neg hlt, if_neg (show ¬ _ = 0 from by omega)]
    exact RpnSpliceStream.serialize_mul (hcoeff.comp hkey) hif
  · refine (RpnSentenceCodes.ifZero (hB.sentence_poly.comp hq) hpad htest).of_eq (fun z ↦ ?_)
    by_cases hlt : z.unpair.2 % width z.unpair.1 <
        hB.termCount (Nat.pair z.unpair.1 (z.unpair.2 / width z.unpair.1))
    · rw [if_pos (show _ = 0 from by omega), if_pos hlt]
    · rw [if_neg (show ¬ _ = 0 from by omega), if_neg hlt]
  · intro m
    rw [AffineCombination.blockSum,
      flatMap_range_map_range (cnt m) (width m) (hwidthPos m)]
    refine List.map_congr_left fun j _ ↦ ?_
    simp only [Nat.unpair_pair]
    rw [hB.terms_eq, getD_map_range]
    by_cases hlt : j % width m < hB.termCount (Nat.pair m (j / width m)) <;>
      simp [hlt, AffineCombination.padEntry]
  · intro m
    rw [AffineCombination.blockSum]
    exact foldr_addMul_rank _ _ _ m (fun k _ ↦ hcoeffRank m k) (fun k _ ↦ hBconstRank m k)
  · intro m j hj
    simp only [Nat.unpair_pair, EF.rank]
    refine Nat.max_le.mpr ⟨hcoeffRank m (j / width m), ?_⟩
    by_cases hlt : j % width m < hB.termCount (Nat.pair m (j / width m))
    · rw [if_pos hlt]
      exact hBcoeffRank m (j / width m) (j % width m) hlt
    · rw [if_neg hlt]
      simp [EF.rank]
  · intro m ρ V
    rw [AffineCombination.blockSum]
    exact foldr_addMul_closed _ _ _ ρ V (fun k _ ↦ hcoeffClosed _ ρ V)
      (fun k _ ↦ hB.const_closed _ ρ V)
  · intro z ρ V
    simp only [EF.denoteWith, EF.denote_mul, Pi.mul_apply]
    rw [hcoeffClosed _ ρ V]
    by_cases hlt : z.unpair.2 % width z.unpair.1 <
        hB.termCount (Nat.pair z.unpair.1 (z.unpair.2 / width z.unpair.1))
    · rw [if_pos hlt, hB.coefficient_closed _ ρ V]
    · rw [if_neg hlt]
      simp [EF.denoteWith]

end AffineCombination
end LogicalInduction
