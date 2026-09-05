import LogicalInduction.Construction.Witnesses.SemanticCertifiedProduct

/-!
# Executable admission of rational quotation factors

The executable admission gate for tag-`2` quotation factors of the fixed product registry:
`app` machinery for `thm:ccee` with no paper `\label` of its own, serving
`lic_no_expected_net_update_conditional_*`.

Tag `2` differs from tag `0`.  A certified paper source carries its own cut-proof program,
whereas a deferred weight already has the repository's `RationalQuoteCode`, and
`semanticQuoteDP` identifies its leaves with old quotation atoms.  The only coherence the
exact product needs from such a factor is downward closure on each finite rational-query
prefix; bounds come separately from `RationalQuoteCode.value_mem`.

Objects defined: `semanticSentenceSeenAtFuel` (bounded literal search in a computable
process), `semanticQuoteFactorClaim` and `…Link`, `…EvidenceAtFuel`, `…DownwardAtFuel`, and
the three nested prefix quantifiers `…ZsValid` / `…ZrValid` / `…NValid` feeding
`semanticQuoteFactorPrefixValidAtFuel`.

Main results: `…PrefixValidAtFuel_computable` (the gate is decidable), `…_mono` (clock
monotonicity), `…_downward` (what an accepted prefix yields), and the two completeness
lemmas `rationalQuote_semanticQuoteFactorPrefix_eventually{,_of_subprocess}`.  They are
consumed by `SemanticRegistryProduct.lean` and `SemanticLiftedCCEE.lean`.

Design: for `r < s`, downward closure follows from either the positive claim at `r` or the
negative claim at `s`; every total `[0,1]` `RationalQuoteCode` eventually supplies one, and a
malformed selector is never trusted for wearing tag `2`.  The `_of_subprocess` form is the
general one — it asks only that the base process contain the canonical theorem/quotation
stages — and the fixed-base form is its instance.
-/

namespace LogicalInduction

open LO LO.Propositional LO.FirstOrder LO.FirstOrder.Arithmetic

attribute [local irreducible] Nat.sqrt

/-! ## Bounded literal search in a computable process -/

/-- Bounded search for a literal sentence in a fixed computable process. -/
def semanticSentenceSeenAtFuel {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (φ : Sentence) (fuel : ℕ) : Bool :=
  (List.range (fuel + 1)).any fun k =>
    match base.stageAtFuel fuel k with
    | some stage => decide (φ ∈ stage)
    | none => false

private lemma listRangeAny_prim' {α : Type} [Primcodable α]
    {bound : α → ℕ} {test : α → ℕ → Bool}
    (hbound : Primrec bound) (htest : Primrec₂ test) :
    Primrec fun a => (List.range (bound a + 1)).any (test a) := by
  have hrange : Primrec fun a => List.range (bound a + 1) :=
    Primrec.list_range.comp (Primrec.nat_add.comp hbound (Primrec.const 1))
  have hstep : Primrec₂ fun (a : α) (q : ℕ × Bool) => test a q.1 || q.2 :=
    (Primrec.dom_bool₂ (· || ·)).comp₂
      (htest.comp₂ Primrec₂.left (Primrec.fst.comp₂ Primrec₂.right))
      (Primrec.snd.comp₂ Primrec₂.right)
  exact (Primrec.list_foldr hrange (Primrec.const false) hstep).of_eq fun a => by
    induction List.range (bound a + 1) with
    | nil => rfl
    | cons x xs ih => simp [List.any, ih]

lemma semanticSentenceSeenAtFuel_prim {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) :
    Primrec fun p : Sentence × ℕ => semanticSentenceSeenAtFuel base p.1 p.2 := by
  let P := Sentence × ℕ
  have hbound : Primrec fun p : P => p.2 := Primrec.snd
  have htest : Primrec₂ fun (p : P) (k : ℕ) =>
      match base.stageAtFuel p.2 k with
      | some stage => decide (p.1 ∈ stage)
      | none => false := by
    let Q := P × ℕ
    have hstage : Primrec fun q : Q => base.stageAtFuel q.1.2 q.2 :=
      (processStageAtFuel_prim base).comp
        (Primrec.snd.comp Primrec.fst) Primrec.snd
    have hmem : Primrec₂ fun (q : Q) (stage : Finset Sentence) =>
        decide (q.1.1 ∈ stage) :=
      (sentenceMemSupport_prim.comp₂ Primrec₂.right
        (Primrec.fst.comp₂ (Primrec.fst.comp₂ Primrec₂.left))).decide
    exact (Primrec.option_casesOn hstage (Primrec.const false) hmem).to₂.of_eq fun p k => by
      cases base.stageAtFuel p.2 k <;> simp
  exact listRangeAny_prim' hbound htest

lemma semanticSentenceSeenAtFuel_iff {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (φ : Sentence) (fuel : ℕ) :
    semanticSentenceSeenAtFuel base φ fuel = true ↔
      ∃ k ≤ fuel, ∃ stage,
        base.stageAtFuel fuel k = some stage ∧ φ ∈ stage := by
  rw [semanticSentenceSeenAtFuel, List.any_eq_true]
  simp only [List.mem_range, Nat.lt_add_one_iff]
  constructor
  · rintro ⟨k, hk, h⟩
    cases hs : base.stageAtFuel fuel k with
    | none => simp [hs] at h
    | some stage => exact ⟨k, hk, stage, hs, by simpa [hs] using h⟩
  · rintro ⟨k, hk, stage, hs, hmem⟩
    exact ⟨k, hk, by simp [hs, hmem]⟩

lemma semanticSentenceSeenAtFuel_mono {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) {φ : Sentence} {fuel fuel' : ℕ}
    (hff : fuel ≤ fuel')
    (h : semanticSentenceSeenAtFuel base φ fuel = true) :
    semanticSentenceSeenAtFuel base φ fuel' = true := by
  obtain ⟨k, hk, stage, hs, hmem⟩ :=
    (semanticSentenceSeenAtFuel_iff base φ fuel).1 h
  exact (semanticSentenceSeenAtFuel_iff base φ fuel').2
    ⟨k, hk.trans hff, stage, base.stageAtFuel_mono hff hs, hmem⟩

lemma semanticSentenceSeenAtFuel_sound {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) {φ : Sentence} {fuel : ℕ}
    (h : semanticSentenceSeenAtFuel base φ fuel = true) :
    ∃ k, φ ∈ DP.D k := by
  obtain ⟨k, _, stage, hs, hmem⟩ :=
    (semanticSentenceSeenAtFuel_iff base φ fuel).1 h
  exact ⟨k, base.stageAtFuel_sound hs ▸ hmem⟩

lemma semanticSentenceSeenAtFuel_eventually {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) {φ : Sentence} {k : ℕ}
    (hmem : φ ∈ DP.D k) : ∃ fuel, semanticSentenceSeenAtFuel base φ fuel = true := by
  obtain ⟨f, hf⟩ := base.stageAtFuel_complete k
  let fuel := max f k
  refine ⟨fuel, (semanticSentenceSeenAtFuel_iff base φ fuel).2 ?_⟩
  exact ⟨k, by simp [fuel], DP.D k,
    base.stageAtFuel_mono (by simp [fuel]) hf, hmem⟩

/-! ## The quotation claim and its definitional link -/

/-- The old quotation claim corresponding to a tag-`2` leaf threshold. -/
noncomputable def semanticQuoteFactorClaim (schema n z : ℕ) (positive : Bool) : Sentence :=
  let atom := quoteAtom (Nat.pair schema.unpair.2
    (Nat.pair n (Encodable.encode (decodedQuotationRat z))))
  bif positive then atom else ∼atom

/-- The fixed quote-leaf direction needed to turn an exposed old quotation literal into
the corresponding semantic fact (positive), or conversely (negative). -/
noncomputable def semanticQuoteFactorLink (schema n z : ℕ) (positive : Bool) : Sentence :=
  let input := Nat.pair n (Encodable.encode (decodedQuotationRat z))
  semanticQuoteDefSentence
    (Nat.pair (bif positive then 0 else 1) (Nat.pair schema.unpair.2 input))

/-! ## The bounded evidence and the finite prefix -/

/-- Both the quotation claim and its definitional link have appeared by this clock. -/
noncomputable def semanticQuoteFactorEvidenceAtFuel {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP)
    (schema fuel n z : ℕ) (positive : Bool) : Bool :=
  semanticSentenceSeenAtFuel base (semanticQuoteFactorClaim schema n z positive) fuel &&
    semanticSentenceSeenAtFuel base (semanticQuoteFactorLink schema n z positive) fuel

attribute [local irreducible] semanticQuoteFactorClaim semanticQuoteFactorLink
  semanticQuoteFactorEvidenceAtFuel

/-- For `r < s`, downward closure is witnessed by the positive claim at `r` or the negative
claim at `s`; trivially true otherwise. -/
noncomputable def semanticQuoteFactorDownwardAtFuel {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP)
    (schema fuel n zr zs : ℕ) : Bool :=
  if decodedQuotationRat zr < decodedQuotationRat zs then
    semanticQuoteFactorEvidenceAtFuel base schema fuel n zr true ||
      semanticQuoteFactorEvidenceAtFuel base schema fuel n zs false
  else true

/-- Inclusive bounded conjunction over the right-threshold coordinate. -/
noncomputable def semanticQuoteFactorZsValid {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (schema fuel n zr limit : ℕ) : Bool :=
  (List.range (limit + 1)).all fun zs =>
    semanticQuoteFactorDownwardAtFuel base schema fuel n zr zs

/-- Inclusive bounded conjunction over the left-threshold coordinate. -/
noncomputable def semanticQuoteFactorZrValid {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP)
    (schema limit fuel n : ℕ) : Bool :=
  (List.range (limit + 1)).all fun zr =>
    semanticQuoteFactorZsValid base schema fuel n zr limit

/-- Inclusive bounded conjunction over the source index. -/
noncomputable def semanticQuoteFactorNValid {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP)
    (schema limit fuel : ℕ) : Bool :=
  (List.range (limit + 1)).all fun n =>
    semanticQuoteFactorZrValid base schema limit fuel n

/-- Every pairwise downward query through `limit` is justified by an exposed quotation
claim.  Bounds are supplied separately by `RationalQuoteCode.value_mem`; exact product
closure only needs this downward compatibility. -/
noncomputable def semanticQuoteFactorPrefixValidAtFuel {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP)
    (schema limit fuel : ℕ) : Bool :=
  (schema.unpair.1 == 2) &&
    semanticQuoteFactorNValid base schema limit fuel

/-! ## Decidability of the gate -/

private lemma sentenceNeg_computable : Computable fun φ : Sentence => ∼φ := by
  have h : Primrec fun φ : Sentence => ∼φ := by
    apply Primrec.encode_iff.mp
    exact (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 2)
      (Primrec₂.natPair.comp Primrec.encode (Primrec.const 1)))).of_eq fun _ => rfl
  exact h.to_comp

lemma semanticQuoteFactorClaim_computable :
    Computable fun p : ((ℕ × ℕ) × ℕ) × Bool =>
      semanticQuoteFactorClaim p.1.1.1 p.1.1.2 p.1.2 p.2 := by
  let P := ((ℕ × ℕ) × ℕ) × Bool
  have hschema : Computable fun p : P => p.1.1.1 :=
    (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).to_comp
  have hn : Computable fun p : P => p.1.1.2 :=
    (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).to_comp
  have hz : Computable fun p : P => p.1.2 :=
    (Primrec.snd.comp Primrec.fst).to_comp
  have hpositive : Computable fun p : P => p.2 := Computable.snd
  have hcode : Computable fun p : P => p.1.1.1.unpair.2 :=
    (Primrec.snd.comp Primrec.unpair).to_comp.comp hschema
  have hrat : Computable fun p : P => decodedQuotationRat p.1.2 :=
    decodedQuotationRat_prim.to_comp.comp hz
  have hinput : Computable fun p : P => Nat.pair p.1.1.2
      (Encodable.encode (decodedQuotationRat p.1.2)) :=
    Primrec₂.natPair.to_comp.comp hn (Computable.encode.comp hrat)
  have hatom : Computable fun p : P => quoteAtom
      (Nat.pair p.1.1.1.unpair.2
        (Nat.pair p.1.1.2 (Encodable.encode (decodedQuotationRat p.1.2)))) :=
    quoteAtom_computable.comp (Primrec₂.natPair.to_comp.comp hcode hinput)
  exact (Computable.cond hpositive hatom (sentenceNeg_computable.comp hatom)).of_eq
    fun p => by cases p.2 <;> rw [semanticQuoteFactorClaim]

lemma semanticQuoteFactorLink_computable :
    Computable fun p : ((ℕ × ℕ) × ℕ) × Bool =>
      semanticQuoteFactorLink p.1.1.1 p.1.1.2 p.1.2 p.2 := by
  let P := ((ℕ × ℕ) × ℕ) × Bool
  have hschema : Computable fun p : P => p.1.1.1 :=
    (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).to_comp
  have hn : Computable fun p : P => p.1.1.2 :=
    (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).to_comp
  have hz : Computable fun p : P => p.1.2 :=
    (Primrec.snd.comp Primrec.fst).to_comp
  have hcode : Computable fun p : P => p.1.1.1.unpair.2 :=
    (Primrec.snd.comp Primrec.unpair).to_comp.comp hschema
  have hinput : Computable fun p : P => Nat.pair p.1.1.2
      (Encodable.encode (decodedQuotationRat p.1.2)) :=
    Primrec₂.natPair.to_comp.comp hn
      (Computable.encode.comp (decodedQuotationRat_prim.to_comp.comp hz))
  have hkind : Computable fun p : P => bif p.2 then 0 else 1 :=
    (Computable.cond Computable.snd (Computable.const 0) (Computable.const 1)).of_eq
      fun p => by cases p.2 <;> rfl
  have hjob : Computable fun p : P => Nat.pair (bif p.2 then 0 else 1)
      (Nat.pair p.1.1.1.unpair.2
        (Nat.pair p.1.1.2 (Encodable.encode (decodedQuotationRat p.1.2)))) :=
    Primrec₂.natPair.to_comp.comp hkind
      (Primrec₂.natPair.to_comp.comp hcode hinput)
  exact (semanticQuoteDefSentence_computable.comp hjob).of_eq fun p => by
    rw [semanticQuoteFactorLink]

set_option maxHeartbeats 2000000 in
lemma semanticQuoteFactorEvidenceAtFuel_computable {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) :
    Computable fun p : ((((ℕ × ℕ) × ℕ) × ℕ) × Bool) =>
      semanticQuoteFactorEvidenceAtFuel base p.1.1.1.1 p.1.1.1.2
        p.1.1.2 p.1.2 p.2 := by
  let P := ((((ℕ × ℕ) × ℕ) × ℕ) × Bool)
  have hschema : Computable fun p : P => p.1.1.1.1 :=
    (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))).to_comp
  have hfuel : Computable fun p : P => p.1.1.1.2 :=
    (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))).to_comp
  have hn : Computable fun p : P => p.1.1.2 :=
    (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).to_comp
  have hz : Computable fun p : P => p.1.2 :=
    (Primrec.snd.comp Primrec.fst).to_comp
  have hpositive : Computable fun p : P => p.2 := Computable.snd
  have hclaim : Computable fun p : P =>
      semanticQuoteFactorClaim p.1.1.1.1 p.1.1.2 p.1.2 p.2 :=
    semanticQuoteFactorClaim_computable.comp
      (((hschema.pair hn).pair hz).pair hpositive)
  have hlink : Computable fun p : P =>
      semanticQuoteFactorLink p.1.1.1.1 p.1.1.2 p.1.2 p.2 :=
    semanticQuoteFactorLink_computable.comp
      (((hschema.pair hn).pair hz).pair hpositive)
  have hclaimSeen : Computable fun p : P => semanticSentenceSeenAtFuel base
      (semanticQuoteFactorClaim p.1.1.1.1 p.1.1.2 p.1.2 p.2) p.1.1.1.2 :=
    semanticSentenceSeenAtFuel_prim base |>.to_comp.comp (hclaim.pair hfuel)
  have hlinkSeen : Computable fun p : P => semanticSentenceSeenAtFuel base
      (semanticQuoteFactorLink p.1.1.1.1 p.1.1.2 p.1.2 p.2) p.1.1.1.2 :=
    semanticSentenceSeenAtFuel_prim base |>.to_comp.comp (hlink.pair hfuel)
  exact ((Primrec.dom_bool₂ (· && ·)).to_comp.comp hclaimSeen hlinkSeen).of_eq
    fun p => by rw [semanticQuoteFactorEvidenceAtFuel]

set_option maxHeartbeats 2000000 in
lemma semanticQuoteFactorDownwardAtFuel_computable {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) :
    Computable fun p : ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) =>
      semanticQuoteFactorDownwardAtFuel base
        p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2 := by
  let P := ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)
  have hschema : Computable fun p : P => p.1.1.1.1 :=
    (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))).to_comp
  have hfuel : Computable fun p : P => p.1.1.1.2 :=
    (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))).to_comp
  have hn : Computable fun p : P => p.1.1.2 :=
    (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).to_comp
  have hzr : Computable fun p : P => p.1.2 := (Primrec.snd.comp Primrec.fst).to_comp
  have hzs : Computable fun p : P => p.2 := Computable.snd
  have hr : Computable fun p : P => decodedQuotationRat p.1.2 :=
    decodedQuotationRat_prim.to_comp.comp hzr
  have hs : Computable fun p : P => decodedQuotationRat p.2 :=
    decodedQuotationRat_prim.to_comp.comp hzs
  have hlt : Computable fun p : P => decide
      (decodedQuotationRat p.1.2 < decodedQuotationRat p.2) := by
    have hle : Computable fun p : P => decide
        (decodedQuotationRat p.2 ≤ decodedQuotationRat p.1.2) :=
      ratLE_prim.decide.to_comp.comp hs hr
    exact ((Primrec.dom_bool Bool.not).to_comp.comp hle).of_eq fun p => by
      by_cases h : decodedQuotationRat p.2 ≤ decodedQuotationRat p.1.2
      · have hnlt : ¬ decodedQuotationRat p.1.2 < decodedQuotationRat p.2 := not_lt_of_ge h
        simp [h, hnlt]
      · have hlt : decodedQuotationRat p.1.2 < decodedQuotationRat p.2 := lt_of_not_ge h
        simp [h, hlt]
  have hevidence (positive : Bool) (z : P → ℕ) (hz : Computable z) :
      Computable fun p : P => semanticQuoteFactorEvidenceAtFuel base
        p.1.1.1.1 p.1.1.1.2 p.1.1.2 (z p) positive :=
    semanticQuoteFactorEvidenceAtFuel_computable base |>.comp
      ((((hschema.pair hfuel).pair hn).pair hz).pair (Computable.const positive))
  have hbody : Computable fun p : P =>
      semanticQuoteFactorEvidenceAtFuel base p.1.1.1.1 p.1.1.1.2
          p.1.1.2 p.1.2 true ||
        semanticQuoteFactorEvidenceAtFuel base p.1.1.1.1 p.1.1.1.2
          p.1.1.2 p.2 false :=
    (Primrec.dom_bool₂ (· || ·)).to_comp.comp
      (hevidence true _ hzr) (hevidence false _ hzs)
  exact (Computable.cond hlt hbody (Computable.const true)).of_eq fun p => by
    simp only [semanticQuoteFactorDownwardAtFuel]
    by_cases h : decodedQuotationRat p.1.2 < decodedQuotationRat p.2 <;> simp [h]

private lemma listRangeAll_computable {P : Type*} [Primcodable P]
    {bound : P → ℕ} {test : P → ℕ → Bool}
    (hbound : Computable bound) (htest : Computable₂ test) :
    Computable fun p => (List.range (bound p + 1)).all (test p) := by
  have hbase : Computable fun p : P => test p 0 :=
    htest.comp Computable.id (Computable.const 0)
  have hstep : Computable₂ fun (p : P) (q : ℕ × Bool) =>
      q.2 && test p (q.1 + 1) := by
    exact (Primrec.dom_bool₂ (· && ·)).to_comp.comp
      (Computable.snd.comp Computable.snd)
      (htest.comp (Computable.fst)
        (Computable.succ.comp (Computable.fst.comp Computable.snd))) |>.to₂
  refine (Computable.nat_rec hbound hbase hstep).of_eq fun p => ?_
  induction bound p with
  | zero => simp
  | succ k ih => simp [List.range_succ, List.all_append, ih, Bool.and_assoc]

set_option maxHeartbeats 2000000 in
lemma semanticQuoteFactorPrefixValidAtFuel_computable {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) :
    Computable fun p : (ℕ × ℕ) × ℕ =>
      semanticQuoteFactorPrefixValidAtFuel base p.1.1 p.1.2 p.2 := by
  have hdown := semanticQuoteFactorDownwardAtFuel_computable base
  have hzs : Computable fun p : ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) =>
      semanticQuoteFactorZsValid base p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2 := by
    apply listRangeAll_computable Computable.snd
    have hpack : Computable fun a : (((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) =>
        (a.1.1, a.2) := (Computable.fst.comp Computable.fst).pair Computable.snd
    exact hdown.comp hpack
  have hzr : Computable fun p : (((ℕ × ℕ) × ℕ) × ℕ) =>
      semanticQuoteFactorZrValid base p.1.1.1 p.2 p.1.1.2 p.1.2 := by
    apply listRangeAll_computable Computable.snd
    have hpack : Computable fun a : ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) =>
        ((a.1.1, a.2), a.1.2) :=
      ((Computable.fst.comp Computable.fst).pair Computable.snd).pair
        (Computable.snd.comp Computable.fst)
    exact hzs.comp hpack
  have hn : Computable fun p : ((ℕ × ℕ) × ℕ) =>
      semanticQuoteFactorNValid base p.1.1 p.2 p.1.2 := by
    apply listRangeAll_computable Computable.snd
    have hpack : Computable fun a : (((ℕ × ℕ) × ℕ) × ℕ) =>
        ((a.1.1, a.2), a.1.2) :=
      ((Computable.fst.comp Computable.fst).pair Computable.snd).pair
        (Computable.snd.comp Computable.fst)
    exact hzr.comp hpack
  have htag : Computable fun p : (ℕ × ℕ) × ℕ => p.1.1.unpair.1 == 2 :=
    (Primrec.eq.comp
      (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.const 2)).decide.to_comp
  have hn' : Computable fun p : (ℕ × ℕ) × ℕ =>
      semanticQuoteFactorNValid base p.1.1 p.1.2 p.2 :=
    hn.comp (((Computable.fst.comp Computable.fst).pair Computable.snd).pair
      (Computable.snd.comp Computable.fst))
  exact ((Primrec.dom_bool₂ (· && ·)).to_comp.comp htag hn').of_eq fun _ => rfl

/-! ## Clock monotonicity -/

private lemma listAll_mono_fuel {P : Type*} {test : P → ℕ → Bool}
    (hmono : ∀ p {f g}, f ≤ g → test p f = true → test p g = true)
    (xs : List P) {f g : ℕ} (hfg : f ≤ g)
    (h : xs.all fun p => test p f) : xs.all (fun p => test p g) := by
  rw [List.all_eq_true] at h ⊢
  intro p hp
  exact hmono p hfg (h p hp)

private lemma listAll_eventually {P : Type*} {test : P → ℕ → Bool}
    (hmono : ∀ p {f g}, f ≤ g → test p f = true → test p g = true)
    (heventual : ∀ p, ∃ f, test p f = true) :
    ∀ xs : List P, ∃ f, xs.all (fun p => test p f) = true := by
  intro xs
  induction xs with
  | nil => exact ⟨0, by simp⟩
  | cons p ps ih =>
      obtain ⟨fp, hfp⟩ := heventual p
      obtain ⟨fs, hfs⟩ := ih
      refine ⟨max fp fs, ?_⟩
      simp only [List.all_cons, Bool.and_eq_true]
      exact ⟨hmono p (le_max_left _ _) hfp,
        listAll_mono_fuel hmono ps (le_max_right _ _) hfs⟩

lemma semanticQuoteFactorDownwardAtFuel_mono {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (schema n zr zs : ℕ)
    {fuel fuel' : ℕ} (hff : fuel ≤ fuel')
    (h : semanticQuoteFactorDownwardAtFuel base schema fuel n zr zs = true) :
    semanticQuoteFactorDownwardAtFuel base schema fuel' n zr zs = true := by
  by_cases hrs : decodedQuotationRat zr < decodedQuotationRat zs
  · simp only [semanticQuoteFactorDownwardAtFuel, semanticQuoteFactorEvidenceAtFuel,
      if_pos hrs, Bool.or_eq_true, Bool.and_eq_true] at h ⊢
    rcases h with h | h
    · exact Or.inl ⟨semanticSentenceSeenAtFuel_mono base hff h.1,
        semanticSentenceSeenAtFuel_mono base hff h.2⟩
    · exact Or.inr ⟨semanticSentenceSeenAtFuel_mono base hff h.1,
        semanticSentenceSeenAtFuel_mono base hff h.2⟩
  · simp [semanticQuoteFactorDownwardAtFuel, hrs]

private lemma semanticQuoteFactorZsValid_mono {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (schema n zr limit : ℕ)
    {fuel fuel' : ℕ} (hff : fuel ≤ fuel')
    (h : semanticQuoteFactorZsValid base schema fuel n zr limit = true) :
    semanticQuoteFactorZsValid base schema fuel' n zr limit = true := by
  exact listAll_mono_fuel
    (fun zs _ _ hfg hz => semanticQuoteFactorDownwardAtFuel_mono
      base schema n zr zs hfg hz) _ hff h

private lemma semanticQuoteFactorZrValid_mono {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (schema limit n : ℕ)
    {fuel fuel' : ℕ} (hff : fuel ≤ fuel')
    (h : semanticQuoteFactorZrValid base schema limit fuel n = true) :
    semanticQuoteFactorZrValid base schema limit fuel' n = true := by
  exact listAll_mono_fuel
    (fun zr _ _ hfg hz => semanticQuoteFactorZsValid_mono
      base schema n zr limit hfg hz) _ hff h

lemma semanticQuoteFactorPrefixValidAtFuel_mono {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (schema limit : ℕ)
    {fuel fuel' : ℕ} (hff : fuel ≤ fuel')
    (h : semanticQuoteFactorPrefixValidAtFuel base schema limit fuel = true) :
    semanticQuoteFactorPrefixValidAtFuel base schema limit fuel' = true := by
  obtain ⟨htag, hN⟩ : (schema.unpair.1 == 2) = true ∧
      semanticQuoteFactorNValid base schema limit fuel = true := by
    simpa [semanticQuoteFactorPrefixValidAtFuel] using h
  rw [semanticQuoteFactorPrefixValidAtFuel, Bool.and_eq_true]
  refine ⟨htag, ?_⟩
  rw [semanticQuoteFactorNValid, List.all_eq_true] at hN ⊢
  intro n hn
  rw [semanticQuoteFactorZrValid, List.all_eq_true] at ⊢
  intro zr hzr
  rw [semanticQuoteFactorZsValid, List.all_eq_true] at ⊢
  intro zs hzs
  exact semanticQuoteFactorDownwardAtFuel_mono base schema n zr zs hff
    (by
      have hNn := hN n hn
      rw [semanticQuoteFactorZrValid, List.all_eq_true] at hNn
      have hzrFuel := hNn zr hzr
      rw [semanticQuoteFactorZsValid, List.all_eq_true] at hzrFuel
      exact hzrFuel zs hzs)

lemma semanticQuoteFactorPrefixValidAtFuel_downward {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) {schema limit fuel n zr zs : ℕ}
    (h : semanticQuoteFactorPrefixValidAtFuel base schema limit fuel = true)
    (hn : n ≤ limit) (hr : zr ≤ limit) (hs : zs ≤ limit) :
    semanticQuoteFactorDownwardAtFuel base schema fuel n zr zs = true := by
  have hnmem : n ∈ List.range (limit + 1) := by simpa using hn
  have hrmem : zr ∈ List.range (limit + 1) := by simpa using hr
  have hsmem : zs ∈ List.range (limit + 1) := by simpa using hs
  have hpair : (schema.unpair.1 == 2) = true ∧
      semanticQuoteFactorNValid base schema limit fuel = true := by
    simpa [semanticQuoteFactorPrefixValidAtFuel] using h
  obtain ⟨_, hN⟩ := hpair
  rw [semanticQuoteFactorNValid, List.all_eq_true] at hN
  have hzrFuel := hN n hnmem
  rw [semanticQuoteFactorZrValid, List.all_eq_true] at hzrFuel
  have hzsFuel := hzrFuel zr hrmem
  rw [semanticQuoteFactorZsValid, List.all_eq_true] at hzsFuel
  exact hzsFuel zs hsmem

/-! ## Completeness for every rational quote code -/

/-- The quotation-factor completeness argument works in any fixed computable base which
contains the canonical theorem/quotation stages. -/
lemma rationalQuote_semanticQuoteFactorDownward_eventually_of_subprocess
    (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    {DP : DeductiveProcess} (base : DeductiveProcessComputation DP)
    (hsub : ∀ k phi, phi ∈ (theoremQuoteBaseDP T).D k → phi ∈ DP.D k)
    {value : ℕ → ℚ} (q : RationalQuoteCode T value)
    (n zr zs : ℕ) :
    ∃ fuel, semanticQuoteFactorDownwardAtFuel base
      (semanticQuoteSchema q.code) fuel n zr zs = true := by
  by_cases hrs : decodedQuotationRat zr < decodedQuotationRat zs
  · by_cases hrv : decodedQuotationRat zr < value n
    · obtain ⟨k, hk⟩ := (quotationPresentation T).quote_positive_enters q.code
          (Nat.pair n (Encodable.encode (decodedQuotationRat zr)))
          (q.pos_complete n _ hrv)
      have hbase : semanticQuoteFactorClaim (semanticQuoteSchema q.code) n zr true ∈
          DP.D k := hsub k _ (by
        change _ ∈ (theoremDP T).D k ∪ semanticQuoteDP.D k
        apply Finset.mem_union_left
        simpa [semanticQuoteFactorClaim, semanticQuoteSchema, Nat.unpair_pair] using hk)
      obtain ⟨fuel, hfuel⟩ := semanticSentenceSeenAtFuel_eventually base hbase
      let e := Nat.pair 0 (Nat.pair q.code
        (Nat.pair n (Encodable.encode (decodedQuotationRat zr))))
      have hlinkBase : semanticQuoteFactorLink (semanticQuoteSchema q.code) n zr true ∈
          DP.D e := hsub e _ (by
        change _ ∈ (theoremDP T).D e ∪ semanticQuoteDP.D e
        apply Finset.mem_union_right
        change _ ∈ (semanticQuoteStageList e).toFinset
        simpa [semanticQuoteFactorLink, semanticQuoteSchema, e] using
          (List.mem_toFinset.mpr (mem_semanticQuoteStageList (le_refl e))))
      obtain ⟨linkFuel, hlinkFuel⟩ := semanticSentenceSeenAtFuel_eventually base hlinkBase
      let common := max fuel linkFuel
      have hc := semanticSentenceSeenAtFuel_mono base
        (Nat.le_max_left fuel linkFuel) hfuel
      have hl := semanticSentenceSeenAtFuel_mono base
        (Nat.le_max_right fuel linkFuel) hlinkFuel
      exact ⟨common, by
        simp only [semanticQuoteFactorDownwardAtFuel, semanticQuoteFactorEvidenceAtFuel,
          if_pos hrs, Bool.or_eq_true, Bool.and_eq_true]
        exact Or.inl ⟨hc, hl⟩⟩
    · have hvs : value n < decodedQuotationRat zs :=
        lt_of_le_of_lt (not_lt.mp hrv) hrs
      obtain ⟨k, hk⟩ := (quotationPresentation T).quote_negative_refutes q.code
          (Nat.pair n (Encodable.encode (decodedQuotationRat zs)))
          (q.neg_complete n _ hvs)
      have hbase : semanticQuoteFactorClaim (semanticQuoteSchema q.code) n zs false ∈
          DP.D k := hsub k _ (by
        change _ ∈ (theoremDP T).D k ∪ semanticQuoteDP.D k
        apply Finset.mem_union_left
        simpa [semanticQuoteFactorClaim, semanticQuoteSchema, Nat.unpair_pair] using hk)
      obtain ⟨fuel, hfuel⟩ := semanticSentenceSeenAtFuel_eventually base hbase
      let e := Nat.pair 1 (Nat.pair q.code
        (Nat.pair n (Encodable.encode (decodedQuotationRat zs))))
      have hlinkBase : semanticQuoteFactorLink (semanticQuoteSchema q.code) n zs false ∈
          DP.D e := hsub e _ (by
        change _ ∈ (theoremDP T).D e ∪ semanticQuoteDP.D e
        apply Finset.mem_union_right
        change _ ∈ (semanticQuoteStageList e).toFinset
        simpa [semanticQuoteFactorLink, semanticQuoteSchema, e] using
          (List.mem_toFinset.mpr (mem_semanticQuoteStageList (le_refl e))))
      obtain ⟨linkFuel, hlinkFuel⟩ := semanticSentenceSeenAtFuel_eventually base hlinkBase
      let common := max fuel linkFuel
      have hc := semanticSentenceSeenAtFuel_mono base
        (Nat.le_max_left fuel linkFuel) hfuel
      have hl := semanticSentenceSeenAtFuel_mono base
        (Nat.le_max_right fuel linkFuel) hlinkFuel
      exact ⟨common, by
        simp only [semanticQuoteFactorDownwardAtFuel, semanticQuoteFactorEvidenceAtFuel,
          if_pos hrs, Bool.or_eq_true, Bool.and_eq_true]
        exact Or.inr ⟨hc, hl⟩⟩
  · exact ⟨0, by simp [semanticQuoteFactorDownwardAtFuel, hrs]⟩

/-- The fixed-base instance of the completeness argument. -/
lemma rationalQuote_semanticQuoteFactorDownward_eventually
    (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    {value : ℕ → ℚ} (q : RationalQuoteCode T value)
    (n zr zs : ℕ) :
    ∃ fuel, semanticQuoteFactorDownwardAtFuel (theoremQuoteBaseDPComputation T)
      (semanticQuoteSchema q.code) fuel n zr zs = true :=
  rationalQuote_semanticQuoteFactorDownward_eventually_of_subprocess T
    (theoremQuoteBaseDPComputation T) (fun _ _ h => h) q n zr zs

set_option maxHeartbeats 2000000 in
lemma rationalQuote_semanticQuoteFactorPrefix_eventually_of_subprocess
    (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    {DP : DeductiveProcess} (base : DeductiveProcessComputation DP)
    (hsub : ∀ k phi, phi ∈ (theoremQuoteBaseDP T).D k → phi ∈ DP.D k)
    {value : ℕ → ℚ} (q : RationalQuoteCode T value) (limit : ℕ) :
    ∃ fuel, semanticQuoteFactorPrefixValidAtFuel base
      (semanticQuoteSchema q.code) limit fuel = true := by
  have hzs (n zr : ℕ) : ∃ fuel,
      semanticQuoteFactorZsValid base (semanticQuoteSchema q.code)
        fuel n zr limit = true := by
    simpa [semanticQuoteFactorZsValid] using
      (listAll_eventually (test := fun zs fuel =>
        semanticQuoteFactorDownwardAtFuel base
          (semanticQuoteSchema q.code) fuel n zr zs)
        (fun zs _ _ hfg h => semanticQuoteFactorDownwardAtFuel_mono
          base _ _ _ _ hfg h)
        (fun zs => rationalQuote_semanticQuoteFactorDownward_eventually_of_subprocess
          T base hsub q n zr zs)
        (List.range (limit + 1)))
  have hzr (n : ℕ) : ∃ fuel,
      semanticQuoteFactorZrValid base (semanticQuoteSchema q.code)
        limit fuel n = true := by
    apply listAll_eventually
        (test := fun zr fuel => semanticQuoteFactorZsValid
          base (semanticQuoteSchema q.code) fuel n zr limit)
        _ (hzs n) (List.range (limit + 1))
    intro zr f g hfg h
    exact semanticQuoteFactorZsValid_mono base
      (semanticQuoteSchema q.code) n zr limit hfg h
  obtain ⟨fuel, hfuel⟩ := listAll_eventually
    (test := fun n fuel => semanticQuoteFactorZrValid
      base (semanticQuoteSchema q.code) limit fuel n)
    (fun n _ _ hfg h => semanticQuoteFactorZrValid_mono
      base (semanticQuoteSchema q.code) limit n hfg h)
    hzr (List.range (limit + 1))
  refine ⟨fuel, ?_⟩
  rw [semanticQuoteFactorPrefixValidAtFuel, Bool.and_eq_true]
  exact ⟨by simp [semanticQuoteSchema], by
    rw [semanticQuoteFactorNValid, List.all_eq_true]
    exact List.all_eq_true.mp hfuel⟩

/-- The fixed-base instance of the finite-prefix completeness argument. -/
lemma rationalQuote_semanticQuoteFactorPrefix_eventually
    (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    {value : ℕ → ℚ} (q : RationalQuoteCode T value) (limit : ℕ) :
    ∃ fuel, semanticQuoteFactorPrefixValidAtFuel (theoremQuoteBaseDPComputation T)
      (semanticQuoteSchema q.code) limit fuel = true :=
  rationalQuote_semanticQuoteFactorPrefix_eventually_of_subprocess T
    (theoremQuoteBaseDPComputation T) (fun _ _ h => h) q limit

end LogicalInduction
