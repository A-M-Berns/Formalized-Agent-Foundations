import LogicalInduction.Construction.Witnesses.OldLanguageLift
import LogicalInduction.Construction.Witnesses.SemanticSourceDP

/-!
# Entailment-gated source admission

This is the certificate-free replacement for the tag-`0` cut-law gate.  A bounded witness
contains only clocks for the universal emitter and the already-fixed base process.  The
gate accepts exactly when exhaustive finite propositional evaluation verifies that the
decoded base stage entails the emitted law.
-/

namespace LogicalInduction

open LO LO.Propositional

/-- One bounded certificate-free source-law check.  The packed witness contains emitter
fuel, base-program fuel, and base stage index. -/
def entailedSourceLawEvidenceAt {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (schema job witness : ℕ) : Bool :=
  let emitterFuel := witness.unpair.1
  let baseFuel := witness.unpair.2.unpair.1
  let stage := witness.unpair.2.unpair.2
  match semanticSourceCutLawAtFuel schema job emitterFuel,
      base.stageAtFuel baseFuel stage with
  | some law, some D => stageEntails D law
  | _, _ => false

private def entailedSourceOptions :
    Option Sentence × Option (Finset Sentence) → Bool
  | (some law, some D) => stageEntails D law
  | _ => false

private lemma entailedSourceOptions_prim : Primrec entailedSourceOptions := by
  have hinnerRaw := Primrec.option_casesOn Primrec.snd (Primrec.const false)
      ((stageEntails_primrec.comp
        (Primrec₂.pair.comp₂ Primrec₂.right
          (Primrec.fst.comp₂ Primrec₂.left))).to₂.of_eq fun _ _ => rfl)
  have hinner1 : Primrec fun q : Sentence × Option (Finset Sentence) =>
      match q.2 with
      | some D => stageEntails D q.1
      | none => false := hinnerRaw.of_eq fun q => by cases q.2 <;> rfl
  have hinner : Primrec₂ fun (law : Sentence) (oD : Option (Finset Sentence)) =>
      match oD with
      | some D => stageEntails D law
      | none => false := hinner1.to₂
  exact (Primrec.option_casesOn Primrec.fst (Primrec.const false)
    (hinner.comp₂ Primrec₂.right
      (Primrec.snd.comp₂ Primrec₂.left))).of_eq fun p => by
      rcases p with ⟨olaw, oD⟩
      cases olaw <;> cases oD <;> rfl

set_option maxHeartbeats 4000000 in
lemma entailedSourceLawEvidenceAt_prim {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) :
    Primrec fun p : (ℕ × ℕ) × ℕ =>
      entailedSourceLawEvidenceAt base p.1.1 p.1.2 p.2 := by
  let P := (ℕ × ℕ) × ℕ
  have hschema : Primrec fun p : P => p.1.1 := Primrec.fst.comp Primrec.fst
  have hjob : Primrec fun p : P => p.1.2 := Primrec.snd.comp Primrec.fst
  have hemitterFuel : Primrec fun p : P => p.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have htail : Primrec fun p : P => p.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)
  have hbaseFuel : Primrec fun p : P => p.2.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp htail)
  have hstage : Primrec fun p : P => p.2.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp htail)
  have hlaw : Primrec fun p : P =>
      semanticSourceCutLawAtFuel p.1.1 p.1.2 p.2.unpair.1 :=
    semanticSourceCutLawAtFuel_prim.comp
      ((hschema.pair hjob).pair hemitterFuel)
  have hbase : Primrec fun p : P =>
      base.stageAtFuel p.2.unpair.2.unpair.1 p.2.unpair.2.unpair.2 :=
    (processStageAtFuel_prim base).comp hbaseFuel hstage
  exact (entailedSourceOptions_prim.comp (hlaw.pair hbase)).of_eq fun p => by
    simp only [entailedSourceLawEvidenceAt]
    cases semanticSourceCutLawAtFuel p.1.1 p.1.2 p.2.unpair.1 <;>
      cases base.stageAtFuel p.2.unpair.2.unpair.1 p.2.unpair.2.unpair.2 <;> rfl

/-- Dovetail the bounded evidence over all packed clock/stage witnesses. -/
def entailedSourceLawSeen {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (schema job fuel : ℕ) : Bool :=
  (List.range (fuel + 1)).any fun witness =>
    entailedSourceLawEvidenceAt base schema job witness

private lemma listRangeAny_prim {α : Type} [Primcodable α]
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

lemma entailedSourceLawSeen_prim {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) :
    Primrec fun p : (ℕ × ℕ) × ℕ =>
      entailedSourceLawSeen base p.1.1 p.1.2 p.2 := by
  let P := (ℕ × ℕ) × ℕ
  have htest : Primrec₂ fun (p : P) (witness : ℕ) =>
      entailedSourceLawEvidenceAt base p.1.1 p.1.2 witness := by
    have hpack : Primrec fun q : P × ℕ =>
        ((q.1.1.1, q.1.1.2), q.2) :=
      ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair Primrec.snd
    exact ((entailedSourceLawEvidenceAt_prim base).comp hpack).to₂
  exact listRangeAny_prim Primrec.snd htest

lemma entailedSourceLawSeen_iff {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (schema job fuel : ℕ) :
    entailedSourceLawSeen base schema job fuel = true ↔
      ∃ witness ≤ fuel,
        entailedSourceLawEvidenceAt base schema job witness = true := by
  rw [entailedSourceLawSeen, List.any_eq_true]
  simp only [List.mem_range, Nat.lt_add_one_iff]

lemma entailedSourceLawSeen_mono {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) {schema job fuel fuel' : ℕ}
    (hff : fuel ≤ fuel')
    (h : entailedSourceLawSeen base schema job fuel = true) :
    entailedSourceLawSeen base schema job fuel' = true := by
  obtain ⟨w, hw, he⟩ := (entailedSourceLawSeen_iff base schema job fuel).1 h
  exact (entailedSourceLawSeen_iff base schema job fuel').2
    ⟨w, hw.trans hff, he⟩

/-- Accepted evidence is semantically sound in every completed base world. -/
lemma entailedSourceLawEvidenceAt_sound {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) {schema job witness : ℕ}
    (h : entailedSourceLawEvidenceAt base schema job witness = true) :
    ∃ law,
      semanticSourceCutLawAtFuel schema job witness.unpair.1 = some law ∧
      ∀ v : PCWorld, v.ConsistentWithTheory DP → v.Holds law := by
  unfold entailedSourceLawEvidenceAt at h
  cases hlaw : semanticSourceCutLawAtFuel schema job witness.unpair.1 with
  | none => simp [hlaw] at h
  | some law =>
      cases hstage : base.stageAtFuel witness.unpair.2.unpair.1
          witness.unpair.2.unpair.2 with
      | none => simp [hlaw, hstage] at h
      | some D =>
          refine ⟨law, rfl, fun v hv => ?_⟩
          have hD : D = DP.D witness.unpair.2.unpair.2 :=
            base.stageAtFuel_sound hstage
          exact (stageEntails_eq_true_iff D law).1 (by simpa [hlaw, hstage] using h)
            v (by simpa [hD] using hv witness.unpair.2.unpair.2)

/-- Any emitted source law which is a completed-base consequence is eventually admitted.
No proof object or source-specific process is supplied to the checker. -/
lemma entailedSourceLawSeen_eventually {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) {schema job : ℕ} {law : Sentence}
    (hemit : ∃ emitterFuel,
      semanticSourceCutLawAtFuel schema job emitterFuel = some law)
    (hsemantic : ∀ v : PCWorld,
      v.ConsistentWithTheory DP → v.Holds law) :
    ∃ fuel, entailedSourceLawSeen base schema job fuel = true := by
  obtain ⟨emitterFuel, hemit⟩ := hemit
  obtain ⟨stage, hentails⟩ :=
    DeductiveProcess.stageEntails_complete_of_semantic DP law hsemantic
  obtain ⟨baseFuel, hstage⟩ := base.stageAtFuel_complete stage
  let witness := Nat.pair emitterFuel (Nat.pair baseFuel stage)
  refine ⟨witness, (entailedSourceLawSeen_iff base schema job witness).2
    ⟨witness, le_rfl, ?_⟩⟩
  simp [entailedSourceLawEvidenceAt, witness, hemit, hstage, hentails]

/-! ## Finite coherent-source prefixes

Exact product consistency uses only freshness and pairwise downward closure.  Bounds are
provided by the `ValuesAt` hypotheses at the point where multiplication is reflected. -/

def entailedSourceDownwardPrefixValidAtFuel {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP)
    (schema limit fuel n zr : ℕ) : Bool :=
  (List.range (limit + 1)).all fun zs =>
    let r := decodedQuotationRat zr
    let s := decodedQuotationRat zs
    if r < s then
      entailedSourceLawSeen base schema (sourceCutDownwardJob n r s) fuel
    else true

def entailedSourceThresholdPrefixValidAtFuel {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP)
    (schema limit fuel n zr : ℕ) : Bool :=
  semanticSourceFreshSeen schema n zr fuel &&
    entailedSourceDownwardPrefixValidAtFuel base schema limit fuel n zr

def entailedSourcePrefixValidAtFuel {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (schema limit fuel : ℕ) : Bool :=
  (List.range (limit + 1)).all fun n =>
    (List.range (limit + 1)).all fun zr =>
      entailedSourceThresholdPrefixValidAtFuel base schema limit fuel n zr

attribute [local irreducible] entailedSourceLawSeen

private lemma entailedListRangeAll_prim { α : Type } [Primcodable α]
    {bound : α → ℕ} {test : α → ℕ → Bool}
    (hbound : Primrec bound) (htest : Primrec₂ test) :
    Primrec fun a => (List.range (bound a + 1)).all (test a) := by
  have hrange : Primrec fun a => List.range (bound a + 1) :=
    Primrec.list_range.comp (Primrec.nat_add.comp hbound (Primrec.const 1))
  have hstep : Primrec₂ fun (a : α) (q : ℕ × Bool) => test a q.1 && q.2 :=
    (Primrec.dom_bool₂ (· && ·)).comp₂
      (htest.comp₂ Primrec₂.left (Primrec.fst.comp₂ Primrec₂.right))
      (Primrec.snd.comp₂ Primrec₂.right)
  exact (Primrec.list_foldr hrange (Primrec.const true) hstep).of_eq fun a => by
    induction List.range (bound a + 1) with
    | nil => rfl
    | cons x xs ih => simp [List.all, ih]

set_option maxHeartbeats 8000000 in
lemma entailedSourceDownwardPrefixValidAtFuel_prim {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) :
    Primrec fun p : ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) =>
      entailedSourceDownwardPrefixValidAtFuel base
        p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2 := by
  let P := ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)
  have hschema : Primrec fun p : P => p.1.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hlimit : Primrec fun p : P => p.1.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hfuel : Primrec fun p : P => p.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hn : Primrec fun p : P => p.1.2 := Primrec.snd.comp Primrec.fst
  have hzr : Primrec fun p : P => p.2 := Primrec.snd
  have hr : Primrec fun p : P => decodedQuotationRat p.2 :=
    decodedQuotationRat_prim.comp hzr
  have htest : Primrec₂ fun (p : P) (zs : ℕ) =>
      if decodedQuotationRat p.2 < decodedQuotationRat zs then
        entailedSourceLawSeen base p.1.1.1.1
          (sourceCutDownwardJob p.1.2 (decodedQuotationRat p.2)
            (decodedQuotationRat zs)) p.1.1.2
      else true := by
    let Q := P × ℕ
    have hs : Primrec fun q : Q => decodedQuotationRat q.2 :=
      decodedQuotationRat_prim.comp Primrec.snd
    have hjob : Primrec fun q : Q => sourceCutDownwardJob q.1.1.2
        (decodedQuotationRat q.1.2) (decodedQuotationRat q.2) := by
      unfold sourceCutDownwardJob
      exact Primrec₂.natPair.comp (Primrec.const 2)
        (Primrec₂.natPair.comp (hn.comp Primrec.fst)
          (Primrec₂.natPair.comp
            (Primrec.encode.comp (hr.comp Primrec.fst))
            (Primrec.encode.comp hs)))
    have hpack : Primrec fun q : Q =>
        ((q.1.1.1.1.1, sourceCutDownwardJob q.1.1.2
          (decodedQuotationRat q.1.2) (decodedQuotationRat q.2)), q.1.1.1.2) :=
      ((hschema.comp Primrec.fst).pair hjob).pair (hfuel.comp Primrec.fst)
    have hseen : Primrec fun q : Q => entailedSourceLawSeen base q.1.1.1.1.1
        (sourceCutDownwardJob q.1.1.2 (decodedQuotationRat q.1.2)
          (decodedQuotationRat q.2)) q.1.1.1.2 :=
      (entailedSourceLawSeen_prim base).comp hpack
    have hlt : PrimrecPred fun q : Q =>
        decodedQuotationRat q.1.2 < decodedQuotationRat q.2 :=
      (ratLE_prim.comp hs (hr.comp Primrec.fst)).not.of_eq fun _ => by simp [not_le]
    exact (Primrec.ite hlt hseen (Primrec.const true)).to₂
  exact entailedListRangeAll_prim hlimit htest

lemma entailedSourceThresholdPrefixValidAtFuel_prim {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) :
    Primrec fun p : ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) =>
      entailedSourceThresholdPrefixValidAtFuel base
        p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2 := by
  let P := ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)
  have hfreshPack : Primrec fun p : P =>
      (((p.1.1.1.1, p.1.2), p.2), p.1.1.2) :=
    (((Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))).pair
      (Primrec.snd.comp Primrec.fst)).pair Primrec.snd).pair
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have hfresh : Primrec fun p : P =>
      semanticSourceFreshSeen p.1.1.1.1 p.1.2 p.2 p.1.1.2 :=
    semanticSourceFreshSeen_prim.comp hfreshPack
  have hdown := entailedSourceDownwardPrefixValidAtFuel_prim base
  exact ((Primrec.dom_bool₂ (· && ·)).comp hfresh hdown).of_eq fun _ => rfl

set_option maxHeartbeats 2000000 in
lemma entailedSourcePrefixValidAtFuel_prim {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) :
    Primrec fun p : (ℕ × ℕ) × ℕ =>
      entailedSourcePrefixValidAtFuel base p.1.1 p.1.2 p.2 := by
  let P := (ℕ × ℕ) × ℕ
  have hlimit : Primrec fun p : P => p.1.2 := Primrec.snd.comp Primrec.fst
  have hinner : Primrec₂ fun (p : P) (n : ℕ) =>
      (List.range (p.1.2 + 1)).all fun zr =>
        entailedSourceThresholdPrefixValidAtFuel base p.1.1 p.1.2 p.2 n zr := by
    let Q := P × ℕ
    have hlimitQ : Primrec fun q : Q => q.1.1.2 := hlimit.comp Primrec.fst
    have htest : Primrec₂ fun (q : Q) (zr : ℕ) =>
        entailedSourceThresholdPrefixValidAtFuel base
          q.1.1.1 q.1.1.2 q.1.2 q.2 zr := by
      have hpack : Primrec fun z : Q × ℕ =>
          ((((z.1.1.1.1, z.1.1.1.2), z.1.1.2), z.1.2), z.2) :=
        (((((Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))).pair
          (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))).pair
          (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair
          (Primrec.snd.comp Primrec.fst)).pair Primrec.snd)
      exact ((entailedSourceThresholdPrefixValidAtFuel_prim base).comp hpack).to₂.of_eq
        fun _ _ => rfl
    exact (entailedListRangeAll_prim hlimitQ htest).to₂
  exact entailedListRangeAll_prim hlimit hinner

lemma entailedSourcePrefixValidAtFuel_fresh {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) {schema limit fuel n z : ℕ}
    (hvalid : entailedSourcePrefixValidAtFuel base schema limit fuel = true)
    (hn : n ≤ limit) (hz : z ≤ limit) :
    semanticSourceFreshSeen schema n z fuel = true := by
  rw [entailedSourcePrefixValidAtFuel, List.all_eq_true] at hvalid
  have h := List.all_eq_true.mp (hvalid n (by simp [hn])) z (by simp [hz])
  rw [entailedSourceThresholdPrefixValidAtFuel] at h
  simp only [Bool.and_eq_true] at h
  exact h.1

lemma entailedSourcePrefixValidAtFuel_downward {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) {schema limit fuel n zr zs : ℕ}
    (hvalid : entailedSourcePrefixValidAtFuel base schema limit fuel = true)
    (hn : n ≤ limit) (hzr : zr ≤ limit) (hzs : zs ≤ limit)
    (hrs : decodedQuotationRat zr < decodedQuotationRat zs) :
    entailedSourceLawSeen base schema
      (sourceCutDownwardJob n (decodedQuotationRat zr) (decodedQuotationRat zs)) fuel = true := by
  rw [entailedSourcePrefixValidAtFuel, List.all_eq_true] at hvalid
  have h := List.all_eq_true.mp (hvalid n (by simp [hn])) zr (by simp [hzr])
  rw [entailedSourceThresholdPrefixValidAtFuel] at h
  simp only [Bool.and_eq_true] at h
  have hdown := h.2
  rw [entailedSourceDownwardPrefixValidAtFuel, List.all_eq_true] at hdown
  simpa [hrs] using hdown zs (by simp [hzs])

lemma entailedSourceDownwardPrefixValidAtFuel_mono {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP)
    {schema limit n zr fuel fuel' : ℕ} (hff : fuel ≤ fuel')
    (h : entailedSourceDownwardPrefixValidAtFuel base schema limit fuel n zr = true) :
    entailedSourceDownwardPrefixValidAtFuel base schema limit fuel' n zr = true := by
  rw [entailedSourceDownwardPrefixValidAtFuel, List.all_eq_true] at h ⊢
  intro zs hzs
  by_cases hrs : decodedQuotationRat zr < decodedQuotationRat zs
  · simpa [hrs] using entailedSourceLawSeen_mono base hff (by simpa [hrs] using h zs hzs)
  · simp [hrs]

lemma entailedSourceThresholdPrefixValidAtFuel_mono {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP)
    {schema limit n zr fuel fuel' : ℕ} (hff : fuel ≤ fuel')
    (h : entailedSourceThresholdPrefixValidAtFuel base schema limit fuel n zr = true) :
    entailedSourceThresholdPrefixValidAtFuel base schema limit fuel' n zr = true := by
  rw [entailedSourceThresholdPrefixValidAtFuel] at h ⊢
  simp only [Bool.and_eq_true] at h ⊢
  exact ⟨semanticSourceFreshSeen_mono hff h.1,
    entailedSourceDownwardPrefixValidAtFuel_mono base hff h.2⟩

lemma entailedSourcePrefixValidAtFuel_mono {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP)
    {schema limit fuel fuel' : ℕ} (hff : fuel ≤ fuel')
    (h : entailedSourcePrefixValidAtFuel base schema limit fuel = true) :
    entailedSourcePrefixValidAtFuel base schema limit fuel' = true := by
  rw [entailedSourcePrefixValidAtFuel, List.all_eq_true] at h ⊢
  intro n hn
  rw [List.all_eq_true]
  intro zr hzr
  exact entailedSourceThresholdPrefixValidAtFuel_mono base hff
    (List.all_eq_true.mp (h n hn) zr hzr)

/-- Entailment-gated downward evidence is sound in the canonical source extension. -/
lemma semanticSourceExtensionWorld_downward_of_entailedSeen {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (v₀ : PCWorld)
    (hv₀ : v₀.ConsistentWithTheory DP) {schema n fuel : ℕ} {r s : ℚ}
    (hsource : schema.unpair.1 = 0) (hrs : r < s)
    (hseen : entailedSourceLawSeen base schema
      (sourceCutDownwardJob n r s) fuel = true) :
    (semanticSourceExtensionWorld v₀).Holds
      (semanticPrimeSentence schema (Nat.pair n (Encodable.encode s))) →
    (semanticSourceExtensionWorld v₀).Holds
      (semanticPrimeSentence schema (Nat.pair n (Encodable.encode r))) := by
  obtain ⟨witness, _, hevidence⟩ :=
    (entailedSourceLawSeen_iff base schema (sourceCutDownwardJob n r s) fuel).1 hseen
  obtain ⟨law, hlaw, hsemantic⟩ := entailedSourceLawEvidenceAt_sound base hevidence
  obtain ⟨φr, φs, hφr, hφs, hfr, hfs, rfl⟩ :=
    semanticSourceCutLawAtFuel_downward_spec hrs hlaw
  have himp : v₀.Holds (φs 🡒 φr) := hsemantic v₀ hv₀
  intro hs
  have hs₀ : v₀.Holds φs :=
    (semanticSourceExtensionWorld_leaf_iff v₀ schema _ witness.unpair.1
      hsource hφs hfs).mp hs
  exact (semanticSourceExtensionWorld_leaf_iff v₀ schema _ witness.unpair.1
    hsource hφr hfr).mpr (himp hs₀)

private lemma entailedListAll_eventually_of_mono {l : List ℕ}
    {test : ℕ → ℕ → Bool}
    (hmono : ∀ x {fuel fuel'}, fuel ≤ fuel' → test x fuel = true →
      test x fuel' = true)
    (heventual : ∀ x ∈ l, ∃ fuel, test x fuel = true) :
    ∃ fuel, l.all (fun x => test x fuel) = true := by
  induction l with
  | nil => exact ⟨0, rfl⟩
  | cons x xs ih =>
      obtain ⟨fx, hfx⟩ := heventual x (by simp)
      obtain ⟨fs, hfs⟩ := ih (fun y hy => heventual y (by simp [hy]))
      refine ⟨max fx fs, ?_⟩
      rw [List.all_cons, Bool.and_eq_true]
      exact ⟨hmono x (Nat.le_max_left _ _) hfx, by
        rw [List.all_eq_true] at hfs ⊢
        intro y hy
        exact hmono y (Nat.le_max_right _ _) (hfs y hy)⟩

/-- Pointwise eventual threshold admission combines into one finite-prefix clock. -/
lemma entailedSourcePrefix_eventually_of_threshold
    {DP : DeductiveProcess} (base : DeductiveProcessComputation DP)
    (schema limit : ℕ)
    (heventual : ∀ n zr, ∃ fuel,
      entailedSourceThresholdPrefixValidAtFuel base schema limit fuel n zr = true) :
    ∃ fuel, entailedSourcePrefixValidAtFuel base schema limit fuel = true := by
  let row : ℕ → ℕ → Bool := fun n fuel =>
    (List.range (limit + 1)).all fun zr =>
      entailedSourceThresholdPrefixValidAtFuel base schema limit fuel n zr
  have rowMono : ∀ n {fuel fuel'}, fuel ≤ fuel' → row n fuel = true →
      row n fuel' = true := by
    intro n fuel fuel' hff h
    change (List.range (limit + 1)).all (fun zr =>
      entailedSourceThresholdPrefixValidAtFuel base schema limit fuel n zr) = true at h
    change (List.range (limit + 1)).all (fun zr =>
      entailedSourceThresholdPrefixValidAtFuel base schema limit fuel' n zr) = true
    rw [List.all_eq_true] at h ⊢
    intro zr hzr
    exact entailedSourceThresholdPrefixValidAtFuel_mono base hff (h zr hzr)
  have rowEventually : ∀ n ∈ List.range (limit + 1),
      ∃ fuel, row n fuel = true := by
    intro n _
    exact entailedListAll_eventually_of_mono
      (l := List.range (limit + 1))
      (fun zr _ _ hff h => entailedSourceThresholdPrefixValidAtFuel_mono base hff h)
      (fun zr _ => heventual n zr)
  obtain ⟨fuel, hfuel⟩ := entailedListAll_eventually_of_mono rowMono rowEventually
  refine ⟨fuel, ?_⟩
  rw [entailedSourcePrefixValidAtFuel, List.all_eq_true]
  exact List.all_eq_true.mp hfuel

#print axioms entailedSourceLawEvidenceAt_prim
#print axioms entailedSourceLawEvidenceAt_sound
#print axioms entailedSourceLawSeen_eventually

end LogicalInduction
