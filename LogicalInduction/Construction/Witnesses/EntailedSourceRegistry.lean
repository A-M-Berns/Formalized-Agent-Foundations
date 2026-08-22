import LogicalInduction.Construction.Witnesses.OldLanguageLift
import LogicalInduction.Construction.Witnesses.SemanticSourceRegistry

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

#print axioms entailedSourceLawEvidenceAt_prim
#print axioms entailedSourceLawEvidenceAt_sound
#print axioms entailedSourceLawSeen_eventually

end LogicalInduction
