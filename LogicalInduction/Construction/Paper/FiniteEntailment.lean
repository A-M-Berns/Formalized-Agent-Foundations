import LogicalInduction.Construction.LIACompiler
import LogicalInduction.Framework.Compactness

/-!
# Executable finite-stage propositional entailment

The semantic compactness theorem supplies a finite stage which forces any completed-theory
consequence.  This file makes that finite check executable by enumerating the Boolean
assignments to exactly the atoms occurring in the stage and target sentence.

`stageEntails` is the decision procedure, `stageEntails_eq_true_iff` its semantic
characterization, `stageEntails_primrec` its primitive recursivity, and
`DeductiveProcess.stageEntails_complete_of_semantic` the compactness bridge: a sentence
holding in every completed-theory world is entailed by some finite stage, executably.
Nothing here is a paper node.

Consumers: `Construction/SemanticExtension/LanguageCopy.lean`, whose admission gate accepts
exactly when
`stageEntails` verifies that the decoded base stage entails the emitted law, and
`Freeze/Counterexample.lean`, whose day-`0` settlement search is `Nat.find` over the
Boolean test `stageEntails` decides.
-/

namespace LogicalInduction

open LO LO.Propositional

/-- The atoms needed to decide whether a finite stage entails one sentence. -/
def stageEntailmentAtoms (D : Finset Sentence) (phi : Sentence) : List ℕ :=
  sentenceListAtoms (phi :: supportSentenceList D)

/-- Finite propositional entailment, computed by exhaustive Boolean evaluation. -/
def stageEntails (D : Finset Sentence) (phi : Sentence) : Bool :=
  let atoms := stageEntailmentAtoms D phi
  (allBoolLists atoms.length).all fun xs =>
    !(tableConsistent (atomTableFromList atoms xs) D) ||
      sentenceBool (atomTableFromList atoms xs) phi

private noncomputable def worldBool (v : PCWorld) (a : ℕ) : Bool :=
  by
    classical
    exact if v a then true else false

private lemma atomTableFromList_map_worldBool (atoms : List ℕ) (v : PCWorld)
    {a : ℕ} (ha : a ∈ atoms) :
    atomTableFromList atoms (atoms.map (worldBool v)) a = worldBool v a := by
  rw [atomTableFromList_apply, if_pos ha]
  have hidx : atoms.idxOf a < atoms.length := List.idxOf_lt_length_of_mem ha
  rw [List.getD_eq_getElem _ _ (by simpa using hidx)]
  simp only [List.getElem_map]
  rw [List.getElem_idxOf hidx]

private lemma sentenceBool_atomTableFromList_map_worldBool
    (atoms : List ℕ) (v : PCWorld) (phi : Sentence)
    (hphi : ∀ a ∈ phi.atoms, a ∈ atoms) :
    sentenceBool (atomTableFromList atoms (atoms.map (worldBool v))) phi = true ↔
      v.Holds phi := by
  classical
  have heq := sentenceBool_congr_of_atoms
    (u := atomTableFromList atoms (atoms.map (worldBool v)))
    (v := fun a => decide (v a)) (φ := phi)
    (fun a ha => by simpa [worldBool] using
      atomTableFromList_map_worldBool atoms v (hphi a ha))
  rw [heq]
  exact sentenceBool_decide_world v phi

private lemma target_atoms_mem (D : Finset Sentence) (phi : Sentence) {a : ℕ}
    (ha : a ∈ phi.atoms) : a ∈ stageEntailmentAtoms D phi := by
  rw [stageEntailmentAtoms, mem_sentenceListAtoms]
  exact ⟨phi, by simp, ha⟩

private lemma stage_atoms_mem (D : Finset Sentence) (phi psi : Sentence)
    (hpsi : psi ∈ D) {a : ℕ} (ha : a ∈ psi.atoms) :
    a ∈ stageEntailmentAtoms D phi := by
  rw [stageEntailmentAtoms, mem_sentenceListAtoms]
  exact ⟨psi, by simp [supportSentenceList, hpsi], ha⟩

/-- The Boolean checker is exactly semantic entailment over p.c. worlds. -/
lemma stageEntails_eq_true_iff (D : Finset Sentence) (phi : Sentence) :
    stageEntails D phi = true ↔
      ∀ v : PCWorld, v.ConsistentWith D → v.Holds phi := by
  classical
  let atoms := stageEntailmentAtoms D phi
  rw [stageEntails, List.all_eq_true]
  constructor
  · intro h v hv
    let xs := atoms.map (worldBool v)
    have hxs : xs ∈ allBoolLists atoms.length := by
      rw [mem_allBoolLists_iff]
      simp [xs]
    have hall := h xs hxs
    have hconsistent :
        tableConsistent (atomTableFromList atoms xs) D = true := by
      rw [tableConsistent_eq_true_iff]
      intro psi hpsi
      apply (sentenceBool_eq_true_iff _ psi).mp
      exact (sentenceBool_atomTableFromList_map_worldBool atoms v psi
        (fun a ha => stage_atoms_mem D phi psi hpsi ha)).2 (hv psi hpsi)
    rw [hconsistent] at hall
    simp only [Bool.not_true, Bool.false_or] at hall
    exact (sentenceBool_atomTableFromList_map_worldBool atoms v phi
      (fun a ha => target_atoms_mem D phi ha)).1 hall
  · intro h xs hxs
    by_cases hconsistent :
        tableConsistent (atomTableFromList atoms xs) D = true
    · rw [hconsistent]
      simp only [Bool.not_true, Bool.false_or]
      apply (sentenceBool_eq_true_iff _ phi).2
      exact h (boolPCWorld (atomTableFromList atoms xs))
        ((tableConsistent_eq_true_iff _ D).1 hconsistent)
    · cases hc : tableConsistent (atomTableFromList atoms xs) D
      · simp
      · exact (hconsistent hc).elim

/-- The finite entailment checker is primitive recursive in the stage and sentence. -/
lemma stageEntails_primrec :
    Primrec fun p : Finset Sentence × Sentence => stageEntails p.1 p.2 := by
  let P := Finset Sentence × Sentence
  have hsentences : Primrec fun p : P => p.2 :: supportSentenceList p.1 :=
    Primrec.list_cons.comp Primrec.snd (supportSentenceList_primrec.comp Primrec.fst)
  have hatoms : Primrec fun p : P => stageEntailmentAtoms p.1 p.2 :=
    (sentenceListAtoms_primrec.comp hsentences).of_eq fun _ => rfl
  have hassignments : Primrec fun p : P =>
      allBoolLists (stageEntailmentAtoms p.1 p.2).length :=
    allBoolLists_primrec.comp (Primrec.list_length.comp hatoms)
  have htest : Primrec₂ fun (p : P) (xs : List Bool) =>
      !(tableConsistent
          (atomTableFromList (stageEntailmentAtoms p.1 p.2) xs) p.1) ||
        sentenceBool
          (atomTableFromList (stageEntailmentAtoms p.1 p.2) xs) p.2 := by
    let Q := P × List Bool
    have hconsistent : Primrec fun q : Q =>
        tableConsistent
          (atomTableFromList (stageEntailmentAtoms q.1.1 q.1.2) q.2) q.1.1 :=
      tableConsistent_atomTableFromList_primrec.comp
        (((hatoms.comp Primrec.fst).pair Primrec.snd).pair
          (Primrec.fst.comp Primrec.fst))
    have hsentence : Primrec fun q : Q =>
        sentenceBool
          (atomTableFromList (stageEntailmentAtoms q.1.1 q.1.2) q.2) q.1.2 :=
      sentenceBool_atomTableFromList_primrec.comp
        (((hatoms.comp Primrec.fst).pair Primrec.snd).pair
          (Primrec.snd.comp Primrec.fst))
    have hnot : Primrec fun q : Q => !(tableConsistent
        (atomTableFromList (stageEntailmentAtoms q.1.1 q.1.2) q.2) q.1.1) :=
      (Primrec.dom_bool Bool.not).comp hconsistent
    exact ((Primrec.dom_bool₂ (· || ·)).comp hnot hsentence).to₂.of_eq fun _ _ => rfl
  have hstep : Primrec₂ fun (p : P) (q : List Bool × Bool) =>
      (!(tableConsistent
          (atomTableFromList (stageEntailmentAtoms p.1 p.2) q.1) p.1) ||
        sentenceBool
          (atomTableFromList (stageEntailmentAtoms p.1 p.2) q.1) p.2) && q.2 :=
    (Primrec.dom_bool₂ (· && ·)).comp₂
      (htest.comp₂ Primrec₂.left (Primrec.fst.comp₂ Primrec₂.right))
      (Primrec.snd.comp₂ Primrec₂.right)
  exact (Primrec.list_foldr hassignments (Primrec.const true) hstep).of_eq fun p => by
    simp only [stageEntails]
    induction allBoolLists (stageEntailmentAtoms p.1 p.2).length with
    | nil => rfl
    | cons x xs ih => simp [List.all, ih]

/-- Every completed-theory semantic consequence is eventually accepted by the executable
finite-stage checker. -/
lemma DeductiveProcess.stageEntails_complete_of_semantic
    (DP : DeductiveProcess) (phi : Sentence)
    (h : ∀ v : PCWorld, v.ConsistentWithTheory DP → v.Holds phi) :
    ∃ k, stageEntails (DP.D k) phi = true := by
  obtain ⟨k, hk⟩ := DP.exists_stage_entails phi h
  exact ⟨k, (stageEntails_eq_true_iff (DP.D k) phi).2 hk⟩

end LogicalInduction
