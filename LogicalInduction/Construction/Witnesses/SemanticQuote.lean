import LogicalInduction.Construction.Witnesses.SemanticPrime
import LogicalInduction.Construction.Witnesses.ComputationDP

/-!
# Fixed quote leaves for semantic-prime syntax

A quote leaf `semanticQuoteSchema code` names the already-existing quotation selector
`code`.  Generic emitted-source programs use the disjoint `semanticEmitterSchema`
namespace.  This is deliberately not a general first-order bridge: it is a fixed syntactic
definitional closure between two public names for the same universal quotation instance.
-/

namespace LogicalInduction

open LO LO.Propositional LO.FirstOrder LO.FirstOrder.Arithmetic

def semanticQuoteLeaf (code input : ℕ) : Sentence :=
  semanticPrimeSentence (semanticQuoteSchema code) input

/-- The existing universal quotation atom is uniformly computable as a sentence-valued
function; this is the reusable emitter core for the fixed quote-leaf process. -/
lemma quoteAtom_computable : Computable quoteAtom := by
  obtain ⟨c, hc⟩ := quotationClaimSentence_poly universalQuotePos universalQuoteNeg
    ⟨_, PolyFueled.id⟩
  exact Computable.encode_iff.mpr (hc.primrec.of_eq (fun n => by rfl)).to_comp

noncomputable def semanticQuoteDefSentence (e : ℕ) : Sentence :=
  if e.unpair.1 = 0 then
    quoteAtom (Nat.pair e.unpair.2.unpair.1 e.unpair.2.unpair.2) 🡒
      semanticQuoteLeaf e.unpair.2.unpair.1 e.unpair.2.unpair.2
  else
    semanticQuoteLeaf e.unpair.2.unpair.1 e.unpair.2.unpair.2 🡒
      quoteAtom (Nat.pair e.unpair.2.unpair.1 e.unpair.2.unpair.2)

noncomputable def semanticQuoteStageList : ℕ → List Sentence
  | 0 => [semanticQuoteDefSentence 0]
  | n + 1 => semanticQuoteDefSentence (n + 1) :: semanticQuoteStageList n

lemma mem_semanticQuoteStageList {e n : ℕ} (h : e ≤ n) :
    semanticQuoteDefSentence e ∈ semanticQuoteStageList n := by
  induction n with
  | zero => simp [semanticQuoteStageList, Nat.le_zero.mp h]
  | succ n ih =>
      rcases Nat.lt_or_ge e (n + 1) with hlt | hge
      · exact List.mem_cons_of_mem _ (ih (Nat.lt_succ_iff.mp hlt))
      · have he : e = n + 1 := le_antisymm h hge
        simp [semanticQuoteStageList, he]

/-- Fixed before any particular quote selector is chosen. -/
noncomputable def semanticQuoteDP : DeductiveProcess where
  D n := (semanticQuoteStageList n).toFinset
  mono n := by
    intro φ h
    simp only [List.mem_toFinset] at h ⊢
    exact List.mem_cons_of_mem _ h

set_option maxHeartbeats 2000000 in
private lemma semanticQuoteLeafJob_encode_computable : Computable fun e : ℕ =>
    Encodable.encode (semanticQuoteLeaf e.unpair.2.unpair.1 e.unpair.2.unpair.2) := by
  have hcode : Computable fun e : ℕ => e.unpair.2.unpair.1 :=
    (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))).to_comp
  have hinput : Computable fun e : ℕ => e.unpair.2.unpair.2 :=
    (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))).to_comp
  have hschema : Computable fun e : ℕ => semanticQuoteSchema e.unpair.2.unpair.1 :=
    (Primrec₂.natPair.comp (Primrec.const 2)
      (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))).to_comp
      |>.of_eq (fun _ => rfl)
  exact (Computable.succ.comp (Computable₂.comp Primrec₂.natPair.to_comp
    (Computable.const 1) (Computable₂.comp Primrec₂.natPair.to_comp
      (Computable.const semanticPrimeTag) (Computable₂.comp Primrec₂.natPair.to_comp
        hschema hinput)))).of_eq (fun _ => rfl)

private lemma semanticQuoteAtomJob_encode_computable : Computable fun e : ℕ =>
    Encodable.encode (quoteAtom
      (Nat.pair e.unpair.2.unpair.1 e.unpair.2.unpair.2)) := by
  have hcode : Computable fun e : ℕ => e.unpair.2.unpair.1 :=
    (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))).to_comp
  have hinput : Computable fun e : ℕ => e.unpair.2.unpair.2 :=
    (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))).to_comp
  have hpair : Computable fun e : ℕ => Nat.pair e.unpair.2.unpair.1 e.unpair.2.unpair.2 :=
    Computable₂.comp Primrec₂.natPair.to_comp hcode hinput
  exact Computable.encode.comp (quoteAtom_computable.comp hpair)

private lemma semanticQuoteImpJob_encode_computable : Computable fun p : ℕ × ℕ =>
    Nat.succ (Nat.pair 2 (Nat.pair p.1 p.2)) :=
  Computable.succ.comp (Computable₂.comp Primrec₂.natPair.to_comp (Computable.const 2)
    (Computable₂.comp Primrec₂.natPair.to_comp Computable.fst Computable.snd))

set_option maxHeartbeats 1000000 in
/-- The narrow quotation closure is computably enumerable.  In particular, it does not
need an oracle for a market or for the source LUV eventually represented by a leaf. -/
lemma semanticQuoteDefSentence_computable : Computable semanticQuoteDefSentence := by
  classical
  refine Computable.encode_iff.mp ?_
  have hfraw := semanticQuoteImpJob_encode_computable.comp
      (semanticQuoteAtomJob_encode_computable.pair semanticQuoteLeafJob_encode_computable)
  have hforward : Computable fun e : ℕ => Encodable.encode
      (quoteAtom (Nat.pair e.unpair.2.unpair.1 e.unpair.2.unpair.2) 🡒
        semanticQuoteLeaf e.unpair.2.unpair.1 e.unpair.2.unpair.2) :=
    hfraw.of_eq (fun _ => rfl)
  have hbraw := semanticQuoteImpJob_encode_computable.comp
      (semanticQuoteLeafJob_encode_computable.pair semanticQuoteAtomJob_encode_computable)
  have hbackward : Computable fun e : ℕ => Encodable.encode
      (semanticQuoteLeaf e.unpair.2.unpair.1 e.unpair.2.unpair.2 🡒
        quoteAtom (Nat.pair e.unpair.2.unpair.1 e.unpair.2.unpair.2)) :=
    hbraw.of_eq (fun _ => rfl)
  have hzero : Computable fun e : ℕ => decide (e.unpair.1 = 0) :=
    (Primrec.eq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 0)).decide.to_comp
  exact (Computable.cond hzero hforward hbackward).of_eq (fun e => by
      rw [semanticQuoteDefSentence]
      split_ifs <;> simp_all)

lemma semanticQuoteDP_computable : ComputableDeductiveProcess semanticQuoteDP := by
  have hlist : Computable semanticQuoteStageList := by
    have hstep : Computable fun p : ℕ × List Sentence =>
        semanticQuoteDefSentence (p.1 + 1) :: p.2 :=
      Computable.list_cons.comp
        (semanticQuoteDefSentence_computable.comp (Primrec.succ.to_comp.comp Computable.fst))
        Computable.snd
    refine (Computable.nat_rec Computable.id
      (Computable.const [semanticQuoteDefSentence 0])
      (hstep.comp₂ Computable.snd.to₂)).of_eq (fun k => ?_)
    induction k with
    | zero => rfl
    | succ k ih => simpa [semanticQuoteStageList] using ih
  have hkey : Computable fun k => Encodable.encode
      ((sentenceDedup (semanticQuoteStageList k)).insertionSort sentenceCodeLE) :=
    Computable.encode.comp
      ((sentenceInsertionSort_prim.comp sentenceDedup_prim).to_comp.comp hlist)
  obtain ⟨code, hcode⟩ := Nat.Partrec.Code.exists_code.mp
    (Partrec.nat_iff.mp hkey)
  refine ⟨code, fun k => ?_⟩
  rw [hcode]
  exact Part.mem_some_iff.mpr (encode_toFinset_eq (semanticQuoteStageList k))

/-- Canonical theorem/quotation base, fixed from the arithmetic theory alone.  It lives
here so all downstream source and product registries share one quotation namespace. -/
noncomputable def theoremQuoteBaseDP
    (T : ArithmeticTheory) [T.Δ₁] [ISigma 1 ⪯ T] : DeductiveProcess :=
  (theoremDP T).union semanticQuoteDP

noncomputable def theoremQuoteBaseDPComputation
    (T : ArithmeticTheory) [T.Δ₁] [ISigma 1 ⪯ T] :
    DeductiveProcessComputation (theoremQuoteBaseDP T) :=
  ((theoremDP_computable T).nonemptyComputation.some).union
    semanticQuoteDP_computable.nonemptyComputation.some

lemma holds_semanticQuoteDefSentence {v : PCWorld}
    (hv : v.ConsistentWithTheory semanticQuoteDP) (e : ℕ) :
    v.Holds (semanticQuoteDefSentence e) :=
  hv e _ (List.mem_toFinset.mpr (mem_semanticQuoteStageList (le_refl e)))

section
attribute [local irreducible] Nat.sqrt

lemma semanticQuoteDefSentence_job (kind code input : ℕ) :
    semanticQuoteDefSentence (Nat.pair kind (Nat.pair code input)) =
      (if kind = 0 then quoteAtom (Nat.pair code input) 🡒 semanticQuoteLeaf code input
        else semanticQuoteLeaf code input 🡒 quoteAtom (Nat.pair code input)) := by
  simp [semanticQuoteDefSentence]

/-- Completed worlds identify a quote leaf with its quotation atom. -/
lemma semanticQuoteLeaf_reflected {v : PCWorld}
    (hv : v.ConsistentWithTheory semanticQuoteDP) (code input : ℕ) :
    v.Holds (semanticQuoteLeaf code input) ↔ v.Holds (quoteAtom (Nat.pair code input)) := by
  constructor
  · have h := holds_semanticQuoteDefSentence hv (Nat.pair 1 (Nat.pair code input))
    rw [semanticQuoteDefSentence_job] at h
    exact h
  · have h := holds_semanticQuoteDefSentence hv (Nat.pair 0 (Nat.pair code input))
    rw [semanticQuoteDefSentence_job] at h
    exact h

end

end LogicalInduction
