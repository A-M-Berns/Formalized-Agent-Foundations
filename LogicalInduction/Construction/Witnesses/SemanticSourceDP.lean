import LogicalInduction.Construction.Witnesses.SemanticSourceRegistry

/-!
# Fixed universal semantic-source interpretation

The single fixed universal source process — construction machinery for `thm:ccee`
(tex:2068) at an arbitrary e.c. source family.

Objects defined: `semanticSourceDefinitionJob`, `semanticSourceDefSentence` (one bounded
definition clause), `semanticSourceStageList`, `semanticSourceDP`, and the canonical
extension world `semanticSourceExtensionWorld`.

Main results: `semanticSourceDP_computable`; `semanticSourceDP_hworld`, which exhibits an
explicit completed world over *every* base world, so no consistency premise hides in source
reflection; `semanticSourceSentenceAtFuel_reflected`; and the two transport lemmas
`certifiedSource_threshold_reflected` and `certifiedSource_valuesAt_iff`.  They are consumed
by `SemanticRegistryProduct.lean`, `EntailedSourceRegistry.lean`, `PaperCutLawDP.lean` and
`LiftedRpnSource.lean`.

The separation of concerns the process rests on: it is a conservative definitional
interpreter for old-language emitter output, and nothing more — the executable cut
certificate that guards exact-product activation lives in `SemanticRegistryProduct.lean`.

Malformed but fresh emitters cannot make the process inconsistent, because every activated
tag-`0` leaf is merely identified with one old-language sentence, and
`semanticSourceSentenceAtFuel_unique` shows bounded runs of one named emitter cannot decode
to two.  The process is fixed universally over program codes and inputs, before any source
family is selected; all failures decode to the inert `⊤`.

`semanticSourceExtensionWorld_consistentWith_union` combines the process conservatively with
any base process whose stages stay in the old language, and `theoremSemanticSourceDP` is the
canonical `T`-only instance of that union.  That instance, its program and its completed
world are offered to clients as a named package; no endpoint prices against them, for the
same reason `PaperCutLawDP.paperBaseDP` is not consumed — unioning the lane into the endpoint
files would pull the semantic-source lane into each of them.
-/

namespace LogicalInduction

open LO LO.Propositional LO.FirstOrder LO.FirstOrder.Arithmetic

attribute [local irreducible] Nat.sqrt

/-! ## The universal definition clauses -/

/-- A universal source-definition job packs schema, input, direction, and bounded fuel. -/
def semanticSourceDefinitionJob (schema input direction fuel : ℕ) : ℕ :=
  Nat.pair schema (Nat.pair input (Nat.pair direction fuel))

/-- One bounded source-definition clause.  All failures are harmless tautologies. -/
def semanticSourceDefSentence (e : ℕ) : Sentence :=
  let schema := e.unpair.1
  let input := e.unpair.2.unpair.1
  let direction := e.unpair.2.unpair.2.unpair.1
  let fuel := e.unpair.2.unpair.2.unpair.2
  if schema.unpair.1 = 0 then
    match semanticSourceSentenceAtFuel schema input fuel with
    | some φ =>
        if semanticPrimeFreshSentenceB φ then
          if direction = 0 then φ 🡒 semanticPrimeSentence schema input
          else semanticPrimeSentence schema input 🡒 φ
        else ⊤
    | none => ⊤
  else ⊤

/-- Stage `k` as a list: every definition clause with index at most `k`, newest first. -/
def semanticSourceStageList : ℕ → List Sentence
  | 0 => [semanticSourceDefSentence 0]
  | k + 1 => semanticSourceDefSentence (k + 1) :: semanticSourceStageList k

lemma mem_semanticSourceStageList {e k : ℕ} (h : e ≤ k) :
    semanticSourceDefSentence e ∈ semanticSourceStageList k := by
  induction k with
  | zero => simp [semanticSourceStageList, Nat.le_zero.mp h]
  | succ k ih =>
      rcases Nat.lt_or_ge e (k + 1) with hlt | hge
      · exact List.mem_cons_of_mem _ (ih (Nat.lt_succ_iff.mp hlt))
      · have he : e = k + 1 := le_antisymm h hge
        simp [semanticSourceStageList, he]

lemma semanticSourceStageList_exists {φ : Sentence} {k : ℕ}
    (h : φ ∈ semanticSourceStageList k) :
    ∃ e, φ = semanticSourceDefSentence e := by
  induction k with
  | zero => exact ⟨0, by simpa [semanticSourceStageList] using h⟩
  | succ k ih =>
      rcases List.mem_cons.mp h with h | h
      · exact ⟨k + 1, h⟩
      · exact ih h

/-! ## The process, and its program -/

/-- The single universal source process.  It contains no chosen source, market, weight,
or deferral data. -/
def semanticSourceDP : DeductiveProcess where
  D k := (semanticSourceStageList k).toFinset
  mono k := by
    intro φ hφ
    simp only [List.mem_toFinset] at hφ ⊢
    exact List.mem_cons_of_mem _ hφ

private lemma semanticSourceImp_prim : Primrec₂ fun φ ψ : Sentence => φ 🡒 ψ := by
  apply Primrec₂.encode_iff.mp
  exact (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 2)
    (Primrec₂.natPair.comp
      (Primrec.encode.comp Primrec.fst)
      (Primrec.encode.comp Primrec.snd)))).to₂.of_eq fun _ _ => rfl

lemma semanticSourceDefSentence_prim : Primrec semanticSourceDefSentence := by
  have hschema : Primrec fun e : ℕ => e.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hrest : Primrec fun e : ℕ => e.unpair.2 := Primrec.snd.comp Primrec.unpair
  have hinput : Primrec fun e : ℕ => e.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp hrest)
  have htail : Primrec fun e : ℕ => e.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp hrest)
  have hdirection : Primrec fun e : ℕ => e.unpair.2.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp htail)
  have hfuel : Primrec fun e : ℕ => e.unpair.2.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp htail)
  have hsentence : Primrec fun e : ℕ =>
      semanticSourceSentenceAtFuel e.unpair.1 e.unpair.2.unpair.1
        e.unpair.2.unpair.2.unpair.2 :=
    semanticSourceSentenceAtFuel_prim.comp ((hschema.pair hinput).pair hfuel)
  have hleaf : Primrec fun e : ℕ =>
      semanticPrimeSentence e.unpair.1 e.unpair.2.unpair.1 := by
    apply Primrec.encode_iff.mp
    exact semanticPrimeSentence_encode_prim.comp (hschema.pair hinput)
  have hsome : Primrec₂ fun (e : ℕ) (φ : Sentence) =>
      if semanticPrimeFreshSentenceB φ then
        if e.unpair.2.unpair.2.unpair.1 = 0 then
          φ 🡒 semanticPrimeSentence e.unpair.1 e.unpair.2.unpair.1
        else semanticPrimeSentence e.unpair.1 e.unpair.2.unpair.1 🡒 φ
      else ⊤ := by
    let Q := ℕ × Sentence
    have hfresh : PrimrecPred fun q : Q => semanticPrimeFreshSentenceB q.2 = true :=
      Primrec.eq.comp (semanticPrimeFreshSentenceB_prim.comp Primrec.snd)
        (Primrec.const true)
    have hdir : PrimrecPred fun q : Q => q.1.unpair.2.unpair.2.unpair.1 = 0 :=
      Primrec.eq.comp (hdirection.comp Primrec.fst) (Primrec.const 0)
    have hleafQ : Primrec fun q : Q =>
        semanticPrimeSentence q.1.unpair.1 q.1.unpair.2.unpair.1 :=
      hleaf.comp Primrec.fst
    have hforward : Primrec fun q : Q =>
        q.2 🡒 semanticPrimeSentence q.1.unpair.1 q.1.unpair.2.unpair.1 :=
      semanticSourceImp_prim.comp Primrec.snd hleafQ
    have hbackward : Primrec fun q : Q =>
        semanticPrimeSentence q.1.unpair.1 q.1.unpair.2.unpair.1 🡒 q.2 :=
      semanticSourceImp_prim.comp hleafQ Primrec.snd
    exact (Primrec.ite hfresh (Primrec.ite hdir hforward hbackward)
      (Primrec.const (⊤ : Sentence))).to₂.of_eq fun _ _ => rfl
  have hdecoded : Primrec fun e : ℕ =>
      match semanticSourceSentenceAtFuel e.unpair.1 e.unpair.2.unpair.1
          e.unpair.2.unpair.2.unpair.2 with
      | some φ =>
          if semanticPrimeFreshSentenceB φ then
            if e.unpair.2.unpair.2.unpair.1 = 0 then
              φ 🡒 semanticPrimeSentence e.unpair.1 e.unpair.2.unpair.1
            else semanticPrimeSentence e.unpair.1 e.unpair.2.unpair.1 🡒 φ
          else ⊤
      | none => ⊤ :=
    (Primrec.option_casesOn hsentence (Primrec.const (⊤ : Sentence)) hsome).of_eq
      fun e => by
        cases h : (semanticSourceSentenceAtFuel e.unpair.1
          e.unpair.2.unpair.1 e.unpair.2.unpair.2.unpair.2) <;> simp
  have hsource : PrimrecPred fun e : ℕ => e.unpair.1.unpair.1 = 0 :=
    Primrec.eq.comp (Primrec.fst.comp (Primrec.unpair.comp hschema))
      (Primrec.const 0)
  exact (Primrec.ite hsource hdecoded (Primrec.const (⊤ : Sentence))).of_eq
    fun e => by simp [semanticSourceDefSentence]

/-- The universal source interpreter is a computable deductive process. -/
lemma semanticSourceDP_computable : ComputableDeductiveProcess semanticSourceDP := by
  have hlist : Computable semanticSourceStageList := by
    have hstep : Computable fun p : ℕ × List Sentence =>
        semanticSourceDefSentence (p.1 + 1) :: p.2 :=
      Computable.list_cons.comp
        (semanticSourceDefSentence_prim.to_comp.comp
          (Primrec.succ.to_comp.comp Computable.fst)) Computable.snd
    refine (Computable.nat_rec Computable.id
      (Computable.const [semanticSourceDefSentence 0])
      (hstep.comp₂ Computable.snd.to₂)).of_eq (fun k => ?_)
    induction k with
    | zero => rfl
    | succ k ih => simpa [semanticSourceStageList] using ih
  have hkey : Computable fun k => Encodable.encode
      ((sentenceDedup (semanticSourceStageList k)).insertionSort sentenceCodeLE) :=
    Computable.encode.comp
      ((sentenceInsertionSort_prim.comp sentenceDedup_prim).to_comp.comp hlist)
  obtain ⟨code, hcode⟩ := Nat.Partrec.Code.exists_code.mp
    (Partrec.nat_iff.mp hkey)
  refine ⟨code, fun k => ?_⟩
  rw [hcode]
  exact Part.mem_some_iff.mpr (encode_toFinset_eq (semanticSourceStageList k))

/-! ## The canonical extension world -/

/-- Bounded runs of one named emitter cannot decode to two different sentences. -/
lemma semanticSourceSentenceAtFuel_unique {schema input fuel fuel' : ℕ}
    {φ ψ : Sentence}
    (hφ : semanticSourceSentenceAtFuel schema input fuel = some φ)
    (hψ : semanticSourceSentenceAtFuel schema input fuel' = some ψ) : φ = ψ := by
  unfold semanticSourceSentenceAtFuel at hφ hψ
  obtain ⟨outφ, houtφ, hdecodeφ⟩ := Option.bind_eq_some_iff.mp hφ
  obtain ⟨outψ, houtψ, hdecodeψ⟩ := Option.bind_eq_some_iff.mp hψ
  have hmemφ := Nat.Partrec.Code.evaln_sound houtφ
  have hmemψ := Nat.Partrec.Code.evaln_sound houtψ
  have hout : outφ = outψ := Part.mem_unique hmemφ hmemψ
  subst outψ
  rw [hdecodeφ] at hdecodeψ
  exact Option.some.inj hdecodeψ

/-- Extend an arbitrary base world by interpreting each successfully emitted fresh
tag-`0` source leaf as the base-world truth of its unique emitted sentence. -/
noncomputable def semanticSourceExtensionWorld (v₀ : PCWorld) : PCWorld := by
  classical
  exact fun a =>
    if a.unpair.1 = semanticPrimeTag ∧ a.unpair.2.unpair.1.unpair.1 = 0 then
      ∃ fuel φ,
        semanticSourceSentenceAtFuel a.unpair.2.unpair.1 a.unpair.2.unpair.2 fuel = some φ ∧
          SemanticPrimeFreshSentence φ ∧ v₀.Holds φ
    else v₀ a

lemma semanticSourceExtensionWorld_agree (v₀ : PCWorld) {a : ℕ}
    (ha : a.unpair.1 ≠ semanticPrimeTag) :
    semanticSourceExtensionWorld v₀ a ↔ v₀ a := by
  simp [semanticSourceExtensionWorld, ha]

lemma semanticSourceExtensionWorld_holds_fresh (v₀ : PCWorld) {φ : Sentence}
    (hφ : SemanticPrimeFreshSentence φ) :
    (semanticSourceExtensionWorld v₀).Holds φ ↔ v₀.Holds φ :=
  PCWorld.holds_congr_atomCodes φ
    (fun a ha => semanticSourceExtensionWorld_agree v₀ (hφ a ha))

lemma semanticSourceExtensionWorld_leaf (v₀ : PCWorld)
    (schema input : ℕ) (hschema : schema.unpair.1 = 0) :
    (semanticSourceExtensionWorld v₀).Holds (semanticPrimeSentence schema input) ↔
      ∃ fuel φ, semanticSourceSentenceAtFuel schema input fuel = some φ ∧
        SemanticPrimeFreshSentence φ ∧ v₀.Holds φ := by
  change semanticSourceExtensionWorld v₀ (semanticPrimeCode schema input) ↔ _
  simp [semanticSourceExtensionWorld, semanticPrimeCode, hschema]

lemma semanticSourceExtensionWorld_leaf_iff (v₀ : PCWorld)
    (schema input fuel : ℕ) (hschema : schema.unpair.1 = 0) {φ : Sentence}
    (hemit : semanticSourceSentenceAtFuel schema input fuel = some φ)
    (hfresh : SemanticPrimeFreshSentence φ) :
    (semanticSourceExtensionWorld v₀).Holds (semanticPrimeSentence schema input) ↔
      v₀.Holds φ := by
  rw [semanticSourceExtensionWorld_leaf v₀ schema input hschema]
  constructor
  · rintro ⟨fuel', ψ, hψ, _, hholds⟩
    simpa [semanticSourceSentenceAtFuel_unique hψ hemit] using hholds
  · intro hholds
    exact ⟨fuel, φ, hemit, hfresh, hholds⟩

/-- Any downward law admitted by the executable registry is semantically valid between
the corresponding source leaves in the canonical extension of a base model. -/
lemma semanticSourceExtensionWorld_downward_of_seen {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (v₀ : PCWorld)
    (hv₀ : v₀.ConsistentWithTheory DP) {schema n fuel : ℕ} {r s : ℚ}
    (hrs : r < s)
    (hseen : semanticSourceLawSeen base schema
      (sourceCutDownwardJob n r s) fuel = true) :
    (semanticSourceExtensionWorld v₀).Holds
      (semanticPrimeSentence schema (Nat.pair n (Encodable.encode s))) →
    (semanticSourceExtensionWorld v₀).Holds
      (semanticPrimeSentence schema (Nat.pair n (Encodable.encode r))) := by
  obtain ⟨f, _, law, hchecked⟩ :=
    (semanticSourceLawSeen_iff base schema (sourceCutDownwardJob n r s) fuel).1 hseen
  obtain ⟨φr, φs, hφr, hφs, hfr, hfs, rfl⟩ :=
    semanticSourceCheckedDownward_spec base hrs hchecked
  have hsource := semanticSourceCheckedLawAtFuel_source base hchecked
  obtain ⟨k, hk⟩ := semanticSourceCheckedLawAtFuel_mem base hchecked
  have hbase : v₀.Holds (φs 🡒 φr) := hv₀ k _ hk
  intro hs
  have hs₀ : v₀.Holds φs :=
    (semanticSourceExtensionWorld_leaf_iff v₀ schema _ f hsource hφs hfs).mp hs
  exact (semanticSourceExtensionWorld_leaf_iff v₀ schema _ f hsource hφr hfr).mpr
    (hbase hs₀)

/-! ## Explicit non-vacuity -/

/-- Every source-definition clause is true in the canonical extension world. -/
lemma semanticSourceExtensionWorld_holds_defSentence (v₀ : PCWorld) (e : ℕ) :
    (semanticSourceExtensionWorld v₀).Holds (semanticSourceDefSentence e) := by
  unfold semanticSourceDefSentence
  by_cases hschema : e.unpair.1.unpair.1 = 0
  · rw [if_pos hschema]
    cases hemit : (semanticSourceSentenceAtFuel e.unpair.1 e.unpair.2.unpair.1
        e.unpair.2.unpair.2.unpair.2) with
    | none =>
        change (semanticSourceExtensionWorld v₀).Holds (⊤ : Sentence)
        exact PCWorld.holds_top _
    | some φ =>
        change (semanticSourceExtensionWorld v₀).Holds
          (if semanticPrimeFreshSentenceB φ then
            if e.unpair.2.unpair.2.unpair.1 = 0 then
              φ 🡒 semanticPrimeSentence e.unpair.1 e.unpair.2.unpair.1
            else semanticPrimeSentence e.unpair.1 e.unpair.2.unpair.1 🡒 φ
          else ⊤)
        by_cases hfreshB : semanticPrimeFreshSentenceB φ = true
        · rw [if_pos hfreshB]
          have hfresh : SemanticPrimeFreshSentence φ :=
            (semanticPrimeFreshSentenceB_eq_true φ).1 hfreshB
          have hleaf := semanticSourceExtensionWorld_leaf_iff v₀
            e.unpair.1 e.unpair.2.unpair.1 e.unpair.2.unpair.2.unpair.2
            hschema hemit hfresh
          have hformula := semanticSourceExtensionWorld_holds_fresh v₀ hfresh
          by_cases hdir : e.unpair.2.unpair.2.unpair.1 = 0
          · rw [if_pos hdir]
            intro h
            exact hleaf.mpr (hformula.mp h)
          · rw [if_neg hdir]
            intro h
            exact hformula.mpr (hleaf.mp h)
        · rw [if_neg hfreshB]
          exact PCWorld.holds_top _
  · rw [if_neg hschema]
    exact PCWorld.holds_top _

/-- The fixed universal source process has an explicit completed world over every base
world; no consistency premise is hidden in source reflection. -/
lemma semanticSourceDP_hworld (v₀ : PCWorld) :
    (semanticSourceExtensionWorld v₀).ConsistentWithTheory semanticSourceDP := by
  intro k φ hφ
  obtain ⟨e, rfl⟩ := semanticSourceStageList_exists (List.mem_toFinset.mp hφ)
  exact semanticSourceExtensionWorld_holds_defSentence v₀ e

/-! ## The theorem-plus-source process

The union offered to clients as a named package: a canonical process, its certified program,
and its explicit completed world.  Nothing downstream prices against it, by the design
decision recorded in the module header. -/

/-- Conservative combination with any base process whose stages stay in the old language. -/
lemma semanticSourceExtensionWorld_consistentWith_union
    (B : DeductiveProcess) (v₀ : PCWorld)
    (hBfresh : ∀ k φ, φ ∈ B.D k → SemanticPrimeFreshSentence φ)
    (hv₀ : v₀.ConsistentWithTheory B) :
    (semanticSourceExtensionWorld v₀).ConsistentWithTheory
      (B.union semanticSourceDP) := by
  intro k
  refine ((semanticSourceExtensionWorld v₀).consistentWith_union_iff
    B semanticSourceDP k).mpr ⟨?_, semanticSourceDP_hworld v₀ k⟩
  intro φ hφ
  exact (semanticSourceExtensionWorld_holds_fresh v₀ (hBfresh k φ hφ)).mpr
    (hv₀ k φ hφ)

/-- The canonical source-aware theory process is fixed from `T` alone. -/
noncomputable def theoremSemanticSourceDP (T : ArithmeticTheory) [T.Δ₁]
    [Entailment.Consistent T] : DeductiveProcess :=
  (theoremDP T).union semanticSourceDP

/-- The certified program for `theoremSemanticSourceDP`, the union of `theoremDP`'s own
program and `semanticSourceDP`'s. -/
noncomputable def theoremSemanticSourceDPComputation (T : ArithmeticTheory)
    [T.Δ₁] [Entailment.Consistent T] :
    DeductiveProcessComputation (theoremSemanticSourceDP T) :=
  ((theoremDP_computable T).nonemptyComputation.some).union
    semanticSourceDP_computable.nonemptyComputation.some

lemma theoremDP_semanticPrimeFresh (T : ArithmeticTheory) [T.Δ₁]
    [Entailment.Consistent T] (k : ℕ) (φ : Sentence) (hφ : φ ∈ (theoremDP T).D k) :
    SemanticPrimeFreshSentence φ := by
  simp only [theoremDP, theoremStage, Finset.mem_image, Finset.mem_filter,
    Finset.mem_range] at hφ
  obtain ⟨e, _, rfl⟩ := hφ
  exact eventAtom_atomCodes_ne_semanticPrimeTag e

/-- Explicit non-vacuity of the fixed theorem-plus-source process. -/
lemma theoremSemanticSourceDP_hworld (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    [Entailment.Consistent T] :
    (semanticSourceExtensionWorld (provabilityWorld T)).ConsistentWithTheory
      (theoremSemanticSourceDP T) :=
  semanticSourceExtensionWorld_consistentWith_union (theoremDP T)
    (provabilityWorld T) (theoremDP_semanticPrimeFresh T) (theoremDP_hworld T)

lemma semanticSourceDefSentence_mem_stage (e : ℕ) :
    semanticSourceDefSentence e ∈ semanticSourceDP.D e :=
  List.mem_toFinset.mpr (mem_semanticSourceStageList (le_refl e))

lemma holds_semanticSourceDefSentence {v : PCWorld}
    (hv : v.ConsistentWithTheory semanticSourceDP) (e : ℕ) :
    v.Holds (semanticSourceDefSentence e) :=
  hv e _ (semanticSourceDefSentence_mem_stage e)

lemma semanticSourceDefSentence_job (schema input direction fuel : ℕ) :
    semanticSourceDefSentence
      (semanticSourceDefinitionJob schema input direction fuel) =
      if schema.unpair.1 = 0 then
        match semanticSourceSentenceAtFuel schema input fuel with
        | some φ =>
            if semanticPrimeFreshSentenceB φ then
              if direction = 0 then φ 🡒 semanticPrimeSentence schema input
              else semanticPrimeSentence schema input 🡒 φ
            else ⊤
        | none => ⊤
      else ⊤ := by
  simp [semanticSourceDefSentence, semanticSourceDefinitionJob]

/-! ## Threshold reflection for certified sources -/

/-- Any successfully decoded fresh source sentence is reflected by its semantic handle in
every completed world of the one fixed process. -/
lemma semanticSourceSentenceAtFuel_reflected {v : PCWorld}
    (hv : v.ConsistentWithTheory semanticSourceDP)
    (schema input fuel : ℕ) (hschema : schema.unpair.1 = 0)
    {φ : Sentence} (hemit : semanticSourceSentenceAtFuel schema input fuel = some φ)
    (hfresh : SemanticPrimeFreshSentence φ) :
    v.Holds (semanticPrimeSentence schema input) ↔ v.Holds φ := by
  have hfreshB : semanticPrimeFreshSentenceB φ = true :=
    (semanticPrimeFreshSentenceB_eq_true φ).2 hfresh
  constructor
  · have h := holds_semanticSourceDefSentence hv
      (semanticSourceDefinitionJob schema input 1 fuel)
    rw [semanticSourceDefSentence_job, if_pos hschema, hemit] at h
    simp [hfreshB] at h
    exact h
  · have h := holds_semanticSourceDefSentence hv
      (semanticSourceDefinitionJob schema input 0 fuel)
    rw [semanticSourceDefSentence_job, if_pos hschema, hemit] at h
    simp [hfreshB] at h
    exact h

/-- Every proof-carrying paper source has exact threshold reflection through its canonical
compact wrapper. -/
lemma certifiedSource_threshold_reflected {DP : DeductiveProcess}
    (X : CertifiedSourceLUVSeq DP) (n : ℕ) (r : ℚ) (v : PCWorld)
    (hv : v.ConsistentWithTheory semanticSourceDP) :
    v.Holds ((X.toPresented.toLUV n).gt r) ↔ v.Holds ((X.toLUV n).gt r) := by
  obtain ⟨fuel, hfuel⟩ := evaln_decode_sentence_eventually X.emitterCode
    (Nat.pair n (Encodable.encode r)) ((X.toLUV n).gt r) (X.emitter_spec n r)
  apply semanticSourceSentenceAtFuel_reflected hv X.thresholdSchema
    (Nat.pair n (Encodable.encode r)) fuel X.thresholdSchema_source
  · simpa [semanticSourceSentenceAtFuel, certified_thresholdSchema_emitterCode] using hfuel
  · exact X.old_language n r

/-- Exact threshold reflection transfers the repository's `ValuesAt` relation both ways. -/
lemma certifiedSource_valuesAt_iff {DP : DeductiveProcess}
    (X : CertifiedSourceLUVSeq DP) (n : ℕ) (x : ℝ) (v : PCWorld)
    (hv : v.ConsistentWithTheory semanticSourceDP) :
    v.ValuesAt (X.toPresented.toLUV n) x ↔ v.ValuesAt (X.toLUV n) x := by
  constructor
  · rintro ⟨hx0, hx1, hx⟩
    exact ⟨hx0, hx1, fun r => by rw [← certifiedSource_threshold_reflected X n r v hv]; exact hx r⟩
  · rintro ⟨hx0, hx1, hx⟩
    exact ⟨hx0, hx1, fun r => by rw [certifiedSource_threshold_reflected X n r v hv]; exact hx r⟩

end LogicalInduction
