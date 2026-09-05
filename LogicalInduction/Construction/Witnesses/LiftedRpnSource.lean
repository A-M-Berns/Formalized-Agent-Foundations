import LogicalInduction.Construction.Witnesses.EntailedSourceRegistry
import LogicalInduction.Construction.Witnesses.SemanticSourceDP

/-!
# Compiling an existing RPN source into the fixed old-language registry

This module is the compiler that admits a caller's *existing* token-metered RPN threshold
certificate (`LUV.RpnThresholdCodeSeq X`) into the fixed old-language semantic registry,
so that the exact product of `thm:ccee` accepts an arbitrary threshold-only source.

It defines `liftedRpnSourceSentence`, the represented sentence at an arbitrary rational
query; `liftedRpnMeshQuery`, the conversion into the `⟨n,⟨k,i⟩⟩` ABI of
`RpnThresholdCodeSeq`; `liftedRpnSourceCode`, the total emitter program extracted from the
caller's certificate; and `liftedRpnSourceSchema`, its self-describing tag-`0` schema.

No new efficiency premise is added to the caller: the exact product needs only nonnegative
rational thresholds, every nonnegative reduced rational is already one of the `i/k` queries
`RpnThresholdCodeSeq` certifies, and negative queries receive the canonical true sentence
`⊤`.

The main results are `liftedRpnSource_reflected` — exact reflection of the internally
lifted source through the one fixed universal source interpreter — and
`liftedRpnSourcePrefix_eventually_valid`, that every finite registry prefix is eventually
validated, which is the hypothesis the registry gate consumes.
`liftedRpnSourceSentence_fresh` separates every derived sentence from the
semantic-extension namespace, which is what keeps the extension world's leaf agreement
available.

Consumers: `Construction/Witnesses/SemanticLiftedCCEE.lean`, where
`liftedRpnSource_factor_eventually` turns these into admission of the source as an exact
product factor, and thence `lic_no_expected_net_update_conditional_exact_canonical`
(`thm:ccee`, generalized semantic-extension form).

Design: the emitter code is *data* inside a universal tag-`0` schema; the semantic process
is never specialized to `X`, which is what keeps the deductive process fixed from `T`
before a source is chosen.
-/

namespace LogicalInduction

open LO LO.Propositional

-- Both registry predicates are `List.range` dovetails (`EntailedSourceRegistry.lean`).
-- The proofs below reach them only through their monotonicity and characterization
-- lemmas, so keeping the ranges opaque stops `simp` unfolding a dovetail inside the
-- eventual-validity inductions.
attribute [local irreducible] entailedSourceLawSeen
attribute [local irreducible] entailedSourcePrefixValidAtFuel

/-! ## The lifted source sentence and its query ABI -/

/-- The source sentence represented at an arbitrary rational query.  Negative thresholds
use `⊤`; nonnegative thresholds are the fixed old-language copy of the caller's source. -/
def liftedRpnSourceSentence (X : ℕ → LUV) (n : ℕ) (r : ℚ) : Sentence :=
  if r < 0 then ⊤ else liftSentence ((X n).gt r)

/-- Convert a canonical rational query to the `⟨n,⟨k,i⟩⟩` ABI of
`RpnThresholdCodeSeq`. -/
def liftedRpnMeshQuery (input : ℕ) : ℕ :=
  let n := input.unpair.1
  let r := decodedQuotationRat input.unpair.2
  let z := Encodable.encode r
  Nat.pair n (Nat.pair z.unpair.2 z.unpair.1.div2)

/-- The query conversion is primitive recursive. -/
lemma liftedRpnMeshQuery_prim : Primrec liftedRpnMeshQuery := by
  have hn : Primrec fun input : ℕ => input.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hz : Primrec fun input : ℕ => Encodable.encode
      (decodedQuotationRat input.unpair.2) :=
    Primrec.encode.comp (decodedQuotationRat_prim.comp
      (Primrec.snd.comp Primrec.unpair))
  have hk : Primrec fun input : ℕ =>
      (Encodable.encode (decodedQuotationRat input.unpair.2)).unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp hz)
  have hi : Primrec fun input : ℕ =>
      (Encodable.encode (decodedQuotationRat input.unpair.2)).unpair.1.div2 :=
    Primrec.nat_div2.comp (Primrec.fst.comp (Primrec.unpair.comp hz))
  exact (Primrec₂.natPair.comp hn (Primrec₂.natPair.comp hk hi)).of_eq fun _ => rfl

private lemma nonnegative_rat_mesh (r : ℚ) (hr : 0 ≤ r) :
    ((r.num.natAbs : ℚ) / (r.den : ℚ)) = r := by
  have hn : 0 ≤ r.num := Rat.num_nonneg.mpr hr
  rw [Nat.cast_natAbs, abs_of_nonneg hn]
  exact Rat.num_div_den r

/-- **The ABI specification**: at a nonnegative query the conversion preserves the LUV
index and the rational `i/k` it names. -/
lemma liftedRpnMeshQuery_spec (n : ℕ) (r : ℚ) (hr : 0 ≤ r) :
    (liftedRpnMeshQuery (Nat.pair n (Encodable.encode r))).unpair.1 = n ∧
    (((liftedRpnMeshQuery (Nat.pair n (Encodable.encode r))).unpair.2.unpair.2 : ℚ) /
      ((liftedRpnMeshQuery (Nat.pair n (Encodable.encode r))).unpair.2.unpair.1 : ℚ)) = r := by
  constructor
  · simp [liftedRpnMeshQuery]
  · simp only [liftedRpnMeshQuery, Nat.unpair_pair, decodedQuotationRat_encode]
    rw [encode_rat_eq]
    simp only [Nat.unpair_pair]
    have hn : 0 ≤ r.num := Rat.num_nonneg.mpr hr
    have hencode : (Encodable.encode r.num).div2 = r.num.natAbs := by
      obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hn
      rw [hm]
      simp [encode_int_natCast]
    rw [hencode]
    exact nonnegative_rat_mesh r hr

private def liftedRpnSourceOutput (X : ℕ → LUV) (input : ℕ) : ℕ :=
  if decodedQuotationRat input.unpair.2 < 0 then
    Encodable.encode (⊤ : Sentence)
  else
    liftSentenceCode (Encodable.encode ((X (liftedRpnMeshQuery input).unpair.1).gt
      (((liftedRpnMeshQuery input).unpair.2.unpair.2 : ℚ) /
        ((liftedRpnMeshQuery input).unpair.2.unpair.1 : ℚ))))

private lemma liftedRpnSourceOutput_computable {X : ℕ → LUV}
    (hX : LUV.RpnThresholdCodeSeq X) : Computable (liftedRpnSourceOutput X) := by
  let sourceOutput : ℕ → ℕ := fun m => Encodable.encode ((X m.unpair.1).gt
    ((m.unpair.2.unpair.2 : ℚ) / (m.unpair.2.unpair.1 : ℚ)))
  have hpart : Partrec fun m => (rpnThresholdSourceCode hX).eval m :=
    Nat.Partrec.Code.eval_part.comp
      (Computable.const (rpnThresholdSourceCode hX)) Computable.id
  have hsource : Computable sourceOutput :=
    hpart.of_eq fun m => Part.eq_some_iff.mpr (rpnThresholdSourceCode_spec hX m)
  have hr : Primrec fun input : ℕ => decodedQuotationRat input.unpair.2 :=
    decodedQuotationRat_prim.comp (Primrec.snd.comp Primrec.unpair)
  have hneg : Computable fun input : ℕ => decide
      (decodedQuotationRat input.unpair.2 < 0) :=
    ((ratLE_prim.comp (Primrec.const 0) hr).not.of_eq fun _ => by simp [not_le]).decide.to_comp
  have hlift : Computable fun input : ℕ => liftSentenceCode
      (sourceOutput (liftedRpnMeshQuery input)) :=
    liftSentenceCode_prim.to_comp.comp
      (hsource.comp liftedRpnMeshQuery_prim.to_comp)
  exact (Computable.cond hneg (Computable.const (Encodable.encode (⊤ : Sentence)))
    hlift).of_eq fun input => by
      by_cases h : decodedQuotationRat input.unpair.2 < 0 <;>
        simp [liftedRpnSourceOutput, sourceOutput, h]

/-! ## The extracted emitter and its schema -/

/-- The total emitter program extracted from the caller's existing token-metered RPN
certificate.  The code is data inside a universal tag-`0` schema; the semantic process is
not specialized to `X`. -/
noncomputable def liftedRpnSourceCode {X : ℕ → LUV}
    (hX : LUV.RpnThresholdCodeSeq X) : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp
    (Partrec.nat_iff.mp (liftedRpnSourceOutput_computable hX)))

/-- **The emitter specification**: the extracted program emits the intended represented
sentence at every rational query. -/
lemma liftedRpnSourceCode_spec {X : ℕ → LUV}
    (hX : LUV.RpnThresholdCodeSeq X) (n : ℕ) (r : ℚ) :
    Encodable.encode (liftedRpnSourceSentence X n r) ∈
      (liftedRpnSourceCode hX).eval (Nat.pair n (Encodable.encode r)) := by
  have hcode := Classical.choose_spec (Nat.Partrec.Code.exists_code.mp
    (Partrec.nat_iff.mp (liftedRpnSourceOutput_computable hX)))
  rw [liftedRpnSourceCode, hcode]
  apply Part.mem_some_iff.mpr
  by_cases hr : r < 0
  · simp [liftedRpnSourceOutput, liftedRpnSourceSentence, hr]
  · have hr0 : 0 ≤ r := le_of_not_gt hr
    obtain ⟨hn, hmesh⟩ := liftedRpnMeshQuery_spec n r hr0
    simp only [liftedRpnSourceOutput, Nat.unpair_pair, decodedQuotationRat_encode,
      if_neg hr, liftedRpnSourceSentence]
    rw [liftSentenceCode_spec]
    rw [hn, hmesh]

/-- Self-describing tag-`0` schema for the derived emitter.  The second payload is a
harmless placeholder: entailment-gated admission never executes a source certificate. -/
noncomputable def liftedRpnSourceSchema {X : ℕ → LUV}
    (hX : LUV.RpnThresholdCodeSeq X) : ℕ :=
  semanticEmitterSchema (Nat.pair (Encodable.encode (liftedRpnSourceCode hX)) 0)

/-- The derived schema carries the source tag `0`. -/
@[simp] lemma liftedRpnSourceSchema_source {X : ℕ → LUV}
    (hX : LUV.RpnThresholdCodeSeq X) : (liftedRpnSourceSchema hX).unpair.1 = 0 := by
  simp [liftedRpnSourceSchema]

/-- The universal interpreter reads the extracted program back out of the schema. -/
@[simp] lemma liftedRpnSourceSchema_emitterCode {X : ℕ → LUV}
    (hX : LUV.RpnThresholdCodeSeq X) :
    semanticSourceEmitterCode (liftedRpnSourceSchema hX) = liftedRpnSourceCode hX := by
  simp [semanticSourceEmitterCode, liftedRpnSourceSchema, semanticEmitterSchema,
    semanticSourceSchema]

/-- Every derived source sentence is separated from the semantic extension namespace. -/
lemma liftedRpnSourceSentence_fresh (X : ℕ → LUV) (n : ℕ) (r : ℚ) :
    SemanticPrimeFreshSentence (liftedRpnSourceSentence X n r) := by
  by_cases hr : r < 0
  · simp [liftedRpnSourceSentence, hr, SemanticPrimeFreshSentence,
      sentenceAtomCodes_verum]
  · intro a ha
    rw [liftedRpnSourceSentence, if_neg hr, sentenceAtomCodes_liftSentence] at ha
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp ha
    have haold : (oldAtom b).unpair.1 = oldLanguageTag := by simp [oldAtom]
    simpa [haold, oldLanguageTag, semanticPrimeTag]

/-! ## Reflection through the universal interpreter -/

/-- Exact reflection of the internally lifted source through the one fixed universal
source interpreter. -/
lemma liftedRpnSource_reflected {X : ℕ → LUV} (hX : LUV.RpnThresholdCodeSeq X)
    (n : ℕ) (r : ℚ) (v : PCWorld)
    (hv : v.ConsistentWithTheory semanticSourceDP) :
    v.Holds (semanticPrimeSentence (liftedRpnSourceSchema hX)
      (Nat.pair n (Encodable.encode r))) ↔
      v.Holds (liftedRpnSourceSentence X n r) := by
  obtain ⟨fuel, heval⟩ := Nat.Partrec.Code.evaln_complete.mp
    (liftedRpnSourceCode_spec hX n r)
  apply semanticSourceSentenceAtFuel_reflected hv (liftedRpnSourceSchema hX)
    (Nat.pair n (Encodable.encode r)) fuel (liftedRpnSourceSchema_source hX)
  · rw [semanticSourceSentenceAtFuel, liftedRpnSourceSchema_emitterCode]
    rw [show Nat.Partrec.Code.evaln fuel (liftedRpnSourceCode hX)
      (Nat.pair n (Encodable.encode r)) =
        some (Encodable.encode (liftedRpnSourceSentence X n r)) from heval]
    simp
  · exact liftedRpnSourceSentence_fresh X n r

/-- Emission is monotone in the interpreter's fuel. -/
lemma semanticSourceSentenceAtFuel_mono {schema input fuel fuel' : ℕ}
    (hff : fuel ≤ fuel') {phi : Sentence}
    (h : semanticSourceSentenceAtFuel schema input fuel = some phi) :
    semanticSourceSentenceAtFuel schema input fuel' = some phi := by
  unfold semanticSourceSentenceAtFuel at h ⊢
  cases he : Nat.Partrec.Code.evaln fuel (semanticSourceEmitterCode schema) input with
  | none => simp [he] at h
  | some out =>
      have he' := Nat.Partrec.Code.evaln_mono hff (Option.mem_def.mpr he)
      rw [show Nat.Partrec.Code.evaln fuel' (semanticSourceEmitterCode schema) input =
        some out from he']
      simpa [he] using h

/-- Enough fuel eventually emits the represented sentence at any one query. -/
lemma liftedRpnSourceSentenceAtFuel_eventually {X : ℕ → LUV}
    (hX : LUV.RpnThresholdCodeSeq X) (n : ℕ) (r : ℚ) :
    ∃ fuel, semanticSourceSentenceAtFuel (liftedRpnSourceSchema hX)
      (Nat.pair n (Encodable.encode r)) fuel =
        some (liftedRpnSourceSentence X n r) := by
  obtain ⟨fuel, hfuel⟩ := evaln_decode_sentence_eventually
    (liftedRpnSourceCode hX) (Nat.pair n (Encodable.encode r))
    (liftedRpnSourceSentence X n r) (liftedRpnSourceCode_spec hX n r)
  refine ⟨fuel, ?_⟩
  simpa [semanticSourceSentenceAtFuel, liftedRpnSourceSchema_emitterCode] using hfuel

/-- Enough fuel eventually witnesses the freshness of the sentence at any one query. -/
lemma liftedRpnSourceFreshSeen_eventually {X : ℕ → LUV}
    (hX : LUV.RpnThresholdCodeSeq X) (n z : ℕ) :
    ∃ fuel, semanticSourceFreshSeen (liftedRpnSourceSchema hX) n z fuel = true := by
  obtain ⟨fuel, hemit⟩ := liftedRpnSourceSentenceAtFuel_eventually hX n
    (decodedQuotationRat z)
  exact ⟨fuel, (semanticSourceFreshSeen_iff _ _ _ _).2
    ⟨fuel, le_rfl, liftedRpnSourceSentence X n (decodedQuotationRat z), hemit,
      liftedRpnSourceSentence_fresh X n _⟩⟩

/-! ## Registry-prefix validity -/

/-- Enough fuel eventually witnesses one downward cut law `X n > s ⊢ X n > r` for `r < s`.
The hypotheses are the ones the registry gate carries: every `X n` is valued in every
world consistent with `DP`, and every world consistent with the base process is consistent
with the lifted copy of `DP`. -/
lemma liftedRpnSourceLawSeen_eventually {DP Base : DeductiveProcess}
    (base : DeductiveProcessComputation Base) {X : ℕ → LUV}
    (hX : LUV.RpnThresholdCodeSeq X)
    (source_valued : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ∃ x, v.ValuesAt (X n) x)
    (base_lifted : ∀ v : PCWorld, v.ConsistentWithTheory Base →
      v.ConsistentWithTheory (liftDP DP))
    (n : ℕ) {r s : ℚ} (hrs : r < s) :
    ∃ fuel, entailedSourceLawSeen base (liftedRpnSourceSchema hX)
      (sourceCutDownwardJob n r s) fuel = true := by
  obtain ⟨fr, hfr⟩ := liftedRpnSourceSentenceAtFuel_eventually hX n r
  obtain ⟨fs, hfs⟩ := liftedRpnSourceSentenceAtFuel_eventually hX n s
  let emitterFuel := max fr fs
  have hfr' : semanticSourceSentenceAtFuel (liftedRpnSourceSchema hX)
      (Nat.pair n (Encodable.encode r)) emitterFuel =
        some (liftedRpnSourceSentence X n r) :=
    semanticSourceSentenceAtFuel_mono (by simp [emitterFuel]) hfr
  have hfs' : semanticSourceSentenceAtFuel (liftedRpnSourceSchema hX)
      (Nat.pair n (Encodable.encode s)) emitterFuel =
        some (liftedRpnSourceSentence X n s) :=
    semanticSourceSentenceAtFuel_mono (by simp [emitterFuel]) hfs
  let law := liftedRpnSourceSentence X n s 🡒 liftedRpnSourceSentence X n r
  have hemit : semanticSourceCutLawAtFuel (liftedRpnSourceSchema hX)
      (sourceCutDownwardJob n r s) emitterFuel = some law := by
    simp only [semanticSourceCutLawAtFuel, sourceCutDownwardJob, Nat.unpair_pair,
      if_neg (by decide : ¬(2 : ℕ) = 0), if_neg (by decide : ¬(2 : ℕ) = 1),
      decodedQuotationRat_encode, if_pos hrs]
    rw [hfr', hfs']
    change _ = some (liftedRpnSourceSentence X n s 🡒
      liftedRpnSourceSentence X n r)
    exact freshImpSourceSentence_eq_some_of_fresh
      (liftedRpnSourceSentence_fresh X n r)
      (liftedRpnSourceSentence_fresh X n s)
  apply entailedSourceLawSeen_eventually base ⟨emitterFuel, hemit⟩
  intro v hv
  by_cases hr : r < 0
  · simp only [law, liftedRpnSourceSentence, if_pos hr]
    intro _
    exact PCWorld.holds_top v
  · have hs : ¬s < 0 := by linarith
    simpa [law, liftedRpnSourceSentence, hr, hs, liftLUV] using
      (liftLUV_holds_downward_of_valued
        (X := X n) (source_valued n) (base_lifted v hv) hrs)

private lemma liftedListAll_eventually_of_mono {l : List ℕ}
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

set_option maxHeartbeats 8000000 in
/-- **Prefix validity**: every finite registry prefix is eventually validated, which is
what the registry gate consumes to admit the lifted source as a certified factor. -/
lemma liftedRpnSourcePrefix_eventually_valid {DP Base : DeductiveProcess}
    (base : DeductiveProcessComputation Base) {X : ℕ → LUV}
    (hX : LUV.RpnThresholdCodeSeq X)
    (source_valued : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ∃ x, v.ValuesAt (X n) x)
    (base_lifted : ∀ v : PCWorld, v.ConsistentWithTheory Base →
      v.ConsistentWithTheory (liftDP DP))
    (limit : ℕ) :
    ∃ fuel, entailedSourcePrefixValidAtFuel base
      (liftedRpnSourceSchema hX) limit fuel = true := by
  have thresholdEventually (n zr : ℕ) : ∃ fuel,
      entailedSourceThresholdPrefixValidAtFuel base
        (liftedRpnSourceSchema hX) limit fuel n zr = true := by
    obtain ⟨ffresh, hfresh⟩ := liftedRpnSourceFreshSeen_eventually hX n zr
    let test : ℕ → ℕ → Bool := fun zs fuel =>
      if decodedQuotationRat zr < decodedQuotationRat zs then
        entailedSourceLawSeen base (liftedRpnSourceSchema hX)
          (sourceCutDownwardJob n (decodedQuotationRat zr)
            (decodedQuotationRat zs)) fuel
      else true
    have htestMono : ∀ zs {fuel fuel'}, fuel ≤ fuel' → test zs fuel = true →
        test zs fuel' = true := by
      intro zs fuel fuel' hff h
      by_cases hrs : decodedQuotationRat zr < decodedQuotationRat zs
      · simpa [test, hrs] using entailedSourceLawSeen_mono base hff
          (by simpa [test, hrs] using h)
      · simp [test, hrs]
    have htestEventually : ∀ zs ∈ List.range (limit + 1),
        ∃ fuel, test zs fuel = true := by
      intro zs _
      by_cases hrs : decodedQuotationRat zr < decodedQuotationRat zs
      · obtain ⟨fuel, h⟩ := liftedRpnSourceLawSeen_eventually base hX
          source_valued base_lifted n hrs
        exact ⟨fuel, by simpa [test, hrs] using h⟩
      · exact ⟨0, by simp [test, hrs]⟩
    obtain ⟨fdown, hdown⟩ := liftedListAll_eventually_of_mono
      htestMono htestEventually
    let fuel := max ffresh fdown
    refine ⟨fuel, ?_⟩
    rw [entailedSourceThresholdPrefixValidAtFuel, Bool.and_eq_true]
    refine ⟨semanticSourceFreshSeen_mono (Nat.le_max_left _ _) hfresh, ?_⟩
    change (List.range (limit + 1)).all (fun zs =>
      if decodedQuotationRat zr < decodedQuotationRat zs then
        entailedSourceLawSeen base (liftedRpnSourceSchema hX)
          (sourceCutDownwardJob n (decodedQuotationRat zr)
            (decodedQuotationRat zs)) fdown
      else true) = true at hdown
    rw [entailedSourceDownwardPrefixValidAtFuel, List.all_eq_true]
    rw [List.all_eq_true] at hdown
    intro zs hzs
    exact htestMono zs (Nat.le_max_right _ _) (hdown zs hzs)
  exact entailedSourcePrefix_eventually_of_threshold base
    (liftedRpnSourceSchema hX) limit thresholdEventually

end LogicalInduction
