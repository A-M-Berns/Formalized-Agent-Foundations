import LogicalInduction.Construction.Primcodable
import LogicalInduction.Construction.LIAComputation
import LogicalInduction.Properties.FinitePerturbations
import LogicalInduction.Framework.Emission.FreezeTransducer
import LogicalInduction.Framework.Emission.WriteOut

/-!
# The finite-prefix freeze: parser control and prefix quoting

`def:lia`.  Overwriting a trader's quotes on the days before a cutoff must preserve efficient
computability.  The pieces are a variable-width emitter for the frozen suffix, exhaustive
raw-code sentence matching (`sentenceMatches`), and lookup of a quote in the logical
inductor's finite table of early belief states, assembled into
`liaFreezeBefore_preserves_ecTok`.  The parser control the emitter runs on is the token
model's own, `freezeControlNat` (`Framework/Emission/FreezeTransducer.lean`).

This is the first of the three freeze-compilation modules, and the cut between them is by
*what is frozen*: `Prefix.lean` holds the token-model quote-table freeze; `CanonicalCodes.lean`
holds the falsum-freeness ruling on the escape test; `Compiler.lean` holds the symbol-level
rewrite of the flat RPN stream.  This module's own imports are the `LIA` spine
(`Construction/LIAComputation.lean`, for `liaHistory` and `liaStatePrefix`) and
`Properties/FinitePerturbations.lean` (for `Trader.freezeBefore`, the object being compiled).

The raw-code matcher below is written in Foundation's `Formula.ofNat` / `Formula.toNat`
terms, read back as `Sentence` codes through the definitional bridges
`decode_sentence_eq_ofNat` and `encode_sentence_eq_toNat`
(`Framework/Foundations.lean`).

**Design choices.**  `dd:fuel` names the certificate calculus these objects certify into, and
the boundary it reaches is stated at `liaFreezeBefore_preserves_ecTok`: the digit model is
closed under the forward big-value operations and open under their inverses, so the
escape-leaf decode test is unavailable at the collapsed class.  `Nat.sqrt` is locally
irreducible in the namespace below, for the reason stated in
`Construction/Statistics/SettlementClock.lean`.
-/

namespace LogicalInduction

namespace PrefixPatchCompile

-- See the module header on `Nat.sqrt` opacity.
attribute [local irreducible] Nat.sqrt

/-! ### Variable-width freeze emission -/

/-- A polynomial quote-code lookup makes the parser-transparent prefix rewrite polynomial on
every polynomial raw source stream. -/
lemma freezeTokenRun_polySegStream {source : ℕ → List ℕ}
    (hsource : PolySegStream source) (quoteCode : ℕ → ℕ → ℕ) (cutoff : ℕ)
    {cq : Nat.Partrec.Code}
    (hquote : PolyFueled cq (fun z => quoteCode z.unpair.1 z.unpair.2)) :
    PolySegStream (fun n =>
      (EF.freezeTokenRun quoteCode cutoff (0, 0) (source n)).2) := by
  obtain ⟨ct, cl, tokenFn, lenFn, htoken, hlen, hslen, hget⟩ := hsource
  obtain ⟨ccontrol, hcontrol⟩ := freezeControlNat_polyFueled htoken
  have hmode := PolyFueled.left.comp hcontrol
  have hpending := PolyFueled.right.comp hcontrol
  have hquoteAt := hquote.comp (htoken.pair hpending)
  have hquoteAt' : PolyFueled _ (fun z =>
      quoteCode (tokenFn z) (freezeControlNat tokenFn z).unpair.2) :=
    hquoteAt.of_eq (fun z => by simp only [Nat.unpair_pair])
  have hshort : PolySegStream (fun z => [tokenFn z]) :=
    PolySegStream.ofTokenStream (PolyTokenStream.polyTok htoken)
  have hlong : PolySegStream (fun z => [tokenFn z, 1,
      quoteCode (tokenFn z) (freezeControlNat tokenFn z).unpair.2, 8]) := by
    exact PolySegStream.ofTokenStream
      (((PolyTokenStream.polyTok htoken).append (PolyTokenStream.const 1)).append
        ((PolyTokenStream.polyTok hquoteAt').append (PolyTokenStream.const 8)))
  obtain ⟨cmode, hmodeEq⟩ := polyFueled_eqConst hmode 2
  have hdayGap := subc_polyFueled.comp ((PolyFueled.const cutoff).pair htoken)
  have hdayGap' : PolyFueled _ (fun z => cutoff - tokenFn z) :=
    hdayGap.of_eq (fun z => by simp only [Nat.unpair_pair])
  have hday : PolySegStream (fun z =>
      if cutoff - tokenFn z = 0 then [tokenFn z]
      else [tokenFn z, 1,
        quoteCode (tokenFn z) (freezeControlNat tokenFn z).unpair.2, 8]) :=
    hshort.ifZero hlong hdayGap'
  have hsegmentRaw : PolySegStream (fun z =>
      if (if (freezeControlNat tokenFn z).unpair.1 = 2 then 1 else 0) = 0 then
        [tokenFn z]
      else if cutoff - tokenFn z = 0 then [tokenFn z]
      else [tokenFn z, 1,
        quoteCode (tokenFn z) (freezeControlNat tokenFn z).unpair.2, 8]) :=
    hshort.ifZero hday hmodeEq
  have hsegment : PolySegStream (fun z =>
      EF.freezeTokenEmit quoteCode cutoff
        ((freezeControlNat tokenFn z).unpair.1,
          (freezeControlNat tokenFn z).unpair.2) (tokenFn z)) :=
    hsegmentRaw.of_eq (fun z => by
      simp only [EF.freezeTokenEmit_eq]
      by_cases hm : (freezeControlNat tokenFn z).unpair.1 = 2
      · by_cases hd : tokenFn z < cutoff
        · have hgap : cutoff - tokenFn z ≠ 0 := by omega
          simp [hm, hd, hgap]
        · have hgap : cutoff - tokenFn z = 0 := Nat.sub_eq_zero_of_le (by omega)
          simp [hm, hd, hgap]
      · simp [hm])
  have hconcat := hsegment.concatVar hlen
  refine hconcat.of_eq (fun n => ?_)
  have hsourceEq : source n =
      (List.range (lenFn n)).map (fun j => tokenFn (Nat.pair n j)) := by
    apply List.ext_getElem
    · simp [hslen n]
    · intro i hleft hright
      rw [List.getElem_map]
      simp only [List.getElem_range]
      rw [hget n i (by simpa [hslen n] using hleft)]
      exact (List.getD_eq_getElem (l := source n) (d := 0) hleft).symm
  have hrun := congrArg Prod.snd
    (EF.freezeTokenRun_range quoteCode cutoff tokenFn n (lenFn n))
  simp only at hrun
  rw [hsourceEq]
  simpa [freezeControlNat] using hrun.symm

/-- Generic compiler theorem behind the concrete prefix patch: a polynomial encoded quote
lookup closes the administrative freeze under `EfficientlyComputableTok`. -/
lemma freezeBefore_preserves_ec
    (quote : ℕ → Sentence → ℚ) (quoteCode : ℕ → ℕ → ℕ) (cutoff : ℕ)
    (hquoteExact : ∀ day code φ, Encodable.decode (α := Sentence) code = some φ →
      quoteCode day code = Encodable.encode (quote day φ))
    {cq : Nat.Partrec.Code}
    (hquotePoly : PolyFueled cq (fun z => quoteCode z.unpair.1 z.unpair.2))
    (Tr : Trader) (hTr : EfficientlyComputableTok Tr) :
    EfficientlyComputableTok (Tr.freezeBefore quote cutoff) := by
  obtain ⟨lengthCode, tokenCode, a, k, hcert⟩ := hTr
  let raw : ℕ → List ℕ := fun n =>
    clockedTokens lengthCode tokenCode (ClockedEmission.ecClock a k n) n
  have hraw : PolySegStream raw :=
    ClockedEmission.clockedTokens_polySegStream lengthCode tokenCode a k
  have hfrozen : PolySegStream (fun n =>
      (EF.freezeTokenRun quoteCode cutoff (0, 0) (raw n)).2) :=
    freezeTokenRun_polySegStream hraw quoteCode cutoff hquotePoly
  apply hfrozen.ecTok (Tr.freezeBefore quote cutoff)
  intro n
  have hcomm := EF.strategyOfTokens_freezeTokenRun_trades quote quoteCode cutoff n
    hquoteExact (raw n)
  simp only at hcomm
  have horig : strategyOfTokens n (raw n) = Tr.strat n := by
    have hs := congrFun (congrArg Trader.strat hcert) n
    exact hs
  rw [congrArg Strategy.trades horig] at hcomm
  have htrades :
      (strategyOfTokens n
        (EF.freezeTokenRun quoteCode cutoff (0, 0) (raw n)).2).trades =
        ((Tr.freezeBefore quote cutoff).strat n).trades := by
    simpa [Trader.freezeBefore, Trader.freezeOn, Strategy.freezeBefore,
      Strategy.freezeOn, EF.freezeBefore] using hcomm
  cases hleft : strategyOfTokens n
      (EF.freezeTokenRun quoteCode cutoff (0, 0) (raw n)).2 with
  | mk leftTrades leftRank =>
      cases hright : (Tr.freezeBefore quote cutoff).strat n with
      | mk rightTrades rightRank =>
          simp only [hleft, hright] at htrades ⊢
          subst rightTrades
          rfl

/-! ### Finite LIA prefix lookup -/

/-- Decide whether an arbitrary raw sentence token decodes to one fixed sentence.  Unlike
comparison with `Encodable.encode`, this accepts every noncanonical token accepted by the
Foundation decoder. -/
def sentenceMatches : Sentence → ℕ → ℕ
  | ⊥, code =>
      if code = 0 then 0
      else if code.pred.unpair.1 = 0 then 1 else 0
  | .atom a, code =>
      if code = 0 then 0
      else if code.pred.unpair.1 = 1 then
        if code.pred.unpair.2 = a then 1 else 0
      else 0
  | φ 🡒 ψ, code =>
      if code = 0 then 0
      else if code.pred.unpair.1 = 2 then
        sentenceMatches φ code.pred.unpair.2.unpair.1 *
          sentenceMatches ψ code.pred.unpair.2.unpair.2
      else 0
  | φ ⋏ ψ, code =>
      if code = 0 then 0
      else if code.pred.unpair.1 = 3 then
        sentenceMatches φ code.pred.unpair.2.unpair.1 *
          sentenceMatches ψ code.pred.unpair.2.unpair.2
      else 0
  | φ ⋎ ψ, code =>
      if code = 0 then 0
      else if code.pred.unpair.1 = 4 then
        sentenceMatches φ code.pred.unpair.2.unpair.1 *
          sentenceMatches ψ code.pred.unpair.2.unpair.2
      else 0

lemma sentenceMatches_eq_one_iff (target : Sentence) (code : ℕ) :
    sentenceMatches target code = 1 ↔
      Encodable.decode (α := Sentence) code = some target := by
  induction target using LO.Propositional.Formula.rec' generalizing code with
  | hfalsum =>
      cases code with
      | zero => simp [sentenceMatches, decode_sentence_eq_ofNat,
          LO.Propositional.Formula.ofNat]
      | succ e =>
          rcases htag : e.unpair.1 with _ | tag
          · simp [sentenceMatches, decode_sentence_eq_ofNat,
              LO.Propositional.Formula.ofNat, htag]
          · rcases tag with _ | _ | _ | _ | tag <;>
              simp [sentenceMatches, decode_sentence_eq_ofNat,
                LO.Propositional.Formula.ofNat, htag, Option.bind_eq_some_iff]
  | hatom a =>
      cases code with
      | zero => simp [sentenceMatches, decode_sentence_eq_ofNat,
          LO.Propositional.Formula.ofNat]
      | succ e =>
          rcases htag : e.unpair.1 with _ | _ | tag
          · simp [sentenceMatches, decode_sentence_eq_ofNat,
              LO.Propositional.Formula.ofNat, htag]
          · simp [sentenceMatches, decode_sentence_eq_ofNat,
              LO.Propositional.Formula.ofNat, htag]
          · rcases tag with _ | _ | _ | tag <;>
              simp [sentenceMatches, decode_sentence_eq_ofNat,
                LO.Propositional.Formula.ofNat, htag, Option.bind_eq_some_iff]
  | himp φ ψ ihφ ihψ =>
      cases code with
      | zero => simp [sentenceMatches, decode_sentence_eq_ofNat,
          LO.Propositional.Formula.ofNat]
      | succ e =>
          rcases htag : e.unpair.1 with _ | _ | _ | tag
          · simp [sentenceMatches, decode_sentence_eq_ofNat,
              LO.Propositional.Formula.ofNat, htag]
          · simp [sentenceMatches, decode_sentence_eq_ofNat,
              LO.Propositional.Formula.ofNat, htag]
          · simp [sentenceMatches, decode_sentence_eq_ofNat,
              LO.Propositional.Formula.ofNat, htag, ihφ, ihψ,
              Option.bind_eq_some_iff]
            cases hleft : LO.Propositional.Formula.ofNat (α := ℕ) e.unpair.2.unpair.1 <;>
              cases hright : LO.Propositional.Formula.ofNat (α := ℕ)
                e.unpair.2.unpair.2 <;>
              simp [LO.Propositional.Formula.imp_inj]
          · rcases tag with _ | _ | tag <;>
              simp [sentenceMatches, decode_sentence_eq_ofNat,
                LO.Propositional.Formula.ofNat, htag, Option.bind_eq_some_iff]
  | hand φ ψ ihφ ihψ =>
      cases code with
      | zero => simp [sentenceMatches, decode_sentence_eq_ofNat,
          LO.Propositional.Formula.ofNat]
      | succ e =>
          rcases htag : e.unpair.1 with _ | _ | _ | _ | tag
          · simp [sentenceMatches, decode_sentence_eq_ofNat,
              LO.Propositional.Formula.ofNat, htag]
          · simp [sentenceMatches, decode_sentence_eq_ofNat,
              LO.Propositional.Formula.ofNat, htag]
          · simp [sentenceMatches, decode_sentence_eq_ofNat,
              LO.Propositional.Formula.ofNat, htag, Option.bind_eq_some_iff]
          · simp [sentenceMatches, decode_sentence_eq_ofNat,
              LO.Propositional.Formula.ofNat, htag, ihφ, ihψ]
            cases hleft : LO.Propositional.Formula.ofNat (α := ℕ) e.unpair.2.unpair.1 <;>
              cases hright : LO.Propositional.Formula.ofNat (α := ℕ)
                e.unpair.2.unpair.2 <;>
              simp [LO.Propositional.Formula.and_inj]
          · rcases tag with _ | tag <;>
              simp [sentenceMatches, decode_sentence_eq_ofNat,
                LO.Propositional.Formula.ofNat, htag, Option.bind_eq_some_iff]
  | hor φ ψ ihφ ihψ =>
      cases code with
      | zero => simp [sentenceMatches, decode_sentence_eq_ofNat,
          LO.Propositional.Formula.ofNat]
      | succ e =>
          rcases htag : e.unpair.1 with _ | _ | _ | _ | _ | tag
          · simp [sentenceMatches, decode_sentence_eq_ofNat,
              LO.Propositional.Formula.ofNat, htag]
          · simp [sentenceMatches, decode_sentence_eq_ofNat,
              LO.Propositional.Formula.ofNat, htag]
          · simp [sentenceMatches, decode_sentence_eq_ofNat,
              LO.Propositional.Formula.ofNat, htag, Option.bind_eq_some_iff]
          · simp [sentenceMatches, decode_sentence_eq_ofNat,
              LO.Propositional.Formula.ofNat, htag, Option.bind_eq_some_iff]
          · simp [sentenceMatches, decode_sentence_eq_ofNat,
              LO.Propositional.Formula.ofNat, htag, ihφ, ihψ]
            cases hleft : LO.Propositional.Formula.ofNat (α := ℕ) e.unpair.2.unpair.1 <;>
              cases hright : LO.Propositional.Formula.ofNat (α := ℕ)
                e.unpair.2.unpair.2 <;>
              simp [LO.Propositional.Formula.or_inj]
          · simp [sentenceMatches, decode_sentence_eq_ofNat,
              LO.Propositional.Formula.ofNat, htag]

/-- The binary-node case of `sentenceMatches_polyFueled`, shared by the three connectives:
the matcher at a node with tag `tag` is a zero test on the code, a tag comparison, and the
product of the two child matchers. -/
private lemma sentenceMatchesBinary_polyFueled (tag : ℕ) {φ ψ : Sentence}
    (ihφ : ∃ c, PolyFueled c (sentenceMatches φ))
    (ihψ : ∃ c, PolyFueled c (sentenceMatches ψ)) :
    ∃ c, PolyFueled c (fun code =>
      if code = 0 then 0
      else if code.pred.unpair.1 = tag then
        sentenceMatches φ code.pred.unpair.2.unpair.1 *
          sentenceMatches ψ code.pred.unpair.2.unpair.2
      else 0) := by
  obtain ⟨cmul, hmul⟩ := mul_polyFueled
  have hpred := predc_polyFueled
  have htag := PolyFueled.left.comp hpred
  have hpayload := PolyFueled.right.comp hpred
  obtain ⟨cφ, hφ⟩ := ihφ
  obtain ⟨cψ, hψ⟩ := ihψ
  have hleft := hφ.comp (PolyFueled.left.comp hpayload)
  have hright := hψ.comp (PolyFueled.right.comp hpayload)
  have hproduct := hmul.comp (hleft.pair hright)
  have hproduct' : PolyFueled _ (fun code =>
      sentenceMatches φ code.pred.unpair.2.unpair.1 *
        sentenceMatches ψ code.pred.unpair.2.unpair.2) :=
    hproduct.of_eq (fun code => by simp only [Nat.unpair_pair])
  obtain ⟨ctag, htagEq⟩ := polyFueled_eqConst htag tag
  obtain ⟨cbody, hbody⟩ := polyFueled_ifZero htagEq (PolyFueled.const 0) hproduct'
  obtain ⟨c, hc⟩ := polyFueled_ifZero PolyFueled.id (PolyFueled.const 0) hbody
  exact ⟨c, hc.of_eq (fun code => by
    by_cases hz : code = 0
    · simp [hz]
    · by_cases ht : code.pred.unpair.1 = tag <;> simp [hz])⟩

lemma sentenceMatches_polyFueled (target : Sentence) :
    ∃ c, PolyFueled c (sentenceMatches target) := by
  induction target using LO.Propositional.Formula.rec' with
  | hfalsum =>
      have htag := PolyFueled.left.comp predc_polyFueled
      obtain ⟨ceq, heq⟩ := polyFueled_eqConst htag 0
      obtain ⟨c, hc⟩ := polyFueled_ifZero PolyFueled.id (PolyFueled.const 0) heq
      exact ⟨c, hc.of_eq (fun code => by simp [sentenceMatches])⟩
  | hatom a =>
      have hpred := predc_polyFueled
      have htag := PolyFueled.left.comp hpred
      have hpayload := PolyFueled.right.comp hpred
      obtain ⟨cpayload, hpayloadEq⟩ := polyFueled_eqConst hpayload a
      obtain ⟨ctag, htagEq⟩ := polyFueled_eqConst htag 1
      obtain ⟨cbody, hbody⟩ := polyFueled_ifZero htagEq (PolyFueled.const 0) hpayloadEq
      obtain ⟨c, hc⟩ := polyFueled_ifZero PolyFueled.id (PolyFueled.const 0) hbody
      exact ⟨c, hc.of_eq (fun code => by simp [sentenceMatches])⟩
  | himp φ ψ ihφ ihψ =>
      obtain ⟨c, hc⟩ := sentenceMatchesBinary_polyFueled 2 ihφ ihψ
      exact ⟨c, hc.of_eq (fun code => by simp [sentenceMatches])⟩
  | hand φ ψ ihφ ihψ =>
      obtain ⟨c, hc⟩ := sentenceMatchesBinary_polyFueled 3 ihφ ihψ
      exact ⟨c, hc.of_eq (fun code => by simp [sentenceMatches])⟩
  | hor φ ψ ihφ ihψ =>
      obtain ⟨c, hc⟩ := sentenceMatchesBinary_polyFueled 4 ihφ ihψ
      exact ⟨c, hc.of_eq (fun code => by simp [sentenceMatches])⟩

lemma sentenceMatches_le_one (target : Sentence) (code : ℕ) :
    sentenceMatches target code ≤ 1 := by
  induction target using LO.Propositional.Formula.rec' generalizing code with
  | hfalsum =>
      cases code with
      | zero => simp [sentenceMatches]
      | succ e =>
          simp only [sentenceMatches, Nat.succ_ne_zero, if_false, Nat.pred_succ]
          split <;> omega
  | hatom a =>
      cases code with
      | zero => simp [sentenceMatches]
      | succ e =>
          simp only [sentenceMatches, Nat.succ_ne_zero, if_false, Nat.pred_succ]
          by_cases htag : e.unpair.1 = 1
          · by_cases hpayload : e.unpair.2 = a <;> simp [htag, hpayload]
          · simp [htag]
  | himp φ ψ ihφ ihψ | hand φ ψ ihφ ihψ | hor φ ψ ihφ ihψ =>
      cases code with
      | zero => simp [sentenceMatches]
      | succ e =>
          simp only [sentenceMatches, Nat.succ_ne_zero, if_false, Nat.pred_succ]
          split
          · nlinarith [ihφ e.unpair.2.unpair.1, ihψ e.unpair.2.unpair.2]
          · omega

lemma sentenceMatches_eq_zero_iff (target : Sentence) (code : ℕ) :
    sentenceMatches target code = 0 ↔
      Encodable.decode (α := Sentence) code ≠ some target := by
  constructor
  · intro hzero hdecode
    have hone := (sentenceMatches_eq_one_iff target code).mpr hdecode
    omega
  · intro hdecode
    have hne : sentenceMatches target code ≠ 1 :=
      fun hone => hdecode ((sentenceMatches_eq_one_iff target code).mp hone)
    have hle := sentenceMatches_le_one target code
    omega

/-- Encoded exact lookup in one fixed rational-belief entry list. -/
def encodedQuoteFromEntries : List (Sentence × ℚ) → ℕ → ℕ
  | [], _ => Encodable.encode (0 : ℚ)
  | (target, q) :: entries, code =>
      if sentenceMatches target code = 0 then encodedQuoteFromEntries entries code
      else Encodable.encode q

private lemma encodedQuoteFromEntries_exact
    (entries : List (Sentence × ℚ)) (code : ℕ) (target : Sentence)
    (hdecode : Encodable.decode (α := Sentence) code = some target) :
    encodedQuoteFromEntries entries code =
      Encodable.encode (quoteFromEntries entries target) := by
  induction entries with
  | nil => simp [encodedQuoteFromEntries, quoteFromEntries]
  | cons entry entries ih =>
      rcases entry with ⟨ψ, q⟩
      by_cases htarget : target = ψ
      · subst ψ
        have hone := (sentenceMatches_eq_one_iff target code).mpr hdecode
        simp [encodedQuoteFromEntries, quoteFromEntries, hone]
      · have hdecNe : Encodable.decode (α := Sentence) code ≠ some ψ := by
          rw [hdecode]
          simpa using htarget
        have hzero := (sentenceMatches_eq_zero_iff ψ code).mpr hdecNe
        simp [encodedQuoteFromEntries, quoteFromEntries, htarget, hzero, ih]

private lemma encodedQuoteFromEntries_polyFueled
    (entries : List (Sentence × ℚ)) :
    ∃ c, PolyFueled c (encodedQuoteFromEntries entries) := by
  induction entries with
  | nil => exact ⟨_, PolyFueled.const (Encodable.encode (0 : ℚ))⟩
  | cons entry entries ih =>
      rcases entry with ⟨target, q⟩
      obtain ⟨cmatch, hmatch⟩ := sentenceMatches_polyFueled target
      obtain ⟨crest, hrest⟩ := ih
      obtain ⟨c, hc⟩ := polyFueled_ifZero hmatch hrest
        (PolyFueled.const (Encodable.encode q))
      exact ⟨c, hc.of_eq (fun code => by simp [encodedQuoteFromEntries])⟩

/-- Quote from the state at one fixed position of a finite belief-state prefix, with zero
after the end of the prefix. -/
def prefixQuoteFromStates : List RationalBeliefState → ℕ → Sentence → ℚ
  | [], _, _ => 0
  | state :: _, 0, φ => state.quote φ
  | _ :: states, day + 1, φ => prefixQuoteFromStates states day φ

/-- Raw-code form of `prefixQuoteFromStates`.  Each fixed state uses the exhaustive decoder
matcher above, so noncanonical sentence tokens receive the same quote as canonical ones. -/
def encodedPrefixQuoteFromStates : List RationalBeliefState → ℕ → ℕ → ℕ
  | [], _, _ => Encodable.encode (0 : ℚ)
  | state :: _, 0, code => encodedQuoteFromEntries state.entries code
  | _ :: states, day + 1, code => encodedPrefixQuoteFromStates states day code

lemma encodedPrefixQuoteFromStates_exact
    (states : List RationalBeliefState) (day code : ℕ) (φ : Sentence)
    (hdecode : Encodable.decode (α := Sentence) code = some φ) :
    encodedPrefixQuoteFromStates states day code =
      Encodable.encode (prefixQuoteFromStates states day φ) := by
  induction states generalizing day with
  | nil => simp [encodedPrefixQuoteFromStates, prefixQuoteFromStates]
  | cons state states ih =>
      cases day with
      | zero =>
          simpa [encodedPrefixQuoteFromStates, prefixQuoteFromStates,
            RationalBeliefState.quote] using
            encodedQuoteFromEntries_exact state.entries code φ hdecode
      | succ day =>
          simpa [encodedPrefixQuoteFromStates, prefixQuoteFromStates] using ih day

lemma encodedPrefixQuoteFromStates_polyFueled
    (states : List RationalBeliefState) :
    ∃ c, PolyFueled c (fun z =>
      encodedPrefixQuoteFromStates states z.unpair.1 z.unpair.2) := by
  induction states with
  | nil => exact ⟨_, PolyFueled.const (Encodable.encode (0 : ℚ))⟩
  | cons state states ih =>
      obtain ⟨centry, hentry⟩ := encodedQuoteFromEntries_polyFueled state.entries
      obtain ⟨crest, hrest⟩ := ih
      have hdayZero := hentry.comp PolyFueled.right
      have hdaySucc := hrest.comp
        ((predc_polyFueled.comp PolyFueled.left).pair PolyFueled.right)
      obtain ⟨c, hc⟩ := polyFueled_ifZero PolyFueled.left hdayZero hdaySucc
      refine ⟨c, hc.of_eq (fun z => ?_)⟩
      cases hday : z.unpair.1 with
      | zero =>
          simp [encodedPrefixQuoteFromStates]
      | succ day =>
          simp [encodedPrefixQuoteFromStates]

private lemma prefixQuoteFromStates_eq_getD
    (states : List RationalBeliefState) (fallback : RationalBeliefState)
    {day : ℕ} (hday : day < states.length) (φ : Sentence) :
    prefixQuoteFromStates states day φ = (states.getD day fallback).quote φ := by
  induction states generalizing day with
  | nil => simp at hday
  | cons state states ih =>
      cases day with
      | zero => simp [prefixQuoteFromStates]
      | succ day =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at hday
          simpa [prefixQuoteFromStates] using ih hday

/-- The finite rational quote table used by the LIA prefix patch. -/
noncomputable def liaPrefixQuote (DP : DeductiveProcess) (cutoff : ℕ) :
    ℕ → Sentence → ℚ :=
  prefixQuoteFromStates (liaStatePrefix DP cutoff)

/-- Polynomial raw-code implementation of `liaPrefixQuote`. -/
noncomputable def liaPrefixQuoteCode (DP : DeductiveProcess) (cutoff : ℕ) :
    ℕ → ℕ → ℕ :=
  encodedPrefixQuoteFromStates (liaStatePrefix DP cutoff)

/-- **Soundness of the prefix patch.**  On every day before the cutoff, the finite frozen
table reproduces the LIA's own belief state, so overwriting a trader's quotes there changes
nothing the trader could observe.  This is the semantic fact behind
`liaFreezeBefore_preserves_ecTok`, whose own content is the token-level efficiency claim. -/
lemma liaPrefixQuote_exact (DP : DeductiveProcess) (cutoff : ℕ)
    (day : ℕ) (hday : day < cutoff) (φ : Sentence) :
    liaHistory DP day φ = (liaPrefixQuote DP cutoff day φ : ℝ) := by
  have hprefix :
      liaPrefixQuote DP cutoff day φ = (liaStates DP day).quote φ := by
    rw [liaPrefixQuote,
      prefixQuoteFromStates_eq_getD (liaStatePrefix DP cutoff) (liaStates DP 0)
        (by simpa [liaStatePrefix_length] using hday) φ,
      liaStatePrefix_getD DP hday]
  simp [liaHistory, RationalBeliefState.toValuation, hprefix]

lemma liaPrefixQuoteCode_exact (DP : DeductiveProcess) (cutoff day code : ℕ)
    (φ : Sentence) (hdecode : Encodable.decode (α := Sentence) code = some φ) :
    liaPrefixQuoteCode DP cutoff day code =
      Encodable.encode (liaPrefixQuote DP cutoff day φ) := by
  exact encodedPrefixQuoteFromStates_exact (liaStatePrefix DP cutoff) day code φ hdecode

lemma liaPrefixQuoteCode_polyFueled (DP : DeductiveProcess) (cutoff : ℕ) :
    ∃ c, PolyFueled c (fun z =>
      liaPrefixQuoteCode DP cutoff z.unpair.1 z.unpair.2) :=
  encodedPrefixQuoteFromStates_polyFueled (liaStatePrefix DP cutoff)

end PrefixPatchCompile

/-! ## The paper-facing freeze endpoint -/

/-- **Concrete finite-prefix compiler, token-level content.**  The LIA's first `cutoff`
rational belief states form a fixed finite table; exhaustive raw sentence matching and the
flat administrative freeze transducer compile that table into a polynomial token emitter,
preserving token-model efficient computability.  That the table reproduces `liaHistory`
before the cutoff is `PrefixPatchCompile.liaPrefixQuote_exact`.

Disclosed boundary (`dd:fuel`): the collapsed `EfficientPrefixPatch.preserves_ec` asks for
token-metered preservation, so this token-model fact does not package into that structure.
The RPN freeze transducer is constructed (`Compiler.lean`), but its fuel certificate needs
a decode test on exponentially large escape codes, and the digit model cannot express it:
`BigDigits` is closed under an operation only when that operation's base-4 digit recurrence
has a poly-bounded carry, and the escape test reduces to `Nat.unpair` / integer square
root, whose carry is the partial remainder — `Θ(len)` digits wide.  The digit model is thus
closed under the forward big-value operations and open under their inverses.  So there is
no LIA inhabitant at the collapsed class, and this token-level fact is the boundary's
constructed content.
Paper node: `def:lia` -/
theorem liaFreezeBefore_preserves_ecTok (DP : DeductiveProcess) (cutoff : ℕ) :
    ∀ Tr : Trader, EfficientlyComputableTok Tr →
      EfficientlyComputableTok
        (Tr.freezeBefore (PrefixPatchCompile.liaPrefixQuote DP cutoff) cutoff) := by
  intro Tr hTr
  obtain ⟨cq, hquotePoly⟩ :=
    PrefixPatchCompile.liaPrefixQuoteCode_polyFueled DP cutoff
  exact PrefixPatchCompile.freezeBefore_preserves_ec
    (PrefixPatchCompile.liaPrefixQuote DP cutoff)
    (PrefixPatchCompile.liaPrefixQuoteCode DP cutoff) cutoff
    (PrefixPatchCompile.liaPrefixQuoteCode_exact DP cutoff)
    hquotePoly Tr hTr


end LogicalInduction
