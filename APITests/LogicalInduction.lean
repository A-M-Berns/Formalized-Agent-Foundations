import LogicalInduction.API

/-!
# Client-style smoke tests for `LogicalInduction.API`

A downstream researcher's session, in order: build a trader, certify it efficient, use the
criterion to conclude it cannot exploit the market, read a §4 property off that market,
condition the inductor, and transport the criterion across a corrected finite-support
perturbation.  Then the rest of the documented interface: the certificate kit an exploiting
trader is assembled from, the exploitation engines and indicator toolkit that prove it
exploits, the shared asymptotic algebra, the convergence and non-dogmatism forms with their
side conditions discharged, hypothesis-free conditioning, return on investment, the
constructed data (`CEEnumeration`, `ComputableHorizon`, `PresentedLUVSeq`, the LUV lanes,
the statistical capstones) that arrives with the same import, and the §4.9–4.10 family
instantiated at `𝗣𝗔` with every binder discharged by instance search.

The last section is a roll-call over all 107 endpoints `AxiomAudit.lean` publishes: the API
documentation claims each resolves from this import and gives its address, and elaborating
the names here is what makes that claim fail the build rather than merely age.

Everything here imports `LogicalInduction.API` and nothing else — no machine, compiler or
parser internals, and no deeper import, because there is none — and uses the API's objects
rather than restating its endpoints.
-/

namespace APITests.LogicalInduction

open _root_.LogicalInduction

/-! ## 1. Building traders and portfolios -/

/-- A client-defined trader that buys one share of the same sentence every day. -/
def buyOneDaily (φ : Sentence) : Trader where
  strat n :=
    { trades := [(EF.const 1, φ)]
      rank_le := by simp }

example (φ : Sentence) (n : ℕ) : ((buyOneDaily φ).strat n).trades = [(EF.const 1, φ)] :=
  rfl

/-- Extensionality lets client transformations prove trader equality without touching the
proof field inside each strategy. -/
example (T U : Trader) (h : ∀ n, T.strat n = U.strat n) : T = U := by
  apply Trader.ext
  exact funext h

example (DP DQ : DeductiveProcess) (h : DP.D = DQ.D) : DP = DQ :=
  DeductiveProcess.ext h

example (X Y : LUV) (h : X.gt = Y.gt) : X = Y :=
  LUV.ext h

def constantPortfolio : AffineCombination where
  const := EF.const 2
  terms := []

example (V : History) (w : Valuation) : constantPortfolio.value V w = 2 := by
  simp [constantPortfolio, AffineCombination.value]

/-! ## 2. Certifying the trader, and landing in the paper's class

The certificate calculus discharges `EfficientlyComputable` compositionally; the single
bridge `EfficientlyComputable.toMachine` lands it in `def:ec`'s machine class.  No
`Complexity.FP` witness is written by hand, and no clocked-code construction is exposed. -/

/-- The client's trader is efficiently computable — fully discharged, no hypotheses. -/
lemma buyOneDaily_efficientlyComputable (φ : Sentence) :
    EfficientlyComputable (buyOneDaily φ) :=
  EfficientlyComputable.ofSingleTradeBlocksBig _ (fun _ => EF.const 1) (fun _ => φ)
    (PolySegStream.ofTokenStream (PolyTokenStream.serialize_const 1))
    (fun _ => trivial)
    (BigSentenceCodes.const φ)
    (fun _ => rfl)

/-- …and therefore polynomial-time in the paper's own sense. -/
lemma buyOneDaily_machineEfficient (φ : Sentence) :
    MachineEfficientTrader (buyOneDaily φ) :=
  (buyOneDaily_efficientlyComputable φ).toMachine

/-- The bridge, in general. -/
example (T : Trader) (h : EfficientlyComputable T) : MachineEfficientTrader T :=
  h.toMachine

/-- A constant sentence family is certified without exposing the emission machinery. -/
example (φ : Sentence) : BigSentenceCodes (fun _ => φ) :=
  BigSentenceCodes.const φ

/-! ## 3. The criterion at the paper's own quantifier -/

/-- The payoff of the certification: over any machine logical inductor, the client's own
trader provably cannot exploit the market. -/
example (P : History) (DP : DeductiveProcess) [IsMachineLogicalInductor P DP] (φ : Sentence) :
    ¬ (buyOneDaily φ).Exploits P DP :=
  IsMachineLogicalInductor.noExploit (P := P) (DP := DP) _ (buyOneDaily_machineEfficient φ)

/-- A client holding a `Complexity.FP` witness directly uses it directly. -/
example (P : History) (DP : DeductiveProcess) [IsMachineLogicalInductor P DP]
    (T : Trader) (hT : MachineEfficientTrader T) : ¬ T.Exploits P DP :=
  IsMachineLogicalInductor.noExploit (P := P) (DP := DP) T hT

/-- The compatibility instance carries the §4 tail to the machine class, with no side
condition. -/
example (P : History) (DP : DeductiveProcess) [IsMachineLogicalInductor P DP] :
    IsLogicalInductor P DP :=
  inferInstance

example (P : History) (DP : DeductiveProcess) [IsMachineLogicalInductor P DP]
    (n : ℕ) (φ : Sentence) : 0 ≤ P n φ ∧ P n φ ≤ 1 :=
  IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ

/-! ## 4. A standard §4 theorem, used at the machine class

`lic_lex_tendsto_zero` is stated in the library against `[IsLogicalInductor …]`, and applies
at a *machine* logical inductor without restatement: provably equivalent sentences have
converging prices. -/

example (P : History) (DP : DeductiveProcess) [IsMachineLogicalInductor P DP]
    (φ ψ : Sentence) (h1 : ∀ n, (∼φ ⋎ ψ) ∈ DP.D n) (h2 : ∀ n, (∼ψ ⋎ φ) ∈ DP.D n)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ConvergesTo (fun n => P n φ - P n ψ) 0 :=
  lic_lex_tendsto_zero P DP φ ψ h1 h2 hcons

/-! ## 5. Conditioning an inductor

Given the conditioning data, a client conditions a machine logical inductor and reads a §4
property off the conditioned market.

The conditioning data is assembled from a **write-out** condition certificate —
`BigSentenceCodes`, `def:ec`'s own class, which meters how many digits a polynomial-time
writer must emit and bounds no token's value, so a condition's Gödel code may be
exponential in the day.  Nothing on this path meters a sentence code. -/

/-- A client's conditioning presentation, built from write-out condition data. -/
def clientPresentation {DP extra : DeductiveProcess} (ψ : ℕ → Sentence)
    (hψ : BigSentenceCodes ψ)
    (hholds : ∀ n (v : PCWorld), v.Holds (ψ n) ↔ v.ConsistentWith (extra.D n))
    (hcomb : ComputableDeductiveProcess (DP.union extra)) :
    ConditioningPresentation DP extra where
  condition := ψ
  condition_codes := hψ
  holds_condition := hholds
  combined_computable := hcomb

/-- Conditioning on a write-out condition family, end to end: the client supplies only a
`BigSentenceCodes` certificate and the compiler for the presentation it builds, and reads a
§4 convergence property off the conditioned market. -/
example (P : History) (DP extra : DeductiveProcess) [IsMachineLogicalInductor P DP]
    (ψc : ℕ → Sentence) (hψc : BigSentenceCodes ψc)
    (hholds : ∀ n (v : PCWorld), v.Holds (ψc n) ↔ v.ConsistentWith (extra.D n))
    (hcomb : ComputableDeductiveProcess (DP.union extra))
    (compiler : ConditioningTraderCompiler P DP extra
      (clientPresentation ψc hψc hholds hcomb))
    (φ ψ : Sentence)
    (h1 : ∀ n, (∼φ ⋎ ψ) ∈ (DP.union extra).D n)
    (h2 : ∀ n, (∼ψ ⋎ φ) ∈ (DP.union extra).D n)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((DP.union extra).D n)) :
    ConvergesTo (fun n => conditionedHistory P ψc n φ
      - conditionedHistory P ψc n ψ) 0 := by
  -- The ascription is load-bearing: without it the local instance's type mentions
  -- `(clientPresentation ψc hψc hholds hcomb).condition` rather than `ψc`, and instance
  -- search does not unfold a plain `def` to see they agree.
  haveI : IsMachineLogicalInductor (conditionedHistory P ψc) (DP.union extra) :=
    lic_conditioned_machine P DP extra
      (clientPresentation ψc hψc hholds hcomb) compiler
  exact lic_lex_tendsto_zero _ _ φ ψ h1 h2 hcons

example (P : History) (DP extra : DeductiveProcess) [IsMachineLogicalInductor P DP]
    (C : ConditioningPresentation DP extra)
    (compiler : ConditioningTraderCompiler P DP extra C)
    (φ ψ : Sentence)
    (h1 : ∀ n, (∼φ ⋎ ψ) ∈ (DP.union extra).D n)
    (h2 : ∀ n, (∼ψ ⋎ φ) ∈ (DP.union extra).D n)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((DP.union extra).D n)) :
    ConvergesTo
      (fun n => conditionedHistory P C.condition n φ
        - conditionedHistory P C.condition n ψ) 0 := by
  haveI := lic_conditioned_machine P DP extra C compiler
  exact lic_lex_tendsto_zero _ _ φ ψ h1 h2 hcons

/-! ## 6. Transporting the criterion across a corrected finite perturbation

The published finite-perturbation theorem is false.  What a client may use is the
finite-*support* correction `lic_iff_of_recognizableSupportPerturbation`: move one price at a
recognizable coordinate, transport the criterion, and read a §4 property off the *perturbed*
market — a market the client built, not one this repository constructs. -/

/-- A client's own one-coordinate perturbation, presented as the theorem's hypothesis. -/
lemma recognizableSupport_of_singleAtom {P P' : History}
    (hagree : ∀ d φ, (d, φ) ≠ (0, (LO.Propositional.Formula.atom 0 : Sentence)) →
      P d φ = P' d φ) :
    RecognizableSupportPerturbation P P' := by
  refine ⟨{(0, (LO.Propositional.Formula.atom 0 : Sentence))}, ?_, fun d φ hmem => hagree d φ ?_⟩
  · intro p hp
    simp only [Finset.mem_singleton] at hp
    subst hp
    exact recognizable_atom 0 atom_zero_noReserved
  · intro hc
    exact hmem (by simp [hc])

/-- **Composition.**  Moving a single price preserves the criterion at the paper's own
quantifier, so every §4 consequence holds of the perturbed market too.  Nothing but the
corrected `thm:ifp` gets us from `P` to `P'` here. -/
example (P P' : History) (DP : DeductiveProcess) [hP : IsMachineLogicalInductor P DP]
    (hP'comp : ComputableMarket P')
    (hagree : ∀ d φ, (d, φ) ≠ (0, (LO.Propositional.Formula.atom 0 : Sentence)) →
      P d φ = P' d φ)
    (φ ψ : Sentence) (h1 : ∀ n, (∼φ ⋎ ψ) ∈ DP.D n) (h2 : ∀ n, (∼ψ ⋎ φ) ∈ DP.D n)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ConvergesTo (fun n => P' n φ - P' n ψ) 0 := by
  have hP' : IsMachineLogicalInductor P' DP :=
    (lic_iff_of_recognizableSupportPerturbation P P' DP
      hP.marketComputable hP'comp (recognizableSupport_of_singleAtom hagree)).mp hP
  exact lic_lex_tendsto_zero P' DP φ ψ h1 h2 hcons

/-- Finite support is strictly stronger than the paper's tail agreement, and the API exposes
the implication a client needs to see that. -/
example (P P' : History) (h : RecognizableSupportPerturbation P P') :
    ∃ N : ℕ, ∀ d, N ≤ d → ∀ ψ, P d ψ = P' d ψ :=
  h.toFiniteSupport.tail_agree

/-! ### A coordinate the previous endpoint could not reach

The moved sentence here has a `⊥` subformula, so it fails `BotFree` and no
`RecognizableSupportPerturbation` can name it.  `NoReservedSupportPerturbation` can, which
is what makes the strengthening visible from the client side rather than only in the
statement. -/

/-- The client's own target: `atom 0 ⋏ ⊥`. -/
private def clientBotSentence : Sentence := (LO.Propositional.Formula.atom 0 : Sentence) ⋏ ⊥

/-- It is **not** recognizable — the old hypothesis is unavailable at this coordinate. -/
example : ¬ BotFree clientBotSentence := by
  intro h
  exact botFree_falsum ((botFree_and _ _).mp h).2

/-- A client's own one-coordinate perturbation at that sentence. -/
lemma noReservedSupport_of_singleBotSentence {P P' : History}
    (hagree : ∀ d φ, (d, φ) ≠ (0, clientBotSentence) → P d φ = P' d φ) :
    NoReservedSupportPerturbation P P' := by
  refine ⟨{(0, clientBotSentence)}, ?_, fun d φ hmem => hagree d φ ?_⟩
  · intro q hq
    simp only [Finset.mem_singleton] at hq
    subst hq
    rw [clientBotSentence, noReserved_and]
    exact ⟨atom_zero_noReserved, noReserved_falsum⟩
  · intro hc
    exact hmem (by simp [hc])

/-- **Composition, at the harder coordinate.**  Same client-side reasoning as above, on a
sentence the previous endpoint's hypothesis cannot express. -/
example (P P' : History) (DP : DeductiveProcess) [hP : IsMachineLogicalInductor P DP]
    (hP'comp : ComputableMarket P')
    (hagree : ∀ d φ, (d, φ) ≠ (0, clientBotSentence) → P d φ = P' d φ)
    (φ ψ : Sentence) (h1 : ∀ n, (∼φ ⋎ ψ) ∈ DP.D n) (h2 : ∀ n, (∼ψ ⋎ φ) ∈ DP.D n)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ConvergesTo (fun n => P' n φ - P' n ψ) 0 := by
  have hP' : IsMachineLogicalInductor P' DP :=
    (lic_iff_of_noReservedSupportPerturbation P P' DP
      hP.marketComputable hP'comp (noReservedSupport_of_singleBotSentence hagree)).mp hP
  exact lic_lex_tendsto_zero P' DP φ ψ h1 h2 hcons

/-! ### A coordinate no syntactic hypothesis can reach

The moved sentence here is a **reserved atom**, `atom (Nat.pair 5 (Nat.pair 0 0))`.  It
fails `NoReserved`, so neither `RecognizableSupportPerturbation` nor
`NoReservedSupportPerturbation` can name this coordinate — a run may denote it through a
structured paper-prime block whose unary length field is unbounded.  Plain
`FiniteSupportPerturbation` names it, and that is the whole hypothesis. -/

/-- The client's own target: a reserved atom. -/
private def clientReservedSentence : Sentence :=
  LO.Propositional.Formula.atom (Nat.pair 5 (Nat.pair 0 0))

/-- It fails `NoReserved` — *both* older hypotheses are unavailable at this coordinate. -/
example : ¬ NoReserved clientReservedSentence := by
  intro h
  exact (noReserved_atom _).mp h 0 0 rfl

/-- A client's own one-coordinate perturbation at that sentence.  Note what is *not* here:
no syntactic side condition on the moved sentence, and no freeze certificate. -/
lemma finiteSupport_of_singleReservedSentence {P P' : History}
    (hagree : ∀ d φ, (d, φ) ≠ (0, clientReservedSentence) → P d φ = P' d φ) :
    FiniteSupportPerturbation P P' := by
  refine ⟨{(0, clientReservedSentence)}, fun d φ hmem => hagree d φ ?_⟩
  intro hc
  exact hmem (by simp [hc])

/-- **Composition, at a coordinate no syntactic hypothesis reaches.**  Same client-side
reasoning as above, on a sentence whose price the earlier endpoints provably could not
freeze. -/
example (P P' : History) (DP : DeductiveProcess) [hP : IsMachineLogicalInductor P DP]
    (hP'comp : ComputableMarket P')
    (hagree : ∀ d φ, (d, φ) ≠ (0, clientReservedSentence) → P d φ = P' d φ)
    (φ ψ : Sentence) (h1 : ∀ n, (∼φ ⋎ ψ) ∈ DP.D n) (h2 : ∀ n, (∼ψ ⋎ φ) ∈ DP.D n)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ConvergesTo (fun n => P' n φ - P' n ψ) 0 := by
  have hP' : IsMachineLogicalInductor P' DP :=
    (lic_iff_of_finiteSupportPerturbation_machine P P' DP
      hP.marketComputable hP'comp (finiteSupport_of_singleReservedSentence hagree)).mp hP
  exact lic_lex_tendsto_zero P' DP φ ψ h1 h2 hcons

/-! ## 7. Expectations -/

noncomputable section

example (P : History) (DP : DeductiveProcess) [IsMachineLogicalInductor P DP]
    (X : LUV) (n : ℕ) : 0 ≤ X.expect P n ∧ X.expect P n ≤ 1 :=
  X.expect_mem_Icc P n fun φ =>
    IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ

end

/-! ## 8. The certificate kit, in the shape a client assembles it

`dd:fuel`'s calculus is part of the interface: an exploiting trader is built by emitting its
feature syntax as a `PolySegStream`, naming its sentences with a write-out class, and closing
the assembly with one of the `EfficientlyComputable.of…` constructors. -/

/-- A rational constant serializes as a segment stream with no side conditions. -/
example (q : ℚ) : PolySegStream (fun _ => (EF.const q).serialize) :=
  PolySegStream.serialize_const q

/-- The `serialize_*` suite mirrors the whole `EF` grammar, so a compound feature's stream is
assembled constructor by constructor. -/
example (A B : ℕ → EF)
    (hA : PolySegStream fun n => (A n).serialize)
    (hB : PolySegStream fun n => (B n).serialize) :
    PolySegStream fun n => (EF.max (EF.add (A n) (B n)) (EF.mul (A n) (B n))).serialize :=
  PolySegStream.serialize_max (PolySegStream.serialize_add hA hB)
    (PolySegStream.serialize_mul hA hB)

/-- A price leaf at a poly-fueled day index, and a reciprocal on top of it. -/
example (f : ℕ → ℕ) (c : Nat.Partrec.Code) (hf : PolyFueled c f) (φ : Sentence) :
    PolySegStream fun m => (EF.safeRecip (EF.price φ (f m))).serialize :=
  PolySegStream.serialize_safeRecip (PolySegStream.serialize_price hf φ)

/-- Sentence families are closed under the connectives, `or` and `imp` included. -/
example (φ ψ : ℕ → Sentence) (hφ : RpnSentenceCodes φ) (hψ : RpnSentenceCodes ψ) :
    RpnSentenceCodes fun z => φ z ⋎ ψ z :=
  RpnSentenceCodes.or hφ hψ

example (φ ψ : ℕ → Sentence) (hφ : RpnSentenceCodes φ) (hψ : RpnSentenceCodes ψ) :
    RpnSentenceCodes fun z => LO.Propositional.Formula.imp (φ z) (ψ z) :=
  RpnSentenceCodes.imp hφ hψ

/-- A constant sentence family is one, so the connectives compose off a base case. -/
example (φ : Sentence) : RpnSentenceCodes fun _ : ℕ => φ := RpnSentenceCodes.const φ

/-- The trader-level capstone: a segment-stream certificate for the day's serialized trades
is a token-model efficiency certificate. -/
example (T : Trader) (h : PolySegStream fun n => serializeTrades (T.strat n).trades) :
    EfficientlyComputableTok T :=
  ecTok_of_segStream T h

/-- The shared recipe behind every machine reading: a segment stream yields a
`Complexity.FP` word that decodes back to it. -/
example (ds : ℕ → List ℕ) (h : PolySegStream ds) := h.exists_FP_word

/-- …and the write-out classes' machine readings are one step from it. -/
example (t : ℕ → List ℕ) (h : BigTokenStream t) : MachineTokenStream t := h.toMachine

example (φ : ℕ → Sentence) (h : BigSentenceCodes φ) : MachineSentenceCodes φ := h.toMachine

example (φ : ℕ → Sentence) (h : RpnSentenceCodes φ) : MachineSentenceCodes φ := h.toMachine

/-- Variable trade count, write-out coefficients and write-out sentences: the general
assembly constructor a `def:ec` argument ends with. -/
example (T : Trader) (count : ℕ → ℕ) (f : ℕ → EF) (ψ : ℕ → Sentence)
    (hcount : ∃ c, PolyFueled c count)
    (hf : BigSpliceStream fun z => (f z).serialize)
    (hψ : BigSentenceCodes ψ)
    (hT : ∀ n, (T.strat n).trades =
      (List.range (count n)).map fun j => (f (Nat.pair n j), ψ (Nat.pair n j))) :
    EfficientlyComputable T :=
  EfficientlyComputable.ofTradeBlocksBig T count f ψ hcount hf hψ hT

/-! ## 9. Showing that a trader exploits

Three engines, and the two accounting lemmas that feed them. -/

open Filter in
/-- World-neutral growth: the trader's net worth is a partial sum of a nonnegative sequence
that is frequently bounded away from zero. -/
example (T : Trader) (P : History) (DP : DeductiveProcess) (w : ℕ → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hnonneg : ∀ i, 0 ≤ w i)
    (hval : ∀ (n : ℕ) (v : PCWorld), v.ConsistentWith (DP.D n) →
      T.netWorth P v n = ∑ i ∈ Finset.range (n + 1), w i)
    (hfreq : ∃ᶠ n in atTop, ε ≤ w n)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    T.Exploits P DP :=
  exploits_of_nonneg_partialSums T P DP w ε hε hnonneg hval hfreq hcons

open Filter in
/-- The world-dependent form, for a trader whose day value depends on the world. -/
example (T : Trader) (P : History) (DP : DeductiveProcess) (w : ℕ → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hnonneg : ∀ i, 0 ≤ w i)
    (hge : ∀ (n : ℕ) (v : PCWorld), v.ConsistentWith (DP.D n) →
      ∑ i ∈ Finset.range (n + 1), w i ≤ T.netWorth P v n)
    (hfreq : ∃ᶠ n in atTop, ε ≤ w n)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    T.Exploits P DP :=
  exploits_of_ge_partialSums T P DP w ε hε hnonneg hge hfreq hcons

/-- The definitional engine: a floor plus unboundedness. -/
example (T : Trader) (P : History) (DP : DeductiveProcess) (C : ℝ)
    (h1 : ∀ x ∈ T.plausibleAssessments P DP, -C ≤ x)
    (h2 : ∀ B : ℝ, ∃ x ∈ T.plausibleAssessments P DP, B < x) :
    T.Exploits P DP :=
  exploits_of_bddBelow_of_unbounded T P DP C h1 h2

/-- Summable total magnitude discharges the bounded-downside half of the definition. -/
example (T : Trader) (V : History) (DP : DeductiveProcess)
    (hP : ∀ n φ, 0 ≤ V n φ ∧ V n φ ≤ 1)
    (hmag : Summable fun n => (T.strat n).magnitude V) :
    BddBelow (T.plausibleAssessments V DP) :=
  T.bddBelow_plausible_of_finiteMagnitude V DP hP hmag

/-- Exploitation transports across markets whose net-worth streams differ boundedly. -/
example {T T' : Trader} {P P' : History} {DP : DeductiveProcess}
    (h : T.Exploits P DP) (C : ℝ)
    (hdiff : ∀ (n : ℕ) (v : PCWorld), v.ConsistentWith (DP.D n) →
      |T.netWorth P v n - T'.netWorth P' v n| ≤ C) :
    T'.Exploits P' DP :=
  h.of_boundedDifference C hdiff

/-! ### The indicator toolkit

The ε-gated buy signal and the latched arming chain the §4.1 and §4.5 traders run on. -/

example (feat : EF) (ε : ℚ) (P : History) : 0 ≤ (buySignal feat ε).denote P :=
  buySignal_nonneg feat ε P

example (feat : EF) (ε : ℚ) (P : History)
    (h : (0 : ℝ) ≤ feat.denote P + (-(ε : ℝ) / 2)) :
    (buySignal feat ε).denote P = feat.denote P + (-(ε : ℝ) / 2) :=
  buySignal_eq_of_pos feat ε P h

example (sig : ℕ → EF) (P : History) : (armChain sig 0).denote P = 1 :=
  armChain_denote_zero sig P

/-- The arming chain's emission shape: one multiplication block per elapsed day. -/
example (sig : ℕ → EF) (n : ℕ) :
    (armChain sig n).serialize
      = [1, Encodable.encode ((1 : ℚ))]
        ++ (List.range n).flatMap fun i => (oneMinus (sig i)).serialize ++ [3] :=
  serialize_armChain sig n

open Filter in
/-- A failure of convergence hands the trader a rational oscillation window. -/
example (P : History) (φ : Sentence) (hb : ∀ n, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hnc : ¬ ∃ L, ConvergesTo (fun n => P n φ) L) :
    ∃ a b : ℚ, (a : ℝ) < b ∧ (∃ᶠ n in atTop, P n φ < (a : ℝ)) ∧
      (∃ᶠ n in atTop, (b : ℝ) < P n φ) :=
  exists_rat_oscillation_of_not_convergesTo P φ hb hnc

/-! ## 10. The shared asymptotic vocabulary, and feature grading -/

example (f₁ g₁ f₂ g₂ : ℕ → ℝ) (h₁ : f₁ ≈ₙ g₁) (h₂ : f₂ ≈ₙ g₂) :
    (fun n => f₁ n - f₂ n) ≈ₙ fun n => g₁ n - g₂ n :=
  h₁.sub h₂

example (c : ℝ) (f g : ℕ → ℝ) (h : f ≈ₙ g) :
    (fun n => c * f n) ≈ₙ fun n => c * g n :=
  AsympEq.const_mul c h

example (f₁ g₁ f₂ g₂ : ℕ → ℝ) (h₁ : f₁ ≲ₙ g₁) (h₂ : f₂ ≲ₙ g₂) :
    (fun n => f₁ n + f₂ n) ≲ₙ fun n => g₁ n + g₂ n :=
  h₁.add h₂

example (f g : ℕ → ℝ) : f ≳ₙ g ↔ g ≲ₙ f := asympGE_iff

/-- Rank grading is monotone, so a rank-`n` strategy may be built from lower-rank pieces. -/
example {m n : ℕ} (h : m ≤ n) : EF.EFn m ≤ EF.EFn n := EF.EFn_mono h

/-- A world values a LUV at most one way. -/
example (v : PCWorld) (X : LUV) (x y : ℝ) (hx : v.ValuesAt X x) (hy : v.ValuesAt X y) :
    x = y :=
  hx.eq hy

/-! ### The limiting expectation, and the deferral interface

`LUV.expectInf` is `𝔼_∞(X)`; its two companion lemmas mean a client never unfolds the choice
inside it. -/

example (P : History) (DP : DeductiveProcess) [IsMachineLogicalInductor P DP] (X : LUV)
    (hcode : X.RpnThresholdCodes)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hval : ∀ v : PCWorld, v.ConsistentWithTheory DP → ∃ x : ℝ, v.ValuesAt X x) :
    ConvergesTo (X.expectSeq P) (X.expectInf P DP hcode hcons hval) :=
  X.expectSeq_convergesTo_expectInf P DP hcode hcons hval

/-- Any independently identified limit of the expectation sequence *is* `𝔼_∞(X)`. -/
example (P : History) (DP : DeductiveProcess) [IsMachineLogicalInductor P DP] (X : LUV)
    (hcode : X.RpnThresholdCodes)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hval : ∀ v : PCWorld, v.ConsistentWithTheory DP → ∃ x : ℝ, v.ValuesAt X x)
    {L : ℝ} (hL : ConvergesTo (X.expectSeq P) L) :
    L = X.expectInf P DP hcode hcons hval :=
  X.expectInf_eq_of_convergesTo P DP hcode hcons hval hL

/-- The self-trust endpoints' `def:deferralfunc` binder is inhabited. -/
example : DeferralFunction := succDeferral

/-- Dividing a quote portfolio's normalization out of a vanishing diagonal price. -/
example {P : History} {gap : ℕ → ℝ} (q : AffineQuotePortfolio P gap)
    (hdiag : (fun n => (q.family n).price P n) ≈ₙ fun _ => 0) :
    gap ≈ₙ fun _ => 0 :=
  q.gap_asympEq_zero_of_diagonal hdiag

/-! ## 11. Convergence and non-dogmatism, with the side conditions discharged -/

example (P : History) (DP : DeductiveProcess) [IsMachineLogicalInductor P DP] (φ : Sentence)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ∃ L, ConvergesTo (fun n => P n φ) L :=
  lic_price_convergesTo P DP φ hcons

/-- An independent sentence's price has a limit strictly inside `(0,1)`, with convergence
supplied by the library rather than assumed by the client. -/
example (P : History) (DP : DeductiveProcess) [IsMachineLogicalInductor P DP] (φ : Sentence)
    (hpos : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ v.Holds φ)
    (hneg : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ ¬ v.Holds φ) :
    (∃ L, ConvergesTo (fun n => P n φ) L ∧ 0 < L) ∧
      (∃ L, ConvergesTo (fun n => P n φ) L ∧ L < 1) :=
  ⟨lic_exists_limit_pos P DP φ hpos, lic_exists_limit_lt_one P DP φ hneg⟩

/-- The affine benchmarks' uniform cross-time price bound, read off a bounded combination
sequence. -/
example (As : ℕ → AffineCombination) (V : History)
    (h : AffineCombination.BoundedCombinationSequence As V)
    (hP : ∀ n φ, 0 ≤ V n φ ∧ V n φ ≤ 1) :
    BoundedAffinePrices As V :=
  h.boundedPrices hP

/-! ## 12. Conditioning with no consistency premise

The two machine endpoints read the stage and market programs off the inductor instance, so a
client supplies only the condition. -/

example (P : History) (DP : DeductiveProcess) [IsMachineLogicalInductor P DP] (ψ : Sentence) :
    IsMachineLogicalInductor (conditionedHistory P fun _ => ψ) (DP.adjoinSentence ψ) :=
  ConditioningCompile.lic_conditioned_fixed_machine P DP ψ

example (P : History) (DP : DeductiveProcess) [IsMachineLogicalInductor P DP]
    (ψ : ℕ → Sentence) (hψ : BigSentenceCodes ψ) :
    IsMachineLogicalInductor
      (conditionedHistory P fun n => sentenceConjunction ((List.range (n + 1)).map ψ))
      (DP.union (prefixProcess ψ)) :=
  ConditioningCompile.lic_conditioned_growing_machine_ofSequence P DP ψ hψ

/-- Conditioning a *machine* inductor on one sentence, then reading a §4 property off the
conditioned market — the whole client session in three lines. -/
example (P : History) (DP : DeductiveProcess) [IsMachineLogicalInductor P DP] (ψ : Sentence)
    (φ χ : Sentence)
    (h1 : ∀ n, (∼φ ⋎ χ) ∈ (DP.adjoinSentence ψ).D n)
    (h2 : ∀ n, (∼χ ⋎ φ) ∈ (DP.adjoinSentence ψ).D n)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((DP.adjoinSentence ψ).D n)) :
    ConvergesTo (fun n => conditionedHistory P (fun _ => ψ) n φ
      - conditionedHistory P (fun _ => ψ) n χ) 0 := by
  haveI := ConditioningCompile.lic_conditioned_fixed_machine P DP ψ
  exact lic_lex_tendsto_zero _ _ φ χ h1 h2 hcons

noncomputable section

/-- The three constructors for the conditioning data, so no client fills the fields by
hand. -/
example {DP : DeductiveProcess} (base : DeductiveProcessComputation DP) (ψ : Sentence) :
    ConditioningPresentation DP (fixedConditionProcess ψ) :=
  fixedConditioningPresentation base ψ

example {DP : DeductiveProcess} (base : DeductiveProcessComputation DP)
    (ψ : ℕ → Sentence) (hψ : BigSentenceCodes ψ) :
    ConditioningPresentation DP (prefixProcess ψ) :=
  prefixConditioningPresentation base ψ hψ

example {DP extra : DeductiveProcess} (base : DeductiveProcessComputation DP)
    (more : CompactConditioningProcessComputation extra) :
    ConditioningPresentation DP extra :=
  conditioningPresentationOfComputations base more

/-! ## 13. Return on investment

`lem:type3`'s maturity input splits: the semantic schedule is free, and only the polynomial
verifier is a real obligation. -/

example (Ts : ℕ → Trader) (V : History) (DP : DeductiveProcess) (ε η : ℝ)
    (hroi : ∀ i, HasROI (Ts i) V DP ε) (hη : 0 < η) :
    ∃ close, ROIBudget.MaturitySchedule Ts V DP ε (fun _ => η) close :=
  ROIBudget.exists_maturitySchedule Ts V DP ε η hroi hη

end

/-! ## 14. The refuted printed theorem, reachable by its bare name

`not_overgeneral_ifp` is re-exported by `LogicalInduction.API`, so a client can state the
paper's own defect without naming the construction namespace it is proved in. -/

example : ¬ ∀ (P P' : History) (DP : DeductiveProcess) (N : ℕ),
    IsMachineLogicalInductor P DP → ComputableMarket P' →
    (∀ n, N ≤ n → ∀ φ, P n φ = P' n φ) → IsMachineLogicalInductor P' DP :=
  not_overgeneral_ifp

/-- …and the corrected theorem doing visible work in the other direction: the constructed
market with one price moved is still a machine logical inductor. -/
example (DP : DeductiveProcess) (hDP : ComputableDeductiveProcess DP) (r : ℚ)
    (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    IsMachineLogicalInductor (LIAPerturbation.liaPerturbed DP r) DP :=
  LIAPerturbation.machineLogicalInductor_liaPerturbed DP hDP r h0 h1

/-! ## 15. Constructed data that arrives with the same import -/

/-- `thm:obu` at the paper's own premise: an unclocked c.e. enumeration of the source. -/
example (P : History) (DP : DeductiveProcess) [IsMachineLogicalInductor P DP]
    (source : ℕ → Sentence) (h : CEEnumeration source)
    (hjoint : ∀ n, ∃ v : PCWorld,
      v.ConsistentWith (DP.D n) ∧ ∀ i, v.Holds (source i)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, ε ≤ limitingBelief P (source i) :=
  lic_uniform_nonDogmatism_ofCE P DP source h hjoint

/-- `def:ece` for rational sequences: the write-out route in, and the computability out. -/
example (P : History) (q : ℕ → ℚ) (hq : DigitRatCodes q) : PGenerableRat P q :=
  PGenerableRat.ofDigitRatCodes hq P

example (P : History) (market : MarketComputation P) (q : ℕ → ℚ)
    (h : PGenerableRat P q) : Computable q :=
  PGenerableRat.computable market h

noncomputable section

/-- Every computable step budget is an admissible §4.10 horizon, and the diagonal Ackermann
function is one — so the interface is strictly wider than any polynomial class. -/
example (steps : ℕ → ℕ) (h : Computable steps) : ComputableHorizon steps :=
  ComputableHorizon.of h

example : ComputableHorizon (fun n => _root_.ack n n) := ComputableHorizon.ackermann

/-- A presented LUV source unfolds its thresholds to the handle it is named by. -/
example (X : PresentedLUVSeq) (n : ℕ) (r : ℚ) :
    (X.toLUV n).gt r =
      semanticPrimeSentence X.thresholdSchema (Nat.pair n (Encodable.encode r)) :=
  X.gt_eq n r

/-- …and the handle families carry `def:ec`'s threshold certificate. -/
example (schema : ℕ) : LUV.RpnThresholdCodeSeq (semanticHandleLUVSeq schema) :=
  semanticHandleLUVSeq_rpnThresholdCodeSeq schema

/-! ### The arithmetic-theory family at a concrete theory

The §4.9–4.10 endpoints carry `[T.Δ₁]`, `[𝗣𝗔⁻ ⪯ T]` and the paper's own
`[RepresentsComputations T]`.  At `𝗣𝗔` all three are discharged by instance search from this
import alone, and `ComputableHorizon.ackermann` supplies a horizon that no primitive
recursive function dominates, so a client instantiating the family supplies nothing at all. -/

example :=
  lic_belief_finitistic_consistency_unconditional 𝗣𝗔 _ ComputableHorizon.ackermann

/-! ## 16. The published surface, name by name

`AxiomAudit.lean` publishes 107 canonical endpoints, and `LogicalInduction.API`'s claim is
that every one of them resolves from this single import.  That claim is checked here rather
than asserted: each line below elaborates one published name, grouped by the module the API
documentation gives as its address, so a move or a rename fails this file before it reaches a
reader.  A worked application of most of them would restate the paper's own theorem, which is
not what a client test is for; the sections above are where the interface is actually
exercised. -/

-- Framework/Criterion.lean
example := @DeductiveProcess
example := @DeductiveProcessComputation
example := @EfficientlyComputable
example := @IsLogicalInductor
example := @MachineEfficientTrader
example := @Strategy
example := @Trader

-- Framework/MachineEfficiency.lean
example := @EfficientlyComputable.toMachine
example := @IsMachineLogicalInductor

-- Framework/Affine.lean
example := @AffineCombination
example := @AffineCombination.BoundedCombinationSequence

-- Framework/Expectations.lean
example := @GeneratedRatFeature
example := @LUV

-- Properties/Coherence.lean
example := @lic_price_convergesTo

-- Properties/LimitCoherence.lean
example := @lic_limitCoherence

-- Properties/AffineCoherence.lean
example := @AffineCombination.PolySequence.affcoh
example := @AffineCombination.PolySequence.affine_provind_theory_eq
example := @AffineCombination.PolySequence.affine_provind_theory_ge
example := @AffineCombination.PolySequence.affine_provind_theory_le
example := @lic_provind

-- Properties/AffinePersistence.lean
example := @AffineCombination.PolySequence.peraffkno
example := @lic_limitingBelief_tendsto

-- Properties/AffinePreemptiveLearning.lean
example := @AffineCombination.BoundedCombinationSequence.affpolymax

-- Properties/TimelyLearning.lean
example := @AffineCombination.sentenceAffine_polySequence
example := @lic_persistence_of_knowledge
example := @lic_preemptive_learning

-- Properties/Calibration.lean
example := @PGenerableWeighting
example := @calibrationIndicator_pgenerable

-- Properties/Relationships.lean
example := @lic_learning_exclusive_exhaustive

-- Properties/NonDogmatism.lean
example := @lic_nonDogmatism
example := @lic_nonDogmatism_dual

-- Properties/UniformNonDogmatism.lean
example := @lic_uniform_nonDogmatism

-- Properties/UniversalSemimeasure.lean
example := @lic_domination_universalSemimeasure
example := @lic_strict_domination_universalSemimeasure

-- Properties/ExpectationConvergence.lean
example := @LUV.expect_converges

-- Properties/ExpectationAffine.lean
example := @lic_expectation_indicator

-- Properties/ExpectationProperties.lean
example := @LUVCombination.BoundedSequence

-- Properties/Introspection.lean
example := @lic_introspection

-- Properties/SelfTrust.lean
example := @DeferralFunction

-- Construction/LIA.lean
example := @liaHistory
example := @liaStates

-- Construction/LIACompiler.lean
example := @LIA_isMachineLogicalInductor
example := @LIA_is_logical_inductor
example := @exists_computable_beliefSequence_logical_inductor
example := @exists_machine_logical_inductor

-- Construction/TradingFirm.lean
example := @trading_firm_dominance

-- Construction/Statistics/HistoricalMaturity.lean
example := @AffineCombination.BoundedCombinationSequence.prandaff
example := @AffineCombination.BoundedCombinationSequence.prandaff_above
example := @AffineCombination.BoundedCombinationSequence.prandaff_below
example := @AffineCombination.BoundedCombinationSequence.recunbiasedaff
example := @AffineCombination.recurringunbiasedness
example := @AffineCombination.simcal
example := @LUVCombination.BoundedSequence.prandexp
example := @LUVCombination.BoundedSequence.prandexp_below
example := @LUVCombination.BoundedSequence.prandexp_eq
example := @LUVCombination.BoundedSequence.recurringunbiasednessexp
example := @lic_learning_pseudorandom_frequency
example := @lic_learning_pseudorandom_frequency_above
example := @lic_learning_pseudorandom_frequency_below
example := @lic_learning_varied_pseudorandom
example := @lic_learning_varied_pseudorandom_above
example := @lic_learning_varied_pseudorandom_below

-- Construction/Statistics/FeedbackTruth.lean
example := @FeedbackTruth.boundedCombination_wubaff_ofComputation
example := @FeedbackTruth.lic_wub_ofComputation
example := @FeedbackTruth.luv_wubexp_ofComputation

-- Construction/Statistics/Endpoints.lean
example := @FeedbackTruth.boundedCombination_wubaff_ofComputation_unconditional
example := @FeedbackTruth.lic_wub_ofComputation_unconditional
example := @FeedbackTruth.luv_wubexp_ofComputation_unconditional

-- Construction/NonDogmatism/RepeatedEnumeration.lean
example := @lic_uniform_nonDogmatism_ofCE

-- Construction/NonDogmatism/BitPrefix.lean
example := @lic_domination_universalSemimeasure_ofIndependentAtoms

-- Construction/NonDogmatism/StrictSeparators.lean
example := @lic_strict_domination_universalSemimeasure_ofAtomCodes

-- Construction/NonDogmatism/UniversalPrefix.lean
example := @UPrefix.lic_occamBounds_ofUniversalPrefix

-- Construction/Freeze/Oracle.lean
example := @FreezeOracle.machine_lic_iff_of_finiteSupport

-- Construction/Freeze/Counterexample.lean
example := @FinitePerturbationCounterexample.not_overgeneral_ifp

-- Construction/Freeze/LIAPerturbation.lean
example := @LIAPerturbation.machineLogicalInductor_liaPerturbed

-- Construction/Conditioning/Endpoints.lean
example := @ConditioningCompile.lic_conditioned_fixed_machine
example := @ConditioningCompile.lic_conditioned_growing_machine_ofProcessComputation
example := @ConditioningCompile.lic_conditioned_growing_machine_ofSequence
example := @lic_conditioned_fixed_machine_unconditional
example := @lic_conditioned_growing_machine_unconditional

-- Construction/LUV/Syntax.lean
example := @LUVCombination.BoundedSequence.expcoh_ofSyntax
example := @LUVCombination.BoundedSequence.exppolymax_ofSyntax
example := @LUVCombination.BoundedSequence.mesh_independence_ofSyntax
example := @LUVCombination.BoundedSequence.perexpkno_ofSyntax

-- Construction/LUV/Endpoints.lean
example := @lic_expect_combination_provind_eq
example := @lic_expect_combination_provind_ge
example := @lic_expect_combination_provind_le
example := @lic_linearity_of_expectation_seq

-- Construction/LUV/PaperLUV.lean
example := @PaperLUV

-- Construction/LUV/ArithmeticSource.lean
example := @PaperLUVCombination.boundedSequence
example := @unitFracPaperLUVBoundedSequence
example := @unitFracPaperLUVSeq

-- Construction/Knowledge/Endpoints.lean
example := @lia_learns_halting_patterns_unconditional
example := @lic_belief_finitistic_consistency_unconditional
example := @lic_belief_stronger_theory_consistency_unconditional
example := @lic_disbelief_inconsistent_theories_unconditional
example := @lic_does_not_anticipate_halting_unconditional
example := @lic_learns_provable_nonhalting_patterns_unconditional

-- Construction/Paper/Market.lean
example := @lic_expectations_of_probabilities_closed
example := @lic_expected_future_expectations_closed
example := @lic_introspection_closed
example := @lic_iterated_expectations_closed
example := @lic_no_expected_net_update_closed
example := @lic_paradox_resistance_ofDiagonal_unconditional
example := @lic_self_trust_closed

-- Construction/Quotation/ExactCCEE.lean
example := @lic_no_expected_net_update_conditional_paperLUV_closed

-- Construction/SemanticExtension/Endpoints.lean
example := @lic_no_expected_net_update_conditional_exact_canonical

/-! ### Documented routes beside the published endpoints

The construction interfaces, discharge kits and non-vacuity witnesses the API documentation
names, which are supported client tools without being paper endpoints of their own. -/

-- Framework/Theory/R0Instances.lean — the paper's §2 premise, discharged at a real theory
example := @representsComputations_of_peanoMinus

-- Construction/NonDogmatism/ — the constructed presentations the §4.6 endpoints run on
example := @bitPrefixSentencesOfIndependentAtoms
example := @Dovetail.universalSemimeasure

-- Construction/Statistics/FeedbackEmission.lean — the delayed-truth trader kit
example := @FeedbackEmission.feedbackTraderEmissionSigns
example := @FeedbackEmission.lic_wubaff_ofFeedbackTruth
example := @FeedbackEmission.boundedCombination_wubaff_ofFeedbackTruth
example := @FeedbackEmission.luv_wubexp_ofFeedbackTruth

-- Construction/SemanticExtension/Prime.lean — the presented-LUV source interface
example := @no_nonvacuous_worldValued_presented_of_rpn

-- Construction/LUV/ — the certified and the literal first-order LUV frontends
example := @ComputableLUV.toLUV_polyThresholdCodes
example := @ComputableLUV.valuesAt_ofArithmetic
example := @PaperLUVSeq
example := @dyadicPaperLUVSeq
example := @ArithSource.ofNNF

-- Construction/Knowledge/Endpoints.lean — the §4.10 hypothesis-discharge kit
example := @theoryOf_const_ofNNF
example := @conGamma_mentions_zero_of_horizon_unbounded

-- Framework/ROI.lean — `lem:type3` and the half of its input that is a real obligation
example := @ROIBudget.noRepeatableROI
example := @ROIBudget.noRepeatableROI_of_verifiedMaturity

-- Construction/LIACompiler.lean — the compiled bounded evaluator the existence proof runs on
example := @liaBoundedEvaluatorCompiler

end

end APITests.LogicalInduction
