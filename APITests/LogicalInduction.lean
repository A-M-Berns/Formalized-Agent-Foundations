import LogicalInduction.API

/-!
# Client-style smoke tests for `LogicalInduction.API`

A downstream researcher's session, in order: build a trader, certify it efficient, use the
criterion to conclude it cannot exploit the market, read a §4 property off that market,
condition the inductor, and transport the criterion across a corrected finite-support
perturbation.

Everything here imports `LogicalInduction.API` and nothing else — no machine, compiler or
parser internals — and uses the API's objects rather than restating its endpoints.
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

end APITests.LogicalInduction
