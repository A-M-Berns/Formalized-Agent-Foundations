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
property off the conditioned market. -/

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

/-! ## 7. Expectations -/

noncomputable section

example (P : History) (DP : DeductiveProcess) [IsMachineLogicalInductor P DP]
    (X : LUV) (n : ℕ) : 0 ≤ X.expect P n ∧ X.expect P n ≤ 1 :=
  X.expect_mem_Icc P n fun φ =>
    IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ

end

end APITests.LogicalInduction
