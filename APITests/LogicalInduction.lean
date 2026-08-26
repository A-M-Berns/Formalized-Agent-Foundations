import LogicalInduction.API

/-!
# Client-style smoke tests for `LogicalInduction.API`

Everything here imports the API and nothing else, and uses its objects rather than
restating its endpoints.  The centre of gravity is the machine-facing criterion:
`MachineEfficientTrader` (`def:ec`) and `IsMachineLogicalInductor` (`def:lic`).
-/

namespace APITests.LogicalInduction

open _root_.LogicalInduction

/-! ## Building traders and features -/

/-- A client-defined trader that buys one share of the same sentence every day. -/
def buyOneDaily (φ : Sentence) : Trader where
  strat n :=
    { trades := [(EF.const 1, φ)]
      rank_le := by simp }

example (φ : Sentence) (n : ℕ) : ((buyOneDaily φ).strat n).trades = [(EF.const 1, φ)] :=
  rfl

/-- Extensionality lets client transformations prove trader equality without touching
the proof field inside each strategy. -/
example (T U : Trader) (h : ∀ n, T.strat n = U.strat n) : T = U := by
  apply Trader.ext
  exact funext h

example (DP DQ : DeductiveProcess) (h : DP.D = DQ.D) : DP = DQ := by
  exact DeductiveProcess.ext h

example (X Y : LUV) (h : X.gt = Y.gt) : X = Y := by
  exact LUV.ext h

def constantPortfolio : AffineCombination where
  const := EF.const 2
  terms := []

example (V : History) (w : Valuation) : constantPortfolio.value V w = 2 := by
  simp [constantPortfolio, AffineCombination.value]

/-! ## Efficiency: certificates land in the paper's class

A client certifies a trader with the fuel calculus and then *uses* it at the machine
class, which is the direction the API supports. -/

/-- A constant sentence family is certified without exposing the clocked-code
construction. -/
example (φ : Sentence) : RpnSentenceCodes (fun _ => φ) :=
  RpnSentenceCodes.const φ

/-- Every fuel certificate is a certificate of membership in `def:ec`'s class. -/
example (T : Trader) (h : EfficientlyComputable T) : MachineEfficientTrader T :=
  h.toMachine

/-! ## The criterion at the paper's own quantifier -/

/-- A client trader certified in the fuel calculus inherits the machine criterion's
no-exploitation guarantee, through `EfficientlyComputable.toMachine`. -/
example (P : History) (DP : DeductiveProcess) [IsMachineLogicalInductor P DP]
    (φ : Sentence) (hEC : EfficientlyComputable (buyOneDaily φ)) :
    ¬ (buyOneDaily φ).Exploits P DP :=
  IsMachineLogicalInductor.noExploit (P := P) (DP := DP) _ hEC.toMachine

/-- And a client that has built a `Complexity.FP` witness directly uses it directly. -/
example (P : History) (DP : DeductiveProcess) [IsMachineLogicalInductor P DP]
    (T : Trader) (hT : MachineEfficientTrader T) : ¬ T.Exploits P DP :=
  IsMachineLogicalInductor.noExploit (P := P) (DP := DP) T hT

/-- The compatibility instance is what carries the §4 tail to the machine class: a
machine logical inductor is a fuel-class one, with no side condition. -/
example (P : History) (DP : DeductiveProcess) [IsMachineLogicalInductor P DP] :
    IsLogicalInductor P DP :=
  inferInstance

example (P : History) (DP : DeductiveProcess) [IsMachineLogicalInductor P DP]
    (n : ℕ) (φ : Sentence) : 0 ≤ P n φ ∧ P n φ ≤ 1 :=
  IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ

/-- A §4 property theorem, stated in the API against `[IsLogicalInductor …]`, applies at
a *machine* logical inductor without restatement: provably equivalent sentences have
converging prices. -/
example (P : History) (DP : DeductiveProcess) [IsMachineLogicalInductor P DP]
    (φ ψ : Sentence) (h1 : ∀ n, (∼φ ⋎ ψ) ∈ DP.D n) (h2 : ∀ n, (∼ψ ⋎ φ) ∈ DP.D n)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ConvergesTo (fun n => P n φ - P n ψ) 0 :=
  lic_lex_tendsto_zero P DP φ ψ h1 h2 hcons

/-! ## Transport: the corrected `thm:ifp` doing client work

The published finite-perturbation theorem is false
(`FinitePerturbationCounterexample.not_overgeneral_ifp`).  What a client may use is the
finite-*support* correction, and this is what using it looks like: move one price at a
recognizable coordinate, transport the criterion, and then read a §4 property off the
*perturbed* market — a market the client built, not one this repository constructs. -/

/-- A client's one-coordinate perturbation is a `RecognizableSupportPerturbation`. -/
lemma recognizableSupport_of_singleAtom {P P' : History}
    (hagree : ∀ d φ, (d, φ) ≠ (0, (LO.Propositional.Formula.atom 0 : Sentence)) →
      P d φ = P' d φ) :
    FreezeOracle.RecognizableSupportPerturbation P P' := by
  refine ⟨FreezeOracle.exampleS, ?_, fun d φ hmem => hagree d φ ?_⟩
  · intro p hp
    simp only [FreezeOracle.exampleS, Finset.mem_singleton] at hp
    subst hp
    exact FreezeOracle.recognizable_atom 0 FreezeOracle.atom_zero_noReserved
  · intro hc
    exact hmem (by simp [FreezeOracle.exampleS, hc])

/-- **Composition.**  Moving a single price at `(0, atom 0)` preserves the criterion at
the paper's own quantifier, so every §4 consequence holds of the perturbed market too.
Nothing but the corrected `thm:ifp` gets us from `P` to `P'` here. -/
example (P P' : History) (DP : DeductiveProcess) [hP : IsMachineLogicalInductor P DP]
    (hP'comp : ComputableMarket P')
    (hagree : ∀ d φ, (d, φ) ≠ (0, (LO.Propositional.Formula.atom 0 : Sentence)) →
      P d φ = P' d φ)
    (φ ψ : Sentence) (h1 : ∀ n, (∼φ ⋎ ψ) ∈ DP.D n) (h2 : ∀ n, (∼ψ ⋎ φ) ∈ DP.D n)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ConvergesTo (fun n => P' n φ - P' n ψ) 0 := by
  have hP' : IsMachineLogicalInductor P' DP :=
    (FreezeOracle.machine_lic_iff_of_recognizableSupport P P' DP
      hP.marketComputable hP'comp (recognizableSupport_of_singleAtom hagree)).mp hP
  exact lic_lex_tendsto_zero P' DP φ ψ h1 h2 hcons

/-- Finite support is strictly stronger than the paper's tail agreement, and the API
exposes the implication a client needs to see that. -/
example (P P' : History)
    (h : FreezeOracle.RecognizableSupportPerturbation P P') :
    ∃ N : ℕ, ∀ d, N ≤ d → ∀ ψ, P d ψ = P' d ψ :=
  h.toFiniteSupport.tail_agree

/-! ## Transport: closure under conditioning, at the machine class -/

/-- Given the conditioning data, a client conditions a machine logical inductor and then
reads a §4 property off the conditioned market. -/
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

/-! ## Expectations -/

noncomputable section

example (P : History) (DP : DeductiveProcess) [IsMachineLogicalInductor P DP]
    (X : LUV) (n : ℕ) : 0 ≤ X.expect P n ∧ X.expect P n ≤ 1 :=
  X.expect_mem_Icc P n fun φ =>
    IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ

end

end APITests.LogicalInduction
