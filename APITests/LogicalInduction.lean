import LogicalInduction.API

namespace APITests.LogicalInduction

open _root_.LogicalInduction

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

/-- A constant sentence family can be certified without exposing the raw clocked-code
construction. -/
example (φ : Sentence) : RpnSentenceCodes (fun _ => φ) :=
  RpnSentenceCodes.const φ

/-- A new efficient client trader inherits the central no-exploitation guarantee. -/
example (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (φ : Sentence) (hEC : EfficientlyComputable (buyOneDaily φ)) :
    ¬ (buyOneDaily φ).Exploits P DP :=
  IsLogicalInductor.noExploit (P := P) (DP := DP) _ hEC

example (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (n : ℕ) (φ : Sentence) : 0 ≤ P n φ ∧ P n φ ≤ 1 :=
  IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ

def constantPortfolio : AffineCombination where
  const := EF.const 2
  terms := []

example (V : History) (w : Valuation) : constantPortfolio.value V w = 2 := by
  simp [constantPortfolio, AffineCombination.value]

noncomputable section

example (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (X : LUV) (n : ℕ) : 0 ≤ X.expect P n ∧ X.expect P n ≤ 1 :=
  X.expect_mem_Icc P n fun φ =>
    IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ

end

end APITests.LogicalInduction
