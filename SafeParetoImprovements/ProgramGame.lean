import SafeParetoImprovements.Representatives
import EconCSLib.GameTheory.StrategicGame.MixedStrategy
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Program games, threat points, and program equilibrium (Appendix A, `dd:program-game`)

The paper's Appendix A analyses the meta-game of delegation as a *program game*
(Tennenholtz 2004): each player submits a program, the programs are run against each
other, and a *program equilibrium* is a Nash equilibrium of the induced game.  This file
carries the abstract interface, in the repo's implementation-independence style: the
concrete instruction language and the realization theorem live in `Instruction.lean`.

## The model

* **Mixed strategies are EconCSLib's** (`StrategicGame.MixedStrategy`, the standard
  simplex over `Γ.S i`), and `Game.expected` is EconCSLib's `expectedPayoff` on
  `Game.toStrategic`: independent mixtures, the paper's `uᵢ(σᵢ, σ₋ᵢ)`.
* **Threat point** (extraction l. 1977–1993): `vᵢ = min_{σ₋ᵢ} max_{σᵢ} uᵢ(σᵢ, σ₋ᵢ)`, over
  products of standard simplices.  Both extrema exist by compactness (`Game.threatPoint`,
  `Game.minimax`), not by linear programming; the paper's "consistent tie-breaking" of the
  minimiser is one `Classical.choice` per player.
* **A program game** (extraction l. 1957–1971, `dd:exec-kernel`): a set of instructions per
  player and an execution map.  Given the representatives' sample point `ω` — the one
  source of randomness the paper's `Πᵢ(Γ′)` calls read — each program's realised action is
  a mixed strategy of its own, and the players' actions are *independent*: `exec` returns a
  profile of mixed strategies, and the outcome distribution is their product.  This is
  what the paper leaves implicit when it lets a program "play `minimax(i, j)`" (a mixed
  action) and then bounds a deviator's payoff by the threat point (erratum D8): the bound
  needs the deviator's action independent of the punishers' draws, and the product
  structure is exactly that.  The induced game's payoff is the expectation over `ω` of the
  expected utility of the product mixture (`ProgramGame.payoff`), and a **program
  equilibrium** is EconCSLib's `IsNashEquilibrium` of the induced `StrategicGame`.

## Proposition 18 over the interface

`ProgramGame.isProgramEquilibrium_of_algorithm2` proves the paper's Proposition 18 for any
program profile with Algorithm 2's *semantics*: everybody's execution is `Π(Γˢ)`, and
against any unilateral deviation by `i` the others play `minimax(i, ·)`.  The deviator's
payoff is *at most* `vᵢ` (erratum D8: the paper says "is"), which is `≤ E[uᵢ(Π(Γ))]` by
the threat-point guarantee and `≤ E[uᵢ(Π(Γˢ))]` because `Γˢ` is an SPI.  The paper node
itself is carried by the concrete Algorithm 2 term in `Instruction.lean`, where the two
semantic hypotheses are *proved* from the execution model.
-/

universe u v w x

namespace SafeParetoImprovements

open StrategicGame MeasureTheory Filter Set

variable {N : Type u} {𝒜 : N → Type v}

namespace Game

variable (Γ : Game N 𝒜)

/-- `Δ(Aᵢ)`: EconCSLib's mixed strategies of player `i` in `Γ`, the standard simplex over
`Γ.S i`. -/
abbrev Mixed (i : N) : Type v := MixedStrategy Γ.toStrategic i

instance (i : N) : Nonempty (Γ.S i) := ⟨⟨_, (Γ.nonempty i).choose_spec⟩⟩

section pure

variable [∀ i, DecidableEq (𝒜 i)]

/-- The pure strategy `a` as a mixed one (EconCSLib's `pureToMixed`). -/
noncomputable def pureMixed {i : N} (a : 𝒜 i) (ha : a ∈ Γ.S i) : Γ.Mixed i :=
  pureToMixed (G := Γ.toStrategic) (⟨a, ha⟩ : Γ.S i)

lemma pureMixed_val {i : N} (a : 𝒜 i) (ha : a ∈ Γ.S i) (b : Γ.S i) :
    (Γ.pureMixed a ha).val b = if (b : 𝒜 i) = a then 1 else 0 := by
  unfold pureMixed pureToMixed
  simp only [Subtype.ext_iff]

end pure

/-- Mixed strategies are probability vectors: every coordinate lies in `[0, 1]`. -/
lemma mixed_val_mem_Icc {i : N} (p : Γ.Mixed i) (b : Γ.S i) : p.val b ∈ Icc (0 : ℝ) 1 := by
  refine ⟨p.2.1 b, ?_⟩
  rw [← p.2.2]
  exact Finset.single_le_sum (fun c _ => p.2.1 c) (Finset.mem_univ b)

variable [DecidableEq N] [Fintype N]

/-- `uᵢ(σ)` for a profile of independent mixed strategies: EconCSLib's expected payoff on
`Γ.toStrategic`. -/
noncomputable abbrev expected (σ : ∀ i, Γ.Mixed i) (i : N) : ℝ :=
  expectedPayoff Γ.toStrategic σ i

lemma expected_eq (σ : ∀ i, Γ.Mixed i) (i : N) :
    Γ.expected σ i = ∑ s : Γ.toStrategic.Profile, (∏ j, (σ j).val (s j)) * Γ.u (Γ.ofStrategicProfile s) i :=
  rfl

/-- Expected payoff at a pure profile is the payoff. -/
lemma expected_pure [∀ i, DecidableEq (𝒜 i)] (a : ∀ i, 𝒜 i) (ha : a ∈ Γ.profiles) (i : N) :
    Γ.expected (fun j => Γ.pureMixed (a j) (ha j)) i = Γ.u a i := by
  rw [expected_eq]
  have key : ∀ s : Γ.toStrategic.Profile,
      (∏ j, (Γ.pureMixed (a j) (ha j)).val (s j)) = if s = Γ.toStrategicProfile a ha then 1 else 0 := by
    intro s
    simp only [pureMixed_val]
    rw [Finset.prod_boole]
    congr 1
    apply propext
    constructor
    · intro h; funext j; exact Subtype.ext (h j (Finset.mem_univ j))
    · intro h j _; rw [h]; rfl
  simp only [key, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rfl

/-- `|uᵢ(σ)|` is bounded by the sum of `|uᵢ|` over pure profiles, uniformly in `σ`. -/
lemma abs_expected_le (σ : ∀ i, Γ.Mixed i) (i : N) :
    |Γ.expected σ i| ≤ ∑ s : Γ.toStrategic.Profile, |Γ.u (Γ.ofStrategicProfile s) i| := by
  rw [expected_eq]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s _ => ?_)
  rw [abs_mul]
  have h0 : 0 ≤ ∏ j, (σ j).val (s j) := Finset.prod_nonneg fun j _ => (Γ.mixed_val_mem_Icc _ _).1
  have h1 : ∏ j, (σ j).val (s j) ≤ 1 :=
    Finset.prod_le_one (fun j _ => (Γ.mixed_val_mem_Icc _ _).1) (fun j _ => (Γ.mixed_val_mem_Icc _ _).2)
  rw [abs_of_nonneg h0]
  exact mul_le_of_le_one_left (abs_nonneg _) h1

/-- `σ ↦ uᵢ(σ)` is continuous on the product of simplices. -/
lemma continuous_expected (i : N) : Continuous fun σ : ∀ j, Γ.Mixed j => Γ.expected σ i := by
  simp only [expected, expectedPayoff]
  refine continuous_finsetSum _ fun s _ => Continuous.mul_const ?_ _
  exact continuous_finsetProd _ fun j _ =>
    ((continuous_apply (s j)).comp continuous_subtype_val).comp (continuous_apply j)

/-! ### Threat points -/

/-- Player `i`'s best-response value against the mixtures `τ₋ᵢ`: `max_{σᵢ ∈ Δ(Aᵢ)} uᵢ(σᵢ, τ₋ᵢ)`
(the `τ i` component is overwritten). -/
noncomputable def bestValue (i : N) (τ : ∀ j, Γ.Mixed j) : ℝ :=
  sSup ((fun p : Γ.Mixed i => Γ.expected (Function.update τ i p) i) '' univ)

lemma continuous_bestValue (i : N) : Continuous (Γ.bestValue i) := by
  unfold bestValue
  refine isCompact_univ.continuous_sSup ?_
  exact (Γ.continuous_expected i).comp ((continuous_fst).update i continuous_snd)

lemma expected_le_bestValue (i : N) (τ : ∀ j, Γ.Mixed j) (p : Γ.Mixed i) :
    Γ.expected (Function.update τ i p) i ≤ Γ.bestValue i τ :=
  le_csSup (isCompact_univ.bddAbove_image
    ((Γ.continuous_expected i).comp (continuous_const.update i continuous_id)).continuousOn)
    (mem_image_of_mem _ (mem_univ p))

/-- **The threat point** `vᵢ = min_{σ₋ᵢ} max_{σᵢ} uᵢ(σᵢ, σ₋ᵢ)` (extraction l. 1977–1983),
over independent mixtures; the `i`-th component of the outer variable is immaterial. -/
noncomputable def threatPoint (i : N) : ℝ := sInf (Γ.bestValue i '' univ)

lemma exists_isMinOn_bestValue (i : N) : ∃ τ, IsMinOn (Γ.bestValue i) univ τ := by
  obtain ⟨τ, -, hτ⟩ := isCompact_univ.exists_isMinOn univ_nonempty (Γ.continuous_bestValue i).continuousOn
  exact ⟨τ, hτ⟩

/-- **The minimax profile against `i`** (extraction l. 1985–1993): a chosen minimiser of
`i`'s best-response value; `minimax i j` is the paper's `minimax(i, j) ∈ Δ(Aⱼ)`.  The choice
is fixed once per player, which is the paper's "consistent tie-breaking". -/
noncomputable def minimax (i : N) : ∀ j, Γ.Mixed j := (Γ.exists_isMinOn_bestValue i).choose

lemma isMinOn_minimax (i : N) : IsMinOn (Γ.bestValue i) univ (Γ.minimax i) :=
  (Γ.exists_isMinOn_bestValue i).choose_spec

lemma bestValue_minimax (i : N) : Γ.bestValue i (Γ.minimax i) = Γ.threatPoint i := by
  unfold threatPoint
  refine (IsLeast.csInf_eq ⟨mem_image_of_mem _ (mem_univ _), ?_⟩).symm
  rintro _ ⟨τ, -, rfl⟩
  exact Γ.isMinOn_minimax i (mem_univ τ)

lemma threatPoint_le_bestValue (i : N) (τ : ∀ j, Γ.Mixed j) :
    Γ.threatPoint i ≤ Γ.bestValue i τ := by
  rw [← Γ.bestValue_minimax i]
  exact Γ.isMinOn_minimax i (mem_univ τ)

/-- Against the minimax profile, no mixture of `i`'s earns more than the threat point. -/
lemma expected_minimax_le_threatPoint (i : N) (p : Γ.Mixed i) :
    Γ.expected (Function.update (Γ.minimax i) i p) i ≤ Γ.threatPoint i :=
  (Γ.expected_le_bestValue i _ p).trans_eq (Γ.bestValue_minimax i)

/-- Mixtures sum to one over profiles: `∑ₛ ∏ⱼ σⱼ(sⱼ) = 1`. -/
lemma sum_prod_mixed (σ : ∀ j, Γ.Mixed j) :
    ∑ s : Γ.toStrategic.Profile, ∏ j, (σ j).val (s j) = 1 := by
  rw [← Fintype.prod_sum]
  exact Finset.prod_eq_one fun j _ => (σ j).2.2

/-- If `aᵢ` is a best response to `a₋ᵢ` among pure actions, then no mixture of `i`'s earns
more than `uᵢ(a)` against the pure profile `a₋ᵢ`. -/
lemma expected_update_pure_le [∀ i, DecidableEq (𝒜 i)] {a : ∀ i, 𝒜 i} (ha : a ∈ Γ.profiles)
    (i : N) (hbr : ∀ b ∈ Γ.S i, Γ.u (Function.update a i b) i ≤ Γ.u a i) (p : Γ.Mixed i) :
    Γ.expected (Function.update (fun j => Γ.pureMixed (a j) (ha j)) i p) i ≤ Γ.u a i := by
  set σ := Function.update (fun j => Γ.pureMixed (a j) (ha j)) i p with hσ
  rw [expected_eq]
  calc ∑ s : Γ.toStrategic.Profile, (∏ j, (σ j).val (s j)) * Γ.u (Γ.ofStrategicProfile s) i
      ≤ ∑ s : Γ.toStrategic.Profile, (∏ j, (σ j).val (s j)) * Γ.u a i := by
        refine Finset.sum_le_sum fun s _ => ?_
        have h0 : 0 ≤ ∏ j, (σ j).val (s j) :=
          Finset.prod_nonneg fun j _ => (Γ.mixed_val_mem_Icc _ _).1
        rcases h0.lt_or_eq with hpos | hzero
        · refine mul_le_mul_of_nonneg_left ?_ h0
          have hs : Γ.ofStrategicProfile s = Function.update a i (s i) := by
            funext j
            by_cases hj : j = i
            · subst hj; simp
            · rw [Function.update_of_ne hj]
              have hne : (σ j).val (s j) ≠ 0 :=
                fun h => hpos.ne' (Finset.prod_eq_zero (Finset.mem_univ j) h)
              rw [hσ, Function.update_of_ne hj, pureMixed_val] at hne
              by_contra hcontra
              exact hne (if_neg hcontra)
          rw [hs]
          exact hbr _ (s i).2
        · rw [← hzero, zero_mul, zero_mul]
    _ = Γ.u a i := by rw [← Finset.sum_mul, sum_prod_mixed, one_mul]

/-- **A pure Nash equilibrium certifies the threat-point guarantee**: if `a` is a pure
profile in which every player best-responds, then `vᵢ ≤ uᵢ(a)` for every `i`. -/
lemma threatPoint_le_of_bestResponse [∀ i, DecidableEq (𝒜 i)] {a : ∀ i, 𝒜 i}
    (ha : a ∈ Γ.profiles) (i : N)
    (hbr : ∀ b ∈ Γ.S i, Γ.u (Function.update a i b) i ≤ Γ.u a i) :
    Γ.threatPoint i ≤ Γ.u a i := by
  refine (Γ.threatPoint_le_bestValue i fun j => Γ.pureMixed (a j) (ha j)).trans ?_
  refine csSup_le ⟨_, mem_image_of_mem _ (mem_univ (Γ.pureMixed (a i) (ha i)))⟩ ?_
  rintro _ ⟨p, -, rfl⟩
  exact Γ.expected_update_pure_le ha i hbr p

end Game

/-! ### Program games -/

/-- **A program game** on `Γ₀`, played by the representatives `R` (extraction l. 1957–1971;
`dd:exec-kernel`).  `Instr i` is the paper's `PROGᵢ`; `exec c ω i` is the mixed action that
player `i`'s program realises when everybody's code is `c` and the representatives' sample
point is `ω` (the randomness every `Πⱼ(Γ′)` call reads).  The players' actions are
independent given `ω`: each program's own randomness is private, so the outcome
distribution is the product of the `exec c ω i`.  Fibers are measurable so that payoffs
are expectations. -/
structure ProgramGame (Γ₀ : Game N 𝒜) (R : Representatives.{u, v, w} N 𝒜) where
  /-- The instructions available to player `i` (`PROGᵢ`). -/
  Instr : N → Type x
  /-- Execution: everybody's code and the sample point give each player's mixed action. -/
  exec : (∀ i, Instr i) → R.Ω → ∀ i, Γ₀.Mixed i
  /-- Each coordinate of the realised mixture is a measurable function of `ω`. -/
  measurable_exec : ∀ (c : ∀ i, Instr i) (i : N) (b : Γ₀.S i), Measurable fun ω => (exec c ω i).val b

namespace ProgramGame

variable {Γ₀ : Game N 𝒜} {R : Representatives.{u, v, w} N 𝒜} (P : ProgramGame.{u, v, w, x} Γ₀ R)

section payoff

variable [DecidableEq N] [Fintype N]

/-- The induced utility `U(c) = E[u(exec(c))]` (extraction l. 1960): the expectation over
the representatives' sample point of the expected utility of the product mixture. -/
noncomputable def payoff (c : ∀ i, P.Instr i) (i : N) : ℝ :=
  ∫ ω, Γ₀.expected (P.exec c ω) i ∂R.μ

lemma measurable_expected_exec (c : ∀ i, P.Instr i) (i : N) :
    Measurable fun ω => Γ₀.expected (P.exec c ω) i := by
  simp only [Game.expected, expectedPayoff]
  refine Finset.measurable_sum _ fun s _ => Measurable.mul_const ?_ _
  exact Finset.measurable_prod _ fun j _ => P.measurable_exec c j (s j)

lemma integrable_expected_exec (c : ∀ i, P.Instr i) (i : N) :
    Integrable (fun ω => Γ₀.expected (P.exec c ω) i) R.μ :=
  Integrable.of_bound (P.measurable_expected_exec c i).aestronglyMeasurable _
    (ae_of_all _ fun ω => Γ₀.abs_expected_le (P.exec c ω) i)

/-- The program game as an EconCSLib strategic game: strategies are instructions, payoffs
are `U`. -/
noncomputable abbrev toStrategic : StrategicGame N ℝ where
  strategy := P.Instr
  payoff := P.payoff

/-- **Program equilibrium** (extraction l. 1970–1971): a Nash equilibrium of the induced
game — EconCSLib's `IsNashEquilibrium`. -/
def IsProgramEquilibrium (c : ∀ i, P.Instr i) : Prop := IsNashEquilibrium P.toStrategic c

lemma isProgramEquilibrium_iff (c : ∀ i, P.Instr i) :
    P.IsProgramEquilibrium c ↔
      ∀ i (c' : P.Instr i), P.payoff (Function.update c i c') i ≤ P.payoff c i :=
  Iff.rfl

end payoff

variable [∀ i, DecidableEq (𝒜 i)]

/-- `exec(c) = f`: the execution is the deterministic outcome `f ω` at every sample point
(the paper's `exec(c) = Π(Γˢ)`). -/
def Plays (c : ∀ i, P.Instr i) (f : R.Ω → ∀ i, 𝒜 i) : Prop :=
  ∀ ω i (b : Γ₀.S i), (P.exec c ω i).val b = if (b : 𝒜 i) = f ω i then 1 else 0

lemma Plays.exec_eq {c : ∀ i, P.Instr i} {f : R.Ω → ∀ i, 𝒜 i}
    (h : P.Plays c f) (hf : ∀ ω, f ω ∈ Γ₀.profiles) (ω : R.Ω) :
    P.exec c ω = fun j => Γ₀.pureMixed (f ω j) (hf ω j) := by
  funext j
  apply Subtype.ext
  funext b
  rw [h ω j b, Game.pureMixed_val]

end ProgramGame

namespace Representatives

variable (R : Representatives.{u, v, w} N 𝒜) [Fintype N]

/-- `ω ↦ g(Π(Γ)(ω))` is measurable for every real function `g` of the outcome: `Π(Γ)`
takes finitely many values, on measurable fibers. -/
lemma measurable_comp_play (Γ : Game N 𝒜) (g : (∀ i, 𝒜 i) → ℝ) :
    Measurable fun ω => g (R.play Γ ω) := by
  classical
  have : (fun ω => g (R.play Γ ω)) =
      fun ω => ∑ a ∈ Γ.profilesFinset, Set.indicator {ω | R.play Γ ω = a} (fun _ => g a) ω := by
    funext ω
    rw [Finset.sum_eq_single (R.play Γ ω)]
    · simp
    · intro b _ hb
      simp [Set.indicator, Ne.symm hb]
    · intro h
      exact absurd (Γ.mem_profilesFinset.2 (R.toPlay.mem Γ ω)) h
  rw [this]
  exact Finset.measurable_sum _ fun a _ => measurable_const.indicator (R.measurableSet_fiber Γ a)

lemma integrable_comp_play (Γ : Game N 𝒜) (g : (∀ i, 𝒜 i) → ℝ) :
    Integrable (fun ω => g (R.play Γ ω)) R.μ := by
  classical
  refine Integrable.of_bound (R.measurable_comp_play Γ g).aestronglyMeasurable
    (∑ a ∈ Γ.profilesFinset, |g a|) (ae_of_all _ fun ω => ?_)
  exact Finset.single_le_sum (f := fun a => |g a|) (fun a _ => abs_nonneg _)
    (Γ.mem_profilesFinset.2 (R.toPlay.mem Γ ω))

end Representatives

namespace ProgramGame

variable {Γ₀ : Game N 𝒜} {R : Representatives.{u, v, w} N 𝒜} (P : ProgramGame.{u, v, w, x} Γ₀ R)
variable [DecidableEq N] [Fintype N] [∀ i, DecidableEq (𝒜 i)]

/-- If `c` executes as the deterministic outcome `f`, its induced payoff is `E[uᵢ(f)]`. -/
lemma payoff_of_plays {c : ∀ i, P.Instr i} {f : R.Ω → ∀ i, 𝒜 i} (h : P.Plays c f)
    (hf : ∀ ω, f ω ∈ Γ₀.profiles) (i : N) :
    P.payoff c i = ∫ ω, Γ₀.u (f ω) i ∂R.μ := by
  unfold payoff
  congr 1
  funext ω
  rw [h.exec_eq P hf ω, Γ₀.expected_pure (f ω) (hf ω) i]

/-- **Proposition 18 over the interface.**  Let `Γˢ` be an SPI on `Γ₀` for `R`, and let `c`
be a program profile with Algorithm 2's semantics: everybody's execution is `Π(Γˢ)`
(`hcoop`), and against any unilateral deviation `c' ≠ c i` the other players play the
minimax profile against `i` (`hpunish`).  If `Π(Γ₀)` guarantees every player at least their
threat point in expectation (`hthreat`), then `c` is a program equilibrium, and its
execution is `Π(Γˢ)`.

The deviator's payoff is bounded *above* by `vᵢ` (erratum D8: the paper writes equality,
which needs the deviator to best-respond), because against the minimax profile no mixture
of `i`'s earns more than `vᵢ` (`Game.expected_minimax_le_threatPoint`) at every sample
point, and the players' actions are independent given `ω` by the execution model.  The
paper node is carried by the concrete Algorithm 2 term (`Instruction.lean`). -/
lemma isProgramEquilibrium_of_algorithm2 {Γs : Game N 𝒜}
    (hSPI : R.toPlay.IsSPI R.certainty Γ₀ Γs) (c : ∀ i, P.Instr i)
    (hcoop : P.Plays c fun ω => R.play Γs ω)
    (hpunish : ∀ i (c' : P.Instr i), c' ≠ c i → ∀ ω j, j ≠ i →
      P.exec (Function.update c i c') ω j = Γ₀.minimax i j)
    (hthreat : ∀ i, Γ₀.threatPoint i ≤ ∫ ω, Γ₀.u (R.play Γ₀ ω) i ∂R.μ) :
    P.IsProgramEquilibrium c ∧ P.Plays c fun ω => R.play Γs ω := by
  refine ⟨fun i c' => ?_, hcoop⟩
  show P.payoff (Function.update c i c') i ≤ P.payoff c i
  by_cases hc : c' = c i
  · rw [hc, Function.update_eq_self]
  have hmem : ∀ ω, R.play Γs ω ∈ Γ₀.profiles :=
    fun ω => hSPI.1.profiles_subset (R.toPlay.mem Γs ω)
  rw [P.payoff_of_plays hcoop hmem i]
  -- the deviation earns at most the threat point
  have hdev : P.payoff (Function.update c i c') i ≤ Γ₀.threatPoint i := by
    unfold payoff
    calc ∫ ω, Γ₀.expected (P.exec (Function.update c i c') ω) i ∂R.μ
        ≤ ∫ _, Γ₀.threatPoint i ∂R.μ := by
          refine integral_mono (P.integrable_expected_exec _ i) (integrable_const _) fun ω => ?_
          have : P.exec (Function.update c i c') ω =
              Function.update (Γ₀.minimax i) i (P.exec (Function.update c i c') ω i) := by
            funext j
            by_cases hj : j = i
            · subst hj; simp
            · rw [Function.update_of_ne hj, hpunish i c' hc ω j hj]
          rw [this]
          exact Γ₀.expected_minimax_le_threatPoint i _
      _ = Γ₀.threatPoint i := by simp
  -- the SPI earns at least `Π(Γ₀)`, which earns at least the threat point
  have hspi : ∫ ω, Γ₀.u (R.play Γ₀ ω) i ∂R.μ ≤ ∫ ω, Γ₀.u (R.play Γs ω) i ∂R.μ := by
    refine integral_mono_ae (R.integrable_comp_play Γ₀ (Γ₀.u · i))
      (R.integrable_comp_play Γs (Γ₀.u · i)) ?_
    filter_upwards [hSPI.2] with ω hω
    exact hω i
  exact hdev.trans ((hthreat i).trans hspi)

end ProgramGame

end SafeParetoImprovements
