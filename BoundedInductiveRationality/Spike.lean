/-
# Spike: A Theory of Bounded Inductive Rationality (Oesterheld, Demski, Conitzer,
  TARK 2023 / arXiv:2307.05068) — feasibility probe, NOT a formalization.

Purpose: decide whether BIR is CF-like, FSM-like, or LI-like, with compiled evidence.
Everything here is a *probe*; nothing is wired into the paper registry, the trust
surface, or `AxiomAudit`.

The file is organised as the report is:

* §A  the extensional BRIA layer (paper Definitions 1–7) and its reading lemmas;
* §B  the asymptotic toolkit the paper needs over and over;
* §C  Theorem 3 (guaranteed payoff), mathematical core, with the *class-membership*
      obligation left as an explicit hypothesis rather than hidden in a predicate;
* §D  Theorem 1's auction — the real experiment: wealth, allowance, argmax
      attainment, no-overestimation, coverage, over a genuinely **countable**
      hypothesis family;
* §E  a concrete allowance schedule and its three analytic properties;
* §F  Theorem 2's diagonal argument, extensionally;
* §G  Definition 8 / Theorem 4 — vMWC randomness, including a compiled refutation of
      the printed Definition 8;
* §H  the game layer: the converse half of Theorem 5 reduced to §C;
* §I  the computability interface — what the extensional layer provably cannot say.

Provenance keys: the paper carries two independent global counters (`Definition 1..10`
and a shared `Theorem/Lemma 1..9`), so printed numbers are the identifiers. Docstrings
cite them; no `Paper node:` lines, because this is a spike and must not be picked up by
the node checkers.
-/
import Mathlib

namespace BIRSpike

open Filter Topology Finset

/-! Classical decidability once, for the whole file: `M ∩ range T` is a `Finset.filter`
over an arbitrary `Set ℕ` membership predicate, and a per-proof `classical` makes the
instances differ syntactically between a definition and the lemmas about it. -/
attribute [local instance] Classical.propDecidable

/-! # §A. The extensional layer — paper §2 and §4

## A.0 Representation decisions

Three choices, each recorded because a real formalization inherits them.

* **`dd:index0`** — the paper indexes time from `1` (`∑_{t=1}^T`); we index from `0`
  and read `∑_{t=1}^T` as `∑ t ∈ Finset.range T`, i.e. "the first `T` rounds". Every
  paper statement in scope is asymptotic in `T`, so the shift is a relabelling. It is
  *not* free of content: it also silently resolves the paper's own `t ≤ T` (Definition
  5) versus `t < T` (proofs of Theorems 1 and 3) inconsistency — see
  `record_shift_le_one` for the exact cost of that discrepancy.

* **`dd:realrewards`** — rewards, estimates and promises are plain `ℝ` carrying
  `Set.Icc 0 1` membership as a hypothesis, not `↥(Set.Icc 0 1)`. Rationale: every
  paper argument is an inequality chain fed to `linarith`, and a subtype forces a
  `Subtype.val` coercion into every one of them. The `[0,1]` bounds are genuinely
  load-bearing only in a handful of places (`h.estimate t ≤ 1` in the auction's
  coverage step), and carrying them as hypotheses makes those places visible.

* **`dd:agentbundle`** — the paper says a hypothesis "has the same type signature as an
  estimating agent". We render both by one structure. This is faithful *extensionally*
  and is exactly where the paper's extensional/intensional slippage lives: §5's
  "computably enumerable set consisting of `O(g(t))`-computable hypotheses" quantifies
  over programs, not sequences, and §2's "`DP_t` may in turn be calculated depending on
  the agent's choices" makes the sequence reading circular. See §I. -/

variable {Action : Type*}

/-- **Definition (§4.1)** — an estimating agent for a decision problem sequence `DP`:
choices `αᶜ_t ∈ DP_t` and estimates `αᵉ_t ∈ [0,1]`. A *hypothesis* has the same type
signature (`dd:agentbundle`); its `choice` is the paper's recommendation `hᶜ` and its
`estimate` the promise `hᵉ`. -/
structure Agent (DP : ℕ → Finset Action) where
  choice : ℕ → Action
  estimate : ℕ → ℝ
  choice_mem : ∀ t, choice t ∈ DP t
  estimate_nonneg : ∀ t, 0 ≤ estimate t
  estimate_le_one : ∀ t, estimate t ≤ 1

/-- A hypothesis is an agent (`dd:agentbundle`). Kept as a separate name so statements
read against the paper. -/
abbrev Hypothesis (DP : ℕ → Finset Action) := Agent DP

variable {DP : ℕ → Finset Action}

/-- **Definition 1** — cumulative overestimation `L_T(ᾱ, r̄) = ∑_{t=1}^T αᵉ_t − r_t`
(`dd:index0`). -/
def cumOver (α : Agent DP) (r : ℕ → ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ range T, (α.estimate t - r t)

/-- **Definition 2** — `ᾱ` does not overestimate on average in the limit. Stated in the
paper's own gloss: "for all `ε > 0` there should be a time `t` such that for all
`T > t`, `L_T/T ≤ ε`". -/
def NoOverestimation (α : Agent DP) (r : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ T in atTop, cumOver α r T / T ≤ ε

/-- **Definition 3** — `h̄` outpromises `ᾱ` (equivalently `ᾱ` rejects `h̄`) at `t`. -/
def Rejects (α : Agent DP) (h : Hypothesis DP) (t : ℕ) : Prop :=
  α.estimate t < h.estimate t

/-- The paper's `B`: the set of times at which `ᾱ` rejects `h̄` (**Definition 6**). -/
def rejectionSet (α : Agent DP) (h : Hypothesis DP) : Set ℕ :=
  {t | Rejects α h t}

/-- **Definition 4** — `M ⊆ ℕ` is a test set of `ᾱ` for `h̄`. -/
def IsTestSet (α : Agent DP) (h : Hypothesis DP) (M : Set ℕ) : Prop :=
  ∀ t ∈ M, α.choice t = h.choice t

/-- **Definition 5** — the empirical record `l_T(ᾱ, r̄, M, h̄) = ∑_{t ∈ M_{≤T}} r_t − hᵉ_t`
(`dd:index0`: `M_{<T}` here; see `record_shift_le_one`). -/
noncomputable def sel (M : Set ℕ) (T : ℕ) : Finset ℕ :=
  @Finset.filter _ (fun t => t ∈ M) (Classical.decPred _) (range T)

@[simp] theorem mem_sel {M : Set ℕ} {T t : ℕ} : t ∈ sel M T ↔ t < T ∧ t ∈ M := by
  simp [sel]

@[simp] theorem sel_univ (T : ℕ) : sel Set.univ T = range T := by
  ext t; simp

noncomputable def record (r : ℕ → ℝ) (M : Set ℕ) (h : Hypothesis DP) (T : ℕ) : ℝ :=
  ∑ t ∈ sel M T, (r t - h.estimate t)

/-- The filter "`T → ∞` along `B`". This is the representation decision behind
**Definition 6**; `covers_iff_forall` below discharges the obligation to show it says
what the paper says, and `not_covers_of_globally_bounded_below` /
`covers_of_tendsto_atBot` fix its relation to the global statement. -/
abbrev alongAtTop (B : Set ℕ) : Filter ℕ := atTop ⊓ 𝓟 B

/-- **Definition 6** — `ᾱ` covers `h̄` with test set `M`: either the rejection set `B` is
finite, or `(l_T)_{T ∈ B} → −∞`. -/
def Covers (α : Agent DP) (r : ℕ → ℝ) (h : Hypothesis DP) (M : Set ℕ) : Prop :=
  (rejectionSet α h).Finite ∨
    Tendsto (record r M h) (alongAtTop (rejectionSet α h)) atBot

/-- **Definition 7** — `ᾱ` is a boundedly rational inductive agent for `DP, r̄` covering
the enumerated family `H` with test sets `M`. The paper writes `H = {h₁, h₂, …}`; the
enumeration is not decoration — Theorem 1 needs it — so `H` is indexed, not a `Set`. -/
structure IsBRIA (α : Agent DP) (r : ℕ → ℝ) {ι : Type*}
    (H : ι → Hypothesis DP) (M : ι → Set ℕ) : Prop where
  noOverestimation : NoOverestimation α r
  testSet : ∀ i, IsTestSet α (H i) (M i)
  covers : ∀ i, Covers α r (H i) (M i)

/-! ## A.1 Reading lemmas for Definition 6

The paper's Definition 6 is a disjunction. It collapses: when `B` is finite the filter
`alongAtTop B` is `⊥`, and `Tendsto f ⊥ l` holds for every `f` and `l`. So the printed
disjunction is redundant — one filter statement is the whole definition. This is worth
knowing before anyone writes fifty case splits. -/

/-- `alongAtTop B` is nontrivial exactly when `B` is infinite. -/
theorem alongAtTop_neBot_iff {B : Set ℕ} : (alongAtTop B).NeBot ↔ B.Infinite := by
  rw [alongAtTop, show B = {x | x ∈ B} from rfl, ← frequently_iff_neBot]
  exact Nat.frequently_atTop_iff_infinite

theorem alongAtTop_eq_bot_of_finite {B : Set ℕ} (hB : B.Finite) : alongAtTop B = ⊥ := by
  by_contra h
  exact hB.not_infinite (alongAtTop_neBot_iff.1 ⟨h⟩)

/-- **Definition 6, collapsed.** The disjunction in the printed definition carries no
information: the finite case is subsumed. -/
theorem covers_iff_tendsto (α : Agent DP) (r : ℕ → ℝ) (h : Hypothesis DP) (M : Set ℕ) :
    Covers α r h M ↔
      Tendsto (record r M h) (alongAtTop (rejectionSet α h)) atBot := by
  refine ⟨fun hc => ?_, fun hc => Or.inr hc⟩
  rcases hc with hfin | ht
  · rw [alongAtTop_eq_bot_of_finite hfin]; exact tendsto_bot
  · exact ht

/-- **Definition 6, unfolded.** The `ε`-`N` reading, so nobody has to trust the filter
encoding: for every bound `C` there is a time `N` past which *every rejection time*
`T ∈ B` has record below `C`. Note the quantifier is over `T ∈ B` only — this is the
statement `Covers` makes, and it is strictly weaker than the same statement for all
`T` (see `not_tendsto_atBot_globally_of_...` below). -/
theorem covers_iff_forall (α : Agent DP) (r : ℕ → ℝ) (h : Hypothesis DP) (M : Set ℕ) :
    Covers α r h M ↔
      ∀ C : ℝ, ∃ N : ℕ, ∀ T ∈ rejectionSet α h, N ≤ T → record r M h T ≤ C := by
  rw [covers_iff_tendsto, tendsto_atBot]
  constructor
  · intro hc C
    have := hc C
    rw [alongAtTop, eventually_inf_principal, eventually_atTop] at this
    obtain ⟨N, hN⟩ := this
    exact ⟨N, fun T hT hNT => hN T hNT hT⟩
  · intro hc C
    obtain ⟨N, hN⟩ := hc C
    rw [alongAtTop, eventually_inf_principal, eventually_atTop]
    exact ⟨N, fun T hNT hT => hN T hT hNT⟩

/-- Global convergence to `−∞` implies the paper's `B`-restricted statement. -/
theorem covers_of_tendsto_atBot {α : Agent DP} {r : ℕ → ℝ} {h : Hypothesis DP}
    {M : Set ℕ} (hg : Tendsto (record r M h) atTop atBot) : Covers α r h M :=
  Or.inr (hg.mono_left inf_le_left)

/-- …and **not** conversely. A hypothesis rejected only at even times, whose record
oscillates, is covered without the record converging globally. This is the compiled
form of the instruction not to replace "the sequence indexed by `B` tends to `−∞`" with
a global statement: the two are genuinely different. -/
example : ∃ (f : ℕ → ℝ) (B : Set ℕ),
    Tendsto f (alongAtTop B) atBot ∧ ¬ Tendsto f atTop atBot := by
  refine ⟨fun T => if Even T then -(T : ℝ) else 0, {T | Even T}, ?_, ?_⟩
  · rw [alongAtTop, tendsto_atBot]
    intro C
    rw [eventually_inf_principal, eventually_atTop]
    refine ⟨⌈max 0 (-C)⌉₊, fun T hT hTe => ?_⟩
    simp only [Set.mem_setOf_eq] at hTe
    simp only [hTe, if_pos]
    have h1 : (⌈max 0 (-C)⌉₊ : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
    have h2 : -C ≤ (⌈max 0 (-C)⌉₊ : ℝ) :=
      le_trans (le_max_right 0 (-C)) (Nat.le_ceil _)
    linarith
  · intro hg
    obtain ⟨N, hN⟩ := eventually_atTop.1 (tendsto_atBot.1 hg (-1))
    have hodd : ¬ Even (2 * N + 1) := by simp [parity_simps]
    have := hN (2 * N + 1) (by omega)
    simp only [hodd, if_neg, not_false_eq_true] at this
    linarith


/-- The `t ≤ T` / `t < T` discrepancy costs one term, whose size is at most `1` because
promises and rewards live in `[0,1]`. So *no* asymptotic statement in the paper is
sensitive to it, and `dd:index0` may resolve it either way. This is the compiled reason
the inconsistency between Definition 5 (`M_{≤T}`) and the proofs of Theorems 1 and 3
(`t ∈ M_i : t < T`) is an erratum and not a defect. -/
theorem record_shift_le_one {r : ℕ → ℝ} (hr0 : ∀ t, 0 ≤ r t) (hr1 : ∀ t, r t ≤ 1)
    {M : Set ℕ} {h : Hypothesis DP} (T : ℕ) :
    |record r M h (T + 1) - record r M h T| ≤ 1 := by
  unfold record
  rw [show sel M (T + 1) = if T ∈ M then insert T (sel M T) else sel M T by
    simp only [sel, Finset.range_add_one, Finset.filter_insert]]
  by_cases hT : T ∈ M
  · rw [if_pos hT, Finset.sum_insert (by simp)]
    have h1 := hr0 T; have h2 := hr1 T
    have h3 := h.estimate_nonneg T; have h4 := h.estimate_le_one T
    rw [add_sub_cancel_right, abs_le]; constructor <;> linarith
  · rw [if_neg hT, sub_self, abs_zero]; linarith

/-! ## A.2 Non-vacuity: the three ways Definition 6 can go

Cheap concrete witnesses, so nobody can read the definitions as vacuous. `Action` is
`Bool` and `DP t` is everything. -/

section Witnesses

/-- The all-options decision problem sequence on `Bool`. -/
def boolDP : ℕ → Finset Bool := fun _ => Finset.univ

/-- A constant agent/hypothesis: always choose `c`, always estimate `e ∈ [0,1]`. -/
def constAgent (c : Bool) (e : ℝ) (h0 : 0 ≤ e) (h1 : e ≤ 1) : Agent boolDP where
  choice _ := c
  estimate _ := e
  choice_mem _ := Finset.mem_univ _
  estimate_nonneg _ := h0
  estimate_le_one _ := h1

/-- **Covered because it stops outpromising.** The hypothesis promises `0`, the agent
estimates `1/2`; the rejection set is empty, so Definition 6's first disjunct fires and
no test is ever required. -/
example :
    Covers (constAgent true (1/2) (by norm_num) (by norm_num))
      (fun _ => 0) (constAgent true 0 le_rfl zero_le_one) ∅ := by
  refine Or.inl (Set.Finite.subset (Set.finite_empty) ?_)
  intro t ht
  simp [rejectionSet, Rejects, constAgent] at ht
  linarith

/-- **Covered because repeated tests drive the record down.** The hypothesis promises
`1` in every round, the agent estimates `0`, and every round is a test that pays `0`. -/
example :
    Covers (constAgent true 0 le_rfl zero_le_one) (fun _ => 0)
      (constAgent true 1 zero_le_one le_rfl) Set.univ := by
  refine Or.inr ((?_ : Tendsto (record (DP := boolDP) (fun _ => 0) Set.univ
      (constAgent true 1 zero_le_one le_rfl)) atTop atBot).mono_left inf_le_left)
  have hrec : record (DP := boolDP) (fun _ => 0) Set.univ
      (constAgent true 1 zero_le_one le_rfl) = fun T : ℕ => -(T : ℝ) := by
    funext T; simp [record, constAgent]
  rw [hrec]
  exact tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop (R := ℝ))

/-- **Not covered.** The hypothesis promises `1` and *keeps* its promise every round,
while outpromising the agent infinitely often. Its record is identically `0`, so no
test set can rescue coverage. This is the shape every "`ᾱ` is not a BRIA" argument in
the paper takes (Theorems 2, 3, 4, 9). -/
example (M : Set ℕ) :
    ¬ Covers (constAgent true 0 le_rfl zero_le_one) (fun _ => 1)
        (constAgent true 1 zero_le_one le_rfl) M := by
  rw [covers_iff_forall]
  push Not
  refine ⟨-1, fun N => ⟨N, ?_, le_rfl, ?_⟩⟩
  · simp [rejectionSet, Rejects, constAgent]
  · have : record (DP := boolDP) (fun _ => 1) M
        (constAgent true 1 zero_le_one le_rfl) N = 0 := by
      simp [record, constAgent]
    rw [this]; norm_num

end Witnesses

/-! # §B. The asymptotic toolkit

Everything the paper does with limits is one of four moves: a Cesàro average, an
"eventually" inequality, a finite exceptional prefix, and a divergence to `±∞`. Mathlib
supplies the last two directly; the first two are the ones that need bespoke lemmas,
and they are cheap. -/

/-- Cesàro average of the first `T` terms. -/
noncomputable def avg (f : ℕ → ℝ) (T : ℕ) : ℝ := (∑ t ∈ range T, f t) / T

/-- The paper's `x ≥ y as T → ∞`, in the form its own Definition 2 gloss uses (this is
`LogicalInduction.AsympGE`, spelled locally so the spike has no cross-paper import). -/
def AsympGE (f g : ℕ → ℝ) : Prop := ∀ ε > 0, ∀ᶠ T in atTop, g T ≤ f T + ε

/-- **Definition 2, alternative reading.** No-overestimation is exactly
`limsup (L_T / T) ≤ 0`. Recorded because the `limsup` form is what a `Filter`-fluent
prover reaches for, and the paper's `∀ ε` form is what its proofs use; a real
development wants both and should not re-derive the bridge twice. -/
theorem noOverestimation_iff_limsup (α : Agent DP) (r : ℕ → ℝ)
    (hb : ∃ C, ∀ T, |cumOver α r T / T| ≤ C) :
    NoOverestimation α r ↔ limsup (fun T => cumOver α r T / T) atTop ≤ 0 := by
  obtain ⟨C, hC⟩ := hb
  have hbdd : IsBoundedUnder (· ≤ ·) atTop (fun T => cumOver α r T / T) :=
    isBoundedUnder_of ⟨C, fun (T : ℕ) => (abs_le.1 (hC T)).2⟩
  have hbdd' : IsBoundedUnder (· ≥ ·) atTop (fun T => cumOver α r T / T) :=
    isBoundedUnder_of ⟨-C, fun (T : ℕ) => (abs_le.1 (hC T)).1⟩
  constructor
  · intro h
    refine le_of_forall_gt_imp_ge_of_dense fun ε hε => ?_
    exact limsup_le_of_le hbdd'.isCoboundedUnder_le (h ε (by linarith))
  · intro h ε hε
    exact eventually_lt_of_limsup_lt (lt_of_le_of_lt h hε) hbdd |>.mono fun T hT => hT.le

/-- **Finite exceptional sets do not affect Cesàro limits.** Mathlib has
`Filter.Tendsto.cesaro` (a converging sequence's averages converge) but not this: two
sequences agreeing eventually have the same Cesàro behaviour, with *no* boundedness
hypothesis, because the difference of partial sums is eventually constant. Fifteen lines,
and the paper leans on it in every proof that says "for all but finitely many `t`". -/
theorem avg_sub_tendsto_zero_of_eventuallyEq {f g : ℕ → ℝ}
    (h : ∀ᶠ t in atTop, f t = g t) :
    Tendsto (fun T => avg f T - avg g T) atTop (𝓝 0) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  set K : ℝ := ∑ t ∈ range N, (f t - g t) with hK
  have hconst : ∀ T, N ≤ T → ∑ t ∈ range T, (f t - g t) = K := by
    intro T hT
    rw [hK, ← Finset.sum_range_add_sum_Ico _ hT, add_eq_left]
    exact Finset.sum_eq_zero fun t ht => by rw [hN t (Finset.mem_Ico.1 ht).1, sub_self]
  refine Tendsto.congr' ?_ (tendsto_const_div_atTop_nhds_zero_nat K)
  filter_upwards [eventually_ge_atTop N] with T hT
  unfold avg
  rw [div_sub_div_same, ← Finset.sum_sub_distrib, hconst T hT]

/-- **The transfer step of Theorems 3, 4, 8 and 9**, isolated: if the agent's estimate
eventually dominates a `[0,1]`-valued sequence `L`, and the agent does not overestimate,
then its average reward eventually dominates the average of `L`.

The finite exceptional prefix is handled by the `[0,1]` bound, not by a Cesàro theorem:
each of the `N` exceptional terms is at least `-1`, so the prefix contributes at most
`N/T → 0`. That is the whole of "finite exceptional sets do not affect Cesàro limits"
in the form this paper needs, and it costs no Mathlib machinery. -/
theorem avg_ge_of_eventually_estimate_ge {α : Agent DP} {r L : ℕ → ℝ}
    (_hL0 : ∀ t, 0 ≤ L t) (hL1 : ∀ t, L t ≤ 1)
    (hno : NoOverestimation α r)
    (hev : ∀ᶠ t in atTop, L t ≤ α.estimate t) :
    AsympGE (avg r) (avg L) := by
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  -- the prefix bound
  have hprefix : ∀ T, N ≤ T →
      ∑ t ∈ range T, (L t - r t) ≤ cumOver α r T + N := by
    intro T hT
    have hsplit : ∑ t ∈ range T, (α.estimate t - L t)
        = ∑ t ∈ range N, (α.estimate t - L t)
          + ∑ t ∈ Finset.Ico N T, (α.estimate t - L t) := by
      rw [← Finset.sum_range_add_sum_Ico _ hT]
    have htail : 0 ≤ ∑ t ∈ Finset.Ico N T, (α.estimate t - L t) :=
      Finset.sum_nonneg fun t ht => by
        have := hN t (Finset.mem_Ico.1 ht).1; linarith
    have hhead : -(N : ℝ) ≤ ∑ t ∈ range N, (α.estimate t - L t) := by
      have : ∀ t ∈ range N, (-1 : ℝ) ≤ α.estimate t - L t := fun t _ => by
        have := α.estimate_nonneg t; have := hL1 t; linarith
      calc -(N : ℝ) = ∑ _t ∈ range N, (-1 : ℝ) := by simp
        _ ≤ _ := Finset.sum_le_sum this
    have hkey : -(N : ℝ) ≤ ∑ t ∈ range T, (α.estimate t - L t) := by
      rw [hsplit]; linarith
    have : ∑ t ∈ range T, (L t - r t)
        = cumOver α r T - ∑ t ∈ range T, (α.estimate t - L t) := by
      unfold cumOver; rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intros; ring
    rw [this]; linarith
  filter_upwards [hno (ε/2) (by linarith), eventually_ge_atTop N,
    eventually_ge_atTop (max 1 ⌈2 * N / ε⌉₊)] with T hT1 hTN hTbig
  have hT0 : (0 : ℝ) < T := by
    have h1 : (1 : ℕ) ≤ T := le_trans (le_max_left _ _) hTbig
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one h1
  have hNle : (N : ℝ) ≤ (ε / 2) * T := by
    have h1 : (⌈2 * (N : ℝ) / ε⌉₊ : ℝ) ≤ T := by
      exact_mod_cast le_trans (le_max_right _ _) hTbig
    have h2 : (2 : ℝ) * N / ε ≤ ⌈2 * (N : ℝ) / ε⌉₊ := Nat.le_ceil _
    have h3 : (2 : ℝ) * N / ε ≤ T := le_trans h2 h1
    rw [div_le_iff₀ hε] at h3
    linarith
  have hcum : cumOver α r T ≤ (ε / 2) * T := by
    rw [div_le_iff₀ hT0] at hT1; linarith
  have hsum : (∑ t ∈ range T, L t) - (∑ t ∈ range T, r t) ≤ ε * T := by
    have hp := hprefix T hTN
    rw [Finset.sum_sub_distrib] at hp
    linarith
  unfold avg
  rw [← sub_le_iff_le_add', div_sub_div_same, div_le_iff₀ hT0]
  linarith


/-! # §C. Theorem 3 — guaranteed payoffs

Two generic lemmas, then the theorem. The generic lemmas are the engine of *every*
positive result in the paper (Theorems 3, 4, 5-converse, 8, 9): each one exhibits a
hypothesis that keeps its promises, concludes that its record cannot diverge, and reads
off from coverage that the agent stops rejecting it. -/

/-- A hypothesis that keeps its promises on its test set has a nonnegative record. -/
theorem record_nonneg {r : ℕ → ℝ} {M : Set ℕ} {h : Hypothesis DP}
    (hkeep : ∀ t ∈ M, h.estimate t ≤ r t) (T : ℕ) : 0 ≤ record r M h T :=
  Finset.sum_nonneg fun t ht => by
    have htM : t ∈ M := (mem_sel.1 ht).2
    linarith [hkeep t htM]

/-- **The coverage lever.** If a hypothesis' record is bounded below and the agent
covers it, the agent can reject it only finitely often. Every "therefore `ᾱ` is not a
BRIA" step in the paper is this lemma. -/
theorem rejectionSet_finite_of_record_bddBelow {α : Agent DP} {r : ℕ → ℝ}
    {h : Hypothesis DP} {M : Set ℕ} (hcov : Covers α r h M)
    {C : ℝ} (hbb : ∀ T, C ≤ record r M h T) : (rejectionSet α h).Finite := by
  by_contra hinf
  have : (alongAtTop (rejectionSet α h)).NeBot :=
    alongAtTop_neBot_iff.2 (Set.not_finite.1 hinf)
  have hev := tendsto_atBot.1 ((covers_iff_tendsto α r h M).1 hcov) (C - 1)
  obtain ⟨T, hT⟩ := hev.exists
  linarith [hbb T]

/-- **Theorem 3 — mathematical core.** If some hypothesis in the covered family
recommends, at every time, an option that guarantees at least its own promise, then the
agent's average reward eventually dominates that promise sequence.

Everything the printed theorem asserts is proved here **except** the sentence "Because
`L̄` is e.c. and the `ā` are efficiently identifiable, `h̄` is e.c." — that sentence is
exactly the hypothesis `i : ι` together with `hi`. Keeping it an explicit index rather
than a `EfficientlyComputable` side condition is the point: it is the whole
computational content of the theorem, and it is the only thing left. -/
theorem theorem3_core {ι : Type*} {α : Agent DP} {r : ℕ → ℝ}
    {H : ι → Hypothesis DP} {M : ι → Set ℕ} (hBRIA : IsBRIA α r H M)
    (a : ℕ → Action) (L : ℕ → ℝ)
    (hL0 : ∀ t, 0 ≤ L t) (hL1 : ∀ t, L t ≤ 1)
    (hguar : ∀ t, α.choice t = a t → L t ≤ r t)
    -- the residue: the guarantee hypothesis `h_t = (a_t, L_t)` belongs to the family
    (i : ι) (hia : (H i).choice = a) (hiL : (H i).estimate = L) :
    AsympGE (avg r) (avg L) := by
  have hkeep : ∀ t ∈ M i, (H i).estimate t ≤ r t := by
    intro t ht
    have hc : α.choice t = a t := hia ▸ hBRIA.testSet i t ht
    rw [hiL]; exact hguar t hc
  have hfin : (rejectionSet α (H i)).Finite :=
    rejectionSet_finite_of_record_bddBelow (hBRIA.covers i)
      (C := 0) (record_nonneg hkeep)
  have hev : ∀ᶠ t in atTop, L t ≤ α.estimate t := by
    obtain ⟨N, hN⟩ := (Set.Finite.bddAbove hfin)
    refine eventually_atTop.2 ⟨N + 1, fun t ht => ?_⟩
    by_contra hlt
    push Not at hlt
    have : t ∈ rejectionSet α (H i) := by
      simp only [rejectionSet, Set.mem_setOf_eq, Rejects, hiL]; exact hlt
    exact absurd (hN this) (by omega)
  exact avg_ge_of_eventually_estimate_ge hL0 hL1 hBRIA.noOverestimation hev

/-- **Theorem 3, as printed** — the same statement with the paper's own phrasing of the
class-membership side condition: there *exists* an index whose hypothesis is `(ā, L̄)`.
The hypothesis `hmem` is the formal residue of "`h̄` is e.c."; see §I for what it would
take to discharge it. -/
theorem theorem3 {ι : Type*} {α : Agent DP} {r : ℕ → ℝ}
    {H : ι → Hypothesis DP} {M : ι → Set ℕ} (hBRIA : IsBRIA α r H M)
    (a : ℕ → Action) (L : ℕ → ℝ)
    (hL0 : ∀ t, 0 ≤ L t) (hL1 : ∀ t, L t ≤ 1)
    (hguar : ∀ t, α.choice t = a t → L t ≤ r t)
    (hmem : ∃ i, (H i).choice = a ∧ (H i).estimate = L) :
    AsympGE (avg r) (avg L) := by
  obtain ⟨i, hia, hiL⟩ := hmem
  exact theorem3_core hBRIA a L hL0 hL1 hguar i hia hiL


/-! # §D. Theorem 1 — the auction construction

This is the load-bearing experiment. The claim being tested is the one the report calls
**Theorem 1a**:

> Given a countably enumerated hypothesis family and an allowance schedule satisfying
> the paper's three requirements, the first-price auction construction *extensionally
> defines a BRIA covering the family*, with the winning-round sets as test sets.

No computability anywhere; the family is genuinely `ℕ`-indexed, not a finite toy.

Two things the paper does not do are done here because they are load-bearing.

1. **Attainment of the `arg max`.** Display (2) picks `i*_t ∈ arg max_{i∈ℕ} min(hᵉ_{i,t},
   w_t(i))` over *infinitely many* hypotheses. Nothing guarantees a maximum exists —
   `sup` over `ℕ` need not be attained. It does exist, but only because the per-round
   allowance total is finite, which forces the bids to tend to `0`. That derivation is
   `wealth_tendsto_zero` + `exists_max_of_tendsto_zero`, and it is absent from the paper.

2. **The wealth identity is an inequality.** The proof of part 3C asserts
   `w_T(i) = ∑_{n<T} A(n,i) + ∑_{t∈M_i, t<T} (r_t − hᵉ_{i,t})`. That is false: the winner
   pays its *wealth-bounded* bid `min(hᵉ, w)`, not `hᵉ`. The true statement is
   `wealth_eq_allowance_add_net` with `bid` in place of `hᵉ`, and the inequality
   `record_le_wealth_sub_allowance` — which happens to point the way the argument needs.
-/

section Auction

variable {DP : ℕ → Finset Action}

/-- The paper's allowance function `A : ℕ × ℕ → ℝ≥0` with its three stated
requirements, verbatim (Appendix A.2, part 1). -/
structure Allowance where
  /-- `A n i` is the allowance paid to hypothesis `i` at time `n`. -/
  A : ℕ → ℕ → ℝ
  nonneg : ∀ n i, 0 ≤ A n i
  /-- "the allowance distributed in any particular round must be finite". -/
  rowSummable : ∀ n, Summable (A n)
  /-- "Each hypothesis must get infinite overall allowance, `∑_n A(n,i) = ∞`". -/
  colNotSummable : ∀ i, ¬ Summable (fun n => A n i)
  /-- "The overall allowance distributed per round `n` must go to zero", display (1). -/
  avgTotalTendstoZero :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, ∑' i, A n i) / N) atTop (𝓝 0)

namespace Allowance

variable (Al : Allowance)

/-- Requirement (i) in the form the coverage proof consumes: cumulative allowance to a
fixed hypothesis diverges. Mathlib supplies the bridge
(`not_summable_iff_tendsto_nat_atTop_of_nonneg`); nothing needs proving by hand. -/
theorem colSums_tendsto_atTop (i : ℕ) :
    Tendsto (fun T => ∑ n ∈ range T, Al.A n i) atTop atTop :=
  (not_summable_iff_tendsto_nat_atTop_of_nonneg (fun n => Al.nonneg n i)).1
    (Al.colNotSummable i)

theorem colSums_nonneg (i T : ℕ) : 0 ≤ ∑ n ∈ range T, Al.A n i :=
  Finset.sum_nonneg fun n _ => Al.nonneg n i

end Allowance

/-! ## D.1 The `arg max` attainment lemma the paper skips -/

/-- A nonnegative sequence tending to `0` attains its maximum. This is display (2)'s
missing side condition. -/
theorem exists_max_of_tendsto_zero {f : ℕ → ℝ} (hf : ∀ i, 0 ≤ f i)
    (h : Tendsto f atTop (𝓝 0)) : ∃ i, ∀ j, f j ≤ f i := by
  by_cases hz : ∀ i, f i = 0
  · exact ⟨0, fun j => by rw [hz j, hz 0]⟩
  push Not at hz
  obtain ⟨i₀, hi₀⟩ := hz
  have hpos : 0 < f i₀ := lt_of_le_of_ne (hf i₀) (Ne.symm hi₀)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h.eventually (eventually_lt_nhds hpos))
  set S : Finset ℕ := (range N).filter (fun j => f i₀ ≤ f j) with hS
  have hi₀N : i₀ < N := by
    by_contra hc
    exact absurd (hN i₀ (by omega)) (by linarith)
  have hne : S.Nonempty := ⟨i₀, by simp [hS, hi₀N]⟩
  obtain ⟨i, hiS, hmax⟩ := Finset.exists_max_image S f hne
  refine ⟨i, fun j => ?_⟩
  by_cases hj : j ∈ S
  · exact hmax j hj
  · have hle : f i₀ ≤ f i := hmax i₀ (by simp [hS, hi₀N])
    have : f j < f i₀ := by
      by_cases hjN : j < N
      · simp only [hS, Finset.mem_filter, Finset.mem_range] at hj
        exact lt_of_not_ge (fun hc => hj ⟨hjN, hc⟩)
      · exact hN j (by omega)
    linarith

/-- Total winner selection: the `arg max` where one exists, `0` otherwise. Keeping this
total decouples the recursion from the attainment proof — `winner_isMax` below shows the
fallback is never taken. This is the Lean-idiom finding for Theorem 1: a partial
`arg max` inside a `Nat.rec` would force the whole invariant into the definition. -/
noncomputable def pickWinner (b : ℕ → ℝ) : ℕ :=
  if h : ∃ i, ∀ j, b j ≤ b i then h.choose else 0

theorem pickWinner_isMax {b : ℕ → ℝ} (h : ∃ i, ∀ j, b j ≤ b i) (j : ℕ) :
    b j ≤ b (pickWinner b) := by
  rw [pickWinner, dif_pos h]; exact h.choose_spec j

/-! ## D.2 The construction -/

variable (Al : Allowance) (H : ℕ → Hypothesis DP) (r : ℕ → ℝ)

/-- Wealth variables. `w₀(i) = 0`; each round every hypothesis receives its allowance
and the winner is additionally credited `r_t` and debited its wealth-bounded bid. -/
noncomputable def wealth : ℕ → ℕ → ℝ
  | 0, _ => 0
  | t + 1, i =>
      wealth t i + Al.A t i +
        (if i = pickWinner (fun j => min ((H j).estimate t) (wealth t j))
          then r t - min ((H i).estimate t) (wealth t i) else 0)

/-- The wealth-bounded bid `min(hᵉ_{i,t}, w_t(i))` of display (2). -/
noncomputable def bid (t i : ℕ) : ℝ := min ((H i).estimate t) (wealth Al H r t i)

/-- The winning hypothesis `i*_t`. -/
noncomputable def winner (t : ℕ) : ℕ := pickWinner (bid Al H r t)

theorem wealth_succ (t i : ℕ) :
    wealth Al H r (t + 1) i = wealth Al H r t i + Al.A t i +
      (if i = winner Al H r t then r t - bid Al H r t i else 0) := rfl

theorem bid_le_estimate (t i : ℕ) : bid Al H r t i ≤ (H i).estimate t := min_le_left _ _

theorem bid_le_wealth (t i : ℕ) : bid Al H r t i ≤ wealth Al H r t i := min_le_right _ _

theorem bid_le_one (t i : ℕ) : bid Al H r t i ≤ 1 :=
  le_trans (bid_le_estimate Al H r t i) ((H i).estimate_le_one t)

/-- Wealth never goes negative: the winner's debit is capped by its wealth and its
credit `r_t` is nonnegative. (The paper states this for "positive"; the construction
starts at `0`, so nonnegativity is the right invariant.) -/
theorem wealth_nonneg (hr : ∀ t, 0 ≤ r t) : ∀ t i, 0 ≤ wealth Al H r t i := by
  intro t
  induction t with
  | zero => intro i; simp [wealth]
  | succ t ih =>
    intro i
    rw [wealth_succ]
    have h1 := ih i
    have h2 := Al.nonneg t i
    by_cases hw : i = winner Al H r t
    · rw [if_pos hw]
      have := bid_le_wealth Al H r t i
      have := hr t
      linarith
    · rw [if_neg hw]; linarith

theorem bid_nonneg (hr : ∀ t, 0 ≤ r t) (t i : ℕ) : 0 ≤ bid Al H r t i :=
  le_min ((H i).estimate_nonneg t) (wealth_nonneg Al H r hr t i)

/-- **The attainment argument.** At every fixed time, wealth tends to `0` as the
hypothesis index grows — because the per-round allowance total is finite, so `A t ·`
is a null sequence, and only one hypothesis is credited per round. -/
theorem wealth_tendsto_zero (_hr : ∀ t, 0 ≤ r t) (t : ℕ) :
    Tendsto (wealth Al H r t) atTop (𝓝 0) := by
  induction t with
  | zero =>
    have h0 : wealth Al H r 0 = fun _ : ℕ => (0 : ℝ) := funext fun _ => rfl
    rw [h0]; exact tendsto_const_nhds
  | succ t ih =>
    have hA : Tendsto (Al.A t) atTop (𝓝 0) := (Al.rowSummable t).tendsto_atTop_zero
    have hsingle : Tendsto
        (fun i => if i = winner Al H r t then r t - bid Al H r t i else 0)
        atTop (𝓝 0) := by
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [eventually_gt_atTop (winner Al H r t)] with i hi
      rw [if_neg (by omega)]
    have hsum := (ih.add hA).add hsingle
    have heq : wealth Al H r (t + 1) = fun i => wealth Al H r t i + Al.A t i +
        (if i = winner Al H r t then r t - bid Al H r t i else 0) :=
      funext (wealth_succ Al H r t)
    rw [heq]
    simpa using hsum

theorem exists_max_bid (hr : ∀ t, 0 ≤ r t) (t : ℕ) :
    ∃ i, ∀ j, bid Al H r t j ≤ bid Al H r t i := by
  refine exists_max_of_tendsto_zero (bid_nonneg Al H r hr t) ?_
  refine squeeze_zero (bid_nonneg Al H r hr t) (bid_le_wealth Al H r t)
    (wealth_tendsto_zero Al H r hr t)

/-- The winner really is a maximiser — the `pickWinner` fallback is never taken. -/
theorem winner_isMax (hr : ∀ t, 0 ≤ r t) (t j : ℕ) :
    bid Al H r t j ≤ bid Al H r t (winner Al H r t) :=
  pickWinner_isMax (exists_max_bid Al H r hr t) j

/-! ## D.3 The agent, its test sets, and the two BRIA clauses -/

/-- The agent defined by the auction: follow and price the winning bid. -/
noncomputable def auctionAgent (hr : ∀ t, 0 ≤ r t) : Agent DP where
  choice t := (H (winner Al H r t)).choice t
  estimate t := bid Al H r t (winner Al H r t)
  choice_mem t := (H (winner Al H r t)).choice_mem t
  estimate_nonneg t := bid_nonneg Al H r hr t _
  estimate_le_one t := bid_le_one Al H r t _

/-- The paper's `M_i`: the rounds hypothesis `i` wins. -/
def winSet (i : ℕ) : Set ℕ := {t | winner Al H r t = i}

/-- **Theorem 1, part 3B.** The winning-round set is a valid test set — immediate from
the construction, as the paper says. -/
theorem isTestSet_winSet (hr : ∀ t, 0 ≤ r t) (i : ℕ) :
    IsTestSet (auctionAgent Al H r hr) (H i) (winSet Al H r i) := by
  intro t ht
  simp only [winSet, Set.mem_setOf_eq] at ht
  simp [auctionAgent, ht]

/-- **The exact wealth identity** — the corrected form of the equation in part 3C. The
winner pays its *wealth-bounded* bid, so `bid` appears here where the paper prints
`hᵉ`. -/
theorem wealth_eq_allowance_add_net (T i : ℕ) :
    wealth Al H r T i = (∑ n ∈ range T, Al.A n i)
      + ∑ t ∈ (range T).filter (fun t => winner Al H r t = i),
          (r t - bid Al H r t i) := by
  induction T with
  | zero => simp [wealth]
  | succ T ih =>
    rw [wealth_succ, ih, Finset.sum_range_succ, Finset.range_add_one,
      Finset.filter_insert]
    by_cases hw : winner Al H r T = i
    · rw [if_pos hw, Finset.sum_insert (by simp), if_pos hw.symm]; ring
    · rw [if_neg hw, if_neg (fun hc => hw hc.symm)]; ring

/-- **The corrected part 3C inequality.** Because `bid ≤ hᵉ`, the record is *at most*
the wealth net of allowance — which is the direction the paper's argument needs, even
though the printed step claims equality. -/
theorem record_le_wealth_sub_allowance (T i : ℕ) :
    record r (winSet Al H r i) (H i) T
      ≤ wealth Al H r T i - ∑ n ∈ range T, Al.A n i := by
  rw [wealth_eq_allowance_add_net]
  simp only [add_sub_cancel_left]
  unfold record
  have hfil : sel (winSet Al H r i) T
      = (range T).filter (fun t => winner Al H r t = i) := by
    ext t; simp [mem_sel, winSet, Finset.mem_filter]
  rw [hfil]
  exact Finset.sum_le_sum fun t _ => by linarith [bid_le_estimate Al H r t i]

/-- At a rejection time the wealth of the rejecting hypothesis is below its own promise,
hence below `1`. This is the one place `hᵉ ≤ 1` is load-bearing. -/
theorem wealth_lt_one_of_rejects (hr : ∀ t, 0 ≤ r t) {T i : ℕ}
    (hT : T ∈ rejectionSet (auctionAgent Al H r hr) (H i)) :
    wealth Al H r T i < 1 := by
  simp only [rejectionSet, Set.mem_setOf_eq, Rejects, auctionAgent] at hT
  have hle : bid Al H r T i ≤ bid Al H r T (winner Al H r T) := winner_isMax Al H r hr T i
  have hlt : bid Al H r T i < (H i).estimate T := lt_of_le_of_lt hle hT
  have : min ((H i).estimate T) (wealth Al H r T i) < (H i).estimate T := hlt
  have hw : wealth Al H r T i < (H i).estimate T := by
    rcases min_cases ((H i).estimate T) (wealth Al H r T i) with ⟨he, _⟩ | ⟨he, _⟩
    · rw [he] at this; exact absurd this (lt_irrefl _)
    · rw [he] at this; exact this
  exact lt_of_lt_of_le hw ((H i).estimate_le_one T)

/-- **Theorem 1, part 3C — coverage.** The auction agent covers every hypothesis in the
family, with the winning rounds as test set. -/
theorem covers_all (hr : ∀ t, 0 ≤ r t) (i : ℕ) :
    Covers (auctionAgent Al H r hr) r (H i) (winSet Al H r i) := by
  rw [covers_iff_tendsto, tendsto_atBot]
  intro C
  have hneg : Tendsto (fun T => -(∑ n ∈ range T, Al.A n i)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp (Al.colSums_tendsto_atTop i)
  have hg : Tendsto (fun T => 1 - ∑ n ∈ range T, Al.A n i) atTop atBot := by
    simpa [sub_eq_add_neg] using tendsto_atBot_add_const_left atTop (1 : ℝ) hneg
  rw [alongAtTop, eventually_inf_principal]
  filter_upwards [tendsto_atBot.1 hg C] with T hT hTB
  calc record r (winSet Al H r i) (H i) T
      ≤ wealth Al H r T i - ∑ n ∈ range T, Al.A n i :=
        record_le_wealth_sub_allowance Al H r T i
    _ ≤ 1 - ∑ n ∈ range T, Al.A n i := by
        linarith [wealth_lt_one_of_rejects Al H r hr hTB]
    _ ≤ C := hT

/-! ### No overestimation

The paper's part 2 bounds cumulative overestimation by the cumulative allowance. Its
`B⁺_T` bookkeeping is unnecessary: every wealth variable is nonnegative from the start
(`wealth_nonneg`), so the whole argument is one telescoping `tsum` identity. -/

/-- The total allowance handed out in round `n`; finite by requirement (iii). -/
noncomputable def totalAllowance (Al : Allowance) (n : ℕ) : ℝ := ∑' i, Al.A n i

theorem summable_wealth (_hr : ∀ t, 0 ≤ r t) (T : ℕ) : Summable (wealth Al H r T) := by
  induction T with
  | zero =>
    have h0 : wealth Al H r 0 = fun _ : ℕ => (0 : ℝ) := funext fun _ => rfl
    rw [h0]; exact summable_zero
  | succ T ih =>
    have hsingle : Summable
        (fun i => if i = winner Al H r T then r T - bid Al H r T i else 0) := by
      refine summable_of_hasFiniteSupport ((Set.finite_singleton (winner Al H r T)).subset ?_)
      intro i hi
      by_contra hc
      exact hi (if_neg (by simpa using hc))
    have heq : wealth Al H r (T + 1) = fun i => wealth Al H r T i + Al.A T i +
        (if i = winner Al H r T then r T - bid Al H r T i else 0) :=
      funext (wealth_succ Al H r T)
    rw [heq]
    exact (ih.add (Al.rowSummable T)).add hsingle

/-- **The telescoping identity of part 2.** Total wealth after `T` rounds equals the
allowance paid out minus the agent's cumulative overestimation. -/
theorem tsum_wealth_eq (hr : ∀ t, 0 ≤ r t) (T : ℕ) :
    ∑' i, wealth Al H r T i
      = (∑ t ∈ range T, totalAllowance Al t)
        - cumOver (auctionAgent Al H r hr) r T := by
  induction T with
  | zero =>
    have h0 : wealth Al H r 0 = fun _ : ℕ => (0 : ℝ) := funext fun _ => rfl
    simp [h0, cumOver]
  | succ T ih =>
    have hsingle : Summable
        (fun i => if i = winner Al H r T then r T - bid Al H r T i else 0) := by
      refine summable_of_hasFiniteSupport ((Set.finite_singleton (winner Al H r T)).subset ?_)
      intro i hi
      by_contra hc
      exact hi (if_neg (by simpa using hc))
    have htsingle :
        (∑' i, if i = winner Al H r T then r T - bid Al H r T i else 0)
          = r T - bid Al H r T (winner Al H r T) := by
      rw [tsum_eq_single (winner Al H r T) (fun b hb => if_neg hb), if_pos rfl]
    have heq : wealth Al H r (T + 1) = fun i => wealth Al H r T i + Al.A T i +
        (if i = winner Al H r T then r T - bid Al H r T i else 0) :=
      funext (wealth_succ Al H r T)
    rw [heq, ((summable_wealth Al H r hr T).add (Al.rowSummable T)).tsum_add hsingle,
      (summable_wealth Al H r hr T).tsum_add (Al.rowSummable T), ih, htsingle,
      Finset.sum_range_succ]
    unfold cumOver totalAllowance
    rw [Finset.sum_range_succ]
    simp only [auctionAgent]
    ring

/-- **Theorem 1, part 2.** Cumulative overestimation is bounded by cumulative
allowance, hence the per-round overestimation vanishes: the auction agent does not
overestimate. -/
theorem noOverestimation_auction (hr : ∀ t, 0 ≤ r t) :
    NoOverestimation (auctionAgent Al H r hr) r := by
  intro ε hε
  have hbound : ∀ T, cumOver (auctionAgent Al H r hr) r T
      ≤ ∑ t ∈ range T, totalAllowance Al t := by
    intro T
    have hnn : 0 ≤ ∑' i, wealth Al H r T i :=
      tsum_nonneg fun i => wealth_nonneg Al H r hr T i
    have := tsum_wealth_eq Al H r hr T
    linarith
  have havg : Tendsto (fun T : ℕ => (∑ t ∈ range T, totalAllowance Al t) / T)
      atTop (𝓝 0) := Al.avgTotalTendstoZero
  filter_upwards [havg.eventually (eventually_lt_nhds hε), eventually_gt_atTop 0] with T hT hT0
  have hT0' : (0 : ℝ) < T := by exact_mod_cast hT0
  calc cumOver (auctionAgent Al H r hr) r T / T
      ≤ (∑ t ∈ range T, totalAllowance Al t) / T := by
        gcongr
        exact hbound T
    _ ≤ ε := hT.le

/-! ### Part 3A — the winning set is infinite

The paper proves this separately. It is **not needed** for Definition 7: `covers_all`
above establishes coverage without it, and `theorem1_extensional` compiles without any
infinitude claim. It is proved here anyway, because it is the step where requirement (i)
— "each hypothesis must get infinite overall allowance" — does its intended work, and
because a test set that is never used would make the construction uninteresting even
where it is formally adequate. -/

/-- Between two times at which a hypothesis never wins, its wealth changes only by
allowance. -/
theorem wealth_eq_of_no_win {i T₀ : ℕ} (hno : ∀ t, T₀ ≤ t → winner Al H r t ≠ i) :
    ∀ T, T₀ ≤ T → wealth Al H r T i
      = wealth Al H r T₀ i + ∑ n ∈ Finset.Ico T₀ T, Al.A n i := by
  intro T hT
  induction T, hT using Nat.le_induction with
  | base => simp
  | succ T hT ih =>
    rw [wealth_succ, if_neg (fun hc => hno T hT hc.symm), ih,
      Finset.sum_Ico_succ_top hT]
    ring

/-- **Theorem 1, part 3A.** A hypothesis that wins only finitely often is eventually
rich enough that its bid is never wealth-constrained, so it eventually stops
outpromising the agent. Contrapositive: a hypothesis that outpromises infinitely often
wins infinitely often. -/
theorem winSet_infinite_of_rejected_infinitely (hr : ∀ t, 0 ≤ r t) (i : ℕ)
    (hrej : (rejectionSet (auctionAgent Al H r hr) (H i)).Infinite) :
    (winSet Al H r i).Infinite := by
  by_contra hfin
  rw [Set.not_infinite] at hfin
  obtain ⟨T₀, hT₀⟩ := hfin.bddAbove
  have hno : ∀ t, T₀ + 1 ≤ t → winner Al H r t ≠ i := by
    intro t ht hc
    exact absurd (hT₀ (show t ∈ winSet Al H r i from hc)) (by omega)
  -- wealth grows without bound past `T₀ + 1`
  have hgrow : Tendsto (fun T => ∑ n ∈ Finset.Ico (T₀ + 1) T, Al.A n i) atTop atTop := by
    have hsplit : ∀ T, T₀ + 1 ≤ T →
        ∑ n ∈ Finset.Ico (T₀ + 1) T, Al.A n i
          = (∑ n ∈ range T, Al.A n i) - ∑ n ∈ range (T₀ + 1), Al.A n i := by
      intro T hT
      rw [eq_sub_iff_add_eq, add_comm, Finset.sum_range_add_sum_Ico _ hT]
    refine Tendsto.congr' ?_ (tendsto_atTop_add_const_right atTop
      (-(∑ n ∈ range (T₀ + 1), Al.A n i)) (Al.colSums_tendsto_atTop i))
    filter_upwards [eventually_ge_atTop (T₀ + 1)] with T hT
    rw [hsplit T hT, sub_eq_add_neg]
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.1 (tendsto_atTop.1 hgrow 1)
  -- past `max (T₀+1) T₁` the wealth constraint is inactive, so `i` never rejects
  have hnorej : ∀ T, max (T₀ + 1) T₁ ≤ T → T ∉ rejectionSet (auctionAgent Al H r hr) (H i) := by
    intro T hT hmem
    have hge1 : (1 : ℝ) ≤ wealth Al H r T i := by
      rw [wealth_eq_of_no_win Al H r hno T (le_trans (le_max_left _ _) hT)]
      have h1 := hT₁ T (le_trans (le_max_right _ _) hT)
      have h2 := wealth_nonneg Al H r hr (T₀ + 1) i
      linarith
    have := wealth_lt_one_of_rejects Al H r hr hmem
    linarith
  exact hrej (Set.Finite.subset (Set.finite_Iio (max (T₀ + 1) T₁)) fun T hT =>
    lt_of_not_ge fun hc => hnorej T hc hT)

/-- **Theorem 1a — the extensional existence theorem.** For any countably enumerated
family of hypotheses and any allowance schedule satisfying the paper's three
requirements, the auction construction is a BRIA covering the family, with the winning
rounds as test sets.

This is the mathematical content of Theorem 1 with the computability and complexity
claims removed. Nothing here mentions an algorithm; §I says what is left. -/
theorem theorem1_extensional (hr : ∀ t, 0 ≤ r t) :
    IsBRIA (auctionAgent Al H r hr) r H (winSet Al H r) where
  noOverestimation := noOverestimation_auction Al H r hr
  testSet := isTestSet_winSet Al H r hr
  covers := covers_all Al H r hr

end Auction

/-! # §E. The allowance schedule

The paper offers `A(n,i) = n⁻¹ i⁻²` and leaves its three properties unverified. They do
hold. Two things are worth recording.

* Requirement (ii) — display (1), the *average* total allowance vanishing — is **not** an
  extra condition. It follows from "per-round total allowance `→ 0`" by Cesàro, which
  Mathlib has (`Filter.Tendsto.cesaro`). Any schedule whose round totals vanish satisfies
  it. `avgTotal_of_tendsto_zero` below.
* Requirement (i) is `¬ Summable`, and the bridge to divergent partial sums is
  Mathlib's `not_summable_iff_tendsto_nat_atTop_of_nonneg`. No hand analysis needed. -/

/-- **Requirement (ii) is Cesàro.** -/
theorem avgTotal_of_tendsto_zero {f : ℕ → ℝ} (h : Tendsto f atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, f n) / N) atTop (𝓝 0) := by
  simpa [div_eq_inv_mul] using h.cesaro

/-- `∑_i (i+1)⁻²` converges. -/
theorem summable_invSq : Summable (fun i : ℕ => 1 / ((i : ℝ) + 1) ^ 2) := by
  have h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) := Real.summable_one_div_nat_pow.2 one_lt_two
  simpa using (summable_nat_add_iff 1).2 h

/-- `∑_n (n+1)⁻¹` diverges. -/
theorem not_summable_invLin : ¬ Summable (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
  intro h
  refine Real.not_summable_one_div_natCast ?_
  exact (summable_nat_add_iff 1).1 (by simpa using h)

/-- **The paper's example schedule**, `A(n,i) = (n+1)⁻¹ (i+1)⁻²` (shifted by
`dd:index0`), with all three requirements discharged. -/
noncomputable def harmonicSquare : Allowance where
  A n i := (1 / ((n : ℝ) + 1)) * (1 / ((i : ℝ) + 1) ^ 2)
  nonneg n i := by positivity
  rowSummable n := summable_invSq.mul_left _
  colNotSummable i := by
    intro h
    refine not_summable_invLin ?_
    have hc : (0 : ℝ) < 1 / ((i : ℝ) + 1) ^ 2 := by positivity
    have := h.mul_right (1 / (1 / ((i : ℝ) + 1) ^ 2))
    refine this.congr fun n => ?_
    field_simp
  avgTotalTendstoZero := by
    refine avgTotal_of_tendsto_zero (f := fun n => ∑' i : ℕ, (1 / ((n : ℝ) + 1)) *
      (1 / ((i : ℝ) + 1) ^ 2)) ?_
    have hts : (fun n : ℕ => ∑' i : ℕ, (1 / ((n : ℝ) + 1)) * (1 / ((i : ℝ) + 1) ^ 2))
        = fun n : ℕ => (1 / ((n : ℝ) + 1)) * ∑' i : ℕ, (1 / ((i : ℝ) + 1) ^ 2) :=
      funext fun _ => tsum_mul_left
    rw [hts]
    have hlin : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hmul := hlin.mul_const (∑' i : ℕ, (1 / ((i : ℝ) + 1) ^ 2))
    rwa [zero_mul] at hmul

/-! # §C.1. Lemma 6 — trimming zero-promise rounds from a test set

Cheap, and genuinely needed: Theorem 4's proof uses it to replace the *legal* promise
`max(μ_t − ε, 0)` by `μ_t − ε` on the test set. -/

/-- **Lemma 6.** Dropping rounds in which the hypothesis promises nothing preserves
coverage. -/
theorem lemma6 {DP : ℕ → Finset Action} {α : Agent DP} {r : ℕ → ℝ} {h : Hypothesis DP}
    {M N : Set ℕ} (hr : ∀ t, 0 ≤ r t) (hN : ∀ t ∈ N, h.estimate t = 0)
    (hcov : Covers α r h M) : Covers α r h (M \ N) := by
  rw [covers_iff_tendsto] at hcov ⊢
  refine tendsto_atBot_mono (fun T => ?_) hcov
  unfold record
  have hsub : sel (M \ N) T ⊆ sel M T := by
    intro t ht
    rw [mem_sel] at ht ⊢
    exact ⟨ht.1, ht.2.1⟩
  refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun t ht htn => ?_
  rw [mem_sel] at ht
  have htN : t ∈ N := by
    by_contra hc
    exact htn (mem_sel.2 ⟨ht.1, ⟨ht.2, hc⟩⟩)
  rw [hN t htN, sub_zero]
  exact hr t

/-! # §F. Theorem 2 — the diagonal lower bound, extensionally

The mathematical half of Theorem 2 is a two-line argument once the diagonal hypothesis
is written down. Writing it down is where the paper's unstated representation
assumptions live; §I collects them. -/

section Diagonal

variable {DP : ℕ → Finset Action} (α : Agent DP)

/-- The rounds the diagonal hypothesis attacks: at least two options available and the
agent's estimate strictly below `1`. -/
def diagGood (t : ℕ) : Prop := 1 < (DP t).card ∧ α.estimate t < 1

/-- Some available option other than the agent's, where one exists. Note the `Classical`
choice: extensionally this is free, and it is precisely the step whose *computability*
Theorem 2 needs but never argues (see §I). -/
noncomputable def diagChoice (t : ℕ) : Action :=
  if h : ∃ b ∈ DP t, b ≠ α.choice t then h.choose else α.choice t

theorem diagChoice_mem (t : ℕ) : diagChoice α t ∈ DP t := by
  unfold diagChoice
  split
  · next h => exact h.choose_spec.1
  · exact α.choice_mem t

theorem diagChoice_ne (t : ℕ) (ht : 1 < (DP t).card) : diagChoice α t ≠ α.choice t := by
  have hex : ∃ b ∈ DP t, b ≠ α.choice t := by
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 ht
    by_cases hxa : x = α.choice t
    · exact ⟨y, hy, fun hc => hxy (hxa.trans hc.symm)⟩
    · exact ⟨x, hx, hxa⟩
  unfold diagChoice
  rw [dif_pos hex]
  exact hex.choose_spec.2

/-- **The diagonal hypothesis of Theorem 2**: promise `1` and recommend something else
whenever the agent leaves room, promise `0` otherwise. -/
noncomputable def diagHyp : Hypothesis DP where
  choice t := if diagGood α t then diagChoice α t else α.choice t
  estimate t := if diagGood α t then 1 else 0
  choice_mem t := by
    by_cases h : diagGood α t
    · simpa [h] using diagChoice_mem α t
    · simpa [h] using α.choice_mem t
  estimate_nonneg t := by by_cases h : diagGood α t <;> simp [h]
  estimate_le_one t := by by_cases h : diagGood α t <;> simp [h]

theorem rejectionSet_diagHyp : rejectionSet α (diagHyp α) = {t | diagGood α t} := by
  ext t
  simp only [rejectionSet, Set.mem_setOf_eq, Rejects, diagHyp]
  constructor
  · intro hlt
    by_contra hg
    rw [if_neg hg] at hlt
    exact absurd hlt (not_lt.2 (α.estimate_nonneg t))
  · intro hg
    rw [if_pos hg]
    exact hg.2

/-- A test set for the diagonal hypothesis misses every attacked round: on those rounds
the hypothesis recommends, by construction, something the agent did not choose. -/
theorem testSet_diagHyp_disjoint {M : Set ℕ} (hM : IsTestSet α (diagHyp α) M) :
    ∀ t ∈ M, ¬ diagGood α t := by
  intro t ht hg
  have hc := hM t ht
  simp only [diagHyp, hg, if_pos] at hc
  exact diagChoice_ne α t hg.1 hc.symm

/-- **Theorem 2 — extensional core.** If the agent leaves room infinitely often, it
covers the diagonal hypothesis with *no* test set. Hence no BRIA whose family contains
the diagonal hypothesis exists.

What the printed theorem adds is: "if `α` is `O(g(t))`-computable then `diagHyp α` is
`O(g(t))`-computable", so the diagonal hypothesis lies in `H`. That step is *not* here
— see §I for the representation assumptions it needs. -/
theorem theorem2_extensional {r : ℕ → ℝ} (hr : ∀ t, 0 ≤ r t)
    (hinf : {t | diagGood α t}.Infinite) (M : Set ℕ) (hM : IsTestSet α (diagHyp α) M) :
    ¬ Covers α r (diagHyp α) M := by
  intro hcov
  have hbb : ∀ T, (0 : ℝ) ≤ record r M (diagHyp α) T :=
    record_nonneg (fun t ht => by
      simp only [diagHyp, if_neg (testSet_diagHyp_disjoint α hM t ht)]
      exact hr t)
  have hfin := rejectionSet_finite_of_record_bddBelow hcov hbb
  rw [rejectionSet_diagHyp] at hfin
  exact hinf hfin

/-- **Theorem 2, packaged**: no BRIA covering a family that contains the diagonal
hypothesis. The paper's conclusion "`α` is not computable in `O(g(t))`" is this together
with the missing complexity-preservation step. -/
theorem theorem2_no_bria {ι : Type*} {r : ℕ → ℝ} (hr : ∀ t, 0 ≤ r t)
    (hinf : {t | diagGood α t}.Infinite)
    {H : ι → Hypothesis DP} {M : ι → Set ℕ} (i : ι) (hi : H i = diagHyp α) :
    ¬ IsBRIA α r H M := by
  intro hB
  exact theorem2_extensional α hr hinf (M i) (hi ▸ hB.testSet i) (hi ▸ hB.covers i)

end Diagonal

/-! # §G. Definition 8 and Theorem 4 — bounded vMWC randomness

## G.0 The printed Definition 8 is unsatisfiable

Definition 8 reads:

> `ȳ` is `(O(h(t)` boundedly) vMWC random with means `μ̄` if for every infinite
> `S ⊆ ℕ` decidable (in `O(h(t))` time) from available information, we have
> `lim_{T→∞} ∑_{t ∈ S_{≤T}} y_t − μ_t = 0`.

That is a *sum*, not an average. The standard notion it generalises (Downey–Hirschfeldt
Definition 7.4.1) is a limiting relative *frequency*. As printed, the condition forces
the increments to vanish along `S`, hence `y_t → μ_t` along every selectable set — so a
`{0,1}`-valued sequence with means `1/2` can never satisfy it, and Theorem 4's hypothesis
is unsatisfiable on the paper's own motivating example (binary digits of `π`).

Both readings are formalized below and the refutation is proved. The proof of Theorem 4
goes through under *either* reading, which is why the slip survived: it only shows up
when you ask whether the hypothesis is inhabited. -/

/-- **Definition 8 as printed** — unnormalized. -/
def VMWCPrinted (y μ : ℕ → ℝ) (Sel : Set (Set ℕ)) : Prop :=
  ∀ S ∈ Sel, S.Infinite → Tendsto (fun T => ∑ t ∈ sel S T, (y t - μ t)) atTop (𝓝 0)

/-- **Definition 8 as intended** — the limiting relative frequency. -/
def VMWCAveraged (y μ : ℕ → ℝ) (Sel : Set (Set ℕ)) : Prop :=
  ∀ S ∈ Sel, S.Infinite →
    Tendsto (fun T => (∑ t ∈ sel S T, (y t - μ t)) / (sel S T).card) atTop (𝓝 0)

/-- Under the printed reading, the selected deviations vanish pointwise. -/
theorem vmwcPrinted_forces_pointwise {y μ : ℕ → ℝ} {S : Set ℕ}
    (h : Tendsto (fun T => ∑ t ∈ sel S T, (y t - μ t)) atTop (𝓝 0)) :
    Tendsto (fun T => if T ∈ S then y T - μ T else 0) atTop (𝓝 0) := by
  have hstep : Tendsto (fun T => (∑ t ∈ sel S (T + 1), (y t - μ t))
      - ∑ t ∈ sel S T, (y t - μ t)) atTop (𝓝 0) := by
    simpa using (h.comp (tendsto_add_atTop_nat 1)).sub h
  refine hstep.congr fun T => ?_
  rw [show sel S (T + 1) = if T ∈ S then insert T (sel S T) else sel S T by
    simp only [sel, Finset.range_add_one, Finset.filter_insert]]
  by_cases hT : T ∈ S
  · rw [if_pos hT, Finset.sum_insert (by simp), if_pos hT]; ring
  · rw [if_neg hT, if_neg hT]; ring

/-- **Definition 8, as printed, is unsatisfiable on binary sequences with mean `1/2`.**
So Theorem 4's hypothesis, read literally, is empty in exactly the case Section 4.5
advertises (the `2^t`-th binary digits of `π`). -/
theorem vmwcPrinted_vacuous_on_bits {y : ℕ → ℝ} {S : Set ℕ} (hS : S.Infinite)
    (hbits : ∀ t, y t = 0 ∨ y t = 1)
    (h : Tendsto (fun T => ∑ t ∈ sel S T, (y t - 1 / 2)) atTop (𝓝 0)) : False := by
  have hpt := vmwcPrinted_forces_pointwise (μ := fun _ => 1 / 2) h
  have hev : ∀ᶠ T in atTop, |(if T ∈ S then y T - 1 / 2 else 0)| < 1 / 2 := by
    filter_upwards [eventually_atTop.2 (Metric.tendsto_atTop.1 hpt (1 / 2) (by norm_num))]
      with T hT
    simpa [Real.dist_eq] using hT
  have hfreq : ∃ᶠ T in atTop, T ∈ S := Nat.frequently_atTop_iff_infinite.2 hS
  obtain ⟨T, hT1, hT2⟩ := (hev.and_frequently hfreq).exists
  rw [if_pos hT2] at hT1
  rcases hbits T with hb | hb <;> rw [hb] at hT1 <;> norm_num at hT1

/-! ## G.1 The record lower bound Theorem 4 actually needs -/

/-- A sequence eventually nonnegative is bounded below. (Feeds
`rejectionSet_finite_of_record_bddBelow`, which wants a *global* bound.) -/
theorem bddBelow_of_eventually_nonneg {f : ℕ → ℝ} (h : ∀ᶠ T in atTop, 0 ≤ f T) :
    ∃ C, ∀ T, C ≤ f T := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  obtain ⟨b, _, hb⟩ := Finset.exists_min_image (range (N + 1)) f ⟨0, by simp⟩
  refine ⟨min (f b) 0, fun T => ?_⟩
  by_cases hT : T ≤ N
  · exact le_trans (min_le_left _ _) (hb T (Finset.mem_range.2 (by omega)))
  · exact le_trans (min_le_right _ _) (hN T (by omega))

/-- **Theorem 4's engine.** On a test set where the hypothesis promises at least `ε`
below the mean, averaged-vMWC rewards keep the record bounded below — indeed eventually
nonnegative. Note `M` need not be infinite: the empty-selection case is handled by the
sum over an empty `Finset` being `0`. -/
theorem record_bddBelow_of_vmwc {DP : ℕ → Finset Action} {r μ : ℕ → ℝ} {M : Set ℕ}
    {h : Hypothesis DP} {ε : ℝ} (hε : 0 < ε)
    (hpromise : ∀ t ∈ M, h.estimate t ≤ μ t - ε)
    (hvm : Tendsto (fun T => (∑ t ∈ sel M T, (r t - μ t)) / (sel M T).card)
      atTop (𝓝 0)) :
    ∃ C, ∀ T, C ≤ record r M h T := by
  refine bddBelow_of_eventually_nonneg ?_
  filter_upwards [eventually_atTop.2 (Metric.tendsto_atTop.1 hvm (ε / 2) (by linarith))]
    with T hT
  have hdev : (∑ t ∈ sel M T, (r t - μ t)) + ε * (sel M T).card ≤ record r M h T := by
    unfold record
    rw [show ε * ((sel M T).card : ℝ) = ∑ _t ∈ sel M T, ε by simp [mul_comm],
      ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun t ht => ?_
    have := hpromise t (mem_sel.1 ht).2
    linarith
  rcases Nat.eq_zero_or_pos (sel M T).card with hc | hc
  · have hempty : sel M T = ∅ := Finset.card_eq_zero.1 hc
    simp only [hempty, Finset.sum_empty] at hdev ⊢
    simpa [hempty] using hdev
  · have hcR : (0 : ℝ) < (sel M T).card := by exact_mod_cast hc
    have habs : |(∑ t ∈ sel M T, (r t - μ t)) / (sel M T).card| < ε / 2 := by
      rw [Real.dist_eq, sub_zero] at hT
      exact hT
    rw [abs_div, abs_of_nonneg hcR.le, div_lt_iff₀ hcR] at habs
    have := abs_le.1 habs.le
    linarith [this.1]

/-- **Theorem 4 — the single-`ε` step**, with Lemma 6 doing the paper's WLOG. The legal
promise is `max(μ_t − ε, 0)`; Lemma 6 trims the rounds where that clips to `0`, and on
what is left the promise is exactly `μ_t − ε`. -/
theorem theorem4_single {DP : ℕ → Finset Action} {ι : Type*} {α : Agent DP} {r : ℕ → ℝ}
    {H : ι → Hypothesis DP} {M : ι → Set ℕ} (hBRIA : IsBRIA α r H M)
    (hr : ∀ t, 0 ≤ r t) (μ : ℕ → ℝ) (ε : ℝ) (hε : 0 < ε) (i : ι)
    (hiE : (H i).estimate = fun t => max (μ t - ε) 0)
    (hvm : Tendsto (fun T =>
        (∑ t ∈ sel (M i \ {t | μ t - ε ≤ 0}) T, (r t - μ t))
          / (sel (M i \ {t | μ t - ε ≤ 0}) T).card) atTop (𝓝 0)) :
    ∀ᶠ t in atTop, μ t - ε ≤ α.estimate t := by
  set N : Set ℕ := {t | μ t - ε ≤ 0} with hNdef
  have hzero : ∀ t ∈ N, (H i).estimate t = 0 := by
    intro t ht
    rw [hiE]
    exact max_eq_right (by simpa [hNdef] using ht)
  have hcov : Covers α r (H i) (M i \ N) := lemma6 hr hzero (hBRIA.covers i)
  have hpromise : ∀ t ∈ M i \ N, (H i).estimate t ≤ μ t - ε := by
    intro t ht
    rw [hiE]
    exact max_le le_rfl (by simpa [hNdef] using (not_le.1 (by simpa [hNdef] using ht.2)).le)
  obtain ⟨C, hC⟩ := record_bddBelow_of_vmwc (h := H i) hε hpromise hvm
  have hfin := rejectionSet_finite_of_record_bddBelow hcov hC
  obtain ⟨K, hK⟩ := hfin.bddAbove
  refine eventually_atTop.2 ⟨K + 1, fun t ht => ?_⟩
  by_contra hlt
  push Not at hlt
  have : t ∈ rejectionSet α (H i) := by
    simp only [rejectionSet, Set.mem_setOf_eq, Rejects, hiE]
    exact lt_of_lt_of_le hlt (le_max_left _ _)
  exact absurd (hK this) (by omega)

theorem avg_const (v : ℝ) {T : ℕ} (hT : 0 < T) : avg (fun _ => v) T = v := by
  unfold avg
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp

/-- **Theorem 4.** Given, for every `ε > 0`, a covered hypothesis promising
`max(μ − ε, 0)` and recommending an option whose rewards are averaged-vMWC with means
`μ`, the agent's average reward dominates the average of `μ`. -/
theorem theorem4 {DP : ℕ → Finset Action} {ι : Type*} {α : Agent DP} {r : ℕ → ℝ}
    {H : ι → Hypothesis DP} {M : ι → Set ℕ} (hBRIA : IsBRIA α r H M)
    (hr : ∀ t, 0 ≤ r t) (μ : ℕ → ℝ) (hμ1 : ∀ t, μ t ≤ 1)
    (hfam : ∀ ε > 0, ∃ i, (H i).estimate = (fun t => max (μ t - ε) 0) ∧
      Tendsto (fun T =>
        (∑ t ∈ sel (M i \ {t | μ t - ε ≤ 0}) T, (r t - μ t))
          / (sel (M i \ {t | μ t - ε ≤ 0}) T).card) atTop (𝓝 0)) :
    AsympGE (avg r) (avg μ) := by
  intro δ hδ
  obtain ⟨i, hiE, hvm⟩ := hfam (δ / 2) (by linarith)
  have hev := theorem4_single hBRIA hr μ (δ / 2) (by linarith) i hiE hvm
  set L : ℕ → ℝ := fun t => max (μ t - δ / 2) 0 with hL
  have hL0 : ∀ t, 0 ≤ L t := fun t => le_max_right _ _
  have hL1 : ∀ t, L t ≤ 1 := fun t => max_le (by linarith [hμ1 t]) zero_le_one
  have hevL : ∀ᶠ t in atTop, L t ≤ α.estimate t := by
    filter_upwards [hev] with t ht
    exact max_le ht (α.estimate_nonneg t)
  have hmain := avg_ge_of_eventually_estimate_ge hL0 hL1 hBRIA.noOverestimation hevL
    (δ / 2) (by linarith)
  filter_upwards [hmain, eventually_gt_atTop 0] with T hT hT0
  have hT0' : (0 : ℝ) < T := by exact_mod_cast hT0
  have key : (∑ t ∈ range T, μ t) - δ / 2 * T ≤ ∑ t ∈ range T, L t := by
    calc (∑ t ∈ range T, μ t) - δ / 2 * T
        = ∑ t ∈ range T, (μ t - δ / 2) := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
      _ ≤ ∑ t ∈ range T, L t := Finset.sum_le_sum fun t _ => le_max_left _ _
  have hcmp : avg μ T - δ / 2 ≤ avg L T := by
    have e1 : avg μ T - δ / 2 = ((∑ t ∈ range T, μ t) - δ / 2 * T) / T := by
      unfold avg; field_simp
    rw [e1]
    unfold avg
    gcongr
  linarith

/-! # §H. Theorem 5 — the game layer

Only the **converse** half is probed, because that is the half whose burden the report
needs to measure: the paper says it "follows directly from Theorem 3", and it does — the
compiled derivation below uses nothing but `theorem3`.

Two findings come out of writing it.

* **Lemma 7 (the minimax theorem) is never used.** The printed proof of Theorem 5 works
  entirely with the *pure*-strategy maximin `max_{a_i} min_{a_{-i}} u_i`, both in the
  definition of "strictly individually rational" and in the coverage bound. Nothing in
  the proof mentions a mixed strategy on the minimising side. So the paper's one external
  mathematical dependency is, in the printed argument, spurious.
* The construction half is the substantial one and is *not* the auction of Theorem 1: it
  builds the two BRIAs directly from a randomisation over `c` and over pure-profile
  punishments. It is also, as printed, a probability-one statement (the coverage step
  needs the randomisation to hit each `p_{a_i}` branch infinitely often) although the
  theorem is stated as plain existence. -/

section Game

variable {Action : Type*} {Opp : Type*}

/-- **Theorem 5, converse half.** A BRIA whose hypothesis family contains the constant
hypothesis "always play `a*`, always promise `v`" earns at least `v` on average, where
`v` is any value `a*` guarantees against every opponent action. Taking `a*` to be a
maximin action and `v` the pure maximin value gives the printed statement. -/
theorem theorem5_converse {DP : ℕ → Finset Action} {ι : Type*}
    (u : Action → Opp → ℝ) (opp : ℕ → Opp)
    {α : Agent DP} {H : ι → Hypothesis DP} {M : ι → Set ℕ}
    (hBRIA : IsBRIA α (fun t => u (α.choice t) (opp t)) H M)
    (astar : Action) (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hmaximin : ∀ b, v ≤ u astar b)
    (hmem : ∃ i, (H i).choice = (fun _ => astar) ∧ (H i).estimate = fun _ => v) :
    AsympGE (avg fun t => u (α.choice t) (opp t)) (avg fun _ => v) := by
  refine theorem3 hBRIA (fun _ => astar) (fun _ => v) (fun _ => hv0) (fun _ => hv1)
    (fun t ht => ?_) hmem
  rw [ht]; exact hmaximin (opp t)

end Game

/-! ## H.1 A concrete game instance

The Prisoner's Dilemma with payoffs in `[0,1]`. `false` = cooperate, `true` = defect.
Row's pure maximin action is `true` with value `1/5`; the converse half of Theorem 5 then
says any BRIA row player averages at least `1/5`. This exercises the actual construction
(a real game, a real maximin action, a real guarantee), not just the definitions. -/

section PD

/-- Row's payoff in the `[0,1]`-scaled Prisoner's Dilemma. -/
noncomputable def pdRow : Bool → Bool → ℝ
  | false, false => 3 / 5
  | false, true  => 0
  | true,  false => 1
  | true,  true  => 1 / 5

/-- Defection guarantees `1/5` against either opponent action — the pure maximin value. -/
theorem pdRow_maximin (b : Bool) : (1 : ℝ) / 5 ≤ pdRow true b := by
  cases b <;> norm_num [pdRow]

/-- …and cooperation guarantees nothing better than `0`, so `true` really is the maximin
action: the value `1/5` is not attainable by the other row. -/
theorem pdRow_coop_worst : pdRow false true = 0 := rfl

example {DP : ℕ → Finset Bool} {ι : Type*} (opp : ℕ → Bool)
    {α : Agent DP} {H : ι → Hypothesis DP} {M : ι → Set ℕ}
    (hBRIA : IsBRIA α (fun t => pdRow (α.choice t) (opp t)) H M)
    (hmem : ∃ i, (H i).choice = (fun _ => true) ∧ (H i).estimate = fun _ => (1 : ℝ) / 5) :
    AsympGE (avg fun t => pdRow (α.choice t) (opp t)) (avg fun _ => (1 : ℝ) / 5) :=
  theorem5_converse pdRow opp hBRIA true (1 / 5) (by norm_num) (by norm_num)
    pdRow_maximin hmem

end PD

/-! # §I. The computability interface — what the extensional layer cannot say

Every theorem above is silent about computation, and that silence is not an oversight:
**Lean's classical logic makes the extensional layer blind to the obstruction.** With
`Classical.propDecidable` in scope, `α.estimate t < 1` is decidable, `arg max` exists,
and tie-breaking is free. Nothing in §A–§H can even *state* that a step is uncomputable.

So the computability layer cannot be an afterthought bolted onto these definitions; it
has to be a separate representation carrying its own decidability. The structures below
are the minimal interfaces the paper's own proofs need, compiled so the report's claims
about them are checkable. Note carefully that none of them is *inhabited by `ℝ`* in any
useful sense — `ℚ` inhabits them; `ℝ` inhabits them only through `Classical`, which is
the whole point. -/

section Computability

/-- What Theorem 1's auction needs of the *representation of promises*: the winner is
`arg max_i min(hᵉ_{i,t}, w_t(i))`, so the algorithm must compare promise values exactly
and break ties. The paper never says what a promise is syntactically. -/
structure PromiseRepresentation where
  /-- The syntactic object an algorithm manipulates in place of a real number. -/
  Rep : Type
  /-- Its denotation. -/
  toReal : Rep → ℝ
  /-- Exact order comparison — required by display (2)'s `arg max`. -/
  decLE : DecidableRel (fun x y : Rep => toReal x ≤ toReal y)
  /-- Wealth is compared against promises, so wealth must live in the same
  representation, closed under the update `w + A + r − bid`. -/
  add : Rep → Rep → Rep
  toReal_add : ∀ x y, toReal (add x y) = toReal x + toReal y

/-- The rationals inhabit it. -/
noncomputable def ratPromises : PromiseRepresentation where
  Rep := ℚ
  toReal := Rat.cast
  decLE := fun x y => decidable_of_iff (x ≤ y) (by exact_mod_cast Iff.rfl)
  add := (· + ·)
  toReal_add := by intros; push_cast; ring

/-- **The obstruction, stated positively.** For a representation to be usable, `decLE`
must be a *genuine decision procedure*, not `Classical.propDecidable`. Lean cannot
express that difference in `Prop`; it is a property of the *term*, not the type. Hence
the report's conclusion: a faithful `O(g(t))` statement needs a machine model in which
programs, not functions, are the objects — exactly the boundary `dd:fuel` marks in
`LogicalInduction`.

Recorded as a compiled fact rather than prose: the classical instance inhabits the
interface for `ℝ` itself, so no theorem stated over `PromiseRepresentation` alone can
rule out an uncomputable promise. -/
noncomputable def realPromises : PromiseRepresentation where
  Rep := ℝ
  toReal := id
  decLE := fun _ _ => Classical.propDecidable _
  add := (· + ·)
  toReal_add := fun _ _ => rfl

/-- What Theorem 2's diagonal step needs, beyond `α` being computable. The printed proof
asserts the diagonal hypothesis "is computable (in `O(g(t))`)" without argument; these
are the four obligations that assertion hides. -/
structure DiagonalObligations {Action : Type*} (DP : ℕ → Finset Action) where
  /-- (1) the agent's estimate is compared *exactly* against `1`. -/
  decEstimateLtOne : ℕ → Bool
  /-- (2) the size test `|DP_t| ≥ 2` is decidable within the bound. -/
  decTwoOptions : ℕ → Bool
  /-- (3) an option other than the agent's must be *produced*, not merely shown to
  exist — a search over `DP_t`, whose cost is the size of `DP_t`, a quantity the
  paper's `O(g(t))` accounting (indexed by `t` alone) never mentions. -/
  altOption : ℕ → Action
  /-- (4) …and it must be legal. -/
  altOption_mem : ∀ t, altOption t ∈ DP t

end Computability

/-! ## Non-vacuity of Theorem 1a

The hypotheses of `theorem1_extensional` are jointly satisfiable: `harmonicSquare`
inhabits `Allowance`, `constAgent` inhabits `Hypothesis boolDP`, and a constant reward
stream is legal. So the existence theorem is not vacuously quantified. -/

noncomputable example : Hypothesis boolDP := constAgent true (1 / 2) (by norm_num) (by norm_num)

example (H : ℕ → Hypothesis boolDP) :
    ∃ (α : Agent boolDP) (M : ℕ → Set ℕ), IsBRIA α (fun _ => (1 : ℝ) / 2) H M :=
  ⟨_, _, theorem1_extensional harmonicSquare H (fun _ => 1 / 2) (fun _ => by norm_num)⟩

/-! ## Axiom audit for the spike's endpoints.

`Classical.choice`/`propDecidable`/`Quot.sound` only — the standard classical trio that
every Mathlib-based development carries. No `sorryAx`, no bespoke axiom. -/

#print axioms covers_iff_forall
#print axioms avg_sub_tendsto_zero_of_eventuallyEq
#print axioms avg_ge_of_eventually_estimate_ge
#print axioms theorem3
#print axioms exists_max_of_tendsto_zero
#print axioms winSet_infinite_of_rejected_infinitely
#print axioms theorem1_extensional
#print axioms harmonicSquare
#print axioms lemma6
#print axioms theorem2_no_bria
#print axioms vmwcPrinted_vacuous_on_bits
#print axioms theorem4
#print axioms theorem5_converse

end BIRSpike
