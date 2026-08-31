import FactoredSpaces.API

/-! Client-style smoke tests for the Factored Space Models API.  These import only
`FactoredSpaces.API`, build their own small factored space, DAG and distributions, and
combine endpoints to prove facts a downstream project would want — none of them restates a
paper node, and none reuses the witnesses of `FactoredSpaces/Examples.lean`. -/

namespace APITests.FactoredSpaces

open _root_.FactoredSpaces

/-! ### A client factored space and a conditioning event

`I = Fin 3`, `Ω_i = Bool`: three bits.  The conditioning event is "at least one of the
first two bits is set", which — unlike a cylinder event — couples two factors. -/

/-- The client's factored space: three bits, `I = Fin 3` and `Ω_i = Bool`. -/
abbrev Bits : Fin 3 → Type := fun _ => Bool

/-- A point of the client's space, written out coordinate by coordinate. -/
private def pt (b₀ b₁ b₂ : Bool) : Pt Bits :=
  fun i => if i = 0 then b₀ else if i = 1 then b₁ else b₂

/-- The client's conditioning event `C`: at least one of the first two bits is set. -/
def someBit : Set (Pt Bits) := {ω | ω 0 = true ∨ ω 1 = true}

private lemma mem_someBit {ω : Pt Bits} : ω ∈ someBit ↔ ω 0 = true ∨ ω 1 = true := Iff.rfl

/-- The client's conditioning *variable*, whose `true`-fibre is `C`. -/
def someBitVar : Pt Bits → Bool := fun ω => ω 0 || ω 1

private lemma fiber_someBitVar_true : fiber someBitVar true = someBit := by
  ext ω
  exact Bool.or_eq_true_iff

private lemma mem_fiber_false {ω : Pt Bits} (h : ω ∈ fiber someBitVar false) :
    ω 0 = false ∧ ω 1 = false :=
  Bool.or_eq_false_iff.1 h

private lemma notMem_someBit_iff {ω : Pt Bits} : ω ∉ someBit ↔ ω 0 = false ∧ ω 1 = false := by
  constructor
  · refine fun h => ⟨?_, ?_⟩
    · rcases Bool.eq_false_or_eq_true (ω 0) with h₀ | h₀
      · exact absurd (mem_someBit.2 (Or.inl h₀)) h
      · exact h₀
    · rcases Bool.eq_false_or_eq_true (ω 1) with h₁ | h₁
      · exact absurd (mem_someBit.2 (Or.inr h₁)) h
      · exact h₁
  · rintro ⟨h₀, h₁⟩ hc
    rcases mem_someBit.1 hc with h' | h'
    · rw [h₀] at h'; exact Bool.noConfusion h'
    · rw [h₁] at h'; exact Bool.noConfusion h'

private lemma fiber_someBitVar_false : fiber someBitVar false = someBitᶜ := by
  ext ω
  exact Bool.or_eq_false_iff.trans notMem_someBit_iff.symm

/-- **Definition 4.5 has content on the client's event.**  `{0, 1}` disintegrates `C`
(Definition 4.5, through the working form `disintegrates_iff_splice`): splicing two members
of `C` along `{0, 1}` copies both constrained coordinates from the same point. -/
lemma disintegrates_someBit : Disintegrates ({0, 1} : Finset (Fin 3)) someBit := by
  rw [disintegrates_iff_splice]
  intro a ha b _
  have h0 : ({0, 1} : Finset (Fin 3)).piecewise a b 0 = a 0 :=
    Finset.piecewise_eq_of_mem _ _ _ (by decide)
  have h1 : ({0, 1} : Finset (Fin 3)).piecewise a b 1 = a 1 :=
    Finset.piecewise_eq_of_mem _ _ _ (by decide)
  rcases mem_someBit.1 ha with h | h
  · exact mem_someBit.2 (Or.inl (h0.trans h))
  · exact mem_someBit.2 (Or.inr (h1.trans h))

/-- **…and is not vacuously satisfied.**  A single one of the two coupled coordinates does
*not* disintegrate `C`: splicing `(f, t, f)` and `(t, f, f)` along `{0}` produces
`(f, f, f) ∉ C`.  Together with the previous lemma this pins the disintegrating family of
`C` down to `{∅, {2}, {0,1}, I}`, which is what makes the history computations below
non-degenerate. -/
lemma not_disintegrates_someBit : ¬ Disintegrates ({0} : Finset (Fin 3)) someBit := by
  rw [disintegrates_iff_splice]
  intro h
  have hmem := h (pt false true false) (mem_someBit.2 (Or.inr (by decide)))
    (pt true false false) (mem_someBit.2 (Or.inl (by decide)))
  have h0 : ({0} : Finset (Fin 3)).piecewise (pt false true false) (pt true false false) 0
      = false := (Finset.piecewise_eq_of_mem _ _ _ (by decide)).trans (by decide)
  have h1 : ({0} : Finset (Fin 3)).piecewise (pt false true false) (pt true false false) 1
      = false := (Finset.piecewise_eq_of_notMem _ _ _ (by decide)).trans (by decide)
  rcases mem_someBit.1 hmem with h' | h'
  · rw [h0] at h'; exact Bool.noConfusion h'
  · rw [h1] at h'; exact Bool.noConfusion h'

/-- The third bit is untouched by `C`, so `{2}` disintegrates it too (Definition 4.5). -/
private lemma disintegrates_singleton_two : Disintegrates ({2} : Finset (Fin 3)) someBit := by
  rw [disintegrates_iff_splice]
  intro a _ b hb
  have h0 : ({2} : Finset (Fin 3)).piecewise a b 0 = b 0 :=
    Finset.piecewise_eq_of_notMem _ _ _ (by decide)
  have h1 : ({2} : Finset (Fin 3)).piecewise a b 1 = b 1 :=
    Finset.piecewise_eq_of_notMem _ _ _ (by decide)
  rcases mem_someBit.1 hb with h | h
  · exact mem_someBit.2 (Or.inl (h0.trans h))
  · exact mem_someBit.2 (Or.inr (h1.trans h))

/-- **`H(U₂ | C) = {2}`**, computed from the API: `Generates` (Definition 4.6, working form
`generates_iff`) gives `⊆` through Lemma 4.7's minimality, and the relevance criterion
`mem_history_of_sep` gives `⊇` from two members of `C` differing only in the third bit. -/
lemma history_bg_two : history (bg (Ω := Bits) 2) someBit = {2} := by
  refine Finset.Subset.antisymm (history_subset_of_generates ?_) ?_
  · exact (generates_iff _ _ _).2
      ⟨disintegrates_singleton_two, fun a _ b _ hab => hab 2 (by decide)⟩
  · intro i hi
    rw [Finset.mem_singleton] at hi
    subst hi
    exact mem_history_of_sep (a := pt true false false) (b := pt true false true)
      (mem_someBit.2 (Or.inl (by decide))) (mem_someBit.2 (Or.inl (by decide)))
      (by decide) (by decide)

/-- **`H(U₀ | C) = {0, 1}` — conditioning drags a second factor into the history.**  The
first bit does not depend on the second in any pointwise sense; `1` is in its conditional
history only because no *disintegrating* subset of `{0, 1}` other than `{0, 1}` itself
contains `0`.  The proof is exactly that argument, run against the API: Lemma 4.7 bounds
the history by the generating set `{0, 1}`, `mem_history_of_sep` puts `0` in it, and if `1`
were missing the history would be `{0}`, which `not_disintegrates_someBit` forbids —
`generates_history` is what supplies the disintegration of the history itself. -/
lemma history_bg_zero : history (bg (Ω := Bits) 0) someBit = ({0, 1} : Finset (Fin 3)) := by
  have hsub : history (bg (Ω := Bits) 0) someBit ⊆ {0, 1} :=
    history_subset_of_generates
      ((generates_iff _ _ _).2 ⟨disintegrates_someBit, fun a _ b _ hab => hab 0 (by decide)⟩)
  have h0 : (0 : Fin 3) ∈ history (bg (Ω := Bits) 0) someBit :=
    mem_history_of_sep (a := pt true true false) (b := pt false true false)
      (mem_someBit.2 (Or.inr (by decide))) (mem_someBit.2 (Or.inr (by decide)))
      (by decide) (by decide)
  by_cases h1 : (1 : Fin 3) ∈ history (bg (Ω := Bits) 0) someBit
  · refine Finset.Subset.antisymm hsub fun i hi => ?_
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact h0
    · rw [Finset.mem_singleton] at hi
      subst hi
      exact h1
  · exfalso
    have heq : history (bg (Ω := Bits) 0) someBit = {0} := by
      refine Finset.Subset.antisymm (fun i hi => ?_) (Finset.singleton_subset_iff.2 h0)
      rcases Finset.mem_insert.1 (hsub hi) with rfl | hi'
      · exact Finset.mem_singleton_self _
      · rw [Finset.mem_singleton] at hi'
        subst hi'
        exact absurd hi h1
    apply not_disintegrates_someBit
    rw [← heq]
    exact (generates_history (bg (Ω := Bits) 0) someBit).2

private lemma one_mem_history_bg_one : (1 : Fin 3) ∈ history (bg (Ω := Bits) 1) someBit :=
  mem_history_of_sep (a := pt true true false) (b := pt true false false)
    (mem_someBit.2 (Or.inl (by decide))) (mem_someBit.2 (Or.inl (by decide)))
    (by decide) (by decide)

/-- **Conditioning creates structural dependence.**  `U₀` and `U₁` are independent
unconditionally, but Definition 4.10's conditional form fails at the value `true` of the
client's conditioning variable, because the two conditional histories both contain `1`.
This is the concrete reason Definition 4.10 must condition on *events* rather than only
compare unconditional histories. -/
example : ¬ StructIndepGiven (bg (Ω := Bits) 0) (bg (Ω := Bits) 1) someBitVar := by
  intro h
  have hd := h true
  rw [fiber_someBitVar_true, history_bg_zero] at hd
  exact Finset.disjoint_left.1 hd (by decide) one_mem_history_bg_one

/-- **The independence that survives conditioning.**  `U₀ ⊥_Ω U₂ | V` for the same `V`: at
`V = true` the two conditional histories are the `{0, 1}` and `{2}` computed above, and at
`V = false` the event pins the first bit down, so `U₀` has *empty* conditional history by
Lemma 4.7's minimality against the empty generating set.  This is the hypothesis that
Theorem 6.2 and Proposition 5.2 are fed below. -/
lemma structIndepGiven_bg_zero_two :
    StructIndepGiven (bg (Ω := Bits) 0) (bg (Ω := Bits) 2) someBitVar := by
  intro z
  cases z with
  | false =>
    have hgen : Generates (∅ : Finset (Fin 3)) (bg (Ω := Bits) 0) (fiber someBitVar false) :=
      (generates_iff _ _ _).2 ⟨disintegrates_empty _, fun a ha b hb _ =>
        ((mem_fiber_false ha).1).trans (mem_fiber_false hb).1.symm⟩
    rw [Finset.subset_empty.1 (history_subset_of_generates hgen)]
    exact Finset.disjoint_empty_left _
  | true =>
    rw [fiber_someBitVar_true, history_bg_zero, history_bg_two]
    decide

/-- **Lemma 4.8 applied to the client's joint variable.**  `H((U₀, U₂) | C)` is all of `I`,
even though `U₂` alone contributes only `{2}` — the union in Lemma 4.8 is what makes the
joint variable see the coupled factor `1` that neither coordinate constrains directly. -/
example : history (pair (bg (Ω := Bits) 0) (bg (Ω := Bits) 2)) someBit = Finset.univ := by
  rw [history_pair, history_bg_zero, history_bg_two]
  decide

/-- **Lemma 4.9 in `Finset` form, on the client's own conditioning variable.**  A `Bool`
variable has exactly two events, so Lemma 4.9's union computes `H(V)` from the history of
`C` and the history of its complement — the decomposition a client uses to reduce a
variable's history to event histories. -/
example : history someBitVar (Set.univ : Set (Pt Bits))
    = eventHistory someBit Set.univ ∪ eventHistory someBitᶜ Set.univ := by
  have huniv : (Finset.univ : Finset Bool) = {true, false} := by decide
  rw [history_eq_biUnion_fibers, huniv]
  simp [fiber_someBitVar_true, fiber_someBitVar_false]

/-- **An event and its complement have the same history**, on any factored space.  The API
has no `eventHistory_compl`, but the fact is two applications of Lemma 4.7's monotonicity
(`history_mono_of_derived`): each indicator is derived from the other by `Not`, one
direction definitionally and the other through `propext`.  A client conditioning on `¬A`
therefore never has to redo a history computation done for `A`. -/
example {I : Type*} [DecidableEq I] [Fintype I] {Ω : I → Type*} (A C : Set (Pt Ω)) :
    eventHistory Aᶜ C = eventHistory A C := by
  refine Finset.Subset.antisymm (history_mono_of_derived ⟨fun p => ¬ p, fun _ _ => rfl⟩)
    (history_mono_of_derived ⟨fun p => ¬ p, fun _ _ => ?_⟩)
  exact propext ⟨fun h hn => hn h, fun h => Classical.not_not.mp h⟩

/-! ### Distributions built by the client

A biased coin per factor, assembled with `Distr.mix`, `Distr.delta` and `Distr.prod`. -/

/-- The client's biased coin: `true` with probability `t`, built out of the API's `mix` and
`delta` rather than by hand — so its two masses come from `mix`'s definition and no
`Distr` structure has to be constructed by the client at all. -/
noncomputable def coin (t : unitInterval) : Distr Bool :=
  Distr.mix t (Distr.delta false) (Distr.delta true)

private lemma coin_mass_true (t : unitInterval) : (coin t).mass true = (t : ℝ) := by
  simp [coin, Distr.mix, Distr.delta_mass]

private lemma coin_mass_false (t : unitInterval) : (coin t).mass false = 1 - (t : ℝ) := by
  simp [coin, Distr.mix, Distr.delta_mass]

private lemma coin_mass_pos {t : unitInterval} (h₀ : (0 : ℝ) < t) (h₁ : (t : ℝ) < 1) (b : Bool) :
    0 < (coin t).mass b := by
  cases b with
  | false => rw [coin_mass_false]; linarith
  | true => rw [coin_mass_true]; exact h₀

/-- A biased product distribution on the client's space: bit `i` comes up `true` with
probability `t i`, independently. -/
noncomputable def bits (t : Fin 3 → unitInterval) : Distr (Pt Bits) :=
  Distr.prod fun i => coin (t i)

lemma factorizes_bits (t : Fin 3 → unitInterval) : Factorizes (bits t) := factorizes_prod _

/-- **The client's family is the API's interpolation.**  `bits` at a constant bias is
literally the `R^λ` of Lemmas C.5/C.10/6.5 between the all-`false` and all-`true` point
masses, so everything the API proves about `interp` applies to it unchanged. -/
example (t : unitInterval) :
    bits (fun _ => t) = interp (fun _ => Distr.delta false) (fun _ => Distr.delta true) t := rfl

/-- **…and at the endpoints it is a point mass.**  `interp_zero` plus Definition C.1's
factorwise delta identity (`Distr.delta_eq_prod`) collapses the whole product to a single
`δ`, a computation the client would otherwise do by hand over `2³` points. -/
example : bits (fun _ => 0) = Distr.delta (fun _ => false : Pt Bits) := by
  rw [show bits (fun _ => (0 : unitInterval))
      = interp (fun _ => Distr.delta false) (fun _ => Distr.delta true) 0 from rfl, interp_zero,
    ← Distr.delta_eq_prod]

/-- **The marginals are the coins they were built from** (`Distr.margAt`, Definition C.2 at
a single factor), so a client can read a bias back off a distribution it assembled. -/
example (t : Fin 3 → unitInterval) (i : Fin 3) : ((bits t).margAt i).mass true = (t i : ℝ) := by
  rw [bits, Distr.margAt_prod, coin_mass_true]

private lemma prob_bits_fiber (t : Fin 3 → unitInterval) (i : Fin 3) (b : Bool) :
    (bits t).prob (fiber (bg (Ω := Bits) i) b) = (coin (t i)).mass b := by
  have hset : fiber (bg (Ω := Bits) i) b
      = {ω : Pt Bits | ∀ j ∈ ({i} : Finset (Fin 3)), ω j = (fun _ => b : Pt Bits) j} := by
    ext ω
    simp [fiber, bg]
  rw [hset, bits, Distr.prob_prod_agree_on]
  simp

private lemma prob_bits_pair (t : Fin 3 → unitInterval) (b₀ b₁ : Bool) :
    (bits t).prob (fiber (bg (Ω := Bits) 0) b₀ ∩ fiber (bg (Ω := Bits) 1) b₁)
      = (coin (t 0)).mass b₀ * (coin (t 1)).mass b₁ := by
  have hset : fiber (bg (Ω := Bits) 0) b₀ ∩ fiber (bg (Ω := Bits) 1) b₁
      = {ω : Pt Bits | ∀ j ∈ ({0, 1} : Finset (Fin 3)), ω j = pt b₀ b₁ false j} := by
    ext ω
    constructor
    · rintro ⟨h0, h1⟩ j hj
      rcases Finset.mem_insert.1 hj with rfl | hj
      · exact h0
      · rw [Finset.mem_singleton] at hj
        subst hj
        exact h1
    · intro h
      exact ⟨h 0 (by decide), h 1 (by decide)⟩
  rw [hset, bits, Distr.prob_prod_agree_on, Finset.prod_insert (by decide),
    Finset.prod_singleton]
  rfl

/-- **The API has no `Distr.prob_compl`**; a client gets it in three lines from
`prob_union_of_disjoint` and `prob_univ`.  Recorded here because every probability
computation below needs it. -/
private lemma prob_compl {S : Type*} [Fintype S] (P : Distr S) (A : Set S) :
    P.prob Aᶜ = 1 - P.prob A := by
  have h := P.prob_union_of_disjoint (A := A) (B := Aᶜ) disjoint_compl_right
  rw [Set.union_compl_self, P.prob_univ] at h
  linarith

/-- **The probability of the client's conditioning event**, computed end to end from the
product structure: `P(C) = 1 − (1 − t₀)(1 − t₁)`.  This is the number a client needs before
conditioning on `C` at all, and it comes out of `Distr.prob_prod_agree_on` (through
`prob_bits_pair`) with no sum over the eight points of `Ω`. -/
example (t : Fin 3 → unitInterval) :
    (bits t).prob someBit = 1 - (1 - (t 0 : ℝ)) * (1 - (t 1 : ℝ)) := by
  have hc : someBitᶜ = fiber (bg (Ω := Bits) 0) false ∩ fiber (bg (Ω := Bits) 1) false := by
    ext ω
    exact notMem_someBit_iff
  have h := prob_compl (bits t) someBit
  rw [hc, prob_bits_pair, coin_mass_false, coin_mass_false] at h
  linarith

/-- **Conditional probability against the product structure** (`Distr.condProb`): under the
client's distribution the second bit is unaffected by conditioning on the first, and the
`0/0` convention is avoided by the positivity hypothesis.  A client checking that its
assembled distribution really has independent coordinates runs exactly this. -/
example (t : Fin 3 → unitInterval) (h : (0 : ℝ) < (t 0 : ℝ)) :
    (bits t).condProb (fiber (bg (Ω := Bits) 1) true) (fiber (bg (Ω := Bits) 0) true)
      = (t 1 : ℝ) := by
  rw [Distr.condProb, Set.inter_comm, prob_bits_pair, prob_bits_fiber, coin_mass_true,
    coin_mass_true, mul_comm, mul_div_assoc, div_self h.ne', mul_one]

/-- **The support is everything exactly when no bias is degenerate** (`Distr.support`,
`Distr.prod_mass_pos_iff`) — the check behind every `StrictlyPositive` hypothesis in the
DAG half of the API (`condCPD`, `tauPos_bijective`). -/
example (t : Fin 3 → unitInterval) (h₀ : ∀ i, (0 : ℝ) < t i) (h₁ : ∀ i, (t i : ℝ) < 1) :
    (bits t).support = Set.univ := by
  ext ω
  simp only [Set.mem_univ, iff_true, Distr.mem_support_iff, bits]
  exact (Distr.prod_mass_pos_iff _ _).2 fun i => coin_mass_pos (h₀ i) (h₁ i) (ω i)

/-- **Pushing the client's distribution forward along its conditioning variable**
(`Distr.map`, `Distr.map_mass`): the law of `V` on `Bool`, computed from the product
structure.  Composed with the previous computations this says the two descriptions of
`P(C)` — as an event probability upstairs and as a mass downstairs — agree. -/
example (t : Fin 3 → unitInterval) :
    ((bits t).map someBitVar).mass false = (1 - (t 0 : ℝ)) * (1 - (t 1 : ℝ)) := by
  have hpre : someBitVar ⁻¹' {false}
      = fiber (bg (Ω := Bits) 0) false ∩ fiber (bg (Ω := Bits) 1) false := by
    ext ω
    exact Bool.or_eq_false_iff
  rw [Distr.map_mass, hpre, prob_bits_pair, coin_mass_false, coin_mass_false]

/-- **Splitting the client's space in two** (Definition C.1's `P_J ⊗ P_{I∖J}`, working form
`Distr.outerCompl`): a factorizing distribution's mass at `ω` is the product of the two
marginal masses at `ω_{0,1}` and `ω_{2}`.  This is the shape every Appendix-C argument
takes, made concrete on the client's own `J = {0, 1}`. -/
example (t : Fin 3 → unitInterval) (ω : Pt Bits) :
    (bits t).mass ω
      = ((bits t).marg ({0, 1} : Finset (Fin 3))).mass (proj {0, 1} ω) *
        ((bits t).marg ({0, 1} : Finset (Fin 3))ᶜ).mass (proj ({0, 1} : Finset (Fin 3))ᶜ ω) := by
  conv_lhs => rw [(factorizes_bits t).eq_outerCompl ({0, 1} : Finset (Fin 3))]
  exact Distr.outerCompl_mass _ _ ω

/-! ### Theorem 6.2 and Proposition 6.6, on the client's objects -/

/-- **Theorem 6.2 used forwards.**  The structural independence proved above transfers to
*every* distribution the client might assemble, in particular to its own biased product —
no probability computation is needed to get a conditional independence out of a history
computation. -/
example (t : Fin 3 → unitInterval) :
    CondIndepVar (bits t) (bg (Ω := Bits) 0) (bg (Ω := Bits) 2) someBitVar :=
  condIndepVar_of_structIndepGiven structIndepGiven_bg_zero_two (bits t) (factorizes_bits t)

/-- **Theorem 6.2 used backwards, and read as a combinatorial fact.**  A client that only
knows an *empirical* statement — every factorizing distribution makes the first two bits
independent given a constant — gets a statement about histories, and composing it with the
sensitivity criterion `mem_history_iff_exists_ne` turns it into the concrete non-membership
`0 ∉ H(U₁)`.  Neither endpoint says this; completeness is what converts the quantified
probabilistic hypothesis into an index-set fact. -/
example (h : ∀ P : Distr (Pt Bits), Factorizes P →
      CondIndepVar P (bg (Ω := Bits) 0) (bg (Ω := Bits) 1) (fun _ : Pt Bits => ())) :
    (0 : Fin 3) ∉ history (bg (Ω := Bits) 1) (Set.univ : Set (Pt Bits)) := by
  have hfib : fiber (fun _ : Pt Bits => ()) () = (Set.univ : Set (Pt Bits)) :=
    Set.eq_univ_iff_forall.2 fun _ => rfl
  have hd := structIndepGiven_of_forall_condIndepVar (Or.inl inferInstance) h ()
  rw [hfib] at hd
  refine Finset.disjoint_left.1 hd ((mem_history_iff_exists_ne _ 0).2 ?_)
  exact ⟨pt true false false, pt false false false, by decide, by decide⟩

/-- **Proposition 6.6 at `S = Δ^⊗(Ω)` itself.**  All of `Δ^⊗(Ω)` is trivially open in
`Δ^⊗(Ω)` under the metric-ball criterion (`dd:open-ball`) and is nonempty because the
client already built a member of it, so strong completeness specialises back to Theorem
6.2's completeness direction.  A client should check this before trusting
`structIndepGiven_of_open` on a smaller `S`: it is the sanity condition that the openness
hypothesis is satisfiable at all. -/
example {α β γ : Type} [Nonempty α] [Nonempty β] {X : Pt Bits → α} {Y : Pt Bits → β}
    {Z : Pt Bits → γ} (h : ∀ P ∈ factorizing Bits, CondIndepVar P X Y Z) :
    StructIndepGiven X Y Z :=
  structIndepGiven_of_open (factorizing Bits) (subset_refl _)
    ⟨bits (fun _ => 0), factorizes_bits _⟩
    (fun _ _ => ⟨1, one_pos, fun _ hQ' _ => hQ'⟩) h

/-! ### Proposition 5.2's axioms as client tools -/

/-- **Composition then weak union, on concrete client variables.**  Proposition 5.2 says
structural independence is a compositional semigraphoid; the two axioms a client actually
reaches for are composition (to merge two independences into a joint one) and weak union
(to move part of the merged variable into the conditioning slot).  Chained here they turn
two independences given `V` into one independence given `(U₁, V)` — a rewriting step no
single endpoint provides. -/
example (h₁ : StructIndepGiven (bg (Ω := Bits) 0) (bg (Ω := Bits) 1) someBitVar)
    (h₂ : StructIndepGiven (bg (Ω := Bits) 0) (bg (Ω := Bits) 2) someBitVar) :
    StructIndepGiven (bg (Ω := Bits) 0) (bg (Ω := Bits) 2) (pair (bg (Ω := Bits) 1) someBitVar) :=
  (isCompositionalSemigraphoid_structIndepRel (Ω := Bits)).toIsSemigraphoid.weakUnion
    _ _ _ _ ((isCompositionalSemigraphoid_structIndepRel (Ω := Bits)).composition _ _ _ _ h₁ h₂)

/-- **The missing axiom is genuinely missing.**  Table 1's negative claim
(`not_isGraphoid_structIndepRel`) is stated about one particular relation; what a client
wants from it is the general statement that no argument can upgrade Proposition 5.2's
compositional semigraphoid to a graphoid.  Composing the two endpoints gives exactly
that. -/
example : ¬ ∀ R : IndepRel (fun _ : Unit => Fin 3), IsCompositionalSemigraphoid R → IsGraphoid R :=
  fun h => not_isGraphoid_structIndepRel (h _ isCompositionalSemigraphoid_structIndepRel)

/-! ### A client DAG: the chain `0 → 1 → 2` over a heterogeneous value family

Nothing here reuses `FactoredSpaces.Examples`' collider or its one-node perfect map; the
chain is the configuration where d-separation has content that adjacency cannot show, and
the value family is genuinely dependent (`Val : V → Type w` is polymorphic), so the
`bnIndex`/`bnFactor` construction is exercised at three different factor types. -/

/-- The client's DAG: the chain `0 → 1 → 2` on `Fin 3`. -/
def chainG : Digraph (Fin 3) := ⟨fun a b => (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2)⟩

instance : DecidableRel chainG.Adj :=
  fun a b => inferInstanceAs (Decidable ((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2)))

/-- A heterogeneous value family on the chain: `Bool`, `Fin 3`, `Bool`. -/
abbrev ChainVal : Fin 3 → Type
  | 0 => Bool
  | 1 => Fin 3
  | 2 => Bool

instance instFintypeChainVal : ∀ v, Fintype (ChainVal v)
  | 0 => inferInstanceAs (Fintype Bool)
  | 1 => inferInstanceAs (Fintype (Fin 3))
  | 2 => inferInstanceAs (Fintype Bool)

instance instDecidableEqChainVal : ∀ v, DecidableEq (ChainVal v)
  | 0 => inferInstanceAs (DecidableEq Bool)
  | 1 => inferInstanceAs (DecidableEq (Fin 3))
  | 2 => inferInstanceAs (DecidableEq Bool)

instance instNontrivialChainVal : ∀ v, Nontrivial (ChainVal v)
  | 0 => inferInstanceAs (Nontrivial Bool)
  | 1 => inferInstanceAs (Nontrivial (Fin 3))
  | 2 => inferInstanceAs (Nontrivial Bool)

private lemma chain_adj_lt {a b : Fin 3} (h : chainG.Adj a b) : a.val < b.val := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

private lemma chain_ancestor_lt {a b : Fin 3} (h : chainG.IsAncestor a b) : a.val < b.val := by
  induction h with
  | single hab => exact chain_adj_lt hab
  | tail _ hbc ih => exact ih.trans (chain_adj_lt hbc)

lemma chainG_isAcyclic : chainG.IsAcyclic :=
  fun _ h => absurd (chain_ancestor_lt h) (lt_irrefl _)

private lemma chain_parents_zero : chainG.parents 0 = ∅ := by decide

/-! ### Reading the node variables off `Ω^G` (eq. (4)) -/

/-- **`X_0` is literally one coordinate of `Ω^G`.**  `nodeVar_apply` is eq. (4) as a table
lookup; at a source of the DAG the consulted parent configuration is the unique element of
`Val_∅`, so `X_0` reads off index `⟨0, c⟩` for whichever `c` the client names. -/
example (ω : Pt (bnFactor chainG ChainVal)) (c : ParentVals chainG ChainVal 0) :
    nodeVar (Val := ChainVal) chainG_isAcyclic 0 ω = ω ⟨0, c⟩ := by
  rw [nodeVar_apply]
  refine table_congr ω (funext fun u => ?_)
  have hne : ¬ (chainG.parents 0).Nonempty := by
    rw [chain_parents_zero]; exact Finset.not_nonempty_empty
  exact absurd ⟨u.1, u.2⟩ hne

/-- **Every fibre of the joint variable is nonempty and explicitly cut out.**
`jointVar_constTable` supplies a point of each fibre; `jointVar_eq_iff` (the set identity
behind Lemma B.2) describes it by three table entries.  This is what a client needs before
conditioning on `{X = x}`: no such event is empty. -/
example (x : Pt ChainVal) :
    (fiber (jointVar (Val := ChainVal) chainG_isAcyclic) x).Nonempty ∧
      fiber (jointVar (Val := ChainVal) chainG_isAcyclic) x
        = {ω | ∀ v, ω (idxAt chainG ChainVal x v) = x v} :=
  ⟨⟨constTable chainG ChainVal x, jointVar_constTable chainG_isAcyclic x⟩,
   Set.ext fun ω => jointVar_eq_iff chainG_isAcyclic ω x⟩

/-! ### Distributions over the chain: Lemma 5.3 and Proposition 5.4 composed -/

/-- The client's own distribution on `Ω^G`: uniform on every factor, hence a product. -/
noncomputable def chainPΩ : Distr (Pt (bnFactor chainG ChainVal)) :=
  Distr.prod fun _ => Distr.uniform

private lemma chainPΩ_factorizes : Factorizes chainPΩ := factorizes_prod _

private lemma chainPΩ_pos : chainPΩ.StrictlyPositive := fun ω =>
  (Distr.prod_mass_pos_iff _ ω).mpr fun _ => Distr.uniform_strictlyPositive _

/-- **`Δ^*(G)` is exactly the `τ`-image of `Δ^⊗(Ω^G)`, on the client's chain.**  Both halves
of Lemma 5.3 in one statement: `τ⁻¹` of a CPD family witnesses `⟹` (`factorizes_tauInv` +
`tau_tauInv`), `factorizesOverDAG_tau` witnesses `⟸`.  Neither endpoint states the
equality, and it is the form a client asking "does my distribution come from a Bayes net
over this graph?" wants. -/
example (P : Distr (Pt ChainVal)) :
    FactorizesOverDAG chainG ChainVal P ↔
      ∃ PΩ : Distr (Pt (bnFactor chainG ChainVal)),
        Factorizes PΩ ∧ tau chainG_isAcyclic PΩ = P := by
  constructor
  · rintro ⟨φ, hφ⟩
    exact ⟨tauInv φ, factorizes_tauInv φ, tau_tauInv chainG_isAcyclic φ hφ⟩
  · rintro ⟨PΩ, hfac, rfl⟩
    exact factorizesOverDAG_tau chainG_isAcyclic hfac

/-- **Identifiability upstairs from the node law downstairs.**  Injectivity of `τ` on the
strictly positive factorizing distributions (Lemma 5.3 in its true form, errata E5): fixing
the law of `X = (X_0, X_1, X_2)` fixes the whole table distribution on `Ω^G`.  The
positivity hypotheses are not decoration — `tauPos_bijective` is false without them. -/
lemma chain_eq_of_tau_eq {P Q : Distr (Pt (bnFactor chainG ChainVal))}
    (hPf : Factorizes P) (hPp : P.StrictlyPositive)
    (hQf : Factorizes Q) (hQp : Q.StrictlyPositive)
    (h : tau chainG_isAcyclic P = tau chainG_isAcyclic Q) : P = Q := by
  have hinj := (tauPos_bijective (G := chainG) (Val := ChainVal) chainG_isAcyclic).1
    (show tauPos chainG_isAcyclic ⟨P, hPf, hPp⟩ = tauPos chainG_isAcyclic ⟨Q, hQf, hQp⟩ from
      Subtype.ext h)
  exact congrArg Subtype.val hinj

/-- The same fact at the client's own witness: `chainPΩ` is the *only* strictly positive
factorizing distribution on `Ω^G` inducing the uniform law on `Val`. -/
example (Q : Distr (Pt (bnFactor chainG ChainVal))) (hQf : Factorizes Q)
    (hQp : Q.StrictlyPositive)
    (h : tau chainG_isAcyclic Q = tau chainG_isAcyclic chainPΩ) : Q = chainPΩ :=
  chain_eq_of_tau_eq hQf hQp chainPΩ_factorizes chainPΩ_pos h

/-- **The chain's node law computes, and `M^G` models it.**  Lemma B.2 turns
`τ(P^Ω)(x) = P^Ω(X = x)` into a product of factor marginals, which `Distr.margAt_prod`
reads off the client's product — mass `1/12` at every joint value of
`Val_0 × Val_1 × Val_2`; and Lemma 5.3 composed with Proposition 5.4 says `M^G` is a
factored space model of that law.  Concrete arithmetic out of the API, plus the structural
statement about it. -/
example (x : Pt ChainVal) :
    (tau chainG_isAcyclic chainPΩ).mass x = 1 / 12 ∧
      IsFactoredSpaceModel (jointVar (Val := ChainVal) chainG_isAcyclic)
        (tau chainG_isAcyclic chainPΩ) := by
  refine ⟨?_, (factorizesOverDAG_iff_isFactoredSpaceModel chainG_isAcyclic _).mp
    (factorizesOverDAG_tau chainG_isAcyclic chainPΩ_factorizes)⟩
  rw [tau_mass, prob_jointVar_fiber chainG_isAcyclic chainPΩ_factorizes]
  have hm : ∀ v : Fin 3,
      (chainPΩ.margAt ⟨v, parentConfig chainG ChainVal x v⟩).mass (x v)
        = (Fintype.card (ChainVal v) : ℝ)⁻¹ := by
    intro v
    rw [chainPΩ, Distr.margAt_prod]
    rfl
  rw [Finset.prod_congr rfl fun v _ => hm v, Fin.prod_univ_three]
  norm_num

/-! ### Proposition 5.6: the chain's strict time order -/

private lemma chain_adj_zero_one : chainG.Adj 0 1 := Or.inl ⟨rfl, rfl⟩

private lemma chain_adj_one_two : chainG.Adj 1 2 := Or.inr ⟨rfl, rfl⟩

private lemma chain_isAncestor_zero_two : chainG.IsAncestor 0 2 :=
  (Relation.TransGen.single chain_adj_zero_one).tail chain_adj_one_two

/-- **Proposition 5.6 in both signs.**  The edge-free pair `(0, 2)` is still ordered —
`X_0 <_{Ω^G} X_2`, since `0` is an *ancestor* of `2` — and strictly in one direction only,
which is what makes `StrictlyBefore` a genuine strict order here rather than a symmetric
one.  Each application passes `(Val := ChainVal)` explicitly (`R1-F50`). -/
example : StrictlyBefore (nodeVar (Val := ChainVal) chainG_isAcyclic 0)
      (nodeVar chainG_isAcyclic 2) ∧
    ¬ StrictlyBefore (nodeVar (Val := ChainVal) chainG_isAcyclic 2)
      (nodeVar chainG_isAcyclic 0) := by
  refine ⟨(isAncestor_iff_strictlyBefore (Val := ChainVal) chainG_isAcyclic
      (by decide : (0 : Fin 3) ≠ 2)).mp chain_isAncestor_zero_two, fun h => ?_⟩
  exact absurd (chain_ancestor_lt ((isAncestor_iff_strictlyBefore (Val := ChainVal)
    chainG_isAcyclic (by decide : (2 : Fin 3) ≠ 0)).mpr h)) (by decide)

/-! ### Proposition 5.5: a d-separation of the chain, proved through the `Z`-closure -/

private lemma chain_unblockedAnc_zero (Z : Finset (Fin 3)) :
    chainG.unblockedAnc Z 0 ⊆ ({0} : Set (Fin 3)) := by
  intro u hu
  rcases Relation.ReflTransGen.cases_tail hu with h | ⟨c, -, hcr⟩
  · exact h.symm
  · rcases hcr.1 with ⟨-, h1⟩ | ⟨-, h2⟩
    · exact absurd h1 (by decide)
    · exact absurd h2 (by decide)

private lemma chain_unblockedAnc_one (Z : Finset (Fin 3)) :
    chainG.unblockedAnc Z 1 ⊆ ({0, 1} : Set (Fin 3)) := by
  intro u hu
  rcases Relation.ReflTransGen.cases_tail hu with h | ⟨c, hc, hcr⟩
  · exact Or.inr h.symm
  · have hc0 : c = 0 := by
      rcases hcr.1 with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact h1
      · exact absurd h2 (by decide)
    subst hc0
    exact Or.inl (chain_unblockedAnc_zero Z hc)

private lemma chain_unblockedAnc_two :
    chainG.unblockedAnc {1} 2 ⊆ ({2} : Set (Fin 3)) := by
  intro u hu
  rcases Relation.ReflTransGen.cases_tail hu with h | ⟨c, -, hcr⟩
  · exact h.symm
  · have hc1 : c = 1 := by
      rcases hcr.1 with ⟨-, h1⟩ | ⟨h2, -⟩
      · exact absurd h1 (by decide)
      · exact h2
    subst hc1
    exact absurd (Finset.mem_singleton_self (1 : Fin 3)) hcr.2

private lemma chain_isZClosed_zero_one : chainG.IsZClosed {1} ({0, 1} : Set (Fin 3)) := by
  rintro w hw -
  rw [Finset.mem_singleton] at hw
  subst hw
  exact chain_unblockedAnc_one {1}

private lemma chain_isZClosed_two : chainG.IsZClosed {1} ({2} : Set (Fin 3)) := by
  rintro w hw ⟨m, hm1, hm2⟩
  rw [Finset.mem_singleton] at hw
  subst hw
  have hm : (m : Fin 3) = 2 := hm2
  subst hm
  exact absurd (chain_unblockedAnc_one {1} hm1 : (2 : Fin 3) = 0 ∨ (2 : Fin 3) = 1) (by decide)

private lemma chain_zClosureSet_zero :
    chainG.zClosureSet {1} {0} ⊆ ({0, 1} : Set (Fin 3)) := by
  intro u hu
  obtain ⟨a, ha, -, hua⟩ := chainG.exists_of_mem_zClosureSet hu
  rw [Finset.mem_singleton] at ha
  subst ha
  exact chainG.zClosure_subset chain_isZClosed_zero_one
    ((chain_unblockedAnc_zero {1}).trans (Set.singleton_subset_iff.2 (Set.mem_insert _ _))) hua

private lemma chain_zClosureSet_two :
    chainG.zClosureSet {1} {2} ⊆ ({2} : Set (Fin 3)) := by
  intro u hu
  obtain ⟨a, ha, -, hua⟩ := chainG.exists_of_mem_zClosureSet hu
  rw [Finset.mem_singleton] at ha
  subst ha
  exact chainG.zClosure_subset chain_isZClosed_two chain_unblockedAnc_two hua

/-- **The chain's Markov d-separation, from the `Z`-closure criterion.**  `S_{1}({0})` stays
inside `{0, 1}` and `S_{1}({2})` inside `{2}`, because conditioning on `1` blocks the only
route into `2`; `dSeparated_iff_disjoint_zClosureSet` turns that into `0 ⟂ 2 | 1`.  The
closure criterion is much cheaper here than exhibiting trails. -/
lemma chain_dSeparated : chainG.DSeparated {0} {2} {1} := by
  rw [Digraph.dSeparated_iff_disjoint_zClosureSet chainG_isAcyclic]
  refine Set.disjoint_left.2 fun u hu1 hu2 => ?_
  have h1 : u = 0 ∨ u = 1 := chain_zClosureSet_zero hu1
  have h2 : u = 2 := chain_zClosureSet_two hu2
  rcases h1 with rfl | rfl <;> exact absurd h2 (by decide)

private lemma chain_zero_mem_unblockedAnc_two : (0 : Fin 3) ∈ chainG.unblockedAnc ∅ 2 :=
  Relation.ReflTransGen.head ⟨chain_adj_zero_one, Finset.notMem_empty 0⟩
    (Relation.ReflTransGen.head ⟨chain_adj_one_two, Finset.notMem_empty 1⟩
      Relation.ReflTransGen.refl)

/-- **The same pair is *not* d-separated unconditionally**, so the chain's conditional
independence is a genuine consequence of conditioning: `0` lies in both `Z`-closures when
`Z = ∅`. -/
lemma chain_not_dSeparated_empty : ¬ chainG.DSeparated {0} {2} ∅ := by
  rw [Digraph.dSeparated_iff_disjoint_zClosureSet chainG_isAcyclic]
  refine fun hdis => Set.disjoint_left.1 hdis
    (chainG.mem_zClosureSet_self (Finset.mem_singleton_self 0) (Finset.notMem_empty 0)) ?_
  exact chainG.mem_zClosureSet_of_mem_unblockedAnc (Finset.mem_singleton_self 2)
    (Finset.notMem_empty 2) chain_zero_mem_unblockedAnc_two

/-- The structural reading of `chain_dSeparated`, via Proposition 5.5. -/
lemma chain_structIndepGiven :
    StructIndepGiven (nodesVar (Val := ChainVal) chainG_isAcyclic {0})
      (nodesVar chainG_isAcyclic {2}) (nodesVar chainG_isAcyclic {1}) :=
  (dSeparated_iff_structIndepGiven (Val := ChainVal) chainG_isAcyclic {0} {2} {1}).mp
    chain_dSeparated

/-- **The payoff: a graph fact becomes a probabilistic one, for every distribution at
once.**  Proposition 5.5 turns `0 ⟂ 2 | 1` into structural independence in `M^G`; the
soundness half of Theorem 6.2 then makes `X_0 ⊥ X_2 | X_1` hold in *every* distribution
factorizing over `Ω^G` — not merely in those that factorize over `G`. -/
example (P : Distr (Pt (bnFactor chainG ChainVal))) (hP : Factorizes P) :
    CondIndepVar P (nodesVar (Val := ChainVal) chainG_isAcyclic {0})
      (nodesVar chainG_isAcyclic {2}) (nodesVar chainG_isAcyclic {1}) :=
  condIndepVar_of_structIndepGiven chain_structIndepGiven P hP

/-- **Proposition 5.5 is not vacuously "always independent".**  Dropping the conditioning
set makes the two endpoints structurally *dependent*, by the completeness half of the same
iff run against `chain_not_dSeparated_empty`. -/
example : ¬ StructIndepGiven (nodesVar (Val := ChainVal) chainG_isAcyclic {0})
    (nodesVar chainG_isAcyclic {2}) (nodesVar chainG_isAcyclic ∅) := fun h =>
  chain_not_dSeparated_empty
    ((dSeparated_iff_structIndepGiven (Val := ChainVal) chainG_isAcyclic {0} {2} ∅).mpr h)

/-! ### Definition 5.7 unfolded on the client's objects -/

/-- **What a perfect-map hypothesis buys on this chain.**  From `IsPerfectMapDAG chainG P`
alone: `P` is modelled by `M^G` — the I-map ⟹ factorization theorem that Proposition
5.8(1)'s printed proof omits (errata E7), composed with Proposition 5.4 — the proved
d-separation `0 ⟂ 2 | 1` reads off as a conditional independence of `P`'s projections, and
Proposition 5.8(1) upgrades the hypothesis to Definition 5.7(2) for `M^G`, whose second
conjunct at `({0}, {2}, {1})` is the bridge between `P`'s coordinate independences and the
factored space's structural ones. -/
example (P : Distr (Pt ChainVal)) (hpm : IsPerfectMapDAG chainG P) :
    IsFactoredSpaceModel (jointVar (Val := ChainVal) chainG_isAcyclic) P ∧
      CondIndepVar P (proj {0}) (proj {2}) (proj {1}) ∧
      (CondIndepVar P (proj {0}) (proj {2}) (proj {1}) ↔
        StructIndepGiven (nodesVar (Val := ChainVal) chainG_isAcyclic {0})
          (nodesVar chainG_isAcyclic {2}) (nodesVar chainG_isAcyclic {1})) := by
  obtain ⟨-, hiff⟩ := isPerfectMapFSM_nodeVar_of_isPerfectMapDAG chainG_isAcyclic hpm
  exact ⟨(factorizesOverDAG_iff_isFactoredSpaceModel chainG_isAcyclic P).mp
      (factorizesOverDAG_of_isIMapDAG chainG_isAcyclic hpm.isIMapDAG),
    (hpm {0} {2} {1}).mp chain_dSeparated, hiff {0} {2} {1}⟩

private lemma chain_condIndep_delta (x : Pt ChainVal) (A B C : Set (Pt ChainVal)) :
    CondIndep (Distr.delta x) A B C := by
  simp only [CondIndep, Distr.delta_prob, Set.mem_inter_iff]
  by_cases hA : x ∈ A <;> by_cases hB : x ∈ B <;> by_cases hC : x ∈ C <;>
    simp [hA, hB, hC]

/-- **A negative instance of Definition 5.7(1).**  Under a point mass every pair of events
is conditionally independent, so the `⟸` half of the perfect-map iff would force `chainG`
to d-separate `0` from `2` with nothing conditioned — refuted above.  A client cannot read a
perfect map off a degenerate distribution. -/
example (x : Pt ChainVal) : ¬ IsPerfectMapDAG chainG (Distr.delta x) := fun h =>
  chain_not_dSeparated_empty
    ((h {0} {2} ∅).mpr fun _ _ _ => chain_condIndep_delta x _ _ _)

/-! ### Proposition 6.6 on a *proper* open piece of `Δ^⊗(Ω)` -/

/-- The client's all-ones point, the single coordinate reading the open condition below
constrains. -/
def allOnes : Pt Bits := fun _ => true

/-- A **proper** open piece of `Δ^⊗(Ω)`: the factorizing distributions that put more than
half their mass on `allOnes`.  Because it constrains one mass only, `abs_sub_le_euclDist`
is the whole of the metric input its openness needs. -/
def heavyOnOnes : Set (Distr (Pt Bits)) := {P | Factorizes P ∧ 1 / 2 < P.mass allOnes}

private lemma heavyOnOnes_subset : heavyOnOnes ⊆ factorizing Bits := fun _ hP => hP.1

private lemma heavyOnOnes_nonempty : heavyOnOnes.Nonempty :=
  ⟨Distr.delta allOnes, factorizes_delta allOnes, by
    rw [Distr.delta_mass, if_pos rfl]; norm_num⟩

private lemma heavyOnOnes_open : ∀ Q ∈ heavyOnOnes, ∃ ε > (0 : ℝ),
    ∀ Q' ∈ factorizing Bits, Distr.euclDist Q Q' < ε → Q' ∈ heavyOnOnes := by
  rintro Q ⟨-, hQ⟩
  refine ⟨Q.mass allOnes - 1 / 2, by linarith, fun Q' hQ' hd => ⟨hQ', ?_⟩⟩
  have hb := (le_abs_self (Q.mass allOnes - Q'.mass allOnes)).trans
    (Distr.abs_sub_le_euclDist Q Q' allOnes)
  linarith

/-- **The piece is genuinely proper.**  The point mass at the all-zeros point factorizes but
misses it, so the independence hypothesis fed to `structIndepGiven_of_open` below is
assumed of strictly fewer distributions than `Δ^⊗(Ω)` contains. -/
lemma heavyOnOnes_ssubset : heavyOnOnes ⊂ factorizing Bits := by
  refine ⟨heavyOnOnes_subset, fun hsub => ?_⟩
  have hne : allOnes ≠ (fun _ => false : Pt Bits) := fun h => Bool.noConfusion (congrFun h 0)
  have h := (hsub (factorizes_delta (fun _ => false : Pt Bits))).2
  rw [Distr.delta_mass, if_neg hne] at h
  norm_num at h

/-- **Proposition 6.6 where it earns its keep.**  Unlike the specialisation at
`S = Δ^⊗(Ω)` above, the independence hypothesis here is assumed only on `heavyOnOnes`,
which `heavyOnOnes_ssubset` shows is a *proper* subset of `Δ^⊗(Ω)`; strong completeness
still returns the structural statement, and Theorem 6.2 then re-exports it to every
factorizing distribution — including the all-zeros point mass, which is one of the ones the
hypothesis said nothing about.  That gap is exactly what `structIndepGiven_of_open` buys
over `structIndepGiven_of_forall_condIndepVar`. -/
example {α β γ : Type} {X : Pt Bits → α} {Y : Pt Bits → β} {Z : Pt Bits → γ}
    (h : ∀ P ∈ heavyOnOnes, CondIndepVar P X Y Z) :
    StructIndepGiven X Y Z ∧
      CondIndepVar (Distr.delta (fun _ => false : Pt Bits)) X Y Z := by
  have hs := structIndepGiven_of_open heavyOnOnes heavyOnOnes_subset heavyOnOnes_nonempty
    heavyOnOnes_open h
  exact ⟨hs, condIndepVar_of_structIndepGiven hs _ (factorizes_delta _)⟩

end APITests.FactoredSpaces
