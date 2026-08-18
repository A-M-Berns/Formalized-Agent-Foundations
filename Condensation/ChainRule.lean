import Condensation.Model

/-!
# The chain rule for a finite family of joint variables

Every remaining §4 endpoint of `Condensation/Perfect.lean` — Proposition 4.2's second
inequality (4.7)–(4.9), Theorem 4.9 (4.29)–(4.36) and Proposition 4.10 (4.38) — runs on one
piece of machinery the vendored Shannon-information layer does not have: the expansion

```
H(Y_F) = ∑_{A ∈ F} H(Y_A | (Y_C)_{C ≺ A})
```

along a linear order `≺` on a finite index family `F`.  PFR stops at the two- and
three-variable chain rules (`chain_rule`, `chain_rule'`, `chain_rule''`, `cond_chain_rule`,
`cond_chain_rule'`), so the family version is built here, by induction on `F` peeling off
its `≺`-greatest element.

Nothing in this file is a numbered node of the paper: it is the shared substrate the four
§4 proofs consume, deliberately stated over a bare `RVModel J` (not over a latent variable
model) because that is the generality the arguments actually use.

## Contents

* `Condensation.exists_strictTotalOrder_ext` — Szpilrajn for a *strict* order: every partial
  order extends to a strict linear one.  Mathlib's `extend_partialOrder`
  (`Mathlib.Order.Extension.Linear`, imported by `Condensation/Model.lean`) produces a
  reflexive linear order; the chain rule wants the irreflexive form.
* `Condensation.exists_revIncl_strictTotalOrder` — the order of (4.7): a strict linear order
  on `P⁺I` in which **supersets come first** (`C ⊊ B → B ≺ C`).
* `Condensation.exists_revIncl_strictTotalOrder_incomparable_first` — the order of the
  paragraph before (4.29): the same, and additionally every `B` incomparable to a fixed `A`
  precedes `A`.  Built by extending the paper's own partial order `⪯ₚ`.
* `Condensation.pred_subset_incomparable_union_strictAbove` — the converse containment the
  §4 proofs pair those with: everything `r`-below `B` is incomparable to `B` or a strict
  superset of it.  This is (4.35)'s "all its elements that are not strict supersets of `B`
  are inclusion-incomparable to `B`" and the right-hand inclusion of (4.39).
* `RVModel.condEntropy_pair_jointOn` — `H[X | ⟨Y_S, Y_T⟩] = H[X | Y_{S ∪ T}]`, the
  relabelling that lets a pair of joint variables be read as a single one.  Used constantly.
* `RVModel.condEntropy_jointOn_mono` — conditioning on more decreases entropy:
  `S ⊆ T → H[X | Y_T] ≤ H[X | Y_S]`.  This is (4.8).
* `RVModel.condEntropy_jointOn_sdiff` — `H[Y_G | Y_W] = H[Y_{G ∖ W} | Y_W]`, and
  `RVModel.condEntropy_jointOn_above` — `H[Y_⊇A | Y_W] = H[X_A | Y_W]` when `⊋A ⊆ W`: the
  two "drop the coordinates already given" identities §4 runs on.
* `RVModel.condEntropy_jointOn_eq_sum`, `RVModel.entropy_jointOn_eq_sum` — the chain rule
  itself, conditioned and unconditioned.
* `RVModel.entropy_jointOn_le_sum`, `RVModel.entropy_jointOn_eq_sum_of_iIndepFun` and
  `RVModel.iIndepFun_of_entropy_jointOn_eq_sum` — joint independence of a finite family is
  equivalent to the entropy of the joint variable being the sum of the individual
  entropies.  Theorem 4.9's (A1) ⟺ (A3) needs *both* directions; PFR has only the forward
  one, and only for a `Fin m`-indexed family.  (4.23)–(4.28).
* `RVModel.condEntropy_jointOn_eq_of_condIndepFun` and its converse
  `RVModel.condIndepFun_of_condEntropy_jointOn_eq` — the bridge between Definition 4.8's
  conditional independence and the termwise entropy equalities (4.30)/(4.32), (4.35),
  (4.40).  Both are stated in the "sandwich" form the proofs need: a conditioning family
  `W` squeezed between `S₂` and `S₁ ∪ S₂`.
-/

universe u v w

namespace Condensation

open MeasureTheory ProbabilityTheory

/-! ## Strict linear extensions -/

section Order

variable {α : Type*}

/-- **Szpilrajn, strict form.**  A partial order `p` extends to a *strict* linear order `r`,
in the sense that `p a b` and `a ≠ b` together imply `r a b`.

Mathlib's `extend_partialOrder` produces a reflexive linear order; the chain rule below
wants an irreflexive one, because its induction peels off a greatest element and needs
`{C | r C A}` to exclude `A` itself. -/
lemma exists_strictTotalOrder_ext (p : α → α → Prop) [IsPartialOrder α p] :
    ∃ r : α → α → Prop, IsStrictTotalOrder α r ∧ ∀ a b, p a b → a ≠ b → r a b := by
  obtain ⟨s, hs, hps⟩ := extend_partialOrder p
  haveI : IsLinearOrder α s := hs
  have htrans : ∀ a b c : α, (s a b ∧ a ≠ b) → (s b c ∧ b ≠ c) → (s a c ∧ a ≠ c) := by
    rintro a b c ⟨hab, hne⟩ ⟨hbc, -⟩
    refine ⟨trans_of s hab hbc, ?_⟩
    rintro rfl
    exact hne (antisymm_of s hab hbc)
  have htri : ∀ a b : α, ¬ (s a b ∧ a ≠ b) → ¬ (s b a ∧ b ≠ a) → a = b := by
    intro a b h1 h2
    by_contra hne
    rcases total_of s a b with h | h
    · exact h1 ⟨h, hne⟩
    · exact h2 ⟨h, fun h' => hne h'.symm⟩
  haveI : Std.Irrefl (fun a b : α => s a b ∧ a ≠ b) := ⟨fun _ h => h.2 rfl⟩
  haveI : IsTrans α (fun a b : α => s a b ∧ a ≠ b) := ⟨htrans⟩
  haveI : Std.Trichotomous (fun a b : α => s a b ∧ a ≠ b) := ⟨fun {a b} => htri a b⟩
  haveI : IsStrictOrder α (fun a b : α => s a b ∧ a ≠ b) := {}
  haveI : IsStrictTotalOrder α (fun a b : α => s a b ∧ a ≠ b) := {}
  exact ⟨fun a b => s a b ∧ a ≠ b, inferInstance, fun a b hab hne => ⟨hps a b hab, hne⟩⟩

end Order

section PPlusOrder

variable {I : Type*}

/-- **The order of (4.7).**  The family `P⁺I` (or any subfamily of it) carries a strict
linear order in which a strict *superset* comes first: `C ⊊ B → B ≺ C`.  This is the paper's
"there exists a total order `⪯` such that whenever `B₁ ⊇ B₂` we have `B₁ ⪯ B₂`", got by
extending reverse inclusion. -/
lemma exists_revIncl_strictTotalOrder :
    ∃ r : PPlus I → PPlus I → Prop, IsStrictTotalOrder (PPlus I) r ∧
      ∀ B C : PPlus I, C < B → r B C := by
  haveI : IsPartialOrder (PPlus I) (fun B C : PPlus I => C ≤ B) :=
    { refl := fun a => le_refl a
      trans := fun _ _ _ hab hbc => le_trans hbc hab
      antisymm := fun _ _ hab hba => le_antisymm hba hab }
  obtain ⟨r, hr, hpr⟩ := exists_strictTotalOrder_ext (fun B C : PPlus I => C ≤ B)
  exact ⟨r, hr, fun B C h => hpr B C h.le h.ne'⟩

/-- **The order of the paragraph before (4.29).**  For a fixed `A ∈ P⁺I` there is a strict
linear order on `P⁺I` which puts strict supersets first *and* puts every element
incomparable to `A` before `A`.

The construction is the paper's: extend the partial order `⪯ₚ` given by "`B ⊇ C`, or `B` is
incomparable to `A` and `A ⊇ C`".  That this is a partial order is where the two clauses
interact — antisymmetry and transitivity both come down to the fact that an element
incomparable to `A` is not `≤ A`. -/
lemma exists_revIncl_strictTotalOrder_incomparable_first (A : PPlus I) :
    ∃ r : PPlus I → PPlus I → Prop, IsStrictTotalOrder (PPlus I) r ∧
      (∀ B C : PPlus I, C < B → r B C) ∧ ∀ B ∈ incomparable A, r B A := by
  classical
  set p : PPlus I → PPlus I → Prop :=
    fun B C => C ≤ B ∨ (B ∈ incomparable A ∧ C ≤ A) with hp
  haveI : IsPartialOrder (PPlus I) p := by
    refine { refl := fun a => Or.inl le_rfl, trans := ?_, antisymm := ?_ }
    · rintro a b c (hba | ⟨ha, hbA⟩) (hcb | ⟨hb, hcA⟩)
      · exact Or.inl (hcb.trans hba)
      · -- `b ≤ a` and `b` incomparable to `A`
        by_cases hAa : A ≤ a
        · exact Or.inl (hcA.trans hAa)
        · refine Or.inr ⟨⟨fun haA => hb.1 (hba.trans haA), hAa⟩, hcA⟩
      · exact Or.inr ⟨ha, hcb.trans hbA⟩
      · exact absurd hbA hb.1
    · rintro a b (hba | ⟨ha, hbA⟩) (hab | ⟨hb, haA⟩)
      · exact le_antisymm hab hba
      · exact absurd (hba.trans haA) hb.1
      · exact absurd (hab.trans hbA) ha.1
      · exact absurd haA ha.1
  obtain ⟨r, hr, hpr⟩ := exists_strictTotalOrder_ext p
  refine ⟨r, hr, fun B C h => hpr B C (Or.inl h.le) h.ne', fun B hB => ?_⟩
  exact hpr B A (Or.inr ⟨hB, le_rfl⟩) (fun h => hB.1 (h ▸ le_rfl))

/-- The other half of the sandwich the §4 proofs need: along a linear order refining reverse
inclusion, **everything strictly preceding `B` is either incomparable to `B` or a strict
superset of it**.  This is the paper's "all its elements that are not strict supersets of
`B` are inclusion-incomparable to `B`" of (4.35), and the right-hand inclusion of (4.39). -/
lemma pred_subset_incomparable_union_strictAbove {r : PPlus I → PPlus I → Prop}
    [IsStrictTotalOrder (PPlus I) r] (hrev : ∀ B C : PPlus I, C < B → r B C) (B : PPlus I)
    {W : Set (PPlus I)} (hW : ∀ C ∈ W, r C B) :
    W ⊆ incomparable B ∪ strictAbove B.toFinset := by
  intro C hC
  have hCB : r C B := hW C hC
  have hne : C ≠ B := by rintro rfl; exact irrefl_of r C hCB
  have hnlt : ¬ C < B := fun h => irrefl_of r C (trans_of r hCB (hrev B C h))
  have hnle : ¬ C ≤ B := fun h => hnlt (lt_of_le_of_ne h hne)
  by_cases hBC : B ≤ C
  · exact Or.inr (PPlus.lt_iff.mp (lt_of_le_of_ne hBC (Ne.symm hne)))
  · exact Or.inl ⟨hnle, hBC⟩

end PPlusOrder

namespace RVModel

variable {J : Type*} [Finite J] (N : RVModel J)

/-! ## Reading a pair of joint variables as one -/

section Relabel

variable {U : Type*} [MeasurableSpace U] [Countable U] [MeasurableSingletonClass U]
  {X : N.Ω → U}

/-- `⟨Y_S, Y_T⟩` and `Y_{S ∪ T}` are the same variable up to an injective relabelling, so
they condition identically.  This is the workhorse that lets the arguments of §4 move
between the paper's `H(Y_A | Y_F, Y_⊋A)` and a single joint variable over `F ∪ ⊋A`. -/
lemma condEntropy_pair_jointOn (hX : Measurable X) (S T : Set J) :
    H[X | ⟨N.jointOn S, N.jointOn T⟩ ; N.P] = H[X | N.jointOn (S ∪ T) ; N.P] := by
  haveI := N.finiteEntropyOf hX
  set f : (∀ B : (S ∪ T : Set J), N.R B) →
      (∀ B : S, N.R B) × (∀ B : T, N.R B) :=
    fun y => (fun B => y ⟨B.1, Or.inl B.2⟩, fun B => y ⟨B.1, Or.inr B.2⟩) with hf
  have hinj : Function.Injective f := by
    intro y y' h
    funext B
    obtain ⟨B, hB⟩ := B
    rcases hB with hB | hB
    · exact congrFun (congrArg Prod.fst h) ⟨B, hB⟩
    · exact congrFun (congrArg Prod.snd h) ⟨B, hB⟩
  have hmeas : Measurable (f ∘ N.jointOn (S ∪ T)) :=
    (N.measurable_jointOn S).prodMk (N.measurable_jointOn T)
  exact ShannonInformation.condEntropy_of_injective' N.P hX
    (N.measurable_jointOn (S ∪ T)) f hinj hmeas

/-- **Conditioning on more decreases entropy** — equation (4.8), in the form the chain-rule
arguments use it: if `S ⊆ T` then `H(X | Y_T) ≤ H(X | Y_S)`. -/
lemma condEntropy_jointOn_mono (hX : Measurable X) {S T : Set J} (h : S ⊆ T) :
    H[X | N.jointOn T ; N.P] ≤ H[X | N.jointOn S ; N.P] := by
  haveI := N.finiteEntropyOf hX
  have hunion : (T \ S) ∪ S = T := by
    ext B
    simp only [Set.mem_union, Set.mem_diff]
    exact ⟨fun hB => hB.elim (·.1) (h ·), fun hB => (em (B ∈ S)).elim Or.inr
      fun hBS => Or.inl ⟨hB, hBS⟩⟩
  calc H[X | N.jointOn T ; N.P]
      = H[X | ⟨N.jointOn (T \ S), N.jointOn S⟩ ; N.P] := by
        rw [N.condEntropy_pair_jointOn hX (T \ S) S, hunion]
    _ ≤ H[X | N.jointOn S ; N.P] :=
        ShannonInformation.entropy_submodular hX (N.measurable_jointOn _)
          (N.measurable_jointOn _)

/-- `H(Y_G | Y_W) = H(Y_{G ∖ W} | Y_W)`: the coordinates of `G` that already lie in `W`
contribute nothing once `Y_W` is given. -/
lemma condEntropy_jointOn_sdiff (G W : Set J) :
    H[N.jointOn G | N.jointOn W ; N.P] = H[N.jointOn (G \ W) | N.jointOn W ; N.P] := by
  classical
  set f : (∀ B : G, N.R B) →
      (∀ B : (G \ W : Set J), N.R B) × (∀ B : (G ∩ W : Set J), N.R B) :=
    fun y => (fun B => y ⟨B.1, B.2.1⟩, fun B => y ⟨B.1, B.2.1⟩) with hf
  have hinj : Function.Injective f := by
    intro y y' h
    funext B
    obtain ⟨B, hB⟩ := B
    by_cases hBW : B ∈ W
    · exact congrFun (congrArg Prod.snd h) ⟨B, hB, hBW⟩
    · exact congrFun (congrArg Prod.fst h) ⟨B, hB, hBW⟩
  have h1 : H[N.jointOn G | N.jointOn W ; N.P] =
      H[⟨N.jointOn (G \ W), N.jointOn (G ∩ W)⟩ | N.jointOn W ; N.P] :=
    (ProbabilityTheory.condEntropy_comp_of_injective (Y := N.jointOn W) N.P
      (N.measurable_jointOn G) f hinj).symm
  have h2 : H[⟨N.jointOn (G \ W), N.jointOn (G ∩ W)⟩ | N.jointOn W ; N.P] =
      H[N.jointOn (G ∩ W) | N.jointOn W ; N.P] +
        H[N.jointOn (G \ W) | ⟨N.jointOn (G ∩ W), N.jointOn W⟩ ; N.P] :=
    ShannonInformation.cond_chain_rule N.P (N.measurable_jointOn _) (N.measurable_jointOn _)
      (N.measurable_jointOn _)
  have h3 : H[N.jointOn (G ∩ W) | N.jointOn W ; N.P] = 0 :=
    Condensation.condEntropy_eq_zero_of_aeFunctionOf (N.measurable_jointOn W)
      (N.measurable_jointOn (G ∩ W))
      (N.aeFunctionOf_jointOn_mono Set.inter_subset_right N.P)
  have h4 : H[N.jointOn (G \ W) | ⟨N.jointOn (G ∩ W), N.jointOn W⟩ ; N.P] =
      H[N.jointOn (G \ W) | N.jointOn W ; N.P] := by
    rw [N.condEntropy_pair_jointOn (N.measurable_jointOn _) (G ∩ W) W,
      Set.union_eq_self_of_subset_left (Set.inter_subset_right : G ∩ W ⊆ W)]
  rw [h1, h2, h3, h4, zero_add]

end Relabel

/-! ## The chain rule for a finite family -/

section Chain

omit [Finite J] in
/-- A finite nonempty set has a `r`-greatest element, for any strict linear order `r`. -/
private lemma exists_greatest {r : J → J → Prop} [IsTrans J r] [IsTrichotomous J r]
    (s : Finset J) : s.Nonempty → ∃ A ∈ s, ∀ C ∈ s, C ≠ A → r C A := by
  classical
  induction s using Finset.induction_on with
  | empty => intro h; simp at h
  | @insert a t ha ih =>
    intro _
    rcases t.eq_empty_or_nonempty with rfl | ht
    · refine ⟨a, Finset.mem_insert_self _ _, fun C hC hne => ?_⟩
      rw [Finset.insert_empty, Finset.mem_singleton] at hC
      exact absurd hC hne
    · obtain ⟨A, hA, hmax⟩ := ih ht
      rcases trichotomous_of r A a with hAa | rfl | haA
      · refine ⟨a, Finset.mem_insert_self _ _, fun C hC hne => ?_⟩
        rcases Finset.mem_insert.mp hC with rfl | hCt
        · exact absurd rfl hne
        · by_cases hCA : C = A
          · exact hCA ▸ hAa
          · exact IsTrans.trans _ _ _ (hmax C hCt hCA) hAa
      · exact absurd hA ha
      · exact ⟨A, Finset.mem_insert_of_mem hA, fun C hC hne => by
          rcases Finset.mem_insert.mp hC with rfl | hCt
          · exact haA
          · exact hmax C hCt hne⟩

variable {r : J → J → Prop} [IsStrictTotalOrder J r]

omit [Finite J] in
/-- Splitting a joint variable at a `r`-greatest index: `{C ∈ s | C ≺ A}` is `s.erase A`. -/
private lemma pred_eq_erase [DecidableEq J] {s : Finset J} {A : J}
    (hmax : ∀ C ∈ s, C ≠ A → r C A) :
    {C | C ∈ s ∧ r C A} = ((s.erase A : Finset J) : Set J) := by
  ext C
  simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_erase]
  constructor
  · rintro ⟨hCs, hCA⟩
    refine ⟨?_, hCs⟩
    rintro rfl
    exact irrefl_of r C hCA
  · rintro ⟨hCA, hCs⟩
    exact ⟨hCs, hmax C hCs hCA⟩

omit [Finite J] in
/-- Erasing the `r`-greatest index does not change the predecessor set of any other. -/
private lemma pred_erase [DecidableEq J] {s : Finset J} {A B : J} (hB : B ∈ s.erase A)
    (hmax : ∀ C ∈ s, C ≠ A → r C A) :
    {C | C ∈ (s.erase A : Finset J) ∧ r C B} = {C | C ∈ s ∧ r C B} := by
  ext C
  simp only [Set.mem_setOf_eq, Finset.mem_erase]
  constructor
  · rintro ⟨⟨-, hCs⟩, hCB⟩
    exact ⟨hCs, hCB⟩
  · rintro ⟨hCs, hCB⟩
    refine ⟨⟨?_, hCs⟩, hCB⟩
    rintro rfl
    obtain ⟨hBA, hBs⟩ := Finset.mem_erase.mp hB
    exact irrefl_of r C (trans_of r hCB (hmax B hBs hBA))

/-- **The chain rule for a finite family, conditioned.**  Along any strict linear order `r`,

`H(Y_s | Z) = ∑_{A ∈ s} H(Y_A | Y_{C ∈ s, C ≺ A}, Z)`.

This is the form equation (4.38) of Proposition 4.10 needs; the unconditioned
`entropy_jointOn_eq_sum` below is (4.9), (4.29) and (4.34). -/
lemma condEntropy_jointOn_eq_sum {V : Type*} [MeasurableSpace V] [Countable V]
    [MeasurableSingletonClass V] {Z : N.Ω → V} (hZ : Measurable Z) (r : J → J → Prop)
    [IsStrictTotalOrder J r] (s : Finset J) :
    H[N.jointOn (↑s : Set J) | Z ; N.P] =
      ∑ A ∈ s, H[N.X A | ⟨N.jointOn {C | C ∈ s ∧ r C A}, Z⟩ ; N.P] := by
  classical
  haveI := N.finiteEntropyOf hZ
  induction s using Finset.strongInductionOn with
  | _ s ih =>
  rcases s.eq_empty_or_nonempty with rfl | hs
  · rw [Finset.sum_empty]
    haveI : IsEmpty ((↑(∅ : Finset J) : Set J) : Type _) :=
      Set.isEmpty_coe_sort.mpr Finset.coe_empty
    have hconst : N.jointOn (↑(∅ : Finset J) : Set J) =
        fun _ => (default : ∀ B : (↑(∅ : Finset J) : Set J), N.R B) :=
      funext fun _ => Subsingleton.elim _ _
    have h0 : H[N.jointOn (↑(∅ : Finset J) : Set J) ; N.P] = 0 := by
      rw [hconst]; exact entropy_const _
    refine le_antisymm ?_ (condEntropy_nonneg _ _ _)
    rw [← h0]
    exact ShannonInformation.condEntropy_le_entropy (N.measurable_jointOn _) hZ
  · obtain ⟨A, hA, hmax⟩ := exists_greatest (r := r) s hs
    have hsub : ∀ {x : J}, x ∈ ((s.erase A : Finset J) : Set J) → x ∈ (↑s : Set J) :=
      fun {x} hx => Finset.mem_of_mem_erase hx
    -- (i) split off the greatest coordinate
    have hrelabel : H[N.jointOn (↑s : Set J) | Z ; N.P] =
        H[⟨N.X A, N.jointOn ((s.erase A : Finset J) : Set J)⟩ | Z ; N.P] := by
      set f : (∀ B : (↑s : Set J), N.R B) →
          N.R A × (∀ B : ((s.erase A : Finset J) : Set J), N.R B) :=
        fun y => (y ⟨A, hA⟩, fun B => y ⟨B.1, hsub B.2⟩) with hf
      have hinj : Function.Injective f := by
        intro y y' h
        funext B
        obtain ⟨B, hB⟩ := B
        by_cases hBA : B = A
        · subst hBA
          have := congrArg Prod.fst h
          simpa [hf] using this
        · have hBe : B ∈ ((s.erase A : Finset J) : Set J) :=
            Finset.mem_erase.mpr ⟨hBA, hB⟩
          exact congrFun (congrArg Prod.snd h) ⟨B, hBe⟩
      exact (ProbabilityTheory.condEntropy_comp_of_injective (Y := Z) N.P
        (N.measurable_jointOn (↑s : Set J)) f hinj).symm
    -- (ii) the two-variable conditional chain rule
    have hchain : H[⟨N.X A, N.jointOn ((s.erase A : Finset J) : Set J)⟩ | Z ; N.P] =
        H[N.jointOn ((s.erase A : Finset J) : Set J) | Z ; N.P] +
          H[N.X A | ⟨N.jointOn ((s.erase A : Finset J) : Set J), Z⟩ ; N.P] :=
      ShannonInformation.cond_chain_rule N.P (N.measurable_X A) (N.measurable_jointOn _) hZ
    -- (iii) the inductive hypothesis, with predecessor sets computed inside `s`
    have hIH : H[N.jointOn ((s.erase A : Finset J) : Set J) | Z ; N.P] =
        ∑ B ∈ s.erase A, H[N.X B | ⟨N.jointOn {C | C ∈ s ∧ r C B}, Z⟩ ; N.P] := by
      rw [ih (s.erase A) (Finset.erase_ssubset hA)]
      refine Finset.sum_congr rfl fun B hB => ?_
      rw [pred_erase (r := r) hB hmax]
    rw [hrelabel, hchain, hIH, ← Finset.add_sum_erase s _ hA,
      pred_eq_erase (r := r) hmax]
    ring

/-- **The chain rule for a finite family** — the paper's `H(Y_F) = ∑ H(Y_B | Y_{C ≺ B})`,
which is (4.9), (4.29) and (4.34). -/
lemma entropy_jointOn_eq_sum (r : J → J → Prop) [IsStrictTotalOrder J r] (s : Finset J) :
    H[N.jointOn (↑s : Set J) ; N.P] =
      ∑ A ∈ s, H[N.X A | N.jointOn {C | C ∈ s ∧ r C A} ; N.P] := by
  classical
  haveI : IsEmpty ((∅ : Set J) : Type _) := Set.isEmpty_coe_sort.mpr rfl
  have hmain := N.condEntropy_jointOn_eq_sum (Z := N.jointOn (∅ : Set J))
    (N.measurable_jointOn _) r s
  rw [Condensation.condEntropy_eq_entropy_of_subsingleton (N.measurable_jointOn _) _] at hmain
  rw [hmain]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [N.condEntropy_pair_jointOn (N.measurable_X A) {C | C ∈ s ∧ r C A} (∅ : Set J),
    Set.union_empty]

end Chain

/-! ## Joint independence and additivity of entropy

The bridge Theorem 4.9 (A1) ⟺ (A3) runs on, in both directions: for a *finite family* of
variables, joint independence is equivalent to the entropy of the joint variable being the
sum of the individual entropies.  Neither direction is available from PFR or Mathlib at
this pin — PFR has `ProbabilityTheory.iIndepFun.entropy_eq_add`, which is the forward
direction only, and only for a `Fin m`-indexed family. -/

section Indep

/-- `H(Y_∅) = 0`: the joint variable over an empty family maps into a subsingleton. -/
private lemma entropy_jointOn_empty : H[N.jointOn (↑(∅ : Finset J) : Set J) ; N.P] = 0 := by
  haveI : IsEmpty ((↑(∅ : Finset J) : Set J) : Type _) :=
    Set.isEmpty_coe_sort.mpr Finset.coe_empty
  have hconst : N.jointOn (↑(∅ : Finset J) : Set J) =
      fun _ => (default : ∀ B : (↑(∅ : Finset J) : Set J), N.R B) :=
    funext fun _ => Subsingleton.elim _ _
  rw [hconst]; exact entropy_const _

/-- Splitting one coordinate off a joint variable: `Y_{insert A s}` is `⟨Y_A, Y_s⟩` up to an
injective relabelling, so the two have the same entropy. -/
private lemma entropy_jointOn_insert [DecidableEq J] (A : J) (s : Finset J) :
    H[N.jointOn (↑(insert A s) : Set J) ; N.P] =
      H[⟨N.X A, N.jointOn (↑s : Set J)⟩ ; N.P] := by
  have hA : A ∈ (↑(insert A s) : Set J) := by simp
  have hsub : ∀ {x : J}, x ∈ (↑s : Set J) → x ∈ (↑(insert A s) : Set J) := by
    intro x hx; simp only [Finset.coe_insert, Set.mem_insert_iff]; exact Or.inr hx
  set f : (∀ B : (↑(insert A s) : Set J), N.R B) →
      N.R A × (∀ B : (↑s : Set J), N.R B) :=
    fun y => (y ⟨A, hA⟩, fun B => y ⟨B.1, hsub B.2⟩) with hf
  have hinj : Function.Injective f := by
    intro y y' h
    funext B
    obtain ⟨B, hB⟩ := B
    rcases Finset.mem_insert.mp (by simpa using hB) with rfl | hBs
    · have := congrArg Prod.fst h
      simpa [hf] using this
    · exact congrFun (congrArg Prod.snd h) ⟨B, by simpa using hBs⟩
  exact (entropy_comp_of_injective N.P (N.measurable_jointOn _) f hinj).symm

/-- Splitting a joint variable at a subfamily: for `s ⊆ t`, `Y_t` is `⟨Y_s, Y_{t \ s}⟩` up to
an injective relabelling. -/
private lemma entropy_jointOn_split [DecidableEq J] {s t : Finset J} (hst : s ⊆ t) :
    H[N.jointOn (↑t : Set J) ; N.P] =
      H[⟨N.jointOn (↑s : Set J), N.jointOn (↑(t \ s) : Set J)⟩ ; N.P] := by
  have h1 : ∀ {x : J}, x ∈ (↑s : Set J) → x ∈ (↑t : Set J) := fun {x} hx => hst hx
  have h2 : ∀ {x : J}, x ∈ (↑(t \ s) : Set J) → x ∈ (↑t : Set J) := by
    intro x hx
    exact (Finset.mem_sdiff.mp (by simpa using hx)).1
  set f : (∀ B : (↑t : Set J), N.R B) →
      (∀ B : (↑s : Set J), N.R B) × (∀ B : (↑(t \ s) : Set J), N.R B) :=
    fun y => (fun B => y ⟨B.1, h1 B.2⟩, fun B => y ⟨B.1, h2 B.2⟩) with hf
  have hinj : Function.Injective f := by
    intro y y' h
    funext B
    obtain ⟨B, hB⟩ := B
    by_cases hBs : B ∈ s
    · exact congrFun (congrArg Prod.fst h) ⟨B, by simpa using hBs⟩
    · exact congrFun (congrArg Prod.snd h) ⟨B, by
        simp only [Finset.coe_sdiff, Set.mem_sdiff, Finset.mem_coe]
        exact ⟨by simpa using hB, hBs⟩⟩
  exact (entropy_comp_of_injective N.P (N.measurable_jointOn _) f hinj).symm

/-- **Subadditivity of entropy for a finite family**: `H(Y_s) ≤ ∑_{B ∈ s} H(Y_B)`.  The
first inequality of the paper's (4.25). -/
lemma entropy_jointOn_le_sum (s : Finset J) :
    H[N.jointOn (↑s : Set J) ; N.P] ≤ ∑ B ∈ s, H[N.X B ; N.P] := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [N.entropy_jointOn_empty, Finset.sum_empty]
  | @insert A t hA ih =>
    rw [N.entropy_jointOn_insert A t, Finset.sum_insert hA]
    exact le_trans (ShannonInformation.entropy_pair_le_add (μ := N.P) (N.measurable_X A)
      (N.measurable_jointOn _)) (by linarith)

/-- **Joint independence gives additivity of entropy**: if the family `(X_B)_{B ∈ J}` is
jointly independent then `H(Y_s) = ∑_{B ∈ s} H(Y_B)` for every finite subfamily `s`.

PFR's `iIndepFun.entropy_eq_add` is the `Fin m`-indexed special case of this; the general
finite index type is what Theorem 4.9's (A2) ⇒ (A1) needs. -/
lemma entropy_jointOn_eq_sum_of_iIndepFun (h : iIndepFun N.X N.P) (s : Finset J) :
    H[N.jointOn (↑s : Set J) ; N.P] = ∑ B ∈ s, H[N.X B ; N.P] := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [N.entropy_jointOn_empty, Finset.sum_empty]
  | @insert A t hA ih =>
    have hdisj : Disjoint ({A} : Finset J) t := by simpa using hA
    have hkey := h.indepFun_finset ({A} : Finset J) t hdisj N.measurable_X
    have hind : IndepFun (N.X A) (N.jointOn (↑t : Set J)) N.P :=
      hkey.comp
        (φ := fun y : (∀ i : ({A} : Finset J), N.R i) =>
          y ⟨A, Finset.mem_singleton_self A⟩)
        (ψ := id) (measurable_pi_apply _) measurable_id
    rw [N.entropy_jointOn_insert A t, Finset.sum_insert hA,
      (ShannonInformation.entropy_pair_eq_add (μ := N.P) (N.measurable_X A)
        (N.measurable_jointOn _)).mpr hind, ih]

/-- **Equation (4.25).**  If additivity holds for a family `t`, it holds for every
subfamily: the squeeze `∑_t = H(Y_t) ≤ H(Y_s) + H(Y_{t \ s}) ≤ ∑_s + ∑_{t \ s} = ∑_t`
forces equality throughout. -/
lemma entropy_jointOn_eq_sum_of_subset {t : Finset J}
    (h : H[N.jointOn (↑t : Set J) ; N.P] = ∑ B ∈ t, H[N.X B ; N.P])
    {s : Finset J} (hs : s ⊆ t) :
    H[N.jointOn (↑s : Set J) ; N.P] = ∑ B ∈ s, H[N.X B ; N.P] := by
  classical
  have hsplit : H[N.jointOn (↑t : Set J) ; N.P] ≤
      H[N.jointOn (↑s : Set J) ; N.P] + H[N.jointOn (↑(t \ s) : Set J) ; N.P] := by
    rw [N.entropy_jointOn_split hs]
    exact ShannonInformation.entropy_pair_le_add (μ := N.P) (N.measurable_jointOn _)
      (N.measurable_jointOn _)
  have h1 := N.entropy_jointOn_le_sum s
  have h2 := N.entropy_jointOn_le_sum (t \ s)
  have hsum : (∑ B ∈ s, H[N.X B ; N.P]) + ∑ B ∈ t \ s, H[N.X B ; N.P] =
      ∑ B ∈ t, H[N.X B ; N.P] := by
    rw [add_comm]; exact Finset.sum_sdiff hs
  linarith

/-- **Equation (4.26)** in its variable form: under the additivity hypothesis, every single
coordinate is independent of the joint variable over any family omitting it. -/
lemma indepFun_X_jointOn_of_entropy_eq [DecidableEq J] {t : Finset J} (ht : ∀ j, j ∈ t)
    (h : H[N.jointOn (↑t : Set J) ; N.P] = ∑ B ∈ t, H[N.X B ; N.P])
    {A : J} {s : Finset J} (hA : A ∉ s) :
    IndepFun (N.X A) (N.jointOn (↑s : Set J)) N.P := by
  refine (ShannonInformation.entropy_pair_eq_add (μ := N.P) (N.measurable_X A)
    (N.measurable_jointOn _)).mp ?_
  rw [← N.entropy_jointOn_insert A s,
    N.entropy_jointOn_eq_sum_of_subset h (fun j _ => ht j),
    N.entropy_jointOn_eq_sum_of_subset h (s := s) (fun j _ => ht j),
    Finset.sum_insert hA]

/-- **Additivity of entropy over the whole family gives joint independence** — the converse
of `entropy_jointOn_eq_sum_of_iIndepFun`, and the paper's (4.23)–(4.26).

The hypothesis is stated at a `Finset` `t` exhausting the index type rather than at
`Finset.univ`, so that no `Fintype J` datum has to be produced to *name* it; a caller with
a `Set`-indexed family passes `famFinset` and `mem_famFinset`. -/
lemma iIndepFun_of_entropy_jointOn_eq_sum {t : Finset J} (ht : ∀ j, j ∈ t)
    (h : H[N.jointOn (↑t : Set J) ; N.P] = ∑ B ∈ t, H[N.X B ; N.P]) :
    iIndepFun N.X N.P := by
  classical
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S
  induction S using Finset.induction_on with
  | empty => intro sets _; simp
  | @insert A T hA ih =>
    intro sets hsets
    have hIH := ih (sets := sets) fun i hi => hsets i (Finset.mem_insert_of_mem hi)
    have hpre : (⋂ i ∈ T, N.X i ⁻¹' sets i) =
        N.jointOn (↑T : Set J) ⁻¹' {y | ∀ i : (↑T : Set J), y i ∈ sets i} := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_setOf_eq, RVModel.jointOn_apply]
      exact ⟨fun hω i => hω i.1 (by simp), fun hω i hi => hω ⟨i, by simpa using hi⟩⟩
    have hmeasset : MeasurableSet {y : ∀ i : (↑T : Set J), N.R i |
        ∀ i : (↑T : Set J), y i ∈ sets i} := by
      have hpi : {y : ∀ i : (↑T : Set J), N.R i | ∀ i : (↑T : Set J), y i ∈ sets i} =
          Set.univ.pi fun i : (↑T : Set J) => sets i := by
        ext y; simp
      rw [hpi]
      exact MeasurableSet.univ_pi fun i => hsets i.1
        (Finset.mem_insert_of_mem (by simp))
    have hind := N.indepFun_X_jointOn_of_entropy_eq ht h (A := A) (s := T) hA
    have hmul := hind.measure_inter_preimage_eq_mul (sets A)
      {y | ∀ i : (↑T : Set J), y i ∈ sets i} (hsets A (Finset.mem_insert_self A T)) hmeasset
    rw [Finset.set_biInter_insert, Finset.prod_insert hA, hpre, hmul, ← hpre, hIH]

end Indep

/-! ## Conditional independence as a termwise entropy equality -/

section CondIndep

variable {U : Type*} [MeasurableSpace U] [Countable U] [MeasurableSingletonClass U]
  {X : N.Ω → U}

/-- **Conditional independence collapses a sandwiched conditioning family.**  If `X` is
conditionally independent of `Y_{S₁}` given `Y_{S₂}`, then conditioning on any family `W`
between `S₂` and `S₁ ∪ S₂` gives the same conditional entropy as conditioning on `S₂`.

This is (4.30)/(4.32), (4.35) and (4.40): the paper's "`S_A ⊆ F ∪ {B ≺ A} ⊆ I_A ∪ S_A`, so
`H(Y_A | Y_F, Y_{B ≺ A}) = H(Y_A | Y_⊋A)`". -/
lemma condEntropy_jointOn_eq_of_condIndepFun (hX : Measurable X) {S₁ S₂ W : Set J}
    (hind : CondIndepFun X (N.jointOn S₁) (N.jointOn S₂) N.P)
    (h₂ : S₂ ⊆ W) (hW : W ⊆ S₁ ∪ S₂) :
    H[X | N.jointOn W ; N.P] = H[X | N.jointOn S₂ ; N.P] := by
  haveI := N.finiteEntropyOf hX
  have hzero : I[X : N.jointOn S₁ | N.jointOn S₂ ; N.P] = 0 :=
    (ShannonInformation.condMutualInfo_eq_zero hX (N.measurable_jointOn _)
      (N.measurable_jointOn _)).mpr hind
  rw [ShannonInformation.condMutualInfo_eq' hX (N.measurable_jointOn _)
    (N.measurable_jointOn _) N.P, N.condEntropy_pair_jointOn hX S₁ S₂] at hzero
  have h1 : H[X | N.jointOn W ; N.P] ≤ H[X | N.jointOn S₂ ; N.P] :=
    N.condEntropy_jointOn_mono hX h₂
  have h2 : H[X | N.jointOn (S₁ ∪ S₂) ; N.P] ≤ H[X | N.jointOn W ; N.P] :=
    N.condEntropy_jointOn_mono hX hW
  linarith

/-- The converse of `condEntropy_jointOn_eq_of_condIndepFun`, in the shape (4.30) ⇒ (4.32)
needs it: if conditioning on a family `W` that *contains* `S₁ ∪ S₂` already gives the same
conditional entropy as conditioning on `S₂` alone, then `X` and `Y_{S₁}` are conditionally
independent given `Y_{S₂}`. -/
lemma condIndepFun_of_condEntropy_jointOn_eq (hX : Measurable X) {S₁ S₂ W : Set J}
    (hW : S₁ ∪ S₂ ⊆ W)
    (heq : H[X | N.jointOn W ; N.P] = H[X | N.jointOn S₂ ; N.P]) :
    CondIndepFun X (N.jointOn S₁) (N.jointOn S₂) N.P := by
  haveI := N.finiteEntropyOf hX
  refine (ShannonInformation.condMutualInfo_eq_zero hX (N.measurable_jointOn _)
    (N.measurable_jointOn _)).mp ?_
  rw [ShannonInformation.condMutualInfo_eq' hX (N.measurable_jointOn _)
    (N.measurable_jointOn _) N.P, N.condEntropy_pair_jointOn hX S₁ S₂]
  have h1 : H[X | N.jointOn W ; N.P] ≤ H[X | N.jointOn (S₁ ∪ S₂) ; N.P] :=
    N.condEntropy_jointOn_mono hX hW
  have h2 : H[X | N.jointOn (S₁ ∪ S₂) ; N.P] ≤ H[X | N.jointOn S₂ ; N.P] :=
    N.condEntropy_jointOn_mono hX Set.subset_union_right
  linarith

end CondIndep

/-! ## The inclusion families of `P⁺I`

One `PPlus`-specific splitting that both Theorem 4.9 and Proposition 4.10 walk: `Y_⊇A`
is `⟨Y_A, Y_⊋A⟩` up to relabelling, so conditioning on anything that already contains
`⊋A` collapses it to `Y_A`. -/

section PPlusJoint

variable {I : Type*} [Finite I]

/-- `H(Y_⊇A | Y_W) = H(Y_A | Y_W)` whenever `W` already contains `⊋A`: the joint variable
over `⊇A` splits as `⟨Y_A, Y_⊋A⟩` and the second half is a function of `Y_W`. -/
lemma condEntropy_jointOn_above (N : RVModel (PPlus I)) (A : PPlus I)
    {W : Set (PPlus I)} (hW : strictAbove A.toFinset ⊆ W) :
    H[N.jointOn (above A.toFinset) | N.jointOn W ; N.P] = H[N.X A | N.jointOn W ; N.P] := by
  classical
  have hA : A ∈ above A.toFinset := Finset.Subset.refl _
  set f : (∀ B : above A.toFinset, N.R B) →
      N.R A × (∀ B : strictAbove A.toFinset, N.R B) :=
    fun y => (y ⟨A, hA⟩, fun B => y ⟨B.1, strictAbove_subset_above _ B.2⟩) with hf
  have hinj : Function.Injective f := by
    intro y y' h
    funext B
    obtain ⟨B, hB⟩ := B
    by_cases hBA : B = A
    · subst hBA
      have := congrArg Prod.fst h
      simpa [hf] using this
    · have hlt : A < B := lt_of_le_of_ne (PPlus.le_iff.mpr hB) (fun hc => hBA hc.symm)
      exact congrFun (congrArg Prod.snd h) ⟨B, PPlus.lt_iff.mp hlt⟩
  have h1 : H[N.jointOn (above A.toFinset) | N.jointOn W ; N.P] =
      H[⟨N.X A, N.jointOn (strictAbove A.toFinset)⟩ | N.jointOn W ; N.P] :=
    (ProbabilityTheory.condEntropy_comp_of_injective (Y := N.jointOn W) N.P
      (N.measurable_jointOn _) f hinj).symm
  have h2 : H[⟨N.X A, N.jointOn (strictAbove A.toFinset)⟩ | N.jointOn W ; N.P] =
      H[N.jointOn (strictAbove A.toFinset) | N.jointOn W ; N.P] +
        H[N.X A | ⟨N.jointOn (strictAbove A.toFinset), N.jointOn W⟩ ; N.P] :=
    ShannonInformation.cond_chain_rule N.P (N.measurable_X A) (N.measurable_jointOn _)
      (N.measurable_jointOn _)
  have h3 : H[N.jointOn (strictAbove A.toFinset) | N.jointOn W ; N.P] = 0 :=
    Condensation.condEntropy_eq_zero_of_aeFunctionOf (N.measurable_jointOn W)
      (N.measurable_jointOn _) (N.aeFunctionOf_jointOn_mono hW N.P)
  have h4 : H[N.X A | ⟨N.jointOn (strictAbove A.toFinset), N.jointOn W⟩ ; N.P] =
      H[N.X A | N.jointOn W ; N.P] := by
    rw [N.condEntropy_pair_jointOn (N.measurable_X A) (strictAbove A.toFinset) W,
      Set.union_eq_self_of_subset_left hW]
  rw [h1, h2, h3, h4, zero_add]

/-- `Y_F` of Definition 3.4 at a jointly independent family: `H(Y_F) = ∑_{B ∈ F} H(Y_B)`.
This is the right-hand equality of (4.11).

The `famFinset` restatement of `RVModel.entropy_jointOn_eq_sum_of_iIndepFun`, which is
indexed by a `Finset` because that is the shape the induction runs on.  `Condensation.famFinset`
is **not** generic in the index type — it is declared inside `LatentModel`'s score section
and takes a `Set (PPlus I)` — so this is the `P⁺I` instance clients actually rewrite with. -/
lemma entropy_jointOn_eq_sum_famFinset (N : RVModel (PPlus I))
    (h : iIndepFun N.X N.P) (F : Set (PPlus I)) :
    H[N.jointOn F ; N.P] = ∑ B ∈ famFinset F, H[N.X B ; N.P] := by
  have hcoe : ((famFinset F : Finset (PPlus I)) : Set (PPlus I)) = F := by ext B; simp
  have h0 := N.entropy_jointOn_eq_sum_of_iIndepFun h (famFinset F)
  rw [hcoe] at h0
  exact h0

end PPlusJoint

end RVModel

end Condensation
