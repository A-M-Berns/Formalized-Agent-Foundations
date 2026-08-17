import FiniteFactoredSets.API

/-! Client-style smoke tests for the Finite Factored Sets API.  These import only
`FiniteFactoredSets.API`, build their own tiny factored set, and combine endpoints to
prove facts a downstream project would want — none of them restates a paper node. -/

namespace APITests.FiniteFactoredSets

open _root_.FiniteFactoredSets _root_.FiniteFactoredSets.FactoredSet
open scoped Classical

universe u

/-! ### A client factored set, built without the paper's example fixtures -/

/-- The discrete factorization of a two-point client type. -/
def clientBasis : Set (Setoid Bool) := {⊥}

lemma clientBasis_isFactorization : IsFactorization clientBasis :=
  isFactorization_singleton_bot_iff.2 fun h => Bool.noConfusion (h.2.elim true false)

/-- A client's factored set: `Bool` with its discrete factorization. -/
def clientFS : FactoredSet Bool := ⟨clientBasis, clientBasis_isFactorization⟩

/-- Its basis is finite by instance search alone. -/
example : Finite clientFS.B := inferInstance

/-- Proposition 5, applied: `Bool` is not one-element, so `{⊥}` is its trivial factorization. -/
example : IsTrivialFactorization clientBasis :=
  (existsUnique_trivialFactorization Bool).2.1 (by simp)

/-- Proposition 8, applied to a client type of prime cardinality: every factorization of
`Fin 3` is trivial. -/
example (B : Set (Setoid (Fin 3))) (hB : IsFactorization B) : IsTrivialFactorization B :=
  isTrivialFactorization_of_isFactorization
    (Or.inr (Or.inr ⟨3, Nat.prime_three, by simp⟩)) hB

/-- Propositions 7 and 9 composed with `size`/`dim` unfolding: a factored set of size `4`
has dimension at most `2`, and its factors' block counts multiply to `4`. -/
example {S : Type u} (F : FactoredSet S) (h : F.size = ((4 : ℕ) : Cardinal)) :
    F.dim ≤ 2 ∧ Cardinal.prod (fun b : F.B => Cardinal.mk (Quotient (b : Setoid S))) = 4 := by
  refine ⟨?_, ?_⟩
  · have := F.dim_spec.2.2.2 [2, 2] (by decide) (by decide) (by simpa using h)
    simpa using this.2
  · rw [← F.size_eq_prod, h]; norm_num

/-! ### Generation, history, orthogonality, time — composed, not restated -/

/-- Proposition 10 used to move between two of its clauses that never mention `Generates`,
and the result handed to Proposition 12: a set of factors whose setwise chimera stays
inside each block of `X` (clause 3) already contains `h^F(X)`.  `TFAE.out` needs an
explicitly typed `have` — its autoparams do not elaborate in term position. -/
example {S : Type u} (F : FactoredSet S) [Finite F.B] {C : Set (Setoid S)} (hC : C ⊆ F.B)
    (X : Setoid S) (h : ∀ x ∈ X.classes, F.chimeraImage C x Set.univ ⊆ x) :
    F.history X ⊆ C := by
  have h7 : commonRefinement C ≤ X := ((F.generates_tfae hC X).out 2 6).1 h
  exact (F.le_iff_history_subset hC X).1 h7

/-- The history of a common *refinement* contains each history: `X ⊓ Y` is the paper's
`X ∨_S Y` (`dd:order-flip`), so Proposition 13 clause 1 applied at `X ⊓ Y ≤ X` puts
`h^F(X)` inside `h^F(X ⊓ Y)`.  (The inclusion does *not* run the other way — by clause 2,
`h^F(X ⊓ Y)` is the *union* `h^F(X) ∪ h^F(Y)`.) -/
example {S : Type u} (F : FactoredSet S) [Finite F.B] (X Y : Setoid S) :
    F.history X ⊆ F.history (X ⊓ Y) :=
  (F.history_spec X (X ⊓ Y)).1 inf_le_left

/-- Time is a preorder: reflexive and transitive (Proposition 18), so `Before` supports
`calc`-style chaining. -/
example {S : Type u} (F : FactoredSet S) [Finite F.B] (X Y Z W : Setoid S)
    (h₁ : F.Before X Y) (h₂ : F.Before Y Z) (h₃ : F.Before Z W) : F.Before X W :=
  (F.before_spec X Z W).2.1 ((F.before_spec X Y Z).2.1 h₁ h₂) h₃

/-- A self-entangled partition is strictly after `Ind_S`: Proposition 18 clause 3 gives
`⊤ ≤^F X`, and the inclusion is proper because otherwise Proposition 13 clause 3 would
make `X = ⊤`, which Proposition 15 clause 4 (read through `entangled_iff`) forbids. -/
example {S : Type u} (F : FactoredSet S) [Finite F.B] (X : Setoid S) (h : F.Entangled X X) :
    F.StrictlyBefore ⊤ X := by
  rw [F.strictlyBefore_def]
  refine ⟨(F.before_spec ⊤ X X).2.2.1 le_top, fun hall => (F.entangled_iff X X).1 h ?_⟩
  rw [(F.history_spec (⊤ : Setoid S) ⊤).2.2.1.2 rfl] at hall
  exact (F.orthogonal_spec X X X).2.2.2.2 ((F.history_spec X X).2.2.1.1
    (Set.subset_empty_iff.1 hall))

/-- `Before` is antisymmetric only up to history — the paper stops Proposition 18 at
reflexivity and transitivity for a reason — but mutually-before partitions do have the
same history, hence literally the same orthogonalities (Proposition 17, both ways). -/
example {S : Type u} (F : FactoredSet S) [Finite F.B] (X Y Z : Setoid S)
    (h₁ : F.Before X Y) (h₂ : F.Before Y X) :
    F.history X = F.history Y ∧ (F.Orthogonal X Z ↔ F.Orthogonal Y Z) :=
  ⟨Set.Subset.antisymm ((F.before_def X Y).1 h₁) ((F.before_def Y X).1 h₂),
   ⟨(F.before_iff_forall_orthogonal Y X).1 h₂ Z, (F.before_iff_forall_orthogonal X Y).1 h₁ Z⟩⟩

/-- Orthogonality of two partitions transports to their common coarsenings with a third
partition's factors held fixed: Proposition 15 clauses 2 and 3 composed. -/
example {S : Type u} (F : FactoredSet S) [Finite F.B] (X X' Y Z : Setoid S)
    (h : F.Orthogonal X Z) (h' : F.Orthogonal X' Z) (hY : X ⊓ X' ≤ Y) : F.Orthogonal Y Z :=
  (F.orthogonal_spec (X ⊓ X') Y Z).2.1 ((F.orthogonal_spec X X' Z).2.2.1 h h') hY

/-- The two extreme histories, computed from the API rather than assumed: `Ind_S` has
empty history (Proposition 13 clause 3), and over a nonempty `S` every factor lies in the
history of `Dis_S`, since `h^F(b) = {b}` (clause 4) is pushed into `h^F(⊥)` by clause 1.
Proposition 12 supplies the reverse inclusion. -/
example {S : Type u} (F : FactoredSet S) [Finite F.B] [Nonempty S] :
    F.history (⊤ : Setoid S) = ∅ ∧ F.history (⊥ : Setoid S) = F.B := by
  refine ⟨(F.history_spec (⊤ : Setoid S) ⊤).2.2.1.2 rfl,
    Set.Subset.antisymm (F.history_isLeast (⊥ : Setoid S)).1.1 fun b hb => ?_⟩
  have hb' : F.history b = {b} :=
    (F.history_spec (⊥ : Setoid S) ⊥).2.2.2 ‹Nonempty S› b hb
  exact (F.history_spec b (⊥ : Setoid S)).1 bot_le (hb'.symm ▸ Set.mem_singleton_iff.2 rfl)

/-- A basis split certifying `Y ⊥^F Z` transports backwards along time with no new split
to find: Proposition 16 turns `sInf C ≤ Y` into `sInf C ≤ X` for `X ≤^F Y`, and
Proposition 14 then reads the very same `C` as a certificate of `X ⊥^F Z`. -/
example {S : Type u} (F : FactoredSet S) [Finite F.B] {C : Set (Setoid S)} {X Y Z : Setoid S}
    (hC : C ⊆ F.B) (hY : commonRefinement C ≤ Y) (hZ : commonRefinement (F.B \ C) ≤ Z)
    (hXY : F.Before X Y) : F.Orthogonal X Z :=
  (F.orthogonal_iff_exists X Z).2 ⟨C, hC, (F.before_iff_forall_sInf X Y).1 hXY C hC hY, hZ⟩

/-- On the client factored set: `Ind_S` has empty history (Proposition 13 clause 3), so it
is orthogonal to `Dis_S`, while `Dis_S` — whose history is the one factor — is entangled
with itself (Proposition 15 clause 4). -/
example : clientFS.Orthogonal ⊤ ⊥ ∧ clientFS.Entangled ⊥ ⊥ := by
  have htop : clientFS.history ⊤ = ∅ := (clientFS.history_spec ⊤ ⊤).2.2.1.2 rfl
  refine ⟨?_, ?_⟩
  · rw [orthogonal_def, htop, Set.empty_inter]
  · intro h
    have hbt : (⊥ : Setoid Bool) = ⊤ := (clientFS.orthogonal_spec ⊥ ⊥ ⊥).2.2.2.1 h
    have hrel : (⊥ : Setoid Bool) true false := by rw [hbt]; trivial
    exact Bool.noConfusion hrel

end APITests.FiniteFactoredSets
