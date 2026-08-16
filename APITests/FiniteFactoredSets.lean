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

/-- Anything a set of factors generates, a larger set generates, and coarsening the
partition preserves it — Proposition 11 clauses 5 and 1 chained. -/
example {S : Type u} (F : FactoredSet S) {C D : Set (Setoid S)} {X Y : Setoid S}
    (hCD : C ⊆ D) (hXY : X ≤ Y) (h : F.Generates C X) : F.Generates D Y :=
  (F.generates_spec D D Y X).1 hXY ((F.generates_spec C D X X).2.2.2.2.1 hCD h)

/-- The history of a common coarsening is contained in either history: Proposition 13
clause 1 read through Mathlib's `⊓`. -/
example {S : Type u} (F : FactoredSet S) [Finite F.B] (X Y : Setoid S) :
    F.history X ⊆ F.history (X ⊓ Y) :=
  (F.history_spec X (X ⊓ Y)).1 inf_le_left

/-- Time is a preorder: reflexive and transitive (Proposition 18), so `Before` supports
`calc`-style chaining. -/
example {S : Type u} (F : FactoredSet S) [Finite F.B] (X Y Z W : Setoid S)
    (h₁ : F.Before X Y) (h₂ : F.Before Y Z) (h₃ : F.Before Z W) : F.Before X W :=
  (F.before_spec X Z W).2.1 ((F.before_spec X Y Z).2.1 h₁ h₂) h₃

/-- Orthogonality is inherited backwards in time: if `X ≤^F Y` and `Y ⊥ Z` then `X ⊥ Z`
(Proposition 17's forward direction), and hence `Entangled X Z → Entangled Y Z`. -/
example {S : Type u} (F : FactoredSet S) [Finite F.B] (X Y Z : Setoid S)
    (hXY : F.Before X Y) (h : F.Entangled X Z) : F.Entangled Y Z :=
  fun hYZ => h ((F.before_iff_forall_orthogonal X Y).1 hXY Z hYZ)

/-- A strictly-earlier partition is orthogonal to everything the later one is. -/
example {S : Type u} (F : FactoredSet S) [Finite F.B] (X Y Z : Setoid S)
    (hXY : F.StrictlyBefore X Y) (h : F.Orthogonal Y Z) : F.Orthogonal X Z :=
  (F.before_iff_forall_orthogonal X Y).1 hXY.before Z h

/-- Orthogonality of two partitions transports to their common coarsenings with a third
partition's factors held fixed: Proposition 15 clauses 2 and 3 composed. -/
example {S : Type u} (F : FactoredSet S) [Finite F.B] (X X' Y Z : Setoid S)
    (h : F.Orthogonal X Z) (h' : F.Orthogonal X' Z) (hY : X ⊓ X' ≤ Y) : F.Orthogonal Y Z :=
  (F.orthogonal_spec (X ⊓ X') Y Z).2.1 ((F.orthogonal_spec X X' Z).2.2.1 h h') hY

/-- History computes through Proposition 12: a set of factors generating `X` bounds the
history from above, and the history itself generates. -/
example {S : Type u} (F : FactoredSet S) [Finite F.B] {C : Set (Setoid S)} {X : Setoid S}
    (hC : C ⊆ F.B) (h : F.Generates C X) :
    F.history X ⊆ C ∧ F.Generates (F.history X) X :=
  ⟨(F.history_isLeast X).2 ⟨hC, h⟩, (F.history_isLeast X).1.2⟩

/-- Proposition 16 as a client uses it: a set of factors that pins down `Y` pins down
everything before `Y`. -/
example {S : Type u} (F : FactoredSet S) [Finite F.B] {C : Set (Setoid S)} {X Y : Setoid S}
    (hC : C ⊆ F.B) (hXY : F.Before X Y) (hY : commonRefinement C ≤ Y) :
    commonRefinement C ≤ X :=
  (F.before_iff_forall_sInf X Y).1 hXY C hC hY

/-- On the client factored set: the single factor is its own history and is strictly
after `⊤`, so `⊤ ⊥ ⊥` while `⊥` is entangled with itself. -/
example : clientFS.Orthogonal ⊤ ⊥ ∧ clientFS.Entangled ⊥ ⊥ := by
  have htop : clientFS.history ⊤ = ∅ := (clientFS.history_spec ⊤ ⊤).2.2.1.2 rfl
  refine ⟨?_, ?_⟩
  · rw [orthogonal_def, htop, Set.empty_inter]
  · intro h
    have hbt : (⊥ : Setoid Bool) = ⊤ := (clientFS.orthogonal_spec ⊥ ⊥ ⊥).2.2.2.1 h
    have hrel : (⊥ : Setoid Bool) true false := by rw [hbt]; trivial
    exact Bool.noConfusion hrel

end APITests.FiniteFactoredSets
