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

/-! ### Subpartitions and conditional orthogonality — §4 composed with §3 -/

/-- Theorem 2's contraction and decomposition composed, which is how a client *coarsens*
the conditioning partition: `X ⊥^F W | (Z ∨_S Y)` on its own says nothing about `Z`, but
together with `X ⊥^F Y | Z` contraction bundles the two into `X ⊥^F (Y ∨_S W) | Z` and
decomposition then splits `W` back out over the coarser `Z`.  Neither clause alone gives
this, and the round trip is not the identity — the `Y` premise is what is consumed. -/
example {S : Type u} (F : FactoredSet S) [Finite F.B] (X Y Z W : Setoid S)
    (h₁ : F.OrthogonalGiven X Y Z) (h₂ : F.OrthogonalGiven X W (Z ⊓ Y)) :
    F.OrthogonalGiven X W Z :=
  ((F.orthogonalGiven_semigraphoid X Y Z W).2.1
    ((F.orthogonalGiven_semigraphoid X Y Z W).2.2.2.1 h₁ h₂)).2

/-- Proposition 24 feeds Theorem 2: an *unconditional* `X ⊥^F (Y ∨_S W)` becomes the
conditional `X ⊥^F Y | W` by reading Proposition 24 forwards and then applying weak union,
because conditioning on `Ind_S ∨_S W` is conditioning on `W` (`⊤ ⊓ W = W`).  This is the
composition a downstream project wants: §3 certificates are §4 certificates. -/
example {S : Type u} (F : FactoredSet S) [Finite F.B] (X Y W : Setoid S)
    (h : F.Orthogonal X (Y ⊓ W)) : F.OrthogonalGiven X Y W := by
  have hwu := (F.orthogonalGiven_semigraphoid X Y ⊤ W).2.2.1
    ((F.orthogonal_iff_orthogonalGiven_top X (Y ⊓ W)).1 h)
  rwa [top_inf_eq] at hwu

/-- Proposition 25 composed with Proposition 18 clause 3: `X ⊥^F X | Y` is exactly the
refinement `Y ≤ X` (the paper's `X ≤_S Y`, `dd:order-flip`), which puts `X` before `Y` in
the §3.4 temporal order.  So a self-orthogonality-given-`Y` certificate is a *timing*
certificate, and by Proposition 17 it transports every orthogonality of `Y` onto `X`. -/
example {S : Type u} (F : FactoredSet S) [Finite F.B] (X Y Z : Setoid S)
    (h : F.OrthogonalGiven X X Y) (hYZ : F.Orthogonal Y Z) :
    F.Before X Y ∧ F.Orthogonal X Z := by
  have hb : F.Before X Y := (F.before_spec X Y Y).2.2.1 ((F.orthogonalGiven_self_iff X Y).1 h)
  exact ⟨hb, (F.before_iff_forall_orthogonal X Y).1 hb Z hYZ⟩

/-- A subpartition built the way a client builds one — `ofSetoidOn E Y`, from the client's
own partition `Y : Setoid E` of its own subset `E ⊆ S` — lands in the §4.2 machinery with
no transport: its domain is `E` on the nose, and coarsening it (relation inclusion, the
paper's `≤_E` inverted by `dd:order-flip`) shrinks its history by Proposition 23 clause 1,
which is precisely `BeforeSub`. -/
example {S : Type u} (F : FactoredSet S) [Finite F.B] (E : Set S) (Y Y' : Setoid E)
    (h : Subpartition.ofSetoidOn E Y ≤ Subpartition.ofSetoidOn E Y') :
    (Subpartition.ofSetoidOn E Y').dom = E ∧
      F.BeforeSub (Subpartition.ofSetoidOn E Y') (Subpartition.ofSetoidOn E Y) :=
  ⟨Subpartition.dom_ofSetoidOn E Y',
   (F.beforeSub_def _ _).2
     ((F.historySub_spec (Subpartition.ofSetoidOn E Y') (Subpartition.ofSetoidOn E Y)
        (Subpartition.ofSetoidOn E Y')
        (by rw [Subpartition.dom_ofSetoidOn, Subpartition.dom_ofSetoidOn])).1 h)⟩

/-! ### A two-dimensional client factored set, where conditioning has something to do

`clientFS` is one-dimensional, so every §4.3 fact about it reduces to §3: over a single
factor the only partitions in sight are `Ind_S` and `Dis_S`, and conditioning on `Ind_S` is
Proposition 24 while conditioning on `Dis_S` trivializes Proposition 25.  A test that only
conditions on `Ind_S` therefore exercises nothing §4.3 adds.  The observables below are a
client's own two independent measurements of a two-bit state — the smallest setting in
which conditioning on one *nontrivial* partition rather than another can flip the verdict.

`FiniteFactoredSets.Examples` builds the same factored set as `coordFS`; rebuilding it
here is a deliberate reconstruction, not a missed reuse.  These tests import only the API
boundary, and `Examples` is explicitly outside it (a regression fixture, not a dependency
surface), so putting a two-dimensional factored set together from `IsFactorization` alone
is exactly the work a downstream project has to do. -/

/-- The client's first observable: the first bit. -/
def obsFst : Setoid (Bool × Bool) := Setoid.comap Prod.fst ⊥

/-- The client's second observable: the second bit. -/
def obsSnd : Setoid (Bool × Bool) := Setoid.comap Prod.snd ⊥

/-- The two observables are a basis: reading both bits determines the state. -/
def clientPairBasis : Set (Setoid (Bool × Bool)) := {obsFst, obsSnd}

lemma clientPairBasis_isFactorization : IsFactorization clientPairBasis where
  nontrivial := by
    rintro b (rfl | rfl) ⟨-, h⟩
    · exact Bool.noConfusion (h (true, true) (false, true))
    · exact Bool.noConfusion (h (true, true) (true, false))
  bijective := by
    refine ⟨fun s t h => Prod.ext (Quotient.exact (congrFun h ⟨obsFst, Or.inl rfl⟩))
      (Quotient.exact (congrFun h ⟨obsSnd, Or.inr rfl⟩)), fun y => ?_⟩
    refine ⟨((Quotient.out (y ⟨obsFst, Or.inl rfl⟩)).1,
            (Quotient.out (y ⟨obsSnd, Or.inr rfl⟩)).2), funext fun b => ?_⟩
    obtain ⟨b, hb⟩ := b
    rcases hb with rfl | rfl
    · refine Eq.trans (Quotient.sound (?_ : obsFst _ _)) (Quotient.out_eq _); rfl
    · refine Eq.trans (Quotient.sound (?_ : obsSnd _ _)) (Quotient.out_eq _); rfl

/-- A client's two-dimensional factored set. -/
def clientPairFS : FactoredSet (Bool × Bool) := ⟨clientPairBasis, clientPairBasis_isFactorization⟩

example : Finite clientPairFS.B := inferInstance

/-- Neither observable is the one-block partition, so all three conditioning partitions
used below are genuinely different: `obsFst` and `obsSnd` have two blocks each, `Ind_S` has
one. -/
example : ¬ IsTrivialPartition obsFst ∧ ¬ IsTrivialPartition obsSnd :=
  ⟨clientPairFS.nontrivial_of_mem (Or.inl rfl), clientPairFS.nontrivial_of_mem (Or.inr rfl)⟩

/-- **The conditioning partition changes the verdict.**  Proposition 25 says `X ⊥^F X | Z`
is the refinement `Z ≤ X`, so on a two-dimensional factored set the *same* pair `obsFst`,
`obsFst` is conditionally orthogonal given `obsFst` and conditionally entangled given
`obsSnd` — two partitions with two blocks apiece, neither of them `Ind_S`.  Conditioning on
`Ind_S` fails too, which is the only one of the three Proposition 24 can account for: it is
`¬ obsFst ⊥^F obsFst`, whereas the `obsFst` and `obsSnd` cases are statements §3 cannot
make. -/
example :
    clientPairFS.OrthogonalGiven obsFst obsFst obsFst ∧
      ¬ clientPairFS.OrthogonalGiven obsFst obsFst obsSnd ∧
      ¬ clientPairFS.OrthogonalGiven obsFst obsFst ⊤ := by
  refine ⟨(clientPairFS.orthogonalGiven_self_iff obsFst obsFst).2 le_rfl, fun h => ?_,
    fun h => ?_⟩
  · have hle : obsSnd ≤ obsFst := (clientPairFS.orthogonalGiven_self_iff obsFst obsSnd).1 h
    have hsnd : obsSnd (true, true) (false, true) := rfl
    exact Bool.noConfusion (hle hsnd : obsFst (true, true) (false, true))
  · have hle : (⊤ : Setoid (Bool × Bool)) ≤ obsFst :=
      (clientPairFS.orthogonalGiven_self_iff obsFst ⊤).1 h
    exact Bool.noConfusion (hle trivial : obsFst (true, true) (false, true))

/-- And the `Ind_S` case really is the §3 statement, by Proposition 24 read backwards: an
unconditional `obsFst ⊥^F obsFst` would transport to `obsFst ⊥^F obsFst | Ind_S`, the third
conjunct just refuted, so it fails.  The route — Proposition 24 into Proposition 25 — never
touches Proposition 15's basis characterization. -/
example : ¬ clientPairFS.Orthogonal obsFst obsFst := fun hO =>
  Bool.noConfusion
    ((clientPairFS.orthogonalGiven_self_iff obsFst ⊤).1
      ((clientPairFS.orthogonal_iff_orthogonalGiven_top obsFst obsFst).1 hO)
      trivial : obsFst (true, true) (false, true))

/-! ### §5.1–§5.2: characteristic polynomials through the API

`Finite S` enters here and nowhere earlier, so these examples are the first in this file
to carry it.  The polynomial operations `mono`, `monos` and `poly` are namespace-level and
take no `F` — the paper's superscript is vestigial on them — while `Q` and `irr` are
`FactoredSet` operations; the examples below exercise both spellings. -/

/-- Propositions 26 and 30 rewrite the *same* polynomial two ways, so a client who has
`poly^F_B(E)` in hand can hand it straight to the irreducible factorization without ever
naming `Q^F_E`.  Neither endpoint alone gives this equation. -/
example {S : Type u} [Finite S] (F : FactoredSet S) {E : Set S} (hE : E.Nonempty) :
    poly F.B E = ∏ᶠ C ∈ F.irr E, poly C E := by
  rw [← F.Q_eq_poly E, F.Q_eq_finprod_poly_irr hE]

/-- Proposition 28 read through Proposition 26: the divisors of `poly^F_B(E)` — the form a
client is likelier to be holding than `Q^F_E` — are exactly the real multiples of the
`poly^F_C(E)` for `C ⊆ B`, and the `r` and `C` come back out of the endpoint's existential
for the client to use. -/
example {S : Type u} [Finite S] (F : FactoredSet S) {E : Set S} (hE : E.Nonempty)
    {p : Poly S} (hp : p ∣ poly F.B E) :
    ∃ (r : ℝ) (C : Set (Setoid S)), C ⊆ F.B ∧ p = MvPolynomial.C r * poly C E := by
  rw [← F.Q_eq_poly E] at hp
  exact F.eq_C_mul_poly_of_dvd_Q hE hp

/-- Proposition 27 at `C₁ = ∅`, which is where it stops being a factorization and becomes
an *invariance*: splicing `E₀` against any nonempty `E₁` outside `C` leaves
`poly^F_C(E₀)` unchanged.  The `C₁ = ∅` instance is legal because `∅ ⊆ B` and `∅` is
disjoint from everything, and it is the form a client reaches for when `E₁` is a
"don't care" set. -/
example {S : Type u} [Finite S] (F : FactoredSet S) {C : Set (Setoid S)} (hC : C ⊆ F.B)
    (E₀ E₁ : Set S) (h₁ : E₁.Nonempty) :
    poly C (F.chimeraImage C E₀ E₁) = poly C E₀ := by
  have h := F.poly_union_chimeraImage hC (Set.empty_subset _) disjoint_bot_right E₀ E₁
  rw [Set.union_empty] at h
  rw [h, poly_empty h₁, mul_one]

/-- Proposition 27 where it *is* a factorization: on the client's own two-dimensional
factored set, at the split `C₀ = {obsFst}`, `C₁ = {obsSnd}` — disjoint, both nonempty,
and covering `B` — with two independent subsets `E₀`, `E₁`.  Neither factor is the empty
product, so unlike the `C₁ = ∅` instance above this genuinely splits the whole-basis
polynomial of the spliced set into two, and it is what a client reaches for when the two
observables are measured on different data. -/
example (E₀ E₁ : Set (Bool × Bool)) :
    poly clientPairFS.B (clientPairFS.chimeraImage {obsFst} E₀ E₁)
      = poly ({obsFst} : Set (Setoid (Bool × Bool))) E₀
        * poly ({obsSnd} : Set (Setoid (Bool × Bool))) E₁ := by
  have hne : obsFst ≠ obsSnd := by
    intro hEq
    have hr : obsFst (true, true) (true, false) := rfl
    rw [hEq] at hr
    exact Bool.noConfusion (hr : (true : Bool) = false)
  have hunion : ({obsFst} : Set (Setoid (Bool × Bool))) ∪ {obsSnd} = clientPairFS.B := rfl
  have h := clientPairFS.poly_union_chimeraImage
    (Set.singleton_subset_iff.2 (Or.inl rfl)) (Set.singleton_subset_iff.2 (Or.inr rfl))
    (Set.disjoint_singleton.2 hne) E₀ E₁
  rwa [hunion] at h

/-- Propositions 30 and 31 composed into the sentence a client actually wants: `Q^F_E` is
a product of *irreducibles*, indexed by `Irr^F(E)`.  Neither proposition says that on its
own — 30 gives the product, 31 gives the irreducibility of each factor. -/
example {S : Type u} [Finite S] (F : FactoredSet S) {E : Set S} (hE : E.Nonempty) :
    ∃ f : Set (Setoid S) → Poly S,
      (∀ C ∈ F.irr E, Irreducible (f C)) ∧ F.Q E = ∏ᶠ C ∈ F.irr E, f C :=
  ⟨fun C => poly C E, fun _ hC => F.irreducible_poly_of_mem_irr hE hC,
    F.Q_eq_finprod_poly_irr hE⟩

/-! ### §5.3–§5.5: divisibility, distributions, and the fundamental theorem

The endpoints here are the ones a downstream project actually calls: Theorem 3 is a
*test*, so the examples below run it in both directions — a combinatorial certificate in,
a numerical identity out, and one failing distribution in, a refutation out. -/

/-- Lemma 3's divisibility clause sharpened with §5.1's `Q_ne_zero`: clause 2 says only
that `Q^F_z` divides `Q^F_{x∩z} · Q^F_{y∩z}`, leaving the cofactor anonymous, and clause 3
exhibits one.  Over a *nonempty* block `Q^F_z ≠ 0`, and `Poly S` has no zero divisors, so
the cofactor is unique — it is forced to be `Q^F_{x∩y∩z}`.  That is what a client actually
needs before it can compute with a quotient it obtained from the divisibility, and no
single endpoint says it: `Q_mul_Q_eq_of_orthogonalGiven` supplies the witness and
`Q_ne_zero` supplies the cancellation. -/
example {S : Type u} [Finite S] (F : FactoredSet S) {X Y Z : Setoid S}
    (h : F.OrthogonalGiven X Y Z) {x y z : Set S} (hx : x ∈ X.classes) (hy : y ∈ Y.classes)
    (hz : z ∈ Z.classes) (hzne : z.Nonempty) :
    ∃! c : Poly S, F.Q (x ∩ z) * F.Q (y ∩ z) = F.Q z * c :=
  ⟨F.Q (x ∩ y ∩ z), (F.Q_mul_Q_eq_of_orthogonalGiven h hx hy hz).symm, fun _ hc =>
    (mul_left_cancel₀ (F.Q_ne_zero hzne)
      ((F.Q_mul_Q_eq_of_orthogonalGiven h hx hy hz).trans hc)).symm⟩

/-- Propositions 26 and 32 composed: a client holding `poly^F_B(E)` — the form Proposition
30 factors — reads a probability straight off it, without ever naming `Q^F_E`. -/
example {S : Type u} [Finite S] (F : FactoredSet S) (P : ProbDist S)
    (hP : F.IsDistribution P) (E : Set S) : P E = MvPolynomial.eval P.P (poly F.B E) := by
  rw [← F.Q_eq_poly E]
  exact (F.isDistribution_iff P).1 hP E

/-- Proposition 24 composed with Theorem 3: *unconditional* orthogonality is ordinary
independence in every distribution on `F`.  Conditioning on `Ind_S` collapses the three
intersections and `P(S) = 1`, so the theorem's division-free identity becomes
`P(x) · P(y) = P(x ∩ y)` — the sentence a client with no interest in conditioning wants,
and one neither Proposition 24 nor Theorem 3 states alone. -/
example {S : Type u} [Finite S] [Nonempty S] (F : FactoredSet S) {X Y : Setoid S}
    (h : F.Orthogonal X Y) (P : ProbDist S) (hP : F.IsDistribution P) {x y : Set S}
    (hx : x ∈ X.classes) (hy : y ∈ Y.classes) : P x * P y = P (x ∩ y) := by
  have hz : (Set.univ : Set S) ∈ (⊤ : Setoid S).classes := by
    rw [classes_top ‹Nonempty S›]; rfl
  have hind := (F.orthogonalGiven_iff_forall_isDistribution X Y ⊤).1
    ((F.orthogonal_iff_orthogonalGiven_top X Y).1 h) P hP x hx y hy Set.univ hz
  rwa [Set.inter_univ, Set.inter_univ, Set.inter_univ, P.univ, mul_one] at hind

/-- Theorem 3 used as a **refutation** tool, which is the direction the paper's open-set
argument buys: one distribution and one triple of blocks where the identity fails is a
proof that `X ⊥^F Y | Z` is false.  A client testing a causal hypothesis calls it in this
form, and it needs no computation of histories at all. -/
example {S : Type u} [Finite S] (F : FactoredSet S) (X Y Z : Setoid S) (P : ProbDist S)
    (hP : F.IsDistribution P) {x y z : Set S} (hx : x ∈ X.classes) (hy : y ∈ Y.classes)
    (hz : z ∈ Z.classes) (hne : P (x ∩ z) * P (y ∩ z) ≠ P (x ∩ y ∩ z) * P z) :
    ¬ F.OrthogonalGiven X Y Z :=
  fun h => hne ((F.orthogonalGiven_iff_forall_isDistribution X Y Z).1 h P hP x hx y hy z hz)

/-- Lemma 3 into Theorem 3, skipping orthogonality entirely: a client who has verified the
*polynomial* identity of clause 3 gets probabilistic independence in every distribution on
`F`.  Neither endpoint says this on its own — Lemma 3's clause 3 → clause 1 direction is
the isolated `orthogonalGiven_of_Q_mul_Q_eq`, and Theorem 3 supplies the rest. -/
example {S : Type u} [Finite S] (F : FactoredSet S) (X Y Z : Setoid S)
    (hQ : ∀ x ∈ X.classes, ∀ y ∈ Y.classes, ∀ z ∈ Z.classes,
      F.Q z * F.Q (x ∩ y ∩ z) = F.Q (x ∩ z) * F.Q (y ∩ z))
    (P : ProbDist S) (hP : F.IsDistribution P) {x y z : Set S} (hx : x ∈ X.classes)
    (hy : y ∈ Y.classes) (hz : z ∈ Z.classes) :
    P (x ∩ z) * P (y ∩ z) = P (x ∩ y ∩ z) * P z :=
  (F.orthogonalGiven_iff_forall_isDistribution X Y Z).1
    (F.orthogonalGiven_of_Q_mul_Q_eq hQ) P hP x hx y hy z hz

/-! ### The API's own distribution, and why the theorem is stated without division

Definition 36 is a bare structure, but a downstream project never has to populate it by
hand: the API already supplies the point mass `ProbDist.diracAt`, its unfolding
`diracAt_apply`, and `isDistribution_diracAt` — which makes it a distribution on *every*
factored set of finite dimension, so in particular on the client's own `clientPairFS`,
with `Finite clientPairFS.B` found by instance search and nothing else asked of the
client.  It is the degenerate case worth having at the boundary: a product distribution
whose two marginals are point masses, assigning probability zero to two of the four
blocks.  Any statement of the fundamental theorem phrased with conditional probabilities
would be undefined there; the paper's division-free form is not. -/

/-- Definition 37 for the API's point mass on the client's *own* factored set: the only
thing the client supplies is the instance `Finite clientPairFS.B`, and instance search
supplies that. -/
example : clientPairFS.IsDistribution (ProbDist.diracAt (true, true)) :=
  clientPairFS.isDistribution_diracAt _

/-- The `obsFst` block on which the client's point mass vanishes. -/
def obsFstFalse : Set (Bool × Bool) := {p | p.1 = false}

lemma obsFstFalse_mem_classes : obsFstFalse ∈ obsFst.classes :=
  obsFst.mem_classes (false, false)

/-- Theorem 3 at a block the client's distribution gives probability **zero**.  Proposition
25 makes `obsFst ⊥^F obsFst | obsFst` true, so the theorem's identity has to hold at every
`obsFst` block — including `[·]₁ = false`, where `P(z) = 0` (by `diracAt_apply`) and every
conditional probability is undefined.  That is exactly what the division-free phrasing of
Theorem 3 buys, and it is why the uniform distribution is not the only case worth having at
the boundary. -/
example :
    ProbDist.diracAt (true, true) obsFstFalse = 0 ∧
      ProbDist.diracAt (true, true) (obsFstFalse ∩ obsFstFalse)
            * ProbDist.diracAt (true, true) (obsFstFalse ∩ obsFstFalse)
        = ProbDist.diracAt (true, true) (obsFstFalse ∩ obsFstFalse ∩ obsFstFalse)
            * ProbDist.diracAt (true, true) obsFstFalse := by
  refine ⟨?_, ?_⟩
  · rw [ProbDist.diracAt_apply]
    exact if_neg (fun h => Bool.noConfusion (h : (true : Bool) = false))
  · exact (clientPairFS.orthogonalGiven_iff_forall_isDistribution obsFst obsFst obsFst).1
      ((clientPairFS.orthogonalGiven_self_iff obsFst obsFst).2 le_rfl)
      _ (clientPairFS.isDistribution_diracAt _) _ obsFstFalse_mem_classes _
      obsFstFalse_mem_classes _ obsFstFalse_mem_classes

/-! ### §6: models of a sample space, databases, and inferred time

A downstream project doing temporal inference works one level up from a `FactoredSet`: it
has a sample space `Ω`, builds a `Model Ω` of it — Definition 38's pair `(F, f)` — and
records what it knows in an `OrthDatabase Ω`.  Two things about that boundary are worth a
client's attention, and the examples below exercise both.

First, `Model` bundles `Finite S` as a *field* (`dd:model`), so the finiteness obligation
is discharged once, by instance search, at the point the client constructs its model — and
no §6 statement afterwards carries a `[Finite …]` binder.  Second, Definition 45's
`X <_D Y` quantifies over *models of `D`*, which makes it monotone in the database and
irreflexive whenever the database is consistent; both of those are what a client needs in
order to accumulate observations without accidentally "inferring" everything.  The last
group then consumes §6.2's own worked examples — Propositions 33–36 — through this same
import, since an exported endpoint is only usable if a client can apply it. -/

/-- A client's model of the sample space `Bool`: its own two-dimensional factored set,
observed through the first coordinate.  Definition 38's `Finite S` field is supplied by
instance search and never appears again. -/
def clientModel : Model Bool := ⟨clientPairFS, Prod.fst⟩

/-- Definition 39 read pointwise through `pullback_apply`: the client's finest partition of
the sample space pulls back to the *first coordinate factor* of its own factored set, not
to `Dis_S`.  That is the whole reason §6 is about models rather than about factorizations
of `Ω`. -/
example : clientModel.pullback ⊥ = obsFst :=
  Setoid.ext fun s t => by rw [Model.pullback_apply]; exact Iff.rfl

/-- Definition 43 at the database that asserts nothing: Definition 42 is vacuous there, so
the client's own model witnesses consistency.  This is the base case a client starts from
before adding observations. -/
example : (⟨∅, ∅⟩ : OrthDatabase Bool).Consistent := by
  refine ⟨clientModel, fun _ _ _ => ⟨fun h => ?_, fun h => ?_⟩⟩ <;>
    simp only [OrthDatabase.Orth, OrthDatabase.NotOrth, Set.mem_empty_iff_false] at h

/-- Definition 44 in its general form: a database is `Complete` as soon as `O` and `N`
*jointly* cover the triples, and the split may be by any predicate whatever.  Neither
clause has to be large, and no model is involved — completeness is a statement about the
database alone. -/
example (p : Setoid Bool × Setoid Bool × Setoid Bool → Prop) :
    (⟨{t | p t}, {t | ¬ p t}⟩ : OrthDatabase Bool).Complete :=
  fun X Y Z => Classical.em (p (X, Y, Z))

/-- …which is why completeness neither implies nor is implied by consistency.  Taking the
predicate above to be `True` and `¬ True` at once — `O = N = Set.univ` — gives a database
that is `Complete` and has **no model at all**, since Definition 42's two clauses then
contradict each other on every triple.  (`Examples.completeInconsistentDB` is the
in-library witness of the same fact; a client importing only `FiniteFactoredSets.API`
cannot reach it, so this re-derives it on the client's own sample space.) -/
example : ¬ (⟨Set.univ, Set.univ⟩ : OrthDatabase Bool).Consistent := by
  rintro ⟨M, hM⟩
  exact (hM ⊤ ⊤ ⊤).2 (Set.mem_univ _) ((hM ⊤ ⊤ ⊤).1 (Set.mem_univ _))

/-- **Definition 45 is monotone in the database.**  Extending `O` and `N` can only shrink
the family of models, so an inferred `X <_D Y` survives every extension of `D`.  This is
the fact that lets a client accumulate observations incrementally instead of re-deriving
its temporal conclusions from scratch. -/
example {Ω : Type u} {D D' : OrthDatabase Ω} (hO : D.O ⊆ D'.O) (hN : D.N ⊆ D'.N)
    {X Y : Setoid Ω} (h : D.Before X Y) : D'.Before X Y :=
  fun M hM => h M fun A B C => ⟨fun hA => (hM A B C).1 (hO hA), fun hB => (hM A B C).2 (hN hB)⟩

/-- …and it never holds reflexively on a *consistent* database, because `<^F` is a strict
inclusion of histories in whichever model witnesses consistency.  Read with the
monotonicity above: piling on assertions can only produce `X <_D X` by making `D`
inconsistent, and there Definition 45 holds of everything vacuously.  So "is `D`
consistent?" is the question a client must answer before reading anything off `<_D`. -/
example {Ω : Type u} {D : OrthDatabase Ω} (hD : D.Consistent) (X : Setoid Ω) :
    ¬ D.Before X X := by
  obtain ⟨M, hM⟩ := hD
  exact fun h => lt_irrefl _ (h M hM)

/-! ### §6.2's worked examples, consumed through the API boundary

Propositions 33–36 are exported, so a client does not re-derive them: it *uses* them.  The
four examples below apply each of `Example1.D_consistent`, `Example1.before_X_Y`,
`Example2.D_consistent` and `Example2.before_X_Y_Z` to prove something the paper does not
state, which is the only way to check that those endpoints are usable from outside. -/

/-- Proposition 33 is what makes Proposition 34's inference more than a vacuity: read
together with the irreflexivity above, `Example1.D` infers `X <_D Y` and does *not* infer
`X <_D X`. -/
example : ¬ Example1.D.Before Example1.X Example1.X := by
  obtain ⟨M, hM⟩ := Example1.D_consistent
  exact fun h => lt_irrefl _ (h M hM)

/-- The two together **separate the partitions**: a consistent database never infers
`X <_D X`, so Proposition 34 forces `Example1.X ≠ Example1.Y` with no computation on the
partitions themselves.  This is the shape of client reasoning §6 is for — a temporal
conclusion used to derive a structural one. -/
example : Example1.X ≠ Example1.Y := fun h => by
  obtain ⟨M, hM⟩ := Example1.D_consistent
  have hlt := Example1.before_X_Y M hM
  rw [h] at hlt
  exact lt_irrefl _ hlt

/-- Proposition 35 in the same role for Example 2: `Example2.D` orders `X`, `Y`, `Z` and
still infers nothing about `Z` against itself. -/
example : ¬ Example2.D.Before Example2.Z Example2.Z := by
  obtain ⟨M, hM⟩ := Example2.D_consistent
  exact fun h => lt_irrefl _ (h M hM)

/-- Proposition 36's chain **survives extending the database**, by the monotonicity above.
A client that keeps accumulating observations on top of `Example2.D` never loses
`X <_D Y <_D Z`, which is what makes the worked example a usable starting point rather
than a closed computation. -/
example {D' : OrthDatabase Example2.Ω} (hO : Example2.D.O ⊆ D'.O) (hN : Example2.D.N ⊆ D'.N) :
    D'.Before Example2.X Example2.Y ∧ D'.Before Example2.Y Example2.Z :=
  ⟨fun M hM => Example2.before_X_Y_Z.1 M fun A B C =>
      ⟨fun hA => (hM A B C).1 (hO hA), fun hB => (hM A B C).2 (hN hB)⟩,
    fun M hM => Example2.before_X_Y_Z.2 M fun A B C =>
      ⟨fun hA => (hM A B C).1 (hO hA), fun hB => (hM A B C).2 (hN hB)⟩⟩

/-! ### §7: embedded agency and Conjecture 1

The last two layers are of different kinds and are used differently.  §7.3's five
definitions (46–50) are vocabulary with no theorem attached — the paper states none — so
what a client wants from the API is not an endpoint but the *reductions*: which §3–§4 fact
each §7 definition collapses to at its degenerate arguments, plus a positive and a negative
instance so that neither predicate is silently total.  §7.2's Conjecture 1 is an unproved
`Prop`, so what a client wants is to *assume* it and get something out, and to know that
its finite case is already a theorem.

Two small computations are shared below and factored out, because they are the only place
`historySub_spec` gets projected: a partition restricted to a set on which it makes no
distinction *is* the indiscrete subpartition there, and Proposition 23 clause 4 then makes
its history empty. -/

/-- `Ind_S` restricted to any `E` is `Ind_E`: Definition 22 adds the two domain conjuncts,
and Definition 7's relation contributes nothing. -/
lemma restrict_top_eq_indiscrete {S : Type u} (E : Set S) :
    (Subpartition.ofSetoid (⊤ : Setoid S)).restrict E = Subpartition.indiscrete E :=
  Subpartition.ext fun _ _ => ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, trivial⟩⟩

/-- Proposition 23 clause 4 in the direction §7 consumes: where `Y|E` is `Ind_E`, the
history `h^F(Y|E)` is empty.  Definitions 46 and 50 are both read off this. -/
lemma historySub_restrict_eq_empty {S : Type u} (F : FactoredSet S) [Finite F.B]
    (Y : Setoid S) {E : Set S}
    (hY : (Subpartition.ofSetoid Y).restrict E = Subpartition.indiscrete E) :
    F.historySub ((Subpartition.ofSetoid Y).restrict E) = ∅ :=
  (F.historySub_spec ((Subpartition.ofSetoid Y).restrict E)
      ((Subpartition.ofSetoid Y).restrict E) ((Subpartition.ofSetoid Y).restrict E)
      rfl).2.2.2.1.2
    (by rw [Subpartition.dom_restrict_ofSetoid]; exact hY)

/-- `Ind_S` is orthogonal to everything, by Proposition 13 clause 3 read backwards: its
history is empty, so Definition 18's intersection is. -/
lemma orthogonal_top_left {S : Type u} (F : FactoredSet S) [Finite F.B] (Y : Setoid S) :
    F.Orthogonal ⊤ Y := by
  rw [F.orthogonal_def ⊤ Y, (F.history_spec ⊤ Y).2.2.1.2 rfl, Set.empty_inter]

/-- **Definition 46 has a universal corner, and it is `Ind_S`.**  The agent that makes no
distinctions observes *every* event with respect to *every* world model, on every factored
set: the first conjunct is `orthogonal_top_left` and the second is Definition 26 against an
empty history.  Worth knowing before reading an `Observes` hypothesis as informative — it
constrains `A`, and `A = Ind_S` discharges it for free. -/
example {S : Type u} (F : FactoredSet S) [Finite F.B] (W : Setoid S) (E : Set S) :
    F.Observes ⊤ W E := by
  refine ⟨orthogonal_top_left F _, ?_⟩
  rw [F.orthogonalGivenSet_def ⊤ W Eᶜ,
    historySub_restrict_eq_empty F ⊤ (restrict_top_eq_indiscrete Eᶜ), Set.empty_inter]

/-- **Definition 46 at the impossible event is Definition 18.**  With `E = ∅` the auxiliary
partition `X_E` collapses to `Ind_S` — every point agrees on membership in `∅` — and the
conditioning set `S \ E` is all of `S`, where Proposition 24 identifies Definition 26 with
unconditional orthogonality.  So `A` observes `∅` with respect to `W` exactly when
`A ⊥^F W`, and the §7 predicate says nothing new there.  This is the reduction to reach for
before believing an `Observes` fact is about §7 rather than §3. -/
lemma observes_empty_iff {S : Type u} [Nonempty S] (F : FactoredSet S) [Finite F.B]
    (A W : Setoid S) : F.Observes A W ∅ ↔ F.Orthogonal A W := by
  have hev : eventPartition (∅ : Set S) = ⊤ :=
    Setoid.ext fun _ _ => ⟨fun _ => trivial, fun _ => rfl⟩
  have hcl : (⊤ : Setoid S).classes = {Set.univ} := classes_top ‹Nonempty S›
  constructor
  · rintro ⟨-, h2⟩
    refine (F.orthogonal_iff_orthogonalGiven_top A W).2 ?_
    rw [F.orthogonalGiven_def A W ⊤, hcl]
    rintro z rfl
    simpa using h2
  · intro h
    refine ⟨by rw [hev]; exact (F.orthogonal_spec ⊤ A A).1 (orthogonal_top_left F A), ?_⟩
    have h' := (F.orthogonal_iff_orthogonalGiven_top A W).1 h
    rw [F.orthogonalGiven_def A W ⊤, hcl] at h'
    simpa using h' _ rfl

/-- The client's own two observables are orthogonal, by Proposition 14 at `C = {obsFst}`:
reading the first bit and reading the second use disjoint halves of the basis.  The §4.3
examples above are all about *conditional* orthogonality and the one unconditional
statement there is a refutation, so this positive fact is new here. -/
lemma orthogonal_obsFst_obsSnd : clientPairFS.Orthogonal obsFst obsSnd := by
  have hne : obsFst ≠ obsSnd := by
    intro h
    have h2 : obsSnd (true, true) (false, true) := rfl
    rw [← h] at h2
    exact Bool.noConfusion h2
  have hdiff : clientPairFS.B \ {obsFst} = {obsSnd} := by
    ext x
    simp only [show clientPairFS.B = {obsFst, obsSnd} from rfl, Set.mem_sdiff,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    exact ⟨fun h => h.1.resolve_left h.2, fun h => ⟨Or.inr h, fun hx => hne (hx.symm.trans h)⟩⟩
  refine (clientPairFS.orthogonal_iff_exists obsFst obsSnd).2
    ⟨{obsFst}, Set.singleton_subset_iff.2 (Or.inl rfl), ?_, ?_⟩
  · rw [commonRefinement, sInf_singleton]
  · rw [hdiff, commonRefinement, sInf_singleton]

/-- **Definition 46 is neither empty nor total on the client's own factored set.**  Through
the reduction above: `obsFst` observes `∅` with respect to `obsSnd`, while `Dis_S` observes
`∅` with respect to `obsFst` not at all.  The negative half runs Proposition 15's clauses 2
and 4 in series — coarsening `Dis_S` up to `obsFst` would make `obsFst` orthogonal to
itself, hence equal to `Ind_S`, which it is not — so it is a statement about a *factor*,
not the self-orthogonality corner. -/
example : clientPairFS.Observes obsFst obsSnd ∅ ∧ ¬ clientPairFS.Observes ⊥ obsFst ∅ := by
  refine ⟨(observes_empty_iff clientPairFS obsFst obsSnd).2 orthogonal_obsFst_obsSnd,
    fun h => ?_⟩
  have hself : clientPairFS.Orthogonal obsFst obsFst :=
    (clientPairFS.orthogonal_spec ⊥ obsFst obsFst).2.1
      ((observes_empty_iff clientPairFS ⊥ obsFst).1 h) bot_le
  have htop : obsFst = ⊤ := (clientPairFS.orthogonal_spec obsFst obsFst obsFst).2.2.2.1 hself
  have hrel : obsFst (true, true) (false, true) := by rw [htop]; trivial
  exact Bool.noConfusion hrel

/-- **Definition 48 is inhabited, and its cheapest witness is `Ind_S`.**  Proposition 13
clause 3 gives `h^F(Ind_S) = {}`, and Definition 8's common refinement of nothing is `Ind_S`
again (`sInf ∅ = ⊤`), so Definition 48's equation closes.  Read as: an agent that
distinguishes nothing is counterfactable for free. -/
example {S : Type u} (F : FactoredSet S) [Finite F.B] : F.Counterfactable (⊤ : Setoid S) := by
  rw [FactoredSet.Counterfactable, (F.history_spec ⊤ ⊤).2.2.1.2 rfl, commonRefinement,
    sInf_empty]

/-- **Every factor is counterfactable** — the informative positive instance.  Proposition 13
clause 4 computes `h^F(b) = {b}` for `b ∈ B` over a nonempty carrier, and the common
refinement of a single partition is that partition, so Definition 48's equation is an
identity.  Neither endpoint states this. -/
lemma counterfactable_of_mem_basis {S : Type u} [Nonempty S] (F : FactoredSet S) [Finite F.B]
    {b : Setoid S} (hb : b ∈ F.B) : F.Counterfactable b := by
  rw [FactoredSet.Counterfactable, (F.history_spec b b).2.2.2 ‹Nonempty S› b hb,
    commonRefinement, sInf_singleton]

/-- The same on the client's own basis: both of its observables are counterfactable. -/
example : clientPairFS.Counterfactable obsFst ∧ clientPairFS.Counterfactable obsSnd :=
  ⟨counterfactable_of_mem_basis clientPairFS (Or.inl rfl),
    counterfactable_of_mem_basis clientPairFS (Or.inr rfl)⟩

/-- **Definition 50 at `E = S` is Definition 19.**  Restriction to all of `S` is the
identity on subpartitions, and Proposition 22's second half identifies `h^F` on a total
subpartition with §3.2's `h^F`, so conditional time over the whole space is ordinary time.
The reduction to apply before reading a `BeforeGivenSet` fact as conditional. -/
lemma beforeGivenSet_univ_iff {S : Type u} (F : FactoredSet S) [Finite F.B] (X Y : Setoid S) :
    F.BeforeGivenSet X Y Set.univ ↔ F.Before X Y := by
  rw [FactoredSet.BeforeGivenSet, Subpartition.restrict_univ, Subpartition.restrict_univ,
    F.historySub_isLeast_and_eq_history.2 X, F.historySub_isLeast_and_eq_history.2 Y,
    F.before_def X Y]

/-- **Definition 50 is neither empty nor total, at `E = S` on the client's factored set.**
`Ind_S` is before `obsFst` given `S` and `obsFst` is not before `Ind_S` given `S`: through
the reduction above that is `{} ⊆ {obsFst}` against `{obsFst} ⊆ {}`, with the two histories
computed by Proposition 13 clauses 3 and 4.  So conditional time is a genuine ordering here
and not the total relation. -/
example : clientPairFS.BeforeGivenSet ⊤ obsFst Set.univ ∧
    ¬ clientPairFS.BeforeGivenSet obsFst ⊤ Set.univ := by
  have htop : clientPairFS.history ⊤ = ∅ := (clientPairFS.history_spec ⊤ ⊤).2.2.1.2 rfl
  have hfst : clientPairFS.history obsFst = {obsFst} :=
    (clientPairFS.history_spec obsFst obsFst).2.2.2 inferInstance obsFst (Or.inl rfl)
  refine ⟨(beforeGivenSet_univ_iff clientPairFS ⊤ obsFst).2 ?_, fun h => ?_⟩
  · rw [clientPairFS.before_def, htop]
    exact Set.empty_subset _
  · have h' := (beforeGivenSet_univ_iff clientPairFS obsFst ⊤).1 h
    rw [clientPairFS.before_def, htop, hfst] at h'
    exact absurd (h' rfl) (Set.notMem_empty obsFst)

/-- **Definition 50 at a proper conditioning set, where §3.2's `h^F` cannot reach.**  `Ind_S`
is before every partition given *any* `E`, because `Ind_S|E` is `Ind_E`, whose history is
empty by Proposition 23 clause 4 — a statement about `historySub` at a set that need be
neither `S` nor a block of anything, so the reduction above does not cover it. -/
example {S : Type u} (F : FactoredSet S) [Finite F.B] (Y : Setoid S) (E : Set S) :
    F.BeforeGivenSet ⊤ Y E := by
  rw [FactoredSet.BeforeGivenSet,
    historySub_restrict_eq_empty F ⊤ (restrict_top_eq_indiscrete E)]
  exact Set.empty_subset _

/-- **Conjecture 1 consumed as a hypothesis, composed with Proposition 24.**  A client
willing to *assume* the finite-dimensional fundamental theorem gets more than the
conjecture states at face value: instantiated at `Z = Ind_S` and read against
Proposition 24, it turns *unconditional* `⊥^F` into a numerical test over distributions, on
the client's own factored set.  This is the shape a downstream project wants — the unproved
`Prop` is an ordinary hypothesis, and no declaration of the library claims it. -/
example (h : FundamentalTheoremFiniteDim.{0}) (X Y : Setoid (Bool × Bool)) :
    clientPairFS.Orthogonal X Y ↔
      ∀ P : ProbDist (Bool × Bool), clientPairFS.IsDistribution P →
        ∀ x ∈ X.classes, ∀ y ∈ Y.classes, ∀ z ∈ (⊤ : Setoid (Bool × Bool)).classes,
          P (x ∩ z) * P (y ∩ z) = P (x ∩ y ∩ z) * P z :=
  (clientPairFS.orthogonal_iff_orthogonalGiven_top X Y).trans (h clientPairFS X Y ⊤)

/-- **The conjecture's proved finite instance, composed with Proposition 25.**  No hypothesis
at all this time: `fundamentalTheoremFiniteDim_of_finite` is Theorem 3, and against
Proposition 25 it turns the *order* relation `Z ≤ X` — the paper's `X ≤_S Z`, by
`dd:order-flip` — into a numerical test, satisfied exactly when every distribution on the
client's factored set makes `X` independent of itself given `Z`.  Neither endpoint says
that, and the two together are what a client checking a refinement claim against data
needs. -/
example (X Z : Setoid (Bool × Bool)) :
    Z ≤ X ↔
      ∀ P : ProbDist (Bool × Bool), clientPairFS.IsDistribution P →
        ∀ x ∈ X.classes, ∀ y ∈ X.classes, ∀ z ∈ Z.classes,
          P (x ∩ z) * P (y ∩ z) = P (x ∩ y ∩ z) * P z :=
  (clientPairFS.orthogonalGiven_self_iff X Z).symm.trans
    (fundamentalTheoremFiniteDim_of_finite clientPairFS X X Z)

end APITests.FiniteFactoredSets
