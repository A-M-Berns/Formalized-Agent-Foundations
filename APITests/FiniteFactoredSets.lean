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
order to accumulate observations without accidentally "inferring" everything. -/

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

/-- Definition 44 at the other extreme: a database asserting every triple orthogonal is
`Complete` by construction.  Completeness is a statement about `O ∪ N` covering the
triples, not about any model — so it neither implies nor is implied by consistency. -/
example : (⟨Set.univ, ∅⟩ : OrthDatabase Bool).Complete :=
  fun _ _ _ => Or.inl (Set.mem_univ _)

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

end APITests.FiniteFactoredSets
