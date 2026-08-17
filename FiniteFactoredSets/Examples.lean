import FiniteFactoredSets.ConditionalOrthogonality

/-!
# Worked factored sets — the non-vacuity witnesses

Every §2–§4 endpoint is stated over `FactoredSet`, so until something exhibits one those
endpoints say nothing about anything.  This file exhibits four factored sets, covering the
degenerate sizes Proposition 5 singles out and one genuinely two-dimensional example that
makes the chimera function actually splice, and then runs the §2.5, §3 and §4 vocabulary —
`size`, `dim`, `Generates`, `history`, `Orthogonal`, `Entangled`, `Before`,
`StrictlyBefore`, `Subpartition`, `GeneratesSub`, `historySub`, `OrthogonalSub`,
`OrthogonalGivenSet`, `OrthogonalGiven` — over them.

`coordFS` is the load-bearing one: with a single factor every `C` behaves as `∅` or `B`,
so Proposition 4 would be a family of near-tautologies.  `not_subsingleton_coordFS_basis`
and `coordFS_chimera_corners` are what rule that out — the four `C`-corners of
`χ^F_C((true,true),(false,false))` are pairwise distinct.

The §3 half computes the three histories that pin the whole order down —
`h(fstFactor) = {fstFactor}`, `h(Ind_S) = {}`, `h(Dis_S) = B` — and then exhibits each §3
relation both holding and failing, so that none of `Orthogonal`, `Entangled`, `Before`,
`StrictlyBefore` is silently empty or silently total.  Two negative facts are worth
calling out: `history_not_injective` shows `Before` is a preorder and *not* antisymmetric
(the XOR partition and `Dis_S` are distinct partitions sharing a history), and the
`emptyFS_*` lemmas show the `Nonempty S` hypothesis on Proposition 13 clause 4 and
Proposition 19 is load-bearing rather than decorative.

The §4 half restricts `coordFS`'s factors to two subsets — a block `Efst` of `fstFactor`
and the diagonal `Ediag` (a block of `xorPart`) — and computes domains, blocks,
`GeneratesSub`, `historySub` and conditional orthogonality over them.  Four negative facts
carry most of the weight: generation of a subpartition is **not** monotone in `C`
(`generatesSub_not_superset_monotone`), the second conjunct of Proposition 20 clause 7 is
**not** implied by the first (`clause7_second_conjunct_loadbearing`), the `hE` hypothesis
of Proposition 23 clause 2 is load-bearing (`historySub_spec_hE_loadbearing`), and
restriction can **entangle** two unconditionally orthogonal partitions
(`not_orthogonalGivenSet_Ediag`, `not_orthogonalGiven_fst_snd_xorPart`) — which is what
stops `OrthogonalGiven` from being silently total.

No declaration here is a paper node, so all of them are `lemma`s: the `theorem` keyword is
reserved for the paper's numbered nodes.  Every *witness* lemma — the ones that carry a
non-vacuity claim, kind `N±` — is inventoried in `AxiomAudit.lean` alongside the nodes it
de-vacuates; the proof helpers that only exist to shorten those proofs
(`fstFactor_ne_sndFactor`, `coordFS_chimera_eq`, `coordFS_basis_eq`, `fstFactor_mem`,
`sndFactor_mem`, the `singleton_*_subset` and `commonRefinement_singleton_*` lemmas, and
in §4 the `mem_*`, `dom_*`, `*_apply` unfoldings together with `Ediag_eq`,
`generatesSub_snd_botInfIndEfalse`, `botInfIndEfalse_ne_indiscrete`,
`generatesSub_fstOnEdiag_forces`, `generatesSub_sndOnEdiag_forces` and
`inf_ofSetoid_coord`) are
not, since they claim nothing about the paper.  The witnesses cite the paper in prose
rather than carrying the reserved node annotation: the paper's Examples 1 and 2 are §6
orthogonality databases, not these.
-/

universe u

namespace FiniteFactoredSets
namespace Examples

open scoped Classical

/-! ### `|S| = 2` (prime): the discrete factorization of `Bool`, `B = {Dis_S}`. -/

lemma bool_isFactorization :
    IsFactorization ({(⊥ : Setoid Bool)} : Set (Setoid Bool)) where
  nontrivial := by
    rintro b hb ⟨-, h⟩
    simp only [Set.mem_singleton_iff] at hb
    subst hb
    exact Bool.noConfusion (h true false)
  bijective := by
    refine ⟨fun s t h => Quotient.exact (congrFun h ⟨⊥, rfl⟩), fun y => ?_⟩
    refine ⟨Quotient.out (y ⟨⊥, rfl⟩), funext fun b => ?_⟩
    obtain ⟨b, hb⟩ := b
    simp only [Set.mem_singleton_iff] at hb
    subst hb
    exact Quotient.out_eq _

/-- A factored set of size 2 and dimension 1. -/
def boolFS : FactoredSet Bool := ⟨_, bool_isFactorization⟩

/-! ### Dimension 2: the coordinate factorization of `Bool × Bool`. -/

/-- The partition of `Bool × Bool` by first coordinate. -/
def fstFactor : Setoid (Bool × Bool) := Setoid.comap Prod.fst ⊥
/-- The partition of `Bool × Bool` by second coordinate. -/
def sndFactor : Setoid (Bool × Bool) := Setoid.comap Prod.snd ⊥

lemma fstFactor_ne_sndFactor : fstFactor ≠ sndFactor := by
  intro h
  have hr : fstFactor (true, false) (true, true) := rfl
  rw [h] at hr
  exact Bool.noConfusion hr

/-- The two-element basis `{fstFactor, sndFactor}`. -/
def coordBasis : Set (Setoid (Bool × Bool)) := {fstFactor, sndFactor}

lemma coord_isFactorization : IsFactorization coordBasis where
  nontrivial := by
    rintro b (rfl | rfl) ⟨-, h⟩
    · exact Bool.noConfusion (h (true, true) (false, true))
    · exact Bool.noConfusion (h (true, true) (true, false))
  bijective := by
    refine ⟨fun s t h => Prod.ext (Quotient.exact (congrFun h ⟨fstFactor, Or.inl rfl⟩))
      (Quotient.exact (congrFun h ⟨sndFactor, Or.inr rfl⟩)), fun y => ?_⟩
    refine ⟨((Quotient.out (y ⟨fstFactor, Or.inl rfl⟩)).1,
            (Quotient.out (y ⟨sndFactor, Or.inr rfl⟩)).2), funext fun b => ?_⟩
    obtain ⟨b, hb⟩ := b
    rcases hb with rfl | rfl
    · refine Eq.trans (Quotient.sound (?_ : fstFactor _ _)) (Quotient.out_eq _); rfl
    · refine Eq.trans (Quotient.sound (?_ : sndFactor _ _)) (Quotient.out_eq _); rfl

/-- A factored set of size 4 and dimension 2 — the smallest one whose chimera splices. -/
def coordFS : FactoredSet (Bool × Bool) := ⟨coordBasis, coord_isFactorization⟩

/-- The basis is not a subsingleton: `chimera` really has two independent factors. -/
lemma not_subsingleton_coordFS_basis : ¬ Subsingleton coordFS.B := fun h =>
  fstFactor_ne_sndFactor
    (congrArg Subtype.val (h.allEq ⟨fstFactor, Or.inl rfl⟩ ⟨sndFactor, Or.inr rfl⟩))

/-- The chimera of `coordFS` computes coordinatewise. -/
lemma coordFS_chimera_eq (C : Set (Setoid (Bool × Bool))) (s t : Bool × Bool) :
    coordFS.chimera C s t = (if fstFactor ∈ C then s.1 else t.1,
                             if sndFactor ∈ C then s.2 else t.2) := by
  refine Prod.ext ?_ ?_
  · by_cases h : fstFactor ∈ C
    · rw [if_pos h]; exact coordFS.chimera_rel_of_mem s t (Or.inl rfl) h
    · rw [if_neg h]; exact coordFS.chimera_rel_of_notMem s t (Or.inl rfl) h
  · by_cases h : sndFactor ∈ C
    · rw [if_pos h]; exact coordFS.chimera_rel_of_mem s t (Or.inr rfl) h
    · rw [if_neg h]; exact coordFS.chimera_rel_of_notMem s t (Or.inr rfl) h

/-- The four corners of `χ^F_C((⊤,⊤), (⊥,⊥))` are pairwise distinct. -/
lemma coordFS_chimera_corners :
    coordFS.chimera ∅ (true, true) (false, false) = (false, false) ∧
    coordFS.chimera {fstFactor} (true, true) (false, false) = (true, false) ∧
    coordFS.chimera {sndFactor} (true, true) (false, false) = (false, true) ∧
    coordFS.chimera coordFS.B (true, true) (false, false) = (true, true) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [coordFS_chimera_eq] <;>
    simp [coordFS, coordBasis, fstFactor_ne_sndFactor, Ne.symm fstFactor_ne_sndFactor]

/-! ### `|S| = 0`: Proposition 5's `B = {Dis_S} = {{}}`. -/

lemma empty_isFactorization :
    IsFactorization ({(⊥ : Setoid Empty)} : Set (Setoid Empty)) where
  nontrivial := by rintro b - ⟨⟨e⟩, -⟩; exact e.elim
  bijective := ⟨fun s => s.elim, fun y => (Quotient.out (y ⟨⊥, rfl⟩)).elim⟩

def emptyFS : FactoredSet Empty := ⟨_, empty_isFactorization⟩

/-- The empty basis is *not* a factorization of the empty set (paper, Proposition 5). -/
lemma not_isFactorization_empty_basis : ¬ IsFactorization (∅ : Set (Setoid Empty)) := by
  rintro ⟨-, -, hsurj⟩
  obtain ⟨s, -⟩ := hsurj fun b => b.2.elim
  exact s.elim

/-! ### `|S| = 1`: Proposition 5's `B = {}`, and it is the only one. -/

lemma unit_isFactorization : IsFactorization (∅ : Set (Setoid Unit)) where
  nontrivial := by rintro b ⟨⟩
  bijective := ⟨fun s t _ => Subsingleton.elim s t, fun y => ⟨(), funext fun b => b.2.elim⟩⟩

def unitFS : FactoredSet Unit := ⟨_, unit_isFactorization⟩

lemma unitFS_basis_unique (F : FactoredSet Unit) : F.B = ∅ := by
  ext b
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hb
  refine F.nontrivial_of_mem hb ⟨⟨()⟩, fun s t => ?_⟩
  have hst : s = t := Subsingleton.elim s t
  subst hst
  exact b.refl' s

/-! ### Definition 10's two fields are independent.

Neither field of `IsFactorization` implies the other, so neither is decoration.  The two
lemmas below exhibit a set of partitions satisfying `nontrivial` and failing `bijective`,
and one satisfying `bijective` and failing `nontrivial`. -/

/-- `nontrivial` does not imply `bijective`: `{fstFactor}` is a set of nontrivial
partitions of `Bool × Bool`, but nothing in it sees the second coordinate, so the
coordinate map is not injective. -/
lemma not_isFactorization_singleton_fstFactor :
    (∀ b ∈ ({fstFactor} : Set (Setoid (Bool × Bool))), ¬ IsTrivialPartition b) ∧
      ¬ IsFactorization ({fstFactor} : Set (Setoid (Bool × Bool))) := by
  refine ⟨?_, ?_⟩
  · rintro b hb ⟨-, h⟩
    simp only [Set.mem_singleton_iff] at hb
    subst hb
    exact Bool.noConfusion (h (true, true) (false, true))
  · rintro ⟨-, hinj, -⟩
    refine Bool.noConfusion (congrArg Prod.snd (hinj (funext fun b => ?_) :
      ((true, true) : Bool × Bool) = (true, false)))
    obtain ⟨b, hb⟩ := b
    simp only [Set.mem_singleton_iff] at hb
    subst hb
    exact Quotient.sound (rfl : fstFactor (true, true) (true, false))

/-- `bijective` does not imply `nontrivial`: over `Unit` the basis `{Ind_S}` has a
bijective coordinate map, yet `Ind_Unit` is the one-block partition and so is barred as a
factor.  Dropping the `nontrivial` field would therefore give `Unit` two factorizations,
`∅` and `{Ind_S}`, falsifying Proposition 5's uniqueness. -/
lemma not_isFactorization_unit_singleton_top :
    Function.Bijective (fun (s : Unit) (b : ({(⊤ : Setoid Unit)} : Set (Setoid Unit))) =>
        Quotient.mk (b : Setoid Unit) s) ∧
      ¬ IsFactorization ({(⊤ : Setoid Unit)} : Set (Setoid Unit)) := by
  refine ⟨⟨fun s t _ => Subsingleton.elim s t, fun y => ⟨(), funext fun b => ?_⟩⟩, ?_⟩
  · obtain ⟨b, hb⟩ := b
    simp only [Set.mem_singleton_iff] at hb
    subst hb
    refine Eq.trans (Quotient.sound (?_ : (⊤ : Setoid Unit) _ _)) (Quotient.out_eq _)
    trivial
  · rintro ⟨hnt, -⟩
    exact hnt ⊤ rfl ⟨⟨()⟩, fun _ _ => trivial⟩

/-! ## §2.5 and §3 over the witnesses

Everything below is stated for `coordFS` unless it says otherwise.  `Finite F.B` — the
hypothesis every §3.2–§3.4 theorem carries — is discharged by instance search on each
witness, so no declaration here has to supply it by hand. -/

example : Finite coordFS.B := inferInstance
example : Finite boolFS.B := inferInstance
example : Finite emptyFS.B := inferInstance
example : Finite unitFS.B := inferInstance

lemma coordFS_basis_eq :
    coordFS.B = ({fstFactor, sndFactor} : Set (Setoid (Bool × Bool))) := rfl

lemma fstFactor_mem : fstFactor ∈ coordFS.B := Or.inl rfl
lemma sndFactor_mem : sndFactor ∈ coordFS.B := Or.inr rfl

lemma singleton_fstFactor_subset :
    ({fstFactor} : Set (Setoid (Bool × Bool))) ⊆ coordFS.B :=
  Set.singleton_subset_iff.2 fstFactor_mem

lemma singleton_sndFactor_subset :
    ({sndFactor} : Set (Setoid (Bool × Bool))) ⊆ coordFS.B :=
  Set.singleton_subset_iff.2 sndFactor_mem

/-! ### §2.5: size, dimension, and Propositions 7–9 on a witness.

`size` and `dim` unfold for a client through the public `@[simp]` lemmas `size_eq_mk` and
`dim_eq_mk`, which is how the two computations below start. -/

lemma size_coordFS : coordFS.size = ((4 : ℕ) : Cardinal) := by
  rw [coordFS.size_eq_mk, Cardinal.mk_prod, Cardinal.mk_bool, Cardinal.lift_two]
  norm_num

lemma dim_coordFS : coordFS.dim = ((2 : ℕ) : Cardinal) := by
  rw [coordFS.dim_eq_mk, coordFS_basis_eq, Cardinal.mk_insert (by
    simp only [Set.mem_singleton_iff]; exact fstFactor_ne_sndFactor), Cardinal.mk_singleton]
  norm_num

/-- Proposition 7 applies to `coordFS`: `|S| = ∏_b |b|`, and both sides are `4`. -/
lemma size_eq_prod_coordFS :
    (Cardinal.prod fun b : coordFS.B => Cardinal.mk (Quotient (b : Setoid (Bool × Bool))))
      = ((4 : ℕ) : Cardinal) := coordFS.size_eq_prod ▸ size_coordFS

/-- Proposition 9 clause 4 applies to `coordFS`: `4 = 2 · 2` is a product of two primes,
so `1 ≤ dim ≤ 2`. -/
lemma dim_spec_coordFS : 1 ≤ coordFS.dim ∧ coordFS.dim ≤ 2 := by
  have hl : ∀ p ∈ [2, 2], Nat.Prime p := by decide
  have h := coordFS.dim_spec.2.2.2 [2, 2] hl (by decide) (by rw [size_coordFS]; rfl)
  simpa using h

/-- Proposition 8 applies to `boolFS`: `|Bool| = 2` is prime, so its factorization is the
trivial one. -/
lemma boolFS_trivial : IsTrivialFactorization boolFS.B :=
  isTrivialFactorization_of_isFactorization
    (Or.inr (Or.inr ⟨2, Nat.prime_two, by simp⟩)) boolFS.isFactorization

/-! ### §3.1–§3.2: generation and history on `coordFS`. -/

/-- Proposition 10 clause 7 read as a client would: `{fstFactor}` generates `fstFactor`.
Binding clause 7 with an explicitly typed `have` first is necessary — it unfolds to a
strict-implicit `∀ ⦃x y⦄`, and `List.TFAE.out`'s autoparams then fail in term mode. -/
lemma generates_singleton_fstFactor : coordFS.Generates {fstFactor} fstFactor := by
  have h7 : commonRefinement ({fstFactor} : Set (Setoid (Bool × Bool))) ≤ fstFactor :=
    fun {_ _} h => commonRefinement_iff.1 h fstFactor rfl
  exact ((coordFS.generates_tfae singleton_fstFactor_subset fstFactor).out 6 0).1 h7

/-- Proposition 13 clause 4 on a witness: `h^F(b) = {b}` for a factor `b`. -/
lemma history_fstFactor : coordFS.history fstFactor = {fstFactor} :=
  (coordFS.history_spec fstFactor fstFactor).2.2.2 ⟨(true, true)⟩ fstFactor fstFactor_mem

lemma history_sndFactor : coordFS.history sndFactor = {sndFactor} :=
  (coordFS.history_spec sndFactor sndFactor).2.2.2 ⟨(true, true)⟩ sndFactor sndFactor_mem

/-- The same history re-derived *without* Proposition 13 clause 4, so the witness does not
merely echo the endpoint it is testing: `le_iff_history_subset` gives the inclusion in
`{fstFactor}`, and clause 3 rules out `∅`. -/
example : coordFS.history fstFactor = {fstFactor} := by
  have hsub : coordFS.history fstFactor ⊆ {fstFactor} :=
    (coordFS.le_iff_history_subset singleton_fstFactor_subset fstFactor).1
      (fun {_ _} h => commonRefinement_iff.1 h fstFactor rfl)
  have hne : coordFS.history fstFactor ≠ ∅ := by
    intro h
    have htop : fstFactor = (⊤ : Setoid (Bool × Bool)) :=
      (coordFS.history_spec fstFactor fstFactor).2.2.1.1 h
    have hr : fstFactor (true, true) (false, true) := by rw [htop]; trivial
    exact Bool.noConfusion hr
  rcases Set.subset_singleton_iff_eq.1 hsub with h | h
  · exact absurd h hne
  · exact h

/-- Proposition 13 clause 3 on a witness: `Ind_S` has empty history. -/
lemma history_top : coordFS.history (⊤ : Setoid (Bool × Bool)) = ∅ :=
  (coordFS.history_spec (⊤ : Setoid (Bool × Bool)) ⊤).2.2.1.2 rfl

lemma commonRefinement_singleton_fstFactor :
    commonRefinement ({fstFactor} : Set (Setoid (Bool × Bool))) (true, true) (true, false) :=
  commonRefinement_iff.2 fun c hc => by
    simp only [Set.mem_singleton_iff] at hc; subst hc; rfl

lemma commonRefinement_singleton_sndFactor :
    commonRefinement ({sndFactor} : Set (Setoid (Bool × Bool))) (true, true) (false, true) :=
  commonRefinement_iff.2 fun c hc => by
    simp only [Set.mem_singleton_iff] at hc; subst hc; rfl

/-- Any partition separating both coordinate pairs needs *both* factors: its history is
all of `B`.  This is Proposition 10 clause 7 composed with Proposition 12, used
contrapositively. -/
lemma history_eq_basis_of {X : Setoid (Bool × Bool)}
    (h₁ : ¬ X (true, true) (true, false)) (h₂ : ¬ X (true, true) (false, true)) :
    coordFS.history X = coordFS.B := by
  have hsub : coordFS.history X ⊆ coordFS.B := coordFS.history_subset X
  have hnf : ¬ coordFS.history X ⊆ {fstFactor} := fun hle =>
    h₁ ((coordFS.le_iff_history_subset singleton_fstFactor_subset X).2 hle
      commonRefinement_singleton_fstFactor)
  have hns : ¬ coordFS.history X ⊆ {sndFactor} := fun hle =>
    h₂ ((coordFS.le_iff_history_subset singleton_sndFactor_subset X).2 hle
      commonRefinement_singleton_sndFactor)
  obtain ⟨c, hc, hcne⟩ := Set.not_subset.1 hnf
  obtain ⟨d, hd, hdne⟩ := Set.not_subset.1 hns
  have hcs : c = sndFactor := by
    rcases hsub hc with rfl | rfl
    · exact absurd rfl hcne
    · rfl
  have hdf : d = fstFactor := by
    rcases hsub hd with rfl | rfl
    · rfl
    · exact absurd rfl hdne
  subst hcs; subst hdf
  refine Set.Subset.antisymm hsub ?_
  rintro b (rfl | rfl)
  · exact hd
  · exact hc

/-- `Dis_S` needs every factor: `h^F(⊥) = B`. -/
lemma history_bot : coordFS.history (⊥ : Setoid (Bool × Bool)) = coordFS.B :=
  history_eq_basis_of (fun h => Bool.noConfusion (congrArg Prod.snd h))
    (fun h => Bool.noConfusion (congrArg Prod.fst h))

/-! ### §3.3: orthogonality and entanglement on `coordFS`. -/

/-- `fstFactor ⊥^F sndFactor`, proved through Proposition 14 — no history in sight. -/
lemma orthogonal_fstFactor_sndFactor : coordFS.Orthogonal fstFactor sndFactor :=
  (coordFS.orthogonal_iff_exists fstFactor sndFactor).2
    ⟨{fstFactor}, singleton_fstFactor_subset,
      fun {_ _} h => commonRefinement_iff.1 h fstFactor rfl,
      fun {_ _} h => commonRefinement_iff.1 h sndFactor
        ⟨sndFactor_mem, fun hc => fstFactor_ne_sndFactor (Set.mem_singleton_iff.1 hc).symm⟩⟩

/-- Orthogonality is not reflexive: by Proposition 15 clause 4 only `Ind_S` is orthogonal
to itself, and `fstFactor` is not `Ind_S`. -/
lemma not_orthogonal_fstFactor_self : ¬ coordFS.Orthogonal fstFactor fstFactor := by
  intro hO
  have htop : fstFactor = (⊤ : Setoid (Bool × Bool)) :=
    (coordFS.orthogonal_spec fstFactor fstFactor fstFactor).2.2.2.1 hO
  have hr : fstFactor (true, true) (false, true) := by rw [htop]; trivial
  exact Bool.noConfusion hr

/-- Orthogonality is not total either: `Dis_S` sees every factor, so it is entangled with
`fstFactor`. -/
lemma not_orthogonal_bot_fstFactor :
    ¬ coordFS.Orthogonal (⊥ : Setoid (Bool × Bool)) fstFactor := by
  intro hO
  exact (coordFS.orthogonal_iff_forall_notMem ⊥ fstFactor).1 hO fstFactor
    (by rw [history_bot]; exact fstFactor_mem) (by rw [history_fstFactor]; rfl)

/-! ### §3.4: time on `coordFS`. -/

/-- Proposition 18 clause 3 at `Dis_S ≤_S fstFactor`: every factor is before `Dis_S`. -/
lemma before_fstFactor_bot : coordFS.Before fstFactor ⊥ :=
  (coordFS.before_spec fstFactor ⊥ ⊥).2.2.1 bot_le

/-- And strictly so: `{fstFactor} ⊂ B`. -/
lemma strictlyBefore_fstFactor_bot : coordFS.StrictlyBefore fstFactor ⊥ := by
  rw [coordFS.strictlyBefore_def, history_fstFactor, history_bot]
  refine ⟨singleton_fstFactor_subset, fun hall => fstFactor_ne_sndFactor ?_⟩
  exact (Set.mem_singleton_iff.1 (hall sndFactor_mem)).symm

/-- `Before` is not total: the two coordinate factors are incomparable in time. -/
lemma not_before_fstFactor_sndFactor : ¬ coordFS.Before fstFactor sndFactor := by
  intro h
  have h' := (coordFS.before_def fstFactor sndFactor).1 h
  rw [history_fstFactor, history_sndFactor] at h'
  exact fstFactor_ne_sndFactor (Set.mem_singleton_iff.1 (h' rfl))

/-- Proposition 19 on a witness satisfying both `[Finite F.B]` and `[Nonempty S]`: its
hypothesis set is satisfiable. -/
lemma history_eq_setOf_before_coordFS :
    coordFS.history fstFactor = {b ∈ coordFS.B | coordFS.Before b fstFactor} :=
  coordFS.history_eq_setOf_before fstFactor

/-! ### The XOR partition: `Before` is a preorder, not a partial order. -/

/-- `p ∼ q` iff `p.1 XOR p.2 = q.1 XOR q.2`.  Two blocks, and neither coordinate factor
alone determines it. -/
def xorPart : Setoid (Bool × Bool) := Setoid.comap (fun p => p.1 != p.2) ⊥

lemma xorPart_tt_ff : xorPart (true, true) (false, false) := rfl

lemma not_xorPart_tt_tf : ¬ xorPart (true, true) (true, false) := fun h => Bool.noConfusion h

lemma not_xorPart_tt_ft : ¬ xorPart (true, true) (false, true) := fun h => Bool.noConfusion h

/-- The whole basis is the history of `xorPart`: neither coordinate alone computes it. -/
lemma history_xorPart : coordFS.history xorPart = coordFS.B :=
  history_eq_basis_of not_xorPart_tt_tf not_xorPart_tt_ft

lemma xorPart_ne_bot : xorPart ≠ (⊥ : Setoid (Bool × Bool)) := fun h =>
  Bool.noConfusion (congrArg Prod.snd (h ▸ xorPart_tt_ff))

/-- History is *not* injective, so `Before` is a preorder and not a partial order:
`xorPart` and `Dis_S` are distinct partitions with the same history, hence each before the
other.  Proposition 18 claims reflexivity and transitivity and stops there; this is why. -/
lemma history_not_injective :
    coordFS.history xorPart = coordFS.history ⊥ ∧ xorPart ≠ (⊥ : Setoid (Bool × Bool)) :=
  ⟨history_xorPart.trans history_bot.symm, xorPart_ne_bot⟩

lemma before_xorPart_bot_and_back :
    coordFS.Before xorPart ⊥ ∧ coordFS.Before ⊥ xorPart :=
  ⟨le_of_eq (history_xorPart.trans history_bot.symm),
   le_of_eq (history_bot.trans history_xorPart.symm)⟩

/-- Definition 18's second sentence on a witness: `xorPart` is *entangled* with each
coordinate factor, since computing it needs that coordinate. -/
lemma entangled_xorPart_fstFactor : coordFS.Entangled xorPart fstFactor := by
  rw [coordFS.entangled_iff]
  intro hO
  refine (coordFS.orthogonal_iff_forall_notMem xorPart fstFactor).1 hO fstFactor ?_ ?_
  · rw [history_xorPart]; exact fstFactor_mem
  · rw [history_fstFactor]; rfl

/-! ### `Fintype F.B` is *not* dischargeable by instance search on a witness.

`Finite coordFS.B` is (the four `inferInstance`s above), but `natCard_eq_prod` asks for
`Fintype F.B`, which no witness supplies.  The reason is *not* a missing `DecidableEq`:
`open scoped Classical` is in force in this file, so `DecidableEq (Setoid (Bool × Bool))`
synthesizes as `Classical.propDecidable`, and `Fintype ↥({fstFactor, sndFactor} : Set _)`
synthesizes as `Set.fintypeInsert`.  What fails is `Fintype ↥coordBasis` — and hence
`Fintype ↥coordFS.B` — because `coordBasis` and `coordFS` are ordinary non-reducible
`def`s, which instance search will not unfold to find the `insert`/`singleton` structure
underneath.  So a client must build the instance by hand, and it has to be in scope *at
statement elaboration time*, because the `∏` in the statement needs it. -/

section FintypeFriction

noncomputable local instance : Fintype coordFS.B := Fintype.ofFinite _

example : Nat.card (Bool × Bool)
    = ∏ b : coordFS.B, Nat.card (Quotient (b : Setoid (Bool × Bool))) :=
  coordFS.natCard_eq_prod

end FintypeFriction

/-! ### `emptyFS`: the `Nonempty S` hypotheses of §3 are load-bearing.

Proposition 13 clause 4 and Proposition 19 both carry `Nonempty S`.  Over `Empty` all
setoids coincide, so `⊥` is a factor whose history is `∅` rather than `{⊥}` — both
conclusions fail outright, and the hypothesis is not decoration. -/

lemma emptyFS_history_bot : emptyFS.history (⊥ : Setoid Empty) = ∅ :=
  (emptyFS.history_spec (⊥ : Setoid Empty) ⊥).2.2.1.2
    (Setoid.ext fun a _ => (IsEmpty.false a).elim)

/-- Proposition 13 clause 4 fails without `Nonempty S`: `⊥ ∈ emptyFS.B` but `h(⊥) ≠ {⊥}`. -/
lemma emptyFS_history_ne_singleton :
    emptyFS.history (⊥ : Setoid Empty) ≠ {(⊥ : Setoid Empty)} := by
  rw [emptyFS_history_bot]
  exact fun h => Set.singleton_ne_empty _ h.symm

/-- Proposition 19 fails without `Nonempty S`: its right-hand side contains `⊥`. -/
lemma emptyFS_history_ne_setOf_before :
    emptyFS.history (⊥ : Setoid Empty) ≠ {b ∈ emptyFS.B | emptyFS.Before b ⊥} := by
  rw [emptyFS_history_bot]
  intro h
  have hmem : (⊥ : Setoid Empty) ∈ {b ∈ emptyFS.B | emptyFS.Before b ⊥} :=
    ⟨rfl, subset_rfl.trans (le_of_eq (congrArg emptyFS.history
      (Setoid.ext fun a _ => (IsEmpty.false a).elim)))⟩
  rw [← h] at hmem
  exact hmem

/-! ### Client's-eye uses of the §3 endpoints on a witness. -/

example : IsLeast {C | C ⊆ coordFS.B ∧ coordFS.Generates C fstFactor}
    (coordFS.history fstFactor) := coordFS.history_isLeast fstFactor

example : coordFS.Generates {fstFactor} fstFactor ↔
    coordFS.history fstFactor ⊆ {fstFactor} :=
  coordFS.generates_iff_history_subset singleton_fstFactor_subset fstFactor

example : coordFS.Orthogonal fstFactor sndFactor ↔
    ∃ C ⊆ coordFS.B, commonRefinement C ≤ fstFactor ∧
      commonRefinement (coordFS.B \ C) ≤ sndFactor :=
  coordFS.orthogonal_iff_exists fstFactor sndFactor

example : coordFS.Before fstFactor ⊥ ↔
    ∀ C ⊆ coordFS.B, commonRefinement C ≤ (⊥ : Setoid (Bool × Bool)) →
      commonRefinement C ≤ fstFactor :=
  coordFS.before_iff_forall_sInf fstFactor ⊥

/-! ## §4 over `coordFS`: subpartitions, generation, history, conditional orthogonality

Everything below restricts the two coordinate factors of `coordFS` to one of two subsets
of `Bool × Bool`, and computes the §4 vocabulary over the result.  The subsets are chosen
so that one restriction *keeps* the factors independent and the other *entangles* them,
which is what makes the §4.3 endpoints say something.

Definitions 20–22 are exercised by exhibiting a subpartition's domain and its actual set
of blocks; Definition 23 and Propositions 20–21 by a generating set and a non-generating
one; Definition 24 and Propositions 22–23 by histories computed to `{sndFactor}`, `∅` and
`B`; Definitions 25–27 and Propositions 24–25 and Theorem 2 by conditional orthogonality
holding and failing on the same pair of factors. -/

open Subpartition

/-! ### The two subsets that are conditioned on -/

/-- A block of `fstFactor`: the points with first coordinate `true`. -/
def Efst : Set (Bool × Bool) := {p | p.1 = true}

/-- The diagonal `{(false, false), (true, true)}` — a block of `xorPart`. -/
def Ediag : Set (Bool × Bool) := {p | p.1 = p.2}

lemma Ediag_eq : Ediag = ({(false, false), (true, true)} : Set (Bool × Bool)) := by
  ext p
  obtain ⟨a, b⟩ := p
  cases a <;> cases b <;>
    simp [Ediag, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.ext_iff]

/-! ### §4.1: `sndFactor` restricted to a block of `fstFactor`

Definition 22's `X|E` on a concrete `X` and `E`.  Its domain is `E` on the nose, its two
blocks are computed, and `{sndFactor}` generates it while `{fstFactor}` does not — so
Definition 23 is neither empty nor total on the witness. -/

/-- `sndFactor|Efst`, the paper's `X|E` for `X = sndFactor` and `E` a block of
`fstFactor`. -/
def sndOnEfst : Subpartition (Bool × Bool) := (ofSetoid sndFactor).restrict Efst

lemma dom_sndOnEfst : sndOnEfst.dom = Efst := dom_restrict_ofSetoid _ _

/-- Definition 22's blocks, computed: `sndFactor|Efst` is the *discrete* partition of
`Efst`, with the two singleton blocks. -/
lemma classes_sndOnEfst :
    sndOnEfst.classes
      = {{((true, true) : Bool × Bool)}, {((true, false) : Bool × Bool)}} := by
  ext x
  constructor
  · rintro ⟨s, hs, rfl⟩
    rw [dom_sndOnEfst] at hs
    obtain ⟨a, b⟩ := s
    have ha : a = true := hs
    subst ha
    cases b
    · refine Or.inr ?_
      ext u
      obtain ⟨c, d⟩ := u
      constructor
      · rintro ⟨hc, -, hd⟩
        simp only [Set.mem_singleton_iff, Prod.mk.injEq]
        exact ⟨hc, hd⟩
      · rintro h
        simp only [Set.mem_singleton_iff, Prod.mk.injEq] at h
        exact ⟨h.1, rfl, h.2⟩
    · refine Or.inl ?_
      ext u
      obtain ⟨c, d⟩ := u
      constructor
      · rintro ⟨hc, -, hd⟩
        simp only [Set.mem_singleton_iff, Prod.mk.injEq]
        exact ⟨hc, hd⟩
      · rintro h
        simp only [Set.mem_singleton_iff, Prod.mk.injEq] at h
        exact ⟨h.1, rfl, h.2⟩
  · rintro (rfl | rfl)
    · refine ⟨(true, true), by rw [dom_sndOnEfst]; rfl, ?_⟩
      ext u
      obtain ⟨c, d⟩ := u
      constructor
      · rintro h
        simp only [Set.mem_singleton_iff, Prod.mk.injEq] at h
        exact ⟨h.1, rfl, h.2⟩
      · rintro ⟨hc, -, hd⟩
        simp only [Set.mem_singleton_iff, Prod.mk.injEq]
        exact ⟨hc, hd⟩
    · refine ⟨(true, false), by rw [dom_sndOnEfst]; rfl, ?_⟩
      ext u
      obtain ⟨c, d⟩ := u
      constructor
      · rintro h
        simp only [Set.mem_singleton_iff, Prod.mk.injEq] at h
        exact ⟨h.1, rfl, h.2⟩
      · rintro ⟨hc, -, hd⟩
        simp only [Set.mem_singleton_iff, Prod.mk.injEq]
        exact ⟨hc, hd⟩

/-- Definition 23 on the witness: `{sndFactor} ⊢^F sndFactor|Efst`. -/
lemma generatesSub_sndOnEfst : coordFS.GeneratesSub {sndFactor} sndOnEfst := by
  rw [coordFS.generatesSub_iff_rel]
  intro s hs t ht
  rw [dom_sndOnEfst] at hs ht
  rw [coordFS_chimera_eq, if_neg (by simpa using fstFactor_ne_sndFactor),
    if_pos (Set.mem_singleton _)]
  exact ⟨ht, hs, rfl⟩

/-- And `{fstFactor}` does **not** generate it, so `GeneratesSub` is not total. -/
lemma not_generatesSub_fst_sndOnEfst : ¬ coordFS.GeneratesSub {fstFactor} sndOnEfst := by
  intro h
  rw [coordFS.generatesSub_iff_rel] at h
  have hs : ((true, true) : Bool × Bool) ∈ sndOnEfst.dom := by rw [dom_sndOnEfst]; rfl
  have ht : ((true, false) : Bool × Bool) ∈ sndOnEfst.dom := by rw [dom_sndOnEfst]; rfl
  have key := h _ hs _ ht
  rw [coordFS_chimera_eq, if_pos (Set.mem_singleton _),
    if_neg (by simpa using (Ne.symm fstFactor_ne_sndFactor))] at key
  exact Bool.noConfusion key.2.2

/-- Definition 24 computed: `h^F(sndFactor|Efst) = {sndFactor}`, obtained from
Proposition 22's leastness and Proposition 23 clause 4 rather than by unfolding the
intersection. -/
lemma historySub_sndOnEfst : coordFS.historySub sndOnEfst = {sndFactor} := by
  have hle : coordFS.historySub sndOnEfst ⊆ {sndFactor} :=
    (coordFS.historySub_isLeast_and_eq_history.1 sndOnEfst).2
      ⟨singleton_sndFactor_subset, generatesSub_sndOnEfst⟩
  rcases Set.subset_singleton_iff_eq.1 hle with h | h
  · exfalso
    have hind : sndOnEfst = indiscrete sndOnEfst.dom :=
      (coordFS.historySub_spec sndOnEfst sndOnEfst sndOnEfst rfl).2.2.2.1.1 h
    have hmem : sndOnEfst (true, true) (true, false) := by
      rw [hind, dom_sndOnEfst]
      exact ⟨rfl, rfl⟩
    exact Bool.noConfusion hmem.2.2
  · exact h

/-- Proposition 20 clause 7 read as a client would, on the witness. -/
lemma generatesSub_tfae_on_sndOnEfst :
    coordFS.GeneratesSub {sndFactor} sndOnEfst ↔
      ((ofSetoid (commonRefinement ({sndFactor} : Set (Setoid (Bool × Bool))))).restrict
            sndOnEfst.dom ≤ sndOnEfst ∧
        coordFS.chimeraImage {sndFactor} sndOnEfst.dom sndOnEfst.dom = sndOnEfst.dom) :=
  (coordFS.generatesSub_tfae singleton_sndFactor_subset sndOnEfst).out 0 6

/-- The §4.2 replacement for `generates_iff_history_subset`, on the witness: containing the
history is only half of the criterion. -/
lemma generatesSub_iff_on_sndOnEfst :
    coordFS.GeneratesSub {sndFactor} sndOnEfst ↔
      coordFS.historySub sndOnEfst ⊆ {sndFactor} ∧
        ∀ s ∈ sndOnEfst.dom, ∀ t ∈ sndOnEfst.dom,
          coordFS.chimera {sndFactor} s t ∈ sndOnEfst.dom :=
  coordFS.generatesSub_iff_historySub_subset singleton_sndFactor_subset sndOnEfst

/-! ### Generating a subpartition is not monotone in `C`

The paper says so in the remark after Proposition 21; this is the executable
counterexample.  `Ind_Ediag` is generated by `∅`, its history `∅` is contained in
`{fstFactor}`, and yet `{fstFactor}` does not generate it — because
`χ^F_{fstFactor}((false,false), (true,true)) = (false,true) ∉ Ediag`.  So the naive §4
analogue of `generates_iff_history_subset` is false, and Proposition 20 clause 7's second
conjunct is what repairs it. -/

/-- `Ind_E` on the diagonal. -/
def indDiag : Subpartition (Bool × Bool) := indiscrete Ediag

lemma dom_indDiag : indDiag.dom = Ediag := dom_indiscrete _

lemma historySub_indDiag : coordFS.historySub indDiag = ∅ :=
  (coordFS.historySub_spec indDiag indDiag indDiag rfl).2.2.2.1.2 (by rw [dom_indDiag]; rfl)

lemma generatesSub_empty_indDiag : coordFS.GeneratesSub ∅ indDiag :=
  (coordFS.generatesSub_spec ∅ ∅ indDiag indDiag indDiag rfl).2.2.2.1.2
    (by rw [dom_indDiag]; rfl)

lemma not_generatesSub_fst_indDiag : ¬ coordFS.GeneratesSub {fstFactor} indDiag := by
  intro h
  rw [coordFS.generatesSub_iff_rel] at h
  have hs : ((false, false) : Bool × Bool) ∈ indDiag.dom := by rw [dom_indDiag]; rfl
  have ht : ((true, true) : Bool × Bool) ∈ indDiag.dom := by rw [dom_indDiag]; rfl
  have key := h _ hs _ ht
  rw [coordFS_chimera_eq, if_pos (Set.mem_singleton _),
    if_neg (by simpa using (Ne.symm fstFactor_ne_sndFactor))] at key
  exact Bool.noConfusion (key.1 : (false : Bool) = true)

/-- **Generation of a subpartition is not superset-monotone.**  `∅` generates `Ind_Ediag`,
its history is `∅ ⊆ {fstFactor}`, and yet `{fstFactor}` does not generate it. -/
lemma generatesSub_not_superset_monotone :
    coordFS.GeneratesSub ∅ indDiag ∧
      coordFS.historySub indDiag ⊆ ({fstFactor} : Set (Setoid (Bool × Bool))) ∧
      ¬ coordFS.GeneratesSub {fstFactor} indDiag :=
  ⟨generatesSub_empty_indDiag, by rw [historySub_indDiag]; exact Set.empty_subset _,
    not_generatesSub_fst_indDiag⟩

/-- **Proposition 20 clause 7's second conjunct is load-bearing.**  On the diagonal,
`{fstFactor}` satisfies the order half (trivially, since `Ind_E` is the coarsest
subpartition of `E`) but fails the membership half `χ^F_C(E,E) = E`, and indeed does not
generate.  So clause 7 is not equivalent to its first conjunct alone. -/
lemma clause7_second_conjunct_loadbearing :
    (ofSetoid (commonRefinement ({fstFactor} : Set (Setoid (Bool × Bool))))).restrict
        indDiag.dom ≤ indDiag ∧
      coordFS.chimeraImage {fstFactor} indDiag.dom indDiag.dom ≠ indDiag.dom ∧
      ¬ coordFS.GeneratesSub {fstFactor} indDiag := by
  refine ⟨?_, ?_, not_generatesSub_fst_indDiag⟩
  · intro s t h
    have hs : s ∈ Ediag := by rw [← dom_indDiag]; exact h.1
    have ht : t ∈ Ediag := by rw [← dom_indDiag]; exact h.2.1
    exact ⟨hs, ht⟩
  · intro h
    have hmem : ((false, true) : Bool × Bool) ∈
        coordFS.chimeraImage {fstFactor} indDiag.dom indDiag.dom := by
      refine ⟨(false, false), by rw [dom_indDiag]; rfl, (true, true),
        by rw [dom_indDiag]; rfl, ?_⟩
      rw [coordFS_chimera_eq, if_pos (Set.mem_singleton _),
        if_neg (by simpa using (Ne.symm fstFactor_ne_sndFactor))]
    rw [h, dom_indDiag] at hmem
    exact Bool.noConfusion (hmem : (false : Bool) = true)

/-! ### Proposition 23 clause 2's `hE : X.dom = Y.dom` is load-bearing

With `X = Dis_S` (domain all of `S`) and `Y = Ind_E` for `E` the `fst = false` block,
`h^F(X ∨_E Y) = {sndFactor}` while `h^F(X) ∪ h^F(Y) = B ∋ fstFactor`.  The history on the
left is *nonempty*, so the discriminator is not the degenerate `∅`. -/

/-- The other block of `fstFactor`: the points with first coordinate `false`. -/
def Efalse : Set (Bool × Bool) := {p | p.1 = false}

/-- `Dis_S ∨_E Ind_Efalse` — a common refinement of two subpartitions with *different*
domains. -/
def botInfIndEfalse : Subpartition (Bool × Bool) :=
  ofSetoid (⊥ : Setoid (Bool × Bool)) ⊓ indiscrete Efalse

lemma dom_botInfIndEfalse : botInfIndEfalse.dom = Efalse := by
  show ((ofSetoid (⊥ : Setoid (Bool × Bool))).dom ∩ (indiscrete Efalse).dom) = Efalse
  simp

lemma generatesSub_snd_botInfIndEfalse :
    coordFS.GeneratesSub {sndFactor} botInfIndEfalse := by
  refine (coordFS.generatesSub_iff_rel _ _).2 fun s hs t ht => ?_
  rw [dom_botInfIndEfalse] at hs ht
  have hchi : coordFS.chimera {sndFactor} s t = s := by
    rw [coordFS_chimera_eq, if_neg (by simpa using fstFactor_ne_sndFactor),
      if_pos (Set.mem_singleton _)]
    have h1 : t.1 = s.1 := by rw [(ht : t.1 = false), (hs : s.1 = false)]
    rw [h1]
  rw [hchi]
  exact ⟨rfl, hs, hs⟩

lemma botInfIndEfalse_ne_indiscrete : botInfIndEfalse ≠ indiscrete botInfIndEfalse.dom := by
  intro h
  have h1 : botInfIndEfalse ((false, false) : Bool × Bool) ((false, true) : Bool × Bool) := by
    rw [h, dom_botInfIndEfalse]
    exact ⟨rfl, rfl⟩
  exact Bool.noConfusion (congrArg Prod.snd h1.1)

/-- A nondegenerate subpartition history: `{sndFactor}`, neither `∅` nor `B`. -/
lemma historySub_botInfIndEfalse : coordFS.historySub botInfIndEfalse = {sndFactor} := by
  have hle : coordFS.historySub botInfIndEfalse ⊆ {sndFactor} :=
    coordFS.historySub_subset_of_generatesSub singleton_sndFactor_subset
      generatesSub_snd_botInfIndEfalse
  rcases Set.subset_singleton_iff_eq.1 hle with h | h
  · exact absurd ((coordFS.historySub_spec botInfIndEfalse botInfIndEfalse botInfIndEfalse
      rfl).2.2.2.1.1 h) botInfIndEfalse_ne_indiscrete
  · exact h

/-- **Proposition 23 clause 2 fails without `hE`.**  `Dis_S` and `Ind_Efalse` have different
domains, and the union formula for the history of their common refinement is then false. -/
lemma historySub_spec_hE_loadbearing :
    coordFS.historySub botInfIndEfalse ≠
      coordFS.historySub (ofSetoid (⊥ : Setoid (Bool × Bool))) ∪
        coordFS.historySub (indiscrete Efalse) := by
  intro heq
  have hIndY : coordFS.historySub (indiscrete Efalse) = ∅ :=
    (coordFS.historySub_spec (indiscrete Efalse) (indiscrete Efalse) (indiscrete Efalse)
      rfl).2.2.2.1.2 (by rw [dom_indiscrete])
  have hbotX : coordFS.historySub (ofSetoid (⊥ : Setoid (Bool × Bool))) = coordFS.B :=
    (coordFS.historySub_isLeast_and_eq_history.2 ⊥).trans history_bot
  rw [hIndY, hbotX, Set.union_empty, historySub_botInfIndEfalse] at heq
  have hmem : fstFactor ∈ ({sndFactor} : Set (Setoid (Bool × Bool))) := by
    rw [heq]; exact fstFactor_mem
  exact fstFactor_ne_sndFactor (Set.mem_singleton_iff.1 hmem)

/-! ### `Subset` and the `dd:subpartition` correspondence on a witness

`Subset` — the paper's inclusion *as sets of blocks* — is exhibited both holding and
failing, and the `ofSetoidOn` / `toSetoid` bijection of `dd:subpartition` is run in both
directions on a concrete subset. -/

/-- `sndFactor|Efst` is the discrete partition of `Efst`, exhibited through `ofSetoidOn`:
the client-facing constructor and the restriction agree on the nose. -/
lemma ofSetoidOn_bot_Efst : ofSetoidOn Efst (⊥ : Setoid Efst) = sndOnEfst := by
  refine Subpartition.ext fun s t => ⟨?_, ?_⟩
  · rintro ⟨hs, ht, hst⟩
    have h : s = t := congrArg Subtype.val hst
    exact ⟨hs, ht, congrArg Prod.snd h⟩
  · rintro ⟨hs, ht, hsnd⟩
    refine ⟨hs, ht, ?_⟩
    have h : s = t := Prod.ext (hs.trans ht.symm) hsnd
    exact Subtype.ext h

/-- Round trip one, on a concrete subpartition: `ofSetoidOn (dom X) (toSetoid X) = X`. -/
lemma roundtrip_sndOnEfst : ofSetoidOn sndOnEfst.dom sndOnEfst.toSetoid = sndOnEfst :=
  ofSetoidOn_toSetoid sndOnEfst

/-- Round trip two, on a concrete `E` and a concrete partition of it: `toSetoid` recovers
the setoid it was built from, pointwise. -/
lemma roundtrip_bot_Efst (a b : (ofSetoidOn Efst (⊥ : Setoid Efst)).dom) :
    (ofSetoidOn Efst (⊥ : Setoid Efst)).toSetoid a b ↔
      (⊥ : Setoid Efst) ⟨a, by simpa using a.2⟩ ⟨b, by simpa using b.2⟩ :=
  toSetoid_ofSetoidOn Efst (⊥ : Setoid Efst) a b

/-- `Subset`, positive: the diagonal is a block of `xorPart`, so `Ind_Ediag ⊆ xorPart`. -/
lemma subset_indDiag_xorPart : indDiag.Subset (ofSetoid xorPart) := by
  intro s hs t
  rw [dom_indDiag] at hs
  have hs' : s.1 = s.2 := hs
  constructor
  · rintro ⟨ht, -⟩
    have ht' : t.1 = t.2 := ht
    show (t.1 != t.2) = (s.1 != s.2)
    rw [ht', hs']
    simp
  · intro h
    have h' : (t.1 != t.2) = (s.1 != s.2) := h
    rw [hs'] at h'
    simp only [bne_self_eq_false] at h'
    exact ⟨by simpa [Ediag] using h', hs⟩

/-- `Subset`, negative: the blocks of `sndFactor|Efst` are singletons, which are not blocks
of `sndFactor`.  So `Subset` is strictly stronger than `dom`-inclusion, and Proposition 21
clause 6 is not vacuous. -/
lemma not_subset_sndOnEfst_snd : ¬ sndOnEfst.Subset (ofSetoid sndFactor) := by
  intro h
  have hs : ((true, true) : Bool × Bool) ∈ sndOnEfst.dom := by rw [dom_sndOnEfst]; rfl
  have key := (h _ hs (false, true)).2 (rfl : sndFactor (false, true) (true, true))
  exact Bool.noConfusion (key.1 : (false : Bool) = true)

/-- Nested restriction on the witness: `(sndFactor|Efst)|{(true,true)}` collapses. -/
lemma restrict_restrict_sndOnEfst :
    sndOnEfst.restrict {((true, true) : Bool × Bool)}
      = (ofSetoid sndFactor).restrict {((true, true) : Bool × Bool)} :=
  restrict_restrict_of_subset _ (by
    rintro p hp
    simp only [Set.mem_singleton_iff] at hp
    subst hp
    rfl)

/-! ### §4.2: Lemmas 1 and 2 instantiated on `coordFS`

Both lemmas carry hypotheses (`X.dom = Y.dom`, disjoint histories, a point of the domain)
that a reader could suspect of being jointly unsatisfiable.  They are not: on `coordFS`
every one of them is discharged in a line, and Lemma 2's two sides are each computed to
`B` *without* invoking Lemma 2 — the left side from Proposition 22, the right side from
Lemma 1 — so the pair cross-checks Lemma 2 on the witness. -/

lemma historySub_ofSetoid_fstFactor :
    coordFS.historySub (ofSetoid fstFactor) = {fstFactor} := by
  rw [coordFS.historySub_isLeast_and_eq_history.2 fstFactor, history_fstFactor]

lemma historySub_ofSetoid_sndFactor :
    coordFS.historySub (ofSetoid sndFactor) = {sndFactor} := by
  rw [coordFS.historySub_isLeast_and_eq_history.2 sndFactor, history_sndFactor]

/-- Lemma 1's disjointness hypothesis, discharged on the witness. -/
lemma historySub_disjoint_coord :
    coordFS.historySub (ofSetoid fstFactor) ∩ coordFS.historySub (ofSetoid sndFactor)
      = ∅ := by
  rw [historySub_ofSetoid_fstFactor, historySub_ofSetoid_sndFactor]
  refine Set.eq_empty_iff_forall_notMem.2 ?_
  rintro b ⟨hb1, hb2⟩
  simp only [Set.mem_singleton_iff] at hb1 hb2
  exact fstFactor_ne_sndFactor (hb1.symm.trans hb2)

/-- **Lemma 1** on the witness: restricting `fstFactor` to any block of `sndFactor` leaves
its history equal to `{fstFactor}`. -/
lemma lemma1_coordFS (s : Bool × Bool) :
    coordFS.historySub ((ofSetoid fstFactor).restrict ((ofSetoid sndFactor).part s))
      = {fstFactor} := by
  rw [← coordFS.historySub_restrict_part_eq (X := ofSetoid fstFactor)
      (Y := ofSetoid sndFactor) (by simp) historySub_disjoint_coord (by simp),
    historySub_ofSetoid_fstFactor]

/-- Lemma 1 the other way round, so that neither coordinate is privileged. -/
lemma lemma1_coordFS' (s : Bool × Bool) :
    coordFS.historySub ((ofSetoid sndFactor).restrict ((ofSetoid fstFactor).part s))
      = {sndFactor} := by
  rw [← coordFS.historySub_restrict_part_eq (X := ofSetoid sndFactor)
      (Y := ofSetoid fstFactor) (by simp)
      (by rw [Set.inter_comm]; exact historySub_disjoint_coord) (by simp),
    historySub_ofSetoid_sndFactor]

lemma inf_ofSetoid_coord :
    ofSetoid fstFactor ⊓ ofSetoid sndFactor = ofSetoid (⊥ : Setoid (Bool × Bool)) :=
  Subpartition.ext fun _ _ =>
    ⟨fun h => Prod.ext h.1 h.2, fun h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩⟩

/-- Lemma 2's left side, computed independently of Lemma 2: `fst ∨_S snd = Dis_S`, whose
history is all of `B`. -/
lemma lemma2_lhs_coordFS :
    coordFS.historySub (ofSetoid fstFactor ⊓ ofSetoid sndFactor) = coordFS.B := by
  rw [inf_ofSetoid_coord, coordFS.historySub_isLeast_and_eq_history.2, history_bot]

/-- **Lemma 2**'s right side, computed *without* using Lemma 2, so that the pair
`lemma2_lhs_coordFS`/`lemma2_rhs_coordFS` genuinely cross-checks it on `coordFS`: every
union term is `{sndFactor}` by Lemma 1 (`lemma1_coordFS'`) and `h^F(fstFactor)` is
`{fstFactor}`, so the union is `{fstFactor, sndFactor} = B`. -/
lemma lemma2_rhs_coordFS :
    coordFS.historySub (ofSetoid fstFactor) ∪
      (⋃ s ∈ (ofSetoid fstFactor).dom,
        coordFS.historySub ((ofSetoid sndFactor).restrict ((ofSetoid fstFactor).part s)))
      = coordFS.B := by
  have h : ∀ s : Bool × Bool,
      coordFS.historySub ((ofSetoid sndFactor).restrict ((ofSetoid fstFactor).part s))
        = {sndFactor} := lemma1_coordFS'
  simp only [h, historySub_ofSetoid_fstFactor, dom_ofSetoid]
  ext b
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_singleton_iff, Set.mem_univ, exists_const]
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl

/-! ### §4.3: conditioning on the diagonal entangles the coordinate factors

`fstFactor ⊥^F sndFactor` unconditionally, but on the diagonal the first coordinate
*determines* the second, so each restriction needs both factors and the two histories
coincide with `B`.  This is what stops Definitions 26–27 from being implied by
Definition 18, and Proposition 24 from being the whole story. -/

/-- `fstFactor|Ediag`. -/
def fstOnEdiag : Subpartition (Bool × Bool) := (ofSetoid fstFactor).restrict Ediag

/-- `sndFactor|Ediag`. -/
def sndOnEdiag : Subpartition (Bool × Bool) := (ofSetoid sndFactor).restrict Ediag

lemma dom_fstOnEdiag : fstOnEdiag.dom = Ediag := dom_restrict_ofSetoid _ _

lemma dom_sndOnEdiag : sndOnEdiag.dom = Ediag := dom_restrict_ofSetoid _ _

/-- Every set generating `fstFactor|Ediag` contains **both** factors: splicing two diagonal
points along one coordinate alone leaves the diagonal. -/
lemma generatesSub_fstOnEdiag_forces {C : Set (Setoid (Bool × Bool))}
    (h : coordFS.GeneratesSub C fstOnEdiag) : fstFactor ∈ C ∧ sndFactor ∈ C := by
  rw [coordFS.generatesSub_iff_rel] at h
  have hs : ((false, false) : Bool × Bool) ∈ fstOnEdiag.dom := by rw [dom_fstOnEdiag]; rfl
  have ht : ((true, true) : Bool × Bool) ∈ fstOnEdiag.dom := by rw [dom_fstOnEdiag]; rfl
  have key := h _ hs _ ht
  rw [coordFS_chimera_eq] at key
  obtain ⟨hmem, -, hfst⟩ := key
  have h1 : (if fstFactor ∈ C then false else true) = false := hfst
  have hC1 : fstFactor ∈ C := by
    by_contra hc
    rw [if_neg hc] at h1
    exact Bool.noConfusion h1
  have h2 : (if fstFactor ∈ C then false else true)
      = (if sndFactor ∈ C then false else true) := hmem
  rw [if_pos hC1] at h2
  have hC2 : sndFactor ∈ C := by
    by_contra hc
    rw [if_neg hc] at h2
    exact Bool.noConfusion h2
  exact ⟨hC1, hC2⟩

lemma generatesSub_sndOnEdiag_forces {C : Set (Setoid (Bool × Bool))}
    (h : coordFS.GeneratesSub C sndOnEdiag) : fstFactor ∈ C ∧ sndFactor ∈ C := by
  rw [coordFS.generatesSub_iff_rel] at h
  have hs : ((false, false) : Bool × Bool) ∈ sndOnEdiag.dom := by rw [dom_sndOnEdiag]; rfl
  have ht : ((true, true) : Bool × Bool) ∈ sndOnEdiag.dom := by rw [dom_sndOnEdiag]; rfl
  have key := h _ hs _ ht
  rw [coordFS_chimera_eq] at key
  obtain ⟨hmem, -, hsnd⟩ := key
  have h1 : (if sndFactor ∈ C then false else true) = false := hsnd
  have hC2 : sndFactor ∈ C := by
    by_contra hc
    rw [if_neg hc] at h1
    exact Bool.noConfusion h1
  have h2 : (if fstFactor ∈ C then false else true)
      = (if sndFactor ∈ C then false else true) := hmem
  rw [if_pos hC2] at h2
  have hC1 : fstFactor ∈ C := by
    by_contra hc
    rw [if_neg hc] at h2
    exact Bool.noConfusion h2
  exact ⟨hC1, hC2⟩

lemma historySub_fstOnEdiag : coordFS.historySub fstOnEdiag = coordFS.B := by
  refine Set.Subset.antisymm (coordFS.historySub_subset _) ?_
  intro b hb
  refine Set.mem_sInter.2 ?_
  rintro C ⟨-, hC⟩
  rcases hb with rfl | rfl
  · exact (generatesSub_fstOnEdiag_forces hC).1
  · exact (generatesSub_fstOnEdiag_forces hC).2

lemma historySub_sndOnEdiag : coordFS.historySub sndOnEdiag = coordFS.B := by
  refine Set.Subset.antisymm (coordFS.historySub_subset _) ?_
  intro b hb
  refine Set.mem_sInter.2 ?_
  rintro C ⟨-, hC⟩
  rcases hb with rfl | rfl
  · exact (generatesSub_sndOnEdiag_forces hC).1
  · exact (generatesSub_sndOnEdiag_forces hC).2

/-- **Restriction can entangle.**  Definition 18 holds for the pair, Definition 26 fails on
the diagonal. -/
lemma not_orthogonalGivenSet_Ediag :
    coordFS.Orthogonal fstFactor sndFactor ∧
      ¬ coordFS.OrthogonalGivenSet fstFactor sndFactor Ediag := by
  refine ⟨orthogonal_fstFactor_sndFactor, ?_⟩
  intro h
  rw [coordFS.orthogonalGivenSet_def] at h
  have h' : coordFS.historySub fstOnEdiag ∩ coordFS.historySub sndOnEdiag = ∅ := h
  rw [historySub_fstOnEdiag, historySub_sndOnEdiag, Set.inter_self] at h'
  have hmem : fstFactor ∈ (∅ : Set (Setoid (Bool × Bool))) := h' ▸ fstFactor_mem
  exact hmem

/-- The diagonal is a block of `xorPart`, so Definition 27 can be tested at it. -/
lemma Ediag_mem_xorPart_classes : Ediag ∈ xorPart.classes := by
  refine ⟨(false, false), ?_⟩
  ext p
  constructor
  · intro h
    show (p.1 != p.2) = (false != false)
    have hp : p.1 = p.2 := h
    rw [hp]
    simp
  · intro h
    show p.1 = p.2
    have hp : (p.1 != p.2) = (false != false) := h
    simpa using hp

/-- Definition 27 fails at `Z = xorPart` even though Definition 18 holds for the pair. -/
lemma not_orthogonalGiven_fst_snd_xorPart :
    ¬ coordFS.OrthogonalGiven fstFactor sndFactor xorPart := fun h =>
  not_orthogonalGivenSet_Ediag.2 (h Ediag Ediag_mem_xorPart_classes)

/-- Proposition 24 on the witness. -/
lemma orthogonalGiven_fst_snd_top : coordFS.OrthogonalGiven fstFactor sndFactor ⊤ :=
  (coordFS.orthogonal_iff_orthogonalGiven_top fstFactor sndFactor).1
    orthogonal_fstFactor_sndFactor

/-- `OrthogonalGiven` is neither empty nor total on `coordFS`: the same pair of factors is
orthogonal given `Ind_S` and entangled given `xorPart`. -/
lemma orthogonalGiven_nondegenerate :
    coordFS.OrthogonalGiven fstFactor sndFactor ⊤ ∧
      ¬ coordFS.OrthogonalGiven fstFactor sndFactor xorPart :=
  ⟨orthogonalGiven_fst_snd_top, not_orthogonalGiven_fst_snd_xorPart⟩

/-- Proposition 25, negative side: `X ⊥^F X | Ind_S` would force `Ind_S ≤ X`. -/
lemma not_orthogonalGiven_fst_fst_top :
    ¬ coordFS.OrthogonalGiven fstFactor fstFactor ⊤ := by
  intro h
  have hle : (⊤ : Setoid (Bool × Bool)) ≤ fstFactor :=
    (coordFS.orthogonalGiven_self_iff fstFactor ⊤).1 h
  have hr : fstFactor (true, true) (false, true) := hle trivial
  exact Bool.noConfusion hr

/-- Proposition 25, positive side at `Y = X`. -/
lemma orthogonalGiven_fst_fst_fst :
    coordFS.OrthogonalGiven fstFactor fstFactor fstFactor :=
  (coordFS.orthogonalGiven_self_iff fstFactor fstFactor).2 le_rfl

/-- Theorem 2's decomposition on the witness. -/
lemma thm2_decomposition_coordFS :
    coordFS.OrthogonalGiven fstFactor sndFactor ⊤ ∧
      coordFS.OrthogonalGiven fstFactor ⊤ ⊤ := by
  have h : coordFS.OrthogonalGiven fstFactor (sndFactor ⊓ ⊤) ⊤ := by
    rw [inf_top_eq]; exact orthogonalGiven_fst_snd_top
  exact (coordFS.orthogonalGiven_semigraphoid fstFactor sndFactor ⊤ ⊤).2.1 h

/-- Theorem 2's weak union on the witness: `fst ⊥^F snd | snd`. -/
lemma thm2_weakUnion_coordFS :
    coordFS.OrthogonalGiven fstFactor sndFactor sndFactor := by
  have h : coordFS.OrthogonalGiven fstFactor (sndFactor ⊓ sndFactor) ⊤ := by
    rw [inf_idem]; exact orthogonalGiven_fst_snd_top
  have h2 := (coordFS.orthogonalGiven_semigraphoid fstFactor sndFactor ⊤ sndFactor).2.2.1 h
  rwa [top_inf_eq] at h2

/-! ### Degenerate corners of Definitions 26–27

Conditioning on the empty set, or on `Dis_S`, makes *every* pair orthogonal — including a
partition with itself.  Both match the paper (a block of a partition is never empty, so
Definition 27 never conditions on `∅`), but a client reading Definition 26 alone should
know, so both corners are recorded here rather than left to be rediscovered. -/

lemma orthogonalGivenSet_empty : coordFS.OrthogonalGivenSet fstFactor fstFactor ∅ := by
  refine (coordFS.orthogonalGivenSet_def fstFactor fstFactor ∅).2 ?_
  have h : coordFS.historySub ((ofSetoid fstFactor).restrict (∅ : Set (Bool × Bool)))
      = ∅ := by
    refine (coordFS.historySub_spec ((ofSetoid fstFactor).restrict ∅)
      ((ofSetoid fstFactor).restrict ∅) ((ofSetoid fstFactor).restrict ∅) rfl).2.2.2.1.2 ?_
    rw [dom_restrict_ofSetoid]
    exact Subpartition.ext fun s t => ⟨fun hst => ⟨hst.1, hst.2.1⟩, fun hst => hst.1.elim⟩
  rw [h, Set.empty_inter]

/-- Conditioning on `Dis_S` trivializes conditional orthogonality (Proposition 25 at
`Y = ⊥`), even though `fstFactor` is not orthogonal to itself. -/
lemma orthogonalGiven_bot :
    coordFS.OrthogonalGiven fstFactor fstFactor ⊥ ∧
      ¬ coordFS.Orthogonal fstFactor fstFactor :=
  ⟨(coordFS.orthogonalGiven_self_iff fstFactor ⊥).2 bot_le, not_orthogonal_fstFactor_self⟩

/-! ### Client's-eye uses of the §4 endpoints on a witness. -/

example : IsLeast {C | C ⊆ coordFS.B ∧ coordFS.GeneratesSub C sndOnEfst}
    (coordFS.historySub sndOnEfst) :=
  coordFS.historySub_isLeast_and_eq_history.1 sndOnEfst

example : coordFS.OrthogonalSub fstOnEdiag sndOnEdiag ↔
    coordFS.historySub fstOnEdiag ∩ coordFS.historySub sndOnEdiag = ∅ :=
  coordFS.orthogonalSub_def fstOnEdiag sndOnEdiag

end Examples
end FiniteFactoredSets
