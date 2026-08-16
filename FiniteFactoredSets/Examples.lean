import FiniteFactoredSets.Orthogonality

/-!
# Worked factored sets — the non-vacuity witnesses

Every §2–§3 endpoint is stated over `FactoredSet`, so until something exhibits one those
endpoints say nothing about anything.  This file exhibits four factored sets, covering the
degenerate sizes Proposition 5 singles out and one genuinely two-dimensional example that
makes the chimera function actually splice, and then runs the §2.5 and §3 vocabulary —
`size`, `dim`, `Generates`, `history`, `Orthogonal`, `Entangled`, `Before`,
`StrictlyBefore` — over them.

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

Every declaration here is a non-vacuity witness (kind `N±`), so all of them are `lemma`s:
the `theorem` keyword is reserved for the paper's numbered nodes, and none of these is
one.  They are inventoried in `AxiomAudit.lean` alongside the nodes they de-vacuate.  They cite the paper in prose rather than carrying the reserved node annotation: the
paper's Examples 1 and 2 are §6 orthogonality databases, not these.
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

/-! ## §2.5 and §3 over the witnesses

Everything below is stated for `coordFS` unless it says otherwise.  `Finite F.B` — the
standing hypothesis of §3 — is discharged by instance search on each witness, so no
declaration here has to supply it by hand. -/

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

/-! ### §2.5: size, dimension, and Propositions 7–9 on a witness. -/

/-- `size` and `dim` unfold for a client only through `rfl`; `size_eq_mk` and `dim_eq_mk`
are `private`. -/
lemma size_coordFS_eq_mk : coordFS.size = Cardinal.mk (Bool × Bool) := rfl

lemma dim_coordFS_eq_mk : coordFS.dim = Cardinal.mk coordFS.B := rfl

lemma size_coordFS : coordFS.size = ((4 : ℕ) : Cardinal) := by
  rw [size_coordFS_eq_mk, Cardinal.mk_prod, Cardinal.mk_bool, Cardinal.lift_two]
  norm_num

lemma dim_coordFS : coordFS.dim = ((2 : ℕ) : Cardinal) := by
  rw [dim_coordFS_eq_mk, coordFS_basis_eq, Cardinal.mk_insert (by
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
`Fintype F.B`, which no witness supplies: `Setoid (Bool × Bool)` has no `DecidableEq`, so
membership in `coordBasis` is not decidable.  A client must build the instance by hand,
and it has to be in scope *at statement elaboration time*, because the `∏` in the
statement needs it. -/

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

end Examples
end FiniteFactoredSets
