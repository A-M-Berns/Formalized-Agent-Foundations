import FiniteFactoredSets.Inference

/-!
# Inferring time: the two worked examples

This file is §6.2 of Garrabrant, *Temporal Inference with Finite Factored Sets*
(arXiv:2109.11513): Examples 1 and 2 (orthogonality databases on two- and three-bit sample
spaces) and Propositions 33–36 — each database is consistent, and the inferred temporal
order recovers `X <_D Y` (Example 1) and `X <_D Y <_D Z` (Example 2).

Bit strings are tuples of `Bool`; the paper's `x_i`, `y_i`, `z_i` are the coordinate
partitions (`Setoid.comap Prod.fst ⊥` etc.), `V` is the "first two bits agree" partition,
and `{Ω}` is `⊤`.  Example 2's model lives on `Bool × Bool × Option Bool`: the paper's
two-bit strings are the points with third coordinate `none`, so `Z'` (Definition 39's third
factor, "the third bit exists and is `i`" / "there are only two bits") is the third-coordinate
partition and `f` copies the second bit into a missing third one.
-/

universe u

namespace FiniteFactoredSets

open scoped Classical

/-! ## Example 1 -/

namespace Example1

/-- Ω for Example 1: bit strings of length 2. -/
abbrev Ω := Bool × Bool

/-- `X`: the first bit. -/
def X : Setoid Ω := Setoid.comap Prod.fst ⊥
/-- `Y`: the second bit. -/
def Y : Setoid Ω := Setoid.comap Prod.snd ⊥
/-- `V`: whether the two bits are equal. -/
def V : Setoid Ω := Setoid.comap (fun p : Ω => (p.1 == p.2)) ⊥

/-- Example 1's database: `O = {(X, V, {Ω})}`, `N = {(V, V, {Ω})}`.

Paper node: Example 1 (§6.2). -/
def D : OrthDatabase Ω := ⟨{(X, V, ⊤)}, {(V, V, ⊤)}⟩

/-! ### The paper's model `(Ω, {X, V})`

Proposition 33's proof names one factored set — `Ω` factored by the first bit and by the
agreement of the two bits — and takes `f` to be the identity.  This is *not* the coordinate
factorization `{X, Y}`; `V` is a genuinely non-coordinate factor, and it is what makes
`Y` late. -/

lemma X_ne_V : X ≠ V := fun h =>
  Bool.noConfusion ((Setoid.ext_iff.1 h (true, true) (true, false)).1 rfl)

lemma V_ne_top : V ≠ (⊤ : Setoid Ω) := fun h =>
  Bool.noConfusion ((Setoid.ext_iff.1 h (true, true) (true, false)).2 trivial)

/-- Example 1's basis `B = {X, V}`. -/
def basis : Set (Setoid Ω) := {X, V}

/-- Prescribing the first bit and the agreement bit pins down a point of `Ω` — the
surjectivity half of `{X, V}` being a factorization. -/
private lemma exists_bits (a v : Bool) : ∃ p : Ω, p.1 = a ∧ (p.1 == p.2) = v :=
  ⟨(a, v == a), rfl, by revert a v; decide⟩

lemma basis_isFactorization : IsFactorization basis where
  nontrivial := by
    rintro b (rfl | rfl) ⟨-, h⟩
    · exact Bool.noConfusion (h (true, true) (false, false))
    · exact Bool.noConfusion (h (true, true) (true, false))
  bijective := by
    refine ⟨fun s t h => ?_, fun y => ?_⟩
    · have h1 : s.1 = t.1 := Quotient.exact (congrFun h ⟨X, Or.inl rfl⟩)
      have h2 : (s.1 == s.2) = (t.1 == t.2) := Quotient.exact (congrFun h ⟨V, Or.inr rfl⟩)
      clear h
      obtain ⟨s1, s2⟩ := s
      obtain ⟨t1, t2⟩ := t
      revert h1 h2
      revert s1 s2 t1 t2
      decide
    · obtain ⟨p, hp1, hp2⟩ := exists_bits (Quotient.out (y ⟨X, Or.inl rfl⟩)).1
        ((Quotient.out (y ⟨V, Or.inr rfl⟩)).1 == (Quotient.out (y ⟨V, Or.inr rfl⟩)).2)
      refine ⟨p, funext fun b => ?_⟩
      obtain ⟨b, (rfl | rfl)⟩ := b
      · exact (Quotient.sound hp1).trans (Quotient.out_eq _)
      · exact (Quotient.sound hp2).trans (Quotient.out_eq _)

/-- Example 1's factored set `F = (Ω, {X, V})`. -/
def F : FactoredSet Ω := ⟨basis, basis_isFactorization⟩

lemma X_mem_basis : X ∈ F.B := Or.inl rfl

lemma V_mem_basis : V ∈ F.B := Or.inr rfl

/-- Proposition 33's model `M = (F, f)` with `f` the identity on `Ω`. -/
def idModel : Model Ω := ⟨F, id⟩

/-- Pullback along `idModel` is the identity — `Model.pullback_id`, which is why every
obligation below can be read directly as a statement about `F`. -/
example (A : Setoid Ω) : idModel.pullback A = A := Model.pullback_id F A

/-- `h^F(X) = {X}` by Proposition 13 clause 4: a factor is its own history. -/
lemma history_X : F.history X = {X} :=
  (F.history_spec X X).2.2.2 ⟨(true, true)⟩ X X_mem_basis

/-- `h^F(V) = {V}`, likewise. -/
lemma history_V : F.history V = {V} :=
  (F.history_spec V V).2.2.2 ⟨(true, true)⟩ V V_mem_basis

lemma orthogonal_X_V : F.Orthogonal X V := by
  refine (F.orthogonal_iff_forall_notMem X V).2 fun b hb hb' => X_ne_V ?_
  rw [history_X, Set.mem_singleton_iff] at hb
  rw [history_V, Set.mem_singleton_iff] at hb'
  exact hb.symm.trans hb'

/-- Proposition 15 clause 4: `V` is entangled with itself because `V ≠ Ind_Ω`. -/
lemma not_orthogonal_V_V : ¬ F.Orthogonal V V := fun h =>
  V_ne_top ((F.orthogonal_spec V V V).2.2.2.1 h)

/-- The identity model on `(Ω, {X, V})` models `D`: its one orthogonality is Proposition 24
applied to `X ⊥ V`, and its one non-orthogonality is `V` entangled with itself. -/
lemma models_D : OrthDatabase.Models idModel D := by
  refine fun A B C => ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨rfl, rfl, rfl⟩ : A = X ∧ B = V ∧ C = ⊤ := by
      simpa [OrthDatabase.Orth, D, Prod.ext_iff] using h
    show F.OrthogonalGiven X V ⊤
    exact (F.orthogonal_iff_orthogonalGiven_top X V).1 orthogonal_X_V
  · obtain ⟨rfl, rfl, rfl⟩ : A = V ∧ B = V ∧ C = ⊤ := by
      simpa [OrthDatabase.NotOrth, D, Prod.ext_iff] using h
    show ¬ F.OrthogonalGiven V V ⊤
    exact fun hg => not_orthogonal_V_V ((F.orthogonal_iff_orthogonalGiven_top V V).2 hg)

/-- **Proposition 33** — Example 1's database is consistent (the identity model on the
factored set `(Ω, {X, V})` models it).

Paper node: Proposition 33 (§6.2). -/
theorem D_consistent : D.Consistent := ⟨idModel, models_D⟩

/-! ### The bit arithmetic behind Proposition 34

The paper's `X ≤_Ω Y ∨_Ω V` is Mathlib's `Y ⊓ V ≤ X` (`dd:order-flip`: the paper's `≤_Ω`
is `≥`, and its `∨_Ω` is `⊓`).  Both directions are two-bit case checks. -/

/-- The second bit together with the agreement bit determines the first bit. -/
lemma inf_Y_V_le_X : Y ⊓ V ≤ X := by
  rintro ⟨a1, a2⟩ ⟨b1, b2⟩ ⟨(h1 : a2 = b2), (h2 : (a1 == a2) = (b1 == b2))⟩
  show a1 = b1
  revert h1 h2
  revert a1 a2 b1 b2
  decide

/-- The paper's "by swapping `X` and `V`": the two bits determine the agreement bit. -/
lemma inf_Y_X_le_V : Y ⊓ X ≤ V := by
  rintro ⟨a1, a2⟩ ⟨b1, b2⟩ ⟨(h1 : a2 = b2), (h2 : a1 = b1)⟩
  show (a1 == a2) = (b1 == b2)
  revert h1 h2
  revert a1 a2 b1 b2
  decide

/-- **Proposition 34** — in Example 1, `X <_D Y`: every model of `D` puts the first bit
strictly before the second.

Paper node: Proposition 34 (§6.2). -/
theorem before_X_Y : D.Before X Y := by
  intro M hM
  -- `f⁻¹(X) ≤_S f⁻¹(Y) ∨_S f⁻¹(V)` and its `X`/`V` swap, pulled back pointwise.
  have hXle : M.pullback Y ⊓ M.pullback V ≤ M.pullback X := by
    intro s t hst
    obtain ⟨h1, h2⟩ := hst
    exact inf_Y_V_le_X (⟨h1, h2⟩ : (Y ⊓ V) (M.f s) (M.f t))
  have hVle : M.pullback Y ⊓ M.pullback X ≤ M.pullback V := by
    intro s t hst
    obtain ⟨h1, h2⟩ := hst
    exact inf_Y_X_le_V (⟨h1, h2⟩ : (Y ⊓ X) (M.f s) (M.f t))
  -- `D`'s two assertions, transported through Proposition 24.
  have hOrthXV : M.F.Orthogonal (M.pullback X) (M.pullback V) :=
    (M.F.orthogonal_iff_orthogonalGiven_top _ _).2 (by simpa using (hM X V ⊤).1 rfl)
  have hNotVV : ¬ M.F.Orthogonal (M.pullback V) (M.pullback V) := fun h =>
    (hM V V ⊤).2 rfl (by simpa using (M.F.orthogonal_iff_orthogonalGiven_top _ _).1 h)
  -- `H_V ≠ {}`: Proposition 15 clause 4 then Proposition 13 clause 3.
  have hVne : M.F.history (M.pullback V) ≠ ∅ := fun h =>
    hNotVV ((M.F.orthogonal_spec (M.pullback V) (M.pullback V) (M.pullback V)).2.2.2.2
      ((M.F.history_spec (M.pullback V) (M.pullback V)).2.2.1.1 h))
  -- `H_X ⊆ H_Y ∪ H_V` and `H_V ⊆ H_Y ∪ H_X`: Proposition 13 clauses 1 and 2.
  have hXsub : M.F.history (M.pullback X) ⊆
      M.F.history (M.pullback Y) ∪ M.F.history (M.pullback V) := by
    have h := (M.F.history_spec (M.pullback X) (M.pullback Y ⊓ M.pullback V)).1 hXle
    rwa [(M.F.history_spec (M.pullback Y) (M.pullback V)).2.1] at h
  have hVsub : M.F.history (M.pullback V) ⊆
      M.F.history (M.pullback Y) ∪ M.F.history (M.pullback X) := by
    have h := (M.F.history_spec (M.pullback V) (M.pullback Y ⊓ M.pullback X)).1 hVle
    rwa [(M.F.history_spec (M.pullback Y) (M.pullback X)).2.1] at h
  have hdisj := (M.F.orthogonal_iff_forall_notMem (M.pullback X) (M.pullback V)).1 hOrthXV
  have hXY : M.F.history (M.pullback X) ⊆ M.F.history (M.pullback Y) := fun b hb =>
    Or.resolve_right (hXsub hb) (hdisj b hb)
  have hVY : M.F.history (M.pullback V) ⊆ M.F.history (M.pullback Y) := fun b hb =>
    Or.resolve_right (hVsub hb) fun hbX => hdisj b hbX hb
  obtain ⟨b, hb⟩ := Set.nonempty_iff_ne_empty.2 hVne
  exact (Set.ssubset_iff_of_subset hXY).2 ⟨b, hVY hb, fun hbX => hdisj b hbX hb⟩

/-! ### Client's-eye use

Proposition 33 hands over a model of `D`, and Proposition 34 applies to *that* model to
give a strict temporal order between the pullbacks — the two endpoints composed the way a
downstream consumer would compose them, with `D` never unfolded.  The witness is pinned at
`idModel` rather than taken from `D_consistent`'s existential, so the strict order below is
exhibited on a named factored set. -/

example : D.Orth X V ⊤ := rfl

example : idModel.F.StrictlyBefore (idModel.pullback X) (idModel.pullback Y) :=
  before_X_Y idModel models_D

example : ∃ M : Model Ω, M.F.StrictlyBefore (M.pullback X) (M.pullback Y) :=
  ⟨idModel, before_X_Y idModel models_D⟩

end Example1

/-! ## Example 2 -/

namespace Example2

/-- Ω for Example 2: bit strings of length 3. -/
abbrev Ω := Bool × Bool × Bool

/-- `X`: the first bit. -/
def X : Setoid Ω := Setoid.comap (fun p : Ω => p.1) ⊥
/-- `Y`: the second bit. -/
def Y : Setoid Ω := Setoid.comap (fun p : Ω => p.2.1) ⊥
/-- `Z`: the third bit. -/
def Z : Setoid Ω := Setoid.comap (fun p : Ω => p.2.2) ⊥
/-- `V`: whether the first two bits are equal. -/
def V : Setoid Ω := Setoid.comap (fun p : Ω => (p.1 == p.2.1)) ⊥

/-- Example 2's database: `O = {(X,V,{Ω}), (X,Z,Y), (V,Z,Y)}`,
`N = {(X,Z,{Ω}), (V,Z,{Ω}), (Z,Z,Y)}`.

Paper node: Example 2 (§6.2). -/
def D : OrthDatabase Ω := ⟨{(X, V, ⊤), (X, Z, Y), (V, Z, Y)}, {(X, Z, ⊤), (V, Z, ⊤), (Z, Z, Y)}⟩

open Subpartition

/-! ### Pullbacks in an arbitrary model of `D`

Definition 39's `f⁻¹(-)` for the three partitions of `Ω` that Proposition 36's argument
has to read coordinatewise, and the three coarsening facts the paper opens Propositions 34
and 36 with — `X ≤_Ω Y ∨_Ω V` and its two rotations — pulled back along an arbitrary `f`.
Each unfolding is `Iff.rfl`: `Setoid.comap` composes with the coordinate map definitionally,
which is why the proofs below can move between `f⁻¹(A) s t` and a `Bool` equation by
`show` alone. -/

section Pullbacks

variable {M : Model Ω}

private lemma pbX_iff (s t : M.S) : M.pullback X s t ↔ (M.f s).1 = (M.f t).1 := Iff.rfl
private lemma pbY_iff (s t : M.S) : M.pullback Y s t ↔ (M.f s).2.1 = (M.f t).2.1 := Iff.rfl
private lemma pbV_iff (s t : M.S) :
    M.pullback V s t ↔ ((M.f s).1 == (M.f s).2.1) = ((M.f t).1 == (M.f t).2.1) := Iff.rfl

/-- `X ≤_Ω Y ∨_Ω V`, pulled back. -/
private lemma pb_inf_YV_le_X : M.pullback Y ⊓ M.pullback V ≤ M.pullback X := by
  intro s t hst
  have h1 := (pbY_iff s t).1 hst.1
  have h2 := (pbV_iff s t).1 hst.2
  rw [pbX_iff]
  revert h1 h2
  cases (M.f s).1 <;> cases (M.f s).2.1 <;> cases (M.f t).1 <;> cases (M.f t).2.1 <;> decide

/-- `V ≤_Ω X ∨_Ω Y`, pulled back. -/
private lemma pb_inf_XY_le_V : M.pullback X ⊓ M.pullback Y ≤ M.pullback V := by
  intro s t hst
  have h1 := (pbX_iff s t).1 hst.1
  have h2 := (pbY_iff s t).1 hst.2
  rw [pbV_iff, h1, h2]

/-- `Y ≤_Ω X ∨_Ω V`, pulled back. -/
private lemma pb_inf_XV_le_Y : M.pullback X ⊓ M.pullback V ≤ M.pullback Y := by
  intro s t hst
  have h1 := (pbX_iff s t).1 hst.1
  have h2 := (pbV_iff s t).1 hst.2
  rw [pbY_iff]
  revert h1 h2
  cases (M.f s).1 <;> cases (M.f s).2.1 <;> cases (M.f t).1 <;> cases (M.f t).2.1 <;> decide

end Pullbacks

/-! ### Proposition 35 — the paper's twelve-point model

The paper's `S` is the set of bit strings of length 2 *or* 3, so it has latent structure
`Ω` does not: `f` collapses the four two-bit strings onto four of the three-bit ones.  The
factors are the paper's `X'` (first bit), `V'` (the first two bits agree) and `Z'` (the
third coordinate, with *three* blocks — "the third bit is `0`", "…is `1`", and "there are
only two bits").  `Y'` and `ZP` are not factors: they are the pullbacks `f⁻¹(Y)` and
`f⁻¹(Z)`, named because the paper's proof computes their histories.

All six verdicts go through *upper* bounds on the restricted histories — the only lower
bound anyone needs is that `h^F(f⁻¹(Z)|y)` is nonempty, for `¬(Z ⊥_D Z | Y)`. -/

/-! #### The carrier and its factorization -/

/-- The paper's `S`: bit strings of length 2 or 3.  A third coordinate `none` is a two-bit
string, `some c` a three-bit string with third bit `c`. -/
abbrev Carrier := Bool × Bool × Option Bool

/-- The paper's `X'`: the first bit. -/
def X' : Setoid Carrier := Setoid.comap (fun s : Carrier => s.1) ⊥
/-- The paper's `V'`: whether the first two bits are equal. -/
def V' : Setoid Carrier := Setoid.comap (fun s : Carrier => (s.1 == s.2.1)) ⊥
/-- The paper's `Z'`, a partition into *three* blocks: the third bit is `0`, is `1`, or
there is no third bit. -/
def Z' : Setoid Carrier := Setoid.comap (fun s : Carrier => s.2.2) ⊥
/-- The paper's `Y'`: the second bit.  Not a factor — it is `f⁻¹(Y)`. -/
def Y' : Setoid Carrier := Setoid.comap (fun s : Carrier => s.2.1) ⊥
/-- `f⁻¹(Z)`, the last bit of `f s`: the paper's two-block partition
`{{000,010,100,110,00,10}, {001,011,101,111,01,11}}`. -/
def ZP : Setoid Carrier := Setoid.comap (fun s : Carrier => s.2.2.getD s.2.1) ⊥

/-- The paper's `B = {X', V', Z'}`. -/
def basis : Set (Setoid Carrier) := {X', V', Z'}

lemma bool_snd_eq : ∀ a b a' b' : Bool, a = a' → (a == b) = (a' == b') → b = b' := by decide

lemma bool_beq_beq : ∀ a v : Bool, (a == (a == v)) = v := by decide

lemma X'_ne_V' : X' ≠ V' := by
  intro h
  have hr : X' (true, true, none) (true, false, none) := rfl
  rw [h] at hr
  exact Bool.noConfusion (show (true : Bool) = false from hr)

lemma X'_ne_Z' : X' ≠ Z' := by
  intro h
  have hr : X' (true, true, none) (true, true, some true) := rfl
  rw [h] at hr
  exact absurd (show (none : Option Bool) = some true from hr) (by simp)

lemma V'_ne_Z' : V' ≠ Z' := by
  intro h
  have hr : V' (true, true, none) (true, true, some true) := rfl
  rw [h] at hr
  exact absurd (show (none : Option Bool) = some true from hr) (by simp)

lemma basis_isFactorization : IsFactorization basis where
  nontrivial := by
    rintro b (rfl | rfl | rfl) ⟨-, h⟩
    · exact Bool.noConfusion
        (show (true : Bool) = false from h (true, false, none) (false, false, none))
    · exact Bool.noConfusion
        (show (true : Bool) = false from h (true, true, none) (true, false, none))
    · exact absurd
        (show (none : Option Bool) = some true from
          h (false, false, none) (false, false, some true)) (by simp)
  bijective := by
    constructor
    · intro s t h
      have h1 : s.1 = t.1 := Quotient.exact (congrFun h ⟨X', Or.inl rfl⟩)
      have h2 : (s.1 == s.2.1) = (t.1 == t.2.1) :=
        Quotient.exact (congrFun h ⟨V', Or.inr (Or.inl rfl)⟩)
      have h3 : s.2.2 = t.2.2 := Quotient.exact (congrFun h ⟨Z', Or.inr (Or.inr rfl)⟩)
      exact Prod.ext h1 (Prod.ext (bool_snd_eq _ _ _ _ h1 h2) h3)
    · intro y
      refine ⟨((Quotient.out (y ⟨X', Or.inl rfl⟩)).1,
        (Quotient.out (y ⟨X', Or.inl rfl⟩)).1 ==
          ((Quotient.out (y ⟨V', Or.inr (Or.inl rfl)⟩)).1 ==
            (Quotient.out (y ⟨V', Or.inr (Or.inl rfl)⟩)).2.1),
        (Quotient.out (y ⟨Z', Or.inr (Or.inr rfl)⟩)).2.2), funext fun b => ?_⟩
      obtain ⟨b, hb⟩ := b
      rcases hb with rfl | rfl | rfl
      · refine Eq.trans (Quotient.sound ?_) (Quotient.out_eq _)
        rfl
      · refine Eq.trans (Quotient.sound ?_) (Quotient.out_eq _)
        exact bool_beq_beq _ _
      · refine Eq.trans (Quotient.sound ?_) (Quotient.out_eq _)
        rfl

lemma basis_finite : basis.Finite := ((Set.finite_singleton Z').insert V').insert X'

/-- The paper's finite factored set `(S, B)`. -/
def carrierFS : FactoredSet Carrier := ⟨basis, basis_isFactorization⟩

instance : Finite (carrierFS.B) := basis_finite.to_subtype

lemma memX' : X' ∈ carrierFS.B := Or.inl rfl
lemma memV' : V' ∈ carrierFS.B := Or.inr (Or.inl rfl)
lemma memZ' : Z' ∈ carrierFS.B := Or.inr (Or.inr rfl)

/-- The paper's `f`, which copies the second bit into a missing third one. -/
def f : Carrier → Ω := fun s => (s.1, s.2.1, s.2.2.getD s.2.1)

/-- The paper's model `(F, f)` of Example 2. -/
def model : Model Ω := ⟨carrierFS, f⟩

/-! #### The pullbacks -/

lemma pullback_X : model.pullback X = X' := Setoid.ext fun _ _ => Iff.rfl
lemma pullback_Y : model.pullback Y = Y' := Setoid.ext fun _ _ => Iff.rfl
lemma pullback_V : model.pullback V = V' := Setoid.ext fun _ _ => Iff.rfl
lemma pullback_Z : model.pullback Z = ZP := Setoid.ext fun _ _ => Iff.rfl

/-! #### Histories -/

lemma history_X' : carrierFS.history X' = {X'} :=
  (carrierFS.history_spec X' X').2.2.2 ⟨(false, false, none)⟩ X' memX'

lemma history_V' : carrierFS.history V' = {V'} :=
  (carrierFS.history_spec V' V').2.2.2 ⟨(false, false, none)⟩ V' memV'


/-- A separating pair refutes `h^F(W) ⊆ C`: if every factor in `C` identifies `p` and `q`
but `W` does not, then `C` cannot contain the history of `W`. -/
lemma not_history_subset {C : Set (Setoid Carrier)} (hC : C ⊆ carrierFS.B) (W : Setoid Carrier)
    (p q : Carrier) (hp : ∀ b ∈ C, b p q) (hq : ¬ W p q) : ¬ carrierFS.history W ⊆ C := fun h =>
  hq ((carrierFS.le_iff_history_subset hC W).2 h (commonRefinement_iff.2 hp))

lemma pair_XV_subset : ({X', V'} : Set (Setoid Carrier)) ⊆ carrierFS.B := by
  rintro b (rfl | rfl)
  · exact memX'
  · exact memV'

lemma pair_XZ_subset : ({X', Z'} : Set (Setoid Carrier)) ⊆ carrierFS.B := by
  rintro b (rfl | rfl)
  · exact memX'
  · exact memZ'

lemma pair_VZ_subset : ({V', Z'} : Set (Setoid Carrier)) ⊆ carrierFS.B := by
  rintro b (rfl | rfl)
  · exact memV'
  · exact memZ'

lemma history_Y' : carrierFS.history Y' = {X', V'} := by
  have hsub : carrierFS.history Y' ⊆ {X', V'} := by
    refine (carrierFS.le_iff_history_subset pair_XV_subset Y').1 ?_
    intro s t hst
    exact bool_snd_eq _ _ _ _ (commonRefinement_iff.1 hst X' (Or.inl rfl))
      (commonRefinement_iff.1 hst V' (Or.inr rfl))
  have hX : X' ∈ carrierFS.history Y' := by
    by_contra hc
    refine not_history_subset (Set.singleton_subset_iff.2 memV') Y'
      (false, false, none) (true, true, none) ?_ ?_ ?_
    · intro b hb
      simp only [Set.mem_singleton_iff] at hb
      subst hb
      exact rfl
    · intro hh
      exact Bool.noConfusion (show (false : Bool) = true from hh)
    · intro c hc'
      rcases hsub hc' with rfl | rfl
      · exact absurd hc' hc
      · rfl
  have hV : V' ∈ carrierFS.history Y' := by
    by_contra hc
    refine not_history_subset (Set.singleton_subset_iff.2 memX') Y'
      (false, false, none) (false, true, none) ?_ ?_ ?_
    · intro b hb
      simp only [Set.mem_singleton_iff] at hb
      subst hb
      exact rfl
    · intro hh
      exact Bool.noConfusion (show (false : Bool) = true from hh)
    · intro c hc'
      rcases hsub hc' with rfl | rfl
      · rfl
      · exact absurd hc' hc
  refine Set.Subset.antisymm hsub ?_
  rintro b (rfl | rfl)
  · exact hX
  · exact hV

lemma history_ZP : carrierFS.history ZP = carrierFS.B := by
  refine Set.Subset.antisymm (carrierFS.history_subset ZP) ?_
  rintro b (rfl | rfl | rfl)
  · by_contra hc
    refine not_history_subset pair_VZ_subset ZP
      (false, false, none) (true, true, none) ?_ ?_ ?_
    · rintro c (rfl | rfl)
      · exact rfl
      · exact rfl
    · intro hh
      exact Bool.noConfusion (show (false : Bool) = true from hh)
    · intro c hc'
      rcases carrierFS.history_subset ZP hc' with rfl | rfl | rfl
      · exact absurd hc' hc
      · exact Or.inl rfl
      · exact Or.inr rfl
  · by_contra hc
    refine not_history_subset pair_XZ_subset ZP
      (false, false, none) (false, true, none) ?_ ?_ ?_
    · rintro c (rfl | rfl)
      · exact rfl
      · exact rfl
    · intro hh
      exact Bool.noConfusion (show (false : Bool) = true from hh)
    · intro c hc'
      rcases carrierFS.history_subset ZP hc' with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact absurd hc' hc
      · exact Or.inr rfl
  · by_contra hc
    refine not_history_subset pair_XV_subset ZP
      (false, false, none) (false, false, some true) ?_ ?_ ?_
    · rintro c (rfl | rfl)
      · exact rfl
      · exact rfl
    · intro hh
      exact Bool.noConfusion (show (false : Bool) = true from hh)
    · intro c hc'
      rcases carrierFS.history_subset ZP hc' with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd hc' hc

/-! #### Histories of the restrictions to a block of `Y'` -/

lemma generatesSub_X'_restrict (v : Carrier) :
    carrierFS.GeneratesSub {X', V'} ((ofSetoid X').restrict {x | Y' x v}) := by
  refine (carrierFS.generatesSub_iff_rel _ _).2 ?_
  rw [dom_restrict_ofSetoid]
  intro s hs t _
  have h1 : (carrierFS.chimera {X', V'} s t).1 = s.1 :=
    carrierFS.chimera_rel_of_mem s t memX' (Or.inl rfl)
  have h2 : ((carrierFS.chimera {X', V'} s t).1 == (carrierFS.chimera {X', V'} s t).2.1)
      = (s.1 == s.2.1) := carrierFS.chimera_rel_of_mem s t memV' (Or.inr rfl)
  have h3 : (carrierFS.chimera {X', V'} s t).2.1 = s.2.1 := bool_snd_eq _ _ _ _ h1 h2
  exact ⟨show (carrierFS.chimera {X', V'} s t).2.1 = v.2.1 from h3.trans hs, hs, h1⟩

lemma generatesSub_V'_restrict (v : Carrier) :
    carrierFS.GeneratesSub {X', V'} ((ofSetoid V').restrict {x | Y' x v}) := by
  refine (carrierFS.generatesSub_iff_rel _ _).2 ?_
  rw [dom_restrict_ofSetoid]
  intro s hs t _
  have h1 : (carrierFS.chimera {X', V'} s t).1 = s.1 :=
    carrierFS.chimera_rel_of_mem s t memX' (Or.inl rfl)
  have h2 : ((carrierFS.chimera {X', V'} s t).1 == (carrierFS.chimera {X', V'} s t).2.1)
      = (s.1 == s.2.1) := carrierFS.chimera_rel_of_mem s t memV' (Or.inr rfl)
  have h3 : (carrierFS.chimera {X', V'} s t).2.1 = s.2.1 := bool_snd_eq _ _ _ _ h1 h2
  exact ⟨show (carrierFS.chimera {X', V'} s t).2.1 = v.2.1 from h3.trans hs, hs, h2⟩

lemma generatesSub_ZP_restrict (v : Carrier) :
    carrierFS.GeneratesSub {Z'} ((ofSetoid ZP).restrict {x | Y' x v}) := by
  refine (carrierFS.generatesSub_iff_rel _ _).2 ?_
  rw [dom_restrict_ofSetoid]
  intro s hs t ht
  have h1 : (carrierFS.chimera {Z'} s t).2.2 = s.2.2 :=
    carrierFS.chimera_rel_of_mem s t memZ' rfl
  have h2 : (carrierFS.chimera {Z'} s t).1 = t.1 :=
    carrierFS.chimera_rel_of_notMem s t memX' (fun hh => X'_ne_Z' hh)
  have h3 : ((carrierFS.chimera {Z'} s t).1 == (carrierFS.chimera {Z'} s t).2.1)
      = (t.1 == t.2.1) := carrierFS.chimera_rel_of_notMem s t memV' (fun hh => V'_ne_Z' hh)
  have h4 : (carrierFS.chimera {Z'} s t).2.1 = t.2.1 := bool_snd_eq _ _ _ _ h2 h3
  have hst : t.2.1 = s.2.1 :=
    (show t.2.1 = v.2.1 from ht).trans (show s.2.1 = v.2.1 from hs).symm
  have h5 : (carrierFS.chimera {Z'} s t).2.1 = s.2.1 := h4.trans hst
  refine ⟨show (carrierFS.chimera {Z'} s t).2.1 = v.2.1 from h5.trans hs, hs, ?_⟩
  show (carrierFS.chimera {Z'} s t).2.2.getD (carrierFS.chimera {Z'} s t).2.1 = s.2.2.getD s.2.1
  rw [h1, h5]

lemma historySub_X'_restrict (v : Carrier) :
    carrierFS.historySub ((ofSetoid X').restrict {x | Y' x v}) ⊆ {X', V'} :=
  carrierFS.historySub_subset_of_generatesSub pair_XV_subset (generatesSub_X'_restrict v)

lemma historySub_V'_restrict (v : Carrier) :
    carrierFS.historySub ((ofSetoid V').restrict {x | Y' x v}) ⊆ {X', V'} :=
  carrierFS.historySub_subset_of_generatesSub pair_XV_subset (generatesSub_V'_restrict v)

lemma historySub_ZP_restrict (v : Carrier) :
    carrierFS.historySub ((ofSetoid ZP).restrict {x | Y' x v}) ⊆ {Z'} :=
  carrierFS.historySub_subset_of_generatesSub (Set.singleton_subset_iff.2 memZ')
    (generatesSub_ZP_restrict v)

/-! #### The six verdicts -/

lemma orth_X'_V' : carrierFS.Orthogonal X' V' := by
  rw [FactoredSet.orthogonal_def, history_X', history_V']
  refine Set.eq_empty_iff_forall_notMem.2 ?_
  rintro b ⟨hb1, hb2⟩
  simp only [Set.mem_singleton_iff] at hb1 hb2
  subst hb1
  exact X'_ne_V' hb2

lemma orth_X'_ZP : carrierFS.OrthogonalGiven X' ZP Y' := by
  rintro z ⟨v, rfl⟩
  refine (carrierFS.orthogonalGivenSet_def X' ZP _).2 ?_
  refine Set.eq_empty_iff_forall_notMem.2 ?_
  rintro b ⟨hb1, hb2⟩
  have h1 := historySub_X'_restrict v hb1
  have h2 := historySub_ZP_restrict v hb2
  simp only [Set.mem_singleton_iff] at h2
  subst h2
  rcases h1 with h | h
  · exact X'_ne_Z' h.symm
  · exact V'_ne_Z' h.symm

lemma orth_V'_ZP : carrierFS.OrthogonalGiven V' ZP Y' := by
  rintro z ⟨v, rfl⟩
  refine (carrierFS.orthogonalGivenSet_def V' ZP _).2 ?_
  refine Set.eq_empty_iff_forall_notMem.2 ?_
  rintro b ⟨hb1, hb2⟩
  have h1 := historySub_V'_restrict v hb1
  have h2 := historySub_ZP_restrict v hb2
  simp only [Set.mem_singleton_iff] at h2
  subst h2
  rcases h1 with h | h
  · exact X'_ne_Z' h.symm
  · exact V'_ne_Z' h.symm

lemma not_orth_X'_ZP : ¬ carrierFS.Orthogonal X' ZP := by
  rw [FactoredSet.orthogonal_def, history_X', history_ZP]
  intro h
  have hmem : X' ∈ ({X'} : Set (Setoid Carrier)) ∩ carrierFS.B := ⟨rfl, memX'⟩
  rw [h] at hmem
  exact hmem

lemma not_orth_V'_ZP : ¬ carrierFS.Orthogonal V' ZP := by
  rw [FactoredSet.orthogonal_def, history_V', history_ZP]
  intro h
  have hmem : V' ∈ ({V'} : Set (Setoid Carrier)) ∩ carrierFS.B := ⟨rfl, memV'⟩
  rw [h] at hmem
  exact hmem

lemma not_orth_ZP_ZP : ¬ carrierFS.OrthogonalGiven ZP ZP Y' := by
  intro h
  have hz := h {x | Y' x ((false, false, none) : Carrier)} ⟨(false, false, none), rfl⟩
  rw [carrierFS.orthogonalGivenSet_def, Set.inter_self] at hz
  have hind := (carrierFS.historySub_spec ((ofSetoid ZP).restrict
    {x | Y' x ((false, false, none) : Carrier)})
    ((ofSetoid ZP).restrict {x | Y' x ((false, false, none) : Carrier)})
    ((ofSetoid ZP).restrict {x | Y' x ((false, false, none) : Carrier)}) rfl).2.2.2.1.1 hz
  have hdom : ((ofSetoid ZP).restrict {x | Y' x ((false, false, none) : Carrier)}).dom
      = {x | Y' x ((false, false, none) : Carrier)} := dom_restrict_ofSetoid _ _
  have hA : (ofSetoid ZP).restrict {x | Y' x ((false, false, none) : Carrier)}
      (false, false, none) (false, false, some true) := by
    rw [hind, hdom]
    exact ⟨rfl, rfl⟩
  exact Bool.noConfusion (show (false : Bool) = true from hA.2.2)

/-! #### The model models `D` -/

lemma models_D : OrthDatabase.Models model D := by
  intro A B C
  constructor
  · intro h
    have h' : (A, B, C) = (X, V, ⊤) ∨ (A, B, C) = (X, Z, Y) ∨ (A, B, C) = (V, Z, Y) := h
    rcases h' with h' | h' | h'
    · simp only [Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl, rfl⟩ := h'
      rw [pullback_X, pullback_V, Model.pullback_top]
      exact (carrierFS.orthogonal_iff_orthogonalGiven_top X' V').1 orth_X'_V'
    · simp only [Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl, rfl⟩ := h'
      rw [pullback_X, pullback_Z, pullback_Y]
      exact orth_X'_ZP
    · simp only [Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl, rfl⟩ := h'
      rw [pullback_V, pullback_Z, pullback_Y]
      exact orth_V'_ZP
  · intro h
    have h' : (A, B, C) = (X, Z, ⊤) ∨ (A, B, C) = (V, Z, ⊤) ∨ (A, B, C) = (Z, Z, Y) := h
    rcases h' with h' | h' | h'
    · simp only [Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl, rfl⟩ := h'
      rw [pullback_X, pullback_Z, Model.pullback_top]
      exact fun hc => not_orth_X'_ZP ((carrierFS.orthogonal_iff_orthogonalGiven_top X' ZP).2 hc)
    · simp only [Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl, rfl⟩ := h'
      rw [pullback_V, pullback_Z, Model.pullback_top]
      exact fun hc => not_orth_V'_ZP ((carrierFS.orthogonal_iff_orthogonalGiven_top V' ZP).2 hc)
    · simp only [Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl, rfl⟩ := h'
      rw [pullback_Z, pullback_Y]
      exact not_orth_ZP_ZP

/-- **Proposition 35** — Example 2's database is consistent: the paper's twelve-point model
(three-bit strings plus two-bit strings, factored by first bit, agreement of the first two
bits, and the third coordinate) models it.

Paper node: Proposition 35 (§6.2). -/
theorem D_consistent : D.Consistent := ⟨model, models_D⟩

/-! ### Proposition 36

Everything below quantifies over an *arbitrary* model `(F, f)` of `D`; write
`H_A = h^F(f⁻¹(A))`.  The first half is Proposition 34's pattern: `H_Y = H_X ∪ H_V` from
the three coarsenings above, the union being disjoint by `X ⊥_D V | {Ω}`, and `H_V ≠ {}`
by `¬(V ⊥_D Z | {Ω})`.

The second half is the paper's long argument, in five steps: the four points `r_{ij} =
χ^F_{H_X}(s_i, t_j)` realizing every (first bit, agreement) pair; the resulting dichotomy
"either `h^F(A) ∩ H_Y = {}` or `H_Y ⊆ h^F(A)`" for a subpartition `A` of a `y`-block;
`h^F(f⁻¹(X)|y) = H_Y`, whence `h^F(f⁻¹(Z)|y) ∩ H_Y = {}` from `X ⊥_D Z | Y`; the `p₀`/`p₁`
splice giving `H_Y ⊆ H_Z`; and strictness from `¬(Z ⊥_D Z | Y)`.

The printed proof miscites the database twice — `X ⊥_D Y | {Ω}` for the disjointness (`O`
contains `(X,V,{Ω})`) and `¬(Y ⊥_D Z | {Ω})` for `H_V ≠ {}` (`N` contains `(V,Z,{Ω})`) —
and writes `h_Z` for `H_Z` once.  None changes a statement; all three are recorded as
E4–E6 in `notes/paper-errata.md`. -/

section Prop36

variable {M : Model Ω}

/-- The three non-orthogonalities of `N` give a nonempty intersection of histories. -/
private lemma inter_hist_nonempty_of_notOrth (hM : OrthDatabase.Models M D) {A B : Setoid Ω}
    (hAB : D.NotOrth A B ⊤) :
    (M.F.history (M.pullback A) ∩ M.F.history (M.pullback B)).Nonempty := by
  have h := (hM A B ⊤).2 hAB
  rw [Model.pullback_top] at h
  have h' : ¬ M.F.Orthogonal (M.pullback A) (M.pullback B) := fun hc =>
    h ((M.F.orthogonal_iff_orthogonalGiven_top _ _).1 hc)
  rw [FactoredSet.orthogonal_def] at h'
  exact Set.nonempty_iff_ne_empty.2 h'

private lemma orth_XV (hM : OrthDatabase.Models M D) :
    M.F.history (M.pullback X) ∩ M.F.history (M.pullback V) = ∅ := by
  have h := (hM X V ⊤).1 (Or.inl rfl)
  rw [Model.pullback_top] at h
  exact (M.F.orthogonal_iff_orthogonalGiven_top _ _).2 h

private lemma notMem_histV_of_mem_histX (hM : OrthDatabase.Models M D) {b : Setoid M.S}
    (hbX : b ∈ M.F.history (M.pullback X)) : b ∉ M.F.history (M.pullback V) := by
  intro hbV
  have : b ∈ M.F.history (M.pullback X) ∩ M.F.history (M.pullback V) := ⟨hbX, hbV⟩
  rw [orth_XV hM] at this
  exact this

private lemma histX_inter_histZ_nonempty (hM : OrthDatabase.Models M D) :
    (M.F.history (M.pullback X) ∩ M.F.history (M.pullback Z)).Nonempty :=
  inter_hist_nonempty_of_notOrth hM (Or.inl rfl)

private lemma histX_nonempty (hM : OrthDatabase.Models M D) :
    (M.F.history (M.pullback X)).Nonempty :=
  let ⟨b, hb⟩ := histX_inter_histZ_nonempty hM; ⟨b, hb.1⟩

private lemma histV_nonempty (hM : OrthDatabase.Models M D) :
    (M.F.history (M.pullback V)).Nonempty :=
  let ⟨b, hb⟩ := inter_hist_nonempty_of_notOrth (A := V) (B := Z) hM (Or.inr (Or.inl rfl))
  ⟨b, hb.1⟩

/-- `H_Y = H_X ∪ H_V`. -/
private lemma histY_eq (hM : OrthDatabase.Models M D) :
    M.F.history (M.pullback Y)
      = M.F.history (M.pullback X) ∪ M.F.history (M.pullback V) := by
  have hunion : ∀ A B : Setoid M.S,
      M.F.history (A ⊓ B) = M.F.history A ∪ M.F.history B := fun A B =>
    (M.F.history_spec A B).2.1
  have hXsub : M.F.history (M.pullback X) ⊆ M.F.history (M.pullback Y) := by
    have h1 := (M.F.history_spec (M.pullback X) (M.pullback Y ⊓ M.pullback V)).1 pb_inf_YV_le_X
    intro b hb
    rcases (hunion _ _ ▸ h1 hb : b ∈ _ ∪ _) with h | h
    · exact h
    · exact absurd h (notMem_histV_of_mem_histX hM hb)
  have hVsub : M.F.history (M.pullback V) ⊆ M.F.history (M.pullback Y) := by
    have h1 := (M.F.history_spec (M.pullback V) (M.pullback X ⊓ M.pullback Y)).1 pb_inf_XY_le_V
    intro b hb
    rcases (hunion _ _ ▸ h1 hb : b ∈ _ ∪ _) with h | h
    · exact absurd hb (notMem_histV_of_mem_histX hM h)
    · exact h
  refine Set.Subset.antisymm ?_ (Set.union_subset hXsub hVsub)
  have h1 := (M.F.history_spec (M.pullback Y) (M.pullback X ⊓ M.pullback V)).1 pb_inf_XV_le_Y
  intro b hb
  exact hunion _ _ ▸ h1 hb

/-- The first half of Proposition 36 on a fixed model: `f⁻¹(X) <^F f⁻¹(Y)`. -/
private lemma strictlyBefore_X_Y (hM : OrthDatabase.Models M D) :
    M.F.StrictlyBefore (M.pullback X) (M.pullback Y) := by
  obtain ⟨b, hb⟩ := histV_nonempty hM
  refine ⟨(histY_eq hM) ▸ Set.subset_union_left, fun hsub => ?_⟩
  have hbY : b ∈ M.F.history (M.pullback Y) := (histY_eq hM) ▸ Or.inr hb
  exact notMem_histV_of_mem_histX hM (hsub hbY) hb

/-! #### The `r_{ij}` family -/

/-- A pair of points separated by a `Bool`-valued statistic, re-indexed by that statistic. -/
private lemma exists_boolIndexed {P : M.S → Bool} {s₀ s₁ : M.S} {b : Setoid M.S}
    (hs : ∀ c ∈ M.F.B, c ≠ b → c s₀ s₁) (hne : P s₀ ≠ P s₁) :
    ∃ g : Bool → M.S, (∀ i, P (g i) = i) ∧ ∀ i i', ∀ c ∈ M.F.B, c ≠ b → c (g i) (g i') := by
  refine ⟨fun i => if P s₀ = i then s₀ else s₁, fun i => ?_, fun i i' c hc hcb => ?_⟩
  · show P (if P s₀ = i then s₀ else s₁) = i
    by_cases h : P s₀ = i
    · rw [if_pos h]; exact h
    · rw [if_neg h]
      revert h hne
      cases P s₀ <;> cases P s₁ <;> cases i <;> simp
  · show c (if P s₀ = i then s₀ else s₁) (if P s₀ = i' then s₀ else s₁)
    by_cases h : P s₀ = i
    · rw [if_pos h]
      by_cases h' : P s₀ = i'
      · rw [if_pos h']
      · rw [if_neg h']; exact hs c hc hcb
    · rw [if_neg h]
      by_cases h' : P s₀ = i'
      · rw [if_pos h']; exact c.symm' (hs c hc hcb)
      · rw [if_neg h']

/-- The paper's `r_{ij} = χ^F_{H_X}(s_i, t_j)`: four points realizing every combination of a
first bit and an agreement bit, spliced so that `b_X` sees only `i` and `b_V` only `j`. -/
private lemma exists_rFamily (hM : OrthDatabase.Models M D) {bX bV : Setoid M.S}
    (hbX : bX ∈ M.F.history (M.pullback X)) (hbV : bV ∈ M.F.history (M.pullback V)) :
    ∃ r : Bool → Bool → M.S,
      (∀ i j, (M.f (r i j)).1 = i) ∧
      (∀ i j, ((M.f (r i j)).1 == (M.f (r i j)).2.1) = j) ∧
      (∀ b ∈ M.F.B, b ≠ bX → b ≠ bV → ∀ i j i' j', b (r i j) (r i' j')) ∧
      (∀ i j j', bX (r i j) (r i j')) ∧
      (∀ i i' j, bV (r i j) (r i' j)) := by
  obtain ⟨s₀, s₁, hs, hsX⟩ := M.F.exists_not_rel_of_mem_history hbX
  obtain ⟨t₀, t₁, ht, htV⟩ := M.F.exists_not_rel_of_mem_history hbV
  obtain ⟨sf, hsf1, hsf2⟩ := exists_boolIndexed (P := fun s => (M.f s).1) hs hsX
  obtain ⟨tf, htf1, htf2⟩ :=
    exists_boolIndexed (P := fun t => ((M.f t).1 == (M.f t).2.1)) ht htV
  have hmem : ∀ (b : Setoid M.S), b ∈ M.F.history (M.pullback X) →
      ∀ i j, b (M.F.chimera (M.F.history (M.pullback X)) (sf i) (tf j)) (sf i) :=
    fun b hb i j => M.F.chimera_rel_of_mem _ _ (M.F.history_subset _ hb) hb
  have hnot : ∀ (b : Setoid M.S), b ∈ M.F.B → b ∉ M.F.history (M.pullback X) →
      ∀ i j, b (M.F.chimera (M.F.history (M.pullback X)) (sf i) (tf j)) (tf j) :=
    fun b hb hb' i j => M.F.chimera_rel_of_notMem _ _ hb hb'
  have hbVnot : bV ∉ M.F.history (M.pullback X) := fun h =>
    notMem_histV_of_mem_histX hM h hbV
  refine ⟨fun i j => M.F.chimera (M.F.history (M.pullback X)) (sf i) (tf j), ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    have : M.pullback X (M.F.chimera (M.F.history (M.pullback X)) (sf i) (tf j)) (sf i) :=
      M.F.commonRefinement_history_le _ (commonRefinement_iff.2 fun b hb => hmem b hb i j)
    exact (this : _ = _).trans (hsf1 i)
  · intro i j
    have : M.pullback V (M.F.chimera (M.F.history (M.pullback X)) (sf i) (tf j)) (tf j) :=
      M.F.commonRefinement_history_le _ (commonRefinement_iff.2 fun b hb =>
        hnot b (M.F.history_subset _ hb) (fun h => notMem_histV_of_mem_histX hM h hb) i j)
    exact (this : _ = _).trans (htf1 j)
  · intro b hb hbX' hbV' i j i' j'
    by_cases hbH : b ∈ M.F.history (M.pullback X)
    · exact b.trans' (hmem b hbH i j)
        (b.trans' (hsf2 i i' b hb hbX') (b.symm' (hmem b hbH i' j')))
    · exact b.trans' (hnot b hb hbH i j)
        (b.trans' (htf2 j j' b hb hbV') (b.symm' (hnot b hb hbH i' j')))
  · exact fun i j j' => bX.trans' (hmem bX hbX i j) (bX.symm' (hmem bX hbX i j'))
  · exact fun i i' j => bV.trans' (hnot bV (M.F.history_subset _ hbV) hbVnot i j)
      (bV.symm' (hnot bV (M.F.history_subset _ hbV) hbVnot i' j))

/-- The second bit of `f(r_{ij})` is `i == j`. -/
private lemma snd_eq_beq {w : M.S} {i j : Bool} (h1 : (M.f w).1 = i)
    (h2 : ((M.f w).1 == (M.f w).2.1) = j) : (M.f w).2.1 = (i == j) := by
  subst h1
  revert h2
  cases (M.f w).1 <;> cases (M.f w).2.1 <;> cases j <;> decide

/-- Every combination of a first bit and a second bit is realized in `S`. -/
private lemma exists_point (hM : OrthDatabase.Models M D) (a b : Bool) :
    ∃ w : M.S, (M.f w).1 = a ∧ (M.f w).2.1 = b := by
  obtain ⟨bX, hbX⟩ := histX_nonempty hM
  obtain ⟨bV, hbV⟩ := histV_nonempty hM
  obtain ⟨r, h1, h2, -, -, -⟩ := exists_rFamily hM hbX hbV
  refine ⟨r a (a == b), h1 _ _, ?_⟩
  have := snd_eq_beq (h1 a (a == b)) (h2 a (a == b))
  rw [this]
  cases a <;> cases b <;> decide

/-! #### The chimera argument on a block of `f⁻¹(Y)` -/

/-- The paper's "either `h^F(A) ∩ H_Y = {}` or `H_Y ⊆ h^F(A)`", in the form it is proved:
a `C` meeting one of `H_X`, `H_V` while missing a factor of the other moves some pair of
points out of its `f⁻¹(Y)`-block. -/
private lemma exists_chimera_notMem (hM : OrthDatabase.Models M D) {C : Set (Setoid M.S)}
    (hsplit : ((∃ b ∈ M.F.history (M.pullback X), b ∈ C) ∧
                ∃ b ∈ M.F.history (M.pullback V), b ∉ C) ∨
              ((∃ b ∈ M.F.history (M.pullback V), b ∈ C) ∧
                ∃ b ∈ M.F.history (M.pullback X), b ∉ C))
    {y : Set M.S} (hy : y ∈ (M.pullback Y).classes) :
    ∃ u ∈ y, ∃ v ∈ y, M.F.chimera C u v ∉ y := by
  obtain ⟨v, rfl⟩ := hy
  have hb1 : ∀ c : Bool, (true == c) = c := by decide
  have hb2 : ∀ c : Bool, (false == !c) = c := by decide
  have hb3 : ∀ c : Bool, ¬ ((true == !c) = c) := by decide
  have hb4 : ∀ c : Bool, ¬ ((false == c) = c) := by decide
  obtain ⟨bX, hbX, bV, hbV, hchim⟩ :
      ∃ bX ∈ M.F.history (M.pullback X), ∃ bV ∈ M.F.history (M.pullback V),
        ∀ r : Bool → Bool → M.S,
          (∀ b ∈ M.F.B, b ≠ bX → b ≠ bV → ∀ i j i' j', b (r i j) (r i' j')) →
          (∀ i j j', bX (r i j) (r i j')) → (∀ i i' j, bV (r i j) (r i' j)) →
          ∀ i j i' j', M.F.chimera C (r i j) (r i' j') = r i j' ∨
            M.F.chimera C (r i j) (r i' j') = r i' j := by
    rcases hsplit with ⟨⟨bX, hbX, hbXC⟩, ⟨bV, hbV, hbVC⟩⟩ | ⟨⟨bV, hbV, hbVC⟩, ⟨bX, hbX, hbXC⟩⟩
    · refine ⟨bX, hbX, bV, hbV, fun r h3 h4 h5 i j i' j' => Or.inl ?_⟩
      refine M.F.eq_of_forall_rel fun b hb => ?_
      by_cases hb1 : b = bX
      · subst hb1; exact b.trans' (M.F.chimera_rel_of_mem _ _ hb hbXC) (h4 i j j')
      by_cases hb2 : b = bV
      · subst hb2; exact b.trans' (M.F.chimera_rel_of_notMem _ _ hb hbVC) (h5 i' i j')
      by_cases hbC : b ∈ C
      · exact b.trans' (M.F.chimera_rel_of_mem _ _ hb hbC) (h3 b hb hb1 hb2 i j i j')
      · exact b.trans' (M.F.chimera_rel_of_notMem _ _ hb hbC) (h3 b hb hb1 hb2 i' j' i j')
    · refine ⟨bX, hbX, bV, hbV, fun r h3 h4 h5 i j i' j' => Or.inr ?_⟩
      refine M.F.eq_of_forall_rel fun b hb => ?_
      by_cases hb1 : b = bX
      · subst hb1; exact b.trans' (M.F.chimera_rel_of_notMem _ _ hb hbXC) (h4 i' j' j)
      by_cases hb2 : b = bV
      · subst hb2; exact b.trans' (M.F.chimera_rel_of_mem _ _ hb hbVC) (h5 i i' j)
      by_cases hbC : b ∈ C
      · exact b.trans' (M.F.chimera_rel_of_mem _ _ hb hbC) (h3 b hb hb1 hb2 i j i' j)
      · exact b.trans' (M.F.chimera_rel_of_notMem _ _ hb hbC) (h3 b hb hb1 hb2 i' j' i' j)
  obtain ⟨r, h1, h2, h3, h4, h5⟩ := exists_rFamily hM hbX hbV
  have hsnd : ∀ i j, (M.f (r i j)).2.1 = (i == j) := fun i j => snd_eq_beq (h1 i j) (h2 i j)
  refine ⟨r true (M.f v).2.1, ?_, r false (!(M.f v).2.1), ?_, ?_⟩
  · show (M.f (r true (M.f v).2.1)).2.1 = (M.f v).2.1
    rw [hsnd]; exact hb1 _
  · show (M.f (r false (!(M.f v).2.1))).2.1 = (M.f v).2.1
    rw [hsnd]; exact hb2 _
  · intro hmem
    have hmem' : (M.f (M.F.chimera C (r true (M.f v).2.1)
        (r false (!(M.f v).2.1)))).2.1 = (M.f v).2.1 := hmem
    rcases hchim r h3 h4 h5 true (M.f v).2.1 false (!(M.f v).2.1) with he | he <;>
      rw [he, hsnd] at hmem'
    · exact hb3 _ hmem'
    · exact hb4 _ hmem'

/-! #### Restricted histories on a block of `f⁻¹(Y)` -/

/-- The paper's "either `h^F(A) ∩ H_Y = {}`, or `H_Y ⊆ h^F(A)`", for a subpartition `A`
whose domain is a block of `f⁻¹(Y)`. -/
private lemma histY_subset_of_inter (hM : OrthDatabase.Models M D) {A : Subpartition M.S}
    {y : Set M.S} (hy : y ∈ (M.pullback Y).classes) (hdom : A.dom = y)
    (hne : (M.F.historySub A ∩ M.F.history (M.pullback Y)).Nonempty) :
    M.F.history (M.pullback Y) ⊆ M.F.historySub A := by
  have hclosed : ∀ u ∈ y, ∀ v ∈ y, M.F.chimera (M.F.historySub A) u v ∈ y := by
    intro u hu v hv
    have h := (M.F.generatesSub_iff_rel (M.F.historySub A) A).1
      (M.F.generatesSub_historySub A) u (by rw [hdom]; exact hu) v (by rw [hdom]; exact hv)
    rw [← hdom]
    exact Subpartition.mem_dom_of_rel h
  have hnosplit : ¬ (((∃ b ∈ M.F.history (M.pullback X), b ∈ M.F.historySub A) ∧
        ∃ b ∈ M.F.history (M.pullback V), b ∉ M.F.historySub A) ∨
      ((∃ b ∈ M.F.history (M.pullback V), b ∈ M.F.historySub A) ∧
        ∃ b ∈ M.F.history (M.pullback X), b ∉ M.F.historySub A)) := by
    intro hs
    obtain ⟨u, hu, v, hv, hnot⟩ := exists_chimera_notMem hM hs hy
    exact hnot (hclosed u hu v hv)
  have hVsub : (∃ b ∈ M.F.history (M.pullback X), b ∈ M.F.historySub A) →
      M.F.history (M.pullback V) ⊆ M.F.historySub A := by
    intro hx b hb
    by_contra hb'
    exact hnosplit (Or.inl ⟨hx, ⟨b, hb, hb'⟩⟩)
  have hXsub : (∃ b ∈ M.F.history (M.pullback V), b ∈ M.F.historySub A) →
      M.F.history (M.pullback X) ⊆ M.F.historySub A := by
    intro hv b hb
    by_contra hb'
    exact hnosplit (Or.inr ⟨hv, ⟨b, hb, hb'⟩⟩)
  obtain ⟨b, hbA, hbY⟩ := hne
  rw [histY_eq hM]
  rcases (histY_eq hM ▸ hbY : b ∈ _ ∪ _) with h | h
  · obtain ⟨c, hc⟩ := histV_nonempty hM
    have h1 := hVsub ⟨b, h, hbA⟩
    exact Set.union_subset (hXsub ⟨c, hc, h1 hc⟩) h1
  · obtain ⟨c, hc⟩ := histX_nonempty hM
    have h1 := hXsub ⟨b, h, hbA⟩
    exact Set.union_subset h1 (hVsub ⟨c, hc, h1 hc⟩)

/-- `h^F(W|y) ⊆ H_Y ∪ h^F(W)` for any `W` and any block `y` of `f⁻¹(Y)` (Lemma 2). -/
private lemma histSub_restrict_subset (W : Setoid M.S) {y : Set M.S}
    (hy : y ∈ (M.pullback Y).classes) :
    M.F.historySub ((Subpartition.ofSetoid W).restrict y) ⊆
      M.F.history (M.pullback Y) ∪ M.F.history W := by
  obtain ⟨v, rfl⟩ := hy
  have hE : (Subpartition.ofSetoid (M.pullback Y)).dom = (Subpartition.ofSetoid W).dom := by
    simp
  have h2 := M.F.historySub_inf_eq (X := Subpartition.ofSetoid (M.pullback Y))
    (Y := Subpartition.ofSetoid W) hE
  have hinf : (Subpartition.ofSetoid (M.pullback Y) ⊓ Subpartition.ofSetoid W)
      = Subpartition.ofSetoid (M.pullback Y ⊓ W) := Subpartition.ext fun _ _ => Iff.rfl
  have hleft : M.F.historySub
      (Subpartition.ofSetoid (M.pullback Y) ⊓ Subpartition.ofSetoid W)
      = M.F.history (M.pullback Y) ∪ M.F.history W := by
    rw [hinf, M.F.historySub_isLeast_and_eq_history.2,
      (M.F.history_spec (M.pullback Y) W).2.1]
  intro b hb
  rw [← hleft, h2]
  refine Or.inr ?_
  simp only [Set.mem_iUnion, exists_prop]
  exact ⟨v, by simp, hb⟩

/-- Two points of a block of `f⁻¹(Y)` that `f⁻¹(X)` separates. -/
private lemma exists_pair_in_block (hM : OrthDatabase.Models M D) {y : Set M.S}
    (hy : y ∈ (M.pullback Y).classes) : ∃ u ∈ y, ∃ v ∈ y, ¬ M.pullback X u v := by
  obtain ⟨v, rfl⟩ := hy
  obtain ⟨u₀, hu₀1, hu₀2⟩ := exists_point hM true (M.f v).2.1
  obtain ⟨u₁, hu₁1, hu₁2⟩ := exists_point hM false (M.f v).2.1
  exact ⟨u₀, hu₀2, u₁, hu₁2, by rw [pbX_iff, hu₀1, hu₁1]; exact Bool.noConfusion⟩

/-- The complement of a block of `f⁻¹(Y)` is again a block: `Y` has two parts. -/
private lemma compl_mem_classes (hM : OrthDatabase.Models M D) {y : Set M.S}
    (hy : y ∈ (M.pullback Y).classes) : yᶜ ∈ (M.pullback Y).classes := by
  obtain ⟨v, rfl⟩ := hy
  obtain ⟨w, -, hw2⟩ := exists_point hM true (!(M.f v).2.1)
  refine ⟨w, ?_⟩
  ext u
  show ¬ ((M.f u).2.1 = (M.f v).2.1) ↔ (M.f u).2.1 = (M.f w).2.1
  rw [hw2]
  cases (M.f u).2.1 <;> cases (M.f v).2.1 <;> simp

/-- `h^F(f⁻¹(X)|y) = H_Y` for every block `y` of `f⁻¹(Y)`. -/
private lemma histSub_restrict_X_eq (hM : OrthDatabase.Models M D) {y : Set M.S}
    (hy : y ∈ (M.pullback Y).classes) :
    M.F.historySub ((Subpartition.ofSetoid (M.pullback X)).restrict y)
      = M.F.history (M.pullback Y) := by
  have hsub : M.F.historySub ((Subpartition.ofSetoid (M.pullback X)).restrict y)
      ⊆ M.F.history (M.pullback Y) := by
    intro b hb
    rcases histSub_restrict_subset (M.pullback X) hy hb with h | h
    · exact h
    · exact (histY_eq hM) ▸ Or.inl h
  refine Set.Subset.antisymm hsub ?_
  obtain ⟨u, hu, v, hv, huv⟩ := exists_pair_in_block hM hy
  have hne : (M.F.historySub ((Subpartition.ofSetoid (M.pullback X)).restrict y)).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h0
    have hind := ((M.F.historySub_spec ((Subpartition.ofSetoid (M.pullback X)).restrict y)
      ((Subpartition.ofSetoid (M.pullback X)).restrict y)
      ((Subpartition.ofSetoid (M.pullback X)).restrict y) rfl).2.2.2.1).1 h0
    have : ((Subpartition.ofSetoid (M.pullback X)).restrict y) u v := by
      rw [hind]
      exact ⟨by simpa using hu, by simpa using hv⟩
    exact huv this.2.2
  obtain ⟨b, hb⟩ := hne
  exact histY_subset_of_inter hM hy (by simp) ⟨b, hb, hsub hb⟩

/-- `h^F(f⁻¹(Z)|y) ∩ H_Y = {}` for every block `y` of `f⁻¹(Y)`, from `X ⊥_D Z | Y`. -/
private lemma histSub_restrict_Z_disjoint (hM : OrthDatabase.Models M D) {y : Set M.S}
    (hy : y ∈ (M.pullback Y).classes) :
    M.F.historySub ((Subpartition.ofSetoid (M.pullback Z)).restrict y)
      ∩ M.F.history (M.pullback Y) = ∅ := by
  have h := (hM X Z Y).1 (Or.inr (Or.inl rfl)) y hy
  rw [FactoredSet.orthogonalGivenSet_def, histSub_restrict_X_eq hM hy, Set.inter_comm] at h
  exact h

/-! #### `H_Y ⊆ H_Z` -/

/-- The paper's `p₀`/`p₁` construction, with the block containing `u₀` fixed and `q₀`
chosen inside it. -/
private lemma mem_histZ_aux (hM : OrthDatabase.Models M D) {bZ bY : Setoid M.S}
    {u₀ u₁ q₀ q₁ : M.S} (hbZX : bZ ∈ M.F.history (M.pullback X))
    (hu : ∀ c ∈ M.F.B, c ≠ bZ → c u₀ u₁) (hu' : ¬ M.pullback Z u₀ u₁)
    (hq : ∀ c ∈ M.F.B, c ≠ bY → c q₀ q₁) (hq' : ¬ M.pullback Y q₀ q₁)
    (hq₀ : M.pullback Y q₀ u₀) : bY ∈ M.F.history (M.pullback Z) := by
  have hy : {w : M.S | M.pullback Y w u₀} ∈ (M.pullback Y).classes := ⟨u₀, rfl⟩
  have hu₀y : u₀ ∈ {w : M.S | M.pullback Y w u₀} := (M.pullback Y).refl' u₀
  have hin : ∀ (q : M.S), ∀ b ∈ M.F.history (M.pullback Y),
      b (M.F.chimera (M.F.history (M.pullback Y)) q u₀) q :=
    fun q b hb => M.F.chimera_rel_of_mem _ _ (M.F.history_subset _ hb) hb
  have hout : ∀ (q : M.S), ∀ b ∈ M.F.B, b ∉ M.F.history (M.pullback Y) →
      b (M.F.chimera (M.F.history (M.pullback Y)) q u₀) u₀ :=
    fun q b hb hb' => M.F.chimera_rel_of_notMem _ _ hb hb'
  have hpY : ∀ q : M.S, M.pullback Y (M.F.chimera (M.F.history (M.pullback Y)) q u₀) q :=
    fun q => M.F.commonRefinement_history_le _ (commonRefinement_iff.2 (hin q))
  have hbZY : bZ ∈ M.F.history (M.pullback Y) := (histY_eq hM) ▸ Or.inl hbZX
  have hu_out : ∀ b ∈ M.F.B, b ∉ M.F.history (M.pullback Y) → b u₀ u₁ := fun b hb hb' =>
    hu b hb fun h => hb' (by rw [← h] at hbZY; exact hbZY)
  -- Splicing the `f⁻¹(Z)`-history of a block onto a point that already agrees off `H_Y`.
  have key : ∀ z ∈ (M.pullback Y).classes, ∀ p ∈ z, ∀ w ∈ z,
      (∀ b ∈ M.F.B, b ∉ M.F.history (M.pullback Y) → b p w) → M.pullback Z w p := by
    intro z hz p hp w hw hpw
    have hDzB : M.F.historySub ((Subpartition.ofSetoid (M.pullback Z)).restrict z) ⊆ M.F.B :=
      M.F.historySub_subset _
    have hDzHY : ∀ b ∈ M.F.historySub ((Subpartition.ofSetoid (M.pullback Z)).restrict z),
        b ∉ M.F.history (M.pullback Y) := by
      intro b hb hb'
      have : b ∈ _ ∩ _ := Set.mem_inter hb hb'
      rw [histSub_restrict_Z_disjoint hM hz] at this
      exact this
    have heq : M.F.chimera
        (M.F.historySub ((Subpartition.ofSetoid (M.pullback Z)).restrict z)) p w = w :=
      M.F.chimera_eq_right fun b hb _ => hpw b (hDzB hb) (hDzHY b hb)
    have hgen := (M.F.generatesSub_iff_rel _
      ((Subpartition.ofSetoid (M.pullback Z)).restrict z)).1
      (M.F.generatesSub_historySub _) p (by simpa using hp) w (by simpa using hw)
    rw [heq] at hgen
    exact hgen.2.2
  have hp₀y : M.F.chimera (M.F.history (M.pullback Y)) q₀ u₀ ∈ {w : M.S | M.pullback Y w u₀} :=
    (M.pullback Y).trans' (hpY q₀) hq₀
  have h1 : M.pullback Z u₀ (M.F.chimera (M.F.history (M.pullback Y)) q₀ u₀) :=
    key _ hy _ hp₀y u₀ hu₀y fun b hb hb' => hout q₀ b hb hb'
  have hu₁ny : u₁ ∉ {w : M.S | M.pullback Y w u₀} := by
    intro hu₁y
    have h2 : M.pullback Z u₁ (M.F.chimera (M.F.history (M.pullback Y)) q₀ u₀) :=
      key _ hy _ hp₀y u₁ hu₁y fun b hb hb' =>
        b.trans' (hout q₀ b hb hb') (hu_out b hb hb')
    exact hu' ((M.pullback Z).trans' h1 ((M.pullback Z).symm' h2))
  have hq₁ny : ¬ M.pullback Y q₁ u₀ := fun h =>
    hq' ((M.pullback Y).trans' hq₀ ((M.pullback Y).symm' h))
  have hp₁ny : M.F.chimera (M.F.history (M.pullback Y)) q₁ u₀ ∈ {w : M.S | M.pullback Y w u₀}ᶜ :=
    fun h => hq₁ny ((M.pullback Y).trans' ((M.pullback Y).symm' (hpY q₁)) h)
  have h3 : M.pullback Z u₁ (M.F.chimera (M.F.history (M.pullback Y)) q₁ u₀) :=
    key _ (compl_mem_classes hM hy) _ hp₁ny u₁ hu₁ny fun b hb hb' =>
      b.trans' (hout q₁ b hb hb') (hu_out b hb hb')
  refine M.F.mem_history_of_not_rel (s := M.F.chimera (M.F.history (M.pullback Y)) q₀ u₀)
    (t := M.F.chimera (M.F.history (M.pullback Y)) q₁ u₀) ?_ ?_
  · intro c hc hcY
    by_cases hcHY : c ∈ M.F.history (M.pullback Y)
    · exact c.trans' (hin q₀ c hcHY) (c.trans' (hq c hc hcY) (c.symm' (hin q₁ c hcHY)))
    · exact c.trans' (hout q₀ c hc hcHY) (c.symm' (hout q₁ c hc hcHY))
  · intro h
    exact hu' ((M.pullback Z).trans' h1 ((M.pullback Z).trans' h ((M.pullback Z).symm' h3)))

private lemma histY_subset_histZ (hM : OrthDatabase.Models M D) :
    M.F.history (M.pullback Y) ⊆ M.F.history (M.pullback Z) := by
  intro bY hbY
  obtain ⟨bZ, hbZX, hbZZ⟩ := histX_inter_histZ_nonempty hM
  obtain ⟨u₀, u₁, hu, hu'⟩ := M.F.exists_not_rel_of_mem_history hbZZ
  obtain ⟨q₀, q₁, hq, hq'⟩ := M.F.exists_not_rel_of_mem_history hbY
  by_cases hcase : M.pullback Y q₀ u₀
  · exact mem_histZ_aux hM hbZX hu hu' hq hq' hcase
  · refine mem_histZ_aux hM hbZX hu hu' (fun c hc hcY => c.symm' (hq c hc hcY))
      (fun h => hq' ((M.pullback Y).symm' h)) ?_
    show (M.f q₁).2.1 = (M.f u₀).2.1
    have e1 : ¬ ((M.f q₀).2.1 = (M.f q₁).2.1) := hq'
    have e2 : ¬ ((M.f q₀).2.1 = (M.f u₀).2.1) := hcase
    revert e1 e2
    cases (M.f q₀).2.1 <;> cases (M.f q₁).2.1 <;> cases (M.f u₀).2.1 <;> decide

/-- From `¬(Z ⊥_D Z | Y)`: some block of `f⁻¹(Y)` has a nonempty restricted `Z`-history. -/
private lemma exists_block_histSubZ_nonempty (hM : OrthDatabase.Models M D) :
    ∃ y ∈ (M.pullback Y).classes,
      (M.F.historySub ((Subpartition.ofSetoid (M.pullback Z)).restrict y)).Nonempty := by
  by_contra hcon
  refine (hM Z Z Y).2 (Or.inr (Or.inr rfl)) fun z hz => ?_
  have hempty : M.F.historySub ((Subpartition.ofSetoid (M.pullback Z)).restrict z) = ∅ := by
    rw [← Set.not_nonempty_iff_eq_empty]
    exact fun h => hcon ⟨z, hz, h⟩
  rw [FactoredSet.orthogonalGivenSet_def, hempty, Set.empty_inter]

/-- The second half of Proposition 36 on a fixed model: `f⁻¹(Y) <^F f⁻¹(Z)`. -/
private lemma strictlyBefore_Y_Z (hM : OrthDatabase.Models M D) :
    M.F.StrictlyBefore (M.pullback Y) (M.pullback Z) := by
  refine ⟨histY_subset_histZ hM, fun hsub => ?_⟩
  obtain ⟨y, hy, b, hb⟩ := exists_block_histSubZ_nonempty hM
  have hbHY : b ∉ M.F.history (M.pullback Y) := by
    intro h
    have : b ∈ _ ∩ _ := Set.mem_inter hb h
    rw [histSub_restrict_Z_disjoint hM hy] at this
    exact this
  have hbZ : b ∈ M.F.history (M.pullback Z) := by
    rcases histSub_restrict_subset (M.pullback Z) hy hb with h | h
    · exact absurd h hbHY
    · exact h
  exact hbHY (hsub hbZ)

end Prop36

/-- **Proposition 36** — in Example 2, `X <_D Y <_D Z`.

Paper node: Proposition 36 (§6.2). -/
theorem before_X_Y_Z : D.Before X Y ∧ D.Before Y Z :=
  ⟨fun _ hM => strictlyBefore_X_Y hM, fun _ hM => strictlyBefore_Y_Z hM⟩

/-! ### Client's-eye checks

The model is the paper's — twelve points, the eight three-bit strings plus the four
two-bit ones — and the order Definition 45 infers is a genuine strict order on
`{X, Y, Z}`, not the vacuous relation a database with no model would give. -/

/-- The carrier really has the paper's `8 + 4` points. -/
example : Nat.card Carrier = 12 := by
  rw [Nat.card_eq_fintype_card]
  rfl

/-- Definition 45 composes: `X <_D Z`. -/
example : D.Before X Z := fun M hM =>
  ⟨(before_X_Y_Z.1 M hM).1.trans (before_X_Y_Z.2 M hM).1,
    fun h => (before_X_Y_Z.1 M hM).2 ((before_X_Y_Z.2 M hM).1.trans h)⟩

/-- The inferred order is not vacuous — `Y <_D X` fails — precisely because Proposition 35
supplies a model at which Proposition 36's first inclusion is strict. -/
example : ¬ D.Before Y X := fun h =>
  (h model models_D).2 (before_X_Y_Z.1 model models_D).1

end Example2

end FiniteFactoredSets
