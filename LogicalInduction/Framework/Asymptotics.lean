import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Asymptotics — the limit vocabulary (`dd:asymp`)

The single home of the limit vocabulary the §4 property tail is stated in; nothing
downstream redefines it.

* `AsympEq` (`≈ₙ`), `AsympLE` (`≲ₙ`) and `AsympGE` (`≳ₙ`) are the paper's §2 notation:
  `f ≈ₙ g` is `f n − g n → 0`; `f ≲ₙ g` is "for every `ε > 0`, eventually `f n ≤ g n + ε`";
  `f ≳ₙ g` is `≲ₙ` reversed, i.e. `liminf (f n − g n) ≥ 0`.
* `EventuallyWithin ε f g` is the finite-stage building block, and `ConvergesTo f x` a thin
  alias for `Tendsto f atTop (𝓝 x)`, so no downstream file spells the filter form.

Everything is built on Mathlib's `Tendsto` and `∀ᶠ n in atTop`, in the limiting rather than
the finite-stage form; the finite-stage form appears only where a consumer needs it. The
`thm:perkno` and `thm:tbo` endpoints of `Properties/TimelyLearning.lean`, and the
`thm:wubaff` / `thm:wubexp` family in `Properties/Pseudorandomness.lean` and
`Properties/ExpectationProperties.lean`, take the limiting form.

The workhorses are the ε-characterization `asympEq_iff_eventuallyWithin` and the two-sided
split `asympEq_iff_asympLE_asympGE`. `≈ₙ` is an equivalence, registered with
`@[refl]`/`@[symm]`/`@[trans]` so that `calc`, `rfl` and `symm` work on it; `AsympLE.trans`
is likewise `@[trans]`, and `AsympLE.trans_asympEq` / `AsympEq.trans_asympLE` chain the
one-sided form against the two-sided one. `AsympEq.add`, `.sub`, `.const_mul`,
`AsympLE.add` and `AsympEq.finsetSum` are the congruence algebra, so a consumer combining
sequences need not descend to `filter_upwards` by hand.
-/

namespace LogicalInduction

open Filter Topology

/-! ## The limit relations -/

/-- `f ≈ₙ g` : the two sequences agree in the limit (`dd:asymp`). -/
def AsympEq (f g : ℕ → ℝ) : Prop :=
  Tendsto (fun n => f n - g n) atTop (𝓝 0)

@[inherit_doc] scoped infix:50 " ≈ₙ " => AsympEq

/-- `f ≲ₙ g` : `f` does not exceed `g` in the limit — for every ε > 0, eventually
`f n ≤ g n + ε` (`dd:asymp`). -/
def AsympLE (f g : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ n in atTop, f n ≤ g n + ε

@[inherit_doc] scoped infix:50 " ≲ₙ " => AsympLE

/-- `f ≳ₙ g` : `f` is at least `g` in the limit (`dd:asymp`). -/
def AsympGE (f g : ℕ → ℝ) : Prop :=
  AsympLE g f

@[inherit_doc] scoped infix:50 " ≳ₙ " => AsympGE

/-- `≳ₙ` is `≲ₙ` with its arguments exchanged. -/
lemma asympGE_iff {f g : ℕ → ℝ} : f ≳ₙ g ↔ g ≲ₙ f := Iff.rfl

/-- The sequences `f` and `g` are eventually within `ε` of each other. The finite-stage
building block; the limiting forms above are the default vocabulary. -/
abbrev EventuallyWithin (ε : ℝ) (f g : ℕ → ℝ) : Prop :=
  ∀ᶠ n in atTop, |f n - g n| ≤ ε

/-- `ConvergesTo f x` : the sequence `f` converges to `x`. Thin alias for Mathlib's
`Tendsto f atTop (𝓝 x)`, so downstream files never spell the filter form. -/
abbrev ConvergesTo (f : ℕ → ℝ) (x : ℝ) : Prop :=
  Tendsto f atTop (𝓝 x)

/-! ## The ε-characterization -/

lemma asympEq_iff_eventuallyWithin {f g : ℕ → ℝ} :
    f ≈ₙ g ↔ ∀ ε > 0, EventuallyWithin ε f g := by
  unfold AsympEq
  rw [Metric.tendsto_atTop]
  constructor
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
    have hd := hN n hn
    rw [Real.dist_eq, sub_zero] at hd
    exact hd.le
  · intro h ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.1 (h (ε / 2) (by positivity))
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq, sub_zero]
    exact (hN n hn).trans_lt (by linarith)

/-! ## `≈ₙ` is an equivalence -/

@[refl]
lemma AsympEq.refl (f : ℕ → ℝ) : f ≈ₙ f := by
  show Tendsto (fun n => f n - f n) atTop (𝓝 0)
  simp [sub_self]

@[symm]
lemma AsympEq.symm {f g : ℕ → ℝ} (h : f ≈ₙ g) : g ≈ₙ f := by
  have h' : Tendsto (fun n => f n - g n) atTop (𝓝 0) := h
  show Tendsto (fun n => g n - f n) atTop (𝓝 0)
  simpa [neg_sub] using h'.neg

@[trans]
lemma AsympEq.trans {f g h : ℕ → ℝ} (hfg : f ≈ₙ g) (hgh : g ≈ₙ h) : f ≈ₙ h := by
  have h₁ : Tendsto (fun n => f n - g n) atTop (𝓝 0) := hfg
  have h₂ : Tendsto (fun n => g n - h n) atTop (𝓝 0) := hgh
  show Tendsto (fun n => f n - h n) atTop (𝓝 0)
  simpa [sub_add_sub_cancel] using h₁.add h₂

/-! ## One-sided bounds and their transitivity -/

lemma AsympEq.asympLE {f g : ℕ → ℝ} (h : f ≈ₙ g) : f ≲ₙ g := by
  intro ε hε
  filter_upwards [asympEq_iff_eventuallyWithin.1 h ε hε] with n hn
  have := (abs_sub_le_iff.1 hn).1
  linarith

lemma AsympEq.asympGE {f g : ℕ → ℝ} (h : f ≈ₙ g) : f ≳ₙ g :=
  h.symm.asympLE

/-- `≲ₙ` is transitive. -/
@[trans]
lemma AsympLE.trans {f g h : ℕ → ℝ} (h₁ : f ≲ₙ g) (h₂ : g ≲ₙ h) : f ≲ₙ h := by
  intro ε hε
  filter_upwards [h₁ (ε / 2) (by linarith), h₂ (ε / 2) (by linarith)] with n hn₁ hn₂
  linarith

/-- `f ≲ₙ g` followed by `g ≈ₙ h` gives `f ≲ₙ h`. -/
lemma AsympLE.trans_asympEq {f g h : ℕ → ℝ} (h₁ : f ≲ₙ g) (h₂ : g ≈ₙ h) : f ≲ₙ h :=
  h₁.trans h₂.asympLE

/-- `f ≈ₙ g` followed by `g ≲ₙ h` gives `f ≲ₙ h`. -/
lemma AsympEq.trans_asympLE {f g h : ℕ → ℝ} (h₁ : f ≈ₙ g) (h₂ : g ≲ₙ h) : f ≲ₙ h :=
  h₁.asympLE.trans h₂

lemma asympEq_iff_asympLE_asympGE {f g : ℕ → ℝ} :
    f ≈ₙ g ↔ f ≲ₙ g ∧ f ≳ₙ g := by
  refine ⟨fun h => ⟨h.asympLE, h.asympGE⟩, fun ⟨h₁, h₂⟩ => ?_⟩
  rw [asympEq_iff_eventuallyWithin]
  intro ε hε
  filter_upwards [h₁ ε hε, h₂ ε hε] with n hn₁ hn₂
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-! ## Sums and scalars -/

/-- `≈ₙ` is preserved by pointwise addition. -/
lemma AsympEq.add {f₁ g₁ f₂ g₂ : ℕ → ℝ} (h₁ : f₁ ≈ₙ g₁) (h₂ : f₂ ≈ₙ g₂) :
    (fun n => f₁ n + f₂ n) ≈ₙ fun n => g₁ n + g₂ n := by
  have h₁' : Tendsto (fun n => f₁ n - g₁ n) atTop (𝓝 0) := h₁
  have h₂' : Tendsto (fun n => f₂ n - g₂ n) atTop (𝓝 0) := h₂
  show Tendsto (fun n => f₁ n + f₂ n - (g₁ n + g₂ n)) atTop (𝓝 0)
  simpa [add_sub_add_comm] using h₁'.add h₂'

/-- `≈ₙ` is preserved by pointwise subtraction. -/
lemma AsympEq.sub {f₁ g₁ f₂ g₂ : ℕ → ℝ} (h₁ : f₁ ≈ₙ g₁) (h₂ : f₂ ≈ₙ g₂) :
    (fun n => f₁ n - f₂ n) ≈ₙ fun n => g₁ n - g₂ n := by
  have h₁' : Tendsto (fun n => f₁ n - g₁ n) atTop (𝓝 0) := h₁
  have h₂' : Tendsto (fun n => f₂ n - g₂ n) atTop (𝓝 0) := h₂
  show Tendsto (fun n => f₁ n - f₂ n - (g₁ n - g₂ n)) atTop (𝓝 0)
  simpa [sub_sub_sub_comm] using h₁'.sub h₂'

/-- `≈ₙ` is preserved by multiplication by a constant. -/
lemma AsympEq.const_mul {f g : ℕ → ℝ} (c : ℝ) (h : f ≈ₙ g) :
    (fun n => c * f n) ≈ₙ fun n => c * g n := by
  have h' : Tendsto (fun n => f n - g n) atTop (𝓝 0) := h
  show Tendsto (fun n => c * f n - c * g n) atTop (𝓝 0)
  simpa [mul_sub] using h'.const_mul c

/-- `≲ₙ` is preserved by pointwise addition. -/
lemma AsympLE.add {f₁ g₁ f₂ g₂ : ℕ → ℝ} (h₁ : f₁ ≲ₙ g₁) (h₂ : f₂ ≲ₙ g₂) :
    (fun n => f₁ n + f₂ n) ≲ₙ fun n => g₁ n + g₂ n := by
  intro ε hε
  filter_upwards [h₁ (ε / 2) (by linarith), h₂ (ε / 2) (by linarith)] with n hn₁ hn₂
  show f₁ n + f₂ n ≤ g₁ n + g₂ n + ε
  linarith

/-- Finite sums respect `≈ₙ`. -/
lemma AsympEq.finsetSum {J : Type*} [Fintype J] {f g : J → ℕ → ℝ}
    (h : ∀ j, f j ≈ₙ g j) : (fun n => ∑ j, f j n) ≈ₙ (fun n => ∑ j, g j n) := by
  have key : Tendsto (fun n => ∑ j, (f j n - g j n)) atTop (𝓝 (∑ _j : J, (0 : ℝ))) :=
    tendsto_finset_sum _ (fun j _ => h j)
  simpa [AsympEq, Finset.sum_sub_distrib] using key

/-! ## Convergence as `≈ₙ` against a constant -/

/-- `f` converges to `x` exactly when it is asymptotically equal to the constant sequence
`x` (`dd:asymp`). -/
lemma convergesTo_iff_asympEq_const {f : ℕ → ℝ} {x : ℝ} :
    ConvergesTo f x ↔ f ≈ₙ fun _ => x := by
  show Tendsto f atTop (𝓝 x) ↔ AsympEq f fun _ => x
  unfold AsympEq
  exact (tendsto_sub_nhds_zero_iff (u := f) (x := x)).symm

/-- Cancel a positive fixed scale from asymptotic nonnegativity. -/
lemma asympGE_zero_of_const_mul_pos
    {x : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (h : (fun n => c * x n) ≳ₙ (fun _ => 0)) :
    x ≳ₙ (fun _ => 0) := by
  intro ε hε
  have hs := h (c * ε) (mul_pos hc hε)
  filter_upwards [hs] with n hn
  have hm : 0 ≤ c * (x n + ε) := by
    simpa only [mul_add, zero_add] using hn
  exact (mul_nonneg_iff_of_pos_left hc).mp hm

/-- Cancel a positive fixed scale from asymptotic nonpositivity. -/
lemma asympLE_zero_of_const_mul_pos
    {x : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (h : (fun n => c * x n) ≲ₙ (fun _ => 0)) :
    x ≲ₙ (fun _ => 0) := by
  intro ε hε
  have hs := h (c * ε) (mul_pos hc hε)
  filter_upwards [hs] with n hn
  have hm : c * x n ≤ c * ε := by
    simpa only [zero_add] using hn
  simpa only [zero_add] using (mul_le_mul_iff_of_pos_left hc).mp hm

/-- Cancel a positive fixed scale from asymptotic equality to zero. -/
lemma asympEq_zero_of_const_mul_pos
    {x : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (h : (fun n => c * x n) ≈ₙ (fun _ => 0)) :
    x ≈ₙ (fun _ => 0) := by
  rw [asympEq_iff_asympLE_asympGE] at h ⊢
  exact ⟨asympLE_zero_of_const_mul_pos hc h.1,
    asympGE_zero_of_const_mul_pos hc h.2⟩

end LogicalInduction
