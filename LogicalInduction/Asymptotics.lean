/-
# Asymptotics (`dd:asymp`)

The single home for the limit vocabulary used across the property tail: `≈ₙ` / `≳ₙ` /
`≲ₙ`, "eventually within ε", and "converges to". Built on Mathlib's
`Tendsto (· − ·) atTop (𝓝 0)` and `∀ᶠ n in atTop, …`. Define each idiom **once** here;
do not redefine per file.

Convention: state results in the **limiting** form by default (the downstream deference
work consumes it); add the finite-stage form only where a consumer needs it.

Paper reference (arXiv:1609.03543 §2, notation): `f ≈ₙ g` means `f n − g n → 0`;
`f ≳ₙ g` means `liminf (f n − g n) ≥ 0`, i.e. for every ε > 0, eventually
`f n ≥ g n − ε`.
-/
import Mathlib.Analysis.SpecificLimits.Basic

namespace LogicalInduction

open Filter Topology

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

/-- The sequences `f` and `g` are eventually within `ε` of each other. The finite-stage
building block; the limiting forms above are the default vocabulary. -/
abbrev EventuallyWithin (ε : ℝ) (f g : ℕ → ℝ) : Prop :=
  ∀ᶠ n in atTop, |f n - g n| ≤ ε

/-- `ConvergesTo f x` : the sequence `f` converges to `x`. Thin alias for Mathlib's
`Tendsto f atTop (𝓝 x)`, so downstream files never spell the filter form. -/
abbrev ConvergesTo (f : ℕ → ℝ) (x : ℝ) : Prop :=
  Tendsto f atTop (𝓝 x)

/-! ## The ε-characterization -/

theorem asympEq_iff_eventuallyWithin {f g : ℕ → ℝ} :
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
theorem AsympEq.refl (f : ℕ → ℝ) : f ≈ₙ f := by
  show Tendsto (fun n => f n - f n) atTop (𝓝 0)
  simp [sub_self]

@[symm]
theorem AsympEq.symm {f g : ℕ → ℝ} (h : f ≈ₙ g) : g ≈ₙ f := by
  have h' : Tendsto (fun n => f n - g n) atTop (𝓝 0) := h
  show Tendsto (fun n => g n - f n) atTop (𝓝 0)
  simpa [neg_sub] using h'.neg

@[trans]
theorem AsympEq.trans {f g h : ℕ → ℝ} (hfg : f ≈ₙ g) (hgh : g ≈ₙ h) : f ≈ₙ h := by
  have h₁ : Tendsto (fun n => f n - g n) atTop (𝓝 0) := hfg
  have h₂ : Tendsto (fun n => g n - h n) atTop (𝓝 0) := hgh
  show Tendsto (fun n => f n - h n) atTop (𝓝 0)
  simpa [sub_add_sub_cancel] using h₁.add h₂

/-! ## Splitting `≈ₙ` into the one-sided bounds -/

theorem AsympEq.asympLE {f g : ℕ → ℝ} (h : f ≈ₙ g) : f ≲ₙ g := by
  intro ε hε
  filter_upwards [asympEq_iff_eventuallyWithin.1 h ε hε] with n hn
  have := (abs_sub_le_iff.1 hn).1
  linarith

theorem AsympEq.asympGE {f g : ℕ → ℝ} (h : f ≈ₙ g) : f ≳ₙ g :=
  h.symm.asympLE

theorem asympEq_iff_asympLE_asympGE {f g : ℕ → ℝ} :
    f ≈ₙ g ↔ f ≲ₙ g ∧ f ≳ₙ g := by
  refine ⟨fun h => ⟨h.asympLE, h.asympGE⟩, fun ⟨h₁, h₂⟩ => ?_⟩
  rw [asympEq_iff_eventuallyWithin]
  intro ε hε
  filter_upwards [h₁ ε hε, h₂ ε hε] with n hn₁ hn₂
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-! ## Convergence as `≈ₙ` against a constant -/

theorem convergesTo_iff_asympEq_const {f : ℕ → ℝ} {x : ℝ} :
    ConvergesTo f x ↔ f ≈ₙ fun _ => x := by
  show Tendsto f atTop (𝓝 x) ↔ AsympEq f fun _ => x
  unfold AsympEq
  exact (tendsto_sub_nhds_zero_iff (u := f) (x := x)).symm

end LogicalInduction
