/-
# Closure properties of the polynomial-time machine class

Stage 1 of the efficiency-model program (`notes/boundary-efficiency-model.md`), continued
from `Basic.lean`.

The construction is sequential composition of controls (`seq`): the composite's states are
the disjoint union of the two machines' states, and the switch from the first stage to the
second is a single `nop` step that hands over the memory untouched. No data movement is
needed because a run's halting memory is required to be in the canonical `layout` — the
first machine's output is already exactly the second machine's input configuration.

`MachinePolyEC.comp` is then the composition closure, and it is the theorem Mathlib
currently records as open for its own poly-time class
(`proof_wanted Turing.TM2ComputableInPolyTime.comp`). Its only non-formal ingredient is
that a machine writes at most one symbol per step, so the second machine's clock is
evaluated at a polynomially bounded length (`RunsInTime.length_output_le` in `Basic.lean`).

Pairing is **not** proved here, and the reason is a design finding rather than a missing
lemma: the fixed four-stack memory shape of `Basic.lean` leaves nowhere to park a copy of
the input across a sub-machine's run. The section comment below states the obstruction and
the intended fix (private stack blocks over a shared I/O stack) in full.
-/
import LogicalInduction.Construction.Machine.Basic
import Mathlib.Tactic.Ring

namespace LogicalInduction.Counted

variable {Γ : Type}

/-! ## Sequential composition of machines -/

/-- **Sequential composition.** Run `M₁`; on the step where `M₁` would halt, move to `M₂`'s
initial state instead, leaving memory alone; then run `M₂`. The handover costs exactly one
step. -/
def seq (M₁ M₂ : Machine Γ) : Machine Γ where
  Λ := M₁.Λ ⊕ M₂.Λ
  init := Sum.inl M₁.init
  step q tops :=
    match q with
    | Sum.inl q₁ =>
        match M₁.step q₁ tops with
        | some (q', act) => some (Sum.inl q', act)
        | none => some (Sum.inr M₂.init, Act.nop)
    | Sum.inr q₂ => (M₂.step q₂ tops).map fun p => (Sum.inr p.1, p.2)

/-- A first-stage configuration, as a configuration of the composite. -/
def seqL (M₁ M₂ : Machine Γ) (c : Cfg Γ M₁.Λ) : Cfg Γ (seq M₁ M₂).Λ :=
  ⟨Sum.inl c.state, c.store⟩

/-- A second-stage configuration, as a configuration of the composite. -/
def seqR (M₁ M₂ : Machine Γ) (c : Cfg Γ M₂.Λ) : Cfg Γ (seq M₁ M₂).Λ :=
  ⟨Sum.inr c.state, c.store⟩

lemma seq_step_inl (M₁ M₂ : Machine Γ) (q : M₁.Λ) (tops : Stack → Option Γ) :
    (seq M₁ M₂).step (Sum.inl q) tops =
      match M₁.step q tops with
      | some (q', act) => some (Sum.inl q', act)
      | none => some (Sum.inr M₂.init, Act.nop) := rfl

lemma seq_step_inr (M₁ M₂ : Machine Γ) (q : M₂.Λ) (tops : Stack → Option Γ) :
    (seq M₁ M₂).step (Sum.inr q) tops = (M₂.step q tops).map fun p => (Sum.inr p.1, p.2) :=
  rfl

/-- While the first stage is running, the composite mirrors it step for step. -/
lemma stepCfg_seqL_some {M₁ M₂ : Machine Γ} {c c' : Cfg Γ M₁.Λ} (h : stepCfg M₁ c = some c') :
    stepCfg (seq M₁ M₂) (seqL M₁ M₂ c) = some (seqL M₁ M₂ c') := by
  rw [stepCfg, Option.map_eq_some_iff] at h
  obtain ⟨⟨q', act⟩, hstep, rfl⟩ := h
  simp [stepCfg, seqL, seq_step_inl, hstep]

/-- The handover: the step on which the first stage would halt enters the second stage's
initial state, leaving memory untouched. -/
lemma stepCfg_seqL_none {M₁ M₂ : Machine Γ} {c : Cfg Γ M₁.Λ} (h : stepCfg M₁ c = none) :
    stepCfg (seq M₁ M₂) (seqL M₁ M₂ c) = some (seqR M₁ M₂ ⟨M₂.init, c.store⟩) := by
  rw [stepCfg, Option.map_eq_none_iff] at h
  simp [stepCfg, seqL, seqR, seq_step_inl, h, Act.apply]

lemma stepCfg_seqR_some {M₁ M₂ : Machine Γ} {c c' : Cfg Γ M₂.Λ} (h : stepCfg M₂ c = some c') :
    stepCfg (seq M₁ M₂) (seqR M₁ M₂ c) = some (seqR M₁ M₂ c') := by
  rw [stepCfg, Option.map_eq_some_iff] at h
  obtain ⟨⟨q', act⟩, hstep, rfl⟩ := h
  simp only [stepCfg, seqR, seq_step_inr, hstep, Option.map_some, Option.map_eq_some_iff]
  exact ⟨(Sum.inr q', act), rfl, rfl⟩

lemma stepCfg_seqR_none {M₁ M₂ : Machine Γ} {c : Cfg Γ M₂.Λ} (h : stepCfg M₂ c = none) :
    stepCfg (seq M₁ M₂) (seqR M₁ M₂ c) = none := by
  rw [stepCfg, Option.map_eq_none_iff] at h
  simp only [stepCfg, seqR, seq_step_inr, h]
  rfl

lemma runFor_seqL {M₁ M₂ : Machine Γ} : ∀ {t : ℕ} {c c' : Cfg Γ M₁.Λ},
    runFor M₁ t c = some c' → runFor (seq M₁ M₂) t (seqL M₁ M₂ c) = some (seqL M₁ M₂ c')
  | 0, c, c', h => by cases h; rfl
  | t + 1, c, c', h => by
      rw [runFor_succ, Option.bind_eq_some_iff] at h
      obtain ⟨d, hd, hrest⟩ := h
      rw [runFor_succ, stepCfg_seqL_some hd, Option.bind_some]
      exact runFor_seqL hrest

lemma runFor_seqR {M₁ M₂ : Machine Γ} : ∀ {t : ℕ} {c c' : Cfg Γ M₂.Λ},
    runFor M₂ t c = some c' → runFor (seq M₁ M₂) t (seqR M₁ M₂ c) = some (seqR M₁ M₂ c')
  | 0, c, c', h => by cases h; rfl
  | t + 1, c, c', h => by
      rw [runFor_succ, Option.bind_eq_some_iff] at h
      obtain ⟨d, hd, hrest⟩ := h
      rw [runFor_succ, stepCfg_seqR_some hd, Option.bind_some]
      exact runFor_seqR hrest

/-- **Sequential composition is additive in time**, with exactly one step of overhead for
the handover. -/
lemma seq_runsInTime {M₁ M₂ : Machine Γ} {x u y : List Γ} {t₁ t₂ : ℕ}
    (h₁ : RunsInTime M₁ x u t₁) (h₂ : RunsInTime M₂ u y t₂) :
    RunsInTime (seq M₁ M₂) x y (t₁ + 1 + t₂) := by
  obtain ⟨s₁, hs₁, q₁, hrun₁, hhalt₁⟩ := h₁
  obtain ⟨s₂, hs₂, q₂, hrun₂, hhalt₂⟩ := h₂
  refine ⟨s₁ + 1 + s₂, by omega, Sum.inr q₂, ?_, ?_⟩
  · have hstart : initCfg (seq M₁ M₂) x = seqL M₁ M₂ (initCfg M₁ x) := rfl
    have hstage₁ : runFor (seq M₁ M₂) s₁ (initCfg (seq M₁ M₂) x)
        = some (seqL M₁ M₂ ⟨q₁, layout u⟩) := by
      rw [hstart]; exact runFor_seqL hrun₁
    have hswitch : runFor (seq M₁ M₂) 1 (seqL M₁ M₂ ⟨q₁, layout u⟩)
        = some (seqR M₁ M₂ (initCfg M₂ u)) := by
      rw [runFor_succ, stepCfg_seqL_none hhalt₁]; rfl
    have hstage₂ : runFor (seq M₁ M₂) s₂ (seqR M₁ M₂ (initCfg M₂ u))
        = some (seqR M₁ M₂ ⟨q₂, layout y⟩) := runFor_seqR hrun₂
    rw [runFor_add, runFor_add, hstage₁, Option.bind_some, hswitch, Option.bind_some,
      hstage₂]
    rfl
  · exact stepCfg_seqR_none hhalt₂

/-! ## The clock normal form -/

/-- The clock's additive constant is absorbed into its coefficient. -/
lemma clock_le (a : ℕ) {X : ℕ} (hX : 1 ≤ X) : a * X + a ≤ (2 * a + 1) * X := by
  have h : a ≤ a * X := by simpa using Nat.mul_le_mul (le_refl a) hX
  calc a * X + a ≤ a * X + a * X := Nat.add_le_add_left h _
    _ = 2 * a * X := by ring
    _ ≤ (2 * a + 1) * X := Nat.mul_le_mul (by omega) (le_refl X)

/-- **The clock normal form is closed under the substitution machine composition performs.**
The first machine's clock bounds both its own running time and the length of its output, so
the second machine's clock is evaluated at `n + t₁ n`; the result is again of the form
`a * (n + 1) ^ k + a`. Stated as a bare arithmetic fact so that `MachinePolyEC.comp` needs
no polynomial API. -/
lemma exists_clock_comp (a₁ k₁ a₂ k₂ : ℕ) :
    ∃ a k : ℕ, ∀ n : ℕ,
      (a₁ * (n + 1) ^ k₁ + a₁) + 1 +
          (a₂ * ((n + (a₁ * (n + 1) ^ k₁ + a₁)) + 1) ^ k₂ + a₂)
        ≤ a * (n + 1) ^ k + a := by
  refine ⟨(2 * a₁ + 1) + 1 + (2 * a₂ + 1) * ((2 * a₁ + 1) + 1) ^ k₂,
    max (max k₁ 1) (max k₁ 1 * k₂), fun n => ?_⟩
  set N := n + 1 with hN
  set K₁ := max k₁ 1 with hK₁
  set K := max K₁ (K₁ * k₂) with hK
  have hNpos : 0 < N := by omega
  have hmono : ∀ i j : ℕ, i ≤ j → N ^ i ≤ N ^ j := fun _ _ h => Nat.pow_le_pow_right hNpos h
  -- the first machine's clock, in the `K₁` normal form
  have ht₁ : a₁ * N ^ k₁ + a₁ ≤ (2 * a₁ + 1) * N ^ K₁ :=
    (clock_le a₁ (Nat.one_le_pow _ _ hNpos)).trans
      (Nat.mul_le_mul (le_refl _) (hmono _ _ (le_max_left _ _)))
  -- the argument the second machine's clock is evaluated at
  have hm : n + (a₁ * N ^ k₁ + a₁) + 1 ≤ ((2 * a₁ + 1) + 1) * N ^ K₁ := by
    have hNK : N ≤ N ^ K₁ := by
      calc N = N ^ 1 := (pow_one N).symm
        _ ≤ N ^ K₁ := hmono 1 K₁ (le_max_right _ _)
    calc n + (a₁ * N ^ k₁ + a₁) + 1 = N + (a₁ * N ^ k₁ + a₁) := by omega
      _ ≤ N ^ K₁ + (2 * a₁ + 1) * N ^ K₁ := Nat.add_le_add hNK ht₁
      _ = ((2 * a₁ + 1) + 1) * N ^ K₁ := by ring
  have hpow : (n + (a₁ * N ^ k₁ + a₁) + 1) ^ k₂
      ≤ ((2 * a₁ + 1) + 1) ^ k₂ * N ^ (K₁ * k₂) := by
    calc (n + (a₁ * N ^ k₁ + a₁) + 1) ^ k₂ ≤ (((2 * a₁ + 1) + 1) * N ^ K₁) ^ k₂ :=
          Nat.pow_le_pow_left hm k₂
      _ = ((2 * a₁ + 1) + 1) ^ k₂ * (N ^ K₁) ^ k₂ := Nat.mul_pow _ _ _
      _ = ((2 * a₁ + 1) + 1) ^ k₂ * N ^ (K₁ * k₂) := by rw [← Nat.pow_mul]
  have ht₂ : a₂ * (n + (a₁ * N ^ k₁ + a₁) + 1) ^ k₂ + a₂
      ≤ ((2 * a₂ + 1) * ((2 * a₁ + 1) + 1) ^ k₂) * N ^ K := by
    calc a₂ * (n + (a₁ * N ^ k₁ + a₁) + 1) ^ k₂ + a₂
        ≤ (2 * a₂ + 1) * (n + (a₁ * N ^ k₁ + a₁) + 1) ^ k₂ :=
          clock_le a₂ (Nat.one_le_pow _ _ (by omega))
      _ ≤ (2 * a₂ + 1) * (((2 * a₁ + 1) + 1) ^ k₂ * N ^ (K₁ * k₂)) :=
          Nat.mul_le_mul (le_refl _) hpow
      _ = ((2 * a₂ + 1) * ((2 * a₁ + 1) + 1) ^ k₂) * N ^ (K₁ * k₂) := by ring
      _ ≤ ((2 * a₂ + 1) * ((2 * a₁ + 1) + 1) ^ k₂) * N ^ K :=
          Nat.mul_le_mul (le_refl _) (hmono _ _ (le_max_right _ _))
  have ht₁' : a₁ * N ^ k₁ + a₁ ≤ (2 * a₁ + 1) * N ^ K :=
    ht₁.trans (Nat.mul_le_mul (le_refl _) (hmono _ _ (le_max_left _ _)))
  have hone : 1 ≤ 1 * N ^ K := by simpa using Nat.one_le_pow K N hNpos
  calc (a₁ * N ^ k₁ + a₁) + 1 + (a₂ * (n + (a₁ * N ^ k₁ + a₁) + 1) ^ k₂ + a₂)
      ≤ (2 * a₁ + 1) * N ^ K + 1 * N ^ K
          + ((2 * a₂ + 1) * ((2 * a₁ + 1) + 1) ^ k₂) * N ^ K :=
        Nat.add_le_add (Nat.add_le_add ht₁' hone) ht₂
    _ = ((2 * a₁ + 1) + 1 + (2 * a₂ + 1) * ((2 * a₁ + 1) + 1) ^ k₂) * N ^ K := by ring
    _ ≤ ((2 * a₁ + 1) + 1 + (2 * a₂ + 1) * ((2 * a₁ + 1) + 1) ^ k₂) * N ^ K
          + ((2 * a₁ + 1) + 1 + (2 * a₂ + 1) * ((2 * a₁ + 1) + 1) ^ k₂) := Nat.le_add_right _ _

/-! ## Closure -/

/-- **The polynomial-time machine class is closed under composition.**

This is the closure Mathlib records as open for its own poly-time class
(`proof_wanted Turing.TM2ComputableInPolyTime.comp`, in
`Mathlib/Computability/TuringMachine/Computable.lean`); the memory convention of
`RunsInTime` is what removes the "copy the output tape to the input tape" phase that makes
the statement awkward there. -/
lemma MachinePolyEC.comp [Fintype Γ] {f g : List Γ → List Γ}
    (hf : MachinePolyEC f) (hg : MachinePolyEC g) : MachinePolyEC (fun x => g (f x)) := by
  obtain ⟨M₁, a₁, k₁, h₁⟩ := hf
  obtain ⟨M₂, a₂, k₂, h₂⟩ := hg
  obtain ⟨a, k, hclock⟩ := exists_clock_comp a₁ k₁ a₂ k₂
  refine ⟨seq M₁ M₂, a, k, fun x => ?_⟩
  have hx := h₁ x
  have hlen : (f x).length ≤ x.length + (a₁ * (x.length + 1) ^ k₁ + a₁) := hx.length_output_le
  have hy : RunsInTime M₂ (f x) (g (f x))
      (a₂ * ((x.length + (a₁ * (x.length + 1) ^ k₁ + a₁)) + 1) ^ k₂ + a₂) :=
    (h₂ (f x)).mono
      (Nat.add_le_add_right
        (Nat.mul_le_mul (le_refl a₂) (Nat.pow_le_pow_left (by omega) k₂)) a₂)
  exact (seq_runsInTime hx hy).mono (hclock x.length)

/-! ## Pairing — open, and why (a design finding, not a missing lemma)

`MachinePolyEC` should also be closed under `fun x => pairWord s₀ s₁ (f x) (g x)`. Unlike
composition, this needs the input *twice*: run `f` on `x`, keep `x`, run `g` on `x`, then
emit. The phases are routine as machines — transfer one stack onto another (`n` steps,
reversing), duplicate through the control state (`3n` steps, the popped symbol held in the
state), and a tagging emitter — and `seq` chains them with additive clocks.

**What blocks it is the memory shape, not the phases.** `Stack` is a fixed four-element
type shared by every machine, and `RunsInTime` requires the canonical `layout` at both ends
of a run: input on `main`, *every other stack empty*. Under that convention a saved copy of
`x` cannot be parked anywhere while `f`'s machine runs — the convention forbids the parking
stack from being non-empty at `f`'s start, and `f`'s machine may in any case read and write
all four stacks, since nothing in `MachinePolyEC` restricts which stacks a member uses.
That is not a gap in this file's proofs; it is a consequence of the definition in
`Basic.lean`.

The fix, for the next tranche, is to give each machine a **private stack block over a shared
I/O stack**: bundle a finite index type `K` into `Machine` and let its stacks be `Option K`,
with `none` the shared input/output stack and `some k` private scratch. Then

* `seq` still needs no data movement — both stages share the I/O stack — but now composes
  over `Option (K₁ ⊕ K₂)`, each stage embedded into its own block;
* a machine embedded into a larger block provably cannot see or touch the other blocks (its
  step function is precomposed with the restriction of the stack tops to its own block), so
  the frame lemma that pairing needs holds *by construction* rather than as a side condition;
* pairing allocates its own private stacks alongside `f`'s and `g`'s and parks the saved
  copy there.

The cost is a rewrite of `Basic.lean`'s memory shape plus an embedding/frame simulation
lemma, and a corresponding re-proof of the four `seq` lemmas above. It is scheduled as the
next tranche rather than bolted on, per the repository's consolidation discipline: the
strongest version should take the plain name, not sit beside a superseded one.
-/

/-- Self-delimiting pairing of words over an alphabet with two distinguished symbols: each
symbol of `u` is preceded by the tag `s₁`, and `s₀` terminates the `u` block. -/
def pairWord (s₀ s₁ : Γ) (u v : List Γ) : List Γ :=
  (u.flatMap fun x => [s₁, x]) ++ s₀ :: v

/-- Pairing is injective on its two arguments, given two distinct tags: `pairWord` really
does encode the pair. -/
lemma pairWord_injective {s₀ s₁ : Γ} (hs : s₀ ≠ s₁) {u u' v v' : List Γ}
    (h : pairWord s₀ s₁ u v = pairWord s₀ s₁ u' v') : u = u' ∧ v = v' := by
  induction u generalizing u' with
  | nil =>
      cases u' with
      | nil => simpa [pairWord] using h
      | cons x' u'' => simp [pairWord] at h; exact absurd h.1 hs
  | cons x u ih =>
      cases u' with
      | nil => simp [pairWord] at h; exact absurd h.1.symm hs
      | cons x' u'' =>
          simp only [pairWord, List.flatMap_cons, List.cons_append, List.append_assoc,
            List.cons.injEq] at h
          obtain ⟨-, hx, hrest⟩ := h
          obtain ⟨hu, hv⟩ := ih (by simpa [pairWord] using hrest)
          exact ⟨by rw [hx, hu], hv⟩

/-- **Pairing closure — not proved.** Believed true and not attempted here: under the
current fixed four-stack memory shape there is nowhere to park a copy of the input across a
sub-machine's run (see the section comment above), so the proof waits on the private-stack
refactor rather than on any lemma stated here. The statement itself is expected to survive
that refactor unchanged, since it mentions only `MachinePolyEC`. -/
lemma MachinePolyEC.pair [Fintype Γ] {s₀ s₁ : Γ} {f g : List Γ → List Γ}
    (hf : MachinePolyEC f) (hg : MachinePolyEC g) :
    MachinePolyEC (fun x => pairWord s₀ s₁ (f x) (g x)) := by
  -- TODO(def:ec): need `Machine` to carry a private stack block over a shared I/O stack,
  -- with the embedding/frame simulation lemma; then the transfer, duplicate and tagging
  -- phases chained by `seq`.  See the section comment above for the full account.
  sorry

end LogicalInduction.Counted
