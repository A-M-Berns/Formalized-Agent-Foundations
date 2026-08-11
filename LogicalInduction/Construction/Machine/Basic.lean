/-
# A counted-step machine and its polynomial-time class

Stage 1 of the efficiency-model program (`notes/boundary-efficiency-model.md`). This file
defines a machine whose steps are *counted by construction*, together with the polynomial
time class `MachinePolyEC` built over it.

**Model.** A machine is a finite control (`Machine.Λ`, a `Fintype`) over four stacks
(`Stack`) of symbols from a finite alphabet `Γ`. One step reads the top symbol of every
stack and performs exactly one memory action: push a symbol onto one stack, pop one stack,
or nothing (`Act`). The step function returning `none` is halting. This is Mathlib's
`Turing.TM2` primitive set, restricted to a fixed memory shape and metered at one unit per
action rather than one unit per structured statement; two stacks already simulate a
single-tape Turing machine with linear overhead, so it is a genuine machine class rather
than a unit-cost RAM.

Finiteness is what makes the class honest: with `Fintype Γ` and `Fintype Λ` the transition
function is a finite table, so no information can be smuggled into the control. Both
finiteness assumptions are load-bearing — over an infinite `Γ` the step function would be
an arbitrary map on an infinite domain, i.e. an oracle.

**Relation to the rest of the repository.** Nothing here is bridged to
`LogicalInduction.EfficientlyComputable` — that inclusion is Stage 2 of the plan and is not
started. `MachinePolyEC` is deliberately given the same shape as `EfficientlyComputable`
(`Framework/Criterion.lean`): an existential over programs and over a clock in the normal
form `fun n => a * (n + 1) ^ k + a`, which is also the normal form of the repository's
`IsPolyBounded` (`Framework/Computable.lean`). This file does **not** import either, since
the material is intended to be upstreamable to Mathlib, where the composition of
polynomial-time machine-computable functions is currently an open item
(`proof_wanted Turing.TM2ComputableInPolyTime.comp`). The two definitions are only made to
look alike; no theorem here relates them.

**No paper node.** Nothing in this directory is a rendering of anything in
arXiv:1609.03543; it is infrastructure for a future recalibration of `def:ec`. Consistently
with the plan's "no partial credit before Stage 3", no strength claim anywhere in the
repository changes because of it.
-/
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.DeriveFintype

namespace LogicalInduction.Counted

/-- The machine's memory: four stacks. `main` carries the input at the start of a run and
the output at the end; `a`, `b`, `c` are scratch. A fixed memory shape (rather than a
machine-supplied index type) is what makes sequential composition of two machines a
construction on the control alone. -/
inductive Stack where
  | main : Stack
  | a : Stack
  | b : Stack
  | c : Stack
  deriving DecidableEq, Fintype, Inhabited

/-- The memory action performed by one step: push a symbol onto one stack, pop one stack,
or leave memory alone. Exactly one action per step is what makes the step count a faithful
time measure. -/
inductive Act (Γ : Type) where
  | push : Stack → Γ → Act Γ
  | pop : Stack → Act Γ
  | nop : Act Γ

/-- A machine configuration: the control state and the contents of the four stacks (each
written top-first). -/
structure Cfg (Γ : Type) (Λ : Type) where
  /-- The current control state. -/
  state : Λ
  /-- The contents of each stack, top of stack first.  (Named `store` rather than
  `stacks`: Mathlib's `@[stacks]` attribute reserves `stacks` as a token.) -/
  store : Stack → List Γ

/-- A counted-step machine over the alphabet `Γ`: a finite control together with a
transition function that sees the top symbol of every stack and emits one action.
`step q tops = none` means the machine halts in state `q`.

The control state type is bundled (rather than being a parameter) so that constructions
like `seq` may enlarge it, and so that `MachinePolyEC` can existentially quantify over
machines without quantifying over types with instances. -/
structure Machine (Γ : Type) where
  /-- The control states. -/
  Λ : Type
  /-- The control is finite: the transition function is a finite table. -/
  [fintypeΛ : Fintype Λ]
  /-- The state the machine starts in. -/
  init : Λ
  /-- One step: read every stack top, then move to a new state and perform one action, or
  halt (`none`). -/
  step : Λ → (Stack → Option Γ) → Option (Λ × Act Γ)

attribute [instance] Machine.fintypeΛ

variable {Γ : Type}

/-- Perform one memory action. -/
def Act.apply : Act Γ → (Stack → List Γ) → Stack → List Γ
  | .push k x, S => Function.update S k (x :: S k)
  | .pop k, S => Function.update S k (S k).tail
  | .nop, S => S

/-- One action changes the length of any one stack by at most one. This is the whole
content of "the step count is a time measure": it bounds output size by input size plus
running time. -/
lemma Act.length_apply_le (act : Act Γ) (S : Stack → List Γ) (k : Stack) :
    (act.apply S k).length ≤ (S k).length + 1 := by
  cases act with
  | push j x =>
      by_cases h : k = j
      · subst h; simp [Act.apply, Function.update_self]
      · simp [Act.apply, Function.update_of_ne h]
  | pop j =>
      by_cases h : k = j
      · subst h; simp [Act.apply, Function.update_self]; omega
      · simp [Act.apply, Function.update_of_ne h]
  | nop => simp [Act.apply]

/-- One step of `M`, as a partial function on configurations. -/
def stepCfg (M : Machine Γ) (c : Cfg Γ M.Λ) : Option (Cfg Γ M.Λ) :=
  (M.step c.state fun k => (c.store k).head?).map fun p => ⟨p.1, p.2.apply c.store⟩

/-- `M` has halted in configuration `c`. -/
def Halts (M : Machine Γ) (c : Cfg Γ M.Λ) : Prop := stepCfg M c = none

/-- Run `M` for exactly `t` steps, or `none` if it halts first. Unlike
`StateTransition.Reaches₁`, the step count is a parameter of the statement rather than an
existential inside a transitive closure — which is the entire point of the model (see the
Stage-0 probe in `Scratch_TimedRespects.lean`). -/
def runFor (M : Machine Γ) : ℕ → Cfg Γ M.Λ → Option (Cfg Γ M.Λ)
  | 0, c => some c
  | t + 1, c => (stepCfg M c).bind (runFor M t)

@[simp] theorem runFor_zero (M : Machine Γ) (c : Cfg Γ M.Λ) : runFor M 0 c = some c := rfl

lemma runFor_succ (M : Machine Γ) (t : ℕ) (c : Cfg Γ M.Λ) :
    runFor M (t + 1) c = (stepCfg M c).bind (runFor M t) := rfl

/-- Runs concatenate, and their lengths add. -/
lemma runFor_add (M : Machine Γ) (s t : ℕ) (c : Cfg Γ M.Λ) :
    runFor M (s + t) c = (runFor M s c).bind (runFor M t) := by
  induction s generalizing c with
  | zero => simp
  | succ s ih =>
      have key : runFor M (s + t) = fun c' => (runFor M s c').bind (runFor M t) :=
        funext fun c' => ih c'
      rw [show s + 1 + t = (s + t) + 1 by omega, runFor_succ, runFor_succ,
        Option.bind_assoc, key]

/-- The canonical memory layout: the word `w` on `main`, every other stack empty. Both the
initial and the halting configuration of a run are required to have this shape; that is
what lets one machine be started on another's output. -/
def layout (w : List Γ) : Stack → List Γ := fun k => if k = .main then w else []

@[simp] theorem layout_main (w : List Γ) : layout w .main = w := rfl

/-- The initial configuration of `M` on input `x`. -/
def initCfg (M : Machine Γ) (x : List Γ) : Cfg Γ M.Λ := ⟨M.init, layout x⟩

/-- **`M` maps `x` to `y` within `t` steps.** The machine started on `x` in the canonical
layout halts after at most `t` steps in a configuration whose memory is the canonical layout
of `y`: the output is on `main` and the scratch stacks have been cleared.

Requiring the halting memory to be a `layout` is a convention, not a restriction — clearing
scratch stacks costs a number of steps linear in what was written there — and it is what
makes `seq` (below) a construction on control states alone. -/
def RunsInTime (M : Machine Γ) (x y : List Γ) (t : ℕ) : Prop :=
  ∃ s ≤ t, ∃ q : M.Λ, runFor M s (initCfg M x) = some ⟨q, layout y⟩ ∧ Halts M ⟨q, layout y⟩

lemma RunsInTime.mono {M : Machine Γ} {x y : List Γ} {t t' : ℕ} (h : RunsInTime M x y t)
    (ht : t ≤ t') : RunsInTime M x y t' := by
  obtain ⟨s, hs, q, hrun, hhalt⟩ := h
  exact ⟨s, hs.trans ht, q, hrun, hhalt⟩

/-! ### Time bounds output size -/

lemma length_store_stepCfg_le {M : Machine Γ} {c c' : Cfg Γ M.Λ} (h : stepCfg M c = some c')
    (k : Stack) : (c'.store k).length ≤ (c.store k).length + 1 := by
  rw [stepCfg, Option.map_eq_some_iff] at h
  obtain ⟨p, -, rfl⟩ := h
  exact Act.length_apply_le _ _ _

lemma length_store_runFor_le {M : Machine Γ} : ∀ {t : ℕ} {c c' : Cfg Γ M.Λ},
    runFor M t c = some c' → ∀ k : Stack, (c'.store k).length ≤ (c.store k).length + t
  | 0, c, c', h, k => by cases h; simp
  | t + 1, c, c', h, k => by
      rw [runFor_succ, Option.bind_eq_some_iff] at h
      obtain ⟨d, hd, hrest⟩ := h
      have h₁ := length_store_runFor_le hrest k
      have h₂ := length_store_stepCfg_le hd k
      omega

/-- A machine cannot write more than one symbol per step, so a time bound is also an output
size bound. This is what makes the polynomial class closed under composition: the second
machine's clock is evaluated at a polynomially bounded length. -/
lemma RunsInTime.length_output_le {M : Machine Γ} {x y : List Γ} {t : ℕ}
    (h : RunsInTime M x y t) : y.length ≤ x.length + t := by
  obtain ⟨s, hs, q, hrun, -⟩ := h
  have := length_store_runFor_le hrun .main
  simp only [initCfg, layout_main] at this
  omega

/-! ### The polynomial-time class -/

/-- **The polynomial-time machine class.** `f : List Γ → List Γ` is machine-poly-computable
if one machine computes it on every input within a clock of the normal form
`fun n => a * (n + 1) ^ k + a`, `n` being the input length.

This is deliberately the same shape as `LogicalInduction.EfficientlyComputable`: an
existential over the program and over the clock's `(a, k)`. It is *not* related to it by
any theorem — the inclusion is Stage 2 of `notes/boundary-efficiency-model.md` and is not
started. The `Fintype Γ` hypothesis is part of the model, not a convenience: an infinite
alphabet would let the transition function act as an oracle. -/
def MachinePolyEC [Fintype Γ] (f : List Γ → List Γ) : Prop :=
  ∃ (M : Machine Γ) (a k : ℕ), ∀ x : List Γ,
    RunsInTime M x (f x) (a * (x.length + 1) ^ k + a)

end LogicalInduction.Counted
