/-
# A counted-step machine and its polynomial-time class

Stage 1 of the efficiency-model program (`notes/boundary-efficiency-model.md`). This file
defines a machine whose steps are *counted by construction*, together with the polynomial
time class `MachinePolyEC` built over it.

**Model.** A machine is a finite control (`Machine.Λ`, a `Fintype`) over a stack memory. One
step reads the top symbol of every stack and performs exactly one memory action: push a
symbol onto one stack, pop one stack, or nothing (`Act`). The step function returning `none`
is halting. This is Mathlib's `Turing.TM2` primitive set, restricted to one action per unit
of time rather than one structured statement; two stacks already simulate a single-tape
Turing machine with linear overhead, so it is a genuine machine class rather than a
unit-cost RAM.

**Memory shape: a private block over a shared I/O stack.** A machine declares a finite index
type `Machine.K` of *private* stacks; its stacks are `Stack K = Option K`, where `none`
(`Stack.io`) is the input/output stack every machine shares and `some k` is private scratch.
This is what makes machines composable. Two machines are combined by relabelling each into
its own block of a larger index type (`Prog.relabel`, `Closure.lean`); a relabelled machine
then *provably* cannot see or touch the other blocks, because its transition function is
precomposed with the restriction of the stack tops to its own block. The frame property
composite constructions need is therefore a consequence of the definition rather than a side
condition to discharge.

**Halting convention.** A run starts with the input on the shared stack and every private
stack empty, and ends with the output on the shared stack; private stacks may be left dirty
(`RunsInTime`). Requiring them to be cleared would buy nothing and cost a cleanup phase in
every construction: a machine's private stacks are invisible to anything it is embedded in,
and each embedded machine is started once, on a block that is empty because the embedding
gives it a fresh one.

**Finiteness is what makes the class honest.** With `Fintype Γ`, `Fintype K` and `Fintype Λ`
the transition function is a finite table, so no information can be smuggled into the
control. Over an infinite alphabet it would be an arbitrary map on an infinite domain, i.e.
an oracle.

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
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.DeriveFintype

namespace LogicalInduction.Counted

variable {Γ S S' Λ : Type}

/-! ## Configurations and programs over an arbitrary stack index

The semantics is stated for an arbitrary stack index type `S` so that the same `runFor` and
`HaltsFrom` vocabulary applies to a machine, to a machine relabelled into a larger memory,
and to the primitive phase programs of a composite construction. -/

/-- The memory action performed by one step: push a symbol onto one stack, pop one stack, or
leave memory alone. Exactly one action per step is what makes the step count a faithful time
measure. -/
inductive Act (S : Type) (Γ : Type) where
  | push : S → Γ → Act S Γ
  | pop : S → Act S Γ
  | nop : Act S Γ

/-- Perform one memory action. -/
def Act.apply [DecidableEq S] : Act S Γ → (S → List Γ) → S → List Γ
  | .push k x, T => Function.update T k (x :: T k)
  | .pop k, T => Function.update T k (T k).tail
  | .nop, T => T

/-- One action changes the length of any one stack by at most one. This is the whole content
of "the step count is a time measure": it bounds output size by input size plus running
time. -/
lemma Act.length_apply_le [DecidableEq S] (act : Act S Γ) (T : S → List Γ) (k : S) :
    (act.apply T k).length ≤ (T k).length + 1 := by
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

/-- An action leaves untouched every stack it does not name. -/
lemma Act.apply_of_ne [DecidableEq S] : ∀ (act : Act S Γ) (T : S → List Γ) {k : S},
    (∀ j x, act ≠ .push j x ∨ j ≠ k) → (∀ j, act ≠ .pop j ∨ j ≠ k) → act.apply T k = T k
  | .push j x, T, k, h₁, _ => by
      rcases h₁ j x with h | h
      · exact absurd rfl h
      · simp [Act.apply, Function.update_of_ne (Ne.symm h)]
  | .pop j, T, k, _, h₂ => by
      rcases h₂ j with h | h
      · exact absurd rfl h
      · simp [Act.apply, Function.update_of_ne (Ne.symm h)]
  | .nop, T, k, _, _ => rfl

/-- A machine configuration: the control state and the contents of the stacks (each written
top-first). -/
structure Cfg (Γ S Λ : Type) where
  /-- The current control state. -/
  state : Λ
  /-- The contents of each stack, top of stack first.  (Named `store` rather than `stacks`:
  Mathlib's `@[stacks]` attribute reserves `stacks` as a token.) -/
  store : S → List Γ

/-- A transition function: read every stack top, then move to a new state performing one
action, or halt (`none`). -/
abbrev Prog (Γ S Λ : Type) := Λ → (S → Option Γ) → Option (Λ × Act S Γ)

/-- One step of `P`, as a partial function on configurations. -/
def stepCfg [DecidableEq S] (P : Prog Γ S Λ) (c : Cfg Γ S Λ) : Option (Cfg Γ S Λ) :=
  (P c.state fun k => (c.store k).head?).map fun p => ⟨p.1, p.2.apply c.store⟩

/-- Run `P` for exactly `t` steps, or `none` if it halts first. Unlike
`StateTransition.Reaches₁`, the step count is a parameter of the statement rather than an
existential inside a transitive closure — which is the entire point of the model (see the
Stage-0 probe in `TimedRespectsProbe.lean`). -/
def runFor [DecidableEq S] (P : Prog Γ S Λ) : ℕ → Cfg Γ S Λ → Option (Cfg Γ S Λ)
  | 0, c => some c
  | t + 1, c => (stepCfg P c).bind (runFor P t)

@[simp] lemma runFor_zero [DecidableEq S] (P : Prog Γ S Λ) (c : Cfg Γ S Λ) :
    runFor P 0 c = some c := rfl

lemma runFor_succ [DecidableEq S] (P : Prog Γ S Λ) (t : ℕ) (c : Cfg Γ S Λ) :
    runFor P (t + 1) c = (stepCfg P c).bind (runFor P t) := rfl

/-- Runs concatenate, and their lengths add. -/
lemma runFor_add [DecidableEq S] (P : Prog Γ S Λ) (s t : ℕ) (c : Cfg Γ S Λ) :
    runFor P (s + t) c = (runFor P s c).bind (runFor P t) := by
  induction s generalizing c with
  | zero => simp
  | succ s ih =>
      have key : runFor P (s + t) = fun c' => (runFor P s c').bind (runFor P t) :=
        funext fun c' => ih c'
      rw [show s + 1 + t = (s + t) + 1 by omega, runFor_succ, runFor_succ,
        Option.bind_assoc, key]

/-- **`P`, started in state `q` on store `T`, halts within `t` steps leaving store `T'`.**
This store-to-store form is the one composite constructions chain: the intermediate stores
of a multi-phase machine are not canonical layouts, so a statement fixing the layout at both
ends could not be composed. -/
def HaltsFrom [DecidableEq S] (P : Prog Γ S Λ) (q : Λ) (T T' : S → List Γ) (t : ℕ) : Prop :=
  ∃ s ≤ t, ∃ r : Λ, runFor P s ⟨q, T⟩ = some ⟨r, T'⟩ ∧ stepCfg P ⟨r, T'⟩ = none

lemma HaltsFrom.mono [DecidableEq S] {P : Prog Γ S Λ} {q : Λ} {T T' : S → List Γ} {t t' : ℕ}
    (h : HaltsFrom P q T T' t) (ht : t ≤ t') : HaltsFrom P q T T' t' := by
  obtain ⟨s, hs, r, hrun, hhalt⟩ := h
  exact ⟨s, hs.trans ht, r, hrun, hhalt⟩

/-! ### Time bounds output size -/

lemma length_store_stepCfg_le [DecidableEq S] {P : Prog Γ S Λ} {c c' : Cfg Γ S Λ}
    (h : stepCfg P c = some c') (k : S) : (c'.store k).length ≤ (c.store k).length + 1 := by
  rw [stepCfg, Option.map_eq_some_iff] at h
  obtain ⟨p, -, rfl⟩ := h
  exact Act.length_apply_le _ _ _

lemma length_store_runFor_le [DecidableEq S] {P : Prog Γ S Λ} : ∀ {t : ℕ} {c c' : Cfg Γ S Λ},
    runFor P t c = some c' → ∀ k : S, (c'.store k).length ≤ (c.store k).length + t
  | 0, c, c', h, k => by cases h; simp
  | t + 1, c, c', h, k => by
      rw [runFor_succ, Option.bind_eq_some_iff] at h
      obtain ⟨d, hd, hrest⟩ := h
      have h₁ := length_store_runFor_le hrest k
      have h₂ := length_store_stepCfg_le hd k
      omega

lemma HaltsFrom.length_le [DecidableEq S] {P : Prog Γ S Λ} {q : Λ} {T T' : S → List Γ} {t : ℕ}
    (h : HaltsFrom P q T T' t) (k : S) : (T' k).length ≤ (T k).length + t := by
  obtain ⟨s, hs, r, hrun, -⟩ := h
  have h' := length_store_runFor_le hrun k
  simp only at h'
  omega

/-! ## Machines -/

/-- The stacks of a machine with private block `K`: the shared input/output stack
(`Stack.io`) together with one private stack for each `k : K`. -/
abbrev Stack (K : Type) := Option K

/-- The shared input/output stack. -/
def Stack.io {K : Type} : Stack K := none

/-- A private stack of the block `K`. -/
def Stack.priv {K : Type} (k : K) : Stack K := some k

/-- A counted-step machine over the alphabet `Γ`: a finite private stack block, a finite
control, and a transition function over `Stack K`.

Both index types are bundled rather than parameters, so that composite constructions may
enlarge them and so that `MachinePolyEC` can quantify over machines without quantifying over
types carrying instances. -/
structure Machine (Γ : Type) where
  /-- The machine's private stacks. -/
  K : Type
  /-- The private block is finite. -/
  [fintypeK : Fintype K]
  /-- Stack indices are decidable, so that a stack may be updated. -/
  [decEqK : DecidableEq K]
  /-- The control states. -/
  Λ : Type
  /-- The control is finite: the transition function is a finite table. -/
  [fintypeΛ : Fintype Λ]
  /-- The state the machine starts in. -/
  init : Λ
  /-- The transition function. -/
  step : Prog Γ (Stack K) Λ

attribute [instance] Machine.fintypeK Machine.decEqK Machine.fintypeΛ

/-- The canonical initial memory: the word `w` on the shared stack, every private stack
empty. -/
def layout {K : Type} (w : List Γ) : Stack K → List Γ
  | none => w
  | some _ => []

@[simp] lemma layout_io {K : Type} (w : List Γ) : layout (K := K) w Stack.io = w := rfl

@[simp] lemma layout_priv {K : Type} (w : List Γ) (k : K) :
    layout w (Stack.priv k) = [] := rfl

/-- **`M` maps `x` to `y` within `t` steps.** The machine started on `x` in the canonical
initial memory halts after at most `t` steps with `y` on the shared stack. Private stacks may
be left dirty: they are invisible to any construction `M` is embedded in, so clearing them
would be pure overhead. -/
def RunsInTime (M : Machine Γ) (x y : List Γ) (t : ℕ) : Prop :=
  ∃ T' : Stack M.K → List Γ, T' Stack.io = y ∧ HaltsFrom M.step M.init (layout x) T' t

lemma RunsInTime.mono {M : Machine Γ} {x y : List Γ} {t t' : ℕ} (h : RunsInTime M x y t)
    (ht : t ≤ t') : RunsInTime M x y t' := by
  obtain ⟨T', hout, hrun⟩ := h
  exact ⟨T', hout, hrun.mono ht⟩

/-- A machine cannot write more than one symbol per step, so a time bound is also an output
size bound. This is what makes the polynomial class closed under composition: the second
machine's clock is evaluated at a polynomially bounded length. -/
lemma RunsInTime.length_output_le {M : Machine Γ} {x y : List Γ} {t : ℕ}
    (h : RunsInTime M x y t) : y.length ≤ x.length + t := by
  obtain ⟨T', hout, hrun⟩ := h
  have h' := hrun.length_le Stack.io
  rw [hout] at h'
  simpa [Stack.io, layout] using h'

/-! ## The polynomial-time class -/

/-- **The polynomial-time machine class.** `f : List Γ → List Γ` is machine-poly-computable
if one machine computes it on every input within a clock of the normal form
`fun n => a * (n + 1) ^ k + a`, `n` being the input length.

This is deliberately the same shape as `LogicalInduction.EfficientlyComputable`: an
existential over the program and over the clock's `(a, k)`. It is *not* related to it by any
theorem — the inclusion is Stage 2 of `notes/boundary-efficiency-model.md` and is not
started. The `Fintype Γ` hypothesis is part of the model, not a convenience: an infinite
alphabet would let the transition function act as an oracle. -/
def MachinePolyEC [Fintype Γ] (f : List Γ → List Γ) : Prop :=
  ∃ (M : Machine Γ) (a k : ℕ), ∀ x : List Γ,
    RunsInTime M x (f x) (a * (x.length + 1) ^ k + a)

end LogicalInduction.Counted
