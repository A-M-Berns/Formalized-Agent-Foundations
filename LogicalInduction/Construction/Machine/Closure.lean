/-
# Composing machines: sequencing, relabelling, and the composition closure

Stage 1 of the efficiency-model program (`notes/boundary-efficiency-model.md`), continued
from `Basic.lean`.

Two independent constructions, both stated on `Prog` (a transition function over a bare
stack index) rather than on `Machine`, so that they apply equally to a machine and to a
phase of a composite:

* **`seqProg`** — run one program, then another *over the same memory*. The composite's
  states are the disjoint union, and the switch is a single `nop` step that hands the store
  over untouched. `HaltsFrom.seq` chains two store-to-store runs with additive time; a
  multi-phase machine is built by iterating it, and no data movement is ever required.
* **`Prog.relabel`** — carry a program along an injection of stack indices. Its transition
  function is precomposed with the restriction of the stack tops to the image, so a
  relabelled program *cannot see* the stacks outside it; `HaltsFrom.relabel` records both
  halves of that: the run mirrors the original on the image, and everything off the image is
  untouched. This is the frame property, obtained from the definition rather than assumed.

`MachinePolyEC.comp` combines the two: a composite machine over `K₁ ⊕ K₂` runs each
component relabelled into its own private block, sharing the I/O stack. This is the closure
Mathlib currently records as open for its own poly-time class
(`proof_wanted Turing.TM2ComputableInPolyTime.comp`).
-/
import LogicalInduction.Construction.Machine.Basic
import Mathlib.Tactic.Ring

namespace LogicalInduction.Counted

variable {Γ S S' Λ Λ₁ Λ₂ : Type}

/-! ## Sequencing two programs over a common memory -/

/-- **Sequential composition.** Run `P₁` from the given state; on the step where `P₁` would
halt, move to `P₂`'s initial state instead, leaving memory alone; then run `P₂`. The handover
costs exactly one step. -/
def seqProg (P₁ : Prog Γ S Λ₁) (init₂ : Λ₂) (P₂ : Prog Γ S Λ₂) : Prog Γ S (Λ₁ ⊕ Λ₂) :=
  fun q tops =>
    match q with
    | Sum.inl q₁ =>
        match P₁ q₁ tops with
        | some (q', act) => some (Sum.inl q', act)
        | none => some (Sum.inr init₂, Act.nop)
    | Sum.inr q₂ => (P₂ q₂ tops).map fun p => (Sum.inr p.1, p.2)

/-- A first-stage configuration, as a configuration of the composite. -/
def seqL (Λ₂ : Type) (c : Cfg Γ S Λ₁) : Cfg Γ S (Λ₁ ⊕ Λ₂) := ⟨Sum.inl c.state, c.store⟩

/-- A second-stage configuration, as a configuration of the composite. -/
def seqR (Λ₁ : Type) (c : Cfg Γ S Λ₂) : Cfg Γ S (Λ₁ ⊕ Λ₂) := ⟨Sum.inr c.state, c.store⟩

section Seq

variable [DecidableEq S] {P₁ : Prog Γ S Λ₁} {P₂ : Prog Γ S Λ₂} {init₂ : Λ₂}

/-- While the first stage is running, the composite mirrors it step for step. -/
lemma stepCfg_seqL_some {c c' : Cfg Γ S Λ₁} (h : stepCfg P₁ c = some c') :
    stepCfg (seqProg P₁ init₂ P₂) (seqL Λ₂ c) = some (seqL Λ₂ c') := by
  rw [stepCfg, Option.map_eq_some_iff] at h
  obtain ⟨⟨q', act⟩, hstep, rfl⟩ := h
  simp only [stepCfg, seqL, seqProg, hstep, Option.map_some]

/-- The handover: the step on which the first stage would halt enters the second stage's
initial state, leaving memory untouched. -/
lemma stepCfg_seqL_none {c : Cfg Γ S Λ₁} (h : stepCfg P₁ c = none) :
    stepCfg (seqProg P₁ init₂ P₂) (seqL Λ₂ c) = some (seqR Λ₁ ⟨init₂, c.store⟩) := by
  rw [stepCfg, Option.map_eq_none_iff] at h
  simp only [stepCfg, seqL, seqR, seqProg, h, Option.map_some]
  rfl

lemma stepCfg_seqR_some {c c' : Cfg Γ S Λ₂} (h : stepCfg P₂ c = some c') :
    stepCfg (seqProg P₁ init₂ P₂) (seqR Λ₁ c) = some (seqR Λ₁ c') := by
  rw [stepCfg, Option.map_eq_some_iff] at h
  obtain ⟨⟨q', act⟩, hstep, rfl⟩ := h
  simp only [stepCfg, seqR, seqProg, hstep, Option.map_some]

lemma stepCfg_seqR_none {c : Cfg Γ S Λ₂} (h : stepCfg P₂ c = none) :
    stepCfg (seqProg P₁ init₂ P₂) (seqR Λ₁ c) = none := by
  rw [stepCfg, Option.map_eq_none_iff] at h
  simp only [stepCfg, seqR, seqProg, h]
  rfl

lemma runFor_seqL : ∀ {t : ℕ} {c c' : Cfg Γ S Λ₁}, runFor P₁ t c = some c' →
    runFor (seqProg P₁ init₂ P₂) t (seqL Λ₂ c) = some (seqL Λ₂ c')
  | 0, c, c', h => by cases h; rfl
  | t + 1, c, c', h => by
      rw [runFor_succ, Option.bind_eq_some_iff] at h
      obtain ⟨d, hd, hrest⟩ := h
      rw [runFor_succ, stepCfg_seqL_some (P₂ := P₂) (init₂ := init₂) hd, Option.bind_some]
      exact runFor_seqL hrest

lemma runFor_seqR : ∀ {t : ℕ} {c c' : Cfg Γ S Λ₂}, runFor P₂ t c = some c' →
    runFor (seqProg P₁ init₂ P₂) t (seqR Λ₁ c) = some (seqR Λ₁ c')
  | 0, c, c', h => by cases h; rfl
  | t + 1, c, c', h => by
      rw [runFor_succ, Option.bind_eq_some_iff] at h
      obtain ⟨d, hd, hrest⟩ := h
      rw [runFor_succ, stepCfg_seqR_some (P₁ := P₁) (init₂ := init₂) hd, Option.bind_some]
      exact runFor_seqR hrest

/-- **Sequencing is additive in time**, with exactly one step of overhead for the handover.
This is the lemma a multi-phase construction iterates: it speaks about arbitrary stores, so
the intermediate memory of a composite need not be in any canonical form. -/
lemma HaltsFrom.seq {q₁ : Λ₁} {T T' T'' : S → List Γ} {t₁ t₂ : ℕ}
    (h₁ : HaltsFrom P₁ q₁ T T' t₁) (h₂ : HaltsFrom P₂ init₂ T' T'' t₂) :
    HaltsFrom (seqProg P₁ init₂ P₂) (Sum.inl q₁) T T'' (t₁ + 1 + t₂) := by
  obtain ⟨s₁, hs₁, r₁, hrun₁, hhalt₁⟩ := h₁
  obtain ⟨s₂, hs₂, r₂, hrun₂, hhalt₂⟩ := h₂
  refine ⟨s₁ + 1 + s₂, by omega, Sum.inr r₂, ?_, ?_⟩
  · have hstage₁ : runFor (seqProg P₁ init₂ P₂) s₁ ⟨Sum.inl q₁, T⟩
        = some (seqL Λ₂ ⟨r₁, T'⟩) := runFor_seqL hrun₁
    have hswitch : runFor (seqProg P₁ init₂ P₂) 1 (seqL Λ₂ ⟨r₁, T'⟩)
        = some (seqR Λ₁ ⟨init₂, T'⟩) := by
      rw [runFor_succ, stepCfg_seqL_none (P₂ := P₂) (init₂ := init₂) hhalt₁]; rfl
    have hstage₂ : runFor (seqProg P₁ init₂ P₂) s₂ (seqR Λ₁ ⟨init₂, T'⟩)
        = some (seqR Λ₁ ⟨r₂, T''⟩) := runFor_seqR hrun₂
    rw [runFor_add, runFor_add, hstage₁, Option.bind_some, hswitch, Option.bind_some,
      hstage₂]
    rfl
  · exact stepCfg_seqR_none hhalt₂

end Seq

/-! ## Relabelling a program into a larger memory -/

/-- Carry an action along a map of stack indices. -/
def Act.relabel (e : S → S') : Act S Γ → Act S' Γ
  | .push k x => .push (e k) x
  | .pop k => .pop (e k)
  | .nop => .nop

/-- **Carry a program along a map of stack indices.** The transition function is
precomposed with the restriction of the stack tops to the image, so the relabelled program
cannot even *read* a stack outside it. -/
def Prog.relabel (e : S → S') (P : Prog Γ S Λ) : Prog Γ S' Λ :=
  fun q tops => (P q fun k => tops (e k)).map fun p => (p.1, p.2.relabel e)

section Relabel

variable [DecidableEq S] [DecidableEq S'] {e : S → S'}

/-- On the image of the embedding, a relabelled action does what the original action does. -/
lemma Act.apply_relabel_mem (he : Function.Injective e) (act : Act S Γ) {T : S' → List Γ}
    {U : S → List Γ} (h : ∀ k, T (e k) = U k) (k : S) :
    (act.relabel e).apply T (e k) = act.apply U k := by
  cases act with
  | push j x =>
      by_cases hk : k = j
      · subst hk; simp [Act.relabel, Act.apply, Function.update_self, h]
      · rw [Act.relabel, Act.apply, Act.apply,
          Function.update_of_ne (fun hc => hk (he hc)) , Function.update_of_ne hk]
        exact h k
  | pop j =>
      by_cases hk : k = j
      · subst hk; simp [Act.relabel, Act.apply, Function.update_self, h]
      · rw [Act.relabel, Act.apply, Act.apply,
          Function.update_of_ne (fun hc => hk (he hc)), Function.update_of_ne hk]
        exact h k
  | nop => exact h k

omit [DecidableEq S] in
/-- Off the image of the embedding, a relabelled action changes nothing. This is the frame
half of the embedding. -/
lemma Act.apply_relabel_not_mem (act : Act S Γ) (T : S' → List Γ) {j : S'}
    (hj : ∀ k, e k ≠ j) : (act.relabel e).apply T j = T j := by
  cases act with
  | push m x => exact Function.update_of_ne (Ne.symm (hj m)) _ _
  | pop m => exact Function.update_of_ne (Ne.symm (hj m)) _ _
  | nop => rfl

lemma stepCfg_relabel_some {P : Prog Γ S Λ} {q q' : Λ} {U U' : S → List Γ} {T : S' → List Γ}
    (he : Function.Injective e) (halign : ∀ k, T (e k) = U k)
    (h : stepCfg P ⟨q, U⟩ = some ⟨q', U'⟩) :
    ∃ T' : S' → List Γ, stepCfg (P.relabel e) ⟨q, T⟩ = some ⟨q', T'⟩ ∧
      (∀ k, T' (e k) = U' k) ∧ (∀ j, (∀ k, e k ≠ j) → T' j = T j) := by
  rw [stepCfg, Option.map_eq_some_iff] at h
  obtain ⟨⟨r, act⟩, hstep, hcfg⟩ := h
  have htops : (fun k => (T (e k)).head?) = fun k => (U k).head? := by
    funext k; rw [halign k]
  have hq : r = q' := congrArg Cfg.state hcfg
  have hU : act.apply U = U' := congrArg Cfg.store hcfg
  subst hq
  refine ⟨(act.relabel e).apply T, ?_, ?_, ?_⟩
  · simp only [stepCfg, Prog.relabel, htops, hstep, Option.map_some]
  · intro k; rw [Act.apply_relabel_mem he act halign k, hU]
  · intro j hj; exact Act.apply_relabel_not_mem act T hj

lemma stepCfg_relabel_none {P : Prog Γ S Λ} {q : Λ} {U : S → List Γ} {T : S' → List Γ}
    (halign : ∀ k, T (e k) = U k) (h : stepCfg P ⟨q, U⟩ = none) :
    stepCfg (P.relabel e) ⟨q, T⟩ = none := by
  rw [stepCfg, Option.map_eq_none_iff] at h
  have htops : (fun k => (T (e k)).head?) = fun k => (U k).head? := by
    funext k; rw [halign k]
  simp only [stepCfg, Prog.relabel, htops, h]
  rfl

lemma runFor_relabel {P : Prog Γ S Λ} (he : Function.Injective e) :
    ∀ {t : ℕ} {q q' : Λ} {U U' : S → List Γ} {T : S' → List Γ}, (∀ k, T (e k) = U k) →
      runFor P t ⟨q, U⟩ = some ⟨q', U'⟩ →
      ∃ T' : S' → List Γ, runFor (P.relabel e) t ⟨q, T⟩ = some ⟨q', T'⟩ ∧
        (∀ k, T' (e k) = U' k) ∧ (∀ j, (∀ k, e k ≠ j) → T' j = T j)
  | 0, q, q', U, U', T, halign, h => by
      cases h
      exact ⟨T, rfl, halign, fun _ _ => rfl⟩
  | t + 1, q, q', U, U', T, halign, h => by
      rw [runFor_succ, Option.bind_eq_some_iff] at h
      obtain ⟨⟨qm, Um⟩, hstep, hrest⟩ := h
      obtain ⟨Tm, hstepT, halignm, hframem⟩ := stepCfg_relabel_some he halign hstep
      obtain ⟨T', hrunT, halign', hframe'⟩ := runFor_relabel he halignm hrest
      refine ⟨T', ?_, halign', fun j hj => ?_⟩
      · rw [runFor_succ, hstepT, Option.bind_some]; exact hrunT
      · rw [hframe' j hj, hframem j hj]

/-- **The embedding/frame lemma.** A program relabelled into a larger memory runs exactly as
it did on its own block, and leaves every stack outside that block untouched.

The second conclusion is what a composite construction needs and what the previous
fixed-memory design could not provide: data parked outside a sub-machine's block survives its
run, by construction. -/
lemma HaltsFrom.relabel {P : Prog Γ S Λ} {q : Λ} {U U' : S → List Γ} {T : S' → List Γ}
    {t : ℕ} (he : Function.Injective e) (halign : ∀ k, T (e k) = U k)
    (h : HaltsFrom P q U U' t) :
    ∃ T' : S' → List Γ, HaltsFrom (P.relabel e) q T T' t ∧
      (∀ k, T' (e k) = U' k) ∧ (∀ j, (∀ k, e k ≠ j) → T' j = T j) := by
  obtain ⟨s, hs, r, hrun, hhalt⟩ := h
  obtain ⟨T', hrunT, halign', hframe⟩ := runFor_relabel he halign hrun
  exact ⟨T', ⟨s, hs, r, hrunT, stepCfg_relabel_none halign' hhalt⟩, halign', hframe⟩

end Relabel

/-! ## Embedding a machine's private block into a sum -/

/-- The left block of a sum of private stack blocks, sharing the I/O stack. -/
def stackInl (K₁ K₂ : Type) : Stack K₁ → Stack (K₁ ⊕ K₂)
  | none => none
  | some k => some (Sum.inl k)

/-- The right block of a sum of private stack blocks, sharing the I/O stack. -/
def stackInr (K₁ K₂ : Type) : Stack K₂ → Stack (K₁ ⊕ K₂)
  | none => none
  | some k => some (Sum.inr k)

lemma stackInl_injective (K₁ K₂ : Type) : Function.Injective (stackInl K₁ K₂) := by
  rintro (_ | a) (_ | b) h <;> simp_all [stackInl]

lemma stackInr_injective (K₁ K₂ : Type) : Function.Injective (stackInr K₁ K₂) := by
  rintro (_ | a) (_ | b) h <;> simp_all [stackInr]

lemma stackInl_ne_inr {K₁ K₂ : Type} (k : Stack K₁) (m : K₂) :
    stackInl K₁ K₂ k ≠ some (Sum.inr m) := by
  cases k <;> simp [stackInl]

/-! ## Sequential composition of machines -/

/-- **Sequential composition of machines.** Each component runs relabelled into its own
private block of `K₁ ⊕ K₂`, and they share the I/O stack, so the first machine's output is
already the second machine's input: no data movement. -/
def seq (M₁ M₂ : Machine Γ) : Machine Γ where
  K := M₁.K ⊕ M₂.K
  Λ := M₁.Λ ⊕ M₂.Λ
  init := Sum.inl M₁.init
  step := seqProg (M₁.step.relabel (stackInl M₁.K M₂.K)) M₂.init
    (M₂.step.relabel (stackInr M₁.K M₂.K))

/-- Sequencing composes runs, with one step of handover overhead. -/
lemma seq_runsInTime {M₁ M₂ : Machine Γ} {x u y : List Γ} {t₁ t₂ : ℕ}
    (h₁ : RunsInTime M₁ x u t₁) (h₂ : RunsInTime M₂ u y t₂) :
    RunsInTime (seq M₁ M₂) x y (t₁ + 1 + t₂) := by
  obtain ⟨U₁, hout₁, hrun₁⟩ := h₁
  obtain ⟨U₂, hout₂, hrun₂⟩ := h₂
  -- stage 1, relabelled into the left block
  have halign₁ : ∀ k : Stack M₁.K,
      (layout (K := M₁.K ⊕ M₂.K) x) (stackInl M₁.K M₂.K k) = layout x k := by
    rintro (_ | k) <;> rfl
  obtain ⟨T₁, hrunT₁, hmem₁, hframe₁⟩ :=
    hrun₁.relabel (stackInl_injective M₁.K M₂.K) halign₁
  -- the composite store after stage 1 is `u` on the I/O stack and empty on the right block
  have halign₂ : ∀ k : Stack M₂.K, T₁ (stackInr M₁.K M₂.K k) = layout u k := by
    rintro (_ | k)
    · show T₁ none = u
      have h : T₁ none = U₁ none := hmem₁ none
      rw [h]; exact hout₁
    · exact hframe₁ (some (Sum.inr k)) (fun j => stackInl_ne_inr j k)
  obtain ⟨T₂, hrunT₂, hmem₂, -⟩ :=
    hrun₂.relabel (stackInr_injective M₁.K M₂.K) halign₂
  refine ⟨T₂, ?_, hrunT₁.seq hrunT₂⟩
  show T₂ none = y
  have h : T₂ none = U₂ none := hmem₂ none
  rw [h]; exact hout₂

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
`a * (n + 1) ^ k + a`. Stated as a bare arithmetic fact so that `MachinePolyEC.comp` needs no
polynomial API. -/
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
  have ht₁ : a₁ * N ^ k₁ + a₁ ≤ (2 * a₁ + 1) * N ^ K₁ :=
    (clock_le a₁ (Nat.one_le_pow _ _ hNpos)).trans
      (Nat.mul_le_mul (le_refl _) (hmono _ _ (le_max_left _ _)))
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

/-! ## Closure under composition -/

/-- **The polynomial-time machine class is closed under composition.**

This is the closure Mathlib records as open for its own poly-time class
(`proof_wanted Turing.TM2ComputableInPolyTime.comp`, in
`Mathlib/Computability/TuringMachine/Computable.lean`); the shared I/O stack is what removes
the "copy the output tape to the input tape" phase that makes the statement awkward there. -/
lemma MachinePolyEC.comp [Fintype Γ] {f g : List Γ → List Γ} (hf : MachinePolyEC f)
    (hg : MachinePolyEC g) : MachinePolyEC (fun x => g (f x)) := by
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

end LogicalInduction.Counted
