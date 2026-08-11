/-
# Data-movement phases, and closure of the machine class under pairing

Stage 1 of the efficiency-model program (`notes/boundary-efficiency-model.md`), continued
from `Closure.lean`.

Composition needs no data movement, because the two machines share the I/O stack. Pairing
does: `fun x => pairWord s₀ s₁ (f x) (g x)` must run `f` and `g` on the *same* input, so a
copy of the input has to survive `f`'s run. That is what the private-block memory is for —
the copy is parked on a stack outside `f`'s block, and `HaltsFrom.relabel` says `f` cannot
touch it.

Everything here is built from one primitive, `pump`: a three-beat loop that pops a symbol off
one stack and performs two symbol-dependent actions. `xfer`, `dup` and `emitTagged` are its
three instantiations, and the pairing machine is eight phases chained by `HaltsFrom.seq`.
-/
import LogicalInduction.Construction.Machine.Closure
import Mathlib.Tactic.FinCases

namespace LogicalInduction.Counted

variable {Γ S : Type} [DecidableEq S]

/-! ## The data-movement primitive -/

/-- **The three-beat data-movement loop.** In state `none`, look at the top of `src`: if it
is empty, halt; otherwise pop it and remember the symbol in the control. Then perform
`act₁` on it, then `act₂` on it, and return to `none`.

One loop iteration therefore costs exactly three steps, and every data-movement phase of a
composite machine below is an instance of it. -/
def pump (src : S) (act₁ act₂ : Γ → Act S Γ) : Prog Γ S (Option (Γ × Bool)) :=
  fun q tops =>
    match q with
    | none => (tops src).map fun c => (some (c, false), Act.pop src)
    | some (c, false) => some (some (c, true), act₁ c)
    | some (c, true) => some (none, act₂ c)

lemma pump_halt (src : S) (act₁ act₂ : Γ → Act S Γ) {T : S → List Γ} (h : T src = []) :
    stepCfg (pump src act₁ act₂) ⟨none, T⟩ = none := by
  simp [stepCfg, pump, h]

/-- One iteration of the loop: three steps, popping one symbol and performing both actions. -/
lemma pump_step3 (src : S) (act₁ act₂ : Γ → Act S Γ) {T : S → List Γ} {c : Γ} {rest : List Γ}
    (h : T src = c :: rest) :
    runFor (pump src act₁ act₂) 3 ⟨none, T⟩ =
      some ⟨none, (act₂ c).apply ((act₁ c).apply (Function.update T src rest))⟩ := by
  have h1 : stepCfg (pump src act₁ act₂) ⟨none, T⟩
      = some ⟨some (c, false), Function.update T src rest⟩ := by
    simp [stepCfg, pump, h, Act.apply]
  have h2 : stepCfg (pump src act₁ act₂) ⟨some (c, false), Function.update T src rest⟩
      = some ⟨some (c, true), (act₁ c).apply (Function.update T src rest)⟩ := by
    simp [stepCfg, pump]
  have h3 : stepCfg (pump src act₁ act₂)
        ⟨some (c, true), (act₁ c).apply (Function.update T src rest)⟩
      = some ⟨none, (act₂ c).apply ((act₁ c).apply (Function.update T src rest))⟩ := by
    simp [stepCfg, pump]
  have e3 : runFor (pump src act₁ act₂) 3 ⟨none, T⟩
      = (stepCfg (pump src act₁ act₂) ⟨none, T⟩).bind (runFor (pump src act₁ act₂) 2) := rfl
  have e2 : ∀ c', runFor (pump src act₁ act₂) 2 c'
      = (stepCfg (pump src act₁ act₂) c').bind (runFor (pump src act₁ act₂) 1) := fun _ => rfl
  have e1 : ∀ c', runFor (pump src act₁ act₂) 1 c'
      = (stepCfg (pump src act₁ act₂) c').bind (runFor (pump src act₁ act₂) 0) := fun _ => rfl
  rw [e3, h1, Option.bind_some, e2, h2, Option.bind_some, e1, h3, Option.bind_some,
    runFor_zero]

/-! ## The three phases -/

/-- Move `src` onto `dst`, reversing it. -/
def xfer (src dst : S) : Prog Γ S (Option (Γ × Bool)) :=
  pump src (fun c => Act.push dst c) (fun _ => Act.nop)

/-- Move `src` onto both `d₁` and `d₂`, reversing: the content of `src` is duplicated. This
is the phase that makes pairing possible, and the reason the control carries the popped
symbol. -/
def dup (src d₁ d₂ : S) : Prog Γ S (Option (Γ × Bool)) :=
  pump src (fun c => Act.push d₁ c) (fun c => Act.push d₂ c)

/-- Move `src` onto `dst`, reversing, writing `tag` above each transferred symbol. This is
the self-delimiting encoder of `pairWord`. -/
def emitTagged (src dst : S) (tag : Γ) : Prog Γ S (Option (Γ × Bool)) :=
  pump src (fun c => Act.push dst c) (fun _ => Act.push dst tag)

lemma xfer_run (src dst : S) (hne : dst ≠ src) : ∀ (l : List Γ) (T : S → List Γ), T src = l →
    HaltsFrom (xfer src dst) none T
      (Function.update (Function.update T src []) dst (l.reverse ++ T dst)) (3 * l.length)
  | [], T, hT => by
      have hfix : Function.update (Function.update T src []) dst
          (([] : List Γ).reverse ++ T dst) = T := by
        funext j
        by_cases hj : j = dst
        · subst hj; simp [Function.update_self]
        · by_cases hj2 : j = src
          · subst hj2
            rw [Function.update_of_ne hj, Function.update_self, hT]
          · rw [Function.update_of_ne hj, Function.update_of_ne hj2]
      rw [hfix]
      exact ⟨0, by simp, none, rfl, pump_halt _ _ _ hT⟩
  | c :: rest, T, hT => by
      have h3 := pump_step3 src (fun c => Act.push dst c) (fun _ => Act.nop) hT
      have hsrc : (Function.update T src rest) dst = T dst := Function.update_of_ne hne _ _
      have hstore : (Act.nop).apply ((Act.push dst c).apply (Function.update T src rest))
          = Function.update (Function.update T src rest) dst (c :: T dst) := by
        simp [Act.apply, hsrc]
      rw [hstore] at h3
      set T₁ := Function.update (Function.update T src rest) dst (c :: T dst) with hT₁
      have hT₁src : T₁ src = rest := by
        rw [hT₁, Function.update_of_ne (Ne.symm hne), Function.update_self]
      have hT₁dst : T₁ dst = c :: T dst := by rw [hT₁, Function.update_self]
      have ih := xfer_run src dst hne rest T₁ hT₁src
      have hgoal : Function.update (Function.update T₁ src []) dst (rest.reverse ++ T₁ dst)
          = Function.update (Function.update T src []) dst ((c :: rest).reverse ++ T dst) := by
        funext j
        by_cases hj : j = dst
        · subst hj
          rw [Function.update_self, Function.update_self, hT₁dst, List.reverse_cons,
            List.append_assoc]
          rfl
        · by_cases hj2 : j = src
          · subst hj2
            rw [Function.update_of_ne hj, Function.update_self, Function.update_of_ne hj,
              Function.update_self]
          · rw [Function.update_of_ne hj, Function.update_of_ne hj2,
              Function.update_of_ne hj, Function.update_of_ne hj2, hT₁,
              Function.update_of_ne hj, Function.update_of_ne hj2]
      rw [hgoal] at ih
      refine (HaltsFrom.prepend h3 ih).mono ?_
      simp only [List.length_cons]
      omega

lemma dup_run (src d₁ d₂ : S) (h₁ : d₁ ≠ src) (h₂ : d₂ ≠ src) (h₁₂ : d₁ ≠ d₂) :
    ∀ (l : List Γ) (T : S → List Γ), T src = l →
      HaltsFrom (dup src d₁ d₂) none T
        (Function.update
          (Function.update (Function.update T src []) d₁ (l.reverse ++ T d₁)) d₂
          (l.reverse ++ T d₂)) (3 * l.length)
  | [], T, hT => by
      have hfix : Function.update
          (Function.update (Function.update T src []) d₁ (([] : List Γ).reverse ++ T d₁)) d₂
          (([] : List Γ).reverse ++ T d₂) = T := by
        funext j
        by_cases hj2 : j = d₂
        · subst hj2; simp [Function.update_self]
        · rw [Function.update_of_ne hj2]
          by_cases hj1 : j = d₁
          · subst hj1; simp [Function.update_self]
          · rw [Function.update_of_ne hj1]
            by_cases hjs : j = src
            · subst hjs; rw [Function.update_self, hT]
            · rw [Function.update_of_ne hjs]
      rw [hfix]
      exact ⟨0, by simp, none, rfl, pump_halt _ _ _ hT⟩
  | c :: rest, T, hT => by
      have h3 := pump_step3 src (fun c => Act.push d₁ c) (fun c => Act.push d₂ c) hT
      have e₁ : (Function.update T src rest) d₁ = T d₁ := Function.update_of_ne h₁ _ _
      have e₂ : (Function.update (Function.update T src rest) d₁ (c :: T d₁)) d₂ = T d₂ := by
        rw [Function.update_of_ne (Ne.symm h₁₂), Function.update_of_ne h₂]
      have hstore : (Act.push d₂ c).apply ((Act.push d₁ c).apply (Function.update T src rest))
          = Function.update (Function.update (Function.update T src rest) d₁ (c :: T d₁)) d₂
              (c :: T d₂) := by
        simp only [Act.apply, e₁, e₂]
      rw [hstore] at h3
      set T₁ := Function.update
        (Function.update (Function.update T src rest) d₁ (c :: T d₁)) d₂ (c :: T d₂) with hT₁
      have hT₁src : T₁ src = rest := by
        rw [hT₁, Function.update_of_ne (Ne.symm h₂), Function.update_of_ne (Ne.symm h₁),
          Function.update_self]
      have hT₁d₁ : T₁ d₁ = c :: T d₁ := by
        rw [hT₁, Function.update_of_ne h₁₂, Function.update_self]
      have hT₁d₂ : T₁ d₂ = c :: T d₂ := by rw [hT₁, Function.update_self]
      have ih := dup_run src d₁ d₂ h₁ h₂ h₁₂ rest T₁ hT₁src
      have hgoal : Function.update
            (Function.update (Function.update T₁ src []) d₁ (rest.reverse ++ T₁ d₁)) d₂
            (rest.reverse ++ T₁ d₂)
          = Function.update
            (Function.update (Function.update T src []) d₁ ((c :: rest).reverse ++ T d₁)) d₂
            ((c :: rest).reverse ++ T d₂) := by
        funext j
        have hval : ∀ (v : List Γ), rest.reverse ++ c :: v = (c :: rest).reverse ++ v := by
          intro v; rw [List.reverse_cons, List.append_assoc]; rfl
        by_cases hj2 : j = d₂
        · subst hj2
          rw [Function.update_self, Function.update_self, hT₁d₂, hval]
        · rw [Function.update_of_ne hj2, Function.update_of_ne hj2]
          by_cases hj1 : j = d₁
          · subst hj1
            rw [Function.update_self, Function.update_self, hT₁d₁, hval]
          · rw [Function.update_of_ne hj1, Function.update_of_ne hj1]
            by_cases hjs : j = src
            · subst hjs; rw [Function.update_self, Function.update_self]
            · rw [Function.update_of_ne hjs, Function.update_of_ne hjs, hT₁,
                Function.update_of_ne hj2, Function.update_of_ne hj1,
                Function.update_of_ne hjs]
      rw [hgoal] at ih
      refine (HaltsFrom.prepend h3 ih).mono ?_
      simp only [List.length_cons]
      omega

lemma emitTagged_run (src dst : S) (tag : Γ) (hne : dst ≠ src) :
    ∀ (l : List Γ) (T : S → List Γ), T src = l →
      HaltsFrom (emitTagged src dst tag) none T
        (Function.update (Function.update T src []) dst
          (l.reverse.flatMap (fun c => [tag, c]) ++ T dst)) (3 * l.length)
  | [], T, hT => by
      have hfix : Function.update (Function.update T src []) dst
          (([] : List Γ).reverse.flatMap (fun c => [tag, c]) ++ T dst) = T := by
        funext j
        by_cases hj : j = dst
        · subst hj; simp [Function.update_self]
        · by_cases hj2 : j = src
          · subst hj2
            rw [Function.update_of_ne hj, Function.update_self, hT]
          · rw [Function.update_of_ne hj, Function.update_of_ne hj2]
      rw [hfix]
      exact ⟨0, by simp, none, rfl, pump_halt _ _ _ hT⟩
  | c :: rest, T, hT => by
      have h3 := pump_step3 src (fun c => Act.push dst c) (fun _ => Act.push dst tag) hT
      have hsrc : (Function.update T src rest) dst = T dst := Function.update_of_ne hne _ _
      have hstore :
          (Act.push dst tag).apply ((Act.push dst c).apply (Function.update T src rest))
            = Function.update (Function.update T src rest) dst (tag :: c :: T dst) := by
        simp only [Act.apply, hsrc, Function.update_self, Function.update_idem]
      rw [hstore] at h3
      set T₁ := Function.update (Function.update T src rest) dst (tag :: c :: T dst) with hT₁
      have hT₁src : T₁ src = rest := by
        rw [hT₁, Function.update_of_ne (Ne.symm hne), Function.update_self]
      have hT₁dst : T₁ dst = tag :: c :: T dst := by rw [hT₁, Function.update_self]
      have ih := emitTagged_run src dst tag hne rest T₁ hT₁src
      have hgoal : Function.update (Function.update T₁ src []) dst
            (rest.reverse.flatMap (fun c => [tag, c]) ++ T₁ dst)
          = Function.update (Function.update T src []) dst
            ((c :: rest).reverse.flatMap (fun c => [tag, c]) ++ T dst) := by
        funext j
        by_cases hj : j = dst
        · subst hj
          rw [Function.update_self, Function.update_self, hT₁dst, List.reverse_cons,
            List.flatMap_append]
          simp [List.append_assoc]
        · by_cases hj2 : j = src
          · subst hj2
            rw [Function.update_of_ne hj, Function.update_self, Function.update_of_ne hj,
              Function.update_self]
          · rw [Function.update_of_ne hj, Function.update_of_ne hj2,
              Function.update_of_ne hj, Function.update_of_ne hj2, hT₁,
              Function.update_of_ne hj, Function.update_of_ne hj2]
      rw [hgoal] at ih
      refine (HaltsFrom.prepend h3 ih).mono ?_
      simp only [List.length_cons]
      omega

/-- Push one fixed symbol, then halt. -/
def pushOne (dst : S) (x : Γ) : Prog Γ S Bool :=
  fun q _ => if q then some (false, Act.push dst x) else none

lemma pushOne_run (dst : S) (x : Γ) (T : S → List Γ) :
    HaltsFrom (pushOne dst x) true T (Function.update T dst (x :: T dst)) 1 := by
  refine ⟨1, le_rfl, false, ?_, ?_⟩
  · show (stepCfg (pushOne dst x) ⟨true, T⟩).bind (runFor (pushOne dst x) 0) = _
    simp [stepCfg, pushOne, Act.apply]
  · simp [stepCfg, pushOne]

/-! ## The pairing encoding -/

/-- Self-delimiting pairing of words over an alphabet with two distinguished symbols: each
symbol of `u` is preceded by the tag `s₁`, and `s₀` terminates the `u` block. -/
def pairWord (s₀ s₁ : Γ) (u v : List Γ) : List Γ :=
  (u.flatMap fun x => [s₁, x]) ++ s₀ :: v

/-- Pairing is injective in both arguments, given two distinct tags: `pairWord` really does
encode the pair. -/
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

/-! ## The memory of the pairing machine

Three scratch stacks of its own, plus a private block for each of the two component
machines, so that a copy of the input can be parked outside both. -/

section Pair

variable (M₁ M₂ : Machine Γ)

/-- The private stack block of the pairing machine. -/
abbrev pairK : Type := Fin 3 ⊕ (M₁.K ⊕ M₂.K)

/-- One of the pairing machine's own three scratch stacks. -/
abbrev scratch (i : Fin 3) : Stack (pairK M₁ M₂) := some (Sum.inl i)

/-- The first component machine's block, sharing the I/O stack. -/
abbrev embF : Stack M₁.K → Stack (pairK M₁ M₂) :=
  fun k => stackInr (Fin 3) (M₁.K ⊕ M₂.K) (stackInl M₁.K M₂.K k)

/-- The second component machine's block, sharing the I/O stack. -/
abbrev embG : Stack M₂.K → Stack (pairK M₁ M₂) :=
  fun k => stackInr (Fin 3) (M₁.K ⊕ M₂.K) (stackInr M₁.K M₂.K k)

lemma embF_injective : Function.Injective (embF M₁ M₂) :=
  (stackInr_injective (Fin 3) (M₁.K ⊕ M₂.K)).comp (stackInl_injective M₁.K M₂.K)

lemma embG_injective : Function.Injective (embG M₁ M₂) :=
  (stackInr_injective (Fin 3) (M₁.K ⊕ M₂.K)).comp (stackInr_injective M₁.K M₂.K)

@[simp] lemma scratch_ne_io (i : Fin 3) : scratch M₁ M₂ i ≠ none := by simp [scratch]

@[simp] lemma embF_ne_scratch (k : Stack M₁.K) (i : Fin 3) :
    embF M₁ M₂ k ≠ scratch M₁ M₂ i := by
  cases k <;> simp [embF, scratch, stackInl, stackInr]

@[simp] lemma embG_ne_scratch (k : Stack M₂.K) (i : Fin 3) :
    embG M₁ M₂ k ≠ scratch M₁ M₂ i := by
  cases k <;> simp [embG, scratch, stackInr]

lemma embF_ne_embG_priv (k : Stack M₁.K) (j : M₂.K) :
    embF M₁ M₂ k ≠ embG M₁ M₂ (some j) := by
  cases k <;> simp [embF, embG, stackInl, stackInr]

end Pair

/-! ### Pointwise forms of the phase run lemmas

The phase lemmas above describe their output store as a nest of `Function.update`s. These
restate them in terms of the store's *values*, which is the form a chain of phases can use
without unfolding anything.

These are the forms to use at a bundled machine's memory. A `Function.update`-shaped
statement instantiated at `Stack M.K` mentions `DecidableEq (Stack M.K)`, which the
elaborator may build from the ambient instance while the goal carries the one built from
`Machine.decEqK`; the two are defeq but not syntactically equal, and `rw`/`simp` on the
update nest then fails to fire. The `_val` forms mention no instance beyond the one
`HaltsFrom` already carries, so they do not have that problem. Every phase lemma should
therefore have one, and new phase lemmas should not be stated in update form only. -/

section Pointwise

variable {Γ S : Type} [DecidableEq S]

lemma xfer_run_val (src dst : S) (hne : dst ≠ src) (l : List Γ) (T T' : S → List Γ)
    (hT : T src = l) (h1 : T' src = []) (h2 : T' dst = l.reverse ++ T dst)
    (h3 : ∀ j, j ≠ src → j ≠ dst → T' j = T j) :
    HaltsFrom (xfer src dst) none T T' (3 * l.length) := by
  have h := xfer_run src dst hne l T hT
  have heq : Function.update (Function.update T src []) dst (l.reverse ++ T dst) = T' := by
    funext j
    by_cases hjd : j = dst
    · subst hjd; rw [Function.update_self, h2]
    · rw [Function.update_of_ne hjd]
      by_cases hjs : j = src
      · subst hjs; rw [Function.update_self, h1]
      · rw [Function.update_of_ne hjs, h3 j hjs hjd]
  rwa [heq] at h

lemma dup_run_val (src d₁ d₂ : S) (k₁ : d₁ ≠ src) (k₂ : d₂ ≠ src) (k₁₂ : d₁ ≠ d₂)
    (l : List Γ) (T T' : S → List Γ) (hT : T src = l)
    (h1 : T' src = []) (h2 : T' d₁ = l.reverse ++ T d₁) (h3 : T' d₂ = l.reverse ++ T d₂)
    (h4 : ∀ j, j ≠ src → j ≠ d₁ → j ≠ d₂ → T' j = T j) :
    HaltsFrom (dup src d₁ d₂) none T T' (3 * l.length) := by
  have h := dup_run src d₁ d₂ k₁ k₂ k₁₂ l T hT
  have heq : Function.update
      (Function.update (Function.update T src []) d₁ (l.reverse ++ T d₁)) d₂
      (l.reverse ++ T d₂) = T' := by
    funext j
    by_cases hj2 : j = d₂
    · subst hj2; rw [Function.update_self, h3]
    · rw [Function.update_of_ne hj2]
      by_cases hj1 : j = d₁
      · subst hj1; rw [Function.update_self, h2]
      · rw [Function.update_of_ne hj1]
        by_cases hjs : j = src
        · subst hjs; rw [Function.update_self, h1]
        · rw [Function.update_of_ne hjs, h4 j hjs hj1 hj2]
  rwa [heq] at h

lemma emitTagged_run_val (src dst : S) (tag : Γ) (hne : dst ≠ src) (l : List Γ)
    (T T' : S → List Γ) (hT : T src = l) (h1 : T' src = [])
    (h2 : T' dst = l.reverse.flatMap (fun c => [tag, c]) ++ T dst)
    (h3 : ∀ j, j ≠ src → j ≠ dst → T' j = T j) :
    HaltsFrom (emitTagged src dst tag) none T T' (3 * l.length) := by
  have h := emitTagged_run src dst tag hne l T hT
  have heq : Function.update (Function.update T src []) dst
      (l.reverse.flatMap (fun c => [tag, c]) ++ T dst) = T' := by
    funext j
    by_cases hjd : j = dst
    · subst hjd; rw [Function.update_self, h2]
    · rw [Function.update_of_ne hjd]
      by_cases hjs : j = src
      · subst hjs; rw [Function.update_self, h1]
      · rw [Function.update_of_ne hjs, h3 j hjs hjd]
  rwa [heq] at h

lemma pushOne_run_val (dst : S) (x : Γ) (T T' : S → List Γ) (h1 : T' dst = x :: T dst)
    (h2 : ∀ j, j ≠ dst → T' j = T j) : HaltsFrom (pushOne dst x) true T T' 1 := by
  have h := pushOne_run dst x T
  have heq : Function.update T dst (x :: T dst) = T' := by
    funext j
    by_cases hjd : j = dst
    · subst hjd; rw [Function.update_self, h1]
    · rw [Function.update_of_ne hjd, h2 j hjd]
  rwa [heq] at h

end Pointwise

section Pair

variable {Γ : Type} (M₁ M₂ : Machine Γ)

/-- Case analysis on the pairing machine's stacks: the I/O stack, the three scratch stacks,
and the two component blocks. -/
lemma pairStack_cases {motive : Stack (pairK M₁ M₂) → Prop} (hio : motive none)
    (h0 : motive (scratch M₁ M₂ 0)) (h1 : motive (scratch M₁ M₂ 1))
    (h2 : motive (scratch M₁ M₂ 2)) (hF : ∀ k, motive (embF M₁ M₂ (some k)))
    (hG : ∀ k, motive (embG M₁ M₂ (some k))) : ∀ j, motive j := by
  rintro (_ | (i | (k | k)))
  · exact hio
  · fin_cases i
    · exact h0
    · exact h1
    · exact h2
  · exact hF k
  · exact hG k

/-- The pairing machine's memory, described by the contents of the I/O stack and of its three
scratch stacks, over whatever the two component blocks currently hold. -/
def pairStore (m o t th : List Γ) (B : Stack (pairK M₁ M₂) → List Γ) :
    Stack (pairK M₁ M₂) → List Γ := fun j =>
  if j = none then m
  else if j = scratch M₁ M₂ 0 then o
  else if j = scratch M₁ M₂ 1 then t
  else if j = scratch M₁ M₂ 2 then th
  else B j

variable {M₁ M₂}

@[simp] lemma pairStore_io (m o t th : List Γ) (B : Stack (pairK M₁ M₂) → List Γ) :
    pairStore M₁ M₂ m o t th B none = m := if_pos rfl

@[simp] lemma pairStore_zero (m o t th : List Γ) (B : Stack (pairK M₁ M₂) → List Γ) :
    pairStore M₁ M₂ m o t th B (scratch M₁ M₂ 0) = o := by
  simp [pairStore, scratch]

@[simp] lemma pairStore_one (m o t th : List Γ) (B : Stack (pairK M₁ M₂) → List Γ) :
    pairStore M₁ M₂ m o t th B (scratch M₁ M₂ 1) = t := by
  simp [pairStore, scratch]

@[simp] lemma pairStore_two (m o t th : List Γ) (B : Stack (pairK M₁ M₂) → List Γ) :
    pairStore M₁ M₂ m o t th B (scratch M₁ M₂ 2) = th := by
  simp [pairStore, scratch]

@[simp] lemma pairStore_embF (m o t th : List Γ) (B : Stack (pairK M₁ M₂) → List Γ)
    (j : M₁.K) : pairStore M₁ M₂ m o t th B (embF M₁ M₂ (some j))
      = B (embF M₁ M₂ (some j)) := by
  simp [pairStore, scratch, embF, stackInl, stackInr]

@[simp] lemma pairStore_embG (m o t th : List Γ) (B : Stack (pairK M₁ M₂) → List Γ)
    (j : M₂.K) : pairStore M₁ M₂ m o t th B (embG M₁ M₂ (some j))
      = B (embG M₁ M₂ (some j)) := by
  simp [pairStore, scratch, embG, stackInr]

end Pair

/-! ## The pairing machine -/

section PairMachine

variable {Γ : Type} [Fintype Γ] (M₁ M₂ : Machine Γ) (s₀ s₁ : Γ)

/-- **The pairing machine**: eight phases, chained by `seqProg`, over a memory holding three
scratch stacks of its own and a private block for each component machine.

`dup` copies the input onto two scratch stacks; `xfer` restores one copy to the I/O stack;
`M₁` runs in its own block, leaving its output on the I/O stack while the second copy of the
input sits untouched on a scratch stack it cannot reach; `xfer` parks that output; `xfer`
restores the input; `M₂` runs; `pushOne` writes the separator; `emitTagged` writes the tagged
block of `M₁`'s output on top. -/
def pairMachine : Machine Γ where
  K := pairK M₁ M₂
  Λ := Option (Γ × Bool) ⊕ (Option (Γ × Bool) ⊕ (M₁.Λ ⊕ (Option (Γ × Bool) ⊕
        (Option (Γ × Bool) ⊕ (M₂.Λ ⊕ (Bool ⊕ Option (Γ × Bool)))))))
  init := Sum.inl none
  step :=
    seqProg (dup none (scratch M₁ M₂ 0) (scratch M₁ M₂ 1)) (Sum.inl none)
      (seqProg (xfer (scratch M₁ M₂ 0) none) (Sum.inl M₁.init)
        (seqProg (M₁.step.relabel (embF M₁ M₂)) (Sum.inl none)
          (seqProg (xfer none (scratch M₁ M₂ 2)) (Sum.inl none)
            (seqProg (xfer (scratch M₁ M₂ 1) none) (Sum.inl M₂.init)
              (seqProg (M₂.step.relabel (embG M₁ M₂)) (Sum.inl true)
                (seqProg (pushOne none s₀) none
                  (emitTagged (scratch M₁ M₂ 2) none s₁)))))))

variable {M₁ M₂ s₀ s₁}

/-- **The pairing machine computes the pair, in time linear in the inputs plus the two
component running times.** The `6 * u.length` term is the cost of moving `M₁`'s output out of
the way and then emitting it tagged. -/
lemma pairMachine_runsInTime {x u v : List Γ} {t₁ t₂ : ℕ} (hf : RunsInTime M₁ x u t₁)
    (hg : RunsInTime M₂ x v t₂) :
    RunsInTime (pairMachine M₁ M₂ s₀ s₁) x (pairWord s₀ s₁ u v)
      (9 * x.length + 6 * u.length + t₁ + t₂ + 8) := by
  obtain ⟨U₁, hU₁, hrun₁⟩ := hf
  obtain ⟨U₂, hU₂, hrun₂⟩ := hg
  have hs0 : scratch M₁ M₂ 0 ≠ (none : Stack (pairK M₁ M₂)) := by simp
  have hs1 : scratch M₁ M₂ 1 ≠ (none : Stack (pairK M₁ M₂)) := by simp
  have hs2 : scratch M₁ M₂ 2 ≠ (none : Stack (pairK M₁ M₂)) := by simp
  have hs01 : scratch M₁ M₂ 0 ≠ scratch M₁ M₂ 1 := by simp [scratch]
  set Z : Stack (pairK M₁ M₂) → List Γ := fun _ => [] with hZ
  -- Phase A: duplicate the input onto the two scratch stacks.
  have hA : HaltsFrom (dup none (scratch M₁ M₂ 0) (scratch M₁ M₂ 1)) none
      (layout x) (pairStore M₁ M₂ [] x.reverse x.reverse [] Z) (3 * x.length) := by
    refine dup_run_val _ _ _ hs0 hs1 hs01 x _ _ rfl (by simp) (by simp [layout])
      (by simp [layout]) ?_
    refine pairStack_cases M₁ M₂ ?_ ?_ ?_ ?_ ?_ ?_
    · intro h; exact absurd rfl h
    · intro _ h _; exact absurd rfl h
    · intro _ _ h; exact absurd rfl h
    · intro _ _ _; simp [layout]
    · intro k _ _ _; simp only [pairStore_embF, hZ]; rfl
    · intro k _ _ _; simp only [pairStore_embG, hZ]; rfl
  -- Phase B: restore one copy to the I/O stack.
  have hB : HaltsFrom (xfer (scratch M₁ M₂ 0) none)
      none (pairStore M₁ M₂ [] x.reverse x.reverse [] Z)
      (pairStore M₁ M₂ x [] x.reverse [] Z) (3 * x.reverse.length) := by
    refine xfer_run_val _ _ (Ne.symm hs0) x.reverse _ _ (by simp) (by simp) (by simp) ?_
    refine pairStack_cases M₁ M₂ ?_ ?_ ?_ ?_ ?_ ?_
    · intro _ h; exact absurd rfl h
    · intro h; exact absurd rfl h
    · intro _ _; simp
    · intro _ _; simp
    · intro k _ _; simp
    · intro k _ _; simp
  -- Phase C: run the first machine in its own block.
  have halignF : ∀ k : Stack M₁.K,
      (pairStore M₁ M₂ x [] x.reverse [] Z) (embF M₁ M₂ k) = layout x k := by
    rintro (_ | k)
    · show pairStore M₁ M₂ x [] x.reverse [] Z none = x
      simp
    · simp only [pairStore_embF, hZ]; rfl
  obtain ⟨T₃, hC, hCmem, hCframe⟩ := hrun₁.relabel (embF_injective M₁ M₂) halignF
  have hT₃io : T₃ none = u := (hCmem none).trans hU₁
  have hT₃s0 : T₃ (scratch M₁ M₂ 0) = [] := by
    rw [hCframe _ (fun k => embF_ne_scratch M₁ M₂ k 0)]; simp
  have hT₃s1 : T₃ (scratch M₁ M₂ 1) = x.reverse := by
    rw [hCframe _ (fun k => embF_ne_scratch M₁ M₂ k 1)]; simp
  have hT₃s2 : T₃ (scratch M₁ M₂ 2) = [] := by
    rw [hCframe _ (fun k => embF_ne_scratch M₁ M₂ k 2)]; simp
  have hT₃G : ∀ j : M₂.K, T₃ (embG M₁ M₂ (some j)) = [] := by
    intro j
    rw [hCframe _ (fun k => embF_ne_embG_priv M₁ M₂ k j)]; simp [hZ]
  -- Phase D: park the first output on a scratch stack.
  have hD : HaltsFrom (xfer none (scratch M₁ M₂ 2)) none T₃
      (pairStore M₁ M₂ [] [] x.reverse u.reverse T₃) (3 * u.length) := by
    refine xfer_run_val _ _ hs2 u _ _ hT₃io (by simp) (by simp [hT₃s2]) ?_
    refine pairStack_cases M₁ M₂ ?_ ?_ ?_ ?_ ?_ ?_
    · intro h; exact absurd rfl h
    · intro _ _; simp [hT₃s0]
    · intro _ _; simp [hT₃s1]
    · intro _ h; exact absurd rfl h
    · intro k _ _; simp
    · intro k _ _; simp
  -- Phase E: restore the second copy of the input.
  have hE : HaltsFrom (xfer (scratch M₁ M₂ 1) none) none
      (pairStore M₁ M₂ [] [] x.reverse u.reverse T₃)
      (pairStore M₁ M₂ x [] [] u.reverse T₃) (3 * x.reverse.length) := by
    refine xfer_run_val _ _ (Ne.symm hs1) x.reverse _ _ (by simp) (by simp) (by simp) ?_
    refine pairStack_cases M₁ M₂ ?_ ?_ ?_ ?_ ?_ ?_
    · intro _ h; exact absurd rfl h
    · intro _ _; simp
    · intro h; exact absurd rfl h
    · intro _ _; simp
    · intro k _ _; simp
    · intro k _ _; simp
  -- Phase F: run the second machine in its own block.
  have halignG : ∀ k : Stack M₂.K,
      (pairStore M₁ M₂ x [] [] u.reverse T₃) (embG M₁ M₂ k) = layout x k := by
    rintro (_ | k)
    · show pairStore M₁ M₂ x [] [] u.reverse T₃ none = x
      simp
    · simp only [pairStore_embG]; rw [hT₃G k]; rfl
  obtain ⟨T₆, hF, hFmem, hFframe⟩ := hrun₂.relabel (embG_injective M₁ M₂) halignG
  have hT₆io : T₆ none = v := (hFmem none).trans hU₂
  have hT₆s2 : T₆ (scratch M₁ M₂ 2) = u.reverse := by
    rw [hFframe _ (fun k => embG_ne_scratch M₁ M₂ k 2)]; simp
  -- Phase G: the separator.
  have hG := pushOne_run (none : Stack (pairK M₁ M₂)) s₀ T₆
  have hT₇io : (Function.update T₆ none (s₀ :: T₆ none)) none = s₀ :: v := by
    rw [Function.update_self, hT₆io]
  have hT₇s2 : (Function.update T₆ none (s₀ :: T₆ none)) (scratch M₁ M₂ 2) = u.reverse := by
    rw [Function.update_of_ne hs2, hT₆s2]
  -- Phase H: emit the tagged block of the first output.
  have hH := emitTagged_run (scratch M₁ M₂ 2) (none : Stack (pairK M₁ M₂)) s₁ (Ne.symm hs2)
    u.reverse (Function.update T₆ none (s₀ :: T₆ none)) hT₇s2
  refine ⟨_, ?_, ((hA.seq (hB.seq (hC.seq (hD.seq (hE.seq (hF.seq (hG.seq hH))))))).mono ?_)⟩
  · rw [Function.update_self, List.reverse_reverse, hT₆io]
    rfl
  · simp only [List.length_reverse]
    omega

end PairMachine

/-! ## Closure under pairing -/

section Closure

variable {Γ : Type} [Fintype Γ]

/-- The clock normal form absorbs the pairing overhead: linear movement costs, the two
component clocks, and the length of the first output (itself bounded by the first clock). -/
lemma exists_clock_pair (a₁ k₁ a₂ k₂ : ℕ) :
    ∃ a k : ℕ, ∀ n m : ℕ, m ≤ n + (a₁ * (n + 1) ^ k₁ + a₁) →
      9 * n + 6 * m + (a₁ * (n + 1) ^ k₁ + a₁) + (a₂ * (n + 1) ^ k₂ + a₂) + 8
        ≤ a * (n + 1) ^ k + a := by
  refine ⟨23 + 7 * (2 * a₁ + 1) + (2 * a₂ + 1), max (max k₁ k₂) 1, fun n m hm => ?_⟩
  have hNpos : 0 < n + 1 := Nat.succ_pos n
  have hmono : ∀ i j : ℕ, i ≤ j → (n + 1) ^ i ≤ (n + 1) ^ j :=
    fun _ _ h => Nat.pow_le_pow_right hNpos h
  have hA1 : 1 ≤ (n + 1) ^ (max (max k₁ k₂) 1) := Nat.one_le_pow _ _ hNpos
  have hn : n ≤ (n + 1) ^ (max (max k₁ k₂) 1) := by
    have h := hmono 1 (max (max k₁ k₂) 1) (le_max_right _ _)
    simp only [pow_one] at h; omega
  have h1 : a₁ * (n + 1) ^ k₁ + a₁ ≤ (2 * a₁ + 1) * (n + 1) ^ (max (max k₁ k₂) 1) :=
    (clock_le a₁ (Nat.one_le_pow _ _ hNpos)).trans
      (Nat.mul_le_mul (le_refl _)
        (hmono _ _ ((le_max_left k₁ k₂).trans (le_max_left _ 1))))
  have h2 : a₂ * (n + 1) ^ k₂ + a₂ ≤ (2 * a₂ + 1) * (n + 1) ^ (max (max k₁ k₂) 1) :=
    (clock_le a₂ (Nat.one_le_pow _ _ hNpos)).trans
      (Nat.mul_le_mul (le_refl _)
        (hmono _ _ ((le_max_right k₁ k₂).trans (le_max_left _ 1))))
  have key : (23 + 7 * (2 * a₁ + 1) + (2 * a₂ + 1)) * (n + 1) ^ (max (max k₁ k₂) 1)
      = 23 * (n + 1) ^ (max (max k₁ k₂) 1)
        + 7 * ((2 * a₁ + 1) * (n + 1) ^ (max (max k₁ k₂) 1))
        + (2 * a₂ + 1) * (n + 1) ^ (max (max k₁ k₂) 1) := by ring
  calc 9 * n + 6 * m + (a₁ * (n + 1) ^ k₁ + a₁) + (a₂ * (n + 1) ^ k₂ + a₂) + 8
      ≤ 23 * (n + 1) ^ (max (max k₁ k₂) 1)
          + 7 * ((2 * a₁ + 1) * (n + 1) ^ (max (max k₁ k₂) 1))
          + (2 * a₂ + 1) * (n + 1) ^ (max (max k₁ k₂) 1) := by omega
    _ = (23 + 7 * (2 * a₁ + 1) + (2 * a₂ + 1)) * (n + 1) ^ (max (max k₁ k₂) 1) := key.symm
    _ ≤ (23 + 7 * (2 * a₁ + 1) + (2 * a₂ + 1)) * (n + 1) ^ (max (max k₁ k₂) 1)
          + (23 + 7 * (2 * a₁ + 1) + (2 * a₂ + 1)) := Nat.le_add_right _ _

/-- **The polynomial-time machine class is closed under pairing.**

Together with `MachinePolyEC.comp` this is the pair of closure results Stage 1 set out to
prove. Unlike composition, this one genuinely needs the memory architecture: the machine
keeps a copy of its input on a scratch stack across `f`'s run, and it is `HaltsFrom.relabel`
— the frame half of the embedding — that says `f` cannot disturb it.

**The tags are deliberately unconstrained here.** `s₀ ≠ s₁` is *not* a hypothesis: the
machine emits `pairWord s₀ s₁ (f x) (g x)` within the clock whatever the two symbols are, and
adding the hypothesis would weaken the statement for no gain. It is the *reading* of the
output as a pair that needs distinct tags — with `s₀ = s₁` the encoding is not
self-delimiting and the block boundary is lost. That is exactly the content of
`pairWord_injective`, which does take `s₀ ≠ s₁`, and it is where a caller who needs to
decode should get the separation from. So: this lemma says the class is closed under
`fun x => pairWord s₀ s₁ (f x) (g x)`; it does not by itself say the class is closed under
pairing *as an encoding of pairs*. -/
lemma MachinePolyEC.pair {s₀ s₁ : Γ} {f g : List Γ → List Γ}
    (hf : MachinePolyEC f) (hg : MachinePolyEC g) :
    MachinePolyEC (fun x => pairWord s₀ s₁ (f x) (g x)) := by
  obtain ⟨M₁, a₁, k₁, h₁⟩ := hf
  obtain ⟨M₂, a₂, k₂, h₂⟩ := hg
  obtain ⟨a, k, hclock⟩ := exists_clock_pair a₁ k₁ a₂ k₂
  refine ⟨pairMachine M₁ M₂ s₀ s₁, a, k, fun x => ?_⟩
  have hx := h₁ x
  exact (pairMachine_runsInTime hx (h₂ x)).mono
    (hclock x.length (f x).length hx.length_output_le)

end Closure

/-! ## Non-vacuity witnesses, and the closure lemmas exercised

`MachinePolyEC.id` (`Basic.lean`) and `MachinePolyEC.const_nil` below are constructed
inhabitants of the class: the two closure lemmas are therefore not conditionals about an
empty class, and the examples below run each of them on a pair of real witnesses. The
erasing machine lives here rather than beside the identity because it is built from `xfer`,
which this file introduces. -/

section Witnesses

variable (Γ : Type) [Fintype Γ]

/-- **The erasing machine**: one private stack, and a control that pumps the whole I/O stack
onto it and halts. It computes `fun _ => []` in `3 * n` steps — the input is not destroyed
but parked, which is all the halting convention asks (private stacks may be left dirty). -/
def eraseMachine : Machine Γ where
  K := Unit
  Λ := Option (Γ × Bool)
  init := none
  step := xfer none (some ())

variable {Γ}

/-- The erasing machine empties the I/O stack in three steps per input symbol.  Kind `N+`: a
constructed inhabitant of `RunsInTime` over a machine with a nonempty private block and a
nontrivial control. -/
lemma eraseMachine_runsInTime (x : List Γ) : RunsInTime (eraseMachine Γ) x [] (3 * x.length) := by
  refine ⟨fun j => match j with | none => [] | some _ => x.reverse, rfl, ?_⟩
  refine xfer_run_val none (some ()) (by simp) x _ _ rfl rfl (by simp [layout]) ?_
  rintro (_ | j) h1 h2 <;> simp_all

/-- **`MachinePolyEC` contains a function that moves data**: `fun _ => []`, computed by
`eraseMachine` inside the clock `3 * (n + 1) + 3`.  Kind `N+`. Together with
`MachinePolyEC.id` this gives the closure lemmas below two distinct witnesses to chew on. -/
lemma MachinePolyEC.const_nil : MachinePolyEC (fun _ : List Γ => ([] : List Γ)) :=
  ⟨eraseMachine Γ, 3, 1, fun x => (eraseMachine_runsInTime x).mono (by rw [pow_one]; omega)⟩

-- The composition closure, exercised: erasing after the identity is in the class.
example : MachinePolyEC ((fun _ : List Γ => ([] : List Γ)) ∘ (fun x : List Γ => x)) :=
  MachinePolyEC.comp MachinePolyEC.id MachinePolyEC.const_nil

-- The pairing closure, exercised: the input paired with the empty word is in the class.
example (s₀ s₁ : Γ) : MachinePolyEC (fun x : List Γ => pairWord s₀ s₁ x []) :=
  MachinePolyEC.pair MachinePolyEC.id MachinePolyEC.const_nil

end Witnesses

end LogicalInduction.Counted
