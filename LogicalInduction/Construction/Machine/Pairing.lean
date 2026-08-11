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

end LogicalInduction.Counted
