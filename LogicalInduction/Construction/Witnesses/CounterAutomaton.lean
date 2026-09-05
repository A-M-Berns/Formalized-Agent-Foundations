import LogicalInduction.Construction.Witnesses.RunAutomaton
import Complexitylib.Classes.P

/-!
# A finite control with one unbounded counter, in polynomial time

`RunAuto.BlockAutomaton` fixes the number of states, and that is exactly what an `aⁿbⁿ`
constraint defeats: a structured arithmetic leaf's unary length field must equal its
payload's own token count, and no finite-state device decides that.  `RunAuto.BlockMachine`
is the relaxation that can — an arbitrary *word* state growing by at most a constant per
token — but an interface with no inhabitant decides nothing.

This file is the inhabitant: a **one-counter machine**.  `CtrProgram` is the value-level
datum — a finite control below `Q`, a bounded token alphabet, and, on every transition, a
counter action (`keep` / `inc` / `dec`) chosen from the control state, the clamped token,
and a zero test on the counter.  `ctrMachine` packages it as a `RunAuto.BlockMachine`, and
`ifCtr_mem_FP` is the consumer-facing decision, the counter analogue of
`RunAuto.BlockAutomaton.ifAuto_mem_FP`.

The encoding is what makes the word step a *fixed-depth* nest rather than a scan.  A state
`(i, n)` is the word `ctrlWord p i ++ 1ⁿ`, where `ctrlWord p i = 1ⁱ 0^(Q+1-i)` always
occupies exactly `Q + 1` bits.  The control is therefore a constant-width prefix, testable
against a *fixed word* by `TokenFold.eqConstFn_mem_FP`, and the counter is the suffix, whose
zero test is a single `TokenFold.ifEqLen_mem_FP` at `Q + 1` and whose three actions are
`append`, `take`-off-the-tail, and identity.  Both nests — `Q + 1` control states, `A + 1`
letters — are finite because both bounds are constants of the program.

Two things are deliberate rather than incidental.  First, the decode is **total**: an
arbitrary state word that matches no control block decodes to the junk control state
`Q + 1`, which is a perfectly good state for `p.ctrl` to be asked about (`ctrl_le` clamps
its successor back below `Q`).  `BlockMachine.step` is applied to arbitrary words inside
`BlockMachine.run`, so a partial decode would have left `ctrMachine_accepts` unprovable;
the encode/decode round trip is instead the invariant of that induction.  Second, the
per-token growth constant is `Q + 2` — the control block is rewritten wholesale each step,
and the counter grows by at most one — which is what buys admission to
`TokenFold.runFold_cli_mem_FP`.

Everything here is supporting infrastructure rather than a paper claim, so the declarations
are `lemma`s and `def`s.
-/

namespace LogicalInduction.CtrAuto

open Complexity Complexity.Cobham LogicalInduction.FPFold LogicalInduction.TokenFold
open LogicalInduction.RunAuto

/-! ## The value-level program -/

/-- What a transition does to the counter. -/
inductive CAct
  /-- Leave the counter alone. -/
  | keep
  /-- Increment it. -/
  | inc
  /-- Decrement it, truncated at zero. -/
  | dec
  deriving DecidableEq, Repr

/-- The counter action, on a number. -/
def CAct.apply : CAct → ℕ → ℕ
  | .keep, n => n
  | .inc, n => n + 1
  | .dec, n => n - 1

/-- The counter action, on the unary word the counter is carried as. -/
def CAct.applyW : CAct → List Bool → List Bool
  | .keep, u => u
  | .inc, u => u ++ [true]
  | .dec, u => u.take u.tail.length

lemma CAct.applyW_replicate (a : CAct) (n : ℕ) :
    a.applyW (List.replicate n true) = List.replicate (a.apply n) true := by
  cases a
  · rfl
  · simp [CAct.applyW, CAct.apply, ← List.replicate_succ']
  · cases n with
    | zero => rfl
    | succ k =>
        simp only [CAct.applyW, CAct.apply, List.tail_replicate, List.length_replicate,
          List.take_replicate]
        congr 1
        omega

lemma CAct.length_applyW_le (a : CAct) (u : List Bool) :
    (a.applyW u).length ≤ u.length + 1 := by
  cases a
  · simp [CAct.applyW]
  · simp [CAct.applyW]
  · simp only [CAct.applyW, List.length_take]
    omega

/-- **A finite control paired with one unbounded unary counter.**

`ctrl` and `act` see the control state, the token *clamped* to `min t (A + 1)` — so that a
finite nest suffices — and a zero test on the counter.  Acceptance demands both an accepting
control state and an empty counter, which is what makes the device decide `aⁿbⁿ`. -/
structure CtrProgram where
  /-- Control-state bound; `Q + 1` is available as the junk state an unparseable word
  decodes to. -/
  Q : ℕ
  /-- Alphabet bound: tokens are clamped to `min t (A + 1)` before dispatch. -/
  A : ℕ
  /-- Control transition: state, clamped token, and whether the counter is zero. -/
  ctrl : ℕ → ℕ → Bool → ℕ
  /-- Counter action, on the same three arguments. -/
  act : ℕ → ℕ → Bool → CAct
  /-- Accepting control states (the counter must ALSO be zero to accept). -/
  accept : ℕ → Bool
  /-- The initial control state. -/
  init : ℕ
  /-- It is a control state. -/
  init_le : init ≤ Q
  /-- Successors are control states — including from the junk state. -/
  ctrl_le : ∀ i t z, ctrl i t z ≤ Q

namespace CtrProgram

variable (p : CtrProgram)

/-- One step on a control/counter pair. -/
def step : ℕ × ℕ → ℕ → ℕ × ℕ :=
  fun s t => (p.ctrl s.1 (min t (p.A + 1)) (decide (s.2 = 0)),
              (p.act s.1 (min t (p.A + 1)) (decide (s.2 = 0))).apply s.2)

/-- The state after reading a token list from `(init, 0)`. -/
def run (b : List ℕ) : ℕ × ℕ := b.foldl p.step (p.init, 0)

/-- Acceptance: an accepting control state *and* an empty counter. -/
def Accepts (b : List ℕ) : Bool := p.accept (p.run b).1 && decide ((p.run b).2 = 0)

lemma foldl_step_fst_le : ∀ (b : List ℕ) (s : ℕ × ℕ), s.1 ≤ p.Q →
    (List.foldl p.step s b).1 ≤ p.Q
  | [], s, hs => hs
  | t :: b, s, hs => by
      rw [List.foldl_cons]
      exact foldl_step_fst_le b _ (p.ctrl_le _ _ _)

lemma run_fst_le (b : List ℕ) : (p.run b).1 ≤ p.Q :=
  foldl_step_fst_le p b _ p.init_le

end CtrProgram

/-! ## The encoding

A state `(i, n)` is `1ⁱ 0^(Q+1-i)` followed by `1ⁿ`.  The control block has constant width
`Q + 1`, so the control is a fixed-word test on `w.take (Q+1)` and the counter is `w.drop
(Q+1)`; both are `Complexity.FP` primitives. -/

/-- The constant word denoting control state `i`. -/
def ctrlWord (p : CtrProgram) (i : ℕ) : List Bool :=
  List.replicate i true ++ List.replicate (p.Q + 1 - i) false

lemma length_ctrlWord {p : CtrProgram} {i : ℕ} (hi : i ≤ p.Q + 1) :
    (ctrlWord p i).length = p.Q + 1 := by
  simp only [ctrlWord, List.length_append, List.length_replicate]
  omega

private lemma takeWhile_id_replicate_append (i k : ℕ) :
    (List.replicate i true ++ List.replicate (k + 1) false).takeWhile id
      = List.replicate i true := by
  induction i with
  | zero => simp [List.replicate_succ]
  | succ n ih =>
      rw [List.replicate_succ, List.cons_append]
      simp [ih]

/-- The control block's leading run of `true`s recovers the state — the round trip that
makes `ctrlWord` injective below the bound. -/
lemma length_takeWhile_ctrlWord {p : CtrProgram} {i : ℕ} (hi : i ≤ p.Q) :
    ((ctrlWord p i).takeWhile id).length = i := by
  have hk : p.Q + 1 - i = (p.Q - i) + 1 := by omega
  rw [ctrlWord, hk, takeWhile_id_replicate_append, List.length_replicate]

lemma ctrlWord_injOn {p : CtrProgram} {i j : ℕ} (hi : i ≤ p.Q) (hj : j ≤ p.Q)
    (h : ctrlWord p i = ctrlWord p j) : i = j := by
  have h1 := length_takeWhile_ctrlWord hi
  rw [h, length_takeWhile_ctrlWord hj] at h1
  exact h1.symm

/-- The state word for a control/counter pair. -/
def encode (p : CtrProgram) (s : ℕ × ℕ) : List Bool :=
  ctrlWord p s.1 ++ List.replicate s.2 true

lemma take_encode {p : CtrProgram} {s : ℕ × ℕ} (hs : s.1 ≤ p.Q) :
    (encode p s).take (p.Q + 1) = ctrlWord p s.1 := by
  rw [encode, ← length_ctrlWord (p := p) (i := s.1) (by omega)]
  exact List.take_left ..

lemma drop_encode {p : CtrProgram} {s : ℕ × ℕ} (hs : s.1 ≤ p.Q) :
    (encode p s).drop (p.Q + 1) = List.replicate s.2 true := by
  rw [encode, ← length_ctrlWord (p := p) (i := s.1) (by omega)]
  exact List.drop_left ..

lemma length_encode {p : CtrProgram} {s : ℕ × ℕ} (hs : s.1 ≤ p.Q) :
    (encode p s).length = p.Q + 1 + s.2 := by
  rw [encode, List.length_append, List.length_replicate, length_ctrlWord (by omega)]

/-! ## The word-level step -/

/-- The control state a word denotes: the first listed state whose word is the word's
constant-width prefix, and the junk state `Q + 1` if none is. -/
def ctrlSel (p : CtrProgram) : List ℕ → List Bool → ℕ
  | [], _ => p.Q + 1
  | i :: is, w => if w.take (p.Q + 1) = ctrlWord p i then i else ctrlSel p is w

lemma ctrlSel_le (p : CtrProgram) : ∀ (l : List ℕ) (w : List Bool),
    (∀ j ∈ l, j ≤ p.Q) → ctrlSel p l w ≤ p.Q + 1
  | [], w, _ => by rw [ctrlSel]
  | (i :: l), w, hl => by
      rw [ctrlSel]
      split_ifs with h
      · exact le_trans (hl i (List.mem_cons_self ..)) (by omega)
      · exact ctrlSel_le p l w (fun j hj => hl j (List.mem_cons_of_mem _ hj))

lemma ctrlSel_eq (p : CtrProgram) {w : List Bool} {i : ℕ} (hi : i ≤ p.Q)
    (hw : w.take (p.Q + 1) = ctrlWord p i) : ∀ (l : List ℕ), i ∈ l → (∀ j ∈ l, j ≤ p.Q) →
      ctrlSel p l w = i
  | [], hm, _ => absurd hm (by simp)
  | (j :: l), hm, hl => by
      rw [ctrlSel]
      by_cases h : w.take (p.Q + 1) = ctrlWord p j
      · rw [if_pos h]
        exact (ctrlWord_injOn hi (hl j (List.mem_cons_self ..)) (hw ▸ h)).symm
      · rw [if_neg h]
        refine ctrlSel_eq p hi hw l ?_ (fun q hq => hl q (List.mem_cons_of_mem _ hq))
        rcases List.mem_cons.mp hm with hc | hc
        · exact absurd (hc ▸ hw) h
        · exact hc

/-- The transition, at a *known* control state and *clamped* token: rewrite the control
block and act on the counter suffix. -/
def leafW (p : CtrProgram) (i t : ℕ) (w : List Bool) : List Bool :=
  ctrlWord p (p.ctrl i t (decide (w.length = p.Q + 1)))
    ++ (p.act i t (decide (w.length = p.Q + 1))).applyW (w.drop (p.Q + 1))

lemma length_leafW_le (p : CtrProgram) (i t : ℕ) (w : List Bool) :
    (leafW p i t w).length ≤ w.length + p.Q + 2 := by
  have hc := length_ctrlWord (p := p) (i := p.ctrl i t (decide (w.length = p.Q + 1)))
    (by have := p.ctrl_le i t (decide (w.length = p.Q + 1)); omega)
  have ha := CAct.length_applyW_le (p.act i t (decide (w.length = p.Q + 1)))
    (w.drop (p.Q + 1))
  have hd : (w.drop (p.Q + 1)).length ≤ w.length := by simp
  rw [leafW, List.length_append, hc]
  omega

/-- The mathematical word step: decode the control, clamp the token, act. -/
def wstep (p : CtrProgram) (w : List Bool) (t : ℕ) : List Bool :=
  leafW p (ctrlSel p (List.range (p.Q + 1)) w) (min t (p.A + 1)) w

/-- **The encoding is preserved by the word step.** -/
lemma wstep_encode (p : CtrProgram) (s : ℕ × ℕ) (hs : s.1 ≤ p.Q) (t : ℕ) :
    wstep p (encode p s) t = encode p (p.step s t) := by
  have hsel : ctrlSel p (List.range (p.Q + 1)) (encode p s) = s.1 :=
    ctrlSel_eq p hs (take_encode hs) _ (by simp only [List.mem_range]; omega)
      (by intro j hj; simp only [List.mem_range] at hj; omega)
  have hz : decide ((encode p s).length = p.Q + 1) = decide (s.2 = 0) := by
    rw [length_encode hs]
    by_cases h : s.2 = 0
    · simp [h]
    · simp only [h, decide_false, decide_eq_false_iff_not]
      omega
  rw [wstep, leafW, hsel, hz, drop_encode hs, CAct.applyW_replicate]
  rfl

/-! ## The `Complexity.FP` presentation -/

private def cliBlk (v : List Bool) : List Bool := fstBlock (sndBlock v)
private def tokBlk (v : List Bool) : List Bool := sndBlock (sndBlock v)

private lemma cliBlk_pair (W cli tok : List Bool) : cliBlk (pair W (pair cli tok)) = cli := by
  rw [cliBlk, sndBlock_pair, fstBlock_pair]

private lemma tokBlk_pair (W cli tok : List Bool) : tokBlk (pair W (pair cli tok)) = tok := by
  rw [tokBlk, sndBlock_pair, sndBlock_pair]

private lemma cliBlk_mem_FP : cliBlk ∈ FP := mem_FP_comp sndBlock_mem_FP fstBlock_mem_FP

private lemma tokBlk_mem_FP : tokBlk ∈ FP := mem_FP_comp sndBlock_mem_FP sndBlock_mem_FP

private lemma applyW_mem_FP (a : CAct) {D : List Bool → List Bool} (hD : D ∈ FP) :
    (fun z => a.applyW (D z)) ∈ FP := by
  cases a
  · simpa [CAct.applyW] using hD
  · simpa [CAct.applyW] using appendFn_mem_FP hD (constFn_mem_FP [true])
  · simpa [CAct.applyW] using takeLenFn_mem_FP (tail_mem_FP hD) hD

private lemma dropCli_mem_FP {p : CtrProgram} : (fun v => (cliBlk v).drop (p.Q + 1)) ∈ FP := by
  have h := dropLenFn_mem_FP (constFn_mem_FP (List.replicate (p.Q + 1) true)) cliBlk_mem_FP
  simpa using h

private lemma takeCli_mem_FP {p : CtrProgram} : (fun v => (cliBlk v).take (p.Q + 1)) ∈ FP := by
  have h := takeLenFn_mem_FP (constFn_mem_FP (List.replicate (p.Q + 1) true)) cliBlk_mem_FP
  simpa using h

lemma leafW_mem_FP (p : CtrProgram) (i t : ℕ) : (fun v => leafW p i t (cliBlk v)) ∈ FP := by
  have hD := dropCli_mem_FP (p := p)
  have hbr : ∀ z : Bool, (fun v => ctrlWord p (p.ctrl i t z)
      ++ (p.act i t z).applyW ((cliBlk v).drop (p.Q + 1))) ∈ FP := fun z =>
    appendFn_mem_FP (constFn_mem_FP _) (applyW_mem_FP _ hD)
  have h := ifEqLen_mem_FP cliBlk_mem_FP (p.Q + 1) (hbr true) (hbr false)
  have heq : (fun v => if (cliBlk v).length = p.Q + 1 then
        ctrlWord p (p.ctrl i t true) ++ (p.act i t true).applyW ((cliBlk v).drop (p.Q + 1))
      else
        ctrlWord p (p.ctrl i t false)
          ++ (p.act i t false).applyW ((cliBlk v).drop (p.Q + 1)))
      = fun v => leafW p i t (cliBlk v) := by
    funext v
    rw [leafW]
    by_cases hv : (cliBlk v).length = p.Q + 1
    · rw [if_pos hv, decide_eq_true hv]
    · rw [if_neg hv, decide_eq_false hv]
  rwa [heq] at h

/-- The inner nest: dispatch on the token's value against each literal below the alphabet
bound, falling through to the merged class `A + 1`. -/
def tokNestC (p : CtrProgram) (i : ℕ) : List ℕ → List Bool → List Bool
  | [], v => leafW p i (p.A + 1) (cliBlk v)
  | t :: ts, v => if NumEqBits t (tokBlk v) then leafW p i t (cliBlk v)
                  else tokNestC p i ts v

lemma tokNestC_eq (p : CtrProgram) (i : ℕ) (W cli : List Bool) (cur : List ℕ)
    (hcur : ∀ d ∈ cur, d < 4) : ∀ (l : List ℕ), (∀ t ∈ l, t ≤ p.A) →
      tokNestC p i l (pair W (pair cli (digitsToBits cur)))
        = leafW p i (if digitVal cur ∈ l then digitVal cur else p.A + 1) cli
  | [], _ => by rw [tokNestC, cliBlk_pair]; simp
  | (t :: l), hl => by
      have hle : ∀ t' ∈ l, t' ≤ p.A := fun t' ht' => hl t' (List.mem_cons_of_mem _ ht')
      rw [tokNestC, tokBlk_pair, cliBlk_pair]
      by_cases h : NumEqBits t (digitsToBits cur)
      · have hv : digitVal cur = t := (numEqBits_spec t cur hcur).mp h
        rw [if_pos h, if_pos (by rw [hv]; exact List.mem_cons_self ..), hv]
      · have hv : digitVal cur ≠ t := fun hc => h ((numEqBits_spec t cur hcur).mpr hc)
        rw [if_neg h, tokNestC_eq p i W cli cur hcur l hle]
        by_cases hm : digitVal cur ∈ l
        · rw [if_pos hm, if_pos (List.mem_cons_of_mem _ hm)]
        · rw [if_neg hm, if_neg (by
            intro hc
            rcases List.mem_cons.mp hc with hc | hc
            · exact hv hc
            · exact hm hc)]

lemma length_tokNestC_le (p : CtrProgram) (i : ℕ) : ∀ (l : List ℕ) (v : List Bool),
    (tokNestC p i l v).length ≤ (cliBlk v).length + p.Q + 2
  | [], v => by rw [tokNestC]; exact length_leafW_le p i _ _
  | (t :: l), v => by
      rw [tokNestC]
      split_ifs
      · exact length_leafW_le p i _ _
      · exact length_tokNestC_le p i l v

lemma tokNestC_mem_FP (p : CtrProgram) (i : ℕ) : ∀ l : List ℕ,
    (fun v => tokNestC p i l v) ∈ FP
  | [] => by
      have heq : (fun v => tokNestC p i [] v) = fun v => leafW p i (p.A + 1) (cliBlk v) := by
        funext v; rw [tokNestC]
      rw [heq]; exact leafW_mem_FP p i _
  | (t :: l) => by
      have hrec := tokNestC_mem_FP p i l
      have h := ifNumEq_mem_FP tokBlk_mem_FP t (leafW_mem_FP p i t) hrec
      have heq : (fun v => if NumEqBits t (tokBlk v) then leafW p i t (cliBlk v)
            else tokNestC p i l v) = fun v => tokNestC p i (t :: l) v := by
        funext v; rw [tokNestC]
      rwa [heq] at h

/-- The outer nest: dispatch on the control block, falling through to the junk state. -/
def stNestC (p : CtrProgram) : List ℕ → List Bool → List Bool
  | [], v => tokNestC p (p.Q + 1) (List.range (p.A + 1)) v
  | i :: is, v =>
      if (cliBlk v).take (p.Q + 1) = ctrlWord p i then
        tokNestC p i (List.range (p.A + 1)) v
      else stNestC p is v

/-- **The outer nest computes exactly the decode `ctrlSel` describes.**  The two recursions
branch on the same condition, so the agreement is structural. -/
lemma stNestC_eq (p : CtrProgram) : ∀ (l : List ℕ) (v : List Bool),
    stNestC p l v = tokNestC p (ctrlSel p l (cliBlk v)) (List.range (p.A + 1)) v
  | [], v => by rw [stNestC, ctrlSel]
  | (i :: l), v => by
      rw [stNestC, ctrlSel]
      by_cases h : (cliBlk v).take (p.Q + 1) = ctrlWord p i
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h, stNestC_eq p l v]

lemma length_stNestC_le (p : CtrProgram) : ∀ (l : List ℕ) (v : List Bool),
    (stNestC p l v).length ≤ (cliBlk v).length + p.Q + 2
  | [], v => by rw [stNestC]; exact length_tokNestC_le p _ _ v
  | (i :: l), v => by
      rw [stNestC]
      split_ifs
      · exact length_tokNestC_le p i _ v
      · exact length_stNestC_le p l v

lemma stNestC_mem_FP (p : CtrProgram) : ∀ l : List ℕ, (fun v => stNestC p l v) ∈ FP
  | [] => by
      have heq : (fun v => stNestC p [] v)
          = fun v => tokNestC p (p.Q + 1) (List.range (p.A + 1)) v := by
        funext v; rw [stNestC]
      rw [heq]; exact tokNestC_mem_FP p _ _
  | (i :: l) => by
      have hrec := stNestC_mem_FP p l
      have h := eqConstFn_mem_FP (ctrlWord p i) (takeCli_mem_FP (p := p))
        (tokNestC_mem_FP p i (List.range (p.A + 1))) hrec
      have heq : (fun v => if (cliBlk v).take (p.Q + 1) = ctrlWord p i then
            tokNestC p i (List.range (p.A + 1)) v else stNestC p l v)
          = fun v => stNestC p (i :: l) v := by funext v; rw [stNestC]
      rwa [heq] at h

/-! ## Acceptance -/

/-- The accepting state words — finite, because the control is. -/
def acceptWords (p : CtrProgram) : List (List Bool) :=
  ((List.range (p.Q + 1)).filter fun i => p.accept i).map (ctrlWord p)

/-- The acceptance nest: a one-bit word on a match, empty otherwise. -/
def accNest : List (List Bool) → List Bool → List Bool
  | [], _ => []
  | c :: cs, w => if w = c then [true] else accNest cs w

lemma accNest_spec : ∀ (l : List (List Bool)) (w : List Bool),
    (accNest l w).length = 1 ↔ w ∈ l
  | [], w => by rw [accNest]; simp
  | (c :: cs), w => by
      rw [accNest]
      by_cases h : w = c
      · rw [if_pos h]
        simp [h]
      · rw [if_neg h, accNest_spec cs w]
        simp [h]

lemma accNest_mem_FP : ∀ (l : List (List Bool)), (fun w => accNest l w) ∈ FP
  | [] => by
      have heq : (fun w => accNest [] w) = fun _ : List Bool => ([] : List Bool) := by
        funext w; rw [accNest]
      rw [heq]; exact constFn_mem_FP _
  | (c :: cs) => by
      have hrec := accNest_mem_FP cs
      have h := eqConstFn_mem_FP c (A := fun w => w) Complexity.id_mem_FP
        (constFn_mem_FP [true]) hrec
      have heq : (fun w => if w = c then ([true] : List Bool) else accNest cs w)
          = fun w => accNest (c :: cs) w := by funext w; rw [accNest]
      rwa [heq] at h

/-- **A state word is accepting exactly when its control accepts and its counter is
empty.** -/
lemma mem_acceptWords {p : CtrProgram} {s : ℕ × ℕ} (hs : s.1 ≤ p.Q) :
    encode p s ∈ acceptWords p ↔ (p.accept s.1 = true ∧ s.2 = 0) := by
  rw [acceptWords, List.mem_map]
  constructor
  · rintro ⟨j, hj, hje⟩
    rw [List.mem_filter, List.mem_range] at hj
    have hjQ : j ≤ p.Q := by omega
    have hlen : (ctrlWord p j).length = (encode p s).length := by rw [hje]
    rw [length_ctrlWord (by omega : j ≤ p.Q + 1), length_encode hs] at hlen
    have hn : s.2 = 0 := by omega
    have : ctrlWord p j = ctrlWord p s.1 := by
      rw [hje, encode, hn, List.replicate_zero, List.append_nil]
    exact ⟨(ctrlWord_injOn hjQ hs this) ▸ hj.2, hn⟩
  · rintro ⟨hacc, hn⟩
    refine ⟨s.1, ?_, ?_⟩
    · rw [List.mem_filter, List.mem_range]
      exact ⟨by omega, hacc⟩
    · rw [encode, hn, List.replicate_zero, List.append_nil]

/-! ## The machine -/

/-- **Every one-counter program is a `RunAuto.BlockMachine`.**

Kind `N+` non-vacuity witness — this is what makes `RunAuto.BlockMachine` inhabited by a
device `RunAuto.BlockAutomaton` cannot express.  Provenance: (a) `stNestC_eq`,
`tokNestC_eq`, `numEqBits_spec`, `accNest_spec`; (b) `TokenFold.eqConstFn_mem_FP`,
`TokenFold.ifEqLen_mem_FP`, `TokenFold.ifNumEq_mem_FP`,
`Complexity.Cobham.appendFn_mem_FP`, `Complexity.Cobham.takeLenFn_mem_FP`. -/
def ctrMachine (p : CtrProgram) : RunAuto.BlockMachine where
  c := p.Q + 2
  init := ctrlWord p p.init
  step := wstep p
  accept := fun w => decide (w ∈ acceptWords p)
  acceptW := accNest (acceptWords p)
  acceptW_FP := accNest_mem_FP _
  acceptW_spec := fun s => by rw [accNest_spec]; simp
  stepW := stNestC p (List.range (p.Q + 1))
  stepW_FP := stNestC_mem_FP p _
  stepW_len := fun W cli tok => by
    have h := length_stNestC_le p (List.range (p.Q + 1)) (pair W (pair cli tok))
    rw [cliBlk_pair] at h
    omega
  stepW_spec := by
    intro W cli cur hcur
    rw [stNestC_eq, cliBlk_pair,
      tokNestC_eq p (ctrlSel p (List.range (p.Q + 1)) cli) W cli cur hcur
        (List.range (p.A + 1))
        (by intro t ht; simp only [List.mem_range] at ht; omega),
      wstep]
    congr 1
    by_cases hv : digitVal cur ≤ p.A
    · rw [if_pos (by simp only [List.mem_range]; omega)]
      omega
    · rw [if_neg (by simp only [List.mem_range]; omega)]
      omega

@[simp] lemma ctrMachine_init (p : CtrProgram) :
    (ctrMachine p).init = ctrlWord p p.init := rfl

@[simp] lemma ctrMachine_step (p : CtrProgram) : (ctrMachine p).step = wstep p := rfl

/-- **The machine's state is the program's state, encoded.**

The round trip is the induction's invariant, which is why the decode had to be total. -/
lemma foldl_wstep_encode (p : CtrProgram) : ∀ (b : List ℕ) (s : ℕ × ℕ), s.1 ≤ p.Q →
    List.foldl (wstep p) (encode p s) b = encode p (List.foldl p.step s b)
  | [], s, _ => rfl
  | t :: b, s, hs => by
      rw [List.foldl_cons, List.foldl_cons, wstep_encode p s hs t]
      exact foldl_wstep_encode p b (p.step s t) (p.ctrl_le _ _ _)

lemma ctrMachine_run (p : CtrProgram) (b : List ℕ) :
    (ctrMachine p).run b = encode p (p.run b) := by
  have h := foldl_wstep_encode p b (p.init, 0) p.init_le
  have hinit : encode p (p.init, 0) = ctrlWord p p.init := by
    rw [encode, List.replicate_zero, List.append_nil]
  rw [RunAuto.BlockMachine.run, ctrMachine_step, ctrMachine_init, ← hinit, h, CtrProgram.run]

/-- **The machine accepts exactly the program's language.**

Proof kind: `P` proved.  Provenance: (a) `ctrMachine_run`, `mem_acceptWords`.
Paper node: `app:ifp` -/
lemma ctrMachine_accepts (p : CtrProgram) (b : List ℕ) :
    (ctrMachine p).Accepts b = true ↔ p.Accepts b = true := by
  rw [RunAuto.BlockMachine.Accepts, ctrMachine_run]
  show decide (encode p (p.run b) ∈ acceptWords p) = true ↔ _
  rw [decide_eq_true_iff, mem_acceptWords (p.run_fst_le b), CtrProgram.Accepts]
  simp

/-- **Branching on "this one-counter program accepts this word's token stream" is
polynomial time.**

The counter analogue of `RunAuto.BlockAutomaton.ifAuto_mem_FP`, and the shape a recognizer
of an `aⁿbⁿ`-constrained language runs on.

Proof kind: `C` composition.  Provenance: (a) `ctrMachine_accepts`;
(b) `RunAuto.BlockMachine.ifRun_mem_FP`.
Paper node: `app:ifp` -/
lemma ifCtr_mem_FP (p : CtrProgram) {S X Y : List Bool → List Bool}
    (hS : S ∈ Complexity.FP) (hX : X ∈ Complexity.FP) (hY : Y ∈ Complexity.FP) :
    (fun z => if p.Accepts (decodeBits (S z)) = true then X z else Y z) ∈ Complexity.FP := by
  have h := (ctrMachine p).ifRun_mem_FP hS hX hY
  have heq : (fun z => if (ctrMachine p).Accepts (decodeBits (S z)) = true then X z else Y z)
      = fun z => if p.Accepts (decodeBits (S z)) = true then X z else Y z := by
    funext z
    by_cases hc : p.Accepts (decodeBits (S z)) = true
    · rw [if_pos ((ctrMachine_accepts p _).mpr hc), if_pos hc]
    · rw [if_neg (fun hd => hc ((ctrMachine_accepts p _).mp hd)), if_neg hc]
  rwa [heq] at h

end LogicalInduction.CtrAuto
