/-
# The clocked simulator for a fixed description

Stage 3's soundness half. `Construction/MachineTraderEnumeration.lean` enumerates traders
by a finite `TMDesc` together with a polynomial clock, and reads off the described
machine's output when it halts inside that clock and `[]` when it does not. That truncated
behaviour has to be an ordinary polynomial-time function, or the enumeration is not an
enumeration *of* machine-efficient traders.

This file builds the machine that computes it. The description is *fixed* — an index names
one — so no interpreter is needed: the simulator's control states are the described
machine's own states, and one of its transitions performs one transition of the described
machine while advancing a unary clock head by one cell. Four work tapes: `0` mirrors the
described machine's single work tape, `1` holds the clock, `2` and `3` are the scratch the
clock's construction needs.

Three phases:

* `pre` — one transition moving the shared heads back to cell `0`, so the simulation starts
  at the described machine's own initial configuration. Every combinator delivers its tapes
  with the heads parked at cell `1`, and the described machine's first transition is the one
  that reads `▷`; this is where that offset is paid back.
* the simulation — one transition per described step, guarded by the clock cell under the
  head. Reaching the described halt state wins over an exhausted clock.
* `rewind` / `wipe` — the timeout branch, which walks the output head back to the left end
  and blanks cell `1`, so the output word is empty.

The construction is generic in the description and the clock, and is a candidate for
upstreaming; it is kept here for the same reason as `runChildFixed` and
`forRegs_hoareTime`, to leave the pinned fork untouched.
-/
import LogicalInduction.Construction.Machine.DescExec
import Complexitylib.Models.TuringMachine.Registers
import Complexitylib.Models.TuringMachine.Registers.Emit
import Complexitylib.Models.TuringMachine.Registers.Horner
import Complexitylib.Models.TuringMachine.Registers.InputLen
import Complexitylib.Classes.P.NormalForm

namespace LogicalInduction.MachineExec

open Complexity Complexity.TM

/-! ## The clocked simulator for a fixed description -/

/-- The simulator's states: the simulated machine's own state while it runs, plus four
    phase markers — `pre` (rewind the shared heads to cell 0, so the simulation starts at
    the interpreted machine's own initial configuration), `rewind` and `wipe` (the timeout
    branch, which blanks output cell 1), and `done`. -/
abbrev SimQ (Q : Type) := Q ⊕ Fin 4

variable (d : TMDesc)

/-- The simulator's transition function. Work tape `0` mirrors the interpreted machine's
    single work tape, work tape `1` holds the unary clock (one mark per remaining step,
    head advancing right), and work tapes `2` and `3` are the clock-preparation scratch. -/
def simδ :
    SimQ (d.toTM).Q → Γ → (Fin 4 → Γ) → Γ →
      SimQ (d.toTM).Q × (Fin 4 → Γw) × Γw × Dir3 × (Fin 4 → Dir3) × Dir3 :=
  fun s iHead wHeads oHead =>
  match s with
  | Sum.inl q =>
      if wHeads 1 ≠ Γ.one then
        (Sum.inr 1, fun i => readBackWrite (wHeads i), readBackWrite oHead,
          idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
      else if q = (d.toTM).qhalt then
        (Sum.inr 3, fun i => readBackWrite (wHeads i), readBackWrite oHead,
          idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
      else
        let r := (d.toTM).δ q iHead (fun _ => wHeads 0) oHead
        (Sum.inl r.1,
          fun i => if i = 0 then r.2.1 0 else readBackWrite (wHeads i),
          r.2.2.1,
          r.2.2.2.1,
          fun i => if i = 0 then r.2.2.2.2.1 0 else
            if i = 1 then Dir3.right else idleDir (wHeads i),
          r.2.2.2.2.2)
  | Sum.inr t =>
      if t.val = 0 then
        (Sum.inl (d.toTM).qstart, fun i => readBackWrite (wHeads i), readBackWrite oHead,
          moveLeftDir iHead,
          fun i => if i = 0 then moveLeftDir (wHeads i) else idleDir (wHeads i),
          moveLeftDir oHead)
      else if t.val = 1 then
        if oHead = Γ.start then
          (Sum.inr 2, fun i => readBackWrite (wHeads i), readBackWrite oHead,
            idleDir iHead, fun i => idleDir (wHeads i), Dir3.right)
        else
          (Sum.inr 1, fun i => readBackWrite (wHeads i), readBackWrite oHead,
            idleDir iHead, fun i => idleDir (wHeads i), Dir3.left)
      else if t.val = 2 then
        (Sum.inr 3, fun i => readBackWrite (wHeads i), Γw.blank,
          idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
      else
        (Sum.inr 3, fun i => readBackWrite (wHeads i), readBackWrite oHead,
          idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)

/-- **The clocked simulator.** Rewinds to the interpreted machine's initial configuration,
    then runs it one step per clock mark; halting first wins, exhausting the clock blanks
    output cell 1. -/
def simTM : TM 4 where
  Q := SimQ (d.toTM).Q
  qstart := Sum.inr 0
  qhalt := Sum.inr 3
  δ := simδ d
  δ_right_of_start := by
    intro s iHead wHeads oHead
    match s with
    | Sum.inl q =>
        obtain ⟨h1, h2, h3⟩ :=
          (d.toTM).δ_right_of_start q iHead (fun _ => wHeads 0) oHead
        simp only [simδ]
        split_ifs with hc hq
        · refine ⟨?_, ?_, ?_⟩ <;> intros <;> simp_all [idleDir]
        · refine ⟨?_, ?_, ?_⟩ <;> intros <;> simp_all [idleDir]
        · refine ⟨h1, fun i h => ?_, h3⟩
          by_cases hi : i = 0
          · subst hi
            show ((d.toTM).δ q iHead (fun _ => wHeads 0) oHead).2.2.2.2.1 0 = Dir3.right
            exact h2 0 h
          · by_cases hi1 : i = 1
            · subst hi1; simp
            · simp only [if_neg hi, if_neg hi1]
              simp [idleDir, h]
    | Sum.inr t =>
        simp only [simδ]
        split_ifs with h0 h1 ho h2
        · refine ⟨fun h => by simp [moveLeftDir, h], fun i h => ?_,
            fun h => by simp [moveLeftDir, h]⟩
          by_cases hi : i = 0
          · subst hi; simp [moveLeftDir, h]
          · simp only [if_neg hi]; simp [idleDir, h]
        · exact ⟨fun h => by simp [idleDir, h], fun i h => by simp [idleDir, h],
            fun _ => rfl⟩
        · exact ⟨fun h => by simp [idleDir, h], fun i h => by simp [idleDir, h],
            fun h => absurd h ho⟩
        · exact ⟨fun h => by simp [idleDir, h], fun i h => by simp [idleDir, h],
            fun h => by simp [idleDir, h]⟩
        · exact ⟨fun h => by simp [idleDir, h], fun i h => by simp [idleDir, h],
            fun h => by simp [idleDir, h]⟩


/-! ### The simulator's tape layout -/

/-- The simulator's four work tapes. -/
def simWork (w0 clk s2 s3 : Tape) : Fin 4 → Tape :=
  fun i => if i = 0 then w0 else if i = 1 then clk else if i = 2 then s2 else s3

@[simp] lemma simWork_zero (w0 clk s2 s3 : Tape) : simWork w0 clk s2 s3 0 = w0 := rfl
@[simp] lemma simWork_one (w0 clk s2 s3 : Tape) : simWork w0 clk s2 s3 1 = clk := rfl
@[simp] lemma simWork_two (w0 clk s2 s3 : Tape) : simWork w0 clk s2 s3 2 = s2 := rfl
@[simp] lemma simWork_three (w0 clk s2 s3 : Tape) : simWork w0 clk s2 s3 3 = s3 := rfl

lemma simWork_eq (W : Fin 4 → Tape) : simWork (W 0) (W 1) (W 2) (W 3) = W := by
  funext i
  fin_cases i <;> rfl

/-- A `Fin 1`-indexed tape family is its own value at `0`. -/
lemma work_fin_one (w : Fin 1 → Tape) : (fun _ : Fin 1 => w 0) = w := by
  funext i
  rw [Subsingleton.elim i 0]

/-- Writing back the symbol under the head is a no-op away from the left-end marker. -/
lemma writeBack_move (t : Tape) (h : t.read ≠ Γ.start) (dir : Dir3) :
    t.writeAndMove (readBackWrite t.read).toΓ dir = t.move dir := by
  unfold Tape.writeAndMove
  rw [toΓ_readBackWrite_of_ne_start h]
  simp only [Tape.write, Tape.read]
  split
  · rfl
  · simp [Function.update_eq_self]

/-! ### One simulated step -/

lemma simTM_step_run (d : TMDesc) (c c' : Cfg 1 (d.toTM).Q)
    (hstep : (d.toTM).step c = some c') (clk s2 s3 : Tape) (hclk : clk.read = Γ.one)
    (hs2 : s2.read ≠ Γ.start) (hs3 : s3.read ≠ Γ.start) :
    (simTM d).step
        ⟨Sum.inl c.state, c.input, simWork (c.work 0) clk s2 s3, c.output⟩
      = some ⟨Sum.inl c'.state, c'.input,
          simWork (c'.work 0) (clk.move Dir3.right) s2 s3, c'.output⟩ := by
  have hq : c.state ≠ (d.toTM).qhalt := by
    intro h
    rw [TM.step, if_pos h] at hstep
    exact absurd hstep (by simp)
  rw [TM.step, if_neg hq, Option.some.injEq] at hstep
  subst hstep
  rw [TM.step]
  simp only [simTM]
  rw [if_neg (by simp : (Sum.inl c.state : SimQ (d.toTM).Q) ≠ Sum.inr 3)]
  simp only [simδ]
  rw [if_neg (by simp [hclk]), if_neg hq]
  have hw : (fun _ : Fin 1 => (c.work 0).read) = (fun i => (c.work i).read) := by
    funext i
    rw [Subsingleton.elim i 0]
  simp only [simWork_zero, hw, Option.some.injEq, Cfg.mk.injEq, true_and, and_true]
  funext i
  fin_cases i
  · simp [simWork]
  · simp only [simWork_one, if_neg (by decide : ¬((1 : Fin 4) = 0)),
      if_pos (rfl : (1 : Fin 4) = 1)]
    exact writeBack_move clk (by rw [hclk]; simp) Dir3.right
  · show s2.writeAndMove (readBackWrite s2.read).toΓ (idleDir s2.read) = s2
    rw [writeBack_move s2 hs2, idleDir, if_neg hs2]
    rfl
  · show s3.writeAndMove (readBackWrite s3.read).toΓ (idleDir s3.read) = s3
    rw [writeBack_move s3 hs3, idleDir, if_neg hs3]
    rfl


/-! ### The phase transitions -/

private lemma simTM_ne_halt_inl (d : TMDesc) (q : (d.toTM).Q) :
    (Sum.inl q : SimQ (d.toTM).Q) ≠ Sum.inr 3 := by simp

lemma simTM_step_pre (d : TMDesc) (inp w0 clk s2 s3 out : Tape)
    (hi : inp.read ≠ Γ.start) (hw0 : w0.read ≠ Γ.start) (hout : out.read ≠ Γ.start)
    (hclk : clk.read ≠ Γ.start) (hs2 : s2.read ≠ Γ.start) (hs3 : s3.read ≠ Γ.start) :
    (simTM d).step ⟨Sum.inr 0, inp, simWork w0 clk s2 s3, out⟩
      = some ⟨Sum.inl (d.toTM).qstart, inp.move Dir3.left,
          simWork (w0.move Dir3.left) clk s2 s3, out.move Dir3.left⟩ := by
  rw [TM.step]
  simp only [simTM]
  rw [if_neg (by simp : (Sum.inr 0 : SimQ (d.toTM).Q) ≠ Sum.inr 3)]
  simp only [simδ, Fin.val_zero, reduceIte, Option.some.injEq, Cfg.mk.injEq, true_and,
    and_true]
  refine ⟨by rw [moveLeftDir, if_neg hi], ?_, by
    rw [writeBack_move out hout, moveLeftDir, if_neg hout]⟩
  funext i
  fin_cases i
  · show w0.writeAndMove (readBackWrite w0.read).toΓ (moveLeftDir w0.read) = _
    rw [writeBack_move w0 hw0, moveLeftDir, if_neg hw0]; rfl
  · show clk.writeAndMove (readBackWrite clk.read).toΓ (idleDir clk.read) = clk
    rw [writeBack_move clk hclk, idleDir, if_neg hclk]; rfl
  · show s2.writeAndMove (readBackWrite s2.read).toΓ (idleDir s2.read) = s2
    rw [writeBack_move s2 hs2, idleDir, if_neg hs2]; rfl
  · show s3.writeAndMove (readBackWrite s3.read).toΓ (idleDir s3.read) = s3
    rw [writeBack_move s3 hs3, idleDir, if_neg hs3]; rfl

/-- The shared shape of every phase transition: the work tapes are written back and
    idled, the input tape is idled, and only the output tape and the state move. -/
private lemma simTM_step_phase (d : TMDesc) (s s' : SimQ (d.toTM).Q)
    (hs : s ≠ Sum.inr 3) (inp w0 clk s2 s3 out : Tape) (ow : Γw) (odir : Dir3)
    (hclk : clk.read ≠ Γ.start) (hs2 : s2.read ≠ Γ.start) (hs3 : s3.read ≠ Γ.start)
    (hδ : simδ d s inp.read (fun i => (simWork w0 clk s2 s3 i).read) out.read
      = (s', fun i => readBackWrite ((simWork w0 clk s2 s3 i).read), ow,
          idleDir inp.read,
          fun i => idleDir ((simWork w0 clk s2 s3 i).read), odir)) :
    (simTM d).step ⟨s, inp, simWork w0 clk s2 s3, out⟩
      = some ⟨s', transitionInput inp, simWork (transitionTape w0) clk s2 s3,
          out.writeAndMove ow.toΓ odir⟩ := by
  rw [TM.step]
  simp only [simTM]
  rw [if_neg hs, hδ]
  simp only [Option.some.injEq, Cfg.mk.injEq, true_and, and_true]
  refine ⟨rfl, ?_⟩
  funext i
  fin_cases i
  · rfl
  · show clk.writeAndMove (readBackWrite clk.read).toΓ (idleDir clk.read) = clk
    rw [writeBack_move clk hclk, idleDir, if_neg hclk]; rfl
  · show s2.writeAndMove (readBackWrite s2.read).toΓ (idleDir s2.read) = s2
    rw [writeBack_move s2 hs2, idleDir, if_neg hs2]; rfl
  · show s3.writeAndMove (readBackWrite s3.read).toΓ (idleDir s3.read) = s3
    rw [writeBack_move s3 hs3, idleDir, if_neg hs3]; rfl

/-- The idle transition shared by the halt and timeout branches. -/
private lemma simTM_step_idle (d : TMDesc) (s s' : SimQ (d.toTM).Q)
    (hs : s ≠ Sum.inr 3)
    (inp w0 clk s2 s3 out : Tape)
    (hclk : clk.read ≠ Γ.start) (hs2 : s2.read ≠ Γ.start) (hs3 : s3.read ≠ Γ.start)
    (hδ : simδ d s inp.read (fun i => (simWork w0 clk s2 s3 i).read) out.read
      = (s', fun i => readBackWrite ((simWork w0 clk s2 s3 i).read),
          readBackWrite out.read, idleDir inp.read,
          fun i => idleDir ((simWork w0 clk s2 s3 i).read), idleDir out.read)) :
    (simTM d).step ⟨s, inp, simWork w0 clk s2 s3, out⟩
      = some ⟨s', transitionInput inp, simWork (transitionTape w0) clk s2 s3,
          transitionTape out⟩ :=
  simTM_step_phase d s s' hs inp w0 clk s2 s3 out _ _ hclk hs2 hs3 hδ

lemma simTM_step_halt (d : TMDesc) (inp w0 clk s2 s3 out : Tape)
    (hone : clk.read = Γ.one)
    (hclk : clk.read ≠ Γ.start) (hs2 : s2.read ≠ Γ.start) (hs3 : s3.read ≠ Γ.start) :
    (simTM d).step ⟨Sum.inl (d.toTM).qhalt, inp, simWork w0 clk s2 s3, out⟩
      = some ⟨Sum.inr 3, transitionInput inp, simWork (transitionTape w0) clk s2 s3,
          transitionTape out⟩ :=
  simTM_step_idle d _ _ (simTM_ne_halt_inl d _) inp w0 clk s2 s3 out hclk
    hs2 hs3 (by simp only [simδ]
                rw [if_neg (by simp [hone] : ¬((simWork w0 clk s2 s3 1).read ≠ Γ.one)),
                  if_true])

lemma simTM_step_timeout (d : TMDesc) (q : (d.toTM).Q)
    (inp w0 clk s2 s3 out : Tape) (hclock : clk.read ≠ Γ.one)
    (hclk : clk.read ≠ Γ.start) (hs2 : s2.read ≠ Γ.start) (hs3 : s3.read ≠ Γ.start) :
    (simTM d).step ⟨Sum.inl q, inp, simWork w0 clk s2 s3, out⟩
      = some ⟨Sum.inr 1, transitionInput inp, simWork (transitionTape w0) clk s2 s3,
          transitionTape out⟩ :=
  simTM_step_idle d _ _ (simTM_ne_halt_inl d _) inp w0 clk s2 s3 out hclk
    hs2 hs3 (by simp only [simδ, simWork_one]; rw [if_pos hclock])


/-! ### The clock tape -/

/-- The clock tape after `j` simulated steps: `V` marks, head at cell `1 + j`. -/
def clkTape (V j : ℕ) : Tape := ⟨1 + j, regCells V⟩

@[simp] lemma clkTape_zero (V : ℕ) : clkTape V 0 = regTape V := rfl

lemma clkTape_read (V j : ℕ) :
    (clkTape V j).read = if 1 + j ≤ V then Γ.one else Γ.blank := by
  simp only [clkTape, Tape.read, regCells, if_neg (by omega : ¬(1 + j = 0))]

lemma clkTape_read_ne_start (V j : ℕ) : (clkTape V j).read ≠ Γ.start := by
  rw [clkTape_read]; split_ifs <;> simp

lemma clkTape_move (V j : ℕ) : (clkTape V j).move Dir3.right = clkTape V (j + 1) := rfl

/-! ### The simulation phase -/

lemma simTM_reachesIn_run (d : TMDesc) (V : ℕ) (s2 s3 : Tape)
    (hs2 : s2.read ≠ Γ.start) (hs3 : s3.read ≠ Γ.start) :
    ∀ (t j : ℕ) (c₀ c : Cfg 1 (d.toTM).Q), (d.toTM).reachesIn t c₀ c → j + t ≤ V →
      (simTM d).reachesIn t
        ⟨Sum.inl c₀.state, c₀.input, simWork (c₀.work 0) (clkTape V j) s2 s3, c₀.output⟩
        ⟨Sum.inl c.state, c.input, simWork (c.work 0) (clkTape V (j + t)) s2 s3,
          c.output⟩ := by
  intro t
  induction t with
  | zero =>
      intro j c₀ c hreach _
      cases hreach
      simpa using TM.reachesIn.zero
  | succ t ih =>
      intro j c₀ c hreach hle
      cases hreach with
      | step hstep hrest =>
          rename_i c''
          have hone : (clkTape V j).read = Γ.one := by
            rw [clkTape_read, if_pos (by omega)]
          refine TM.reachesIn.step
            (simTM_step_run d c₀ c'' hstep (clkTape V j) s2 s3 hone hs2 hs3) ?_
          rw [clkTape_move]
          have := ih (j + 1) c'' c hrest (by omega)
          have he : j + 1 + t = j + (t + 1) := by omega
          rwa [he] at this

/-! ### The timeout phase -/

lemma simTM_step_rewind (d : TMDesc) (inp w0 clk s2 s3 out : Tape)
    (hout : out.read ≠ Γ.start)
    (hclk : clk.read ≠ Γ.start) (hs2 : s2.read ≠ Γ.start) (hs3 : s3.read ≠ Γ.start) :
    (simTM d).step ⟨Sum.inr 1, inp, simWork w0 clk s2 s3, out⟩
      = some ⟨Sum.inr 1, transitionInput inp, simWork (transitionTape w0) clk s2 s3,
          out.move Dir3.left⟩ := by
  rw [simTM_step_phase d (Sum.inr 1) (Sum.inr 1) (by simp) inp w0 clk s2 s3 out
    (readBackWrite out.read) Dir3.left hclk hs2 hs3
    (by simp only [simδ]
        rw [if_neg (by decide : ¬(((1 : Fin 4) : ℕ) = 0)),
          if_pos (by decide : ((1 : Fin 4) : ℕ) = 1), if_neg hout]),
    writeBack_move out hout]

lemma simTM_step_rewound (d : TMDesc) (inp w0 clk s2 s3 out : Tape)
    (hout : out.read = Γ.start) (hhead : out.head = 0)
    (hclk : clk.read ≠ Γ.start) (hs2 : s2.read ≠ Γ.start) (hs3 : s3.read ≠ Γ.start) :
    (simTM d).step ⟨Sum.inr 1, inp, simWork w0 clk s2 s3, out⟩
      = some ⟨Sum.inr 2, transitionInput inp, simWork (transitionTape w0) clk s2 s3,
          out.move Dir3.right⟩ := by
  rw [simTM_step_phase d (Sum.inr 1) (Sum.inr 2) (by simp) inp w0 clk s2 s3 out
    (readBackWrite out.read) Dir3.right hclk hs2 hs3
    (by simp only [simδ]
        rw [if_neg (by decide : ¬(((1 : Fin 4) : ℕ) = 0)),
          if_pos (by decide : ((1 : Fin 4) : ℕ) = 1), if_pos hout])]
  simp only [Tape.writeAndMove, Tape.write, hhead, if_true]

lemma simTM_step_wipe (d : TMDesc) (inp w0 clk s2 s3 out : Tape)
    (hout : out.read ≠ Γ.start)
    (hclk : clk.read ≠ Γ.start) (hs2 : s2.read ≠ Γ.start) (hs3 : s3.read ≠ Γ.start) :
    (simTM d).step ⟨Sum.inr 2, inp, simWork w0 clk s2 s3, out⟩
      = some ⟨Sum.inr 3, transitionInput inp, simWork (transitionTape w0) clk s2 s3,
          out.write Γ.blank⟩ := by
  rw [simTM_step_phase d (Sum.inr 2) (Sum.inr 3) (by simp) inp w0 clk s2 s3 out
    Γw.blank (idleDir out.read) hclk hs2 hs3
    (by simp only [simδ]
        rw [if_neg (by decide : ¬(((2 : Fin 4) : ℕ) = 0)),
          if_neg (by decide : ¬(((2 : Fin 4) : ℕ) = 1)),
          if_pos (by decide : ((2 : Fin 4) : ℕ) = 2)])]
  simp only [Tape.writeAndMove, idleDir, if_neg hout]
  rfl

/-- Rewinding the output head to the left end. The input and simulated work tapes are
    idled by each transition, so they arrive iterated by `transitionInput`/`transitionTape`;
    only their cells matter afterwards, and those are preserved. -/
lemma simTM_rewind (d : TMDesc) (clk s2 s3 : Tape)
    (hclk : clk.read ≠ Γ.start) (hs2 : s2.read ≠ Γ.start) (hs3 : s3.read ≠ Γ.start)
    (cells : ℕ → Γ) (hns : ∀ j, 1 ≤ j → cells j ≠ Γ.start) :
    ∀ (h : ℕ) (inp w0 : Tape), (simTM d).reachesIn h
      ⟨Sum.inr 1, inp, simWork w0 clk s2 s3, ⟨h, cells⟩⟩
      ⟨Sum.inr 1, transitionInput^[h] inp, simWork (transitionTape^[h] w0) clk s2 s3,
        ⟨0, cells⟩⟩
  | 0, inp, w0 => TM.reachesIn.zero
  | h + 1, inp, w0 => by
      refine TM.reachesIn.step
        (simTM_step_rewind d inp w0 clk s2 s3 ⟨h + 1, cells⟩ ?_ hclk hs2 hs3) ?_
      · exact hns (h + 1) (by omega)
      · have hrec := simTM_rewind d clk s2 s3 hclk hs2 hs3 cells hns h
          (transitionInput inp) (transitionTape w0)
        show (simTM d).reachesIn h
          ⟨Sum.inr 1, transitionInput inp, simWork (transitionTape w0) clk s2 s3,
            ⟨h, cells⟩⟩ _
        simpa [Function.iterate_succ_apply] using hrec

/-! ### Two invariants of a run's output tape -/

lemma reachesIn_output_startInvariant {n : ℕ} {tm : TM n} :
    ∀ {t : ℕ} {c c' : Cfg n tm.Q}, tm.reachesIn t c c' →
      c.output.StartInvariant → c'.output.StartInvariant := by
  intro t
  induction t with
  | zero => intro c c' h hwf; cases h; exact hwf
  | succ t ih =>
      intro c c' h hwf
      cases h with
      | step hstep hrest =>
          refine ih hrest ?_
          rw [TM.step] at hstep
          split at hstep
          · exact absurd hstep (by simp)
          · simp only [Option.some.injEq] at hstep
            subst hstep
            exact hwf.writeAndMove _ _

lemma reachesIn_output_head_le {n : ℕ} {tm : TM n} :
    ∀ {t : ℕ} {c c' : Cfg n tm.Q}, tm.reachesIn t c c' →
      c'.output.head ≤ c.output.head + t := by
  intro t
  induction t with
  | zero => intro c c' h; cases h; omega
  | succ t ih =>
      intro c c' h
      cases h with
      | step hstep hrest =>
          rename_i c''
          have hle := ih hrest
          have hstep' : c''.output.head ≤ c.output.head + 1 := by
            rw [TM.step] at hstep
            split at hstep
            · exact absurd hstep (by simp)
            · simp only [Option.some.injEq] at hstep
              subst hstep
              show ((c.output.write _).move _).head ≤ c.output.head + 1
              have h1 := Tape.head_move_le (c.output.write
                ((tm.δ c.state c.input.read (fun i => (c.work i).read) c.output.read).2.2.1).toΓ)
                ((tm.δ c.state c.input.read (fun i => (c.work i).read) c.output.read).2.2.2.2.2)
              rw [Tape.write_head] at h1
              exact h1
          omega

/-! ### The word the simulator leaves -/

/-- The output word of the clocked run: the described machine's output when it halts
    inside the clock, and the empty word when it does not. -/
def clockedOutput (d : TMDesc) (V : ℕ) (x : List Bool) : List Bool :=
  match evalHalted d V x with
  | none => []
  | some c => codedOutput c

lemma regCells_zero : regCells 0 = (Tape.init ([] : List Γ)).cells := by
  funext j
  simp only [regCells, Tape.init]
  split_ifs with h1 h2
  · rfl
  · omega
  · simp


/-! ### The simulator's Hoare specification -/

set_option maxHeartbeats 1000000 in
lemma simTM_hoareTime (d : TMDesc) (x : List Bool) (V : ℕ) (s2 s3 : Tape)
    (hs2 : s2.read ≠ Γ.start) (hs3 : s3.read ≠ Γ.start) :
    (simTM d).HoareTime
      (EmitPred ⟨1, (Tape.init (x.map Γ.ofBool)).cells⟩
        (simWork (regTape 0) (regTape V) s2 s3) [])
      (fun _ _ out => out.HasOutput (clockedOutput d V x))
      (2 * V + 6) := by
  rintro inp work out ⟨rfl, rfl, hout⟩
  have hi : (⟨1, (Tape.init (x.map Γ.ofBool)).cells⟩ : Tape).read ≠ Γ.start :=
    (parked_init_input x).2 1 le_rfl
  have hw0 : (regTape 0).read ≠ Γ.start := (parked_regTape 0).2 1 le_rfl
  have hclkV : (regTape V).read ≠ Γ.start := (parked_regTape V).2 1 le_rfl
  -- the entry output tape is the blank tape with the head bumped
  have houteq : out = ⟨1, (Tape.init ([] : List Γ)).cells⟩ := by
    refine Tape.ext (by simpa using hout.1) (funext fun j => ?_)
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [hout.2.1]; rfl
    · rw [hout.2.2.2 j (by simp only [List.length_nil]; omega)]
      show Γ.blank = _
      simp only [Tape.init, if_neg (by omega : ¬ j = 0)]
      simp
  subst houteq
  have hout0 : (⟨1, (Tape.init ([] : List Γ)).cells⟩ : Tape).read ≠ Γ.start := by
    show (Tape.init ([] : List Γ)).cells 1 ≠ Γ.start
    simp [Tape.init]
  -- the `pre` transition lands on the described machine's initial configuration
  have hstart : ((d.toTM).initCfg x).output.StartInvariant := by
    refine ⟨rfl, fun j hj => ?_⟩
    show (Tape.init ([] : List Γ)).cells j ≠ Γ.start
    simp only [Tape.init, if_neg (by omega : ¬ j = 0)]
    simp
  have hwork0 : (regTape 0).move Dir3.left = ((d.toTM).initCfg x).work 0 :=
    Tape.ext rfl regCells_zero
  have hpre := simTM_step_pre d ⟨1, (Tape.init (x.map Γ.ofBool)).cells⟩ (regTape 0)
    (regTape V) s2 s3 ⟨1, (Tape.init ([] : List Γ)).cells⟩ hi hw0 hout0 hclkV hs2 hs3
  rw [hwork0] at hpre
  cases hev : evalHalted d V x with
  | some c =>
      -- the described machine halts inside the clock
      have hspec := runUntilHalt_spec d V (initCoded d x) c hev
      rw [decode_initCoded] at hspec
      obtain ⟨s, hsV, hreach, hhalt⟩ := hspec
      have hHas : (CodedCfg.decode d c).output.HasOutput (codedOutput c) :=
        CodedTape.hasOutput_outputWord (evalHalted_output_invariants hev).1
      have hrun := simTM_reachesIn_run d V s2 s3 hs2 hs3 s 0 ((d.toTM).initCfg x)
        (CodedCfg.decode d c) hreach (by omega)
      have hone : (clkTape V (0 + s)).read = Γ.one := by
        rw [clkTape_read, if_pos (by omega)]
      have hfin := simTM_step_halt d ((CodedCfg.decode d c).input)
        ((CodedCfg.decode d c).work 0) (clkTape V (0 + s)) s2 s3
        ((CodedCfg.decode d c).output) hone (clkTape_read_ne_start V (0 + s)) hs2 hs3
      rw [show (CodedCfg.decode d c).state = (d.toTM).qhalt from hhalt] at hrun
      have hchain := TM.reachesIn.step hpre
        (TM.reachesIn_trans _ hrun (TM.reachesIn.step hfin TM.reachesIn.zero))
      refine ⟨_, _, ?_, hchain, rfl, ?_⟩
      · omega
      · show (transitionTape (CodedCfg.decode d c).output).HasOutput (clockedOutput d V x)
        rw [clockedOutput, hev]
        refine (Tape.hasOutput_congr ?_ _).mpr hHas
        exact transitionTape_cells _
          (reachesIn_output_startInvariant hreach hstart).2
  | none =>
      -- the clock runs out first
      have hno : ∀ (j : ℕ) (cj : Cfg 1 (d.toTM).Q), j < V →
          (d.toTM).reachesIn j ((d.toTM).initCfg x) cj → ¬ (d.toTM).halted cj := by
        intro j cj hj hreach hhalt
        obtain ⟨c', hrun, -⟩ := runUntilHalt_complete d j (initCoded d x) cj
          (by rw [decode_initCoded]; exact hreach) hhalt V hj
        rw [evalHalted, hrun] at hev
        exact absurd hev (by simp)
      have hex : ∀ j, j ≤ V → ∃ cj, (d.toTM).reachesIn j ((d.toTM).initCfg x) cj := by
        intro j
        induction j with
        | zero => exact fun _ => ⟨_, TM.reachesIn.zero⟩
        | succ k ih =>
            intro hk
            obtain ⟨ck, hck⟩ := ih (by omega)
            have hnh := hno k ck (by omega) hck
            obtain ⟨ck1, hstep⟩ : ∃ c', (d.toTM).step ck = some c' := by
              rw [TM.step, if_neg hnh]; exact ⟨_, rfl⟩
            exact ⟨ck1, TM.reachesIn_snoc hck hstep⟩
      obtain ⟨cV, hcV⟩ := hex V le_rfl
      have hrun := simTM_reachesIn_run d V s2 s3 hs2 hs3 V 0 ((d.toTM).initCfg x) cV hcV
        (by omega)
      have hblank : (clkTape V (0 + V)).read ≠ Γ.one := by
        rw [clkTape_read, if_neg (by omega)]
        simp
      have htime := simTM_step_timeout d cV.state cV.input (cV.work 0)
        (clkTape V (0 + V)) s2 s3 cV.output hblank
        (clkTape_read_ne_start V (0 + V)) hs2 hs3
      -- the output tape entering the rewind
      set outT := transitionTape cV.output with houtT
      have hSI : cV.output.StartInvariant := reachesIn_output_startInvariant hcV hstart
      have hcells : outT.cells = cV.output.cells := transitionTape_cells _ hSI.2
      have hns : ∀ j, 1 ≤ j → outT.cells j ≠ Γ.start := by
        intro j hj; rw [hcells]; exact hSI.2 j hj
      have hhead : outT.head ≤ V + 1 := by
        have h1 := reachesIn_output_head_le hcV
        have h2 : outT.head ≤ cV.output.head + 1 := by
          rw [houtT, transitionTape, Tape.writeAndMove]
          have hm := Tape.head_move_le
            (cV.output.write (readBackWrite cV.output.read).toΓ)
            (idleDir cV.output.read)
          rwa [Tape.write_head] at hm
        simp only [Cfg.init, Tape.init_head] at h1
        omega
      have hrew := simTM_rewind d (clkTape V (0 + V)) s2 s3
        (clkTape_read_ne_start V (0 + V)) hs2 hs3 outT.cells hns outT.head
        (transitionInput cV.input) (transitionTape (cV.work 0))
      have hrewound := simTM_step_rewound d
        (transitionInput^[outT.head] (transitionInput cV.input))
        (transitionTape^[outT.head] (transitionTape (cV.work 0)))
        (clkTape V (0 + V)) s2 s3 ⟨0, outT.cells⟩
        (by show outT.cells 0 = Γ.start; rw [hcells]; exact hSI.1) rfl
        (clkTape_read_ne_start V (0 + V)) hs2 hs3
      have hwipe := simTM_step_wipe d
        (transitionInput (transitionInput^[outT.head] (transitionInput cV.input)))
        (transitionTape (transitionTape^[outT.head] (transitionTape (cV.work 0))))
        (clkTape V (0 + V)) s2 s3 ((⟨0, outT.cells⟩ : Tape).move Dir3.right)
        (by show outT.cells 1 ≠ Γ.start; exact hns 1 le_rfl)
        (clkTape_read_ne_start V (0 + V)) hs2 hs3
      have hchain := TM.reachesIn.step hpre (TM.reachesIn_trans _ hrun
        (TM.reachesIn.step htime (TM.reachesIn_trans _ hrew
          (TM.reachesIn.step hrewound (TM.reachesIn.step hwipe TM.reachesIn.zero)))))
      refine ⟨_, _, ?_, hchain, rfl, ?_⟩
      · omega
      · show (((⟨0, outT.cells⟩ : Tape).move Dir3.right).write Γ.blank).HasOutput
          (clockedOutput d V x)
        rw [clockedOutput, hev]
        refine ⟨fun i hi => absurd hi (by simp), ?_⟩
        show Function.update outT.cells 1 Γ.blank (0 + 1) = Γ.blank
        simp

/-! ### The clock preparation -/

/-- The Horner-prefix cap `polyEvalTM` asks for, at the input length. -/
noncomputable def prepCap (p : Polynomial ℕ) (N : ℕ) : ℕ :=
  ((polyCoeffs p).sum + 1) * (N + 1) ^ (polyCoeffs p).length + N

/-- Measure the input length into register `2`, then evaluate the clock polynomial there,
    leaving the clock in register `1`. -/
noncomputable def prepTM (p : Polynomial ℕ) : TM 4 :=
  seqTM (inputLenRegTM 2) (polyEvalTM 2 1 3 p)

lemma prepTM_hoareTime (p : Polynomial ℕ) (x : List Bool) :
    (prepTM p).HoareTime
      (EmitPred ⟨1, (Tape.init (x.map Γ.ofBool)).cells⟩ (fun _ => regTape 0) [])
      (EmitPred ⟨1, (Tape.init (x.map Γ.ofBool)).cells⟩
        (simWork (regTape 0) (regTape (p.eval x.length)) (regTape x.length)
          (regTape (p.eval x.length))) [])
      (2 * x.length + 4 + 1 +
        (opBudget (prepCap p x.length) + 1 +
          ((p.natDegree + 1) * (layerBudget (prepCap p x.length) + 1) + 1))) := by
  set N := x.length with hN
  set M := prepCap p N with hM
  set inp₀ : Tape := ⟨1, (Tape.init (x.map Γ.ofBool)).cells⟩ with hinp
  have hinp₀ : Parked inp₀ := parked_init_input x
  have hlen := inputLenRegTM_hoareTime (n := 4) 2 x (fun _ => regTape 0) []
    (fun i _ => parked_regTape 0) rfl
  set W1 : Fin 4 → Tape := Function.update (fun _ => regTape 0) 2 (regTape N) with hW1
  have hW1p : ∀ i, Parked (W1 i) := by
    intro i
    rw [hW1]
    by_cases hi : i = 2
    · subst hi; rw [Function.update_self]; exact parked_regTape _
    · rw [Function.update_of_ne hi]; exact parked_regTape 0
  have hpoly := polyEvalTM_hoareTime (n := 4) 2 1 3 (by decide) (by decide) (by decide)
    p M N 0 0 (by rw [hM, prepCap]; omega) (by omega) (by omega)
    (fun k _ => le_trans (hornerFold_take_le N _ _) (by rw [hM, prepCap]; omega))
    inp₀ W1 [] hinp₀ hW1p
    (by rw [hW1, Function.update_self])
    (by rw [hW1, Function.update_of_ne (by decide : (1 : Fin 4) ≠ 2)])
    (by rw [hW1, Function.update_of_ne (by decide : (3 : Fin 4) ≠ 2)])
  have hfin : Function.update (Function.update W1 3 (regTape (p.eval N))) 1
      (regTape (p.eval N))
      = simWork (regTape 0) (regTape (p.eval N)) (regTape N) (regTape (p.eval N)) := by
    funext i
    fin_cases i
    · show Function.update (Function.update W1 3 (regTape (p.eval N))) 1
          (regTape (p.eval N)) 0 = regTape 0
      rw [Function.update_of_ne (by decide : (0 : Fin 4) ≠ 1),
        Function.update_of_ne (by decide : (0 : Fin 4) ≠ 3), hW1,
        Function.update_of_ne (by decide : (0 : Fin 4) ≠ 2)]
    · show Function.update (Function.update W1 3 (regTape (p.eval N))) 1
          (regTape (p.eval N)) 1 = regTape (p.eval N)
      rw [Function.update_self]
    · show Function.update (Function.update W1 3 (regTape (p.eval N))) 1
          (regTape (p.eval N)) 2 = regTape N
      rw [Function.update_of_ne (by decide : (2 : Fin 4) ≠ 1),
        Function.update_of_ne (by decide : (2 : Fin 4) ≠ 3), hW1, Function.update_self]
    · show Function.update (Function.update W1 3 (regTape (p.eval N))) 1
          (regTape (p.eval N)) 3 = regTape (p.eval N)
      rw [Function.update_of_ne (by decide : (3 : Fin 4) ≠ 1), Function.update_self]
  rw [hfin] at hpoly
  exact seqTM_hoareTime _ _ hlen
    (fun _ _ _ h => emitPred_transition hinp₀ hW1p [] _ _ _ h) hpoly


/-! ### The whole machine -/

/-- **The clocked machine for a fixed description.** Bump, build the clock, simulate. -/
noncomputable def clockedTM (d : TMDesc) (p : Polynomial ℕ) : TM 4 :=
  seqTM bumpTM (seqTM (prepTM p) (simTM d))

/-- Its step bound. -/
noncomputable def clockedTime (p : Polynomial ℕ) (N : ℕ) : ℕ :=
  1 + 1 + ((2 * N + 4 + 1 +
    (opBudget (prepCap p N) + 1 +
      ((p.natDegree + 1) * (layerBudget (prepCap p N) + 1) + 1))) + 1 +
    (2 * p.eval N + 6))

lemma clockedTM_computesInTime (d : TMDesc) (p : Polynomial ℕ) :
    (clockedTM d p).ComputesInTime
      (fun x => clockedOutput d (p.eval x.length) x) (clockedTime p) := by
  intro x
  set N := x.length with hN
  set inp₀ : Tape := ⟨1, (Tape.init (x.map Γ.ofBool)).cells⟩ with hinp
  have hinp₀ : Parked inp₀ := parked_init_input x
  have hZp : ∀ i : Fin 4, Parked ((fun _ => regTape 0) i) := fun _ => parked_regTape 0
  have hbump : (bumpTM (n := 4)).HoareTime
      (fun inp work out => inp = Tape.init (x.map Γ.ofBool) ∧
        (∀ i, work i = Tape.init []) ∧ out = Tape.init [])
      (EmitPred inp₀ (fun _ => regTape 0) []) 1 := by
    refine (bumpTM_hoareTime (n := 4) x).consequence (fun _ _ _ h => h)
      (fun inp work out h => ?_) (le_refl 1)
    obtain ⟨hi, hw, ho⟩ := h
    exact ⟨hi, funext (fun i => (hw i).eq_regT), ho⟩
  have hWp : ∀ i : Fin 4, Parked
      (simWork (regTape 0) (regTape (p.eval N)) (regTape N) (regTape (p.eval N)) i) := by
    intro i
    fin_cases i <;> exact parked_regTape _
  have hsim := simTM_hoareTime d x (p.eval N) (regTape N) (regTape (p.eval N))
    ((parked_regTape N).2 1 le_rfl) ((parked_regTape (p.eval N)).2 1 le_rfl)
  have hrest := seqTM_hoareTime _ _ (prepTM_hoareTime p x)
    (fun _ _ _ h => emitPred_transition hinp₀ hWp [] _ _ _ h) hsim
  have htotal := seqTM_hoareTime _ _ hbump
    (fun _ _ _ h => emitPred_transition hinp₀ hZp [] _ _ _ h) hrest
  obtain ⟨c', t, ht, hreach, hhalt, hpost⟩ := htotal (Tape.init (x.map Γ.ofBool))
    (fun _ => Tape.init []) (Tape.init []) ⟨rfl, fun _ => rfl, rfl⟩
  exact ⟨c', t, ht, hreach, hhalt, hpost⟩

/-! ### The bound is a polynomial -/

open Polynomial in
/-- The Horner cap, as a polynomial. -/
noncomputable def prepCapPoly (p : Polynomial ℕ) : Polynomial ℕ :=
  C ((polyCoeffs p).sum + 1) * (X + 1) ^ (polyCoeffs p).length + X

open Polynomial in
lemma prepCapPoly_eval (p : Polynomial ℕ) (N : ℕ) :
    (prepCapPoly p).eval N = prepCap p N := by
  simp only [prepCapPoly, prepCap, eval_add, eval_mul, eval_pow, eval_C, eval_X,
    eval_one]

open Polynomial in
/-- The whole step bound, as a polynomial. -/
noncomputable def clockedTimePoly (p : Polynomial ℕ) : Polynomial ℕ :=
  let q := prepCapPoly p
  let ob := C 32 * (q + 2) ^ 3
  let lb := C 4 * ob + 3
  2 + ((2 * X + 4 + 1 + (ob + 1 + (C (p.natDegree + 1) * (lb + 1) + 1))) + 1 +
    (2 * p + 6))

open Polynomial in
lemma clockedTimePoly_eval (p : Polynomial ℕ) (N : ℕ) :
    (clockedTimePoly p).eval N = clockedTime p N := by
  simp only [clockedTimePoly, clockedTime, opBudget, layerBudget, eval_add, eval_mul,
    eval_pow, eval_C, eval_X, eval_ofNat, eval_one, prepCapPoly_eval]
  ring

/-- **The clocked truncation of a fixed description is polynomial-time.** -/
lemma clockedOutput_mem_FP (d : TMDesc) (p : Polynomial ℕ) :
    (fun x => clockedOutput d (p.eval x.length) x) ∈ Complexity.FP := by
  rw [Complexity.mem_FP_iff_computesInTime_polynomial]
  refine ⟨4, clockedTM d p, clockedTimePoly p, ?_⟩
  refine (clockedTM_computesInTime d p).mono (fun m => ?_)
  rw [clockedTimePoly_eval]

end LogicalInduction.MachineExec



