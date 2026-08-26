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
      if q = (d.toTM).qhalt then
        (Sum.inr 3, fun i => readBackWrite (wHeads i), readBackWrite oHead,
          idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
      else if wHeads 1 ≠ Γ.one then
        (Sum.inr 1, fun i => readBackWrite (wHeads i), readBackWrite oHead,
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
        split_ifs with hq hc
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
  simp only [simδ, if_neg hq]
  rw [if_neg (by simp [hclk])]
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
    (hi : inp.read ≠ Γ.start) (hw0 : w0.read ≠ Γ.start)
    (hclk : clk.read ≠ Γ.start) (hs2 : s2.read ≠ Γ.start) (hs3 : s3.read ≠ Γ.start)
    (hδ : simδ d s inp.read (fun i => (simWork w0 clk s2 s3 i).read) out.read
      = (s', fun i => readBackWrite ((simWork w0 clk s2 s3 i).read), ow,
          idleDir inp.read,
          fun i => idleDir ((simWork w0 clk s2 s3 i).read), odir)) :
    (simTM d).step ⟨s, inp, simWork w0 clk s2 s3, out⟩
      = some ⟨s', inp, simWork w0 clk s2 s3, out.writeAndMove ow.toΓ odir⟩ := by
  rw [TM.step]
  simp only [simTM]
  rw [if_neg hs, hδ]
  simp only [Option.some.injEq, Cfg.mk.injEq, true_and, and_true]
  refine ⟨by rw [idleDir, if_neg hi]; rfl, ?_⟩
  funext i
  fin_cases i
  · show w0.writeAndMove (readBackWrite w0.read).toΓ (idleDir w0.read) = w0
    rw [writeBack_move w0 hw0, idleDir, if_neg hw0]; rfl
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
    (hi : inp.read ≠ Γ.start) (hw0 : w0.read ≠ Γ.start) (hout : out.read ≠ Γ.start)
    (hclk : clk.read ≠ Γ.start) (hs2 : s2.read ≠ Γ.start) (hs3 : s3.read ≠ Γ.start)
    (hδ : simδ d s inp.read (fun i => (simWork w0 clk s2 s3 i).read) out.read
      = (s', fun i => readBackWrite ((simWork w0 clk s2 s3 i).read),
          readBackWrite out.read, idleDir inp.read,
          fun i => idleDir ((simWork w0 clk s2 s3 i).read), idleDir out.read)) :
    (simTM d).step ⟨s, inp, simWork w0 clk s2 s3, out⟩
      = some ⟨s', inp, simWork w0 clk s2 s3, out⟩ := by
  rw [simTM_step_phase d s s' hs inp w0 clk s2 s3 out _ _ hi hw0 hclk hs2 hs3 hδ,
    writeBack_move out hout, idleDir, if_neg hout]
  rfl

lemma simTM_step_halt (d : TMDesc) (inp w0 clk s2 s3 out : Tape)
    (hi : inp.read ≠ Γ.start) (hw0 : w0.read ≠ Γ.start) (hout : out.read ≠ Γ.start)
    (hclk : clk.read ≠ Γ.start) (hs2 : s2.read ≠ Γ.start) (hs3 : s3.read ≠ Γ.start) :
    (simTM d).step ⟨Sum.inl (d.toTM).qhalt, inp, simWork w0 clk s2 s3, out⟩
      = some ⟨Sum.inr 3, inp, simWork w0 clk s2 s3, out⟩ :=
  simTM_step_idle d _ _ (simTM_ne_halt_inl d _) inp w0 clk s2 s3 out hi hw0 hout hclk
    hs2 hs3 (by simp only [simδ]; rw [if_true])

lemma simTM_step_timeout (d : TMDesc) (q : (d.toTM).Q) (hq : q ≠ (d.toTM).qhalt)
    (inp w0 clk s2 s3 out : Tape) (hclock : clk.read ≠ Γ.one)
    (hi : inp.read ≠ Γ.start) (hw0 : w0.read ≠ Γ.start) (hout : out.read ≠ Γ.start)
    (hclk : clk.read ≠ Γ.start) (hs2 : s2.read ≠ Γ.start) (hs3 : s3.read ≠ Γ.start) :
    (simTM d).step ⟨Sum.inl q, inp, simWork w0 clk s2 s3, out⟩
      = some ⟨Sum.inr 1, inp, simWork w0 clk s2 s3, out⟩ :=
  simTM_step_idle d _ _ (simTM_ne_halt_inl d _) inp w0 clk s2 s3 out hi hw0 hout hclk
    hs2 hs3 (by simp only [simδ]; rw [if_neg hq]; simp only [simWork_one]; rw [if_pos hclock])


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
    (hi : inp.read ≠ Γ.start) (hw0 : w0.read ≠ Γ.start) (hout : out.read ≠ Γ.start)
    (hclk : clk.read ≠ Γ.start) (hs2 : s2.read ≠ Γ.start) (hs3 : s3.read ≠ Γ.start) :
    (simTM d).step ⟨Sum.inr 1, inp, simWork w0 clk s2 s3, out⟩
      = some ⟨Sum.inr 1, inp, simWork w0 clk s2 s3, out.move Dir3.left⟩ := by
  rw [simTM_step_phase d (Sum.inr 1) (Sum.inr 1) (by simp) inp w0 clk s2 s3 out
    (readBackWrite out.read) Dir3.left hi hw0 hclk hs2 hs3
    (by simp only [simδ]
        rw [if_neg (by decide : ¬(((1 : Fin 4) : ℕ) = 0)),
          if_pos (by decide : ((1 : Fin 4) : ℕ) = 1), if_neg hout]),
    writeBack_move out hout]

lemma simTM_step_rewound (d : TMDesc) (inp w0 clk s2 s3 out : Tape)
    (hi : inp.read ≠ Γ.start) (hw0 : w0.read ≠ Γ.start) (hout : out.read = Γ.start)
    (hhead : out.head = 0)
    (hclk : clk.read ≠ Γ.start) (hs2 : s2.read ≠ Γ.start) (hs3 : s3.read ≠ Γ.start) :
    (simTM d).step ⟨Sum.inr 1, inp, simWork w0 clk s2 s3, out⟩
      = some ⟨Sum.inr 2, inp, simWork w0 clk s2 s3, out.move Dir3.right⟩ := by
  rw [simTM_step_phase d (Sum.inr 1) (Sum.inr 2) (by simp) inp w0 clk s2 s3 out
    (readBackWrite out.read) Dir3.right hi hw0 hclk hs2 hs3
    (by simp only [simδ]
        rw [if_neg (by decide : ¬(((1 : Fin 4) : ℕ) = 0)),
          if_pos (by decide : ((1 : Fin 4) : ℕ) = 1), if_pos hout])]
  simp only [Tape.writeAndMove, Tape.write, hhead, if_true]

lemma simTM_step_wipe (d : TMDesc) (inp w0 clk s2 s3 out : Tape)
    (hi : inp.read ≠ Γ.start) (hw0 : w0.read ≠ Γ.start) (hout : out.read ≠ Γ.start)
    (hclk : clk.read ≠ Γ.start) (hs2 : s2.read ≠ Γ.start) (hs3 : s3.read ≠ Γ.start) :
    (simTM d).step ⟨Sum.inr 2, inp, simWork w0 clk s2 s3, out⟩
      = some ⟨Sum.inr 3, inp, simWork w0 clk s2 s3, out.write Γ.blank⟩ := by
  rw [simTM_step_phase d (Sum.inr 2) (Sum.inr 3) (by simp) inp w0 clk s2 s3 out
    Γw.blank (idleDir out.read) hi hw0 hclk hs2 hs3
    (by simp only [simδ]
        rw [if_neg (by decide : ¬(((2 : Fin 4) : ℕ) = 0)),
          if_neg (by decide : ¬(((2 : Fin 4) : ℕ) = 1)),
          if_pos (by decide : ((2 : Fin 4) : ℕ) = 2)])]
  simp only [Tape.writeAndMove, idleDir, if_neg hout]
  rfl

/-- Rewinding the output head to the left end. -/
lemma simTM_rewind (d : TMDesc) (inp w0 clk s2 s3 : Tape)
    (hi : inp.read ≠ Γ.start) (hw0 : w0.read ≠ Γ.start)
    (hclk : clk.read ≠ Γ.start) (hs2 : s2.read ≠ Γ.start) (hs3 : s3.read ≠ Γ.start)
    (cells : ℕ → Γ) (hns : ∀ j, 1 ≤ j → cells j ≠ Γ.start) :
    ∀ h : ℕ, (simTM d).reachesIn h
      ⟨Sum.inr 1, inp, simWork w0 clk s2 s3, ⟨h, cells⟩⟩
      ⟨Sum.inr 1, inp, simWork w0 clk s2 s3, ⟨0, cells⟩⟩
  | 0 => TM.reachesIn.zero
  | h + 1 => by
      refine TM.reachesIn.step
        (simTM_step_rewind d inp w0 clk s2 s3 ⟨h + 1, cells⟩ hi hw0 ?_ hclk hs2 hs3) ?_
      · exact hns (h + 1) (by omega)
      · exact simTM_rewind d inp w0 clk s2 s3 hi hw0 hclk hs2 hs3 cells hns h

end LogicalInduction.MachineExec



