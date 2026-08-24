/-
# FAF Stage-3 probe: an executable finite coding of described Turing machines

This file is **FAF-owned**, not upstream complexitylib. It lives in the ported
complexitylib tree only because FAF cannot yet `import Complexitylib` (the compatibility
fork is not wired in as a dependency). Its eventual home is

    LogicalInduction/Construction/Machine/DescExec.lean

The Stage-3 bottleneck identified by the adoption audit was executability: FAF's
`LIACompiler` needs a `Primrec₂` evaluator for the trader enumeration, while
complexitylib's configurations carry tapes as *functions* `ℕ → Γ`, which `Primrec`
cannot see.

The resolution is that we never need to execute an arbitrary `TM k`, nor even the fixed
universal machine `utmTM`. The enumeration is indexed by *descriptions*, and a described
machine `TMDesc.toTM` has

* `Q := Fin (2 ^ d.w + 1)` — numeric states, and
* `δ` given by `TMDesc.lookup`, a `List.find?` over `d.entries`

so it is already first-order finite data. This file gives the finite coding and proves
it tracks the real semantics step for step.

## Main results

* `CodedTape.decode_write`, `CodedTape.decode_move` — the coded tape operations commute
  with `Tape.write` / `Tape.move` under decoding.
* `codedStep_eq` — **the vertical simulation lemma**: one coded step decodes to exactly
  one `TMDesc.toTM` step.
* `runCoded_eq` — its iteration: `t` coded steps decode to `t` real steps, via
  `reachesIn`.
* `codedStep_primrec` — the coded step is primitive recursive in the pair
  `(description, configuration)`.
-/
import Complexitylib.Models.TuringMachine.UTM.Universal
import Mathlib.Computability.Primrec.List

open Complexity

namespace LogicalInduction.MachineExec

/-! ## Finite tape coding

A one-sided tape is coded by its head position and a finite window of cells `1, 2, …`;
everything beyond the window is blank. Cell `0` is always `Γ.start`.

The decode map is definitionally `Tape.init`'s cell function, which is what makes the
commutation proofs short. -/

/-- A finite coding of a one-sided tape: `cells` lists the contents of cells
`1, 2, …`, with blanks understood beyond the end. -/
structure CodedTape where
  /-- The head position; cell `0` is the left-end marker. -/
  head : ℕ
  /-- The contents of cells `1, 2, …`; blank beyond the end. -/
  cells : List Γ
  deriving DecidableEq, Inhabited

namespace CodedTape

/-- Decode to a genuine `Tape`. The cell function is exactly `Tape.init`'s. -/
def decode (t : CodedTape) : Tape where
  head := t.head
  cells := fun i => if i = 0 then Γ.start else (t.cells[i - 1]?).getD Γ.blank

@[simp] theorem decode_head (t : CodedTape) : t.decode.head = t.head := rfl

@[simp] theorem decode_cells_zero (t : CodedTape) : t.decode.cells 0 = Γ.start := rfl

theorem decode_cells_succ (t : CodedTape) (i : ℕ) :
    t.decode.cells (i + 1) = (t.cells[i]?).getD Γ.blank := by
  simp [decode]

/-- Overwrite position `i` of a cell list, padding with blanks if the list is short.

Written as a `range`/`map` rather than a two-argument recursion: the semantics is the
same, but this form is directly primitive recursive (`Primrec.list_range`,
`Primrec.list_map`, `Primrec.list_getElem?`), which the recursive form is not without
extra work. -/
def setAt (l : List Γ) (i : ℕ) (s : Γ) : List Γ :=
  (List.range (max l.length (i + 1))).map
    fun j => if j = i then s else (l[j]?).getD Γ.blank

/-- `setAt` writes exactly where it is told and nowhere else. -/
theorem getElem?_setAt (l : List Γ) (i j : ℕ) (s : Γ) :
    ((setAt l i s)[j]?).getD Γ.blank
      = if j = i then s else (l[j]?).getD Γ.blank := by
  by_cases hj : j < max l.length (i + 1)
  · rw [setAt, List.getElem?_map, List.getElem?_range hj]
    simp
  · have hji : j ≠ i := by omega
    have hjl : l[j]? = none := List.getElem?_eq_none (by omega)
    rw [setAt, List.getElem?_map,
      List.getElem?_eq_none (by simpa using Nat.le_of_not_lt hj)]
    simp [hji, hjl]

/-- Coded write: writing at cell `0` is a no-op, mirroring `Tape.write`. -/
def write (t : CodedTape) (s : Γ) : CodedTape :=
  if t.head = 0 then t else { t with cells := setAt t.cells (t.head - 1) s }

/-- Coded head motion, mirroring `Tape.move` (left at `0` saturates). -/
def move (t : CodedTape) (d : Dir3) : CodedTape :=
  match d with
  | .left => { t with head := t.head - 1 }
  | .right => { t with head := t.head + 1 }
  | .stay => t

/-- Coded read, mirroring `Tape.read`. -/
def read (t : CodedTape) : Γ :=
  if t.head = 0 then Γ.start else (t.cells[t.head - 1]?).getD Γ.blank

/-- Coded write, then move — mirroring `Tape.writeAndMove`. -/
def writeAndMove (t : CodedTape) (s : Γ) (d : Dir3) : CodedTape :=
  (t.write s).move d

@[simp] theorem decode_read (t : CodedTape) : t.decode.read = t.read := rfl

theorem decode_move (t : CodedTape) (d : Dir3) :
    (t.move d).decode = t.decode.move d := by
  cases d <;> rfl

theorem decode_write (t : CodedTape) (s : Γ) :
    (t.write s).decode = t.decode.write s := by
  by_cases h : t.head = 0
  · simp [write, Tape.write, decode, h]
  · refine Tape.ext ?_ ?_
    · simp [write, Tape.write, decode, h]
    · funext i
      cases i with
      | zero => simp [write, Tape.write, decode, h, Function.update_of_ne (by omega : (0:ℕ) ≠ t.head)]
      | succ i =>
          have hd : t.decode.head = t.head := rfl
          rw [Tape.write, hd, if_neg h]
          simp only [write, if_neg h, decode, Nat.succ_ne_zero, if_false,
            Function.update_apply]
          rw [getElem?_setAt]
          simp only [Nat.add_sub_cancel]
          by_cases hi : i + 1 = t.head
          · rw [if_pos (by omega : i = t.head - 1), if_pos hi]
          · rw [if_neg (by omega : ¬ i = t.head - 1), if_neg hi]

theorem decode_writeAndMove (t : CodedTape) (s : Γ) (d : Dir3) :
    (t.writeAndMove s d).decode = t.decode.writeAndMove s d := by
  rw [writeAndMove, decode_move, decode_write]

end CodedTape

/-! ## Finite configuration coding

A described machine has a single work tape, so a configuration is three coded tapes and
a numeric state. States are kept *clamped* to `≤ 2 ^ d.w`, which is exactly the invariant
`TMDesc.toTM.δ` maintains, so decoding is a `Fin` injection with no side condition. -/

/-- A finite coding of a `TMDesc.toTM` configuration. -/
structure CodedCfg where
  /-- The state, as a natural number; decoding clamps it to `≤ 2 ^ d.w`. -/
  state : ℕ
  /-- The read-only input tape. -/
  input : CodedTape
  /-- The single work tape. -/
  work : CodedTape
  /-- The output tape. -/
  output : CodedTape
  deriving DecidableEq, Inhabited

namespace CodedCfg

variable (d : TMDesc)

/-- Decode a coded state into `TMDesc.toTM`'s state type `Fin (2 ^ d.w + 1)`. -/
def decodeState (q : ℕ) : (d.toTM).Q :=
  ⟨min q (2 ^ d.w), Nat.lt_succ_of_le (Nat.min_le_right ..)⟩

/-- Decode a coded configuration. -/
def decode (c : CodedCfg) : Cfg 1 (d.toTM).Q where
  state := decodeState d c.state
  input := c.input.decode
  work := fun _ => c.work.decode
  output := c.output.decode

end CodedCfg

/-- **The executable step.** Reads the three heads, consults the description's transition
table, and writes/moves — mirroring `TM.step` for `TMDesc.toTM` exactly, but on finite
data. Returns `none` exactly when the machine has halted. -/
def codedStep (d : TMDesc) (c : CodedCfg) : Option CodedCfg :=
  if min c.state (2 ^ d.w) = min d.qhalt (2 ^ d.w) then none
  else
    let si := c.input.read
    let sw := c.work.read
    let so := c.output.read
    let a := d.lookup (min c.state (2 ^ d.w)) si sw so
    some
      { state := min a.q' (2 ^ d.w)
        input := c.input.move (if si = Γ.start then .right else a.di)
        work := c.work.writeAndMove a.ww.toΓ (if sw = Γ.start then .right else a.dw)
        output := c.output.writeAndMove a.wo.toΓ (if so = Γ.start then .right else a.dOut) }

/-- **The vertical simulation lemma.** One coded step decodes to exactly one
`TMDesc.toTM` step. -/
theorem codedStep_eq (d : TMDesc) (c : CodedCfg) :
    (codedStep d c).map (CodedCfg.decode d) = (d.toTM).step (CodedCfg.decode d c) := by
  have hq : ((CodedCfg.decode d c).state = (d.toTM).qhalt)
      ↔ (min c.state (2 ^ d.w) = min d.qhalt (2 ^ d.w)) := by
    simp [CodedCfg.decode, CodedCfg.decodeState, TMDesc.toTM, Fin.ext_iff]
  by_cases h : min c.state (2 ^ d.w) = min d.qhalt (2 ^ d.w)
  · rw [codedStep, if_pos h, TM.step, if_pos (hq.mpr h)]
    rfl
  · rw [codedStep, if_neg h, TM.step, if_neg (fun hh => h (hq.mp hh))]
    simp only [Option.map_some]
    -- both sides now name the same table action
    have hwork : (fun i : Fin 1 => ((CodedCfg.decode d c).work i).read)
        = fun _ => c.work.read := by
      funext i; simp [CodedCfg.decode]
    simp only [CodedCfg.decode, CodedCfg.decodeState, TMDesc.toTM,
      CodedTape.decode_read, Option.some.injEq, Cfg.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact Fin.ext (Nat.min_eq_left (Nat.min_le_right _ _))
    · rw [CodedTape.decode_move]
    · funext i; rw [CodedTape.decode_writeAndMove]
    · rw [CodedTape.decode_writeAndMove]

/-- Bounded iteration of the executable step. -/
def runCoded (d : TMDesc) : ℕ → CodedCfg → Option CodedCfg
  | 0, c => some c
  | (t + 1), c => (codedStep d c).bind (runCoded d t)

/-- **Iterated simulation.** If the executable run of `t` steps succeeds, the real
machine reaches the decoded result in exactly `t` steps. -/
theorem runCoded_eq (d : TMDesc) :
    ∀ (t : ℕ) (c c' : CodedCfg), runCoded d t c = some c' →
      (d.toTM).reachesIn t (CodedCfg.decode d c) (CodedCfg.decode d c')
  | 0, c, c', h => by
      rw [runCoded, Option.some.injEq] at h; subst h; exact .zero
  | (t + 1), c, c', h => by
      rw [runCoded] at h
      cases hs : codedStep d c with
      | none => rw [hs] at h; exact absurd h (by simp)
      | some c₁ =>
          rw [hs] at h
          refine .step ?_ (runCoded_eq d t c₁ c' h)
          have h2 := codedStep_eq d c
          rw [hs, Option.map_some] at h2
          exact h2.symm

/-! ## Primitive recursiveness

`Γ` is a four-element type, so it is `Primcodable` via `Fin 4`; everything else is built
from `ℕ`, `List`, and products, for which Mathlib's `Primrec` API already applies. -/

/-- `Γ` as a four-element type. -/
def ΓEquivFin : Γ ≃ Fin 4 where
  toFun := fun g => match g with
    | .zero => 0 | .one => 1 | .blank => 2 | .start => 3
  invFun := fun i => match i with
    | 0 => .zero | 1 => .one | 2 => .blank | 3 => .start
  left_inv := by intro g; cases g <;> rfl
  right_inv := by decide

instance : Primcodable Γ := Primcodable.ofEquiv (Fin 4) ΓEquivFin

instance : Primcodable Dir3 :=
  Primcodable.ofEquiv (Fin 3)
    { toFun := fun d => match d with | .left => 0 | .right => 1 | .stay => 2
      invFun := fun i => match i with | 0 => .left | 1 => .right | 2 => .stay
      left_inv := by intro d; cases d <;> rfl
      right_inv := by decide }

instance : Primcodable Γw :=
  Primcodable.ofEquiv (Fin 3)
    { toFun := fun g => match g with | .zero => 0 | .one => 1 | .blank => 2
      invFun := fun i => match i with | 0 => .zero | 1 => .one | 2 => .blank
      left_inv := by intro g; cases g <;> rfl
      right_inv := by decide }

/-- `CodedTape` as a pair. -/
def codedTapeEquiv : CodedTape ≃ ℕ × List Γ where
  toFun t := (t.head, t.cells)
  invFun p := ⟨p.1, p.2⟩
  left_inv := by intro t; cases t; rfl
  right_inv := by intro p; cases p; rfl

instance : Primcodable CodedTape := Primcodable.ofEquiv _ codedTapeEquiv

/-- `CodedCfg` as a nested product. -/
def codedCfgEquiv : CodedCfg ≃ ℕ × CodedTape × CodedTape × CodedTape where
  toFun c := (c.state, c.input, c.work, c.output)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
  left_inv := by intro c; cases c; rfl
  right_inv := by intro p; obtain ⟨_, _, _, _⟩ := p; rfl

instance : Primcodable CodedCfg := Primcodable.ofEquiv _ codedCfgEquiv

/-! ### Descriptions are codable

`DescAct`, `DescEntry` and `TMDesc` are plain first-order records, so each is coded by an
equivalence with a nested product. -/

/-- `DescAct` as a nested product. -/
def descActEquiv : DescAct ≃ ℕ × Γw × Γw × Dir3 × Dir3 × Dir3 where
  toFun a := (a.q', a.ww, a.wo, a.di, a.dw, a.dOut)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2⟩
  left_inv := by intro a; cases a; rfl
  right_inv := by intro p; obtain ⟨_, _, _, _, _, _⟩ := p; rfl

instance : Primcodable DescAct := Primcodable.ofEquiv _ descActEquiv

/-- `DescEntry` as a nested product. -/
def descEntryEquiv : DescEntry ≃ ℕ × Γ × Γ × Γ × DescAct where
  toFun e := (e.q, e.si, e.sw, e.so, e.act)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩
  left_inv := by intro e; cases e; rfl
  right_inv := by intro p; obtain ⟨_, _, _, _, _⟩ := p; rfl

instance : Primcodable DescEntry := Primcodable.ofEquiv _ descEntryEquiv

/-- `TMDesc` as a nested product. -/
def tmDescEquiv : TMDesc ≃ ℕ × ℕ × ℕ × List DescEntry where
  toFun d := (d.w, d.qstart, d.qhalt, d.entries)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
  left_inv := by intro d; cases d; rfl
  right_inv := by intro p; obtain ⟨_, _, _, _⟩ := p; rfl

instance : Primcodable TMDesc := Primcodable.ofEquiv _ tmDescEquiv

/-! ### Primrec accessors -/

open Primrec in
theorem primrec_descAct_q' : Primrec DescAct.q' :=
  (Primrec.fst.comp (Primrec.of_equiv (e := descActEquiv))).of_eq fun _ => rfl

open Primrec in
theorem primrec_descAct_ww : Primrec DescAct.ww :=
  ((Primrec.fst.comp Primrec.snd).comp (Primrec.of_equiv (e := descActEquiv))).of_eq
    fun _ => rfl

open Primrec in
theorem primrec_descAct_wo : Primrec DescAct.wo :=
  ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).comp
    (Primrec.of_equiv (e := descActEquiv))).of_eq fun _ => rfl

open Primrec in
theorem primrec_descAct_di : Primrec DescAct.di :=
  ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).comp
    (Primrec.of_equiv (e := descActEquiv))).of_eq fun _ => rfl

open Primrec in
theorem primrec_descAct_dw : Primrec DescAct.dw :=
  ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))).comp
    (Primrec.of_equiv (e := descActEquiv))).of_eq fun _ => rfl

open Primrec in
theorem primrec_descAct_dOut : Primrec DescAct.dOut :=
  ((Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))).comp
    (Primrec.of_equiv (e := descActEquiv))).of_eq fun _ => rfl

open Primrec in
theorem primrec_descEntry_act : Primrec DescEntry.act :=
  ((Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).comp
    (Primrec.of_equiv (e := descEntryEquiv))).of_eq fun _ => rfl

open Primrec in
theorem primrec_tmDesc_w : Primrec TMDesc.w :=
  (Primrec.fst.comp (Primrec.of_equiv (e := tmDescEquiv))).of_eq fun _ => rfl

open Primrec in
theorem primrec_tmDesc_qhalt : Primrec TMDesc.qhalt :=
  ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).comp
    (Primrec.of_equiv (e := tmDescEquiv))).of_eq fun _ => rfl

open Primrec in
theorem primrec_tmDesc_entries : Primrec TMDesc.entries :=
  ((Primrec.snd.comp (Primrec.snd.comp Primrec.snd)).comp
    (Primrec.of_equiv (e := tmDescEquiv))).of_eq fun _ => rfl

/-! ### `List.find?` is primitive recursive

Mathlib supplies `Primrec.list_findIdx` and `Primrec.list_getElem?`; `find?` is their
composite, because `findIdx` returns the list length when nothing matches and
`getElem?` returns `none` there. -/

theorem list_find?_eq_getElem? {β : Type*} (p : β → Bool) :
    ∀ l : List β, l.find? p = l[l.findIdx p]?
  | [] => rfl
  | a :: l => by
      by_cases h : p a
      · simp [List.findIdx_cons, h]
      · simp [List.findIdx_cons, h, list_find?_eq_getElem? p l]

open Primrec in
theorem primrec_list_find? {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → List β} {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec fun a => (f a).find? (p a) :=
  ((Primrec.list_getElem?.comp hf (Primrec.list_findIdx hf hp))).of_eq fun a =>
    (list_find?_eq_getElem? (p a) (f a)).symm

/-! ### The transition table lookup is primitive recursive -/

/-- Any function out of `Γ` is primitive recursive: `Γ` has four elements, so the
function is a fixed finite lookup table indexed by the code of its argument. -/
theorem primrec_of_gamma {σ : Type*} [Primcodable σ] (g : Γ → σ) (dflt : σ) :
    Primrec g :=
  ((Primrec.list_getD dflt).comp
      (Primrec.const [g .zero, g .one, g .blank, g .start])
      Primrec.encode).of_eq fun x => by cases x <;> rfl

theorem primrec_readback : Primrec TMDesc.readback :=
  primrec_of_gamma TMDesc.readback Γw.blank

set_option maxHeartbeats 1000000 in
/-- The default action taken when no table row matches. -/
theorem primrec_defaultAct :
    Primrec fun z : TMDesc × Γ × Γ => z.1.defaultAct z.2.1 z.2.2 := by
  refine (Primrec.of_equiv_symm.comp (Primrec.pair
    (primrec_tmDesc_qhalt.comp Primrec.fst) (Primrec.pair
      (primrec_readback.comp (Primrec.fst.comp Primrec.snd)) (Primrec.pair
        (primrec_readback.comp (Primrec.snd.comp Primrec.snd)) (Primrec.pair
          (Primrec.const Dir3.stay) (Primrec.pair
            (Primrec.const Dir3.stay) (Primrec.const Dir3.stay))))))).of_eq ?_
  intro z
  rfl

set_option maxHeartbeats 1000000 in
/-- The table-row match predicate. -/
theorem primrec_entryMatches :
    Primrec₂ fun (z : ℕ × Γ × Γ × Γ) (e : DescEntry) =>
      (e.q == z.1 && e.si == z.2.1 && e.sw == z.2.2.1 && e.so == z.2.2.2) := by
  set A := ℕ × Γ × Γ × Γ
  have hz : Primrec fun w : A × DescEntry => w.1 := Primrec.fst
  have he : Primrec fun w : A × DescEntry => descEntryEquiv w.2 :=
    (Primrec.of_equiv (e := descEntryEquiv)).comp Primrec.snd
  exact Primrec.and.comp
    (Primrec.and.comp
      (Primrec.and.comp
        (Primrec.beq.comp (Primrec.fst.comp he) (Primrec.fst.comp hz))
        (Primrec.beq.comp (Primrec.fst.comp (Primrec.snd.comp he))
          (Primrec.fst.comp (Primrec.snd.comp hz))))
      (Primrec.beq.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp he)))
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hz)))))
    (Primrec.beq.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
        (Primrec.snd.comp he))))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hz))))

set_option maxHeartbeats 1000000 in
/-- **The description's transition lookup is primitive recursive.** -/
theorem primrec_lookup :
    Primrec fun z : TMDesc × ℕ × Γ × Γ × Γ =>
      z.1.lookup z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 := by
  set A := TMDesc × ℕ × Γ × Γ × Γ
  have hfind : Primrec fun z : A =>
      z.1.entries.find? fun e =>
        (e.q == z.2.1 && e.si == z.2.2.1 && e.sw == z.2.2.2.1 && e.so == z.2.2.2.2) :=
    primrec_list_find? (primrec_tmDesc_entries.comp Primrec.fst)
      (primrec_entryMatches.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
  have hdef : Primrec fun z : A => z.1.defaultAct z.2.2.2.1 z.2.2.2.2 :=
    primrec_defaultAct.comp (Primrec.pair Primrec.fst
      (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
  exact (Primrec.option_casesOn hfind hdef
    (Primrec.to₂ (primrec_descEntry_act.comp Primrec.snd))).of_eq fun z => by
      rw [TMDesc.lookup]
      cases h : z.1.entries.find? fun e =>
        (e.q == z.2.1 && e.si == z.2.2.1 && e.sw == z.2.2.2.1 && e.so == z.2.2.2.2) <;>
        simp

/-! ### The coded tape operations are primitive recursive -/

open Primrec in
theorem primrec_tape_head : Primrec CodedTape.head :=
  (Primrec.fst.comp (Primrec.of_equiv (e := codedTapeEquiv))).of_eq fun _ => rfl

open Primrec in
theorem primrec_tape_cells : Primrec CodedTape.cells :=
  (Primrec.snd.comp (Primrec.of_equiv (e := codedTapeEquiv))).of_eq fun _ => rfl

set_option maxHeartbeats 1000000 in
theorem primrec_tape_read : Primrec CodedTape.read :=
  (Primrec.ite (Primrec.eq.comp primrec_tape_head (Primrec.const 0))
    (Primrec.const Γ.start)
    (Primrec.option_getD.comp
      (Primrec.list_getElem?.comp primrec_tape_cells
        (Primrec.nat_sub.comp primrec_tape_head (Primrec.const 1)))
      (Primrec.const Γ.blank))).of_eq fun _ => rfl

set_option maxHeartbeats 1000000 in
theorem primrec_setAt :
    Primrec fun z : List Γ × ℕ × Γ => CodedTape.setAt z.1 z.2.1 z.2.2 := by
  set A := List Γ × ℕ × Γ
  have hl : Primrec fun z : A => z.1 := Primrec.fst
  have hi : Primrec fun z : A => z.2.1 := Primrec.fst.comp Primrec.snd
  have hs : Primrec fun z : A => z.2.2 := Primrec.snd.comp Primrec.snd
  have hrange : Primrec fun z : A => List.range (max z.1.length (z.2.1 + 1)) :=
    Primrec.list_range.comp
      (Primrec.nat_max.comp (Primrec.list_length.comp hl) (Primrec.succ.comp hi))
  have hinner : Primrec₂ fun (z : A) (j : ℕ) =>
      if j = z.2.1 then z.2.2 else (z.1[j]?).getD Γ.blank :=
    Primrec.ite (Primrec.eq.comp Primrec.snd (hi.comp Primrec.fst))
      (hs.comp Primrec.fst)
      (Primrec.option_getD.comp
        (Primrec.list_getElem?.comp (hl.comp Primrec.fst) Primrec.snd)
        (Primrec.const Γ.blank))
  exact Primrec.list_map hrange hinner

set_option maxHeartbeats 1000000 in
theorem primrec_tape_write : Primrec fun z : CodedTape × Γ => z.1.write z.2 := by
  refine (Primrec.ite
    (Primrec.eq.comp (primrec_tape_head.comp Primrec.fst) (Primrec.const 0))
    Primrec.fst
    (Primrec.of_equiv_symm.comp (Primrec.pair
      (primrec_tape_head.comp Primrec.fst)
      (primrec_setAt.comp (Primrec.pair
        (primrec_tape_cells.comp Primrec.fst)
        (Primrec.pair
          (Primrec.nat_sub.comp (primrec_tape_head.comp Primrec.fst) (Primrec.const 1))
          Primrec.snd)))))).of_eq ?_
  rintro ⟨t, s⟩
  rw [CodedTape.write]
  split <;> rfl

set_option maxHeartbeats 1000000 in
theorem primrec_tape_move : Primrec fun z : CodedTape × Dir3 => z.1.move z.2 := by
  set B := CodedTape × Dir3
  have hcells : Primrec fun z : B => z.1.cells := primrec_tape_cells.comp Primrec.fst
  have hhead : Primrec fun z : B => z.1.head := primrec_tape_head.comp Primrec.fst
  have hleft : Primrec fun z : B => (⟨z.1.head - 1, z.1.cells⟩ : CodedTape) :=
    (Primrec.of_equiv_symm.comp (Primrec.pair
      (Primrec.nat_sub.comp hhead (Primrec.const 1)) hcells)).of_eq fun _ => rfl
  have hright : Primrec fun z : B => (⟨z.1.head + 1, z.1.cells⟩ : CodedTape) :=
    (Primrec.of_equiv_symm.comp (Primrec.pair
      (Primrec.succ.comp hhead) hcells)).of_eq fun _ => rfl
  refine (Primrec.cond (Primrec.beq.comp Primrec.snd (Primrec.const Dir3.left)) hleft
    (Primrec.cond (Primrec.beq.comp Primrec.snd (Primrec.const Dir3.right)) hright
      Primrec.fst)).of_eq ?_
  rintro ⟨t, d⟩
  cases d <;> rfl

set_option maxHeartbeats 1000000 in
theorem primrec_tape_writeAndMove :
    Primrec fun z : CodedTape × Γ × Dir3 => z.1.writeAndMove z.2.1 z.2.2 :=
  (primrec_tape_move.comp (Primrec.pair
    (primrec_tape_write.comp (Primrec.pair Primrec.fst
      (Primrec.fst.comp Primrec.snd)))
    (Primrec.snd.comp Primrec.snd))).of_eq fun _ => rfl

/-- Any function out of `Γw` is primitive recursive (three elements, fixed table). -/
theorem primrec_of_gammaW {σ : Type*} [Primcodable σ] (g : Γw → σ) (dflt : σ) :
    Primrec g :=
  ((Primrec.list_getD dflt).comp
      (Primrec.const [g .zero, g .one, g .blank]) Primrec.encode).of_eq fun x => by
    cases x <;> rfl

theorem primrec_toΓ : Primrec Γw.toΓ := primrec_of_gammaW Γw.toΓ Γ.blank

/-- Any function out of `Bool` is primitive recursive. -/
theorem primrec_of_bool {σ : Type*} [Primcodable σ] (g : Bool → σ) (dflt : σ) :
    Primrec g :=
  ((Primrec.list_getD dflt).comp
      (Primrec.const [g false, g true]) Primrec.encode).of_eq fun x => by
    cases x <;> rfl

/-! ### The executable step is primitive recursive

This is the statement FAF's `LIACompiler` consumes: the whole evaluator is primitive
recursive in the pair (description, configuration). -/

set_option maxHeartbeats 4000000 in
/-- **The executable step is primitive recursive.** -/
theorem primrec_codedStep :
    Primrec fun z : TMDesc × CodedCfg => codedStep z.1 z.2 := by
  set C := TMDesc × CodedCfg
  have hpow₂ : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) := Primrec₂.unpaired'.mp Nat.Primrec.pow
  have hd : Primrec fun z : C => z.1 := Primrec.fst
  have hcE : Primrec fun z : C => codedCfgEquiv z.2 :=
    (Primrec.of_equiv (e := codedCfgEquiv)).comp Primrec.snd
  have hstate : Primrec fun z : C => z.2.state :=
    (Primrec.fst.comp hcE).of_eq fun _ => rfl
  have hinp : Primrec fun z : C => z.2.input :=
    (Primrec.fst.comp (Primrec.snd.comp hcE)).of_eq fun _ => rfl
  have hwrk : Primrec fun z : C => z.2.work :=
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hcE))).of_eq fun _ => rfl
  have hotp : Primrec fun z : C => z.2.output :=
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hcE))).of_eq fun _ => rfl
  have hN : Primrec fun z : C => 2 ^ z.1.w :=
    hpow₂.comp (Primrec.const 2) (primrec_tmDesc_w.comp hd)
  have hq : Primrec fun z : C => min z.2.state (2 ^ z.1.w) :=
    Primrec.nat_min.comp hstate hN
  have hqh : Primrec fun z : C => min z.1.qhalt (2 ^ z.1.w) :=
    Primrec.nat_min.comp (primrec_tmDesc_qhalt.comp hd) hN
  have hsi : Primrec fun z : C => z.2.input.read := primrec_tape_read.comp hinp
  have hsw : Primrec fun z : C => z.2.work.read := primrec_tape_read.comp hwrk
  have hso : Primrec fun z : C => z.2.output.read := primrec_tape_read.comp hotp
  have ha : Primrec fun z : C => z.1.lookup (min z.2.state (2 ^ z.1.w))
      z.2.input.read z.2.work.read z.2.output.read :=
    primrec_lookup.comp (Primrec.pair hd
      (Primrec.pair hq (Primrec.pair hsi (Primrec.pair hsw hso))))
  -- the three sanitized head directions
  have hdI : Primrec fun z : C => if z.2.input.read = Γ.start then Dir3.right
      else (z.1.lookup (min z.2.state (2 ^ z.1.w))
        z.2.input.read z.2.work.read z.2.output.read).di :=
    Primrec.ite (Primrec.eq.comp hsi (Primrec.const Γ.start))
      (Primrec.const Dir3.right) (primrec_descAct_di.comp ha)
  have hdW : Primrec fun z : C => if z.2.work.read = Γ.start then Dir3.right
      else (z.1.lookup (min z.2.state (2 ^ z.1.w))
        z.2.input.read z.2.work.read z.2.output.read).dw :=
    Primrec.ite (Primrec.eq.comp hsw (Primrec.const Γ.start))
      (Primrec.const Dir3.right) (primrec_descAct_dw.comp ha)
  have hdO : Primrec fun z : C => if z.2.output.read = Γ.start then Dir3.right
      else (z.1.lookup (min z.2.state (2 ^ z.1.w))
        z.2.input.read z.2.work.read z.2.output.read).dOut :=
    Primrec.ite (Primrec.eq.comp hso (Primrec.const Γ.start))
      (Primrec.const Dir3.right) (primrec_descAct_dOut.comp ha)
  -- the three updated tapes
  have hInp' := primrec_tape_move.comp (Primrec.pair hinp hdI)
  have hWrk' := primrec_tape_writeAndMove.comp (Primrec.pair hwrk
    (Primrec.pair (primrec_toΓ.comp (primrec_descAct_ww.comp ha)) hdW))
  have hOtp' := primrec_tape_writeAndMove.comp (Primrec.pair hotp
    (Primrec.pair (primrec_toΓ.comp (primrec_descAct_wo.comp ha)) hdO))
  refine (Primrec.ite (Primrec.eq.comp hq hqh)
    (Primrec.const (none : Option CodedCfg))
    (Primrec.option_some.comp (Primrec.of_equiv_symm.comp (Primrec.pair
      (Primrec.nat_min.comp (primrec_descAct_q'.comp ha) hN)
      (Primrec.pair hInp' (Primrec.pair hWrk' hOtp')))))).of_eq ?_
  intro z
  rw [codedStep]
  split <;> rfl

/-! ### The bounded run is primitive recursive

`runCoded` is the shape FAF's `LIACompiler` needs: a total, clock-bounded evaluator,
primitive recursive in (description, clock, initial configuration). -/

/-- One step lifted to the `Option` monad, so the bounded run is a plain iteration. -/
def stepOpt (d : TMDesc) (o : Option CodedCfg) : Option CodedCfg :=
  o.bind (codedStep d)

theorem iterate_stepOpt_none (d : TMDesc) : ∀ t, (stepOpt d)^[t] none = none
  | 0 => rfl
  | (t + 1) => by
      rw [Function.iterate_succ_apply]
      simpa [stepOpt] using iterate_stepOpt_none d t

theorem runCoded_eq_iterate (d : TMDesc) :
    ∀ (t : ℕ) (c : CodedCfg), runCoded d t c = (stepOpt d)^[t] (some c)
  | 0, c => rfl
  | (t + 1), c => by
      rw [runCoded, Function.iterate_succ_apply]
      have hs : stepOpt d (some c) = codedStep d c := rfl
      rw [hs]
      cases h : codedStep d c with
      | none => simp [iterate_stepOpt_none]
      | some c₁ => simpa [h] using runCoded_eq_iterate d t c₁

set_option maxHeartbeats 4000000 in
theorem primrec_stepOpt : Primrec fun z : TMDesc × Option CodedCfg => stepOpt z.1 z.2 :=
  Primrec.option_bind Primrec.snd
    (Primrec.to₂ (primrec_codedStep.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)))

set_option maxHeartbeats 4000000 in
/-- **The bounded executable run is primitive recursive.** -/
theorem primrec_runCoded :
    Primrec fun z : TMDesc × ℕ × CodedCfg => runCoded z.1 z.2.1 z.2.2 := by
  refine (Primrec.nat_iterate (Primrec.fst.comp Primrec.snd)
    (Primrec.option_some.comp (Primrec.snd.comp Primrec.snd))
    (Primrec.to₂ (primrec_stepOpt.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)))).of_eq ?_
  rintro ⟨d, t, c⟩
  exact (runCoded_eq_iterate d t c).symm

/-! ### The initial configuration

The coded initial configuration decodes to the real one, so the vertical slice runs from
a genuine input word, not from an arbitrary configuration. -/

/-- The coded initial configuration of the machine described by `d` on input `x`. -/
def initCoded (d : TMDesc) (x : List Bool) : CodedCfg where
  state := d.qstart % 2 ^ d.w
  input := ⟨0, x.map Γ.ofBool⟩
  work := ⟨0, []⟩
  output := ⟨0, []⟩

theorem decode_initCoded (d : TMDesc) (x : List Bool) :
    CodedCfg.decode d (initCoded d x) = (d.toTM).initCfg x := by
  have hlt : d.qstart % 2 ^ d.w < 2 ^ d.w := Nat.mod_lt _ (Nat.two_pow_pos _)
  refine Cfg.ext (Fin.ext ?_) rfl rfl rfl
  show min (d.qstart % 2 ^ d.w) (2 ^ d.w) = d.qstart % 2 ^ d.w
  omega

set_option maxHeartbeats 1000000 in
theorem primrec_initCoded :
    Primrec fun z : TMDesc × List Bool => initCoded z.1 z.2 := by
  have hw : Primrec fun z : TMDesc × List Bool => 2 ^ z.1.w :=
    (Primrec₂.unpaired'.mp Nat.Primrec.pow).comp (Primrec.const 2)
      (primrec_tmDesc_w.comp Primrec.fst)
  have hqs : Primrec fun z : TMDesc × List Bool => z.1.qstart :=
    ((Primrec.fst.comp (Primrec.snd.comp
      (Primrec.of_equiv (e := tmDescEquiv)))).comp Primrec.fst).of_eq fun _ => rfl
  have hinp : Primrec fun z : TMDesc × List Bool =>
      (⟨0, z.2.map Γ.ofBool⟩ : CodedTape) :=
    (Primrec.of_equiv_symm.comp (Primrec.pair (Primrec.const 0)
      (Primrec.list_map Primrec.snd
        (Primrec.to₂ (primrec_of_bool Γ.ofBool Γ.blank |>.comp Primrec.snd))))).of_eq
      fun _ => rfl
  exact (Primrec.of_equiv_symm.comp (Primrec.pair
    (Primrec.nat_mod.comp hqs hw)
    (Primrec.pair hinp (Primrec.pair (Primrec.const ⟨0, []⟩)
      (Primrec.const ⟨0, []⟩))))).of_eq fun _ => rfl

/-- **The end-to-end bounded evaluator**: from a description and an input word, run the
described machine for `t` steps, entirely on finite data. -/
def evalCoded (d : TMDesc) (t : ℕ) (x : List Bool) : Option CodedCfg :=
  runCoded d t (initCoded d x)

/-- The bounded evaluator tracks the real machine: if it returns a configuration, the
described machine reaches its decoding from the genuine initial configuration in exactly
`t` steps. -/
theorem evalCoded_reachesIn (d : TMDesc) (t : ℕ) (x : List Bool) {c : CodedCfg}
    (h : evalCoded d t x = some c) :
    (d.toTM).reachesIn t ((d.toTM).initCfg x) (CodedCfg.decode d c) := by
  have := runCoded_eq d t (initCoded d x) c h
  rwa [decode_initCoded] at this

set_option maxHeartbeats 4000000 in
/-- **The end-to-end bounded evaluator is primitive recursive.** -/
theorem primrec_evalCoded :
    Primrec fun z : TMDesc × ℕ × List Bool => evalCoded z.1 z.2.1 z.2.2 :=
  (primrec_runCoded.comp (Primrec.pair Primrec.fst
    (Primrec.pair (Primrec.fst.comp Primrec.snd)
      (primrec_initCoded.comp (Primrec.pair Primrec.fst
        (Primrec.snd.comp Primrec.snd)))))).of_eq fun _ => rfl

end LogicalInduction.MachineExec

