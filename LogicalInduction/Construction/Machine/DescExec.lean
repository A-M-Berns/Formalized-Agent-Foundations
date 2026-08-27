/-
# Executable bounded execution of `complexitylib` machine descriptions

The **FAF-specific executable bridge** from finite `complexitylib` machine descriptions to
primitive-recursive bounded execution. The complexity theory it stands on — the machine
model, its time measure, `FP`, and the correctness of the description interpreter — is
upstream, in the pinned `complexitylib` compatibility fork (see `lakefile.lean`).

**Why descriptions, and not machines.** `LogicalInduction/Construction/LIACompiler.lean`
needs the trader enumeration to be *primitive recursive*, while a `Complexity.TM k` carries
its state type as a bundled `Q : Type` and its tapes as functions `ℕ → Γ`, neither of which
`Primrec` can see. The resolution is that the enumeration is indexed by **descriptions**,
and an interpreted description

```
Complexity.TMDesc.toTM d : TM 1     with  Q := Fin (2 ^ d.w + 1)
                                    and   δ  := d.lookup, a `List.find?` over `d.entries`
```

is already first-order finite data. So neither an arbitrary `TM k` nor the combinator-built
universal machine `utmTM` has to be executed — only `TMDesc.toTM`, uniformly in `d`, which
is what the enumeration ranges over anyway.

**What this file provides.**

* A finite coding of tapes and configurations, `CodedTape` / `CodedCfg`, whose decode map is
  definitionally the cell function of upstream's own `Tape.init`: a finite window with
  blanks understood outside it. No head-motion or reachable-region bound is needed — the
  window grows with the write.
* `codedStep_eq`, `runCoded_eq`, `decode_initCoded`, `evalCoded_reachesIn` — the simulation
  lemmas: executable steps on finite data are steps of the real machine, from a real input.
* Explicit `Primcodable` instances (`Γ`, `Γw`, `Dir3`, `DescAct`, `DescEntry`, `TMDesc`,
  `CodedTape`, `CodedCfg`) and `primrec_codedStep`, `primrec_runCoded`, `primrec_evalCoded`.
* `codedOutput` and `hasOutput_codedOutput` — finite output-word extraction, proved equal to
  upstream's `Tape.HasOutput` convention rather than merely length-bounded.
* `machineTokens` and `primrec_machineTokens` — the compiler-facing bounded total evaluator,
  and the one obligation `LIACompiler` consumes.

**Three layers, deliberately kept apart.** Nothing in this file proves anything about
polynomial time. Executability (`Primrec`), polynomial-time soundness of each indexed
computation, and coverage of every polynomial-time trader are three different facts; making
the primitive-recursive evaluator carry the complexity proof is the conflation to avoid.
`machineTokens_steps_le` below is the *step-count* fact this layer can honestly supply; the
`FP` statement belongs with the complexity layer.

**Elaboration hazard — read before extending this file.** `descAt` routes through
`Encodable.decode` at `TMDesc`, whose `Primcodable` instance is a stack of
`Primcodable.ofEquiv`s down to `Fin 4`. *Any* `rfl`/`whnf` obligation that lets the
elaborator unfold it descends into that stack and does not return: five builds of this
module died on `whnf` timeouts at 200k, 1M, 2M, 4M and 8M heartbeats before the cause was
identified. **Raising the heartbeat limit is not the fix.** The discipline that works, and
that the code below follows throughout, is:

* `descAt` is sealed `attribute [irreducible]` immediately after its `Primrec` lemma;
* index fields are plain functions (`progDesc`, `progCoeff`, `progDeg`, `progClock`), not
  projections out of a structure, so nothing has to reduce to read them;
* the `Option` fallback is factored into `tokensOf : Option CodedCfg → List ℕ`, so
  `Primrec.option_casesOn` unifies at that small domain rather than at `ℕ × ℕ`;
* every `Primrec` lemma is a bare `.comp` whose underlying function is *syntactically* the
  definition it characterises, so no `of_eq` defeq check is ever performed at a type
  carrying the coding stack.

Keep all four when adding declarations here.

**Not a paper node.** Nothing here renders anything in arXiv:1609.03543, and no strength
claim in the repository changes because of it. Declarations use `lemma`, not `theorem`, for
that reason (`scripts/lint_paper_labels.py`).
-/
import Complexitylib.Models.TuringMachine.UTM.Internal.Interp
import Complexitylib.Classes.P.Description
import Mathlib.Computability.Primrec.List
import LogicalInduction.Framework.Criterion

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

lemma decode_cells_succ (t : CodedTape) (i : ℕ) :
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
lemma getElem?_setAt (l : List Γ) (i j : ℕ) (s : Γ) :
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

lemma decode_move (t : CodedTape) (d : Dir3) :
    (t.move d).decode = t.decode.move d := by
  cases d <;> rfl

lemma decode_write (t : CodedTape) (s : Γ) :
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

lemma decode_writeAndMove (t : CodedTape) (s : Γ) (d : Dir3) :
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
lemma codedStep_eq (d : TMDesc) (c : CodedCfg) :
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
lemma runCoded_eq (d : TMDesc) :
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
lemma primrec_descAct_q' : Primrec DescAct.q' :=
  (Primrec.fst.comp (Primrec.of_equiv (e := descActEquiv))).of_eq fun _ => rfl

open Primrec in
lemma primrec_descAct_ww : Primrec DescAct.ww :=
  ((Primrec.fst.comp Primrec.snd).comp (Primrec.of_equiv (e := descActEquiv))).of_eq
    fun _ => rfl

open Primrec in
lemma primrec_descAct_wo : Primrec DescAct.wo :=
  ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).comp
    (Primrec.of_equiv (e := descActEquiv))).of_eq fun _ => rfl

open Primrec in
lemma primrec_descAct_di : Primrec DescAct.di :=
  ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).comp
    (Primrec.of_equiv (e := descActEquiv))).of_eq fun _ => rfl

open Primrec in
lemma primrec_descAct_dw : Primrec DescAct.dw :=
  ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))).comp
    (Primrec.of_equiv (e := descActEquiv))).of_eq fun _ => rfl

open Primrec in
lemma primrec_descAct_dOut : Primrec DescAct.dOut :=
  ((Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))).comp
    (Primrec.of_equiv (e := descActEquiv))).of_eq fun _ => rfl

open Primrec in
lemma primrec_descEntry_act : Primrec DescEntry.act :=
  ((Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).comp
    (Primrec.of_equiv (e := descEntryEquiv))).of_eq fun _ => rfl

open Primrec in
lemma primrec_tmDesc_w : Primrec TMDesc.w :=
  (Primrec.fst.comp (Primrec.of_equiv (e := tmDescEquiv))).of_eq fun _ => rfl

open Primrec in
lemma primrec_tmDesc_qhalt : Primrec TMDesc.qhalt :=
  ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).comp
    (Primrec.of_equiv (e := tmDescEquiv))).of_eq fun _ => rfl

open Primrec in
lemma primrec_tmDesc_entries : Primrec TMDesc.entries :=
  ((Primrec.snd.comp (Primrec.snd.comp Primrec.snd)).comp
    (Primrec.of_equiv (e := tmDescEquiv))).of_eq fun _ => rfl

/-! ### `List.find?` is primitive recursive

Mathlib supplies `Primrec.list_findIdx` and `Primrec.list_getElem?`; `find?` is their
composite, because `findIdx` returns the list length when nothing matches and
`getElem?` returns `none` there. -/

lemma list_find?_eq_getElem? {β : Type*} (p : β → Bool) :
    ∀ l : List β, l.find? p = l[l.findIdx p]?
  | [] => rfl
  | a :: l => by
      by_cases h : p a
      · simp [List.findIdx_cons, h]
      · simp [List.findIdx_cons, h, list_find?_eq_getElem? p l]

open Primrec in
lemma primrec_list_find? {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → List β} {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec fun a => (f a).find? (p a) :=
  ((Primrec.list_getElem?.comp hf (Primrec.list_findIdx hf hp))).of_eq fun a =>
    (list_find?_eq_getElem? (p a) (f a)).symm

/-! ### The transition table lookup is primitive recursive -/

/-- Any function out of `Γ` is primitive recursive: `Γ` has four elements, so the
function is a fixed finite lookup table indexed by the code of its argument. -/
lemma primrec_of_gamma {σ : Type*} [Primcodable σ] (g : Γ → σ) (dflt : σ) :
    Primrec g :=
  ((Primrec.list_getD dflt).comp
      (Primrec.const [g .zero, g .one, g .blank, g .start])
      Primrec.encode).of_eq fun x => by cases x <;> rfl

lemma primrec_readback : Primrec TMDesc.readback :=
  primrec_of_gamma TMDesc.readback Γw.blank

set_option maxHeartbeats 1000000 in
/-- The default action taken when no table row matches. -/
lemma primrec_defaultAct :
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
lemma primrec_entryMatches :
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
lemma primrec_lookup :
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
lemma primrec_tape_head : Primrec CodedTape.head :=
  (Primrec.fst.comp (Primrec.of_equiv (e := codedTapeEquiv))).of_eq fun _ => rfl

open Primrec in
lemma primrec_tape_cells : Primrec CodedTape.cells :=
  (Primrec.snd.comp (Primrec.of_equiv (e := codedTapeEquiv))).of_eq fun _ => rfl

set_option maxHeartbeats 1000000 in
lemma primrec_tape_read : Primrec CodedTape.read :=
  (Primrec.ite (Primrec.eq.comp primrec_tape_head (Primrec.const 0))
    (Primrec.const Γ.start)
    (Primrec.option_getD.comp
      (Primrec.list_getElem?.comp primrec_tape_cells
        (Primrec.nat_sub.comp primrec_tape_head (Primrec.const 1)))
      (Primrec.const Γ.blank))).of_eq fun _ => rfl

set_option maxHeartbeats 1000000 in
lemma primrec_setAt :
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
lemma primrec_tape_write : Primrec fun z : CodedTape × Γ => z.1.write z.2 := by
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
lemma primrec_tape_move : Primrec fun z : CodedTape × Dir3 => z.1.move z.2 := by
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
lemma primrec_tape_writeAndMove :
    Primrec fun z : CodedTape × Γ × Dir3 => z.1.writeAndMove z.2.1 z.2.2 :=
  (primrec_tape_move.comp (Primrec.pair
    (primrec_tape_write.comp (Primrec.pair Primrec.fst
      (Primrec.fst.comp Primrec.snd)))
    (Primrec.snd.comp Primrec.snd))).of_eq fun _ => rfl

/-- Any function out of `Γw` is primitive recursive (three elements, fixed table). -/
lemma primrec_of_gammaW {σ : Type*} [Primcodable σ] (g : Γw → σ) (dflt : σ) :
    Primrec g :=
  ((Primrec.list_getD dflt).comp
      (Primrec.const [g .zero, g .one, g .blank]) Primrec.encode).of_eq fun x => by
    cases x <;> rfl

lemma primrec_toΓ : Primrec Γw.toΓ := primrec_of_gammaW Γw.toΓ Γ.blank

/-- Any function out of `Bool` is primitive recursive. -/
lemma primrec_of_bool {σ : Type*} [Primcodable σ] (g : Bool → σ) (dflt : σ) :
    Primrec g :=
  ((Primrec.list_getD dflt).comp
      (Primrec.const [g false, g true]) Primrec.encode).of_eq fun x => by
    cases x <;> rfl

/-! ### The executable step is primitive recursive

This is the statement FAF's `LIACompiler` consumes: the whole evaluator is primitive
recursive in the pair (description, configuration). -/

set_option maxHeartbeats 4000000 in
/-- **The executable step is primitive recursive.** -/
lemma primrec_codedStep :
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

lemma iterate_stepOpt_none (d : TMDesc) : ∀ t, (stepOpt d)^[t] none = none
  | 0 => rfl
  | (t + 1) => by
      rw [Function.iterate_succ_apply]
      simpa [stepOpt] using iterate_stepOpt_none d t

lemma runCoded_eq_iterate (d : TMDesc) :
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
lemma primrec_stepOpt : Primrec fun z : TMDesc × Option CodedCfg => stepOpt z.1 z.2 :=
  Primrec.option_bind Primrec.snd
    (Primrec.to₂ (primrec_codedStep.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)))

set_option maxHeartbeats 4000000 in
/-- **The bounded executable run is primitive recursive.** -/
lemma primrec_runCoded :
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

lemma decode_initCoded (d : TMDesc) (x : List Bool) :
    CodedCfg.decode d (initCoded d x) = (d.toTM).initCfg x := by
  have hlt : d.qstart % 2 ^ d.w < 2 ^ d.w := Nat.mod_lt _ (Nat.two_pow_pos _)
  refine Cfg.ext (Fin.ext ?_) rfl rfl rfl
  show min (d.qstart % 2 ^ d.w) (2 ^ d.w) = d.qstart % 2 ^ d.w
  omega

set_option maxHeartbeats 1000000 in
lemma primrec_initCoded :
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
lemma evalCoded_reachesIn (d : TMDesc) (t : ℕ) (x : List Bool) {c : CodedCfg}
    (h : evalCoded d t x = some c) :
    (d.toTM).reachesIn t ((d.toTM).initCfg x) (CodedCfg.decode d c) := by
  have := runCoded_eq d t (initCoded d x) c h
  rwa [decode_initCoded] at this

set_option maxHeartbeats 4000000 in
/-- **The end-to-end bounded evaluator is primitive recursive.** -/
lemma primrec_evalCoded :
    Primrec fun z : TMDesc × ℕ × List Bool => evalCoded z.1 z.2.1 z.2.2 :=
  (primrec_runCoded.comp (Primrec.pair Primrec.fst
    (Primrec.pair (Primrec.fst.comp Primrec.snd)
      (primrec_initCoded.comp (Primrec.pair Primrec.fst
        (Primrec.snd.comp Primrec.snd)))))).of_eq fun _ => rfl

/-! ## Finite output extraction

A halted configuration's output tape holds the machine's output word in cells
`1 … m`, terminated by the first blank (upstream's `Tape.HasOutput`). On the coded side
that is a `takeWhile` on the finite cell list — provided no cell holds the left-end marker
`Γ.start`, which is exactly what the writable alphabet `Γw` guarantees and what the
invariant below tracks. -/

/-- The left-end marker occurs nowhere in a coded tape's window. Upstream's `δ` writes only
`Γw`, which excludes `Γ.start`, so this is preserved by every step and holds initially. -/
def CodedTape.NoStart (t : CodedTape) : Prop := ∀ g ∈ t.cells, g ≠ Γ.start

lemma CodedTape.noStart_nil (h : ℕ) : CodedTape.NoStart ⟨h, []⟩ := by
  intro g hg; cases hg

lemma CodedTape.NoStart.setAt {l : List Γ} (hl : ∀ g ∈ l, g ≠ Γ.start) (i : ℕ) {s : Γ}
    (hs : s ≠ Γ.start) : ∀ g ∈ CodedTape.setAt l i s, g ≠ Γ.start := by
  intro g hg
  rw [CodedTape.setAt, List.mem_map] at hg
  obtain ⟨j, -, rfl⟩ := hg
  by_cases hj : j = i
  · rw [if_pos hj]; exact hs
  · rw [if_neg hj]
    cases hlj : l[j]? with
    | none => simp
    | some a => simpa using hl a (List.mem_of_getElem? hlj)

lemma CodedTape.NoStart.write {t : CodedTape} (ht : t.NoStart) {s : Γ}
    (hs : s ≠ Γ.start) : (t.write s).NoStart := by
  rw [CodedTape.write]
  split
  · exact ht
  · exact CodedTape.NoStart.setAt ht _ hs

lemma CodedTape.NoStart.move {t : CodedTape} (ht : t.NoStart) (d : Dir3) :
    (t.move d).NoStart := by
  cases d <;> exact ht

lemma CodedTape.NoStart.writeAndMove {t : CodedTape} (ht : t.NoStart) {s : Γ}
    (hs : s ≠ Γ.start) (d : Dir3) : (t.writeAndMove s d).NoStart :=
  (ht.write hs).move d

/-- The index of the first blank in a coded tape's window — its length if there is none.
This is the frontier upstream's `Tape.HasOutput` is stated against. -/
def CodedTape.frontier (t : CodedTape) : ℕ := t.cells.findIdx fun g => g == Γ.blank

/-- The output word held by a coded tape: its window up to the first blank, read as bits.

Written as a `range`/`map` rather than a `takeWhile` so that it is directly primitive
recursive, the same device used for `setAt`. -/
def CodedTape.outputWord (t : CodedTape) : List Bool :=
  (List.range t.frontier).map fun j => decide ((t.cells[j]?).getD Γ.blank = Γ.one)

@[simp] lemma CodedTape.length_outputWord (t : CodedTape) :
    t.outputWord.length = t.frontier := by simp [CodedTape.outputWord]

/-- **Extraction is correct.** The decoded tape has exactly `outputWord` as its output in
upstream's sense: cells `1 … n` carry its bits and cell `n + 1` is blank. This is an
equality against `Tape.HasOutput`, not a length bound. -/
lemma CodedTape.hasOutput_outputWord {t : CodedTape} (ht : t.NoStart) :
    t.decode.HasOutput t.outputWord := by
  have hle : t.frontier ≤ t.cells.length := List.findIdx_le_length
  constructor
  · intro i hi
    rw [CodedTape.length_outputWord] at hi
    have hilt : i < t.cells.length := lt_of_lt_of_le hi hle
    have hget : t.cells[i]? = some (t.cells[i]'hilt) := List.getElem?_eq_getElem hilt
    have hnb : (t.cells[i]'hilt) ≠ Γ.blank := by
      intro hc
      have h := List.not_of_lt_findIdx (p := fun g => g == Γ.blank)
        (show i < t.cells.findIdx (fun g => g == Γ.blank) from hi)
      simp only [beq_eq_false_iff_ne, ne_eq] at h
      exact h hc
    have hns : (t.cells[i]'hilt) ≠ Γ.start := ht _ (List.getElem_mem hilt)
    have hcell : t.decode.cells (i + 1) = t.cells[i]'hilt := by
      rw [CodedTape.decode_cells_succ, hget]; rfl
    have hword : t.outputWord[i]'(by simpa using hi)
        = decide ((t.cells[i]'hilt) = Γ.one) := by
      simp only [CodedTape.outputWord, List.getElem_map, List.getElem_range, hget]
      rfl
    rw [hcell, hword]
    cases hg : t.cells[i]'hilt <;> simp_all [Γ.ofBool]
  · rw [CodedTape.length_outputWord, CodedTape.decode_cells_succ]
    rcases lt_or_ge t.frontier t.cells.length with hlt | hge
    · have hb : (t.cells[t.frontier]'hlt) = Γ.blank := by
        have h := List.findIdx_getElem (p := fun g => g == Γ.blank) (w := hlt)
        simp only [beq_iff_eq] at h
        exact h
      rw [List.getElem?_eq_getElem hlt, hb]; rfl
    · rw [List.getElem?_eq_none hge]; rfl

/-- The output word of a coded configuration. -/
def codedOutput (c : CodedCfg) : List Bool := c.output.outputWord

lemma primrec_frontier : Primrec CodedTape.frontier :=
  Primrec.list_findIdx primrec_tape_cells
    (Primrec.to₂ (Primrec.beq.comp Primrec.snd (Primrec.const Γ.blank)))

set_option maxHeartbeats 1000000 in
lemma primrec_outputWord : Primrec CodedTape.outputWord :=
  Primrec.list_map (Primrec.list_range.comp primrec_frontier)
    (Primrec.to₂ (Primrec.beq.comp
      (Primrec.option_getD.comp
        (Primrec.list_getElem?.comp (primrec_tape_cells.comp Primrec.fst) Primrec.snd)
        (Primrec.const Γ.blank))
      (Primrec.const Γ.one)))

set_option maxHeartbeats 1000000 in
/-- Output extraction is primitive recursive. -/
lemma primrec_codedOutput : Primrec codedOutput := by
  have hout : Primrec fun c : CodedCfg => c.output :=
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.of_equiv (e := codedCfgEquiv))))).of_eq fun _ => rfl
  exact primrec_outputWord.comp hout

/-! ## Running to a halt within a budget

`runCoded` iterates a fixed number of steps and fails when the machine halts early. What a
clocked evaluator needs is the opposite: run *until* the machine halts, giving up when the
budget is exhausted. The frozen-pair form below is that, written as a plain iteration so it
is primitive recursive by `Primrec.nat_iterate`. -/

/-- One step of the budgeted run: a configuration paired with "has already halted". -/
def stepFrozen (d : TMDesc) (s : CodedCfg × Bool) : CodedCfg × Bool :=
  if s.2 then s else
    match codedStep d s.1 with
    | none => (s.1, true)
    | some c' => (c', false)

/-- Run the described machine until it halts, giving up after `t` steps. -/
def runUntilHalt (d : TMDesc) (t : ℕ) (c : CodedCfg) : Option CodedCfg :=
  let r := (stepFrozen d)^[t] (c, false)
  if r.2 then some r.1 else none

/-- **The end-to-end budgeted evaluator**: from a description and an input word, run to a
halt within `t` steps. Total: `none` means "did not halt in budget". -/
def evalHalted (d : TMDesc) (t : ℕ) (x : List Bool) : Option CodedCfg :=
  runUntilHalt d t (initCoded d x)

lemma stepFrozen_frozen (d : TMDesc) (c : CodedCfg) :
    ∀ t, (stepFrozen d)^[t] (c, true) = (c, true)
  | 0 => rfl
  | (t + 1) => by
      rw [Function.iterate_succ_apply]
      simpa [stepFrozen] using stepFrozen_frozen d c t

/-- A coded step reports `none` exactly when the decoded machine has halted. -/
lemma halted_of_codedStep_none {d : TMDesc} {c : CodedCfg} (h : codedStep d c = none) :
    (d.toTM).halted (CodedCfg.decode d c) := by
  have h2 := codedStep_eq d c
  rw [h, Option.map_none] at h2
  by_contra hne
  rw [TM.step, if_neg hne] at h2
  simp at h2

/-- **Budgeted execution is faithful.** If the evaluator reports a halted configuration, the
real machine reaches its decoding, in at most the budgeted number of steps, and has genuinely
halted there. The step bound `s ≤ t` is the fact the polynomial-soundness argument uses. -/
lemma runUntilHalt_spec (d : TMDesc) :
    ∀ (t : ℕ) (c c' : CodedCfg), runUntilHalt d t c = some c' →
      ∃ s < t, (d.toTM).reachesIn s (CodedCfg.decode d c) (CodedCfg.decode d c') ∧
        (d.toTM).halted (CodedCfg.decode d c')
  | 0, c, c', h => by
      rw [runUntilHalt] at h; simp at h
  | (t + 1), c, c', h => by
      rw [runUntilHalt, Function.iterate_succ_apply] at h
      have hsf : stepFrozen d (c, false)
          = (match codedStep d c with
             | none => (c, true)
             | some c₁ => (c₁, false)) := by
        rw [stepFrozen]; rfl
      rw [hsf] at h
      cases hs : codedStep d c with
      | none =>
          rw [hs] at h
          simp only [stepFrozen_frozen, if_pos, Option.some.injEq] at h
          subst h
          exact ⟨0, Nat.succ_pos t, .zero, halted_of_codedStep_none hs⟩
      | some c₁ =>
          rw [hs] at h
          obtain ⟨s, hst, hreach, hhalt⟩ :=
            runUntilHalt_spec d t c₁ c' (by rw [runUntilHalt]; exact h)
          refine ⟨s + 1, by omega, .step ?_ hreach, hhalt⟩
          have h2 := codedStep_eq d c
          rw [hs, Option.map_some] at h2
          exact h2.symm

set_option maxHeartbeats 1000000 in
lemma primrec_stepFrozen :
    Primrec fun z : TMDesc × CodedCfg × Bool => stepFrozen z.1 z.2 := by
  have hc : Primrec fun z : TMDesc × CodedCfg × Bool => z.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hb : Primrec fun z : TMDesc × CodedCfg × Bool => z.2.2 :=
    Primrec.snd.comp Primrec.snd
  have hstep : Primrec fun z : TMDesc × CodedCfg × Bool => codedStep z.1 z.2.1 :=
    primrec_codedStep.comp (Primrec.pair Primrec.fst hc)
  refine (Primrec.cond hb Primrec.snd
    (Primrec.option_casesOn hstep (Primrec.pair hc (Primrec.const true))
      (Primrec.to₂ (Primrec.pair Primrec.snd (Primrec.const false))))).of_eq ?_
  rintro ⟨d, c, b⟩
  cases b
  · rw [stepFrozen]
    cases codedStep d c <;> rfl
  · rw [stepFrozen]
    rfl

set_option maxHeartbeats 4000000 in
/-- The budgeted run is primitive recursive. -/
lemma primrec_runUntilHalt :
    Primrec fun z : TMDesc × ℕ × CodedCfg => runUntilHalt z.1 z.2.1 z.2.2 := by
  have hiter : Primrec fun z : TMDesc × ℕ × CodedCfg =>
      (stepFrozen z.1)^[z.2.1] (z.2.2, false) :=
    Primrec.nat_iterate (Primrec.fst.comp Primrec.snd)
      (Primrec.pair (Primrec.snd.comp Primrec.snd) (Primrec.const false))
      (Primrec.to₂ (primrec_stepFrozen.comp
        (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)))
  refine (Primrec.ite (Primrec.eq.comp (Primrec.snd.comp hiter) (Primrec.const true))
    (Primrec.option_some.comp (Primrec.fst.comp hiter))
    (Primrec.const none)).of_eq ?_
  rintro ⟨d, t, c⟩
  rw [runUntilHalt]

set_option maxHeartbeats 4000000 in
lemma primrec_evalHalted :
    Primrec fun z : TMDesc × ℕ × List Bool => evalHalted z.1 z.2.1 z.2.2 :=
  (primrec_runUntilHalt.comp (Primrec.pair Primrec.fst
    (Primrec.pair (Primrec.fst.comp Primrec.snd)
      (primrec_initCoded.comp (Primrec.pair Primrec.fst
        (Primrec.snd.comp Primrec.snd)))))).of_eq fun _ => rfl

/-! ## Two invariants of the output tape

Both are needed to turn a successful budgeted run into a usable token stream: the
`NoStart` invariant makes extraction correct, and the size invariant is what bounds the
output word by the clock. -/

/-- The output tape's window never acquires the left-end marker: `δ` writes only `Γw`. -/
lemma codedStep_output_noStart {d : TMDesc} {c c' : CodedCfg}
    (hns : c.output.NoStart) (h : codedStep d c = some c') : c'.output.NoStart := by
  rw [codedStep] at h
  split at h
  · exact absurd h (by simp)
  · rw [Option.some.injEq] at h
    subst h
    exact hns.writeAndMove (Γw.toΓ_ne_start _) _

/-- Head position and window length after `k` steps are both at most `k`. Each step moves
the head by at most one and extends the window only as far as the head. -/
def CodedTape.Bounded (t : CodedTape) (k : ℕ) : Prop :=
  t.head ≤ k ∧ t.cells.length ≤ k

lemma CodedTape.bounded_nil : CodedTape.Bounded ⟨0, []⟩ 0 := ⟨le_rfl, le_rfl⟩

lemma CodedTape.Bounded.mono {t : CodedTape} {k k' : ℕ} (h : t.Bounded k) (hk : k ≤ k') :
    t.Bounded k' := ⟨h.1.trans hk, h.2.trans hk⟩

lemma CodedTape.Bounded.writeAndMove {t : CodedTape} {k : ℕ} (h : t.Bounded k) (s : Γ)
    (d : Dir3) : (t.writeAndMove s d).Bounded (k + 1) := by
  obtain ⟨hh, hl⟩ := h
  have hw : (t.write s).head = t.head ∧
      (t.write s).cells.length ≤ max t.cells.length t.head := by
    rw [CodedTape.write]
    split
    · exact ⟨rfl, le_max_left _ _⟩
    · refine ⟨rfl, ?_⟩
      simp only [CodedTape.setAt, List.length_map, List.length_range]
      omega
  refine ⟨?_, ?_⟩
  · rw [CodedTape.writeAndMove]
    cases d <;> simp only [CodedTape.move, hw.1] <;> omega
  · rw [CodedTape.writeAndMove]
    cases d <;> simp only [CodedTape.move] <;> (have := hw.2; omega)

lemma codedStep_output_bounded {d : TMDesc} {c c' : CodedCfg} {k : ℕ}
    (hb : c.output.Bounded k) (h : codedStep d c = some c') :
    c'.output.Bounded (k + 1) := by
  rw [codedStep] at h
  split at h
  · exact absurd h (by simp)
  · rw [Option.some.injEq] at h
    subst h
    exact hb.writeAndMove _ _

/-- Both invariants, carried through a budgeted run. -/
lemma runUntilHalt_output_invariants (d : TMDesc) :
    ∀ (t : ℕ) (c c' : CodedCfg), runUntilHalt d t c = some c' →
      ∀ k, c.output.NoStart → c.output.Bounded k →
        c'.output.NoStart ∧ c'.output.Bounded (k + t)
  | 0, c, c', h => by rw [runUntilHalt] at h; simp at h
  | (t + 1), c, c', h => by
      intro k hns hb
      rw [runUntilHalt, Function.iterate_succ_apply] at h
      have hsf : stepFrozen d (c, false)
          = (match codedStep d c with
             | none => (c, true)
             | some c₁ => (c₁, false)) := by
        rw [stepFrozen]; rfl
      rw [hsf] at h
      cases hs : codedStep d c with
      | none =>
          rw [hs] at h
          simp only [stepFrozen_frozen, if_pos, Option.some.injEq] at h
          subst h
          exact ⟨hns, hb.mono (by omega)⟩
      | some c₁ =>
          rw [hs] at h
          obtain ⟨h1, h2⟩ := runUntilHalt_output_invariants d t c₁ c'
            (by rw [runUntilHalt]; exact h) (k + 1)
            (codedStep_output_noStart hns hs) (codedStep_output_bounded hb hs)
          exact ⟨h1, h2.mono (by omega)⟩

lemma evalHalted_output_invariants {d : TMDesc} {t : ℕ} {x : List Bool} {c : CodedCfg}
    (h : evalHalted d t x = some c) : c.output.NoStart ∧ c.output.Bounded t := by
  obtain ⟨h1, h2⟩ := runUntilHalt_output_invariants d t _ c h 0
    (CodedTape.noStart_nil 0) CodedTape.bounded_nil
  exact ⟨h1, h2.mono (by omega)⟩

/-- **The bounded run's output is bounded by the clock.** One executable step writes at most
one cell, so the extracted word is no longer than the budget. -/
lemma length_codedOutput_le {d : TMDesc} {t : ℕ} {x : List Bool} {c : CodedCfg}
    (h : evalHalted d t x = some c) : (codedOutput c).length ≤ t := by
  have hb := (evalHalted_output_invariants h).2
  have hf : c.output.frontier ≤ c.output.cells.length := List.findIdx_le_length
  simpa [codedOutput] using hf.trans hb.2

/-- **Budgeted execution is faithful, unconditionally.** The run's step bound, the halting
fact, and correctness of extraction against upstream's `Tape.HasOutput`, together. -/
lemma evalHalted_spec {d : TMDesc} {t : ℕ} {x : List Bool} {c : CodedCfg}
    (h : evalHalted d t x = some c) :
    ∃ s < t, (d.toTM).reachesIn s ((d.toTM).initCfg x) (CodedCfg.decode d c) ∧
      (d.toTM).halted (CodedCfg.decode d c) ∧
      (CodedCfg.decode d c).output.HasOutput (codedOutput c) := by
  obtain ⟨s, hst, hreach, hhalt⟩ := runUntilHalt_spec d t _ c h
  rw [decode_initCoded] at hreach
  exact ⟨s, hst, hreach, hhalt,
    CodedTape.hasOutput_outputWord (evalHalted_output_invariants h).1⟩

/-! ## The compiler-facing bounded token evaluator

This is the object `LogicalInduction/Construction/LIACompiler.lean` consumes. It mirrors
`TraderProgram` / `traderProgramAt` / `clockedTokens` (`Framework/Criterion.lean`,
`Construction/TraderEnumeration.lean`) one-for-one, replacing only the *token producer*: the
decoding chain `strategyOfTokens ∘ unRpn ∘ undigitize` downstream of it is generic in a
`List ℕ` and is reused unchanged.

**Indexing by descriptions, not by description bits.** Upstream's `decodeDesc : List Bool →
TMDesc` exists because the universal machine reads its program off a tape. Here the described
machine is executed directly, so the index decodes straight to a `TMDesc` through the
`Primcodable` instance above. That keeps `decodeDesc`, `encodeDesc`, their roundtrip, and the
`TerminatedRegion` side condition off this path entirely.

**Why the index fields are plain functions.** `descAt` goes through `Encodable.decode` at
`TMDesc`, whose instance is a stack of `Primcodable.ofEquiv`s down to `Fin 4`. Any `rfl`
obligation that lets the elaborator unfold it sends `whnf` into that stack and does not
return in reasonable time — which is why `progDesc`/`progCoeff`/`progDeg` are separate
definitions used directly by `machineTokens`, rather than projections out of a structure,
and why `descAt` is sealed `irreducible` once its `Primrec` fact is proved. The structure
`MachineTraderProgram` survives only as index bookkeeping for the eventual coverage
argument, where it is convenient and never has to reduce.

**Totality.** Four things can go wrong, and none needs new machinery:

1. a malformed index — `Encodable.decode` returns `none` and we take a trivial description;
2. an out-of-range state — `TMDesc.toTM` clamps transition targets, `codedStep` mirrors the
   clamp, and `TMDesc.lookup` falls back to a halting default on a missing key, so *every*
   description denotes a real machine;
3. the machine not halting within its claimed clock — `evalHalted` reports `none`, and
   `tokensOf` emits `[]`;
4. a malformed trader stream — `strategyOfTokens` already returns the zero strategy when
   `deserializeTrades` fails or the rank discipline is violated.

So the only new fallback is `[]` at point 3.

**No clock certificate is verified.** The index carries `(coeff, deg)` and the machine simply
runs for `coeff * (n + 1) ^ deg + coeff` steps. A too-small claim truncates and falls back; a
sufficiently large one appears at another index. Truncation is not merely a totality device —
it *is* the soundness argument, since a machine run for at most `p n` steps computes
something polynomial-time whatever `p` was claimed to be. `machineTokens_steps_le` and
`length_machineTokens_le` are that argument at this layer. -/

/-- Decode an arbitrary natural as a description, using a trivial description for malformed
indices — the analogue of `LogicalInduction.codeAt`. Sealed below. -/
def descAt (i : ℕ) : TMDesc := (Encodable.decode i).getD ⟨0, 0, 0, []⟩

lemma primrec_descAt : Primrec descAt :=
  Primrec.option_getD.comp (Primrec.decode (α := TMDesc)) (Primrec.const (⟨0, 0, 0, []⟩ : TMDesc))

/-- `descAt` inverts `Encodable.encode`. Stated here, *before* the seal below, because it is
the only fact about `descAt`'s internals anything downstream needs — sealing it afterwards is
what keeps `whnf` out of the `Primcodable TMDesc` stack. -/
@[simp] lemma descAt_encode (d : TMDesc) : descAt (Encodable.encode d) = d := by
  rw [descAt, Encodable.encodek]; rfl

attribute [irreducible] descAt

/-- The description named by index `j`. -/
def progDesc (j : ℕ) : TMDesc := descAt (Nat.unpair (Nat.unpair j).1).1

/-- The polynomial clock's coefficient, named by index `j`. -/
def progCoeff (j : ℕ) : ℕ := (Nat.unpair (Nat.unpair j).1).2

/-- The polynomial clock's degree, named by index `j`. -/
def progDeg (j : ℕ) : ℕ := (Nat.unpair j).2

/-- The polynomial clock carried by index `j`, in the `a * (n + 1) ^ k + a` normal form
shared with `IsPolyBounded` and `EfficientlyComputable`. -/
def progClock (j n : ℕ) : ℕ := progCoeff j * (n + 1) ^ progDeg j + progCoeff j

/-- The same clock as a `Polynomial ℕ`, which is the form `Complexity.FP`'s normal form
asks for. -/
noncomputable def progClockPoly (j : ℕ) : Polynomial ℕ :=
  Polynomial.C (progCoeff j) * (Polynomial.X + 1) ^ progDeg j + Polynomial.C (progCoeff j)

lemma progClockPoly_eval (j n : ℕ) : (progClockPoly j).eval n = progClock j n := by
  simp [progClockPoly, progClock]

/-- The finite data an index decodes to. Index bookkeeping for the eventual coverage
argument; `machineTokens` uses the projections above directly. There is no certificate
field — the clock is a *claim*, never checked. -/
structure MachineTraderProgram where
  /-- The machine description; every `TMDesc` denotes a real machine. -/
  desc : TMDesc
  /-- The polynomial clock's coefficient. -/
  coeff : ℕ
  /-- The polynomial clock's degree. -/
  deg : ℕ

/-- A canonical natural index for a description/clock tuple. -/
def MachineTraderProgram.index (p : MachineTraderProgram) : ℕ :=
  Nat.pair (Nat.pair (Encodable.encode p.desc) p.coeff) p.deg

/-- Decode every natural into a description/clock tuple. Total, so the enumeration is. -/
def machineProgramAt (j : ℕ) : MachineTraderProgram :=
  ⟨progDesc j, progCoeff j, progDeg j⟩

/-- Decoding a canonical index returns its description. -/
@[simp] lemma progDesc_index (d : TMDesc) (a k : ℕ) :
    progDesc (MachineTraderProgram.index ⟨d, a, k⟩) = d := by
  rw [progDesc, MachineTraderProgram.index, Nat.unpair_pair, Nat.unpair_pair, descAt_encode]

/-- Decoding a canonical index returns its clock coefficient. -/
@[simp] lemma progCoeff_index (d : TMDesc) (a k : ℕ) :
    progCoeff (MachineTraderProgram.index ⟨d, a, k⟩) = a := by
  rw [progCoeff, MachineTraderProgram.index, Nat.unpair_pair, Nat.unpair_pair]

/-- Decoding a canonical index returns its clock degree. -/
@[simp] lemma progDeg_index (d : TMDesc) (a k : ℕ) :
    progDeg (MachineTraderProgram.index ⟨d, a, k⟩) = k := by
  rw [progDeg, MachineTraderProgram.index, Nat.unpair_pair]

/-- Decoding a canonical index returns its clock. -/
lemma progClock_index (d : TMDesc) (a k n : ℕ) :
    progClock (MachineTraderProgram.index ⟨d, a, k⟩) n = a * (n + 1) ^ k + a := by
  rw [progClock, progCoeff_index, progDeg_index]

/-- Round-trip on the packaged form. -/
@[simp] lemma machineProgramAt_index (p : MachineTraderProgram) :
    machineProgramAt p.index = p := by
  cases p
  rw [machineProgramAt, progDesc_index, progCoeff_index, progDeg_index]


/-- Read a finished run into a digit stream; the timeout fallback lives here, on
`Option CodedCfg`, so its `Primrec` proof stays at that small domain. -/
def tokensOf : Option CodedCfg → List ℕ
  | none => []
  | some c => bitsToDigits (codedOutput c)

/-- **The bounded total machine token evaluator.** Decode index `j`, run the described
machine on the unary day `n` for the indexed polynomial clock, and read off its output as a
digit stream; `[]` if it does not halt within budget. -/
def machineTokens (j n : ℕ) : List ℕ :=
  tokensOf (evalHalted (progDesc j) (progClock j n) (unaryDay n))

/-- **Polynomial soundness, step form.** Whatever index `j` is, the evaluator runs the
described machine for at most the polynomial `j` itself names, and when it produces output
that output is the machine's genuine halted output in upstream's sense. No truthfulness of
the clock claim is assumed, and none is needed: this holds at every index. -/
lemma machineTokens_steps_le (j n : ℕ) :
    machineTokens j n = [] ∨
      ∃ c : CodedCfg, ∃ s < progClock j n,
        ((progDesc j).toTM).reachesIn s (((progDesc j).toTM).initCfg (unaryDay n))
            (CodedCfg.decode (progDesc j) c) ∧
          ((progDesc j).toTM).halted (CodedCfg.decode (progDesc j) c) ∧
          (CodedCfg.decode (progDesc j) c).output.HasOutput (codedOutput c) ∧
          machineTokens j n = bitsToDigits (codedOutput c) := by
  rw [machineTokens]
  cases h : evalHalted (progDesc j) (progClock j n) (unaryDay n) with
  | none => exact Or.inl rfl
  | some c =>
      obtain ⟨s, hs, hreach, hhalt, hout⟩ := evalHalted_spec h
      exact Or.inr ⟨c, s, hs, hreach, hhalt, hout, rfl⟩

/-- **Polynomial soundness, output-size form.** The emitted digit stream is no longer than
the indexed clock, because one step writes at most one cell. Together with
`machineTokens_steps_le` this is all of "every enumerated item is polynomial-time" that lives
at the executable layer; the `FP` statement belongs with the complexity layer. -/
lemma length_machineTokens_le (j n : ℕ) :
    (machineTokens j n).length ≤ progClock j n := by
  rw [machineTokens]
  cases h : evalHalted (progDesc j) (progClock j n) (unaryDay n) with
  | none => simp [tokensOf]
  | some c =>
      have hlen := length_codedOutput_le h
      simp only [tokensOf, length_bitsToDigits]
      omega

/-! ### … and it is primitive recursive

`primrec_machineTokens` is the exact obligation `LIACompiler` consumes: with it, the proof of
`enumeratedTraderTrades_prim` goes through verbatim with `clockedTokens_prim` replaced.

Every step below is a plain `.comp` whose underlying function is *syntactically* the
definition being characterised, so no `of_eq` defeq check is ever performed at a type
carrying the `Primcodable` stack. -/

lemma primrec_progDesc : Primrec progDesc :=
  primrec_descAt.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))

lemma primrec_progCoeff : Primrec progCoeff :=
  Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))

lemma primrec_progDeg : Primrec progDeg := Primrec.snd.comp Primrec.unpair

lemma primrec_b2n : Primrec b2n := primrec_of_bool b2n 0

set_option maxHeartbeats 1000000 in
lemma primrec_progClock : Primrec₂ progClock := by
  have hpow₂ : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) := Primrec₂.unpaired'.mp Nat.Primrec.pow
  have hc : Primrec fun z : ℕ × ℕ => progCoeff z.1 := primrec_progCoeff.comp Primrec.fst
  have hd : Primrec fun z : ℕ × ℕ => progDeg z.1 := primrec_progDeg.comp Primrec.fst
  exact Primrec.nat_add.comp
    (Primrec.nat_mul.comp hc (hpow₂.comp (Primrec.succ.comp Primrec.snd) hd)) hc

lemma primrec_unaryDay : Primrec unaryDay :=
  (Primrec.list_map Primrec.list_range (Primrec.const true).to₂).of_eq fun n => by
    simp [unaryDay, List.map_const']

set_option maxHeartbeats 1000000 in
lemma primrec_digitAt : Primrec₂ digitAt := by
  have hbit : ∀ r : ℕ, Primrec₂ fun (l : List Bool) (i : ℕ) =>
      b2n ((l[3 * i + r]?).getD false) := fun r =>
    primrec_b2n.comp (Primrec.option_getD.comp
      (Primrec.list_getElem?.comp Primrec.fst
        (Primrec.nat_add.comp
          (Primrec.nat_mul.comp (Primrec.const 3) Primrec.snd) (Primrec.const r)))
      (Primrec.const false))
  have h0 : Primrec₂ fun (l : List Bool) (i : ℕ) => b2n ((l[3 * i]?).getD false) := hbit 0
  exact Primrec.nat_add.comp
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 4) h0)
      (Primrec.nat_mul.comp (Primrec.const 2) (hbit 1)))
    (hbit 2)

set_option maxHeartbeats 1000000 in
lemma primrec_bitsToDigits : Primrec bitsToDigits :=
  Primrec.list_map
    (Primrec.list_range.comp (Primrec.nat_div.comp Primrec.list_length (Primrec.const 3)))
    primrec_digitAt

set_option maxHeartbeats 1000000 in
lemma primrec_tokensOf : Primrec tokensOf :=
  (Primrec.option_casesOn Primrec.id (Primrec.const [])
    (Primrec.to₂ (primrec_bitsToDigits.comp
      (primrec_codedOutput.comp Primrec.snd)))).of_eq fun o => by cases o <;> rfl

set_option maxHeartbeats 1000000 in
/-- **The obligation `LIACompiler` consumes.** -/
lemma primrec_machineTokens : Primrec₂ machineTokens :=
  primrec_tokensOf.comp
    (primrec_evalHalted.comp (Primrec.pair
      (primrec_progDesc.comp Primrec.fst)
      (Primrec.pair primrec_progClock (primrec_unaryDay.comp Primrec.snd))))

/-! ## From an `FP` witness to an enumeration index

`Complexity.exists_desc_computesInTime_polynomial` hands back a description together with a
`Polynomial ℕ` time bound. An index of this enumeration carries instead a clock in the
`a * (n + 1) ^ k + a` normal form shared with `IsPolyBounded` and `EfficientlyComputable`.
The conversion is the only arithmetic gap between the two, and it is uniform: a
natural-coefficient polynomial is dominated by its coefficient sum times `(n + 1)` to its
degree, at *every* `n`.

This is what makes coverage a matter of *choosing* an index rather than of proving anything
further about the machine: given `f ∈ FP`, take the description, take the clock below, and
the corresponding index runs the described machine long enough. -/

/-- A natural-coefficient polynomial is dominated at every point by the clock normal form
`a * (n + 1) ^ k + a`, with `a` its coefficient sum and `k` its degree. -/
lemma exists_clock_of_polynomial (q : Polynomial ℕ) :
    ∃ a k : ℕ, ∀ n, q.eval n ≤ a * (n + 1) ^ k + a := by
  refine ⟨∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i, q.natDegree, fun n => ?_⟩
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  refine le_trans (Finset.sum_le_sum fun i hi => ?_) (Nat.le_add_right _ _)
  refine Nat.mul_le_mul_left _ ?_
  calc n ^ i ≤ (n + 1) ^ i := Nat.pow_le_pow_left (Nat.le_succ n) i
    _ ≤ (n + 1) ^ q.natDegree :=
        Nat.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le n))
          (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))

/-- **Every polynomial-time function is computed by a described machine under a clock in
the enumeration's normal form.** The composite of
`Complexity.exists_desc_computesInTime_polynomial` with the conversion above: this is the
statement the coverage half of the machine-trader enumeration consumes, and the last step
that mentions `Complexity.FP` rather than an index. -/
lemma exists_desc_computesInTime_clock {f : List Bool → List Bool}
    (hf : f ∈ Complexity.FP) :
    ∃ (d : TMDesc) (a k : ℕ) (T : ℕ → ℕ),
      d.toTM.ComputesInTime f T ∧ ∀ n, T n ≤ a * (n + 1) ^ k + a := by
  obtain ⟨d, q, -, hd⟩ := Complexity.exists_desc_computesInTime_polynomial hf
  obtain ⟨a, k, hak⟩ := exists_clock_of_polynomial q
  exact ⟨d, a, k, q.eval, hd, hak⟩

/-! ## Completeness of the budgeted run

`runUntilHalt_spec` says the budgeted run is *sound*: whatever it reports really is a halted
configuration the machine reaches. Coverage needs the converse — that when the real machine
halts inside the budget, the executable run finds it rather than timing out.

That direction is available because the machine is deterministic and `codedStep` tracks
`TM.step` exactly (`codedStep_eq`): there is only one run to follow, so the executable one
cannot miss the halt. Note the budget must exceed the running time strictly: `stepFrozen`
spends one iteration *noticing* that `codedStep` returned `none`. -/

/-- A coded step reports `none` exactly when the decoded machine has halted. The forward
direction is `halted_of_codedStep_none`; this is the converse, and the two together are what
make the executable run faithful in both directions. -/
lemma codedStep_eq_none_iff {d : TMDesc} {c : CodedCfg} :
    codedStep d c = none ↔ (d.toTM).halted (CodedCfg.decode d c) := by
  refine ⟨halted_of_codedStep_none, fun h => ?_⟩
  have h2 := codedStep_eq d c
  rw [TM.step, if_pos h] at h2
  exact Option.map_eq_none_iff.mp h2

/-- **Completeness of the budgeted run.** If the real machine reaches a halted configuration
in `s` steps and the budget strictly exceeds `s`, the executable run reports it — with the
same decoded configuration, so nothing about the output is lost. -/
lemma runUntilHalt_complete (d : TMDesc) :
    ∀ (s : ℕ) (c : CodedCfg) (cr : Cfg 1 (d.toTM).Q),
      (d.toTM).reachesIn s (CodedCfg.decode d c) cr → (d.toTM).halted cr →
      ∀ t, s < t → ∃ c', runUntilHalt d t c = some c' ∧ CodedCfg.decode d c' = cr
  | 0, c, cr, hreach, hhalt, t, ht => by
      cases hreach
      obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
      have hs : codedStep d c = none := codedStep_eq_none_iff.mpr hhalt
      have hfz : stepFrozen d (c, false) = (c, true) := by
        rw [stepFrozen]; simp only [hs]; rfl
      refine ⟨c, ?_, rfl⟩
      rw [runUntilHalt, Function.iterate_succ_apply, hfz, stepFrozen_frozen]
      simp
  | (s + 1), c, cr, hreach, hhalt, t, ht => by
      cases hreach with
      | step hstep hrest =>
          rename_i c''
          obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
          -- the coded step mirrors the real one, so it produces a configuration
          have h2 := codedStep_eq d c
          rw [hstep] at h2
          obtain ⟨c₁, hc₁, hdec⟩ : ∃ c₁, codedStep d c = some c₁ ∧
              CodedCfg.decode d c₁ = c'' := by
            cases hcs : codedStep d c with
            | none => rw [hcs] at h2; exact absurd h2.symm (by simp)
            | some c₁ =>
                rw [hcs, Option.map_some, Option.some.injEq] at h2
                exact ⟨c₁, rfl, h2⟩
          have hfz : stepFrozen d (c, false) = (c₁, false) := by
            rw [stepFrozen]; simp only [hc₁]; rfl
          obtain ⟨c', hrun, hdec'⟩ :=
            runUntilHalt_complete d s c₁ cr (by rw [hdec]; exact hrest) hhalt t' (by omega)
          refine ⟨c', ?_, hdec'⟩
          rw [runUntilHalt, Function.iterate_succ_apply, hfz]
          exact hrun

/-- `Tape.HasOutput` determines the output word: the first blank fixes the length, and the
cells fix the bits. -/
lemma hasOutput_unique {t : Tape} {y z : List Bool}
    (hy : t.HasOutput y) (hz : t.HasOutput z) : y = z := by
  have hlen : y.length = z.length := by
    rcases Nat.lt_trichotomy y.length z.length with hlt | heq | hgt
    · exact absurd (hz.1 y.length hlt ▸ hy.2) (Γ.ofBool_ne_blank _)
    · exact heq
    · exact absurd (hy.1 z.length hgt ▸ hz.2) (Γ.ofBool_ne_blank _)
  refine List.ext_getElem hlen fun i hi hi' => ?_
  have h1 := hy.1 i hi
  have h2 := hz.1 i hi'
  rw [h1] at h2
  cases hyi : y[i] <;> cases hzi : z[i] <;> rw [hyi, hzi] at h2 <;> simp_all [Γ.ofBool]

/-- **The budgeted evaluator recovers any in-clock output.** If the described machine computes
`f` within `T` and the budget strictly exceeds `T |x|`, the executable evaluator halts and
extracts exactly `f x`.

This is the bridge coverage needs: it turns a `Complexity.ComputesInTime` fact about a
`TMDesc` into an equation about `machineTokens`. -/
lemma evalHalted_complete {d : TMDesc} {f : List Bool → List Bool} {T : ℕ → ℕ}
    (h : (d.toTM).ComputesInTime f T) (x : List Bool) {t : ℕ} (ht : T x.length < t) :
    ∃ c, evalHalted d t x = some c ∧ codedOutput c = f x := by
  obtain ⟨cr, s, hs, hreach, hhalt, hout⟩ := h x
  rw [← decode_initCoded d x] at hreach
  obtain ⟨c', hrun, hdec⟩ :=
    runUntilHalt_complete d s (initCoded d x) cr hreach hhalt t (by omega)
  refine ⟨c', hrun, ?_⟩
  have hmine : (CodedCfg.decode d c').output.HasOutput (codedOutput c') :=
    CodedTape.hasOutput_outputWord (evalHalted_output_invariants hrun).1
  rw [hdec] at hmine
  exact hasOutput_unique hmine hout

/-! ## `machineTokens` completeness

`machineTokens_steps_le` is the soundness half: whatever an index emits came from a genuine
in-clock run. This is the completeness half, and it is what coverage consumes — if the
description an index names really does compute `f` inside the clock that index claims, then
the index emits exactly `f`'s digit stream.

Note the strict inequality: `stepFrozen` spends one iteration *noticing* that `codedStep`
returned `none`, so the budget must exceed the running time rather than merely match it.
Coverage supplies that by bumping the clock coefficient, which the clock normal form absorbs
(`progClock_lt_of_le`). -/

/-- Bumping the coefficient makes the clock strictly dominate any bound it weakly dominates.
The slack `stepFrozen` needs, obtained without weakening the converse. -/
lemma lt_clock_succ {a k m n : ℕ} (h : m ≤ a * (n + 1) ^ k + a) :
    m < (a + 1) * (n + 1) ^ k + (a + 1) := by
  have h1 : a * (n + 1) ^ k ≤ (a + 1) * (n + 1) ^ k :=
    Nat.mul_le_mul_right _ (Nat.le_succ a)
  omega

/-- **`machineTokens` completeness.** If index `j`'s description computes `f` within a bound
its own clock strictly exceeds, then on day `n` the index emits exactly the digit stream of
`f`'s output on the unary day. -/
lemma machineTokens_eq_of_computesInTime {j : ℕ} {f : List Bool → List Bool} {T : ℕ → ℕ}
    (h : ((progDesc j).toTM).ComputesInTime f T) (n : ℕ)
    (ht : T (unaryDay n).length < progClock j n) :
    machineTokens j n = bitsToDigits (f (unaryDay n)) := by
  obtain ⟨c, hc, hout⟩ := evalHalted_complete h (unaryDay n) ht
  rw [machineTokens, hc, tokensOf, hout]

end LogicalInduction.MachineExec


/-! ## Axiom report

The simulation capstones, the extraction correctness lemma, the compiler obligation, and the
two soundness bounds. All depend on exactly `[propext, Classical.choice, Quot.sound]`. -/

section AxiomReport
open LogicalInduction.MachineExec

#print axioms codedStep_eq
#print axioms runUntilHalt_spec
#print axioms decode_initCoded
#print axioms evalHalted_spec
#print axioms CodedTape.hasOutput_outputWord
#print axioms primrec_codedStep
#print axioms primrec_runUntilHalt
#print axioms primrec_machineTokens
#print axioms machineTokens_steps_le
#print axioms length_machineTokens_le

end AxiomReport
