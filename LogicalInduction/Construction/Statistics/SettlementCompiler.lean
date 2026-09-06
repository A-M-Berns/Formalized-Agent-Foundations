import LogicalInduction.Construction.Statistics.SettlementClock
import LogicalInduction.Construction.LIACompiler
import LogicalInduction.Framework.Emission.WriteOut

/-!
# Compiling the settlement test

`Statistics/SettlementClock.lean` reduces the patient settlement clock to a
`SettlementChecker`: a purely computational bounded test on the market's own quotes.  This
module builds that checker from programs — `SettlementChecker.ofComputations` and, on top of
it, `PatientSettlementClock.ofComputations`, which takes a market computation and a
deductive-process computation and returns the clock with no computability hypothesis left on
the caller.

Three layers make that possible.

**The test on Gödel codes.**  Recursions over `Sentence` cannot be written directly, because
`Sentence`'s recursor is not a `Primrec` combinator; they go by course-of-values recursion on
the Gödel code via `Primrec.nat_strong_rec`, following the `sentencePrimcodable` template of
`LIACompiler.lean`.  Every such quantity is `Option`-encoded — `0` for "the code does not
decode", `v + 1` for "it decodes with value `v`" — and the encoding is load-bearing: for a
binary code with one decodable and one undecodable child the answer must be `0`, which a plain
fold over child values could not distinguish from a genuine value of `0`.  (`formulaBinaryNorm`
in `LIACompiler.lean` uses the same `left = 0 ∨ right = 0` guard for the same reason.)  The
results are `atomBound_prim`, `evalBits_prim`, `stageSatBits_prim`, `allBitLists_prim` and
`settlementAtomLimit_prim`, the `Primrec` leaves of the code recognizing `SettlementTestBool`.

**The fuel layer over the market's quote table.**  `MarketComputation.totalQuote`,
`readyAtFuel` and `denoteRatComp`, with the bridge `denoteRatComp_eq`.  The `readyAtFuel`
guard is what makes the total table sound, and `AffineCombination.settlementCheckAtFuel` — the
conservative bounded check, sound and complete at sufficient fuel — is what
`SettlementChecker.ofComputations` searches over with `rfindOpt`.

**`def:ece` into `Computable`.**  `BigSpliceStream.feature_primrec` and
`PGenerableRat.computable`: the bridge an arithmetic quote code needs in order to emit
`⌜· > q n⌝` from a market-dependent feature progression.  `AffineCombination.PolySequence`
exposes each feature as a polynomially emitted serialization rather than an opaque `EF`, so
the primitive recursion goes through `PolySegStream.primrec` and the canonical trade-stream
decoder.

Foundation's formula tags, used throughout: `0 = ⊥`, `1 = atom`, `2 = 🡒`, `3 = ⋏`, `4 = ⋎`.

`Nat.sqrt` is locally irreducible in two sections below, for the reason stated in
`Statistics/SettlementClock.lean`.
-/

namespace LogicalInduction

section SettlementCompile

open LO.Propositional

/-- `atomBound` on a Gödel code, `Option`-encoded (`0` = does not decode). -/
private def atomBoundNorm (n : ℕ) : ℕ :=
  match (@LO.Propositional.Formula.ofNat ℕ inferInstance n : Option Sentence) with
  | none => 0
  | some φ => BoolPCWorld.atomBound φ + 1

/-- All three binary connectives take the `max` of their children's bounds, so unlike
`formulaBinaryNorm` this needs no tag argument. -/
private def atomBoundBinary (prior : List ℕ) (children : ℕ) : ℕ :=
  let left := prior.getD children.unpair.1 0
  let right := prior.getD children.unpair.2 0
  if left = 0 ∨ right = 0 then 0
  else max (left - 1) (right - 1) + 1

private lemma atomBoundBinary_prim : Primrec₂ atomBoundBinary := by
  let childLeft : List ℕ × ℕ → ℕ := fun p => p.1.getD p.2.unpair.1 0
  let childRight : List ℕ × ℕ → ℕ := fun p => p.1.getD p.2.unpair.2 0
  have hleft : Primrec childLeft :=
    (Primrec.list_getD 0).comp Primrec.fst
      (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))
  have hright : Primrec childRight :=
    (Primrec.list_getD 0).comp Primrec.fst
      (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))
  have hbad : PrimrecPred fun p : List ℕ × ℕ =>
      childLeft p = 0 ∨ childRight p = 0 :=
    (Primrec.eq.comp hleft (Primrec.const 0)).or
      (Primrec.eq.comp hright (Primrec.const 0))
  have hmax : Primrec fun p : List ℕ × ℕ =>
      max (childLeft p - 1) (childRight p - 1) + 1 :=
    Primrec.nat_add.comp
      (Primrec.nat_max.comp
        (Primrec.nat_sub.comp hleft (Primrec.const 1))
        (Primrec.nat_sub.comp hright (Primrec.const 1)))
      (Primrec.const 1)
  exact (Primrec.ite hbad (Primrec.const 0) hmax).to₂.of_eq fun prior children => by
    simp only [atomBoundBinary, childLeft, childRight]

private def atomBoundSucc (prior : List ℕ) (e : ℕ) : ℕ :=
  let tag := e.unpair.1
  let payload := e.unpair.2
  if tag = 0 then 1
  else if tag = 1 then payload + 2
  else if tag = 2 then atomBoundBinary prior payload
  else if tag = 3 then atomBoundBinary prior payload
  else if tag = 4 then atomBoundBinary prior payload
  else 0

private lemma atomBoundSucc_prim : Primrec₂ atomBoundSucc := by
  let tag : List ℕ × ℕ → ℕ := fun p => p.2.unpair.1
  let payload : List ℕ × ℕ → ℕ := fun p => p.2.unpair.2
  have htag : Primrec tag := Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have hpayload : Primrec payload := Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)
  have hatom : Primrec fun p : List ℕ × ℕ => payload p + 2 :=
    Primrec.nat_add.comp hpayload (Primrec.const 2)
  have hbin : Primrec fun p : List ℕ × ℕ => atomBoundBinary p.1 (payload p) :=
    atomBoundBinary_prim.comp Primrec.fst hpayload
  have htagEq (k : ℕ) : PrimrecPred fun p : List ℕ × ℕ => tag p = k :=
    Primrec.eq.comp htag (Primrec.const k)
  have h4 := Primrec.ite (htagEq 4) hbin (Primrec.const 0)
  have h3 := Primrec.ite (htagEq 3) hbin h4
  have h2 := Primrec.ite (htagEq 2) hbin h3
  have h1 := Primrec.ite (htagEq 1) hatom h2
  exact (Primrec.ite (htagEq 0) (Primrec.const 1) h1).to₂.of_eq fun prior e => by
    simp only [atomBoundSucc, tag, payload]

private def atomBoundList (prior : List ℕ) : ℕ :=
  prior.length.casesOn 0 (atomBoundSucc prior)

private lemma atomBoundList_prim : Primrec atomBoundList :=
  (Primrec.nat_casesOn Primrec.list_length (Primrec.const 0)
    atomBoundSucc_prim).of_eq fun prior => by simp only [atomBoundList]

private lemma atomBoundNorm_zero : atomBoundNorm 0 = 0 := by
  simp [atomBoundNorm, LO.Propositional.Formula.ofNat]

private lemma atomBoundHistory_getD {n k : ℕ} (hk : k < n) :
    ((List.range n).map atomBoundNorm).getD k 0 = atomBoundNorm k := by
  rw [← atomBoundNorm_zero, List.getD_map]
  simp [hk]

/-- The binary step reads both children out of the history correctly.  Shared by all three
connectives: `atomBound` maxes its children regardless of which one it is. -/
private lemma atomBoundBinary_history (payload n : ℕ)
    (hleft : payload.unpair.1 < n) (hright : payload.unpair.2 < n) :
    atomBoundBinary ((List.range n).map atomBoundNorm) payload =
      match (@LO.Propositional.Formula.ofNat ℕ inferInstance payload.unpair.1 : Option Sentence),
          (@LO.Propositional.Formula.ofNat ℕ inferInstance payload.unpair.2 : Option Sentence) with
      | some φ, some ψ => max (BoolPCWorld.atomBound φ) (BoolPCWorld.atomBound ψ) + 1
      | _, _ => 0 := by
  unfold atomBoundBinary
  rw [atomBoundHistory_getD hleft, atomBoundHistory_getD hright]
  cases hL : (@LO.Propositional.Formula.ofNat ℕ inferInstance
      payload.unpair.1 : Option Sentence) <;>
    cases hR : (@LO.Propositional.Formula.ofNat ℕ inferInstance
      payload.unpair.2 : Option Sentence) <;>
    simp [atomBoundNorm, hL, hR]

private lemma atomBoundList_history (n : ℕ) :
    atomBoundList ((List.range n).map atomBoundNorm) = atomBoundNorm n := by
  cases n with
  | zero => simp [atomBoundList, atomBoundNorm, LO.Propositional.Formula.ofNat]
  | succ e =>
      have hleft : e.unpair.2.unpair.1 < e + 1 :=
        Nat.lt_succ_iff.mpr <|
          le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _)
      have hright : e.unpair.2.unpair.2 < e + 1 :=
        Nat.lt_succ_iff.mpr <|
          le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _)
      have hbin := atomBoundBinary_history e.unpair.2 (e + 1) hleft hright
      by_cases h0 : e.unpair.1 = 0
      · simp [atomBoundList, atomBoundSucc, atomBoundNorm, BoolPCWorld.atomBound,
          LO.Propositional.Formula.ofNat, h0]
      by_cases h1 : e.unpair.1 = 1
      · simp [atomBoundList, atomBoundSucc, atomBoundNorm, BoolPCWorld.atomBound,
          LO.Propositional.Formula.ofNat, h1]
      -- The three binary tags run the same script; only the numeral `ofNat` rebuilds on
      -- differs, so the script is written once and instantiated at each tag.
      have hbinTag : ∀ t : ℕ, t = 2 ∨ t = 3 ∨ t = 4 → e.unpair.1 = t →
          atomBoundList ((List.range (e + 1)).map atomBoundNorm)
            = atomBoundNorm (e + 1) := by
        rintro t (rfl | rfl | rfl) ht
        all_goals
          simp only [atomBoundList, List.length_map, List.length_range, atomBoundSucc,
            ht, ↓reduceIte]
          rw [hbin]
          simp only [atomBoundNorm, LO.Propositional.Formula.ofNat, ht]
          cases (@LO.Propositional.Formula.ofNat ℕ inferInstance
              e.unpair.2.unpair.1 : Option Sentence) <;>
            cases (@LO.Propositional.Formula.ofNat ℕ inferInstance
              e.unpair.2.unpair.2 : Option Sentence) <;>
            simp [BoolPCWorld.atomBound]
      by_cases h2 : e.unpair.1 = 2
      · exact hbinTag 2 (by tauto) h2
      by_cases h3 : e.unpair.1 = 3
      · exact hbinTag 3 (by tauto) h3
      by_cases h4 : e.unpair.1 = 4
      · exact hbinTag 4 (by tauto) h4
      · have htag : 5 ≤ e.unpair.1 := by omega
        simp [atomBoundList, atomBoundSucc, atomBoundNorm,
          LO.Propositional.Formula.ofNat, h0, h1, h2, h3, h4]

private lemma atomBoundNorm_prim : Primrec atomBoundNorm := by
  have hstep : Primrec₂ (fun (_ : Unit) (prior : List ℕ) =>
      some (atomBoundList prior)) :=
    Primrec₂.option_some_iff.mpr (atomBoundList_prim.comp Primrec₂.right)
  have hrec := Primrec.nat_strong_rec (fun (_ : Unit) n => atomBoundNorm n)
    hstep (fun _ n => by simpa using congrArg some (atomBoundList_history n))
  exact (hrec.comp (Primrec.const ()) Primrec.id).of_eq fun n => rfl

/-- **`atomBound` is primitive recursive.**  The first of the two `Sentence` recursions the
settlement test needs; `evalBits_prim` below is the other. -/
lemma atomBound_prim : Primrec BoolPCWorld.atomBound := by
  have h : Primrec fun φ : Sentence => atomBoundNorm (Encodable.encode φ) - 1 :=
    Primrec.nat_sub.comp (atomBoundNorm_prim.comp Primrec.encode) (Primrec.const 1)
  exact h.of_eq fun φ => by
    simp only [atomBoundNorm, Encodable.encode,
      LO.Propositional.Formula.ofNat_toNat φ, Nat.add_sub_cancel]

/-! ### Evaluation

`eval` is the second `Sentence` recursion, and the one the whole test rests on.  Two things
make it harder than `atomBound`:

* the recursion is **parameterized by the world** (`α := List Bool` in `nat_strong_rec`,
  where `atomBound` used `Unit`), and the atom case is where that parameter is consumed —
  `eval (bitsWorld l) (.atom a) = l.getD a false`, i.e. `Primrec.list_getD` on the
  parameter;
* the three binary tags genuinely differ (`🡒`/`⋏`/`⋎`), where `atomBound` maxed all three
  alike.  The second costs nothing in the end: `Bool` is finite, so `Primrec.dom_bool₂`
  gives *every* `Bool → Bool → Bool` for free, and `evalOp` dispatches on the tag.

The `Option` encoding carries a Boolean, so it is three-valued: `0` = does not decode,
`1` = decodes to `false`, `2` = decodes to `true`. -/

/-- The connective a tag denotes.  `Primrec₂` for free by `Primrec.dom_bool₂`. -/
private def evalOp (tag : ℕ) (a b : Bool) : Bool :=
  if tag = 2 then (!a || b) else if tag = 3 then (a && b) else (a || b)

/-- `eval` on a Gödel code, `Option`-encoded (`0` = does not decode, `1` = false,
`2` = true). -/
private def evalNorm (l : List Bool) (n : ℕ) : ℕ :=
  match (@LO.Propositional.Formula.ofNat ℕ inferInstance n : Option Sentence) with
  | none => 0
  | some φ => if BoolPCWorld.eval (BoolPCWorld.bitsWorld l) φ then 2 else 1

private def evalBinary (tag : ℕ) (prior : List ℕ) (children : ℕ) : ℕ :=
  let left := prior.getD children.unpair.1 0
  let right := prior.getD children.unpair.2 0
  if left = 0 ∨ right = 0 then 0
  else if evalOp tag (decide (left = 2)) (decide (right = 2)) then 2 else 1

private lemma evalBinary_prim (tag : ℕ) : Primrec₂ (evalBinary tag) := by
  let childLeft : List ℕ × ℕ → ℕ := fun p => p.1.getD p.2.unpair.1 0
  let childRight : List ℕ × ℕ → ℕ := fun p => p.1.getD p.2.unpair.2 0
  have hleft : Primrec childLeft :=
    (Primrec.list_getD 0).comp Primrec.fst
      (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))
  have hright : Primrec childRight :=
    (Primrec.list_getD 0).comp Primrec.fst
      (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))
  have hbad : PrimrecPred fun p : List ℕ × ℕ =>
      childLeft p = 0 ∨ childRight p = 0 :=
    (Primrec.eq.comp hleft (Primrec.const 0)).or
      (Primrec.eq.comp hright (Primrec.const 0))
  -- `PrimrecPred p` is `∃ _ : DecidablePred p, Primrec fun a => decide (p a)` — an
  -- existential over the instance, so it never unfolds to `Primrec` on its own.
  -- `PrimrecPred.decide`/`Primrec.primrecPred` are the two directions.
  have ha : Primrec fun p : List ℕ × ℕ => decide (childLeft p = 2) :=
    (Primrec.eq.comp hleft (Primrec.const 2)).decide
  have hb : Primrec fun p : List ℕ × ℕ => decide (childRight p = 2) :=
    (Primrec.eq.comp hright (Primrec.const 2)).decide
  have hop : Primrec fun p : List ℕ × ℕ =>
      evalOp tag (decide (childLeft p = 2)) (decide (childRight p = 2)) :=
    (Primrec.dom_bool₂ (evalOp tag)).comp ha hb
  have hcondp : PrimrecPred fun p : List ℕ × ℕ =>
      evalOp tag (decide (childLeft p = 2)) (decide (childRight p = 2)) = true :=
    Primrec.primrecPred (by simpa using hop)
  have hres := Primrec.ite hcondp (Primrec.const 2) (Primrec.const 1)
  exact (Primrec.ite hbad (Primrec.const 0) hres).to₂.of_eq fun prior children => by
    simp only [evalBinary, childLeft, childRight]

private def evalSucc (l : List Bool) (prior : List ℕ) (e : ℕ) : ℕ :=
  let tag := e.unpair.1
  let payload := e.unpair.2
  if tag = 0 then 1
  else if tag = 1 then (if l.getD payload false then 2 else 1)
  else if tag = 2 then evalBinary 2 prior payload
  else if tag = 3 then evalBinary 3 prior payload
  else if tag = 4 then evalBinary 4 prior payload
  else 0

private lemma evalSucc_prim :
    Primrec fun p : List Bool × List ℕ × ℕ => evalSucc p.1 p.2.1 p.2.2 := by
  let tag : List Bool × List ℕ × ℕ → ℕ := fun p => p.2.2.unpair.1
  let payload : List Bool × List ℕ × ℕ → ℕ := fun p => p.2.2.unpair.2
  have htag : Primrec tag :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.snd))
  have hpayload : Primrec payload :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.snd))
  -- The atom case: this is where the world parameter is consumed, by `list_getD` on the
  -- parameter rather than on the recursion history.  It is the one move `atomBound` (whose
  -- `nat_strong_rec` parameter is `Unit`) does not need.
  have hatom : Primrec fun p : List Bool × List ℕ × ℕ =>
      cond (p.1.getD (payload p) false) 2 1 :=
    Primrec.cond ((Primrec.list_getD false).comp Primrec.fst hpayload)
      (Primrec.const 2) (Primrec.const 1)
  have hbin (k : ℕ) : Primrec fun p : List Bool × List ℕ × ℕ =>
      evalBinary k p.2.1 (payload p) :=
    (evalBinary_prim k).comp (Primrec.fst.comp Primrec.snd) hpayload
  have htagEq (k : ℕ) : PrimrecPred fun p : List Bool × List ℕ × ℕ => tag p = k :=
    Primrec.eq.comp htag (Primrec.const k)
  have h4 := Primrec.ite (htagEq 4) (hbin 4) (Primrec.const 0)
  have h3 := Primrec.ite (htagEq 3) (hbin 3) h4
  have h2 := Primrec.ite (htagEq 2) (hbin 2) h3
  have h1 := Primrec.ite (htagEq 1) hatom h2
  exact (Primrec.ite (htagEq 0) (Primrec.const 1) h1).of_eq fun p => by
    simp only [evalSucc, tag, payload]
    by_cases hc0 : p.2.2.unpair.1 = 0
    · simp [hc0]
    by_cases hc1 : p.2.2.unpair.1 = 1
    · simp only [hc1, if_true]
      cases p.1.getD p.2.2.unpair.2 false <;> simp
    · simp [hc0, hc1]

private def evalList (l : List Bool) (prior : List ℕ) : ℕ :=
  prior.length.casesOn 0 (evalSucc l prior)

private lemma evalList_prim :
    Primrec fun p : List Bool × List ℕ => evalList p.1 p.2 := by
  have h := Primrec.nat_casesOn (Primrec.list_length.comp Primrec.snd)
    (Primrec.const 0)
    (evalSucc_prim.comp
      ((Primrec.fst.comp Primrec.fst).pair
        ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))).to₂
  exact h.of_eq fun p => by simp only [evalList]

private lemma evalNorm_zero (l : List Bool) : evalNorm l 0 = 0 := by
  simp [evalNorm, LO.Propositional.Formula.ofNat]

private lemma evalHistory_getD (l : List Bool) {n k : ℕ} (hk : k < n) :
    ((List.range n).map (evalNorm l)).getD k 0 = evalNorm l k := by
  rw [← evalNorm_zero l, List.getD_map]
  simp [hk]

private lemma evalBinary_history (tag : ℕ) (l : List Bool) (payload n : ℕ)
    (hleft : payload.unpair.1 < n) (hright : payload.unpair.2 < n) :
    evalBinary tag ((List.range n).map (evalNorm l)) payload =
      match (@LO.Propositional.Formula.ofNat ℕ inferInstance payload.unpair.1 : Option Sentence),
          (@LO.Propositional.Formula.ofNat ℕ inferInstance payload.unpair.2 : Option Sentence) with
      | some φ, some ψ =>
          if evalOp tag (BoolPCWorld.eval (BoolPCWorld.bitsWorld l) φ)
            (BoolPCWorld.eval (BoolPCWorld.bitsWorld l) ψ) then 2 else 1
      | _, _ => 0 := by
  unfold evalBinary
  rw [evalHistory_getD l hleft, evalHistory_getD l hright]
  cases hL : (@LO.Propositional.Formula.ofNat ℕ inferInstance
      payload.unpair.1 : Option Sentence) <;>
    cases hR : (@LO.Propositional.Formula.ofNat ℕ inferInstance
      payload.unpair.2 : Option Sentence) <;>
    simp only [evalNorm, hL, hR] <;>
    [skip; skip; skip;
      (cases BoolPCWorld.eval (BoolPCWorld.bitsWorld l) _ <;>
        cases BoolPCWorld.eval (BoolPCWorld.bitsWorld l) _ <;> simp)] <;>
    simp

private lemma evalList_history (l : List Bool) (n : ℕ) :
    evalList l ((List.range n).map (evalNorm l)) = evalNorm l n := by
  cases n with
  | zero => simp [evalList, evalNorm, LO.Propositional.Formula.ofNat]
  | succ e =>
      have hleft : e.unpair.2.unpair.1 < e + 1 :=
        Nat.lt_succ_iff.mpr <| le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _)
      have hright : e.unpair.2.unpair.2 < e + 1 :=
        Nat.lt_succ_iff.mpr <| le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _)
      by_cases h0 : e.unpair.1 = 0
      · simp [evalList, evalSucc, evalNorm, BoolPCWorld.eval,
          LO.Propositional.Formula.ofNat, h0]
      by_cases h1 : e.unpair.1 = 1
      · simp [evalList, evalSucc, evalNorm, BoolPCWorld.eval, BoolPCWorld.bitsWorld,
          LO.Propositional.Formula.ofNat, h1]
      -- The three binary tags run the same script; only the numeral `ofNat` rebuilds on
      -- differs, so the script is written once and instantiated at each tag.
      have hbinTag : ∀ t : ℕ, t = 2 ∨ t = 3 ∨ t = 4 → e.unpair.1 = t →
          evalList l ((List.range (e + 1)).map (evalNorm l)) = evalNorm l (e + 1) := by
        intro t ht2 ht
        have hrw := evalBinary_history t l e.unpair.2 (e + 1) hleft hright
        rcases ht2 with rfl | rfl | rfl
        all_goals
          simp only [evalList, List.length_map, List.length_range, evalSucc,
            ht, ↓reduceIte]
          rw [hrw]
          simp only [evalNorm, LO.Propositional.Formula.ofNat, ht]
          cases (@LO.Propositional.Formula.ofNat ℕ inferInstance
              e.unpair.2.unpair.1 : Option Sentence) <;>
            cases (@LO.Propositional.Formula.ofNat ℕ inferInstance
              e.unpair.2.unpair.2 : Option Sentence) <;>
            simp [BoolPCWorld.eval, evalOp]
      by_cases h2 : e.unpair.1 = 2
      · exact hbinTag 2 (by tauto) h2
      by_cases h3 : e.unpair.1 = 3
      · exact hbinTag 3 (by tauto) h3
      by_cases h4 : e.unpair.1 = 4
      · exact hbinTag 4 (by tauto) h4
      · have htag : 5 ≤ e.unpair.1 := by omega
        simp [evalList, evalSucc, evalNorm,
          LO.Propositional.Formula.ofNat, h0, h1, h2, h3, h4]

private lemma evalNorm_prim : Primrec₂ evalNorm := by
  have hstep : Primrec₂ (fun (l : List Bool) (prior : List ℕ) =>
      some (evalList l prior)) :=
    Primrec₂.option_some_iff.mpr evalList_prim.to₂
  exact Primrec.nat_strong_rec evalNorm hstep
    (fun l n => by simpa using congrArg some (evalList_history l n))

/-- **Evaluation is primitive recursive**, as a function of the bit list denoting the world
and the sentence.  The world never appears as an argument — `bitsWorld` is applied and
beta-reduced in place — which is what makes the statement well-typed at all: `BoolPCWorld`
is `ℕ → Bool` and has no `Primcodable` instance. -/
lemma evalBits_prim : Primrec₂ fun (l : List Bool) (φ : Sentence) =>
    BoolPCWorld.eval (BoolPCWorld.bitsWorld l) φ := by
  have h : Primrec fun p : List Bool × Sentence =>
      decide (evalNorm p.1 (Encodable.encode p.2) = 2) :=
    (Primrec.eq.comp
      (evalNorm_prim.comp Primrec.fst (Primrec.encode.comp Primrec.snd))
      (Primrec.const 2)).decide
  exact h.to₂.of_eq fun l φ => by
    simp only [evalNorm, Encodable.encode, LO.Propositional.Formula.ofNat_toNat φ]
    cases BoolPCWorld.eval (BoolPCWorld.bitsWorld l) φ <;> simp

/-! ### The stage quantifier

`stageSort` is `Finset.sort` under `sentenceCodeLE`, which is the order the stock
`Finset Sentence` encoding already sorts by (Mathlib's `encodeMultiset`
sorts by its private `enle = encode ⁻¹'o (· ≤ ·)`, which `sentenceCodeLE` matches
definitionally, instances included).  So a stage's code *is* the code of its `stageSort`,
by `rfl`, and the compiled test recovers the list by decoding — no sorting is performed and
no `Finset` operation needs compiling.

None of this is semantic: `mem_stageSort` pins `stageSatBits` to `∀ φ ∈ stage` regardless
of the order, so the choice buys compilability only. -/

/-- A stage's Gödel code is exactly the code of its sorted sentence list. -/
lemma encode_eq_encode_stageSort (stage : Finset Sentence) :
    Encodable.encode stage = Encodable.encode (stageSort stage) := rfl

/-- A finite sentence set given as a list's `toFinset` has the code of the canonical
sorted, duplicate-free list.  Every stage-encoding computability proof in the
`Construction/` lanes reduces its stage encoder to this shape. -/
lemma encode_toFinset_eq (l : List Sentence) :
    Encodable.encode l.toFinset =
      Encodable.encode ((sentenceDedup l).insertionSort sentenceCodeLE) := by
  classical
  let canonical := (sentenceDedup l).insertionSort sentenceCodeLE
  have hnodup : canonical.Nodup :=
    (List.perm_insertionSort sentenceCodeLE _).nodup_iff.mpr (sentenceDedup_nodup l)
  have hsorted : canonical.Pairwise sentenceCodeLE :=
    List.pairwise_insertionSort sentenceCodeLE _
  have htoFinset : canonical.toFinset = l.toFinset := by
    ext φ; simp [canonical, mem_sentenceDedup]
  have hsort : l.toFinset.sort sentenceCodeLE = canonical := by
    rw [← htoFinset]
    exact (List.toFinset_sort (r := sentenceCodeLE) hnodup).mpr hsorted
  rw [encode_eq_encode_stageSort l.toFinset]
  exact congrArg Encodable.encode hsort

lemma stageSort_prim : Primrec stageSort := by
  have h : Primrec fun stage : Finset Sentence =>
      (Encodable.decode (α := List Sentence) (Encodable.encode stage)).getD [] :=
    Primrec.option_getD.comp (Primrec.decode.comp Primrec.encode) (Primrec.const [])
  exact h.of_eq fun stage => by
    rw [encode_eq_encode_stageSort, Encodable.encodek, Option.getD_some]

private lemma list_all_eq_foldr {α : Type} (l : List α) (p : α → Bool) :
    l.all p = l.foldr (fun a r => p a && r) true := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [List.all_cons, ih]

/-- **The stage quantifier is primitive recursive.**  Closes `evalBits_prim` over the
stage's sentence list. -/
lemma stageSatBits_prim : Primrec₂ stageSatBits := by
  have hstep : Primrec₂ fun (p : Finset Sentence × List Bool) (x : Sentence × Bool) =>
      BoolPCWorld.eval (BoolPCWorld.bitsWorld p.2) x.1 && x.2 :=
    (Primrec.and.comp
      (evalBits_prim.comp (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  have h := Primrec.list_foldr
    (f := fun p : Finset Sentence × List Bool => stageSort p.1)
    (g := fun _ : Finset Sentence × List Bool => true)
    (stageSort_prim.comp Primrec.fst) (Primrec.const true) hstep
  exact h.to₂.of_eq fun stage l => by
    simp only [stageSatBits, list_all_eq_foldr]

/-! ### The world enumeration -/

/-- **The bit-list enumeration is primitive recursive.**  A plain `Nat.rec` — this is the
one leaf that needed no `Sentence` machinery at all. -/
lemma allBitLists_prim : Primrec allBitLists := by
  have hstep : Primrec₂ fun (_ : ℕ) (prev : List (List Bool)) =>
      prev.flatMap (fun l => [false :: l, true :: l]) := by
    have hg : Primrec₂ fun (_ : ℕ × List (List Bool)) (l : List Bool) =>
        [false :: l, true :: l] :=
      (Primrec.list_cons.comp
        (Primrec.list_cons.comp (Primrec.const false) Primrec.snd)
        (Primrec.list_cons.comp
          (Primrec.list_cons.comp (Primrec.const true) Primrec.snd)
          (Primrec.const []))).to₂
    exact (Primrec.list_flatMap Primrec.snd hg).to₂
  have h : Primrec (Nat.rec (motive := fun _ => List (List Bool)) [[]]
      (fun _ prev => prev.flatMap (fun l => [false :: l, true :: l]))) :=
    Primrec.nat_rec₁ _ hstep
  exact h.of_eq fun n => by
    induction n with
    | zero => rfl
    | succ k ih => simp only [allBitLists, ← ih]

/-! ### The affine combination and its support bound -/

/-- `AffineCombination` is a plain pair of its two fields; `EF`, `Sentence` and `List`
already have `Primcodable` instances, so the structure inherits one through the equiv. -/
def affineEquiv : AffineCombination ≃ EF × List (EF × Sentence) where
  toFun A := (A.const, A.terms)
  invFun p := ⟨p.1, p.2⟩
  left_inv := fun ⟨_, _⟩ => rfl
  right_inv := fun ⟨_, _⟩ => rfl

instance affineCombinationPrimcodable : Primcodable AffineCombination :=
  Primcodable.ofEquiv _ affineEquiv

lemma affineEquiv_prim : Primrec affineEquiv := Primrec.of_equiv

lemma affineConst_prim : Primrec AffineCombination.const :=
  Primrec.fst.comp affineEquiv_prim

lemma affineTerms_prim : Primrec AffineCombination.terms :=
  Primrec.snd.comp affineEquiv_prim

/-! ### Polynomial affine sequences are primitive recursive

`PolySequence` exposes each feature as a polynomially emitted serialization rather than an
opaque encoded `EF`.  Reconstruct the token list via `PolySegStream.primrec`, then reuse the
existing primitive-recursive trade-stream decoder to invert `EF.serialize`. -/

private def serializationMarkerSentence : Sentence :=
  LO.Propositional.Formula.atom 0

/-- Decode one serialized feature by appending a dummy trade frame and reusing the canonical
trade-stream decoder.  Malformed streams totalize to the zero feature. -/
def efFromSerializedTokens (tokens : List ℕ) : EF :=
  match deserializeTrades
      (tokens ++ [6, Encodable.encode serializationMarkerSentence]) with
  | some ((e, _) :: _) => e
  | _ => EF.const 0

lemma efFromSerializedTokens_prim : Primrec efFromSerializedTokens := by
  have hframe : Primrec fun tokens : List ℕ =>
      tokens ++ [6, Encodable.encode serializationMarkerSentence] :=
    Primrec.list_append.comp Primrec.id
      (Primrec.const [6, Encodable.encode serializationMarkerSentence])
  have hdecode : Primrec fun tokens : List ℕ =>
      deserializeTrades (tokens ++ [6, Encodable.encode serializationMarkerSentence]) :=
    deserializeTrades_prim.comp hframe
  have hsome : Primrec₂ fun (_ : List ℕ) (trades : List (EF × Sentence)) =>
      match trades with
      | [] => EF.const 0
      | (e, _) :: _ => e :=
    (Primrec.list_casesOn Primrec.snd (Primrec.const (EF.const 0))
      (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)).to₂).to₂.of_eq
        fun _ trades => by cases trades <;> rfl
  exact (Primrec.option_casesOn hdecode (Primrec.const (EF.const 0)) hsome).of_eq
    fun tokens => by
      unfold efFromSerializedTokens
      cases deserializeTrades
          (tokens ++ [6, Encodable.encode serializationMarkerSentence]) with
      | none => rfl
      | some trades => cases trades <;> rfl

lemma efFromSerializedTokens_serialize (e : EF) :
    efFromSerializedTokens e.serialize = e := by
  unfold efFromSerializedTokens
  rw [show e.serialize ++ [6, Encodable.encode serializationMarkerSentence] =
      serializeTrades [(e, serializationMarkerSentence)] by
    simp [serializeTrades]]
  rw [deserializeTrades_serializeTrades]

/-- The operational polynomial interface on an affine family entails ordinary primitive
recursiveness of the family.  This closes the representation bridge needed by concrete
settlement and maturity checkers. -/
lemma AffineCombination.PolySequence.primrec {As : ℕ → AffineCombination}
    (h : PolySequence As) : Primrec As := by
  have hcount : Primrec h.termCount := by
    obtain ⟨c, hc⟩ := h.termCount_poly
    exact hc.primrec
  have hconstTokens : Primrec fun n => (As n).const.serialize := by
    obtain ⟨s, hs, hcontract⟩ := h.const_poly
    exact (unRpn_prim.comp hs.primrec).of_eq fun n =>
      (hcontract n).unRpn_eq
  have hconst : Primrec fun n => (As n).const :=
    (efFromSerializedTokens_prim.comp hconstTokens).of_eq fun n =>
      efFromSerializedTokens_serialize (As n).const
  have hcoefficientTokens : Primrec fun z => (h.coefficient z).serialize := by
    obtain ⟨s, hs, hcontract⟩ := h.coefficient_poly
    exact (unRpn_prim.comp hs.primrec).of_eq fun z =>
      (hcontract z).unRpn_eq
  have hcoefficient : Primrec h.coefficient :=
    (efFromSerializedTokens_prim.comp hcoefficientTokens).of_eq fun z =>
      efFromSerializedTokens_serialize (h.coefficient z)
  have hsentenceCode : Primrec fun z => Encodable.encode (h.sentence z) := by
    obtain ⟨s, hs, hp⟩ := h.sentence_poly
    have hlist := hs.primrec
    have hparse : Primrec fun z => parseRpnC (s z).length (s z) :=
      parseRpnC_prim.comp (Primrec.list_length.comp hlist) hlist
    refine (Primrec.fst.comp (Primrec.option_getD.comp hparse
      (Primrec.const ((0, []) : ℕ × List ℕ)))).of_eq fun z => ?_
    rw [show parseRpnC (s z).length (s z) =
        some (Encodable.encode (h.sentence z), []) by
      rw [parseRpnC_eq, hp z]; rfl]
    rfl
  have hsentence : Primrec h.sentence := by
    have hdecode : Primrec fun z =>
        (Encodable.decode (Encodable.encode (h.sentence z))).getD
          serializationMarkerSentence :=
      Primrec.option_getD.comp (Primrec.decode.comp hsentenceCode)
        (Primrec.const serializationMarkerSentence)
    exact hdecode.of_eq fun z => by rw [Encodable.encodek]; rfl
  have hrange : Primrec fun n => List.range (h.termCount n) :=
    Primrec.list_range.comp hcount
  have hterm : Primrec₂ fun n j =>
      (h.coefficient (Nat.pair n j), h.sentence (Nat.pair n j)) :=
    ((hcoefficient.comp Primrec₂.natPair).pair
      (hsentence.comp Primrec₂.natPair)).to₂
  have htermsRaw : Primrec fun n =>
      (List.range (h.termCount n)).map fun j =>
        (h.coefficient (Nat.pair n j), h.sentence (Nat.pair n j)) :=
    Primrec.list_map hrange hterm
  have hterms : Primrec fun n => (As n).terms :=
    htermsRaw.of_eq fun n => (h.terms_eq n).symm
  exact (Primrec.of_equiv_symm.comp (hconst.pair hterms)).of_eq fun n => by
    exact affineEquiv.left_inv (As n)

/-- A `Finset` sum is the sum over `stageSort`: `Finset.sort_eq` says the sorted list is a
list representation of the underlying multiset, so no reordering argument is needed. -/
lemma finset_sum_eq_stageSort_sum (stage : Finset Sentence) (f : Sentence → ℕ) :
    stage.sum f = ((stageSort stage).map f).sum := by
  have h : (stageSort stage : Multiset Sentence) = stage.val := Finset.sort_eq _ _
  rw [Finset.sum_eq_multiset_sum, ← h]
  simp

/-- `settlementAtomLimit` over the sorted stage list rather than the `Finset`. -/
lemma settlementAtomLimit_eq_stageSort (A : AffineCombination) (stage : Finset Sentence) :
    A.settlementAtomLimit stage =
      ((stageSort stage).map BoolPCWorld.atomBound).sum +
        (A.terms.map (fun p => BoolPCWorld.atomBound p.2)).sum := by
  rw [AffineCombination.settlementAtomLimit,
    finset_sum_eq_stageSort_sum stage BoolPCWorld.atomBound]

/-- Mathlib's `Primrec` API has no `list_sum`; `List.sum` is a `foldr`. -/
private lemma list_sum_prim : Primrec (fun l : List ℕ => l.sum) := by
  have h := Primrec.list_foldr (f := fun l : List ℕ => l) (g := fun _ : List ℕ => 0)
    Primrec.id (Primrec.const 0)
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂
  exact h.of_eq fun l => by
    induction l with
    | nil => rfl
    | cons a t ih => simp [List.sum_cons, ← ih]

/-- **The support bound is primitive recursive.** -/
lemma settlementAtomLimit_prim :
    Primrec₂ AffineCombination.settlementAtomLimit := by
  have hstage : Primrec fun p : AffineCombination × Finset Sentence =>
      ((stageSort p.2).map BoolPCWorld.atomBound).sum :=
    list_sum_prim.comp
      (Primrec.list_map (stageSort_prim.comp Primrec.snd)
        (atomBound_prim.comp Primrec.snd).to₂)
  have hterms : Primrec fun p : AffineCombination × Finset Sentence =>
      (p.1.terms.map (fun q => BoolPCWorld.atomBound q.2)).sum :=
    list_sum_prim.comp
      (Primrec.list_map (affineTerms_prim.comp Primrec.fst)
        (atomBound_prim.comp (Primrec.snd.comp Primrec.snd)).to₂)
  exact (Primrec.nat_add.comp hstage hterms).to₂.of_eq fun A stage =>
    (settlementAtomLimit_eq_stageSort A stage).symm

/-! ### The fuel layer over the market's quote table

Everything above is `Primrec`.  `valueRat` is not, and cannot be: it calls `EF.denoteRat Q`
where `Q` is the *market*, which a program reaches only through `market.quoteAtFuel`.  So
the checker is a fuel-clocked program rather than a primitive recursive function — which is
exactly the shape `SettlementChecker.spec` asks for (`∃ F, acceptsWithin code F ⟨i,j⟩`).

This mirrors `Strategy.valueRatListAtFuel` (`ROI.lean`) exactly: a three-part
sound/mono/exists-fuel contract over the existing `EF.denoteRatWithAtFuel`.

`AffineCombination.valueRatAtFuel` folds `EF.denoteRatWithAtFuel` — an `EF` recursion that
hits the market at each `price` leaf — so the settlement check is computable only once that
evaluator is.  Rather than compile a fourth `EF`-code recursion, the compiler reuses the
total EF rational stack machine (`efRatCompiledEval`, `LIACompiler.lean`) with the **total** quote
table `totalQuote fuel n φ := (market.quoteAtFuel fuel n φ).getD 0`.

That table is total: it reads `0` for an *unanswered* query, so on its own it cannot tell a
timeout from a genuine `0`.  The `readyAtFuel` guard — every syntactic `priceQueries` cell
of `e` has terminated — is what makes it sound: behind the guard `denoteRatComp` agrees
exactly with the partial `denoteRatWithAtFuel` (`denoteRatComp_eq`); without it, two worlds
could spuriously agree at `0` and certify a false settlement test.  This is why
`efPriceQueries_prim` (`LIACompiler.lean`) is load-bearing, not bookkeeping. -/

/-- Congruence: `denoteRatWith` depends on the price table only at its own price queries. -/
lemma EF.denoteRatWith_congr (e : EF) (ρ : List ℚ) (V₁ V₂ : ℕ → Sentence → ℚ)
    (h : ∀ q ∈ e.priceQueries, V₁ q.1 q.2 = V₂ q.1 q.2) :
    e.denoteRatWith ρ V₁ = e.denoteRatWith ρ V₂ := by
  induction e generalizing ρ with
  | price φ n => exact h (n, φ) (by simp [EF.priceQueries])
  | const q => rfl
  | add a b iha ihb | mul a b iha ihb | max a b iha ihb =>
      have ha := iha ρ (fun q hq => h q (by
        simp only [EF.priceQueries, List.mem_append]; exact Or.inl hq))
      have hb := ihb ρ (fun q hq => h q (by
        simp only [EF.priceQueries, List.mem_append]; exact Or.inr hq))
      simp [EF.denoteRatWith, ha, hb]
  | safeRecip a iha =>
      have ha := iha ρ (fun q hq => h q (by simpa only [EF.priceQueries] using hq))
      simp [EF.denoteRatWith, ha]
  | var i => rfl
  | letE value body ihvalue ihbody =>
      have hvalue := ihvalue ρ (fun q hq => h q (by
        simp only [EF.priceQueries, List.mem_append]; exact Or.inl hq))
      have hbody := ihbody (value.denoteRatWith ρ V₁ :: ρ)
        (fun q hq => h q (by simp only [EF.priceQueries, List.mem_append]; exact Or.inr hq))
      simp only [EF.denoteRatWith]
      rw [hbody, hvalue]

/-- Success of bounded evaluation implies every price query terminated at that clock. -/
lemma EF.denoteRatWithAtFuel_isSome_of_some {P : History}
    (market : MarketComputation P) (fuel : ℕ) (e : EF) (ρ : List ℚ) {q : ℚ}
    (h : e.denoteRatWithAtFuel market fuel ρ = some q) :
    ∀ query ∈ e.priceQueries, (market.quoteAtFuel fuel query.1 query.2).isSome := by
  induction e generalizing ρ q with
  | price φ n =>
      intro query hq
      simp only [EF.priceQueries, List.mem_singleton] at hq
      subst hq
      simp only [EF.denoteRatWithAtFuel] at h
      rw [h]; rfl
  | const c => intro query hq; simp [EF.priceQueries] at hq
  | add a b iha ihb | mul a b iha ihb | max a b iha ihb =>
      simp only [EF.denoteRatWithAtFuel, Option.bind_eq_bind] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨qa, ha, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨qb, hb, _⟩ := h
      intro query hq
      simp only [EF.priceQueries, List.mem_append] at hq
      rcases hq with hq | hq
      · exact iha ρ ha query hq
      · exact ihb ρ hb query hq
  | safeRecip a iha =>
      simp only [EF.denoteRatWithAtFuel, Option.bind_eq_bind] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨qa, ha, _⟩ := h
      intro query hq
      simp only [EF.priceQueries] at hq
      exact iha ρ ha query hq
  | var i => intro query hq; simp [EF.priceQueries] at hq
  | letE value body ihvalue ihbody =>
      simp only [EF.denoteRatWithAtFuel, Option.bind_eq_bind] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨qv, hv, hbody⟩ := h
      intro query hq
      simp only [EF.priceQueries, List.mem_append] at hq
      rcases hq with hq | hq
      · exact ihvalue ρ hv query hq
      · exact ihbody (qv :: ρ) hbody query hq

/-- The total quote table: substitutes `0` for an unanswered query (safe only behind the
`readyAtFuel` guard). -/
def MarketComputation.totalQuote {P : History} (market : MarketComputation P) (fuel : ℕ) :
    ℕ → Sentence → ℚ :=
  fun n φ => (market.quoteAtFuel fuel n φ).getD 0

/-- Every price query of `e` has terminated at this clock. -/
def MarketComputation.readyAtFuel {P : History} (market : MarketComputation P) (fuel : ℕ)
    (e : EF) : Bool :=
  e.priceQueries.all fun q => (market.quoteAtFuel fuel q.1 q.2).isSome

/-- Computable bounded EF evaluator: the total EF rational machine, gated by readiness. -/
def MarketComputation.denoteRatComp {P : History} (market : MarketComputation P) (fuel : ℕ)
    (e : EF) : Option ℚ :=
  if market.readyAtFuel fuel e then
    some (efRatCompiledEval market.totalQuote fuel e)
  else none

/-- **The bridge.**  The gated total machine computes exactly the partial bounded semantics
(at `ρ = []`). -/
lemma MarketComputation.denoteRatComp_eq {P : History} (market : MarketComputation P)
    (fuel : ℕ) (e : EF) :
    market.denoteRatComp fuel e = e.denoteRatWithAtFuel market fuel [] := by
  unfold MarketComputation.denoteRatComp
  by_cases hready : market.readyAtFuel fuel e
  · rw [if_pos hready]
    unfold MarketComputation.readyAtFuel at hready
    rw [List.all_eq_true] at hready
    have hready' : ∀ query ∈ e.priceQueries,
        market.quoteAtFuel fuel query.1 query.2 =
          some (market.quote query.1 (Encodable.encode query.2)) := by
      intro query hq
      have hs := hready query hq
      rw [Option.isSome_iff_exists] at hs
      obtain ⟨v, hv⟩ := hs
      rw [hv, market.quoteAtFuel_sound hv]
    rw [e.denoteRatWithAtFuel_complete market fuel [] hready', efRatCompiledEval_eq]
    congr 1
    rw [EF.denoteRat]
    apply EF.denoteRatWith_congr
    intro query hq
    unfold MarketComputation.totalQuote
    rw [hready' query hq]; rfl
  · rw [if_neg hready]
    unfold MarketComputation.readyAtFuel at hready
    rw [List.all_eq_true] at hready
    cases hd : e.denoteRatWithAtFuel market fuel [] with
    | none => rfl
    | some q =>
        exact absurd (fun query hq =>
          e.denoteRatWithAtFuel_isSome_of_some market fuel [] hd query hq) hready

/-- `readyAtFuel` is primitive recursive in `(fuel, e)` for a fixed market. -/
lemma MarketComputation.readyAtFuel_prim {P : History} (market : MarketComputation P) :
    Primrec₂ fun fuel e => market.readyAtFuel fuel e := by
  have hstep : Primrec₂ fun (p : ℕ × EF) (x : (ℕ × Sentence) × Bool) =>
      (market.quoteAtFuel p.1 x.1.1 x.1.2).isSome && x.2 :=
    (Primrec.and.comp
      (Primrec.option_isSome.comp
        ((quoteAtFuel_prim market).comp
          ((Primrec.fst.comp Primrec.fst).pair (Primrec.fst.comp Primrec.snd))))
      (Primrec.snd.comp Primrec.snd)).to₂
  have h := Primrec.list_foldr
    (f := fun p : ℕ × EF => p.2.priceQueries)
    (g := fun _ : ℕ × EF => true)
    (efPriceQueries_prim.comp Primrec.snd) (Primrec.const true) hstep
  exact h.to₂.of_eq fun fuel e => by
    simp only [MarketComputation.readyAtFuel, list_all_eq_foldr]

/-- `denoteRatComp` is primitive recursive in `(fuel, e)` for a fixed market. -/
lemma MarketComputation.denoteRatComp_prim {P : History} (market : MarketComputation P) :
    Primrec₂ fun fuel e => market.denoteRatComp fuel e := by
  have hV : Primrec fun p : ℕ × (ℕ × Sentence) =>
      market.totalQuote p.1 p.2.1 p.2.2 :=
    Primrec.option_getD.comp
      ((quoteAtFuel_prim market).comp (Primrec.fst.pair Primrec.snd)) (Primrec.const 0)
  have heval : Primrec fun p : ℕ × EF =>
      efRatCompiledEval market.totalQuote p.1 p.2 :=
    efRatCompiledEval_prim market.totalQuote hV
  have hite : Primrec fun p : ℕ × EF =>
      if market.readyAtFuel p.1 p.2 = true then
        some (efRatCompiledEval market.totalQuote p.1 p.2) else none :=
    Primrec.ite (Primrec.eq.comp
        ((market.readyAtFuel_prim).comp Primrec.fst Primrec.snd) (Primrec.const true))
      (Primrec.option_some.comp heval) (Primrec.const none)
  exact hite.to₂.of_eq fun fuel e => by
    simp only [MarketComputation.denoteRatComp]

/-! ### P-generable rational sequences are computable (`def:ece`)

`GeneratedRatFeature` presents a rational sequence only through a *market-dependent* feature
progression, while an arithmetic quote code has to **emit** a sentence naming the numeral
`q n` — which takes a program.  Both halves of that program are already above: the emitted
serialization parses back to the feature (`efFromSerializedTokens`, the same step
`AffineCombination.PolySequence.primrec` uses on coefficients), and the parsed feature
evaluates exactly against the certified market at one interpreter clock
(`MarketComputation.denoteRatComp`, sound and complete through
`EF.denoteRatWithAtFuel`).  What remains is to minimize over the clock.

Evaluation is genuinely unbounded — it dovetails the market program, whose runtime the day
index does not bound — so the certificate is `Computable`, not `PolyFueled`.  That is
exactly what a `Nat.Partrec.Code` quote code consumes. -/

/-- A feature progression emitted as an RPN-spliceable serialization stream is primitive
recursive as a whole-value function. -/
lemma BigSpliceStream.feature_primrec {feature : ℕ → EF}
    (h : BigSpliceStream fun n => (feature n).serialize) : Primrec feature := by
  obtain ⟨s, hs, hcontract⟩ := h
  have htokens : Primrec fun n => (feature n).serialize := by
    exact (unRpn_prim.comp hs.primrec).of_eq fun n =>
      (hcontract n).unRpn_eq
  exact (efFromSerializedTokens_prim.comp htokens).of_eq fun n =>
    efFromSerializedTokens_serialize (feature n)

/-- **A P-generable rational sequence (`def:ece`) is computable against the certified
market.**  This is the bridge the arithmetic quote codes need in order to accept
market-dependent thresholds: `def:ece` hands over only a feature stream, and emitting
`⌜… > q n⌝` requires a program computing `q n`.

Proof kind `C` (composition).  Provenance: the parse step is
`BigSpliceStream.feature_primrec` (a); the evaluation step is minimization of
`MarketComputation.denoteRatComp` over the interpreter clock, pinned by
`EF.denoteRatWithAtFuel_sound`/`_complete` and
`MarketComputation.exists_fuel_quoteAtFuel_list` (a); the bridge from `EF.denote` to
`EF.denoteRat` is `EF.denote_eq_ratCast` against `MarketComputation.quote_exact` (a).
Paper node: `def:ece` -/
lemma PGenerableRat.computable {P : History} (market : MarketComputation P) {q : ℕ → ℚ}
    (h : PGenerableRat P q) : Computable q := by
  obtain ⟨feature, hfeature⟩ := h
  have hfp : Primrec feature :=
    BigSpliceStream.feature_primrec hfeature.polyTok
  have hval : ∀ n, (feature n).denoteRat
      (fun day φ => market.quote day (Encodable.encode φ)) = q n := by
    intro n
    have hcast := EF.denote_eq_ratCast (feature n) P
      (fun day φ => market.quote day (Encodable.encode φ))
      (fun day φ => market.quote_exact day φ)
    rw [hfeature.denote n] at hcast
    exact_mod_cast hcast.symm
  -- Soundness of one accepted clock, and existence of an accepting clock.
  have hsound : ∀ n fuel r, market.denoteRatComp fuel (feature n) = some r → r = q n := by
    intro n fuel r hr
    rw [market.denoteRatComp_eq] at hr
    rw [(feature n).denoteRatWithAtFuel_sound market fuel [] hr, ← EF.denoteRat, hval n]
  have hexists : ∀ n, ∃ fuel, market.denoteRatComp fuel (feature n) = some (q n) := by
    intro n
    obtain ⟨fuel, hfuel⟩ := market.exists_fuel_quoteAtFuel_list (feature n).priceQueries
    refine ⟨fuel, ?_⟩
    rw [market.denoteRatComp_eq,
      (feature n).denoteRatWithAtFuel_complete market fuel [] hfuel, ← EF.denoteRat, hval n]
  let guard : ℕ → ℕ → Option ℕ := fun n fuel =>
    (market.denoteRatComp fuel (feature n)).map Encodable.encode
  have hguard : Computable₂ guard := by
    have hpacked : Primrec fun p : ℕ × ℕ => market.denoteRatComp p.2 (feature p.1) :=
      (market.denoteRatComp_prim).comp Primrec.snd (hfp.comp Primrec.fst)
    exact (Primrec.option_map hpacked
      (Primrec.encode.comp Primrec.snd).to₂).to₂.to_comp
  have hsearch : Partrec fun n => Nat.rfindOpt (guard n) := Partrec.rfindOpt hguard
  refine Computable.encode_iff.mp (hsearch.of_eq_tot ?_)
  intro n
  obtain ⟨fuel, hfuel⟩ := hexists n
  have hdom : (Nat.rfindOpt (guard n)).Dom := by
    rw [Nat.rfindOpt_dom]
    exact ⟨fuel, Encodable.encode (q n), by simp [guard, hfuel]⟩
  have hout : (Nat.rfindOpt (guard n)).get hdom ∈ Nat.rfindOpt (guard n) :=
    Part.get_mem hdom
  obtain ⟨fuel', hfuel'⟩ := Nat.rfindOpt_spec hout
  obtain ⟨r, hr, hrEq⟩ := Option.map_eq_some_iff.mp hfuel'
  rw [show Encodable.encode (q n) = (Nat.rfindOpt (guard n)).get hdom by
    rw [← hrEq, hsound n fuel' r hr]]
  exact hout

/-- Bounded exact evaluator for an affine combination's term list. -/
def affineTermsRatAtFuel {P : History} (market : MarketComputation P)
    (fuel : ℕ) (w : Sentence → ℚ) : List (EF × Sentence) → Option ℚ
  | [] => some 0
  | p :: rest => do
      let coefficient ← p.1.denoteRatWithAtFuel market fuel []
      let tail ← affineTermsRatAtFuel market fuel w rest
      pure (coefficient * w p.2 + tail)

/-- Bounded exact evaluator for `AffineCombination.valueRat`. -/
def AffineCombination.valueRatAtFuel (A : AffineCombination)
    {P : History} (market : MarketComputation P) (fuel : ℕ)
    (w : Sentence → ℚ) : Option ℚ := do
  let c ← A.const.denoteRatWithAtFuel market fuel []
  let ts ← affineTermsRatAtFuel market fuel w A.terms
  pure (c + ts)

lemma affineTermsRatAtFuel_sound {P : History} (market : MarketComputation P)
    (fuel : ℕ) (w : Sentence → ℚ) (terms : List (EF × Sentence)) {q : ℚ}
    (h : affineTermsRatAtFuel market fuel w terms = some q) :
    q = (terms.map (fun p =>
      p.1.denoteRat (fun d φ => market.quote d (Encodable.encode φ)) * w p.2)).sum := by
  induction terms generalizing q with
  | nil => simpa [affineTermsRatAtFuel] using h.symm
  | cons p rest ih =>
      simp only [affineTermsRatAtFuel, Option.bind_eq_bind] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨coefficient, hcoefficient, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨tail, htail, hq⟩ := h
      change some (coefficient * w p.2 + tail) = some q at hq
      injection hq with hq
      subst q
      simp only [List.map_cons, List.sum_cons, EF.denoteRat]
      rw [p.1.denoteRatWithAtFuel_sound market fuel [] hcoefficient, ih htail]
      rfl

lemma affineTermsRatAtFuel_mono {P : History} (market : MarketComputation P)
    {fuel fuel' : ℕ} (w : Sentence → ℚ) (terms : List (EF × Sentence)) {q : ℚ}
    (hff : fuel ≤ fuel')
    (h : affineTermsRatAtFuel market fuel w terms = some q) :
    affineTermsRatAtFuel market fuel' w terms = some q := by
  induction terms generalizing q with
  | nil => simpa [affineTermsRatAtFuel] using h
  | cons p rest ih =>
      simp only [affineTermsRatAtFuel, Option.bind_eq_bind] at h ⊢
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨coefficient, hcoefficient, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨tail, htail, hq⟩ := h
      rw [p.1.denoteRatWithAtFuel_mono market [] hff hcoefficient, Option.bind_eq_some_iff]
      exact ⟨coefficient, rfl, by rw [ih htail, Option.bind_eq_some_iff]; exact ⟨tail, rfl, hq⟩⟩

lemma exists_fuel_affineTermsRatAtFuel {P : History} (market : MarketComputation P)
    (w : Sentence → ℚ) (terms : List (EF × Sentence)) :
    ∃ fuel, affineTermsRatAtFuel market fuel w terms = some ((terms.map (fun p =>
      p.1.denoteRat (fun d φ => market.quote d (Encodable.encode φ)) * w p.2)).sum) := by
  induction terms with
  | nil => exact ⟨0, rfl⟩
  | cons p rest ih =>
      obtain ⟨f1, h1⟩ := EF.exists_fuel_denoteRatWithAtFuel market p.1 []
      obtain ⟨f2, h2⟩ := ih
      refine ⟨max f1 f2, ?_⟩
      simp only [affineTermsRatAtFuel, Option.bind_eq_bind]
      rw [EF.denoteRatWithAtFuel_mono market p.1 [] (le_max_left _ _) h1,
        Option.bind_eq_some_iff]
      refine ⟨_, rfl, ?_⟩
      rw [affineTermsRatAtFuel_mono market w rest (le_max_right _ _) h2,
        Option.bind_eq_some_iff]
      exact ⟨_, rfl, by simp [EF.denoteRat]⟩

lemma AffineCombination.valueRatAtFuel_sound (A : AffineCombination) {P : History}
    (market : MarketComputation P) (fuel : ℕ) (w : Sentence → ℚ) {q : ℚ}
    (h : A.valueRatAtFuel market fuel w = some q) :
    q = A.valueRat (fun d φ => market.quote d (Encodable.encode φ)) w := by
  simp only [AffineCombination.valueRatAtFuel, Option.bind_eq_bind] at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨c, hc, h⟩ := h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨ts, hts, hq⟩ := h
  change some (c + ts) = some q at hq
  injection hq with hq
  subst q
  rw [AffineCombination.valueRat, EF.denoteRat,
    A.const.denoteRatWithAtFuel_sound market fuel [] hc,
    affineTermsRatAtFuel_sound market fuel w A.terms hts]

lemma AffineCombination.valueRatAtFuel_mono (A : AffineCombination) {P : History}
    (market : MarketComputation P) {fuel fuel' : ℕ} (w : Sentence → ℚ) {q : ℚ}
    (hff : fuel ≤ fuel') (h : A.valueRatAtFuel market fuel w = some q) :
    A.valueRatAtFuel market fuel' w = some q := by
  simp only [AffineCombination.valueRatAtFuel, Option.bind_eq_bind] at h ⊢
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨c, hc, h⟩ := h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨ts, hts, hq⟩ := h
  rw [A.const.denoteRatWithAtFuel_mono market [] hff hc, Option.bind_eq_some_iff]
  exact ⟨c, rfl, by
    rw [affineTermsRatAtFuel_mono market w A.terms hff hts, Option.bind_eq_some_iff]
    exact ⟨ts, rfl, hq⟩⟩

lemma AffineCombination.exists_fuel_valueRatAtFuel (A : AffineCombination) {P : History}
    (market : MarketComputation P) (w : Sentence → ℚ) :
    ∃ fuel, A.valueRatAtFuel market fuel w =
      some (A.valueRat (fun d φ => market.quote d (Encodable.encode φ)) w) := by
  obtain ⟨f1, h1⟩ := EF.exists_fuel_denoteRatWithAtFuel market A.const []
  obtain ⟨f2, h2⟩ := exists_fuel_affineTermsRatAtFuel market w A.terms
  refine ⟨max f1 f2, ?_⟩
  simp only [AffineCombination.valueRatAtFuel, Option.bind_eq_bind]
  rw [EF.denoteRatWithAtFuel_mono market A.const [] (le_max_left _ _) h1,
    Option.bind_eq_some_iff]
  refine ⟨_, rfl, ?_⟩
  rw [affineTermsRatAtFuel_mono market w A.terms (le_max_right _ _) h2,
    Option.bind_eq_some_iff]
  exact ⟨_, rfl, by simp [AffineCombination.valueRat, EF.denoteRat]⟩

/-- A single fuel serving finitely many payout tables at once. -/
lemma AffineCombination.exists_fuel_valueRatAtFuel_list (A : AffineCombination)
    {P : History} (market : MarketComputation P) (ws : List (Sentence → ℚ)) :
    ∃ fuel, ∀ w ∈ ws, A.valueRatAtFuel market fuel w =
      some (A.valueRat (fun d φ => market.quote d (Encodable.encode φ)) w) := by
  induction ws with
  | nil => exact ⟨0, by simp⟩
  | cons w rest ih =>
      obtain ⟨f1, h1⟩ := A.exists_fuel_valueRatAtFuel market w
      obtain ⟨f2, h2⟩ := ih
      refine ⟨max f1 f2, fun x hx => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact A.valueRatAtFuel_mono market x (le_max_left _ _) h1
      · exact A.valueRatAtFuel_mono market x (le_max_right _ _) (h2 x hx)

/-! ### The computable value evaluator at a bit-list world

`settlementCheckAtFuel` compares `valueRatAtFuel market fuel (bitsPayoutRat l)` across the
enumerated worlds `l`.  These recast that quantity through the computable `denoteRatComp`
(so the whole check is primitive recursive), with a proved equality back to the original. -/

/-- `bitsPayoutRat` is primitive recursive. -/
lemma bitsPayoutRat_prim :
    Primrec₂ fun (l : List Bool) (φ : Sentence) => BoolPCWorld.bitsPayoutRat l φ := by
  have heval : PrimrecPred fun p : List Bool × Sentence =>
      BoolPCWorld.eval (BoolPCWorld.bitsWorld p.1) p.2 = true :=
    Primrec.eq.comp (evalBits_prim.comp Primrec.fst Primrec.snd) (Primrec.const true)
  exact (Primrec.ite heval (Primrec.const 1) (Primrec.const 0)).to₂.of_eq
    fun l φ => rfl

/-- Computable form of the affine term fold at `w := bitsPayoutRat l`, using the gated
evaluator `denoteRatComp` in place of the partial `denoteRatWithAtFuel`. -/
def affineTermsRatComp {P : History} (market : MarketComputation P) (fuel : ℕ)
    (l : List Bool) (terms : List (EF × Sentence)) : Option ℚ :=
  terms.foldr (fun p acc =>
    (market.denoteRatComp fuel p.1).bind fun cf =>
      acc.map fun t => cf * BoolPCWorld.bitsPayoutRat l p.2 + t) (some 0)

lemma affineTermsRatComp_eq {P : History} (market : MarketComputation P) (fuel : ℕ)
    (l : List Bool) (terms : List (EF × Sentence)) :
    affineTermsRatComp market fuel l terms =
      affineTermsRatAtFuel market fuel (BoolPCWorld.bitsPayoutRat l) terms := by
  induction terms with
  | nil => rfl
  | cons p rest ih =>
      rw [affineTermsRatComp, List.foldr_cons, ← affineTermsRatComp, ih,
        market.denoteRatComp_eq, affineTermsRatAtFuel]
      cases EF.denoteRatWithAtFuel market fuel p.1 [] with
      | none => rfl
      | some cf =>
          cases affineTermsRatAtFuel market fuel (BoolPCWorld.bitsPayoutRat l) rest <;> rfl

/-- Computable form of `valueRatAtFuel` at `w := bitsPayoutRat l`. -/
def valueRatCompAt {P : History} (A : AffineCombination) (market : MarketComputation P)
    (fuel : ℕ) (l : List Bool) : Option ℚ :=
  (market.denoteRatComp fuel A.const).bind fun c =>
    (affineTermsRatComp market fuel l A.terms).map fun ts => c + ts

lemma valueRatCompAt_eq {P : History} (A : AffineCombination)
    (market : MarketComputation P) (fuel : ℕ) (l : List Bool) :
    valueRatCompAt A market fuel l =
      A.valueRatAtFuel market fuel (BoolPCWorld.bitsPayoutRat l) := by
  rw [valueRatCompAt, market.denoteRatComp_eq, affineTermsRatComp_eq,
    AffineCombination.valueRatAtFuel]
  cases A.const.denoteRatWithAtFuel market fuel [] with
  | none => rfl
  | some c =>
      cases affineTermsRatAtFuel market fuel (BoolPCWorld.bitsPayoutRat l) A.terms <;> rfl

section
-- See the module header on `Nat.sqrt` opacity.
attribute [local irreducible] Nat.sqrt

/-- The affine term fold is primitive recursive in `((A, fuel), l)`. -/
lemma affineTermsRatComp_prim {P : History} (market : MarketComputation P) :
    Primrec fun q : (AffineCombination × ℕ) × List Bool =>
      affineTermsRatComp market q.1.2 q.2 q.1.1.terms := by
  have hcf : Primrec fun z : ((AffineCombination × ℕ) × List Bool) ×
      ((EF × Sentence) × Option ℚ) =>
      market.denoteRatComp z.1.1.2 z.2.1.1 :=
    (market.denoteRatComp_prim).comp
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
  have hbody : Primrec₂ fun (w : (((AffineCombination × ℕ) × List Bool) ×
      ((EF × Sentence) × Option ℚ)) × ℚ) (t : ℚ) =>
      w.2 * BoolPCWorld.bitsPayoutRat w.1.1.2 w.1.2.1.2 + t :=
    (ratAdd_prim.comp
      (ratMul_prim.comp (Primrec.snd.comp Primrec.fst)
        (bitsPayoutRat_prim.comp
          (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
          (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))))
      Primrec.snd).to₂
  have hmap : Primrec₂ fun (z : ((AffineCombination × ℕ) × List Bool) ×
      ((EF × Sentence) × Option ℚ)) (cf : ℚ) =>
      z.2.2.map fun t => cf * BoolPCWorld.bitsPayoutRat z.1.2 z.2.1.2 + t :=
    (Primrec.option_map (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) hbody).to₂
  have hstep : Primrec₂ fun (q : (AffineCombination × ℕ) × List Bool)
      (x : (EF × Sentence) × Option ℚ) =>
      (market.denoteRatComp q.1.2 x.1.1).bind fun cf =>
        x.2.map fun t => cf * BoolPCWorld.bitsPayoutRat q.2 x.1.2 + t :=
    (Primrec.option_bind hcf hmap).to₂
  exact Primrec.list_foldr (affineTerms_prim.comp (Primrec.fst.comp Primrec.fst))
    (Primrec.const (some 0)) hstep

/-- `valueRatCompAt` is primitive recursive in `((A, fuel), l)`. -/
lemma valueRatCompAt_prim {P : History} (market : MarketComputation P) :
    Primrec fun q : (AffineCombination × ℕ) × List Bool =>
      valueRatCompAt q.1.1 market q.1.2 q.2 := by
  have hconst : Primrec fun q : (AffineCombination × ℕ) × List Bool =>
      market.denoteRatComp q.1.2 q.1.1.const :=
    (market.denoteRatComp_prim).comp (Primrec.snd.comp Primrec.fst)
      (affineConst_prim.comp (Primrec.fst.comp Primrec.fst))
  have hmap : Primrec₂ fun (q : (AffineCombination × ℕ) × List Bool) (c : ℚ) =>
      (affineTermsRatComp market q.1.2 q.2 q.1.1.terms).map fun ts => c + ts :=
    (Primrec.option_map ((affineTermsRatComp_prim market).comp Primrec.fst)
      (ratAdd_prim.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂).to₂
  exact (Primrec.option_bind hconst hmap).of_eq fun q => rfl

end

/-! ### The bounded settlement check

The analogue of `unitMaturityCheckAtFuel` (`Calibration.lean`) for settlement, and — unlike
that one — carried through to a `Primrec`-backed code below.  It is conservative: any
timeout (of the process program or of any market call) reads as `false`, so a `true` result
always certifies the real test. -/

/-- Tolerance agreement of two *possibly timed-out* market evaluations.  A timeout on
either side reads as failure, so a `true` result always certifies the real comparison. -/
def ratWithinOpt (v v' : Option ℚ) (tol : ℚ) : Bool :=
  (v.isSome && v'.isSome) && ratWithin (v.getD 0) (v'.getD 0) tol

lemma ratWithinOpt_eq_true_iff {v v' : Option ℚ} {tol : ℚ} :
    ratWithinOpt v v' tol = true ↔
      ∃ x y, v = some x ∧ v' = some y ∧ |x - y| ≤ tol := by
  cases v with
  | none => simp [ratWithinOpt]
  | some x =>
      cases v' with
      | none => simp [ratWithinOpt]
      | some y => simp [ratWithinOpt, ratWithin_eq_true_iff]

private lemma ratWithin_prim :
    Primrec fun p : (ℚ × ℚ) × ℚ => ratWithin p.1.1 p.1.2 p.2 := by
  have hx : Primrec fun p : (ℚ × ℚ) × ℚ => p.1.1 := Primrec.fst.comp Primrec.fst
  have hy : Primrec fun p : (ℚ × ℚ) × ℚ => p.1.2 := Primrec.snd.comp Primrec.fst
  have ht : Primrec fun p : (ℚ × ℚ) × ℚ => p.2 := Primrec.snd
  have h1 := (ratLE_prim.comp hx (ratAdd_prim.comp hy ht)).decide
  have h2 := (ratLE_prim.comp hy (ratAdd_prim.comp hx ht)).decide
  exact (Primrec.and.comp h1 h2).of_eq fun _ => rfl

private lemma ratWithinOpt_prim :
    Primrec fun p : (Option ℚ × Option ℚ) × ℚ => ratWithinOpt p.1.1 p.1.2 p.2 := by
  have hv : Primrec fun p : (Option ℚ × Option ℚ) × ℚ => p.1.1 :=
    Primrec.fst.comp Primrec.fst
  have hv' : Primrec fun p : (Option ℚ × Option ℚ) × ℚ => p.1.2 :=
    Primrec.snd.comp Primrec.fst
  have ht : Primrec fun p : (Option ℚ × Option ℚ) × ℚ => p.2 := Primrec.snd
  have hg : Primrec fun p : (Option ℚ × Option ℚ) × ℚ => p.1.1.getD 0 :=
    Primrec.option_getD.comp hv (Primrec.const 0)
  have hg' : Primrec fun p : (Option ℚ × Option ℚ) × ℚ => p.1.2.getD 0 :=
    Primrec.option_getD.comp hv' (Primrec.const 0)
  exact (Primrec.and.comp
    (Primrec.and.comp (Primrec.option_isSome.comp hv) (Primrec.option_isSome.comp hv'))
    (ratWithin_prim.comp ((hg.pair hg').pair ht))).of_eq fun _ => rfl

/-- The executable bounded settlement check.  Accepts only once the certified process
program has produced stage `j` and every market call needed by both worlds' values has
terminated, and then compares the two worlds' rational values within `tol`. -/
def AffineCombination.settlementCheckAtFuel (A : AffineCombination)
    {P : History} {DP : DeductiveProcess}
    (market : MarketComputation P) (process : DeductiveProcessComputation DP)
    (tol : ℚ) (j fuel : ℕ) : Bool :=
  match process.stageAtFuel fuel j with
  | none => false
  | some stage =>
      (allBitLists (A.settlementAtomLimit stage)).all fun l =>
        (allBitLists (A.settlementAtomLimit stage)).all fun l' =>
          !(stageSatBits stage l) || !(stageSatBits stage l') ||
            ratWithinOpt (A.valueRatAtFuel market fuel (BoolPCWorld.bitsPayoutRat l))
              (A.valueRatAtFuel market fuel (BoolPCWorld.bitsPayoutRat l')) tol

section
-- See the module header on `Nat.sqrt` opacity.
attribute [local irreducible] Nat.sqrt

/-- The bounded settlement check is primitive recursive in `(A, j, fuel)` for fixed
market and deductive-process computations.  The unbounded search for a successful fuel is
kept outside this function and is supplied by `Partrec.rfindOpt` below. -/
lemma AffineCombination.settlementCheckAtFuel_prim
    {P : History} {DP : DeductiveProcess}
    (market : MarketComputation P) (process : DeductiveProcessComputation DP) :
    Primrec fun q : AffineCombination × ℚ × ℕ × ℕ =>
      q.1.settlementCheckAtFuel market process q.2.1 q.2.2.1 q.2.2.2 := by
  let Q := AffineCombination × ℚ × ℕ × ℕ
  let S := Q × Finset Sentence
  let R := S × List Bool
  have hlimit : Primrec fun p : S => p.1.1.settlementAtomLimit p.2 :=
    settlementAtomLimit_prim.comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  have hworlds : Primrec fun p : S => allBitLists (p.1.1.settlementAtomLimit p.2) :=
    allBitLists_prim.comp hlimit
  have hsat : Primrec fun p : R => stageSatBits p.1.2 p.2 :=
    stageSatBits_prim.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  have hvalue : Primrec fun p : R =>
      valueRatCompAt p.1.1.1 market p.1.1.2.2.2 p.2 :=
    (valueRatCompAt_prim market).comp
      (((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
        (Primrec.snd.comp (Primrec.snd.comp
          (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))).pair
        Primrec.snd)
  have hagree : Primrec fun p : R × List Bool =>
      let v := valueRatCompAt p.1.1.1.1 market p.1.1.1.2.2.2 p.1.2
      let v' := valueRatCompAt p.1.1.1.1 market p.1.1.1.2.2.2 p.2
      ratWithinOpt v v' p.1.1.1.2.1 := by
    have hv : Primrec fun p : R × List Bool =>
        valueRatCompAt p.1.1.1.1 market p.1.1.1.2.2.2 p.1.2 :=
      hvalue.comp Primrec.fst
    have hv' : Primrec fun p : R × List Bool =>
        valueRatCompAt p.1.1.1.1 market p.1.1.1.2.2.2 p.2 :=
      hvalue.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)
    have htol : Primrec fun p : R × List Bool => p.1.1.1.2.1 :=
      Primrec.fst.comp (Primrec.snd.comp
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
    exact ratWithinOpt_prim.comp ((hv.pair hv').pair htol)
  have hcondition : Primrec fun p : R × List Bool =>
      (!stageSatBits p.1.1.2 p.1.2) || (!stageSatBits p.1.1.2 p.2) ||
        (let v := valueRatCompAt p.1.1.1.1 market p.1.1.1.2.2.2 p.1.2
         let v' := valueRatCompAt p.1.1.1.1 market p.1.1.1.2.2.2 p.2
         ratWithinOpt v v' p.1.1.1.2.1) := by
    have hs1 : Primrec fun p : R × List Bool => stageSatBits p.1.1.2 p.1.2 :=
      hsat.comp Primrec.fst
    have hs2 : Primrec fun p : R × List Bool => stageSatBits p.1.1.2 p.2 :=
      hsat.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)
    exact Primrec.or.comp
      (Primrec.or.comp (Primrec.not.comp hs1) (Primrec.not.comp hs2)) hagree
  have hinnerStep : Primrec₂ fun (r : R) (x : List Bool × Bool) =>
      ((!stageSatBits r.1.2 r.2) || (!stageSatBits r.1.2 x.1) ||
        (let v := valueRatCompAt r.1.1.1 market r.1.1.2.2.2 r.2
         let v' := valueRatCompAt r.1.1.1 market r.1.1.2.2.2 x.1
         ratWithinOpt v v' r.1.1.2.1)) && x.2 :=
    (Primrec.and.comp
      (hcondition.comp (Primrec.fst.pair (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd)).to₂
  have hinner : Primrec fun r : R =>
      (allBitLists (r.1.1.1.settlementAtomLimit r.1.2)).foldr
        (fun l' acc =>
          ((!stageSatBits r.1.2 r.2) || (!stageSatBits r.1.2 l') ||
            (let v := valueRatCompAt r.1.1.1 market r.1.1.2.2.2 r.2
             let v' := valueRatCompAt r.1.1.1 market r.1.1.2.2.2 l'
             ratWithinOpt v v' r.1.1.2.1)) && acc) true :=
    Primrec.list_foldr (hworlds.comp Primrec.fst) (Primrec.const true) hinnerStep
  have houterStep : Primrec₂ fun (s : S) (x : List Bool × Bool) =>
      ((allBitLists (s.1.1.settlementAtomLimit s.2)).foldr
        (fun l' acc =>
          ((!stageSatBits s.2 x.1) || (!stageSatBits s.2 l') ||
            (let v := valueRatCompAt s.1.1 market s.1.2.2.2 x.1
             let v' := valueRatCompAt s.1.1 market s.1.2.2.2 l'
             ratWithinOpt v v' s.1.2.1)) && acc) true) && x.2 :=
    (Primrec.and.comp
      (hinner.comp (Primrec.fst.pair (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd)).to₂
  have houter : Primrec fun s : S =>
      (allBitLists (s.1.1.settlementAtomLimit s.2)).foldr
        (fun l acc =>
          ((allBitLists (s.1.1.settlementAtomLimit s.2)).foldr
            (fun l' acc' =>
              ((!stageSatBits s.2 l) || (!stageSatBits s.2 l') ||
                (let v := valueRatCompAt s.1.1 market s.1.2.2.2 l
                 let v' := valueRatCompAt s.1.1 market s.1.2.2.2 l'
                 ratWithinOpt v v' s.1.2.1)) && acc') true) && acc) true :=
    Primrec.list_foldr hworlds (Primrec.const true) houterStep
  have hstage : Primrec fun q : Q => process.stageAtFuel q.2.2.2 q.2.2.1 :=
    processStageAtFuel_prim process |>.comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have hcompiled : Primrec fun q : Q =>
      match process.stageAtFuel q.2.2.2 q.2.2.1 with
      | none => false
      | some stage =>
          (allBitLists (q.1.settlementAtomLimit stage)).foldr
            (fun l acc =>
              ((allBitLists (q.1.settlementAtomLimit stage)).foldr
                (fun l' acc' =>
                  ((!stageSatBits stage l) || (!stageSatBits stage l') ||
                    (let v := valueRatCompAt q.1 market q.2.2.2 l
                     let v' := valueRatCompAt q.1 market q.2.2.2 l'
                     ratWithinOpt v v' q.2.1)) && acc') true) && acc) true :=
    (Primrec.option_casesOn hstage (Primrec.const false)
      (houter.comp (Primrec.fst.pair Primrec.snd)).to₂).of_eq fun q => by
        cases process.stageAtFuel q.2.2.2 q.2.2.1 <;> rfl
  exact hcompiled.of_eq fun q => by
    unfold AffineCombination.settlementCheckAtFuel
    cases hst : process.stageAtFuel q.2.2.2 q.2.2.1 with
    | none => rfl
    | some stage =>
        simp only
        rw [list_all_eq_foldr]
        apply congrArg (fun f : List Bool → Bool → Bool =>
          List.foldr f true (allBitLists (q.1.settlementAtomLimit stage)))
        funext l acc
        rw [list_all_eq_foldr]
        apply congrArg₂ (fun x y => x && y) _ rfl
        apply congrArg (fun f : List Bool → Bool → Bool =>
          List.foldr f true (allBitLists (q.1.settlementAtomLimit stage)))
        funext l' acc'
        rw [valueRatCompAt_eq, valueRatCompAt_eq]

end

lemma AffineCombination.settlementCheckAtFuel_sound (A : AffineCombination)
    {P : History} {DP : DeductiveProcess}
    (market : MarketComputation P) (process : DeductiveProcessComputation DP)
    {tol : ℚ} {j fuel : ℕ}
    (h : A.settlementCheckAtFuel market process tol j fuel = true) :
    A.SettlementTestBool (fun d φ => market.quote d (Encodable.encode φ))
      (DP.D j) tol = true := by
  unfold AffineCombination.settlementCheckAtFuel at h
  cases hstage : process.stageAtFuel fuel j with
  | none => rw [hstage] at h; exact absurd h (by simp)
  | some stage =>
      rw [hstage] at h
      obtain rfl : stage = DP.D j := process.stageAtFuel_sound hstage
      rw [List.all_eq_true] at h
      rw [AffineCombination.SettlementTestBool, List.all_eq_true]
      intro l hl
      rw [List.all_eq_true]
      intro l' hl'
      have hb := List.all_eq_true.mp (h l hl) l' hl'
      -- Both worlds satisfy the stage, or the disjunction is already discharged.
      cases ha : stageSatBits (DP.D j) l
      · simp
      cases ha' : stageSatBits (DP.D j) l'
      · simp
      rw [ha, ha'] at hb
      simp only [Bool.not_true, Bool.false_or] at hb ⊢
      -- The check certifies both market evaluations terminated and agreed within `tol`.
      obtain ⟨v, v', hv, hv', hclose⟩ := ratWithinOpt_eq_true_iff.1 hb
      rw [ratWithin_eq_true_iff, ← A.valueRatAtFuel_sound market fuel _ hv,
        ← A.valueRatAtFuel_sound market fuel _ hv']
      exact hclose

lemma AffineCombination.settlementCheckAtFuel_complete (A : AffineCombination)
    {P : History} {DP : DeductiveProcess}
    (market : MarketComputation P) (process : DeductiveProcessComputation DP)
    (tol : ℚ) (j : ℕ)
    (h : A.SettlementTestBool (fun d φ => market.quote d (Encodable.encode φ))
      (DP.D j) tol = true) :
    ∃ fuel, A.settlementCheckAtFuel market process tol j fuel = true := by
  obtain ⟨f0, h0⟩ := process.stageAtFuel_complete j
  obtain ⟨f1, h1⟩ := A.exists_fuel_valueRatAtFuel_list market
    ((allBitLists (A.settlementAtomLimit (DP.D j))).map BoolPCWorld.bitsPayoutRat)
  refine ⟨max f0 f1, ?_⟩
  unfold AffineCombination.settlementCheckAtFuel
  rw [process.stageAtFuel_mono (le_max_left _ _) h0]
  rw [AffineCombination.SettlementTestBool, List.all_eq_true] at h
  rw [List.all_eq_true]
  intro l hl
  rw [List.all_eq_true]
  intro l' hl'
  have hb := List.all_eq_true.mp (h l hl) l' hl'
  -- Both payout tables are in the list the common fuel was chosen for.
  have hv := A.valueRatAtFuel_mono market (fuel := f1) (fuel' := max f0 f1)
    (BoolPCWorld.bitsPayoutRat l) (le_max_right f0 f1)
    (h1 _ (List.mem_map_of_mem hl))
  have hv' := A.valueRatAtFuel_mono market (fuel := f1) (fuel' := max f0 f1)
    (BoolPCWorld.bitsPayoutRat l') (le_max_right f0 f1)
    (h1 _ (List.mem_map_of_mem hl'))
  rw [hv, hv']
  exact hb

/-! ### Extracting the settlement checker code -/

/-- Market and deductive-process computations determine a concrete code semi-deciding the
named settlement predicate for every polynomial affine family.  The only unbounded operation
is `rfindOpt` over fuel; soundness and completeness come from the bounded check above.
Paper node: `def:ec` -/
noncomputable def SettlementChecker.ofComputations
    {As : ℕ → AffineCombination} {P : History} {DP : DeductiveProcess}
    (hpoly : AffineCombination.PolySequence As)
    (market : MarketComputation P) (process : DeductiveProcessComputation DP)
    {tol : ℕ → ℚ} (htol : Primrec tol) :
    SettlementChecker As (fun d φ => market.quote d (Encodable.encode φ)) DP tol := by
  have hAs : Primrec As := hpoly.primrec
  have hcheck : Primrec₂ fun (z fuel : ℕ) =>
      (As z.unpair.1).settlementCheckAtFuel market process (tol z.unpair.1)
        z.unpair.2 fuel := by
    have hidx : Primrec fun p : ℕ × ℕ => p.1.unpair.1 :=
      Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)
    have hinput : Primrec fun p : ℕ × ℕ =>
        (As p.1.unpair.1, tol p.1.unpair.1, p.1.unpair.2, p.2) :=
      (hAs.comp hidx).pair ((htol.comp hidx).pair
        ((Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)).pair Primrec.snd))
    exact ((AffineCombination.settlementCheckAtFuel_prim market process).comp hinput).to₂
  let guard : ℕ → ℕ → Option ℕ := fun z fuel =>
    if (As z.unpair.1).settlementCheckAtFuel market process (tol z.unpair.1)
        z.unpair.2 fuel then
      some 1
    else
      none
  have hguard : Computable₂ guard := by
    have hp : Primrec fun p : ℕ × ℕ =>
        if (As p.1.unpair.1).settlementCheckAtFuel market process (tol p.1.unpair.1)
            p.1.unpair.2 p.2 then
          some 1
        else
          none := by
      exact Primrec.ite
        (Primrec.eq.comp hcheck (Primrec.const true))
        (Primrec.const (some 1)) (Primrec.const (none : Option ℕ))
    exact hp.to₂.to_comp
  have hpart : Partrec fun z => Nat.rfindOpt (guard z) :=
    Partrec.rfindOpt hguard
  have hnat : Nat.Partrec fun z => Nat.rfindOpt (guard z) :=
    Partrec.nat_iff.mp hpart
  let code := Classical.choose (Nat.Partrec.Code.exists_code.mp hnat)
  have hcode : Nat.Partrec.Code.eval code = fun z => Nat.rfindOpt (guard z) :=
    Classical.choose_spec (Nat.Partrec.Code.exists_code.mp hnat)
  refine ⟨code, fun i j => ?_⟩
  constructor
  · rintro ⟨fuel, haccept⟩
    have hevaln : Nat.Partrec.Code.evaln fuel code (Nat.pair i j) = some 1 := by
      cases he : Nat.Partrec.Code.evaln fuel code (Nat.pair i j) with
      | none =>
          simp [acceptsWithin, codeEvalnNat, he] at haccept
      | some out =>
          simp [acceptsWithin, codeEvalnNat, he] at haccept
          obtain rfl : out = 1 := by omega
          rfl
    have hmem : 1 ∈ Nat.rfindOpt (guard (Nat.pair i j)) := by
      have : 1 ∈ Nat.Partrec.Code.eval code (Nat.pair i j) :=
        Nat.Partrec.Code.evaln_sound hevaln
      rw [hcode] at this
      exact this
    obtain ⟨fuel', hfuel'⟩ := Nat.rfindOpt_spec hmem
    have hcheckTrue :
        (As i).settlementCheckAtFuel market process (tol i) j fuel' = true := by
      simpa [guard] using hfuel'
    exact (As i).settlementCheckAtFuel_sound market process hcheckTrue
  · intro htest
    obtain ⟨fuel, hfuel⟩ :=
      (As i).settlementCheckAtFuel_complete market process (tol i) j htest
    have hdom : (Nat.rfindOpt (guard (Nat.pair i j))).Dom := by
      rw [Nat.rfindOpt_dom]
      exact ⟨fuel, 1, by simp [guard, hfuel]⟩
    have hone : 1 ∈ Nat.rfindOpt (guard (Nat.pair i j)) := by
      have hout := Part.get_mem hdom
      obtain ⟨fuel', hfuel'⟩ := Nat.rfindOpt_spec hout
      have houtEq : (Nat.rfindOpt (guard (Nat.pair i j))).get hdom = 1 := by
        have hp : (As i).settlementCheckAtFuel market process (tol i) j fuel' = true ∧
            1 = (Nat.rfindOpt (guard (Nat.pair i j))).get hdom := by
          simpa [guard] using hfuel'
        exact hp.2.symm
      rw [houtEq] at hout
      exact hout
    have hmem : 1 ∈ Nat.Partrec.Code.eval code (Nat.pair i j) := by
      rw [hcode]
      exact hone
    obtain ⟨fuel', hevaln⟩ := Nat.Partrec.Code.evaln_complete.mp hmem
    refine ⟨fuel', ?_⟩
    change Nat.Partrec.Code.evaln fuel' code (Nat.pair i j) = some 1 at hevaln
    simp [acceptsWithin, codeEvalnNat, hevaln]

/-- The patient settlement clock with its checker constructed from the supplied market and
deductive-process programs.  No computability bridge or checker remains as a hypothesis.
Paper node: `def:ec` -/
noncomputable def PatientSettlementClock.ofComputations
    {As : ℕ → AffineCombination} {P : History} {DP : DeductiveProcess}
    {truth e err : ℕ → ℝ} {tol : ℕ → ℚ}
    (hpoly : AffineCombination.PolySequence As)
    (market : MarketComputation P) (process : DeductiveProcessComputation DP)
    (hdet : AffineCombination.ApproxDeterminedViaTheory As P DP truth e)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (htolPrim : Primrec tol)
    (hreach : ∀ i, ∃ m, ∀ v w : PCWorld, v.ConsistentWith (DP.D m) →
      w.ConsistentWith (DP.D m) →
      |(As i).value P v.payout - (As i).value P w.payout| ≤ ((tol i : ℚ) : ℝ))
    (herr : ∀ i, ((tol i : ℚ) : ℝ) + e i ≤ err i)
    (f : DeferralFunction) :
    PatientSettlementClock As P DP truth err f :=
  PatientSettlementClock.ofChecker
    (SettlementChecker.ofComputations hpoly market process htolPrim) hdet
    market.quote_exact hworld hreach herr f

end SettlementCompile

end LogicalInduction
