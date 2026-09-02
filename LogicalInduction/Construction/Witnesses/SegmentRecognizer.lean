/-
# The freeze's run recognizer, with no condition on the target

`PatAuto.ifParse_mem_FP` decides "this word's run denotes `ψ`" for a `NoReserved` target.
The condition is not decoration: a reserved atom is *also* spelled by a structured
paper-prime block, whose unary length field must be matched against the payload's own token
count, and no finite-state device decides an `aⁿbⁿ` constraint.

This file removes the condition, by putting three pieces together.

* `StructPat.parseRpn_iff_segMatch` characterizes the full grammar unconditionally: a run
  denotes `ψ` exactly when it matches one of `ψ`'s finitely many *segment* patterns, a
  structured block being one segment.
* `SegAuto.segAuto` is a finite automaton for the **relaxed** language — everything except
  the length identification — with the payload recognized by `PayAuto`, whose obligation
  stack decides, exactly, which token strings denote one fixed formula code.
* `SegCtr.segCtr` is a one-counter machine for the length identification alone, and
  `SegCtr.segMatch_iff_relaxed_and_ctr` says the split is exact.

So the decision is a nest over the target's patterns, each level a conjunction of an
automaton test and a counter test, and each of those is `Complexity.FP`
(`RunAuto.BlockAutomaton.ifAuto_mem_FP`, `CtrAuto.ifCtr_mem_FP`).

The nest's shape matters for the freeze and is not an implementation detail: a run that
matches a pattern's *relaxed* language but fails the counter must still be tried against the
remaining patterns, because a single run can be a relaxed match for one pattern and an exact
match for another.  Hence the inner failure branch falls through to the tail rather than to
`Y`.

What comes out is `ifParseFull_mem_FP`, the unconditional replacement for
`PatAuto.ifParse_mem_FP`, and with it the last syntactic side condition on the corrected
finite-perturbation theorem disappears.
-/
import LogicalInduction.Construction.Witnesses.SegmentAutomaton
import LogicalInduction.Construction.Witnesses.SegmentCounter
import LogicalInduction.Construction.Witnesses.PayloadAutomaton
import LogicalInduction.Construction.Witnesses.FiberTestFP

namespace LogicalInduction.SegRec

open Complexity Complexity.Cobham LogicalInduction.FPFold LogicalInduction.TokenFold
open LogicalInduction.StructPat

-- The `Nat.pair`/`unpair` reachable from the sentence codec unfolds `Nat.sqrt`'s
-- well-founded definition during `whnf` and loops; local opacity stops that.
-- See `notes/lean-gotchas.md`.
attribute [local irreducible] Nat.sqrt

/-! ## The payload recognizer, as `SegAuto` asks for it -/

/-- **`PayAuto` inhabits `SegAuto.PayRec`.**

`SegAuto` is stated against an interface so that it could be built before the recognizer
existed; this is the only instance, and there is no reason for a second.

Kind `C` composition.  Provenance: (a) `PayAuto.payAuto_iff`, `PayAuto.payStep_le`,
`PayAuto.payInit_le`. -/
def payRec (fc : ℕ) : SegAuto.PayRec fc where
  Q := PayAuto.payQ fc
  init := PayAuto.payInit fc
  step := PayAuto.payStep fc
  accept := PayAuto.payAcceptState fc
  init_le := PayAuto.payInit_le fc
  step_le := PayAuto.payStep_le fc
  spec := PayAuto.payAuto_iff fc

/-! ## The exact test for one pattern -/

/-- **A run matches a pattern exactly when both machines accept it.**

The automaton checks the pattern's shape and every structured block's payload; the counter
checks every structured block's length field.  Neither alone is exact.

Proof kind: `C` composition.  Provenance: (a) `SegCtr.segMatch_iff_relaxed_and_ctr`,
`SegAuto.segAuto_accepts`, `PayAuto.nineteen_not_mem_of_parse`.
Paper node: `app:ifp` -/
lemma segMatch_iff_accepts (H : PatAuto.HoleGuards) (p : List PatSeg) (b : List ℕ) :
    SegMatch p b ↔
      (SegAuto.segAuto H payRec p).Accepts b = true ∧ (SegCtr.segCtr p).Accepts b = true := by
  rw [SegCtr.segMatch_iff_relaxed_and_ctr PayAuto.nineteen_not_mem_of_parse p b,
    SegAuto.segAuto_accepts H payRec p b]

/-! ## The nest over a target's patterns -/

/-- Take `X` as soon as one pattern matches, on both machines. -/
def segNest (H : PatAuto.HoleGuards) (S X Y : List Bool → List Bool) :
    List (List PatSeg) → List Bool → List Bool
  | [], z => Y z
  | p :: ps, z =>
      if (SegAuto.segAuto H payRec p).Accepts (decodeBits (S z)) = true then
        (if (SegCtr.segCtr p).Accepts (decodeBits (S z)) = true then X z
          else segNest H S X Y ps z)
      else segNest H S X Y ps z

lemma segNest_pos (H : PatAuto.HoleGuards) (S X Y : List Bool → List Bool) :
    ∀ (l : List (List PatSeg)) (z : List Bool),
      (∃ p ∈ l, SegMatch p (decodeBits (S z))) → segNest H S X Y l z = X z
  | [], z, hm => by obtain ⟨p, hp, -⟩ := hm; exact absurd hp (by simp)
  | (p :: l), z, hm => by
      rw [segNest]
      by_cases h : SegMatch p (decodeBits (S z))
      · obtain ⟨h₁, h₂⟩ := (segMatch_iff_accepts H p _).mp h
        rw [if_pos h₁, if_pos h₂]
      · have hfall : segNest H S X Y l z = X z := by
          refine segNest_pos H S X Y l z ?_
          obtain ⟨q, hq, hqm⟩ := hm
          rcases List.mem_cons.mp hq with hc | hc
          · exact absurd (hc ▸ hqm) h
          · exact ⟨q, hc, hqm⟩
        by_cases h₁ : (SegAuto.segAuto H payRec p).Accepts (decodeBits (S z)) = true
        · rw [if_pos h₁]
          have h₂ : ¬ (SegCtr.segCtr p).Accepts (decodeBits (S z)) = true :=
            fun hc => h ((segMatch_iff_accepts H p _).mpr ⟨h₁, hc⟩)
          rw [if_neg h₂]; exact hfall
        · rw [if_neg h₁]; exact hfall

lemma segNest_neg (H : PatAuto.HoleGuards) (S X Y : List Bool → List Bool) :
    ∀ (l : List (List PatSeg)) (z : List Bool),
      (¬ ∃ p ∈ l, SegMatch p (decodeBits (S z))) → segNest H S X Y l z = Y z
  | [], z, _ => by rw [segNest]
  | (p :: l), z, hm => by
      have hrest : segNest H S X Y l z = Y z :=
        segNest_neg H S X Y l z
          (fun hc => hm (by obtain ⟨q, hq, hqm⟩ := hc; exact ⟨q, List.mem_cons_of_mem _ hq, hqm⟩))
      have hp : ¬ SegMatch p (decodeBits (S z)) :=
        fun hc => hm ⟨p, List.mem_cons_self .., hc⟩
      rw [segNest]
      by_cases h₁ : (SegAuto.segAuto H payRec p).Accepts (decodeBits (S z)) = true
      · rw [if_pos h₁]
        have h₂ : ¬ (SegCtr.segCtr p).Accepts (decodeBits (S z)) = true :=
          fun hc => hp ((segMatch_iff_accepts H p _).mpr ⟨h₁, hc⟩)
        rw [if_neg h₂]; exact hrest
      · rw [if_neg h₁]; exact hrest

/-- The nest returns one of its two branches, whatever the outcome. -/
lemma segNest_cases (H : PatAuto.HoleGuards) (S X Y : List Bool → List Bool) :
    ∀ (l : List (List PatSeg)) (z : List Bool),
      segNest H S X Y l z = X z ∨ segNest H S X Y l z = Y z
  | [], z => by rw [segNest]; exact Or.inr rfl
  | (p :: l), z => by
      rw [segNest]
      split_ifs
      · exact Or.inl rfl
      · exact segNest_cases H S X Y l z
      · exact segNest_cases H S X Y l z

lemma segNest_mem_FP (H : PatAuto.HoleGuards) {S X Y : List Bool → List Bool}
    (hS : S ∈ FP) (hX : X ∈ FP) (hY : Y ∈ FP) :
    ∀ l : List (List PatSeg), (fun z => segNest H S X Y l z) ∈ FP
  | [] => by
      have heq : (fun z => segNest H S X Y [] z) = Y := by funext z; rw [segNest]
      rwa [heq]
  | (p :: l) => by
      have hrec := segNest_mem_FP H hS hX hY l
      have hinner := CtrAuto.ifCtr_mem_FP (SegCtr.segCtr p) hS hX hrec
      have h := (SegAuto.segAuto H payRec p).ifAuto_mem_FP hS hinner hrec
      have heq : (fun z =>
            if (SegAuto.segAuto H payRec p).Accepts (decodeBits (S z)) = true then
              (if (SegCtr.segCtr p).Accepts (decodeBits (S z)) = true then X z
                else segNest H S X Y l z)
            else segNest H S X Y l z)
          = fun z => segNest H S X Y (p :: l) z := by
        funext z; rw [segNest]
      rwa [heq] at h

/-! ## The decision the freeze asks for -/

/-- **Branching on "this word's run denotes `ψ`" is polynomial time — for every `ψ`.**

The unconditional replacement for `PatAuto.ifParse_mem_FP`.  No `BotFree`, no `NoReserved`,
no restriction of any kind on the target: the escape leaf's infinite decode fibre is decided
by `FiberTest`, the structured payload by `PayAuto`, and the structured length field by
`CtrAuto`.

Proof kind: `C` composition.  Provenance: (a) `segNest_pos`, `segNest_neg`,
`segNest_mem_FP`; (b) `StructPat.parseRpn_iff_segMatch`.
Paper node: `app:ifp` -/
lemma ifParseFull_mem_FP (H : PatAuto.HoleGuards) (ψ : Sentence)
    {S X Y : List Bool → List Bool} (hS : S ∈ FP) (hX : X ∈ FP) (hY : Y ∈ FP) :
    (fun z => if parseRpn (decodeBits (S z)).length (decodeBits (S z))
          = some (ψ, []) then X z else Y z) ∈ FP := by
  have h := segNest_mem_FP H hS hX hY (segPatterns ψ)
  have heq : (fun z => segNest H S X Y (segPatterns ψ) z)
      = fun z => if parseRpn (decodeBits (S z)).length (decodeBits (S z))
          = some (ψ, []) then X z else Y z := by
    funext z
    by_cases hp : parseRpn (decodeBits (S z)).length (decodeBits (S z)) = some (ψ, [])
    · rw [segNest_pos H S X Y _ z ((parseRpn_iff_segMatch ψ (decodeBits (S z))).mp hp),
        if_pos hp]
    · rw [segNest_neg H S X Y _ z
        (fun hc => hp ((parseRpn_iff_segMatch ψ (decodeBits (S z))).mpr hc)), if_neg hp]
  rwa [heq] at h

#print axioms LogicalInduction.SegRec.payRec
#print axioms LogicalInduction.SegRec.segMatch_iff_accepts
#print axioms LogicalInduction.SegRec.ifParseFull_mem_FP

end LogicalInduction.SegRec
