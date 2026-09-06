import LogicalInduction.Construction.Freeze.SegmentAutomaton
import LogicalInduction.Construction.Freeze.SegmentCounter
import LogicalInduction.Construction.Freeze.PayloadAutomaton
import LogicalInduction.Construction.Freeze.FiberTest

/-!
# The freeze's run recognizer, with no condition on the target

Renders `app:ifp` (tex:6018): the unconditional polynomial-time decision of "this word's run
denotes `ψ`", for every target.  `PatAuto.ifParse_mem_FP` decides the same question only for
a `NoReserved` target, and that condition is not decoration: a reserved atom is *also*
spelled by a structured paper-prime block, whose unary length field must be matched against
the payload's own token count, and no finite-state device decides an `aⁿbⁿ` constraint.

Three inputs remove it.

* `StructPat.parseRpn_iff_segMatch` characterizes the full grammar unconditionally: a run
  denotes `ψ` exactly when it matches one of `ψ`'s finitely many *segment* patterns, a
  structured block being one segment.
* `SegAuto.segAuto` is a finite automaton for the **relaxed** language — everything except
  the length identification — with the payload recognized by `PayAuto`, whose obligation
  stack decides, exactly, which token strings denote one fixed formula code.  `payRec`
  inhabits the `SegAuto.PayRec` interface and is its only instance.
* `SegCtr.segCtr` is a one-counter machine for the length identification alone, and
  `SegCtr.segMatch_iff_relaxed_and_ctr` says the split is exact.  `segMatch_iff_accepts` is
  the resulting exact test: a run matches a pattern exactly when both machines accept it,
  neither alone being exact.

`segNest` is the nest over the target's patterns, each level an automaton test conjoined
with a counter test, and each of those is `Complexity.FP`
(`RunAuto.BlockAutomaton.ifAuto_mem_FP`, `CtrAuto.ifCtr_mem_FP`).  The nest's shape is a
design fact, not an implementation detail: a run that matches a pattern's *relaxed* language
but fails the counter must still be tried against the remaining patterns, since one run can
be a relaxed match for one pattern and an exact match for another — hence the inner failure
branch falls through to the tail rather than to `Y`.

`ifParseFull_mem_FP` is the decision the freeze asks for, at the full grammar and with no
condition on the target; `FreezeOracle.machine_lic_iff_of_finiteSupport` consumes it.
`segMatch_iff_accepts` and `ifParseFull_mem_FP` are in `AxiomAudit.lean`.
-/

namespace LogicalInduction.SegRec

open Complexity Complexity.Cobham LogicalInduction.FPFold LogicalInduction.TokenFold
open LogicalInduction.StructPat

-- The `Nat.pair`/`unpair` reachable from the sentence codec unfolds `Nat.sqrt`'s
-- well-founded definition during `whnf` and loops; local opacity stops that.
-- See `notes/lean-gotchas.md`.
attribute [local irreducible] Nat.sqrt

/-! ## The payload recognizer, as `SegAuto` asks for it -/

/-- **`PayAuto` inhabits `SegAuto.PayRec`.**

`SegAuto.PayRec` is an interface so that the automaton is independent of the payload
recognizer's internals; `PayAuto` is its only instance.

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

No `BotFree`, no `NoReserved`, no restriction of any kind on the target: the escape leaf's
infinite decode fibre is decided by `FiberTest`, the structured payload by `PayAuto`, and the
structured length field by `CtrAuto`.  `PatAuto.ifParse_mem_FP` is the same decision under
`NoReserved`.

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

end LogicalInduction.SegRec
