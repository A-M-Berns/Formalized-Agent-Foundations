import LogicalInduction.Construction.Witnesses.StructuredPaperRpn

/-!
# Machines that carry the day in their own source

A `def:ec` premise about a *machine sequence* is metered on what the trader writes down:
`DigitMachineCodes m` asks for poly-fueled digit access to `(m n).sourceNat`, the tag
stream of the machine's syntax tree read as a base-16 numeral
(`Framework/CodeSource.lean`).  Until now that class was witnessed only at families whose
day dependence is trivial or bespoke — constant families (`digitMachineCodes_const`) and
the spine family `Nat.Partrec.Code.nest` (`bigDigits_sourceNat_nest`), neither of which
*computes* anything about the day.

This module supplies the reusable day-varying witness.  `dayMachine F n` is Mathlib's
`Nat.Partrec.Code.curry F n`: the machine that runs `F` on the pair `⟨n, ·⟩`, so the day
number sits inside the machine's own source text as the `Code.const n` numeral.  Its tag
stream is therefore available in closed form (`sourceTags_dayMachine`) — `F`'s own stream,
two runs of `n` repeated tags, and a fixed five-tag frame — which is exactly the shape the
segment-stream emitters of `Framework/Computable.lean` produce.  Feeding that stream
through the base-16 write-out bridge discharges `def:ec` for the whole family at once
(`digitMachineCodes_dayMachine`), for *every* fixed `F`, with no bespoke digit-selector
chain.

Consumers wanting a day-varying halting or `theoryOf` family (e.g. the `thm:incons`
witnesses) can now take `F` to be whatever fixed machine implements the intended
computation and get the emission certificate for free.

Nothing here is paper-facing; the paper node discharged downstream is `def:ec`.
-/

namespace LogicalInduction

open Nat.Partrec (Code)

-- Deep `PolyFueled` compositions over paired inputs loop `whnf` on `Nat.sqrt`; keep it
-- opaque (the standing `dd:fuel` safeguard, as in `Framework/CodeSource.lean`).
attribute [local irreducible] Nat.sqrt

/-! ## The day machine -/

/-- **The day-`n` instance of a fixed machine**: Mathlib's `curry`, which feeds the day
number in as the first component of the input pair.  The day is therefore *inside the
source text*, as the `Code.const n` numeral.

Kind Def.  Provenance: (b) Mathlib citation — `Nat.Partrec.Code.curry`. -/
def dayMachine (F : Code) (n : ℕ) : Code :=
  Code.curry F n

/-- The day machine runs `F` on the pair `⟨n, i⟩`.

Kind C (composition).  Provenance: (b) Mathlib citation —
`Nat.Partrec.Code.eval_curry`. -/
lemma dayMachine_eval (F : Code) (n i : ℕ) :
    (dayMachine F n).eval i = F.eval (Nat.pair n i) :=
  Code.eval_curry F n i

/-- The written source of the constant-`n` machine: `n` `succ` tags, a `zero`, and `n`
`comp` tags, since `Code.const (k+1) = comp succ (Code.const k)`.

Kind P (proved, induction on `n`).  Provenance: (a) derived in-project from
`Nat.Partrec.Code.sourceTags`; (b) Mathlib citation — `Nat.Partrec.Code.const`. -/
lemma sourceTags_const : ∀ n : ℕ,
    Code.sourceTags (Code.const n) = List.replicate n 2 ++ [1] ++ List.replicate n 6
  | 0 => rfl
  | n + 1 => by
      have hstep : Code.sourceTags (Code.const (n + 1))
          = [2] ++ Code.sourceTags (Code.const n) ++ [6] := rfl
      rw [hstep, sourceTags_const n]
      simp only [List.replicate_succ, List.cons_append, List.nil_append, List.append_assoc,
        List.cons.injEq, true_and]
      -- residue: the `comp` run grows at the *right* end, so `replicate_succ'`, not
      -- `replicate_succ`, is the closing rewrite.
      rw [← List.replicate_succ', List.replicate_succ]

/-- The day-`n` machine's written source, in closed form: `F`'s own tag stream, then the
two runs of length `n` carrying the day, then a fixed five-tag frame
(`left`, `right`, `pair` for `Code.id`, then `pair` for the argument pair and `comp` for
the outer composition).

Kind P (proved).  Provenance: (a) derived in-project from `sourceTags_const` and
`Nat.Partrec.Code.sourceTags`; (b) Mathlib citation — `Nat.Partrec.Code.curry`,
`Nat.Partrec.Code.id`. -/
lemma sourceTags_dayMachine (F : Code) (n : ℕ) :
    Code.sourceTags (dayMachine F n)
      = Code.sourceTags F ++ List.replicate n 2 ++ [1]
          ++ List.replicate n 6 ++ [3, 4, 5, 5, 6] := by
  have hstep : Code.sourceTags (dayMachine F n)
      = Code.sourceTags F ++ (Code.sourceTags (Code.const n) ++ [3, 4, 5] ++ [5]) ++ [6] :=
    rfl
  rw [hstep, sourceTags_const n]
  simp [List.append_assoc]

/-- The little-endian digit list of `(dayMachine F n).sourceNat`: the reverse of the tag
stream, with the two day runs still contiguous.

Kind C (composition).  Provenance: (a) derived in-project from
`sourceTags_dayMachine`. -/
lemma sourceTags_dayMachine_reverse (F : Code) (n : ℕ) :
    (Code.sourceTags (dayMachine F n)).reverse
      = [6, 5, 5, 4, 3] ++ List.replicate n 6 ++ [1] ++ List.replicate n 2
          ++ (Code.sourceTags F).reverse := by
  rw [sourceTags_dayMachine]
  simp [List.reverse_append, List.reverse_replicate, List.append_assoc]

/-- Every entry of that digit list is a legal tag, hence below `16`.

Kind P (proved).  Provenance: (a) derived in-project from
`Nat.Partrec.Code.sourceTags_lt_16`. -/
lemma dayMachine_digits_lt_16 (F : Code) (n : ℕ) :
    ∀ d ∈ [6, 5, 5, 4, 3] ++ List.replicate n 6 ++ [1] ++ List.replicate n 2
        ++ (Code.sourceTags F).reverse, d < 16 := by
  intro d hd
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with ((((h | h) | h) | h) | h)
  · rcases h with h | h | h | h | h <;> omega
  · have := List.eq_of_mem_replicate h; omega
  · omega
  · have := List.eq_of_mem_replicate h; omega
  · exact (Code.sourceTags_lt_16 F d (List.mem_reverse.mp h)).2

/-- The digit list of the day machine's source is an efficiently emitted segment stream:
a fixed frame, a `repeatTag` run of length `n`, a fixed tag, a second `repeatTag` run of
length `n`, and `F`'s fixed tag stream.

Kind C (composition).  Provenance: (a) derived in-project from `PolySegStream.constList`,
`PolySegStream.repeatTag`, `PolySegStream.append` and `PolyFueled.id`. -/
lemma polySegStream_dayMachineDigits (F : Code) :
    PolySegStream (fun n => [6, 5, 5, 4, 3] ++ List.replicate n 6 ++ [1]
      ++ List.replicate n 2 ++ (Code.sourceTags F).reverse) :=
  ((((PolySegStream.constList [6, 5, 5, 4, 3]).append
      (PolySegStream.repeatTag 6 PolyFueled.id)).append
      (PolySegStream.constList [1])).append
      (PolySegStream.repeatTag 2 PolyFueled.id)).append
      (PolySegStream.constList (Code.sourceTags F).reverse)

/-- **The `def:ec` certificate**: the day machine's source is written out in time
polynomial in the day, for every fixed `F`.  This is the reusable day-varying witness for
`DigitMachineCodes`.

Kind C (composition).  Provenance: (a) derived in-project from
`polySegStream_dayMachineDigits`, `BigDigits.ofBase16PolySegStream` and
`sourceTags_dayMachine_reverse`. -/
lemma digitMachineCodes_dayMachine (F : Code) : DigitMachineCodes (dayMachine F) :=
  (BigDigits.ofBase16PolySegStream (polySegStream_dayMachineDigits F)
    (dayMachine_digits_lt_16 F)).of_eq (fun n => by
      rw [Code.sourceNat, sourceTags_dayMachine_reverse])

/-- Distinct days give distinct machines, hence distinct *names*: a claim family built
over `dayMachine` is genuinely day-varying.

Kind C (composition).  Provenance: (a) derived in-project from
`Nat.Partrec.Code.sourceNat_injective`; (b) Mathlib citation —
`Nat.Partrec.Code.curry_inj`. -/
lemma dayMachine_sourceNat_ne (F : Code) {m n : ℕ} (h : m ≠ n) :
    (dayMachine F m).sourceNat ≠ (dayMachine F n).sourceNat := by
  intro hEq
  exact h (Code.curry_inj (Code.sourceNat_injective hEq)).2

end LogicalInduction

#print axioms LogicalInduction.dayMachine
#print axioms LogicalInduction.dayMachine_eval
#print axioms LogicalInduction.sourceTags_const
#print axioms LogicalInduction.sourceTags_dayMachine
#print axioms LogicalInduction.sourceTags_dayMachine_reverse
#print axioms LogicalInduction.dayMachine_digits_lt_16
#print axioms LogicalInduction.polySegStream_dayMachineDigits
#print axioms LogicalInduction.digitMachineCodes_dayMachine
#print axioms LogicalInduction.dayMachine_sourceNat_ne
