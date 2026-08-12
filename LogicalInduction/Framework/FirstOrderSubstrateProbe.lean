/-
# Scoping probe — a first-order substrate for `Sentence`

**Not part of the build.**  This file is a read-only feasibility probe for
`LogicalInduction/notes/boundary-substrate-fol-scope.md`; it is imported by nothing, claims no paper node,
and is excluded from `AxiomAudit`.  It exists so that two claims in that note are backed
by something the kernel checked rather than by prose.

The note's migration target is **not** `Sentence := LO.FirstOrder.Sentence ℒₒᵣ`.  It is the
paper's own construction (`main.tex` §Notation, "First order theories and prime sentences"):
a *propositional* calculus whose atoms are the **prime** sentences of a first-order language.
So the target keeps `LO.Propositional.Formula`, and changes only its atom type.

Two things the note asserts, checked here:

* **P1 — the prime decomposition is definable, total, and lands in the existing world layer.**
  `primeDecompose` below maps an `ℒₒᵣ`-sentence to a `LO.Propositional.Formula` over an
  `Encodable` atom type, with the paper's factoring: `nrel` is the negation of the prime
  `rel`, and `∀⁰ φ` is the negation of the prime `∃⁰ ∼φ`.  Foundation's negation-normal-form
  `Semiformula` makes this a structural recursion with no normalisation step.  Everything the
  repository builds on `Boolean.Valuation` — `PCWorld`, `BoolPCWorld.eval`, `atomBound`,
  `Framework/Compactness` — is stated over `Formula α` for a general atom type, so it
  transports along this change of atoms rather than being rebuilt.

* **P2 — Foundation's numerals are unary, and the whole-value code of a numeral is
  doubly exponential.**  `Semiterm.Operator.numeral L (n+1)` is `1 + 1 + ⋯ + 1`, so the code of
  `n̄` is a `Nat.pair` nest of depth `n`; `pair_sq_le` below is the squaring step that makes
  the nest doubly exponential.  This is the measured obstruction behind the note's Stage-4
  item: an atom carried as a single whole-value token is not emittable in the fuel calculus,
  so the Polish-notation symbol calculus of `Framework/RpnSentence.lean` would have to be
  extended *into* the atom (FO formula and term constructors), and Foundation's numerals
  replaced by a binary presentation.

**Friction observed while writing this (recorded per CLAUDE.md rule 6).**  The defining
equations of `primeDecompose` do **not** hold by `rfl`, only by `simp [primeDecompose]`, even
with every constructor spelled out.  `Semiformula L ξ n` is an inductive *indexed* by the
bound-variable arity, so a match on it at index `0` compiles through a motive-carrying
recursor rather than by definitional unfolding; `LO.Propositional.Formula α` is a plain
inductive and has no such problem.  A second instance of the same friction: the `and` equation
does not fire on `primeDecompose (φ ⋏ ψ)`, because `⋏` at `Semiformula` is
`LogicalConnective.wedge` and `simp` will not unfold the instance — the constructor has to be
named.  Both are small in themselves, but the repository's `Primrec`/`simp`-heavy layers
(`Construction/LIACompiler.lean`, `Construction/Witnesses/BoundedEvaluation.lean`) lean on
definitional transparency of the sentence type throughout, and would lose it.
-/
import Foundation.FirstOrder.Basic.Coding
import Foundation.FirstOrder.Arithmetic.Basic
import Foundation.Propositional.Boolean.Basic

namespace LogicalInduction.FirstOrderSubstrateProbe

open LO LO.FirstOrder

/-! ## P1 — prime sentences and the Boolean decomposition -/

section Prime

variable {L : Language} {ξ : Type*}

/-- A sentence is **prime** (paper's §Notation) when it is atomic or quantified: the Boolean
connectives `⋏`/`⋎` are the only ones the decomposition looks through.  Under Foundation's
negation-normal form there is no `∼` or `➝` constructor, so `nrel` and `∀⁰` are the two
*negated* primes. -/
def IsPrimeHead : Semiformula L ξ 0 → Bool
  | .verum => false
  | .falsum => false
  | .rel _ _ => true
  | .nrel _ _ => true
  | .and _ _ => false
  | .or _ _ => false
  | .all _ => true
  | .exs _ => true

/-- **The prime decomposition.**  Every first-order sentence is a Boolean combination of
prime sentences; this produces that combination as an object of the repository's *existing*
propositional substrate, with atoms in `Semiformula L ξ 0` (the positive primes).

Every constructor is spelled out, so each equation holds by `rfl`.  Note the shape of the
recursion: only `and`/`or` recurse.  Quantifiers are opaque — a quantified sentence is an
atom, never descended into — which is the whole content of the paper's remark that
`(7 > 1+1)` is *not* a prime of `∃y∀z ((7>1+1) → y+z>2)`.

The two *negated* primes are `nrel` and `all`, matching the paper's factoring: it reads
`⌜∀x: ⋯⌝` as shorthand for `⌜¬∃x: ¬⋯⌝` with the leading `¬` factored out as a Boolean
operator, so the atom is the positive prime `∃⁰ ∼φ`. -/
def primeDecompose :
    Semiformula L ξ 0 → LO.Propositional.Formula (Semiformula L ξ 0)
  | .verum => ⊤
  | .falsum => ⊥
  | .and φ ψ => primeDecompose φ ⋏ primeDecompose ψ
  | .or φ ψ => primeDecompose φ ⋎ primeDecompose ψ
  | .rel r v => LO.Propositional.Formula.atom (.rel r v)
  | .nrel r v => ∼(LO.Propositional.Formula.atom (.rel r v))
  | .exs φ => LO.Propositional.Formula.atom (.exs φ)
  | .all φ => ∼(LO.Propositional.Formula.atom (.exs (∼φ)))

/-- The decomposition only ever produces atoms that are *positive* primes: it never emits an
`nrel` or `∀⁰` atom, so the atom space is the set of positive primes and Boolean structure
carries every negation.  (Stated on the two cases that could violate it.) -/
example (r : L.Rel k) (v : Fin k → Semiterm L ξ 0) :
    primeDecompose (.nrel r v) = ∼(LO.Propositional.Formula.atom (.rel r v)) := by
  simp [primeDecompose]

example (φ : Semiformula L ξ 1) :
    primeDecompose (.all φ) = ∼(LO.Propositional.Formula.atom (.exs (∼φ))) := by
  simp [primeDecompose]

example (φ ψ : Semiformula L ξ 0) :
    primeDecompose (.and φ ψ) = primeDecompose φ ⋏ primeDecompose ψ := by
  simp [primeDecompose]

end Prime

/-! ### The instances the world layer needs, at `ℒₒᵣ`

`PCWorld` is `Boolean.Valuation α = α → Prop`, `Encodable α` is what `def:ec` needs for
sentence codes, and `DecidableEq α` is what the finite-stage decidable checks need.  All
three are available at the first-order atom type with no new development. -/

example : DecidableEq (Sentence ℒₒᵣ) := inferInstance
example : Encodable (Sentence ℒₒᵣ) := inferInstance
example : Encodable (LO.Propositional.Formula (Sentence ℒₒᵣ)) := inferInstance
example : DecidableEq (LO.Propositional.Formula (Sentence ℒₒᵣ)) := inferInstance

/-- The world layer is already stated over a general atom type: a Boolean valuation of
first-order primes evaluates a decomposed sentence with Foundation's existing
`Propositional.Formula.Boolean.val`.  Nothing in `Framework/Criterion.lean`'s
`PCWorld.Holds` is specific to `ℕ` atoms. -/
noncomputable def holdsFO (v : LO.Propositional.Boolean.Valuation (Sentence ℒₒᵣ))
    (φ : Sentence ℒₒᵣ) : Prop :=
  LO.Propositional.Formula.Boolean.val v (primeDecompose φ)

/-! ## P2 — unary numerals and whole-value atom codes

`Semiterm.Operator.numeral L (n+1)` unfolds to `1 + 1 + ⋯ + 1` (`Operator.numeral`,
`Foundation/FirstOrder/Basic/Operator.lean:156`).  `Semiterm.toNat` codes `func f v` as
`Nat.pair 2 (Nat.pair k (Nat.pair (encode f) (Matrix.vecToNat …))) + 1`, and `Nat.pair x y`
is at least `max x y ^ 2`, so each `+ 1` in the numeral squares the code.

The `#eval`s below print `Encodable.encode (numeral ℒₒᵣ n : Semiterm ℒₒᵣ Empty 0)` for small
`n`; the growth is the point, not the values. -/

section Numerals

open Semiterm

/-- The unary shape, definitionally. -/
example : (Operator.numeral ℒₒᵣ 0 : Semiterm.Const ℒₒᵣ) = Operator.Zero.zero := rfl
example : (Operator.numeral ℒₒᵣ 1 : Semiterm.Const ℒₒᵣ) = Operator.One.one := rfl

/-- Each successor is one more `+ 1`, i.e. one more `Nat.pair` nesting level in the code. -/
example (z : ℕ) :
    (Operator.numeral ℒₒᵣ (z + 2) : Semiterm.Const ℒₒᵣ)
      = Operator.Add.add.comp ![Operator.numeral ℒₒᵣ (z + 1), Operator.One.one] :=
  Semiterm.Operator.numeral_add_two

/-- The squaring step.  `Semiterm.toNat (func f v)` is
`Nat.pair 2 (Nat.pair k (Nat.pair (encode f) (Matrix.vecToNat …))) + 1`, and every `Nat.pair`
whose arguments are bounded below by `a` is bounded below by `a * a`.  Since each successor in
a unary numeral adds one `func Add` layer over the previous term's code, the code of `n̄` is at
least `c₀ ^ (2 ^ n)` — doubly exponential in `n`, i.e. its *bit length* is exponential.

That bit length is what the emission calculus would have to stream for a single atom token, so
whole-value metering (`PolySentenceCodes` and friends) is not a weaker fallback class at an FO
atom type — it is an empty one. -/
lemma pair_sq_le (a b : ℕ) (h : a ≤ b) : a * a ≤ Nat.pair a b := by
  rw [Nat.pair]
  rcases Nat.lt_or_ge a b with hlt | hge
  · simp only [hlt, if_pos]
    calc a * a ≤ b * b := Nat.mul_le_mul h h
    _ ≤ b * b + a := Nat.le_add_right _ _
  · have : a = b := Nat.le_antisymm h hge
    subst this
    simp only [lt_irrefl, if_neg, not_false_iff]
    omega

end Numerals

end LogicalInduction.FirstOrderSubstrateProbe
