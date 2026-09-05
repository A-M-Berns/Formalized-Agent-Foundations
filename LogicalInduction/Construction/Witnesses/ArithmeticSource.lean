import LogicalInduction.Construction.Witnesses.StructuredPaperRpn

/-!
# The paper's formula source language, and the literal LUV frontend over it

The paper writes arithmetic expressions over the primitive connectives `¬ ∧ ∨ ⟹ ⟺`
(tex:560) and the quantifiers `∀ ∃` (tex:568-573), and `def:ec` (tex:753) meters *the
formula as the paper writes it*.  Foundation's `Semiformula` is a negation-normal-form
datatype with no `⟺`, so the paper's writing and Foundation's normal form are metered on
two layers; `dd:nnf` is that design decision, and this module is where the paper's layer
lives.

`ArithSource k` is the paper's own formula *source*, with `not`/`imp`/`iff` as primitive
constructors, and

* `compile : ArithSource k → ArithmeticSemiformula ℕ k` sends a source to the Foundation
  normal form it denotes (`⟺` unfolding happens here, once, at compile time);
* `SourceEval` gives the source its own metalevel semantics — `iff` is a genuine `↔`,
  not `(→) ∧ (→)`, so `eval_compile` is a real theorem rather than a restatement;
* `sourceTokens` is the emitted symbol run, one token per *source* node, using the
  parser tags `20` (`¬`), `21` (`⟹`) and `22` (`⟺`) added to
  `parseStructuredArithmeticFormula` alongside the normal-form tags `9`–`18`, and
  `sourceNat` reads that run as a numeral — the name `def:ec` charges for;
* `PolyArithmeticSourceSeq` meters that run.  This is the paper's class: a family is
  certified at the size `def:ec` charges.  `PolyArithmeticFormulaSeq`
  (`StructuredPaperRpn.lean`) is the normal-form-metered foil; it embeds here by
  `PolyArithmeticFormulaSeq.toSource`, and `iffChain` witnesses that the embedding is
  strict.

The closure calculus `PolyArithmeticSourceSeq.{leaf,and,or,all,exs,not,imp,iff}` is the
public interface a client certifies a new family with; `LogicalInduction/README.md` names
this module as the import for that.  The main results are `eval_compile` (compilation is
semantics preserving), `parseStructuredArithmeticFormula_sourceTokens` (the round trip),
`compile_eq_of_sourceTokens_eq` (the emitted run determines what the source denotes, which
is what `dd:machinetheory` needs of a written name) and
`PolyArithmeticSourceSeq.bigDigits_sourceNat` (a source-metered family has write-out
names).  This is the same trade the development already makes for programs with
`Code.sourceNat`: the Gödel code of an `n`-deep `iff` source is roughly `2^(2^n)` and is
never emitted; the emitter writes the small source run, and the number is built by parser
contraction.

On top of the source language sits the literal first-order LUV frontend: `PaperLUVSeq`
carries each LUV's defining formula *as written* (`source`), a proof that it denotes the
LUV's Foundation formula (`compiles`), and the paper's efficiency condition on that
writing (`structural`); `PaperLUVSeq.rpnThresholdCodeSeq` compiles it to
`LUV.RpnThresholdCodeSeq` at the paper's exact threshold syntax, with
`PaperLUV.rpnThresholdCodes` the single-LUV corollary and `PaperLUVSeq.ofNNF` the
constructor for a family presented by normal-form leaves.  Three families inhabit it —
`unitFracPaperLUVSeq` at `1/(n+1)`, `dyadicPaperLUVSeq` at `2⁻ⁿ` (a superpolynomially
small value named in `O(n)` symbols by `binNumeral`), and `iffPaperLUVSeq`, whose `n`-th
defining formula is `O(n)` tokens to write and `≥ 2 ^ n` nodes once compiled.  The
strictness separation `iffChainSource_polyArithmeticSourceSeq` against
`iffChain_not_polyArithmeticFormulaSeq` proves
`PolyArithmeticFormulaSeq ⊊ PolyArithmeticSourceSeq` rather than asserting it, and
`unaryRendering_two_pow_not_polyArithmeticFormulaSeq` / `...SourceSeq` record that
Foundation's unary numeral is inadmissible at `2ⁿ` in *both* classes — an artifact of that
numeral, not a narrowing of `def:ec`, since the paper fixes no numeral notation (tex:564,
tex:614).

Finally `PaperLUVCombination` states `def:blcp` with literal paper LUVs as shares,
reaching the abstract carrier only through `toLUV`; `unitFracPaperLUVBoundedSequence`
inhabits it.

Two design facts about this layer, both of them constraints rather than preferences.

*The leaf's length field is unary, not a count.* `structuredLeafBlock`
(`StructuredPaperRpn.lean`) frames its payload with `replicate payload.length 1` and the
reserved terminator `19`.  An explicit symbol **count** field would be self-delimiting for
the parser and wrong for everything else on the ABI: the conditioning automaton clamps large
token values, so a count read off an untrusted stream reintroduces a polynomial-output
problem on malformed input, and the run/parse correspondence fails at the marker.  Small
tokens plus a reserved terminator keep every scanner's state polynomially bounded on
*arbitrary* input, which is the property the shared grammar needs.

*The decomposition bridge is head-scoped.*
`structuredPaperSourceDecomposeAll_rpnSentenceCodes` covers quantifier-headed propositions,
which is what `PaperLUV.thresholdFormula` always produces.  Arbitrary outer Boolean
structure would need a bracket-counting scan over the payload; no consumer here asks for it.
-/

namespace LogicalInduction

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open Nat.Partrec (Code)

/-! ## Negation on Foundation codes -/

/-- **Correctness of `negFormulaCode`**: the tag-swapping map on Foundation arithmetic
formula codes computes the code of the De Morgan negation.

*Proof kind:* `P` proved. *Provenance:* (a) derived in-project; the code layout is read
off Foundation's `Semiformula.toNat` via `Semiformula.encode_eq_toNat`, provenance (b). -/
lemma negFormulaCode_spec {k : ℕ} (φ : ArithmeticSemiformula ℕ k) :
    negFormulaCode (Encodable.encode φ) = Encodable.encode (∼φ) := by
  induction φ with
  | verum =>
      show negFormulaCode (Nat.pair 2 0 + 1) = _
      rw [negFormulaCode]
      simp only [Nat.unpair_pair]
      norm_num
      rfl
  | falsum =>
      show negFormulaCode (Nat.pair 3 0 + 1) = _
      rw [negFormulaCode]
      simp only [Nat.unpair_pair]
      norm_num
      rfl
  | rel r v =>
      show negFormulaCode (Nat.pair 0 _ + 1) = _
      rw [negFormulaCode]
      simp only [Nat.unpair_pair]
      norm_num
      rfl
  | nrel r v =>
      show negFormulaCode (Nat.pair 1 _ + 1) = _
      rw [negFormulaCode]
      simp only [Nat.unpair_pair]
      norm_num
      rfl
  | and φ ψ ihφ ihψ =>
      show negFormulaCode (Nat.pair 4 _ + 1) = _
      rw [negFormulaCode]
      simp only [Nat.unpair_pair]
      norm_num
      simp only [← LO.FirstOrder.Semiformula.encode_eq_toNat]
      rw [ihφ, ihψ]
      rfl
  | or φ ψ ihφ ihψ =>
      show negFormulaCode (Nat.pair 5 _ + 1) = _
      rw [negFormulaCode]
      simp only [Nat.unpair_pair]
      norm_num
      simp only [← LO.FirstOrder.Semiformula.encode_eq_toNat]
      rw [ihφ, ihψ]
      rfl
  | all φ ih =>
      show negFormulaCode (Nat.pair 6 _ + 1) = _
      rw [negFormulaCode]
      simp only [Nat.unpair_pair]
      norm_num
      simp only [← LO.FirstOrder.Semiformula.encode_eq_toNat]
      rw [ih]
      rfl
  | exs φ ih =>
      show negFormulaCode (Nat.pair 7 _ + 1) = _
      rw [negFormulaCode]
      simp only [Nat.unpair_pair]
      norm_num
      simp only [← LO.FirstOrder.Semiformula.encode_eq_toNat]
      rw [ih]
      rfl

/-! ## The source syntax -/

/-- The paper's arithmetic formula syntax over `k` bound variables: an arbitrary
Foundation normal-form formula as a `leaf`, closed under the paper's own primitive
connectives and quantifiers.  `not`, `imp` and `iff` are *constructors* here; in
`ArithmeticSemiformula` they are not.

*Proof kind:* `Def`. -/
inductive ArithSource : ℕ → Type
  | leaf {k : ℕ} (φ : ArithmeticSemiformula ℕ k) : ArithSource k
  | and {k : ℕ} (a b : ArithSource k) : ArithSource k
  | or {k : ℕ} (a b : ArithSource k) : ArithSource k
  | all {k : ℕ} (a : ArithSource (k + 1)) : ArithSource k
  | exs {k : ℕ} (a : ArithSource (k + 1)) : ArithSource k
  | not {k : ℕ} (a : ArithSource k) : ArithSource k
  | imp {k : ℕ} (a b : ArithSource k) : ArithSource k
  | iff {k : ℕ} (a b : ArithSource k) : ArithSource k

namespace ArithSource

/-- The emitted symbol run of a source: one token per source node, in the same
prefix order as `encodeArithmeticFormulaSymbols`, whose alphabet it extends by the
three connective tags `20`, `21`, `22`. -/
def sourceTokens : ∀ {k : ℕ}, ArithSource k → List ℕ
  | _, .leaf φ => encodeArithmeticFormulaSymbols φ
  | _, .and a b => 15 :: (sourceTokens a ++ sourceTokens b)
  | _, .or a b => 16 :: (sourceTokens a ++ sourceTokens b)
  | _, .all a => 17 :: sourceTokens a
  | _, .exs a => 18 :: sourceTokens a
  | _, .not a => 20 :: sourceTokens a
  | _, .imp a b => 21 :: (sourceTokens a ++ sourceTokens b)
  | _, .iff a b => 22 :: (sourceTokens a ++ sourceTokens b)

/-- The Foundation normal form a source denotes.  All of the normal-form expansion —
De Morgan on `not`, `∼a ⋎ b` on `imp`, and the duplicating unfold on `iff` — happens
here, off the emitted stream. -/
def compile : ∀ {k : ℕ}, ArithSource k → ArithmeticSemiformula ℕ k
  | _, .leaf φ => φ
  | _, .and a b => compile a ⋏ compile b
  | _, .or a b => compile a ⋎ compile b
  | _, .all a => Semiformula.all (compile a)
  | _, .exs a => Semiformula.exs (compile a)
  | _, .not a => ∼compile a
  | _, .imp a b => compile a 🡒 compile b
  | _, .iff a b => compile a 🡘 compile b

/-- A Foundation normal-form formula viewed as a source: a single leaf. -/
def ofNNF {k : ℕ} (φ : ArithmeticSemiformula ℕ k) : ArithSource k := .leaf φ

@[simp] lemma compile_ofNNF {k : ℕ} (φ : ArithmeticSemiformula ℕ k) :
    compile (ofNNF φ) = φ := rfl

@[simp] lemma sourceTokens_ofNNF {k : ℕ} (φ : ArithmeticSemiformula ℕ k) :
    sourceTokens (ofNNF φ) = encodeArithmeticFormulaSymbols φ := rfl

/-! ## Source semantics -/

/-- The metalevel semantics of a source, in a structure for `ℒₒᵣ`.  The `iff` clause is
a genuine `↔` and the `imp` clause a genuine `→`; nothing here is defined through the
normal form, so `eval_compile` below has content. -/
def SourceEval {M : Type*} [Structure ℒₒᵣ M] :
    ∀ {k : ℕ}, (Fin k → M) → (ℕ → M) → ArithSource k → Prop
  | _, e, ε, .leaf φ => Semiformula.Eval e ε φ
  | _, e, ε, .and a b => SourceEval e ε a ∧ SourceEval e ε b
  | _, e, ε, .or a b => SourceEval e ε a ∨ SourceEval e ε b
  | _, e, ε, .all a => ∀ x : M, SourceEval (x :> e) ε a
  | _, e, ε, .exs a => ∃ x : M, SourceEval (x :> e) ε a
  | _, e, ε, .not a => ¬SourceEval e ε a
  | _, e, ε, .imp a b => SourceEval e ε a → SourceEval e ε b
  | _, e, ε, .iff a b => (SourceEval e ε a ↔ SourceEval e ε b)

/-- **Compilation is semantics preserving**: the Foundation normal form a source compiles
to holds in a structure exactly when the source does under its own metalevel reading.

*Proof kind:* `P` proved.  *Provenance:* (a) derived in-project, on Foundation's
`Semiformula.Eval` homomorphism lemmas, provenance (b). -/
lemma eval_compile {M : Type*} [Structure ℒₒᵣ M] {k : ℕ} (ε : ℕ → M)
    (s : ArithSource k) (e : Fin k → M) :
    Semiformula.Eval e ε (compile s) ↔ SourceEval e ε s := by
  induction s with
  | leaf φ => exact Iff.rfl
  | and a b iha ihb => simp [compile, SourceEval, iha, ihb]
  | or a b iha ihb => simp [compile, SourceEval, iha, ihb]
  | all a ih =>
      simp only [compile, SourceEval]
      exact forall_congr' fun x => ih (x :> e)
  | exs a ih =>
      simp only [compile, SourceEval]
      exact exists_congr fun x => ih (x :> e)
  | not a ih => simp [compile, SourceEval, ih]
  | imp a b iha ihb => simp [compile, SourceEval, iha, ihb]
  | iff a b iha ihb => simp [compile, SourceEval, iha, ihb]

/-! ## Round trip -/

/-! The three connective tags, as parser equations.  The literal tag comparisons in
`parseStructuredArithmeticFormula` reduce by evaluation, so each is `rfl`; stating them
keeps the round-trip proof from rewriting inside an unreduced `if`-chain. -/

private lemma parse_tag20 (fuel depth : ℕ) (rest : List ℕ) :
    parseStructuredArithmeticFormula (fuel + 1) depth (20 :: rest) =
      (parseStructuredArithmeticFormula fuel 0 rest).map fun p =>
        (negFormulaCode p.1, p.2) := rfl

private lemma parse_tag21 (fuel depth : ℕ) (rest : List ℕ) :
    parseStructuredArithmeticFormula (fuel + 1) depth (21 :: rest) =
      (parseStructuredArithmeticFormula fuel 0 rest).bind fun p =>
        (parseStructuredArithmeticFormula fuel 0 p.2).map fun q =>
          (Nat.pair 5 (Nat.pair (negFormulaCode p.1) q.1) + 1, q.2) := rfl

private lemma parse_tag22 (fuel depth : ℕ) (rest : List ℕ) :
    parseStructuredArithmeticFormula (fuel + 1) depth (22 :: rest) =
      (parseStructuredArithmeticFormula fuel 0 rest).bind fun p =>
        (parseStructuredArithmeticFormula fuel 0 p.2).map fun q =>
          (Nat.pair 4
            (Nat.pair (Nat.pair 5 (Nat.pair (negFormulaCode p.1) q.1) + 1)
              (Nat.pair 5 (Nat.pair (negFormulaCode q.1) p.1) + 1)) + 1, q.2) := rfl

/-- **Source round trip**: the numeric parser turns a source's emitted run back into the
Gödel code of the formula it compiles to, leaving the suffix untouched.  The three
connective tags are discharged by `negFormulaCode_spec`.

*Proof kind:* `P` proved. -/
lemma parseStructuredArithmeticFormula_sourceTokens {k : ℕ} (s : ArithSource k)
    (tail : List ℕ) {fuel depth : ℕ} (hfuel : (sourceTokens s).length ≤ fuel) :
    parseStructuredArithmeticFormula fuel depth (sourceTokens s ++ tail) =
      some (Encodable.encode (compile s), tail) := by
  induction s generalizing fuel tail depth with
  | leaf φ => exact parseStructuredArithmeticFormula_encode φ tail hfuel
  | and a b iha ihb =>
      cases fuel with
      | zero => simp [sourceTokens] at hfuel
      | succ fuel =>
          simp only [sourceTokens, List.cons_append, List.append_assoc,
            parseStructuredArithmeticFormula]
          rw [iha (sourceTokens b ++ tail) (by simp [sourceTokens] at hfuel; omega),
            Option.bind_some, ihb tail (by simp [sourceTokens] at hfuel; omega)]
          rfl
  | or a b iha ihb =>
      cases fuel with
      | zero => simp [sourceTokens] at hfuel
      | succ fuel =>
          simp only [sourceTokens, List.cons_append, List.append_assoc,
            parseStructuredArithmeticFormula]
          rw [iha (sourceTokens b ++ tail) (by simp [sourceTokens] at hfuel; omega),
            Option.bind_some, ihb tail (by simp [sourceTokens] at hfuel; omega)]
          rfl
  | all a ih =>
      cases fuel with
      | zero => simp [sourceTokens] at hfuel
      | succ fuel =>
          simp only [sourceTokens, List.cons_append, parseStructuredArithmeticFormula]
          rw [ih tail (by simpa [sourceTokens] using hfuel)]
          rfl
  | exs a ih =>
      cases fuel with
      | zero => simp [sourceTokens] at hfuel
      | succ fuel =>
          simp only [sourceTokens, List.cons_append, parseStructuredArithmeticFormula]
          rw [ih tail (by simpa [sourceTokens] using hfuel)]
          rfl
  | not a ih =>
      cases fuel with
      | zero => simp [sourceTokens] at hfuel
      | succ fuel =>
          simp only [sourceTokens, List.cons_append]
          rw [parse_tag20, ih tail (by simpa [sourceTokens] using hfuel),
            Option.map_some, negFormulaCode_spec]
          rfl
  | imp a b iha ihb =>
      cases fuel with
      | zero => simp [sourceTokens] at hfuel
      | succ fuel =>
          simp only [sourceTokens, List.cons_append, List.append_assoc]
          rw [parse_tag21,
            iha (sourceTokens b ++ tail) (by simp [sourceTokens] at hfuel; omega),
            Option.bind_some, ihb tail (by simp [sourceTokens] at hfuel; omega),
            Option.map_some, negFormulaCode_spec]
          rfl
  | iff a b iha ihb =>
      cases fuel with
      | zero => simp [sourceTokens] at hfuel
      | succ fuel =>
          simp only [sourceTokens, List.cons_append, List.append_assoc]
          rw [parse_tag22,
            iha (sourceTokens b ++ tail) (by simp [sourceTokens] at hfuel; omega),
            Option.bind_some, ihb tail (by simp [sourceTokens] at hfuel; omega),
            Option.map_some, negFormulaCode_spec, negFormulaCode_spec]
          rfl

/-- **The emitted run determines what the source denotes.**  `sourceTokens` is *not*
injective — `leaf (φ ⋏ ψ)` and `and (leaf φ) (leaf ψ)` emit the same run — but the parser
reads one code off a run, so two sources with the same run compile to the same formula.
This is what makes a written name unambiguous as a *name of a sentence*, which is all the
`thm:incons` convention `dd:machinetheory` needs of it.

*Proof kind:* `C` (composition).  *Provenance:* (a)
`parseStructuredArithmeticFormula_sourceTokens` derived in-project; (b) Mathlib citation —
`Encodable.encode_injective`. -/
lemma compile_eq_of_sourceTokens_eq {k : ℕ} {s s' : ArithSource k}
    (h : sourceTokens s = sourceTokens s') : compile s = compile s' := by
  have h1 := parseStructuredArithmeticFormula_sourceTokens s []
    (fuel := (sourceTokens s).length) (depth := 0) le_rfl
  have h2 := parseStructuredArithmeticFormula_sourceTokens s' []
    (fuel := (sourceTokens s').length) (depth := 0) le_rfl
  rw [h] at h1
  rw [h1] at h2
  exact Encodable.encode_injective (by simpa using Option.some.inj h2)

/-! ## The source alphabet -/

/-- Every source token is either a normal-form token (`< 19`) or one of the three
connective tags `20`, `21`, `22`.  Both alphabet facts below read off this one induction. -/
lemma sourceTokens_alphabet {k : ℕ} (s : ArithSource k) :
    ∀ x ∈ sourceTokens s, x < 19 ∨ (20 ≤ x ∧ x < 23) := by
  induction s with
  | leaf φ =>
      intro x hx
      simp only [sourceTokens] at hx
      have := encodeArithmeticFormulaSymbols_lt φ x hx
      omega
  | and a b iha ihb =>
      intro x hx
      simp only [sourceTokens] at hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · omega
      · rcases List.mem_append.mp hx' with h | h
        · exact iha x h
        · exact ihb x h
  | or a b iha ihb =>
      intro x hx
      simp only [sourceTokens] at hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · omega
      · rcases List.mem_append.mp hx' with h | h
        · exact iha x h
        · exact ihb x h
  | all a ih =>
      intro x hx
      simp only [sourceTokens] at hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · omega
      · exact ih x hx'
  | exs a ih =>
      intro x hx
      simp only [sourceTokens] at hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · omega
      · exact ih x hx'
  | not a ih =>
      intro x hx
      simp only [sourceTokens] at hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · omega
      · exact ih x hx'
  | imp a b iha ihb =>
      intro x hx
      simp only [sourceTokens] at hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · omega
      · rcases List.mem_append.mp hx' with h | h
        · exact iha x h
        · exact ihb x h
  | iff a b iha ihb =>
      intro x hx
      simp only [sourceTokens] at hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · omega
      · rcases List.mem_append.mp hx' with h | h
        · exact iha x h
        · exact ihb x h

/-- The source alphabet avoids the reserved block terminator `19`, which is what lets a
source run sit inside a structured leaf block. -/
lemma sourceTokens_ne_19 {k : ℕ} (s : ArithSource k) :
    ∀ x ∈ sourceTokens s, x ≠ 19 := fun x hx => by
  rcases sourceTokens_alphabet s x hx with h | h <;> omega

/-- Every source token is a fixed small constant: the alphabet is `0..18, 20..22`. -/
lemma sourceTokens_lt_23 {k : ℕ} (s : ArithSource k) :
    ∀ x ∈ sourceTokens s, x < 23 := fun x hx => by
  rcases sourceTokens_alphabet s x hx with h | h <;> omega

/-! ### Naming a written formula

`def:ec` charges a trader for the symbols it *writes*.  A source's name is therefore its
own emitted run, read as a numeral (`tokenListNat`, `Framework/CodeSource.lean`): one
base-`64` digit per token, closed by a sentinel outside the alphabet.  Its base-`4` digit
count — the length actually written down — is `3 * (sourceTokens s).length + 3`, linear in
the paper's text.

The Gödel code `Encodable.encode (compile s)` is **not** this number and is not usable
here: Foundation's `Semiformula.toNat` pairs at every node, so it is doubly exponential in
the parse tree and its digit count exponential.  `iffChainSource` separates the two on the
nose (`sourceTokens_iffChainSource_length` is `5n + 4`, while the normal form it names has
`≥ 2 ^ n` nodes). -/

/-- **The name of a written formula**: its emitted token run, read as a numeral. -/
def sourceNat {k : ℕ} (s : ArithSource k) : ℕ := tokenListNat (sourceTokens s)

/-- The source alphabet sits below the naming sentinel. -/
lemma sourceTokens_lt_63 {k : ℕ} (s : ArithSource k) : ∀ x ∈ sourceTokens s, x < 63 :=
  fun x hx => lt_trans (sourceTokens_lt_23 s x hx) (by norm_num)

/-- **Distinct writings get distinct names**, with no appeal to what they denote — the
day-separation input for families presented by source text. -/
lemma sourceNat_ne_of_sourceTokens_ne {k l : ℕ} {s : ArithSource k} {t : ArithSource l}
    (h : sourceTokens s ≠ sourceTokens t) : sourceNat s ≠ sourceNat t := fun he =>
  h (tokenListNat_injective (sourceTokens_lt_63 s) (sourceTokens_lt_63 t) he)

end ArithSource

/-! ## The source-metered family class

`PolyArithmeticSourceSeq` is `PolyArithmeticFormulaSeq` with the meter moved from the
Foundation normal form to the paper's source: it certifies that the *emitted source run*
is a `PolySegStream`.  Since `ofNNF` is token-for-token the old encoder
(`sourceTokens_ofNNF`), every family certified by `PolyArithmeticFormulaSeq` is certified
here (`PolyArithmeticFormulaSeq.toSource`), and `⟺` is charged linearly (`dd:nnf`). -/

open ArithSource in
/-- **The paper's efficiency condition on formula families** (`def:ec`, tex:753): the run
the paper's writer emits — one token per *source* node, over the primitive connectives of
tex:560 — is a `PolySegStream`.  Normal-form expansion of `⟹` and `⟺` happens in the
parser, off the stream, so nothing is charged twice.

`PolyArithmeticFormulaSeq` is the normal-form-metered foil, strictly finer than this
class; it embeds by `PolyArithmeticFormulaSeq.toSource`.

*Proof kind:* `Def`. -/
def PolyArithmeticSourceSeq {k : ℕ} (s : ℕ → ArithSource k) : Prop :=
  PolySegStream (fun n => sourceTokens (s n))

namespace PolyArithmeticSourceSeq

open ArithSource

/-! ### The closure calculus

These eight lemmas are the public interface a client certifies a new source-metered family
with: one per source constructor, each charging the constructor's single tag on top of the
sub-family's own run. -/

/-- A normal-form-metered family read as leaves is source-metered, token for token. -/
lemma leaf {k : ℕ} {φ : ℕ → ArithmeticSemiformula ℕ k} (h : PolyArithmeticFormulaSeq φ) :
    PolyArithmeticSourceSeq (fun n => ArithSource.leaf (φ n)) :=
  PolySegStream.of_eq h fun _ => rfl

/-- A conjunction of source-metered families is source-metered: one token (`15`) plus the
two runs. -/
lemma and {k : ℕ} {a b : ℕ → ArithSource k} (ha : PolyArithmeticSourceSeq a)
    (hb : PolyArithmeticSourceSeq b) :
    PolyArithmeticSourceSeq (fun n => ArithSource.and (a n) (b n)) :=
  ((PolySegStream.constList [15]).append (ha.append hb)).of_eq fun _ => by
    simp [sourceTokens]

/-- A disjunction of source-metered families is source-metered: one token (`16`) plus the
two runs. -/
lemma or {k : ℕ} {a b : ℕ → ArithSource k} (ha : PolyArithmeticSourceSeq a)
    (hb : PolyArithmeticSourceSeq b) :
    PolyArithmeticSourceSeq (fun n => ArithSource.or (a n) (b n)) :=
  ((PolySegStream.constList [16]).append (ha.append hb)).of_eq fun _ => by
    simp [sourceTokens]

/-- A universally quantified source-metered family is source-metered: one token (`17`)
plus the run. -/
lemma all {k : ℕ} {a : ℕ → ArithSource (k + 1)} (ha : PolyArithmeticSourceSeq a) :
    PolyArithmeticSourceSeq (fun n => ArithSource.all (a n)) :=
  ((PolySegStream.constList [17]).append ha).of_eq fun _ => by simp [sourceTokens]

/-- An existentially quantified source-metered family is source-metered: one token (`18`)
plus the run. -/
lemma exs {k : ℕ} {a : ℕ → ArithSource (k + 1)} (ha : PolyArithmeticSourceSeq a) :
    PolyArithmeticSourceSeq (fun n => ArithSource.exs (a n)) :=
  ((PolySegStream.constList [18]).append ha).of_eq fun _ => by simp [sourceTokens]

/-- A negated source-metered family is source-metered: one token (`20`) plus the run.  The
De Morgan expansion happens in the parser, off the emitted stream. -/
lemma not {k : ℕ} {a : ℕ → ArithSource k} (ha : PolyArithmeticSourceSeq a) :
    PolyArithmeticSourceSeq (fun n => ArithSource.not (a n)) :=
  ((PolySegStream.constList [20]).append ha).of_eq fun _ => by simp [sourceTokens]

/-- An implication of source-metered families is source-metered: one token (`21`) plus the
two runs, with no negation pushed through the antecedent. -/
lemma imp {k : ℕ} {a b : ℕ → ArithSource k} (ha : PolyArithmeticSourceSeq a)
    (hb : PolyArithmeticSourceSeq b) :
    PolyArithmeticSourceSeq (fun n => ArithSource.imp (a n) (b n)) :=
  ((PolySegStream.constList [21]).append (ha.append hb)).of_eq fun _ => by
    simp [sourceTokens]

/-- A biconditional of source-metered families is source-metered: one token (`22`) plus
the two runs.  This is where `⟺` is charged linearly, against the `2^Ω(n)` the normal form
would charge (`dd:nnf`). -/
lemma iff {k : ℕ} {a b : ℕ → ArithSource k} (ha : PolyArithmeticSourceSeq a)
    (hb : PolyArithmeticSourceSeq b) :
    PolyArithmeticSourceSeq (fun n => ArithSource.iff (a n) (b n)) :=
  ((PolySegStream.constList [22]).append (ha.append hb)).of_eq fun _ => by
    simp [sourceTokens]

end PolyArithmeticSourceSeq

/-- **The write-out certificate, delivered.**  A family certified at the size `def:ec`
charges — one token per source node — is a family whose *names* are efficiently written
out.  This is the bridge that lets a paper-facing statement meter a formula sequence by
its writing instead of by its Gödel code. -/
lemma PolyArithmeticSourceSeq.bigDigits_sourceNat {k : ℕ} {s : ℕ → ArithSource k}
    (h : PolyArithmeticSourceSeq s) : BigDigits (fun n => (s n).sourceNat) :=
  BigDigits.ofTokenListNat h fun n => ArithSource.sourceTokens_lt_63 (s n)

/-- **The old class embeds**: a normal-form-metered family is a source-metered family of
leaves, token for token. -/
lemma PolyArithmeticFormulaSeq.toSource {k : ℕ}
    {φ : ℕ → ArithmeticSemiformula ℕ k} (h : PolyArithmeticFormulaSeq φ) :
    PolyArithmeticSourceSeq (fun n => ArithSource.ofNNF (φ n)) :=
  PolySegStream.of_eq h fun _ => rfl

/-! ## Structured leaves at the source level

The emitted block is `structuredLeafBlock` (`StructuredPaperRpn.lean`) at the paper's
*source* run rather than at the normal form it denotes: the same `[1, 0, polarity]`
dispatch prefix, the same unary payload length, the same reserved terminator `19`, with
`sourceTokens s` as the payload.  Parser contraction rebuilds the Gödel code of
`compile s`, so the public tag-`5` atom is exactly the one the normal-form block produces —
what changes is only how many tokens were emitted to name it. -/

open ArithSource in
/-- The atomic block whose contraction is `paperPrimeSentence positive (compile s)`. -/
def structuredPaperSourcePrimeBlock (positive : Bool) (s : ArithSource 0) : List ℕ :=
  structuredLeafBlock positive (sourceTokens s)

/-- A source leaf block is never empty; this is the fuel side condition `parseRpn` asks
for, and the length hypothesis the claim families supply. -/
lemma structuredPaperSourcePrimeBlock_length_pos (positive : Bool)
    (s : ArithSource 0) : 0 < (structuredPaperSourcePrimeBlock positive s).length :=
  structuredLeafBlock_length_pos positive _

/-- **Source leaf contraction**: the emitted source block parses to the exact public
tag-`5` atom of the formula the source compiles to. -/
lemma parseRpn_structuredPaperSourcePrimeBlock (positive : Bool) (s : ArithSource 0)
    (tail : List ℕ) {fuel : ℕ} (hfuel : 1 ≤ fuel) :
    parseRpn fuel (structuredPaperSourcePrimeBlock positive s ++ tail) =
      some (paperPrimeSentence positive (ArithSource.compile s), tail) :=
  parseRpn_structuredLeafBlock
    (by
      simpa using ArithSource.parseStructuredArithmeticFormula_sourceTokens
        (depth := 0) s [] le_rfl)
    tail hfuel

/-- The source leaf of an efficiently presented source family is efficiently emittable:
constant framing, a unary length run, and the source payload itself. -/
lemma structuredPaperSourcePrimeBlock_polySegStream (positive : Bool)
    (s : ℕ → ArithSource 0) (hs : PolyArithmeticSourceSeq s) :
    PolySegStream (fun n => structuredPaperSourcePrimeBlock positive (s n)) :=
  structuredLeafBlock_polySegStream positive hs

/-- **The source block is a `19`-free span**: the instance of `structuredLeafBlock_span`
at the class the development actually meters, whose payload alphabet is `0..18, 20..22`
(`sourceTokens_lt_23`) and so never contains the terminator. -/
lemma structuredPaperSourcePrimeBlock_span (positive : Bool) (s : ArithSource 0) :
    ∃ w, structuredPaperSourcePrimeBlock positive s = 1 :: 0 :: (w ++ [19]) ∧
      ∀ x ∈ w, x ≠ 19 :=
  structuredLeafBlock_span positive (ArithSource.sourceTokens_ne_19 s)

/-! ### The universally quantified source block

`paperPrimeDecompose` recurses only through the outer Boolean structure, so a
`∀`-headed proposition decomposes to a single leaf inside a negation shell.  Foundation's
`Semiformula` has no `∀` for a negated body either, so the paper's `∀x. φ` is written
`¬∃x. ¬φ`, the reading the paper itself declares (tex:568-573) — at the source level that
costs exactly one extra token (`20`), which is what makes the shell affordable here. -/

/-- The block whose contraction is `paperPrimeDecompose (.all (compile s))`. -/
def structuredPaperSourceDecomposeAllBlock (s : ArithSource 1) : List ℕ :=
  [2] ++ structuredPaperSourcePrimeBlock true (.exs (.not s)) ++ [0]

/-- **Source `∀`-block contraction**, at exactly the block's own length as fuel. -/
lemma parseRpn_structuredPaperSourceDecomposeAllBlock_suffix (s : ArithSource 1)
    (tail : List ℕ) :
    parseRpn (structuredPaperSourceDecomposeAllBlock s).length
      (structuredPaperSourceDecomposeAllBlock s ++ tail) =
      some (paperPrimeDecompose (.all (ArithSource.compile s)), tail) := by
  simp only [structuredPaperSourceDecomposeAllBlock, List.length_cons, List.length_append,
    List.cons_append, List.append_assoc]
  rw [parseRpn_cons]
  norm_num
  rw [parseRpn_structuredPaperSourcePrimeBlock true (.exs (.not s)) (0 :: tail) (by omega)]
  simp only [Option.bind_some]
  rw [parseRpn_mono (0 :: tail) (by omega)
    (show parseRpn 1 (0 :: tail) = some (⊥, tail) by rfl)]
  simp only [Option.bind_some, paperPrimeDecompose]
  rfl

/-- The same contraction on a closed run. -/
lemma parseRpn_structuredPaperSourceDecomposeAllBlock (s : ArithSource 1) :
    parseRpn (structuredPaperSourceDecomposeAllBlock s).length
      (structuredPaperSourceDecomposeAllBlock s) =
      some (paperPrimeDecompose (.all (ArithSource.compile s)), []) := by
  simpa using parseRpn_structuredPaperSourceDecomposeAllBlock_suffix s []

/-- The `∀`-blocks of a source-metered family are efficiently emittable. -/
lemma structuredPaperSourceDecomposeAllBlock_polySegStream
    {s : ℕ → ArithSource 1} (hs : PolyArithmeticSourceSeq s) :
    PolySegStream (fun n => structuredPaperSourceDecomposeAllBlock (s n)) := by
  have hprime := structuredPaperSourcePrimeBlock_polySegStream true
    (fun n => ArithSource.exs (ArithSource.not (s n))) hs.not.exs
  have hshell : PolySegStream (fun _ : ℕ => ([2] : List ℕ)) :=
    PolySegStream.ofTokenStream (PolyTokenStream.const 2)
  have hclose : PolySegStream (fun _ : ℕ => ([0] : List ℕ)) :=
    PolySegStream.ofTokenStream (PolyTokenStream.const 0)
  exact ((hshell.append hprime).append hclose).of_eq fun n => rfl

/-- **Decompose efficiency lifting at a quantified head, source metered**: an
efficiently *written* family of universally quantified paper formulas has an efficient
stream of exact paper-prime decomposition blocks.  The emitter outputs only the small
source block; the tag-`5` atom code is built by parser contraction. -/
lemma structuredPaperSourceDecomposeAll_rpnSentenceCodes (s : ℕ → ArithSource 1)
    (hs : PolyArithmeticSourceSeq s) :
    RpnSentenceCodes (fun n => paperPrimeDecompose (.all (ArithSource.compile (s n)))) :=
  ⟨fun n => structuredPaperSourceDecomposeAllBlock (s n),
    structuredPaperSourceDecomposeAllBlock_polySegStream hs,
    fun n => parseRpn_structuredPaperSourceDecomposeAllBlock (s n)⟩

/-! ### Arity coercion on the source language

A source embedded under `Rew.castLE` is *index preserving* (`Rew.castLe_bvar`:
`castLE h #x = #(Fin.castLE h x)`, same `.val`), so its token run and the formula it
compiles to are literally unchanged and a family's `def:ec` certificate transports along
the coercion with no new emission induction. -/

namespace ArithSource

/-- Arity coercion of a source, leaf-wise by `Rew.castLE`.  Index preserving, hence free
of emission cost. -/
def castLE : ∀ {k k' : ℕ}, k ≤ k' → ArithSource k → ArithSource k'
  | _, _, h, .leaf φ => .leaf (Rew.castLE h ▹ φ)
  | _, _, h, .and a b => .and (castLE h a) (castLE h b)
  | _, _, h, .or a b => .or (castLE h a) (castLE h b)
  | _, _, h, .all a => .all (castLE (Nat.succ_le_succ h) a)
  | _, _, h, .exs a => .exs (castLE (Nat.succ_le_succ h) a)
  | _, _, h, .not a => .not (castLE h a)
  | _, _, h, .imp a b => .imp (castLE h a) (castLE h b)
  | _, _, h, .iff a b => .iff (castLE h a) (castLE h b)

/-- Arity coercion emits nothing: the token run is unchanged. -/
@[simp] lemma sourceTokens_castLE : ∀ {k k' : ℕ} (h : k ≤ k') (a : ArithSource k),
    sourceTokens (castLE h a) = sourceTokens a
  | _, _, h, .leaf φ => by simp [castLE, sourceTokens]
  | _, _, h, .and a b => by
      simp [castLE, sourceTokens, sourceTokens_castLE h a, sourceTokens_castLE h b]
  | _, _, h, .or a b => by
      simp [castLE, sourceTokens, sourceTokens_castLE h a, sourceTokens_castLE h b]
  | _, _, h, .all a => by
      simp [castLE, sourceTokens, sourceTokens_castLE (Nat.succ_le_succ h) a]
  | _, _, h, .exs a => by
      simp [castLE, sourceTokens, sourceTokens_castLE (Nat.succ_le_succ h) a]
  | _, _, h, .not a => by simp [castLE, sourceTokens, sourceTokens_castLE h a]
  | _, _, h, .imp a b => by
      simp [castLE, sourceTokens, sourceTokens_castLE h a, sourceTokens_castLE h b]
  | _, _, h, .iff a b => by
      simp [castLE, sourceTokens, sourceTokens_castLE h a, sourceTokens_castLE h b]

/-- Arity coercion commutes with compilation. -/
lemma compile_castLE : ∀ {k k' : ℕ} (h : k ≤ k') (a : ArithSource k),
    compile (castLE h a) = Rew.castLE h ▹ compile a
  | _, _, h, .leaf φ => rfl
  | _, _, h, .and a b => by
      simp only [castLE, compile, compile_castLE h a, compile_castLE h b,
        LogicalConnective.HomClass.map_and]
  | _, _, h, .or a b => by
      simp only [castLE, compile, compile_castLE h a, compile_castLE h b,
        LogicalConnective.HomClass.map_or]
  | _, _, h, .all a => by
      simp only [castLE, compile, compile_castLE (Nat.succ_le_succ h) a]
      have hq := Rewriting.app_all (Rew.castLE h) (compile a)
      rw [Rew.q_castLE] at hq
      exact hq.symm
  | _, _, h, .exs a => by
      simp only [castLE, compile, compile_castLE (Nat.succ_le_succ h) a]
      have hq := Rewriting.app_exs (Rew.castLE h) (compile a)
      rw [Rew.q_castLE] at hq
      exact hq.symm
  | _, _, h, .not a => by
      simp only [castLE, compile, compile_castLE h a,
        LogicalConnective.HomClass.map_neg]
  | _, _, h, .imp a b => by
      simp only [castLE, compile, compile_castLE h a, compile_castLE h b,
        LogicalConnective.HomClass.map_imply]
  | _, _, h, .iff a b => by
      simp only [castLE, compile, compile_castLE h a, compile_castLE h b,
        LogicalConnective.HomClass.map_iff]

end ArithSource

/-- Arity coercion of a source-metered family is source-metered, at the same cost. -/
lemma PolyArithmeticSourceSeq.castLE {k k' : ℕ} (h : k ≤ k') {a : ℕ → ArithSource k}
    (ha : PolyArithmeticSourceSeq a) :
    PolyArithmeticSourceSeq (fun n => ArithSource.castLE h (a n)) :=
  ha.of_eq fun n => by simp

/-! ## The literal first-order LUV frontend

A single `PaperLUV` carries no efficiency certificate, so the family layer supplies
one — and supplies it as *structural symbol emission of the threshold bodies*, never as
a bound on Foundation's Gödel codes and never as a caller-provided tag-`5` code.  The
compiler below turns that certificate into the paper's exact threshold sentences. -/

section Frontend

variable {T : ArithmeticTheory} [T.Δ₁]

/-- The body under the paper's threshold quantifier, as a proposition-level formula. -/
def paperThresholdBody (X : PaperLUV T) (r : ℚ) : ArithmeticSemiformula ℕ 1 :=
  ((X.formula 🡒 paperRatGtDef r : ArithmeticSemisentence 1) :
    ArithmeticSemiformula ℕ 1)

lemma paperThresholdFormula_eq_all (X : PaperLUV T) (r : ℚ) :
    ((X.thresholdFormula r : ArithmeticSentence) : ArithmeticProposition) =
      .all (paperThresholdBody X r) := by
  simp only [PaperLUV.thresholdFormula, paperThresholdBody]
  simp
  rfl

lemma paperLUV_gt_eq (X : PaperLUV T) (r : ℚ) :
    X.toLUV.gt r = paperPrimeDecompose (.all (paperThresholdBody X r)) := by
  rw [PaperLUV.toLUV_gt, paperThresholdFormula_eq_all]

/-! ### Threshold syntax as small tokens

`paperRatGtDef` is a fixed template around two Foundation numerals, so its encoding
splits into two constant blocks and two numeral runs; the numerals at query index
`⟨n, ⟨k, i⟩⟩` are the reduced numerator and denominator of `i / k`, which the fuel
calculus already computes (`gcdc_polyFueled`, `divmod1_polyFueled`).  Together with the
implication shell this discharges the threshold-body certificate from a certificate on
the LUVs' defining formulas alone. -/

private def ratGtPre : List ℕ :=
  [18, 18, 15, 16, 15, 13, 3, 2, 0, 3, 0, 11, 3, 1, 2, 0, 7, 8, 3, 0, 3, 0, 3, 2,
   0, 15, 16, 11, 3, 0, 3, 2, 0, 13, 3, 0, 3, 2, 0, 11, 3, 1, 2, 0, 7, 7, 8, 3, 2,
   0, 3, 2, 0, 3, 2, 0, 3, 0, 15, 13, 5, 3, 0, 13, 8]

private def ratGtMid : List ℕ := [3, 0, 8, 3, 2, 0]

private lemma oringMul_term :
    (Semiterm.Operator.Mul.mul : Semiterm.Operator ℒₒᵣ 2).term =
      Semiterm.func Language.Mul.mul Semiterm.bvar := rfl

private lemma oringAdd_term :
    (Semiterm.Operator.Add.add : Semiterm.Operator ℒₒᵣ 2).term =
      Semiterm.func Language.Add.add Semiterm.bvar := rfl

private lemma oringNumZero_term :
    (Semiterm.Operator.numeral ℒₒᵣ 0).term =
      Semiterm.func Language.Zero.zero ![] := rfl

private lemma emb_subst_nil_comm {n : ℕ} (t : Semiterm ℒₒᵣ Empty 0) :
    (Rew.emb ((Rew.subst ![]) t) : ArithmeticSemiterm ℕ n) =
      (Rew.subst ![]) (Rew.emb t) := by
  have h : ((Rew.emb : Rew ℒₒᵣ Empty n ℕ n).comp (Rew.subst ![])) =
      ((Rew.subst ![]).comp (Rew.emb : Rew ℒₒᵣ Empty 0 ℕ 0)) := by
    ext x
    · exact Fin.elim0 x
    · exact IsEmpty.elim inferInstance x
  rw [← Rew.comp_app, h, Rew.comp_app]

private def encNumeral (v : ℕ) : List ℕ :=
  encodeArithmeticTermSymbols
    ((Semiterm.Operator.numeral ℒₒᵣ v).const : ArithmeticSemiterm ℕ 3)

private lemma enc_paperRatGtDef (r : ℚ) (hr : ¬ r < 0) :
    encodeArithmeticFormulaSymbols
      ((paperRatGtDef r : ArithmeticSemisentence 1) : ArithmeticSemiformula ℕ 1) =
      ratGtPre ++ encNumeral r.num.natAbs ++ ratGtMid ++ encNumeral r.den := by
  rw [paperRatGtDef, if_neg hr]
  simp [pairDef, encodeArithmeticFormulaSymbols, encodeArithmeticTermSymbols,
    encodeStructuredNat, ratGtPre, ratGtMid, encNumeral,
    Semiformula.Operator.lt_def, Semiformula.Operator.eq_def,
    Semiformula.Operator.le_def, Semiterm.Operator.operator,
    Semiterm.Operator.const, oringMul_term, oringAdd_term,
    oringNumZero_term, Matrix.fun_eq_vec_two, emb_subst_nil_comm]

private lemma encNumeral_zero : encNumeral 0 = [5] := rfl

private lemma encNumeral_of_ne_zero {v : ℕ} (hv : v ≠ 0) :
    encNumeral v = List.replicate (v - 1) 7 ++ List.replicate v 6 :=
  encodeArithmeticTermSymbols_numeral v hv

/-- Numerals of a poly-fueled value stream are emittable, zero included. -/
lemma encNumeral_polySegStream {cv : Code} {v : ℕ → ℕ} (hv : PolyFueled cv v) :
    PolySegStream (fun n => encNumeral (v n)) := by
  have hpred : PolyFueled _ (fun n => v n - 1) :=
    (subc_polyFueled.comp (hv.pair (PolyFueled.const 1))).of_eq fun n => by
      simp only [Nat.unpair_pair]
  have hpos : PolySegStream (fun n => List.replicate (v n - 1) 7 ++
      List.replicate (v n) 6) :=
    (PolySegStream.repeatTag 7 hpred).append (PolySegStream.repeatTag 6 hv)
  refine ((PolySegStream.constList [5]).ifZero hpos hv).of_eq fun n => ?_
  by_cases h : v n = 0
  · rw [if_pos h, h, encNumeral_zero]
  · rw [if_neg h, encNumeral_of_ne_zero h]

/-- The threshold rational named by a `RpnThresholdCodeSeq` query index `⟨n, ⟨k, i⟩⟩`. -/
def queryRat (m : ℕ) : ℚ :=
  (m.unpair.2.unpair.2 : ℚ) / (m.unpair.2.unpair.1 : ℚ)

lemma queryRat_nonneg (m : ℕ) : ¬ queryRat m < 0 := by
  rw [queryRat]
  exact not_lt.mpr (div_nonneg (by positivity) (by positivity))

lemma queryNum_polyFueled :
    ∃ c, PolyFueled c (fun m => (queryRat m).num.natAbs) := by
  obtain ⟨cg, hgcd⟩ := gcdc_polyFueled
  obtain ⟨cdm, hdm⟩ := divmod1_polyFueled
  have hk := PolyFueled.left.comp PolyFueled.right
  have hi := PolyFueled.right.comp PolyFueled.right
  have gPF := hgcd.comp (hi.pair hk)
  have pgPF := predc_polyFueled.comp gPF
  have numPF := PolyFueled.left.comp (hdm.comp (pgPF.pair hi))
  refine ⟨_, (ifzSel_polyFueled.comp
    (((PolyFueled.const 0).pair numPF).pair hk)).of_eq fun m => ?_⟩
  simp only [Nat.unpair_pair, ifzSelFn]
  by_cases hk0 : m.unpair.2.unpair.1 = 0
  · rw [if_pos hk0, queryRat, hk0]
    simp
  · rw [if_neg hk0, queryRat]
    have hg : 0 < Nat.gcd m.unpair.2.unpair.2 m.unpair.2.unpair.1 :=
      Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hk0)
    have hg1 : (Nat.gcd m.unpair.2.unpair.2 m.unpair.2.unpair.1).pred + 1 =
        Nat.gcd m.unpair.2.unpair.2 m.unpair.2.unpair.1 :=
      Nat.succ_pred_eq_of_pos hg
    rw [hg1, ComputableLUV.natCast_div_num hk0, Int.natAbs_natCast]

lemma queryDen_polyFueled :
    ∃ c, PolyFueled c (fun m => (queryRat m).den) := by
  obtain ⟨cg, hgcd⟩ := gcdc_polyFueled
  obtain ⟨cdm, hdm⟩ := divmod1_polyFueled
  have hk := PolyFueled.left.comp PolyFueled.right
  have hi := PolyFueled.right.comp PolyFueled.right
  have gPF := hgcd.comp (hi.pair hk)
  have pgPF := predc_polyFueled.comp gPF
  have denPF := PolyFueled.left.comp (hdm.comp (pgPF.pair hk))
  refine ⟨_, (ifzSel_polyFueled.comp
    (((PolyFueled.const 1).pair denPF).pair hk)).of_eq fun m => ?_⟩
  simp only [Nat.unpair_pair, ifzSelFn]
  by_cases hk0 : m.unpair.2.unpair.1 = 0
  · rw [if_pos hk0, queryRat, hk0]
    simp
  · rw [if_neg hk0, queryRat]
    have hg : 0 < Nat.gcd m.unpair.2.unpair.2 m.unpair.2.unpair.1 :=
      Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hk0)
    have hg1 : (Nat.gcd m.unpair.2.unpair.2 m.unpair.2.unpair.1).pred + 1 =
        Nat.gcd m.unpair.2.unpair.2 m.unpair.2.unpair.1 :=
      Nat.succ_pred_eq_of_pos hg
    rw [hg1, ComputableLUV.natCast_div_den hk0]

/-- The implication shell in symbol form: in the normal form `🡒` is `∼· ⋎ ·`. -/
lemma encodeArithmeticFormulaSymbols_imp {k : ℕ}
    (A B : ArithmeticSemiformula ℕ k) :
    encodeArithmeticFormulaSymbols (A 🡒 B) =
      16 :: (encodeArithmeticFormulaSymbols (∼A) ++
        encodeArithmeticFormulaSymbols B) := by
  show encodeArithmeticFormulaSymbols ((∼A).or B) = _
  rw [encodeArithmeticFormulaSymbols]

/-- De Morgan negation is length preserving on the normal-form encoding: it swaps dual
tags and fixes every term token. -/
lemma encodeArithmeticFormulaSymbols_neg_length {k : ℕ}
    (φ : ArithmeticSemiformula ℕ k) :
    (encodeArithmeticFormulaSymbols (∼φ)).length =
      (encodeArithmeticFormulaSymbols φ).length := by
  induction φ with
  | verum => rfl
  | falsum => rfl
  | rel r v => rcases r with _ | _ <;> rfl
  | nrel r v => rcases r with _ | _ <;> rfl
  | and φ ψ ihφ ihψ =>
      show (encodeArithmeticFormulaSymbols ((∼φ).or (∼ψ))).length = _
      simp [encodeArithmeticFormulaSymbols, ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
      show (encodeArithmeticFormulaSymbols ((∼φ).and (∼ψ))).length = _
      simp [encodeArithmeticFormulaSymbols, ihφ, ihψ]
  | all φ ih =>
      show (encodeArithmeticFormulaSymbols ((∼φ).exs)).length = _
      simp [encodeArithmeticFormulaSymbols, ih]
  | exs φ ih =>
      show (encodeArithmeticFormulaSymbols ((∼φ).all)).length = _
      simp [encodeArithmeticFormulaSymbols, ih]

/-- The threshold syntax of a rational query is structurally emittable. -/
lemma paperRatGt_polySegStream :
    PolySegStream (fun m => encodeArithmeticFormulaSymbols
      ((paperRatGtDef (queryRat m) : ArithmeticSemisentence 1) :
        ArithmeticSemiformula ℕ 1)) := by
  obtain ⟨cn, hnum⟩ := queryNum_polyFueled
  obtain ⟨cd, hden⟩ := queryDen_polyFueled
  refine (((PolySegStream.constList ratGtPre).append
    (encNumeral_polySegStream hnum)).append
      ((PolySegStream.constList ratGtMid).append
        (encNumeral_polySegStream hden))).of_eq fun m => ?_
  rw [enc_paperRatGtDef _ (queryRat_nonneg m)]
  simp [List.append_assoc]

/-! ### The threshold body as source

The paper writes the threshold body as one implication node over the LUV's defining
formula and the fixed comparison template, so the emitted run is three constant tokens,
the LUV's own source run, and the template with its two reduced numerals.  Nothing is
duplicated and no negation is pushed through the antecedent. -/

/-- The paper's threshold body written in the source language: `X ⟹ value > r`. -/
def paperThresholdSource (s : ArithSource 1) (r : ℚ) : ArithSource 1 :=
  .imp s (ArithSource.ofNNF
    ((paperRatGtDef r : ArithmeticSemisentence 1) : ArithmeticSemiformula ℕ 1))

/-- A source naming a LUV's defining formula names that LUV's threshold body. -/
lemma compile_paperThresholdSource (X : PaperLUV T) (s : ArithSource 1) (r : ℚ)
    (hs : ArithSource.compile s =
      ((X.formula : ArithmeticSemisentence 1) : ArithmeticSemiformula ℕ 1)) :
    ArithSource.compile (paperThresholdSource s r) = paperThresholdBody X r := by
  show ArithSource.compile s 🡒 _ = _
  rw [hs, paperThresholdBody]
  simp only [ArithSource.compile_ofNNF, LogicalConnective.HomClass.map_imply]

/-- The threshold bodies of a source-metered family are source-metered: one constant
tag, the family's own run, and the constant comparison template. -/
lemma paperThresholdSource_polyArithmeticSourceSeq {s : ℕ → ArithSource 1}
    (hs : PolyArithmeticSourceSeq s) :
    PolyArithmeticSourceSeq (fun m =>
      paperThresholdSource (s m.unpair.1) (queryRat m)) := by
  have hX : PolySegStream (fun m => ArithSource.sourceTokens (s m.unpair.1)) :=
    PolySegStream.comp hs PolyFueled.left
  exact ((PolySegStream.constList [21]).append
    (hX.append paperRatGt_polySegStream)).of_eq fun m => by
      simp [paperThresholdSource, ArithSource.sourceTokens, ArithSource.ofNNF]

/-- An efficiently presented family of literal paper LUVs.  The certificate is
structural emission of the *source* the paper writes for each LUV's defining formula —
never a bound on Foundation codes, a caller-provided tag-`5` code, or a semantic handle.
Everything the threshold syntax adds on top (the implication node, the fixed comparison
template, and the reduced numerals of the query rational) is discharged internally.

`source` is the paper's own writing of the defining formula, in the primitive
connectives `¬ ∧ ∨ ⟹ ⟺` of tex:560 and the quantifiers `∀ ∃` of tex:568-573;
`compiles` says it denotes the LUV's Foundation normal form; and `structural` meters that
writing — one token per *source* node.  That
is `def:ec`'s own count: the paper's writer emits the formula as written, and the
normal-form expansion of `⟹` and `⟺` happens inside the parser, off the stream.  Large
values are reached by *naming* them compactly: the class is inhabited both by
`unitFracPaperLUVSeq` at `1/(n+1)` and by `dyadicPaperLUVSeq` at `2⁻ⁿ`, whose denominator
`2 ^ n` is named in `O(n)` symbols by `binNumeral`, and by the biconditional family
`iffPaperLUVSeq`, whose Foundation normal form is exponentially larger than its name.
The same `2⁻ⁿ` spelled with Foundation's *unary* numeral has no certificate
(`unaryRendering_two_pow_not_polyArithmeticSourceSeq`), which is an artifact of that
numeral rather than a restriction the paper imposes.  `PaperLUV` itself carries no such
field; only the sequence wrapper does, and this wrapper is the route from a literal
first-order paper LUV into `LUV.RpnThresholdCodeSeq`, with `PaperLUV.rpnThresholdCodes`
its single-LUV corollary.
Paper node: `def:luv` -/
structure PaperLUVSeq (T : ArithmeticTheory) [T.Δ₁] where
  /-- The literal paper LUVs. -/
  luv : ℕ → PaperLUV T
  /-- The paper's own writing of each defining formula, in the primitive connectives of
  tex:560 and the quantifiers of tex:568-573. -/
  source : ℕ → ArithSource 1
  /-- That writing denotes the LUV's Foundation normal form. -/
  compiles : ∀ n, ArithSource.compile (source n) =
    (((luv n).formula : ArithmeticSemisentence 1) : ArithmeticSemiformula ℕ 1)
  /-- `def:ec`'s metering on that writing — one token per source node. -/
  structural : PolyArithmeticSourceSeq source

/-- The threshold bodies inherit the family's structural certificate. -/
lemma PaperLUVSeq.thresholdSource_structural (X : PaperLUVSeq T) :
    PolyArithmeticSourceSeq (fun m =>
      paperThresholdSource (X.source m.unpair.1) (queryRat m)) :=
  paperThresholdSource_polyArithmeticSourceSeq X.structural

/-- **A family presented by normal-form leaves.**  The commonest way to build a
`PaperLUVSeq`: take the LUVs' own defining formulas as the written sources, certified in
the normal-form-metered foil, which embeds into the paper's class by
`PolyArithmeticFormulaSeq.toSource`.  A family whose writing is genuinely smaller than its
normal form is built from the closure calculus instead — see `iffPaperLUVSeq`. -/
def PaperLUVSeq.ofNNF (luv : ℕ → PaperLUV T)
    (h : PolyArithmeticFormulaSeq (fun n =>
      (((luv n).formula : ArithmeticSemisentence 1) : ArithmeticSemiformula ℕ 1))) :
    PaperLUVSeq T where
  luv := luv
  source n := ArithSource.ofNNF
    (((luv n).formula : ArithmeticSemisentence 1) : ArithmeticSemiformula ℕ 1)
  compiles _ := rfl
  structural := h.toSource

/-- Any single literal paper LUV presents as a constant family, its own defining formula
read as a one-leaf source.  This is a convenience, not the non-vacuity witness: see
`unitFracPaperLUVSeq` for a family whose defining formulas genuinely vary with `n`. -/
def PaperLUVSeq.const (X : PaperLUV T) : PaperLUVSeq T :=
  PaperLUVSeq.ofNNF (fun _ => X) (PolySegStream.constList _)

/-- The literal threshold syntax of a paper-LUV family is emittable in the source-metered
calculus, so the abstract LUVs it compiles to carry the threshold-code certificate the
expectation layer consumes.
Paper node: `def:ec` -/
lemma PaperLUVSeq.rpnThresholdCodeSeq (X : PaperLUVSeq T) :
    LUV.RpnThresholdCodeSeq (fun n => (X.luv n).toLUV) := by
  have h := structuredPaperSourceDecomposeAll_rpnSentenceCodes
    (fun m => paperThresholdSource (X.source m.unpair.1) (queryRat m))
    X.thresholdSource_structural
  refine h.of_eq fun m => ?_
  rw [compile_paperThresholdSource (X.luv m.unpair.1) _ _ (X.compiles _)]
  exact (paperLUV_gt_eq _ _).symm

/-- **The single-LUV route.**  A *single* literal paper LUV carries the non-sequence
threshold-code certificate `LUV.RpnThresholdCodes`, which is what the whole-LUV endpoints
take as a hypothesis (`LUV.expect_converges`, `thm:ec`).  It is the constant family
(`PaperLUVSeq.const`) reindexed along the poly-fueled map `m ↦ ⟨0, m⟩`, which turns the
sequence's `⟨n, ⟨k, i⟩⟩` convention into the single-LUV `⟨k, i⟩` one.  No efficiency
hypothesis is needed: a constant formula family is trivially token-metered, so this holds of
*every* `PaperLUV`.  Kind `C`; hypotheses `(a)`.
Paper node: `def:ec` -/
lemma PaperLUV.rpnThresholdCodes (X : PaperLUV T) : X.toLUV.RpnThresholdCodes := by
  have h : RpnSentenceCodes (fun m => (((PaperLUVSeq.const X).luv m.unpair.1).toLUV).gt
      ((m.unpair.2.unpair.2 : ℚ) / (m.unpair.2.unpair.1 : ℚ))) :=
    (PaperLUVSeq.const X).rpnThresholdCodeSeq
  have hf : PolyFueled _ (fun m : ℕ => Nat.pair 0 m) :=
    (PolyFueled.const 0).pair PolyFueled.id
  show RpnSentenceCodes _
  exact (h.comp hf).of_eq fun m => by simp [PaperLUVSeq.const, PaperLUVSeq.ofNNF]

/-! ### Concrete families

The interface is inhabited by genuinely varying families.  Both are reciprocals `1/v` of a
denominator named by a single closed term, so one template and one pair of model arguments
serve them: `invFormula` is the template and `invPaperLUV` discharges uniqueness and
unit-interval membership from the denominator term's *value* alone, in any theory extending
`𝗜𝚺₁`, by completeness over its models.  The two instances differ only in how that value is
named — `unitFracPaperLUVSeq` has value `1/(n+1)` with a unary numeral, `dyadicPaperLUVSeq`
has value `2⁻ⁿ` with the compact numeral of `2 ^ n`. -/

/-- The reciprocal template: the pair code of `1 / d`, with the denominator named once by
the closed term `d`. -/
def invFormula (d : Semiterm.Const ℒₒᵣ) : ArithmeticSemisentence 1 :=
  “q. ∃ b, !!d = b ∧ !pairDef q 1 b”

/-- **The reciprocal paper LUV.**  A closed `ℒₒᵣ` term of positive standard value `v` names
the literal paper LUV of value `1/v`; uniqueness and unit-interval membership are derived in
`T` by completeness from the term's value and nothing else.  That is what makes the *naming*
of the denominator — unary numeral or compact term — a free choice at this layer.
Kind `C`; hypotheses `(a)`.
Paper node: `def:luv` -/
def invPaperLUV (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T]
    (d : Semiterm.Const ℒₒᵣ) (v : ℕ) (hv : 0 < v)
    (hval : ∀ (M : Type) [ORingStructure M] [_i : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻],
      Semiterm.Operator.val (M := M) ![] d = (v : M)) :
    PaperLUV T where
  formula := invFormula d
  unique := by
    apply LO.FirstOrder.Arithmetic.complete T
    intro (M : Type) _ hM
    letI : 𝗜𝗢𝗽𝗲𝗻 ⪯ T :=
      Entailment.WeakerThan.trans (𝓣 := 𝗜𝚺₁) inferInstance inferInstance
    haveI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 :=
      ModelsTheory.of_provably_subtheory M 𝗜𝗢𝗽𝗲𝗻 T inferInstance
    simp [models_iff, invFormula, pairDef, hval M]
    rcases Nat.lt_or_ge 1 v with h1 | h1
    · simp [h1, Nat.not_le.mpr h1]
    · simp [Nat.not_lt.mpr h1, h1]
  unit := by
    apply LO.FirstOrder.Arithmetic.complete T
    intro (M : Type) _ hM
    letI : 𝗜𝗢𝗽𝗲𝗻 ⪯ T :=
      Entailment.WeakerThan.trans (𝓣 := 𝗜𝚺₁) inferInstance inferInstance
    haveI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 :=
      ModelsTheory.of_provably_subtheory M 𝗜𝗢𝗽𝗲𝗻 T inferInstance
    simp [models_iff, invFormula, pairDef, paperRatUnitDef, hval M]
    have hv1 : 1 ≤ v := hv
    intro x hx
    refine ⟨1, (v : M), ?_, ?_, ?_⟩
    · rcases hx with ⟨h1, rfl⟩ | ⟨h1, rfl⟩
      · exact Or.inl ⟨by exact_mod_cast h1, rfl⟩
      · have hv2 : v = 1 := by omega
        subst hv2
        exact Or.inr ⟨by simp, by push_cast; ring⟩
    · exact_mod_cast hv
    · exact_mod_cast hv1

/-- The value `1/(n+1)`: the code of that fraction, with the denominator named once by the
unary numeral `n + 1`. -/
def unitFracFormula (n : ℕ) : ArithmeticSemisentence 1 :=
  invFormula (Semiterm.Operator.numeral ℒₒᵣ (n + 1))

/-- The value `2⁻ⁿ`: the same code, with the denominator named once by the *compact*
numeral of `2 ^ n`.  The value is superpolynomially small; the name is `O(n)` symbols. -/
def dyadicFormula (n : ℕ) : ArithmeticSemisentence 1 :=
  invFormula (binNumeral (2 ^ n))

private def unitFracPost : List ℕ :=
  [3, 0, 16, 15, 13, 6, 3, 0, 11, 3, 2, 0, 7, 8, 3, 0, 3, 0, 6, 15, 16, 11, 3, 0,
   6, 13, 3, 0, 6, 11, 3, 2, 0, 7, 7, 8, 6, 6, 6, 3, 0]

private lemma oringNumOne_term :
    (Semiterm.Operator.numeral ℒₒᵣ 1).term =
      Semiterm.func Language.One.one ![] := rfl

/-- The numeral encoding in the normal form the frame computation leaves behind. -/
private lemma encNumeral_norm (k v : ℕ) (hv : v ≠ 0) :
    encodeArithmeticTermSymbols
      (((Rew.subst ![]) (Rew.emb (Semiterm.Operator.numeral ℒₒᵣ v).term)) :
        ArithmeticSemiterm ℕ k) =
      List.replicate (v - 1) 7 ++ List.replicate v 6 := by
  have h := encodeArithmeticTermSymbols_numeral (k := k) v hv
  simpa [Semiterm.Operator.const, Semiterm.Operator.operator] using h

/-- The compact-numeral encoding in the same normal form. -/
private lemma binNumeral_norm (k v : ℕ) :
    encodeArithmeticTermSymbols
      (((Rew.subst ![]) (Rew.emb (binNumeral v).term)) : ArithmeticSemiterm ℕ k) =
      binNumeralEnc v := by
  have h := encodeArithmeticTermSymbols_binNumeral (k := k) v
  simpa [Semiterm.Operator.const, Semiterm.Operator.operator] using h

/-- The reciprocal template is a fixed frame around the denominator's own symbols: with a
unary numeral the frame encloses that numeral's `2 * v - 1` symbols. -/
private lemma enc_invFormula_numeral (v : ℕ) (hv : v ≠ 0) :
    encodeArithmeticFormulaSymbols
      ((invFormula (Semiterm.Operator.numeral ℒₒᵣ v) : ArithmeticSemisentence 1) :
        ArithmeticSemiformula ℕ 1) =
      [18, 15, 11] ++ (List.replicate (v - 1) 7 ++ List.replicate v 6) ++
        unitFracPost := by
  rw [invFormula]
  simp [pairDef, encodeArithmeticFormulaSymbols, encodeArithmeticTermSymbols,
    encodeStructuredNat, unitFracPost,
    Semiformula.Operator.lt_def, Semiformula.Operator.eq_def,
    Semiformula.Operator.le_def, Semiterm.Operator.operator,
    Semiterm.Operator.const, oringMul_term, oringAdd_term,
    oringNumOne_term, Matrix.fun_eq_vec_two,
    emb_subst_nil_comm, encNumeral_norm _ v hv]

/-- The same frame around the compact numeral's symbols. -/
private lemma enc_invFormula_binNumeral (v : ℕ) :
    encodeArithmeticFormulaSymbols
      ((invFormula (binNumeral v) : ArithmeticSemisentence 1) :
        ArithmeticSemiformula ℕ 1) =
      [18, 15, 11] ++ binNumeralEnc v ++ unitFracPost := by
  rw [invFormula]
  simp [pairDef, encodeArithmeticFormulaSymbols, encodeArithmeticTermSymbols,
    encodeStructuredNat, unitFracPost,
    Semiformula.Operator.lt_def, Semiformula.Operator.eq_def,
    Semiformula.Operator.le_def, Semiterm.Operator.operator,
    Semiterm.Operator.const, oringMul_term, oringAdd_term,
    oringNumOne_term, Matrix.fun_eq_vec_two,
    emb_subst_nil_comm, binNumeral_norm _ v]

private lemma enc_unitFracFormula (n : ℕ) :
    encodeArithmeticFormulaSymbols
      ((unitFracFormula n : ArithmeticSemisentence 1) : ArithmeticSemiformula ℕ 1) =
      [18, 15, 11] ++ (List.replicate n 7 ++ List.replicate (n + 1) 6) ++
        unitFracPost := by
  rw [unitFracFormula]
  simpa using enc_invFormula_numeral (n + 1) (by omega)

private lemma enc_dyadicFormula (n : ℕ) :
    encodeArithmeticFormulaSymbols
      ((dyadicFormula n : ArithmeticSemisentence 1) : ArithmeticSemiformula ℕ 1) =
      [18, 15, 11] ++ binNumeralEnc (2 ^ n) ++ unitFracPost :=
  enc_invFormula_binNumeral (2 ^ n)

/-- The literal paper LUV of value `1/(n+1)`. -/
def unitFracPaperLUV (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] (n : ℕ) :
    PaperLUV T :=
  invPaperLUV T (Semiterm.Operator.numeral ℒₒᵣ (n + 1)) (n + 1) (by omega)
    (fun M _ _ => by simp [numeral_eq_natCast])

/-- The literal paper LUV of value `2⁻ⁿ`. -/
def dyadicPaperLUV (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] (n : ℕ) :
    PaperLUV T :=
  invPaperLUV T (binNumeral (2 ^ n)) (2 ^ n) (by positivity)
    (fun M _ _ => binNumeral_val (M := M) (2 ^ n))

/-- The defining formulas of the `1/(n+1)` family are structurally emittable. -/
lemma unitFrac_polyArithmeticFormulaSeq :
    PolyArithmeticFormulaSeq (fun n =>
      ((unitFracFormula n : ArithmeticSemisentence 1) :
        ArithmeticSemiformula ℕ 1)) := by
  have hid : PolyFueled _ (fun n : ℕ => n) := PolyFueled.id
  have hsucc : PolyFueled _ (fun n : ℕ => n + 1) := PolyFueled.id.succ_comp
  refine ((PolySegStream.constList [18, 15, 11]).append
    (((PolySegStream.repeatTag 7 hid).append
      (PolySegStream.repeatTag 6 hsucc)).append
        (PolySegStream.constList unitFracPost))).of_eq fun n => ?_
  rw [enc_unitFracFormula n]
  simp

/-- **Non-vacuity** (`N+`): a genuinely varying family of literal paper LUVs, with
values `1/(n+1)`, carrying the structural certificate.
Paper node: `def:luv` -/
def unitFracPaperLUVSeq (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] : PaperLUVSeq T :=
  PaperLUVSeq.ofNNF (fun n => unitFracPaperLUV T n) unitFrac_polyArithmeticFormulaSeq

/-- **The literal paper frontend**: an efficiently presented family of literal
first-order paper LUVs is both semantically valued on every completed world of the
canonical theorem process and efficiently thresholded in the source-metered emission
calculus.

This is a statement about `PaperLUVSeq`, **not** about every `PaperLUV` sequence: the
`source`/`compiles`/`structural` fields are extra data `PaperLUV` does not carry.  They are
the paper's own `def:ec` condition on the defining formula — polynomially many symbols of
the formula *as the paper writes it* — and the interface is inhabited across the range the
paper uses: `unitFracPaperLUVSeq_frontend` at `1/(n+1)`, `dyadicPaperLUVSeq_frontend` at
the superpolynomially small `2⁻ⁿ`, and `iffPaperLUVSeq_frontend` at a family whose written
form is linear and whose Foundation normal form is exponential.
Paper node: `def:luv` -/
lemma PaperLUVSeq.source_valued_and_rpnThresholdCodeSeq [𝗜𝚺₁ ⪯ T]
    (X : PaperLUVSeq T) :
    (∀ n, ∀ v : PCWorld, v.ConsistentWithTheory (paperTheoryDP T) →
        ∃ x : ℝ, v.ValuesAt (X.luv n).toLUV x) ∧
      LUV.RpnThresholdCodeSeq (fun n => (X.luv n).toLUV) :=
  ⟨fun n => PaperLUV.source_valued (X.luv n), X.rpnThresholdCodeSeq⟩

/-- **The frontend on a concrete family**: the literal `1/(n+1)` LUVs are valued on every
completed world of the canonical theorem process and efficiently thresholded, so the
frontend's two conclusions hold of an actual first-order family rather than only of a
hypothetical one.
Paper node: `def:luv` -/
lemma unitFracPaperLUVSeq_frontend [𝗜𝚺₁ ⪯ T] :
    (∀ n, ∀ v : PCWorld, v.ConsistentWithTheory (paperTheoryDP T) →
        ∃ x : ℝ, v.ValuesAt ((unitFracPaperLUVSeq T).luv n).toLUV x) ∧
      LUV.RpnThresholdCodeSeq (fun n => ((unitFracPaperLUVSeq T).luv n).toLUV) :=
  (unitFracPaperLUVSeq T).source_valued_and_rpnThresholdCodeSeq

/-- The defining formulas of the `2⁻ⁿ` family are structurally emittable: the compact
numeral of `2 ^ n` is `n` copies of the doubling block, so the whole formula is a fixed
frame around a poly-fueled repeating run. -/
lemma dyadic_polyArithmeticFormulaSeq :
    PolyArithmeticFormulaSeq (fun n =>
      ((dyadicFormula n : ArithmeticSemisentence 1) :
        ArithmeticSemiformula ℕ 1)) := by
  refine ((PolySegStream.constList [18, 15, 11]).append
    (binNumeralEnc_two_pow_polySegStream.append
      (PolySegStream.constList unitFracPost))).of_eq fun n => ?_
  rw [enc_dyadicFormula n]
  simp

/-- **Non-vacuity** (`N+`) at a superpolynomially small value: the family of literal paper
LUVs of value `2⁻ⁿ` carries the structural certificate.  This is the value the paper writes
as `X > 2⁻ⁿ`; it is admissible here because the class meters the *formula string*, and the
compact numeral names `2 ^ n` in `O(n)` symbols.  Kind `N+`; hypotheses `(a)`.
Paper node: `def:luv` -/
def dyadicPaperLUVSeq (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] : PaperLUVSeq T :=
  PaperLUVSeq.ofNNF (fun n => dyadicPaperLUV T n) dyadic_polyArithmeticFormulaSeq

/-- **The frontend at `2⁻ⁿ`**: the literal paper LUVs of value `2⁻ⁿ` are valued on every
completed world of the canonical theorem process and efficiently thresholded.  Together with
`unitFracPaperLUVSeq_frontend` this shows the class is not confined to values of polynomial
denominator.
Paper node: `def:luv` -/
lemma dyadicPaperLUVSeq_frontend [𝗜𝚺₁ ⪯ T] :
    (∀ n, ∀ v : PCWorld, v.ConsistentWithTheory (paperTheoryDP T) →
        ∃ x : ℝ, v.ValuesAt ((dyadicPaperLUVSeq T).luv n).toLUV x) ∧
      LUV.RpnThresholdCodeSeq (fun n => ((dyadicPaperLUVSeq T).luv n).toLUV) :=
  (dyadicPaperLUVSeq T).source_valued_and_rpnThresholdCodeSeq

/-- **A Foundation numeral artifact, not a narrowing of the class.**  The *same* value `2⁻ⁿ`
has an admissible rendering — `dyadicPaperLUVSeq`, whose denominator is the compact numeral
`binNumeral (2 ^ n)` — and an inadmissible one: spell the denominator with Foundation's
*unary* `Semiterm.Operator.numeral` and the formula string itself is `2 ^ n` symbols long,
which no polynomial bounds.

The unary cost is an artifact of Foundation's default numeral, **not** a property of the
paper: the paper fixes no numeral notation — its underline convention (tex:564) substitutes
whatever expression stands for the value, and its examples write numerals as digits.
What matters for faithfulness is that the *value* is nameable compactly inside
`ℒₒᵣ` — `binNumeral v` has `O(log v)` nodes — so on numerals neither class is narrower
than `def:ec`, and this lemma documents that artifact rather than a gap.  It is stated for both
classes, since the artifact is a property of the *name* and survives the move to the source
metering: `unaryRendering_two_pow_not_polyArithmeticSourceSeq` is the statement about the
class `PaperLUVSeq` actually uses.  Kind `P`; hypotheses `(a)`.
Paper node: `def:ec` -/
lemma unaryRendering_two_pow_not_polyArithmeticFormulaSeq :
    ¬ PolyArithmeticFormulaSeq (fun n =>
      ((invFormula (Semiterm.Operator.numeral ℒₒᵣ (2 ^ n)) :
        ArithmeticSemisentence 1) : ArithmeticSemiformula ℕ 1)) := by
  rintro ⟨ct, cl, tokenFn, lenFn, ht, hl, hlen, hget⟩
  obtain ⟨b, hrun, hpb, hbb⟩ := hl
  refine not_isPolyBounded_two_pow (hpb.of_le fun n => ?_)
  have h : (encodeArithmeticFormulaSymbols
      ((invFormula (Semiterm.Operator.numeral ℒₒᵣ (2 ^ n)) : ArithmeticSemisentence 1) :
        ArithmeticSemiformula ℕ 1)).length = lenFn n := hlen n
  rw [enc_invFormula_numeral (2 ^ n) (by positivity)] at h
  have hp : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  simp only [List.length_append, List.length_replicate, List.length_cons,
    List.length_nil, unitFracPost] at h
  omega

/-- **The same numeral artifact, at the live class.**  Read as a one-leaf source, the
unary rendering of `2⁻ⁿ` is inadmissible in this class too: `ofNNF` emits the normal form
token for token, so the artifact of Foundation's unary numeral is not repaired by moving
the meter to the source — and does not need to be, since `binNumeral` names the same value
in `O(n)` symbols (`dyadicPaperLUVSeq`).  Kind `P`; hypotheses `(a)`.
Paper node: `def:ec` -/
lemma unaryRendering_two_pow_not_polyArithmeticSourceSeq :
    ¬ PolyArithmeticSourceSeq (fun n => ArithSource.ofNNF
      ((invFormula (Semiterm.Operator.numeral ℒₒᵣ (2 ^ n)) :
        ArithmeticSemisentence 1) : ArithmeticSemiformula ℕ 1)) :=
  fun h => unaryRendering_two_pow_not_polyArithmeticFormulaSeq h

/-! ### The strictness separation `PolyArithmeticFormulaSeq ⊊ PolyArithmeticSourceSeq`

`⟺` is one of the paper's primitive connectives (tex:560) and `def:ec` (tex:753) meters
the formula *as the paper writes it*.  Foundation's `Semiformula` has no biconditional
constructor: `a 🡘 b` is notation for `(∼a ⋎ b) ⋏ (∼b ⋎ a)`, duplicating both sides.
Metering the normal form therefore charges an `n`-deep `⟺` nest `2^Ω(n)` where the paper
charges `O(n)`.  That is the whole reason the classes are two: `PolyArithmeticSourceSeq`
is the paper's condition, and `PolyArithmeticFormulaSeq` is the strictly finer
normal-form-metered class it strictly contains.

`iffChain` separates them on the nose.  It has **no** `PolyArithmeticFormulaSeq`
certificate (`iffChain_not_polyArithmeticFormulaSeq`) and it **does** have a
`PolyArithmeticSourceSeq` one (`iffChainSource_polyArithmeticSourceSeq`), at exactly
`5n + 4` emitted tokens (`sourceTokens_iffChainSource_length`).  With
`PolyArithmeticFormulaSeq.toSource` giving the inclusion, the containment is strict. -/

/-- The biconditional shell in symbol form.  Unlike `🡒`, which costs `1 + |a| + |b|` in
the normal form (`encodeArithmeticFormulaSymbols_imp` and
`encodeArithmeticFormulaSymbols_neg_length`), `🡘` charges **both** sides **twice**. -/
lemma encodeArithmeticFormulaSymbols_iff {k : ℕ} (a b : ArithmeticSemiformula ℕ k) :
    (encodeArithmeticFormulaSymbols (a 🡘 b)).length =
      3 + 2 * (encodeArithmeticFormulaSymbols a).length
        + 2 * (encodeArithmeticFormulaSymbols b).length := by
  show (encodeArithmeticFormulaSymbols ((a 🡒 b) ⋏ (b 🡒 a))).length = _
  rw [show ((a 🡒 b) ⋏ (b 🡒 a)) = Semiformula.and (a 🡒 b) (b 🡒 a) from rfl,
    encodeArithmeticFormulaSymbols, encodeArithmeticFormulaSymbols_imp,
    encodeArithmeticFormulaSymbols_imp]
  simp [encodeArithmeticFormulaSymbols_neg_length]
  omega

/-- The atom the biconditional chain is built from: `x₀ = 0`. -/
def iffChainAtom : ArithmeticSemisentence 1 :=
  Semiformula.rel Language.ORing.Rel.eq ![.bvar 0, .func Language.ORing.Func.zero ![]]

/-- The left-nested biconditional chain `(⋯((A ⟺ A) ⟺ A) ⋯ ⟺ A)`, `n` levels deep, over
the fixed atom `A = iffChainAtom`.  In the paper's own language — where `⟺` is a primitive
connective (tex:560) — writing this out is `O(n)` characters, so it is exactly the kind of
family `def:ec` (tex:753) asks a polynomial-time writer to produce. -/
def iffChain : ℕ → ArithmeticSemisentence 1
  | 0 => iffChainAtom
  | n + 1 => iffChain n 🡘 iffChainAtom

lemma enc_iffChainAtom : encodeArithmeticFormulaSymbols
    ((iffChainAtom : ArithmeticSemisentence 1) : ArithmeticSemiformula ℕ 1) =
    [11, 3, 0, 5] := by
  simp [iffChainAtom, encodeArithmeticFormulaSymbols, encodeArithmeticTermSymbols,
    encodeStructuredNat, Matrix.fun_eq_vec_two]

lemma emb_iffChain_succ (n : ℕ) :
    ((iffChain (n + 1) : ArithmeticSemisentence 1) : ArithmeticSemiformula ℕ 1) =
      ((iffChain n : ArithmeticSemisentence 1) : ArithmeticSemiformula ℕ 1) 🡘
        ((iffChainAtom : ArithmeticSemisentence 1) : ArithmeticSemiformula ℕ 1) := by
  simp [iffChain]

private lemma encode_iffChain_length_succ (n : ℕ) :
    (encodeArithmeticFormulaSymbols
      ((iffChain (n + 1) : ArithmeticSemisentence 1) :
        ArithmeticSemiformula ℕ 1)).length =
      3 + 2 * (encodeArithmeticFormulaSymbols
        ((iffChain n : ArithmeticSemisentence 1) : ArithmeticSemiformula ℕ 1)).length
        + 2 * (encodeArithmeticFormulaSymbols
          ((iffChainAtom : ArithmeticSemisentence 1) :
            ArithmeticSemiformula ℕ 1)).length := by
  rw [emb_iffChain_succ, encodeArithmeticFormulaSymbols_iff]

/-- Each `⟺` level at least doubles the normal-form node count, so the chain is
exponential *there* — while the source that names it stays linear. -/
lemma two_pow_le_encode_iffChain : ∀ n : ℕ,
    2 ^ n ≤ (encodeArithmeticFormulaSymbols
      ((iffChain n : ArithmeticSemisentence 1) : ArithmeticSemiformula ℕ 1)).length
  | 0 => by
      rw [show ((iffChain 0 : ArithmeticSemisentence 1) : ArithmeticSemiformula ℕ 1) =
        ((iffChainAtom : ArithmeticSemisentence 1) : ArithmeticSemiformula ℕ 1) from rfl,
        enc_iffChainAtom]
      simp
  | n + 1 => by
      have ih := two_pow_le_encode_iffChain n
      rw [encode_iffChain_length_succ n]
      have : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
      omega

/-- **The chain is injective**: each `⟺` level strictly lengthens the normal form, so
distinct chain heights are distinct formulas.  What the `thm:incons` witnesses need in order
to exhibit a genuinely *infinite* day-theory, where the axioms are separated as sentences and
not merely as written sources.

Kind `C` (composition).  Provenance: (a) derived in-project from
`encode_iffChain_length_succ`; (b) Mathlib citation — `strictMono_nat_of_lt_succ`. -/
lemma iffChain_injective : Function.Injective iffChain := by
  have hmono : StrictMono fun n : ℕ => (encodeArithmeticFormulaSymbols
      ((iffChain n : ArithmeticSemisentence 1) : ArithmeticSemiformula ℕ 1)).length := by
    refine strictMono_nat_of_lt_succ fun n => ?_
    rw [encode_iffChain_length_succ n]
    omega
  exact fun a b h => hmono.injective (by rw [h])

/-- **The separation, negative half.**  `iffChain` is `def:ec`-writable in the paper's
language — `O(n)` characters, `⟺` being one of the paper's primitive connectives
(tex:560) — and yet has **no** certificate in the normal-form-metered class, because the
NNF substrate expands each `⟺` into a conjunction of two implications and so doubles per
nesting level.

This is why `PaperLUVSeq` meters the *source* and not the normal form: the class this
lemma excludes `iffChain` from is not the paper's `def:ec`, it is the strictly finer
foil.  The positive half is `iffChainSource_polyArithmeticSourceSeq`, and the family the
two together certify is `iffPaperLUVSeq`.  Kind `P`; hypotheses `(a)`.
Paper node: `def:ec` -/
lemma iffChain_not_polyArithmeticFormulaSeq :
    ¬ PolyArithmeticFormulaSeq (fun n =>
      ((iffChain n : ArithmeticSemisentence 1) : ArithmeticSemiformula ℕ 1)) := by
  rintro ⟨ct, cl, tokenFn, lenFn, ht, hl, hlen, hget⟩
  obtain ⟨b, hrun, hpb, hbb⟩ := hl
  exact not_isPolyBounded_two_pow (hpb.of_le fun n => by
    rw [← hlen n]; exact two_pow_le_encode_iffChain n)

/-! ### The chain as a source

One `iff` node per level, one leaf per atom: the emitted run of `iffChainSource n` is
`n` copies of the tag `22` followed by `n + 1` copies of the four-token atom. -/

/-- The paper's writing of `iffChain n`: `⟺` is a source constructor, so the run grows by
five tokens per level. -/
def iffChainSource : ℕ → ArithSource 1
  | 0 => ArithSource.ofNNF
      ((iffChainAtom : ArithmeticSemisentence 1) : ArithmeticSemiformula ℕ 1)
  | n + 1 => .iff (iffChainSource n) (ArithSource.ofNNF
      ((iffChainAtom : ArithmeticSemisentence 1) : ArithmeticSemiformula ℕ 1))

/-- The source names the chain: compiling it produces the exponentially larger normal
form, once, off the emitted stream. -/
lemma compile_iffChainSource : ∀ n : ℕ, ArithSource.compile (iffChainSource n) =
    ((iffChain n : ArithmeticSemisentence 1) : ArithmeticSemiformula ℕ 1)
  | 0 => rfl
  | n + 1 => by
      rw [iffChainSource, ArithSource.compile, compile_iffChainSource n,
        ArithSource.compile_ofNNF, emb_iffChain_succ]

lemma sourceTokens_iffChainSource : ∀ n : ℕ,
    ArithSource.sourceTokens (iffChainSource n) =
      List.replicate n 22 ++ (List.range (n + 1)).flatMap (fun _ => [11, 3, 0, 5])
  | 0 => by
      rw [iffChainSource, ArithSource.sourceTokens_ofNNF, enc_iffChainAtom]
      simp
  | n + 1 => by
      rw [iffChainSource, ArithSource.sourceTokens, sourceTokens_iffChainSource n,
        ArithSource.sourceTokens_ofNNF, enc_iffChainAtom]
      rw [List.range_succ (n := n + 1), List.flatMap_append]
      simp [List.replicate_succ]

/-- **The name is linear**: `5n + 4` tokens for a normal form of `≥ 2 ^ n` nodes. -/
lemma sourceTokens_iffChainSource_length (n : ℕ) :
    (ArithSource.sourceTokens (iffChainSource n)).length = 5 * n + 4 := by
  rw [sourceTokens_iffChainSource n]
  simp [List.length_flatMap]
  omega

/-- **The separation, positive half.**  The biconditional chain *is* efficiently
writable in the paper's source language: a repeated tag run and a repeated atom block,
both emitted with poly-fueled counts.
Paper node: `def:ec` -/
lemma iffChainSource_polyArithmeticSourceSeq : PolyArithmeticSourceSeq iffChainSource := by
  have hb : PolyTokenStream (fun _ : ℕ => [11, 3, 0, 5]) :=
    (PolyTokenStream.const 11).append <| (PolyTokenStream.const 3).append <|
      (PolyTokenStream.const 0).append (PolyTokenStream.const 5)
  have hsucc : PolyFueled _ (fun n : ℕ => n + 1) := PolyFueled.id.succ_comp
  have hblocks := PolySegStream.blocks hb 4 (fun _ => rfl) (by omega) hsucc
  exact ((PolySegStream.repeatTag 22 PolyFueled.id).append hblocks).of_eq fun n =>
    (sourceTokens_iffChainSource n).symm

/-- **Odd biconditional chains are valid.**  `A ⟺ A` is a theorem of pure logic and
`⊤ ⟺ A` is `A`, so the chain alternates: even levels are equivalent to the atom, odd
levels hold in every structure.  This is what makes `iffChain (2n+1)` an inert conjunct —
it changes nothing about which value a defining formula names, and multiplies the size of
the Foundation object naming it by `2^Ω(n)`.

*Proof kind:* `P` proved. -/
lemma iffChain_odd_valid {M : Type*} [Structure ℒₒᵣ M] (x : M) (n : ℕ) :
    Semiformula.Evalb (M := M) ![x] (iffChain (2 * n + 1)) := by
  have key : ∀ m : ℕ,
      (Semiformula.Evalb (M := M) ![x] (iffChain (2 * m)) ↔
        Semiformula.Evalb (M := M) ![x] iffChainAtom) ∧
      Semiformula.Evalb (M := M) ![x] (iffChain (2 * m + 1)) := by
    intro m
    induction m with
    | zero => constructor <;> simp [iffChain]
    | succ k ih =>
      obtain ⟨-, ih1⟩ := ih
      have he : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
      have ho : 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 := by ring
      refine ⟨?_, ?_⟩
      · rw [he, iffChain]
        simp [ih1]
      · rw [ho, iffChain, iffChain]
        simp [ih1]
  exact (key n).2

/-- **The reciprocal paper LUV, with an inert conjunct.**  A closed `ℒₒᵣ` term of positive
standard value `v` names the literal paper LUV of value `1/v`, and the defining formula may
carry any extra conjunct `ψ` that holds in every model of `𝗣𝗔⁻`: uniqueness and
unit-interval membership are derived in `T` by completeness from the term's value and the
validity of `ψ`, and nothing else.  `invPaperLUV` is the case with no conjunct (it is a
separate definition, since its formula must stay literally `invFormula d`); this is the
route to defining formulas that are large to *write down* without being large as values.
Kind `C`; hypotheses `(a)`.
Paper node: `def:luv` -/
def invPaperLUVWith (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T]
    (d : Semiterm.Const ℒₒᵣ) (v : ℕ) (hv : 0 < v)
    (hval : ∀ (M : Type) [ORingStructure M] [_i : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻],
      Semiterm.Operator.val (M := M) ![] d = (v : M))
    (ψ : ArithmeticSemisentence 1)
    (hψ : ∀ (M : Type) [ORingStructure M] [_i : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] (x : M),
      Semiformula.Evalb (M := M) ![x] ψ) :
    PaperLUV T where
  formula := invFormula d ⋏ ψ
  unique := by
    apply LO.FirstOrder.Arithmetic.complete T
    intro (M : Type) _ hM
    letI : 𝗜𝗢𝗽𝗲𝗻 ⪯ T :=
      Entailment.WeakerThan.trans (𝓣 := 𝗜𝚺₁) inferInstance inferInstance
    haveI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 :=
      ModelsTheory.of_provably_subtheory M 𝗜𝗢𝗽𝗲𝗻 T inferInstance
    simp [models_iff, invFormula, pairDef, hval M, hψ M]
    rcases Nat.lt_or_ge 1 v with h1 | h1
    · simp [h1, Nat.not_le.mpr h1]
    · simp [Nat.not_lt.mpr h1, h1]
  unit := by
    apply LO.FirstOrder.Arithmetic.complete T
    intro (M : Type) _ hM
    letI : 𝗜𝗢𝗽𝗲𝗻 ⪯ T :=
      Entailment.WeakerThan.trans (𝓣 := 𝗜𝚺₁) inferInstance inferInstance
    haveI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 :=
      ModelsTheory.of_provably_subtheory M 𝗜𝗢𝗽𝗲𝗻 T inferInstance
    simp [models_iff, invFormula, pairDef, paperRatUnitDef, hval M, hψ M]
    have hv1 : 1 ≤ v := hv
    intro x hx
    refine ⟨1, (v : M), ?_, ?_, ?_⟩
    · rcases hx with ⟨h1, rfl⟩ | ⟨h1, rfl⟩
      · exact Or.inl ⟨by exact_mod_cast h1, rfl⟩
      · have hv2 : v = 1 := by omega
        subst hv2
        exact Or.inr ⟨by simp, by push_cast; ring⟩
    · exact_mod_cast hv
    · exact_mod_cast hv1

/-- **The biconditional-valued paper LUV.**  Value `1/1 = 1`, named by the numeral `1`,
with the valid chain `iffChain (2n+1)` conjoined onto the defining formula: `O(n)`
characters as the paper writes it, `≥ 2^(2n+1)` nodes once compiled into Foundation's
normal form.  Kind `C`; hypotheses `(a)`.
Paper node: `def:luv` -/
def iffPaperLUV (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] (n : ℕ) : PaperLUV T :=
  invPaperLUVWith T (Semiterm.Operator.numeral ℒₒᵣ 1) 1 (by omega)
    (fun M _ _ => by simp)
    (iffChain (2 * n + 1)) (fun M _ _ x => iffChain_odd_valid x n)

/-! ### The capstone family: `O(n)` characters to write, `2ⁿ` nodes once compiled

An odd biconditional chain is *valid*: `A ⟺ A` is a theorem of pure logic, and `⊤ ⟺ A` is
`A`, so `iffChain (2n+1)` holds in every structure.  Conjoining it to a defining formula
therefore changes nothing about the value the formula names — and multiplies the size of
the Foundation object naming it by `2^Ω(n)`.  That makes it the sharp test of what the
efficiency condition is metering: `iffPaperLUVSeq` is a family of *literal paper LUVs*
whose `n`-th defining formula the paper writes in `O(n)` characters, which is admitted
here (`iffPaperLUVSeq_frontend` reaches `LUV.RpnThresholdCodeSeq`), while the
normal-form-metered foil rejects its `⟺`-chain core
(`iffChain_not_polyArithmeticFormulaSeq`). -/

/-- The paper's writing of `iffPaperLUV`'s defining formula: the reciprocal template at
the numeral `1`, conjoined with the biconditional chain. -/
def iffPaperLUVSource (n : ℕ) : ArithSource 1 :=
  .and (ArithSource.ofNNF ((invFormula (Semiterm.Operator.numeral ℒₒᵣ 1) :
      ArithmeticSemisentence 1) : ArithmeticSemiformula ℕ 1))
    (iffChainSource (2 * n + 1))

lemma compile_iffPaperLUVSource (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] (n : ℕ) :
    ArithSource.compile (iffPaperLUVSource n) =
      (((iffPaperLUV T n).formula : ArithmeticSemisentence 1) :
        ArithmeticSemiformula ℕ 1) := by
  show ArithSource.compile _ ⋏ ArithSource.compile _ = _
  rw [ArithSource.compile_ofNNF, compile_iffChainSource]
  simp [iffPaperLUV, invPaperLUVWith]

/-- **The name stays linear.**  The chain contributes `5(2n+1) + 4` tokens and the
template a constant block, so the whole defining formula is written in `O(n)` tokens. -/
lemma iffPaperLUVSource_polyArithmeticSourceSeq :
    PolyArithmeticSourceSeq iffPaperLUVSource := by
  obtain ⟨cm, hm⟩ := mulc_polyFueled 2
  have hodd : PolyFueled _ (fun n : ℕ => 2 * n + 1) :=
    hm.succ_comp.of_eq fun n => by ring_nf
  exact PolyArithmeticSourceSeq.and (PolySegStream.constList _)
    (PolySegStream.comp iffChainSource_polyArithmeticSourceSeq hodd)

/-- **Non-vacuity** (`N+`) at a formula whose normal form is exponentially larger than its
name: the family of literal paper LUVs of value `1`, each defined by the reciprocal
template conjoined with the valid biconditional chain `iffChain (2n+1)`.  The conjunct is a
logical no-op — every model satisfies it — so the LUVs are the constant-`1` LUVs; what
varies is the *writing*, which is `O(n)` characters here and `≥ 2ⁿ` Foundation nodes after
compilation.  Its `⟺`-chain core is exactly what the normal-form-metered foil provably
excludes (`iffChain_not_polyArithmeticFormulaSeq` is stated at `iffChain`, not at this
conjunction; the separation is the point, the family is its LUV carrier).
Kind `N+`; hypotheses `(a)`.
Paper node: `def:luv` -/
def iffPaperLUVSeq (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] : PaperLUVSeq T where
  luv n := iffPaperLUV T n
  source := iffPaperLUVSource
  compiles n := compile_iffPaperLUVSource T n
  structural := iffPaperLUVSource_polyArithmeticSourceSeq

/-- **The frontend at a `def:ec`-linear, normal-form-exponential family.**  The literal
paper LUVs whose defining formulas nest `⟺` to depth `Ω(n)` are valued on every completed
world of the canonical theorem process and efficiently thresholded.  Together with
`iffChain_not_polyArithmeticFormulaSeq` this is the whole point of metering the source:
the paper's `def:ec` admits this family, and it is admitted here.
Paper node: `def:luv` -/
lemma iffPaperLUVSeq_frontend [𝗜𝚺₁ ⪯ T] :
    (∀ n, ∀ v : PCWorld, v.ConsistentWithTheory (paperTheoryDP T) →
        ∃ x : ℝ, v.ValuesAt ((iffPaperLUVSeq T).luv n).toLUV x) ∧
      LUV.RpnThresholdCodeSeq (fun n => ((iffPaperLUVSeq T).luv n).toLUV) :=
  (iffPaperLUVSeq T).source_valued_and_rpnThresholdCodeSeq

/-- A client consuming the witness: the expectation-of-indicators endpoint (`thm:ei`) takes
the threshold-code class as a hypothesis, and the `2⁻ⁿ` family discharges it outright. -/
example (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP] [𝗜𝚺₁ ⪯ T]
    (φ : ℕ → Sentence) (hφ : BigSentenceCodes φ)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hY : ∀ n, (((dyadicPaperLUVSeq T).luv n).toLUV).IsIndicator (φ n) DP) :
    AsympEq (fun n => (((dyadicPaperLUVSeq T).luv n).toLUV).expect P n)
      (fun n => P n (φ n)) :=
  lic_expectation_indicator P DP φ hφ _ (dyadicPaperLUVSeq T).rpnThresholdCodeSeq
    hcons hY

/-- A client of the single-LUV route: `thm:ec` applied at a *literal* paper LUV, the
`2⁻ⁿ`-valued one, with both representation hypotheses discharged from the frontend —
the threshold-code class by `PaperLUV.rpnThresholdCodes` and the world value by
`PaperLUV.source_valued`.  Only the paper's own consistency premise remains. -/
example (P : History) [𝗜𝚺₁ ⪯ T]
    [IsLogicalInductor P (paperTheoryDP T)] (n : ℕ)
    (hcons : ∀ k, ∃ v : PCWorld, v.ConsistentWith ((paperTheoryDP T).D k)) :
    ∃ L : ℝ, ConvergesTo ((dyadicPaperLUV T n).toLUV.expectSeq P) L :=
  LUV.expect_converges P (paperTheoryDP T) _ (dyadicPaperLUV T n).rpnThresholdCodes
    hcons (PaperLUV.source_valued _)

/-- A client at the capstone family: `thm:ei` consumes the threshold-code class, and the
biconditional family — whose defining formulas are `O(n)` characters to write and `≥ 2ⁿ`
Foundation nodes once compiled — discharges it outright. -/
example (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP] [𝗜𝚺₁ ⪯ T]
    (φ : ℕ → Sentence) (hφ : BigSentenceCodes φ)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hY : ∀ n, (((iffPaperLUVSeq T).luv n).toLUV).IsIndicator (φ n) DP) :
    AsympEq (fun n => (((iffPaperLUVSeq T).luv n).toLUV).expect P n)
      (fun n => P n (φ n)) :=
  lic_expectation_indicator P DP φ hφ _ (iffPaperLUVSeq T).rpnThresholdCodeSeq
    hcons hY

/-- The single-LUV route at the capstone family: `thm:ec` applied at a literal paper LUV
whose defining formula is exponentially larger than its name, with both representation
hypotheses discharged from the frontend. -/
example (P : History) [𝗜𝚺₁ ⪯ T]
    [IsLogicalInductor P (paperTheoryDP T)] (n : ℕ)
    (hcons : ∀ k, ∃ v : PCWorld, v.ConsistentWith ((paperTheoryDP T).D k)) :
    ∃ L : ℝ, ConvergesTo ((iffPaperLUV T n).toLUV.expectSeq P) L :=
  LUV.expect_converges P (paperTheoryDP T) _ (iffPaperLUV T n).rpnThresholdCodes
    hcons (PaperLUV.source_valued _)

/-! ### `def:blcp` over literal paper LUVs

`LUVCombination.BoundedSequence` (`Properties/ExpectationProperties.lean`) states the
paper's bounded LUV-combination sequence over the abstract threshold carrier `LUV`, which
admits families that are not the definable quantities of `def:luv`.  The layer below states
the same node over `PaperLUV`: the combination's shares are literal first-order paper LUVs,
and the abstract carrier is reached only through `toLUV`. -/

/-- A LUV-combination sequence whose shares are literal paper LUVs, together with the
paper's efficiency data for its constants and coefficients.  The fields other than `luvs`
are exactly those of `LUVCombinationSyntax`; `luvs` replaces its abstract `luv : ℕ → LUV`
with a structurally certified family of `PaperLUV`s.
Paper node: `def:blcp` -/
structure PaperLUVCombination (T : ArithmeticTheory) [T.Δ₁] where
  /-- The literal paper LUVs; the share at `⟨n,j⟩` is `luvs.luv (Nat.pair n j)`. -/
  luvs : PaperLUVSeq T
  /-- Number of shares in member `n`. -/
  termCount : ℕ → ℕ
  /-- Trailing constant feature of member `n`. -/
  const : ℕ → EF
  /-- Coefficient of the share at `⟨n,j⟩`. -/
  coefficient : ℕ → EF
  /-- The term count is polynomially computable. -/
  termCount_poly : ∃ c, PolyFueled c termCount
  /-- The constants are polynomially emittable. -/
  const_poly : BigSpliceStream (fun n => (const n).serialize)
  /-- The coefficients are polynomially emittable. -/
  coefficient_poly : BigSpliceStream (fun z => (coefficient z).serialize)
  /-- Constants read only prices of days already seen. -/
  const_rank : ∀ n, (const n).rank ≤ n
  /-- Coefficients read only prices of days already seen. -/
  coefficient_rank : ∀ n j, j < termCount n → (coefficient (Nat.pair n j)).rank ≤ n
  /-- Constants are closed: no free variable. -/
  const_closed : ∀ n ρ V, (const n).denoteWith ρ V = (const n).denote V
  /-- Coefficients are closed: no free variable. -/
  coefficient_closed : ∀ z ρ V, (coefficient z).denoteWith ρ V = (coefficient z).denote V

namespace PaperLUVCombination

/-- The combination sequence a paper-LUV presentation denotes, in the abstract carrier. -/
def combination (D : PaperLUVCombination T) : ℕ → LUVCombination := fun n =>
  { const := D.const n
    terms := (List.range (D.termCount n)).map (fun j =>
      (D.coefficient (Nat.pair n j), (D.luvs.luv (Nat.pair n j)).toLUV)) }

/-- The compact combination syntax of the denoted sequence.  Its threshold-code
certificate is the paper family's own structural one, so no code is assumed of the shares
beyond what their defining formulas supply. -/
def toSyntax (D : PaperLUVCombination T) : LUVCombinationSyntax D.combination where
  termCount := D.termCount
  coefficient := D.coefficient
  luv z := (D.luvs.luv z).toLUV
  termCount_poly := D.termCount_poly
  const_poly := D.const_poly
  coefficient_poly := D.coefficient_poly
  threshold_poly := D.luvs.rpnThresholdCodeSeq
  terms_eq _ := rfl
  const_rank := D.const_rank
  coefficient_rank := D.coefficient_rank
  const_closed := D.const_closed
  coefficient_closed := D.coefficient_closed

/-- **`def:blcp` at the paper's own LUVs.**  A polynomially presented combination sequence
over literal first-order paper LUVs, with one uniform `L¹` bound, is a bounded
LUV-combination sequence in the sense the expectation theorems consume.  Kind `C`;
hypotheses `(a)`.
Paper node: `def:blcp` -/
noncomputable def boundedSequence (D : PaperLUVCombination T) {P : History}
    (hB : ∃ B : ℝ, ∀ n, (D.combination n).l1Norm P ≤ B) :
    LUVCombination.BoundedSequence D.combination P where
  poly := D.toSyntax.polySequence
  bounded := hB

end PaperLUVCombination

/-- The single-share combination sequence `1 · X_n + 0` over the `1/(n+1)` paper LUVs.
Its shares genuinely vary with `n`.
Paper node: `def:blcp` -/
def unitFracPaperLUVCombination (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] :
    PaperLUVCombination T where
  luvs := unitFracPaperLUVSeq T
  termCount _ := 1
  const _ := .const 0
  coefficient _ := .const 1
  termCount_poly := ⟨_, PolyFueled.const 1⟩
  const_poly := BigSpliceStream.serialize_const 0
  coefficient_poly := BigSpliceStream.serialize_const 1
  const_rank n := Nat.zero_le n
  coefficient_rank n _ _ := Nat.zero_le n
  const_closed _ _ _ := by simp
  coefficient_closed _ _ _ := by simp

/-- **Non-vacuity** (`N+`) for `def:blcp` at the paper's own LUVs: the `1/(n+1)` family
presents a bounded combination sequence over every market, with `L¹` bound `1`.
Kind `N+`; hypotheses `(a)`.
Paper node: `def:blcp` -/
noncomputable def unitFracPaperLUVBoundedSequence
    (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] (P : History) :
    LUVCombination.BoundedSequence (unitFracPaperLUVCombination T).combination P :=
  (unitFracPaperLUVCombination T).boundedSequence
    ⟨1, fun n => by
      simp [PaperLUVCombination.combination, unitFracPaperLUVCombination,
        LUVCombination.l1Norm, LUVCombination.shareNorm]⟩

end Frontend

end LogicalInduction
