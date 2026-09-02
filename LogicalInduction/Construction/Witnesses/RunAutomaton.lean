/-
# Deciding a regular property of a token run, in polynomial time

`TokenFold.ifMatch_mem_FP` branches on "this word's token stream is exactly `ts`", for one
fixed token list `ts`.  That is enough while the property being decided is membership in a
finite list of constant runs, and not enough as soon as it is not — and it is not, for the
freeze: a sentence's complete spellings are not a finite set of constant token lists, because
Foundation's decoder is not injective and the structured arithmetic payload admits unbounded
zero padding.  Both of those are *regular* phenomena, so what replaces the constant list is
an automaton.

This file is that generalization, and nothing more: `BlockAutomaton` is a deterministic
automaton over token values with a bounded state set, presented twice — once as a
mathematical transition function `step : ℕ → ℕ → ℕ` and once as a `Complexity.FP` word
function `stepW`, tied together by `stepW_spec`, which says the word step's *output length*
is the mathematical step.  Carrying the state as a length is what makes the fold's own
polynomial bound available: `TokenFold.runFold_cli_mem_FP` bounds a step's output by
`cli.length + tok.length + c`, and `stepW_len` pays for that with the constant `Q`.

`ifAuto_mem_FP` is the consumer-facing form, the exact analogue of `ifMatch_mem_FP`.  The
proof is `matchPass_mem_FP`'s, with the fixed matcher `matchStepR ts` replaced by the
automaton's own step and the single acceptance test `= ts.length` replaced by a nest over
the finitely many accepting states.

`BlockMachine`, in the second half of the file, is the same construction with the bounded
state set dropped: an arbitrary *word* state growing by at most a constant per token, with
acceptance read off its leading bit.  That relaxation is not decoration — the structured
arithmetic leaf's unary length field is an `aⁿbⁿ` constraint and no finite-state device
decides it; the section comment there says exactly why.  Use `BlockAutomaton` where a
finite state set really does suffice, since it is much cheaper to instantiate.

Everything here is supporting infrastructure rather than a paper claim, so the declarations
are `lemma`s and `def`s.  Two of them — `guardedAutomaton` and
`BlockAutomaton.ifAuto_mem_FP` — are named by the `app:ifp` boundary note as the devices the
freeze recognizer runs on, so they carry that node and sit in the endpoint inventory; the
rest do not.
-/
import LogicalInduction.Framework.Machine.TokenFold
-- `Complexity.id_mem_FP` (the fixed-numeral guard tests the token word itself) lives in the
-- `Classes/P` root rather than the Cobham subtree `TokenFold` already reaches.
import Complexitylib.Classes.P

namespace LogicalInduction.RunAuto

open Complexity Complexity.Cobham LogicalInduction.FPFold LogicalInduction.TokenFold

/-! ## The interface -/

/-- **A deterministic automaton over a word's token blocks, presented in `Complexity.FP`.**

The state is a natural number below `Q`, carried through the fold as the *length* of the
client word.  `step` is the mathematical transition and `stepW` the word-level one; they are
tied by `stepW_spec`, which is demanded only at well-formed blocks — words of the form
`digitsToBits cur` with `cur` a run of digits below four, which is all the tokenizer ever
builds (see `FreezeStep.RunOracle.R_spec` for the same restriction and why it is not a
convenience).

`stepW_len` is the price of admission to `TokenFold.runFold_cli_mem_FP`: the fold bounds a
step's output by `cli.length + tok.length + c` for a constant `c`, and a bounded state set
supplies that with `c := Q`.  An automaton with unboundedly many states would not fit, and
that is the honest content of the bound rather than a technicality. -/
structure BlockAutomaton where
  /-- The state bound. -/
  Q : ℕ
  /-- The transition function, on token values. -/
  step : ℕ → ℕ → ℕ
  /-- States stay below the bound. -/
  step_le : ∀ i t, i ≤ Q → step i t ≤ Q
  /-- The word-level transition. -/
  stepW : List Bool → List Bool
  /-- It is polynomial time. -/
  stepW_FP : stepW ∈ FP
  /-- Its output is bounded by the state bound, on every input. -/
  stepW_len : ∀ v : List Bool, (stepW v).length ≤ Q
  /-- And on a well-formed block it computes `step`, in the length.

  The restriction to a *reachable* state (`cli.length ≤ Q`) is what lets the word step be
  a finite nest: a nest can only test the finitely many states it lists, and every state
  the fold actually visits is one of them (`stepW_len` at every step, `0` at the start). -/
  stepW_spec : ∀ (W cli : List Bool) (cur : List ℕ), cli.length ≤ Q → (∀ d ∈ cur, d < 4) →
    (stepW (pair W (pair cli (digitsToBits cur)))).length = step cli.length (digitVal cur)
  /-- The accepting states. -/
  accept : ℕ → Bool

namespace BlockAutomaton

variable (A : BlockAutomaton)

/-- The state after reading a token list from the initial state `0`. -/
def run (b : List ℕ) : ℕ := b.foldl A.step 0

/-- Whether the automaton accepts a token list. -/
def Accepts (b : List ℕ) : Bool := A.accept (A.run b)

lemma foldl_step_le (A : BlockAutomaton) : ∀ (b : List ℕ) (i : ℕ), i ≤ A.Q →
    List.foldl A.step i b ≤ A.Q
  | [], i, hi => hi
  | t :: b, i, hi => by
      rw [List.foldl_cons]
      exact foldl_step_le A b _ (A.step_le i t hi)

/-- Every reachable state is below the bound. -/
lemma run_le (b : List ℕ) : A.run b ≤ A.Q := foldl_step_le A b 0 (Nat.zero_le _)

/-! ## Running it over a word -/

/-- The automaton's step, at block granularity, with an empty parameter block. -/
def stepR (cli : List Bool) (cur : List ℕ) : List Bool :=
  A.stepW (pair [] (pair cli (digitsToBits cur)))

lemma length_stepR (cli : List Bool) (cur : List ℕ) (hcli : cli.length ≤ A.Q)
    (hcur : ∀ d ∈ cur, d < 4) :
    (A.stepR cli cur).length = A.step cli.length (digitVal cur) :=
  A.stepW_spec [] cli cur hcli hcur

lemma length_stepR_le (cli : List Bool) (cur : List ℕ) : (A.stepR cli cur).length ≤ A.Q :=
  A.stepW_len _

/-- **The fold's client state carries the automaton's state, in its length.**

Proof kind: `P` proved.  Provenance: (a) `stepW_spec`. -/
lemma runFold_stepR_length (A : BlockAutomaton) : ∀ (rs : List (List ℕ))
    (cli out : List Bool), cli.length ≤ A.Q → (∀ r ∈ rs, ∀ d ∈ r, d < 4) →
    (runFold A.stepR (fun _ _ => []) cli out rs).1.length
      = List.foldl A.step cli.length (rs.map digitVal)
  | [], cli, out, _, _ => by simp [runFold]
  | (r :: rs), cli, out, hcli, hrs => by
      have hr : ∀ d ∈ r, d < 4 := hrs r (List.mem_cons_self ..)
      have hrest : ∀ q ∈ rs, ∀ d ∈ q, d < 4 :=
        fun q hq => hrs q (List.mem_cons_of_mem _ hq)
      have hih := runFold_stepR_length A rs (A.stepR cli r) (out ++ [])
        (A.length_stepR_le cli r) hrest
      rw [runFold, hih, length_stepR A cli r hcli hr, List.map_cons, List.foldl_cons]

/-- The automaton, run over a word's blocks. -/
def pass (w : List Bool) : List Bool :=
  (runFold A.stepR (fun _ _ => []) [] [] (blockSplit (bitsToDigits w)).1).1

/-- **The pass computes the automaton's state on the word's token stream.**

Proof kind: `C` composition.  Provenance: (a) `runFold_stepR_length`;
(b) `undigitize_eq_blockSplit`. -/
lemma length_pass (w : List Bool) : (A.pass w).length = A.run (decodeBits w) := by
  have h := runFold_stepR_length A (blockSplit (bitsToDigits w)).1 [] []
    (by simp) (fun r hr => (blockSplit_digits_lt (bitsToDigits w)).1 r hr)
  rw [pass, h, run, decodeBits, undigitize_eq_blockSplit]
  rfl

lemma pass_mem_FP {Sf : List Bool → List Bool} (hSf : Sf ∈ FP) :
    (fun z => A.pass (Sf z)) ∈ FP :=
  runFold_cli_mem_FP
    (STEPr := fun W cli cur => A.stepW (pair W (pair cli (digitsToBits cur))))
    (EMITr := fun _ _ _ => []) (c := A.Q) (k := 0) (qQ := 0)
    A.stepW_FP (constFn_mem_FP []) (constFn_mem_FP []) hSf
    (fun _ _ _ => le_trans (A.stepW_len _) (by omega)) (fun _ _ _ => by simp)
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) [] []

end BlockAutomaton

/-! ## Branching on acceptance

The pass leaves the state in a *length*, so the acceptance test is a nest of length
comparisons — one per accepting state, of which there are at most `Q + 1`. -/

/-- A nest of length tests: take `X` as soon as the probe's length is one of the listed
values, and `Y` if none matches. -/
def eqLenNest (P X Y : List Bool → List Bool) : List ℕ → List Bool → List Bool
  | [], z => Y z
  | i :: is, z => if (P z).length = i then X z else eqLenNest P X Y is z

lemma eqLenNest_spec (P X Y : List Bool → List Bool) : ∀ (l : List ℕ) (z : List Bool),
    eqLenNest P X Y l z = if (P z).length ∈ l then X z else Y z
  | [], z => by rw [eqLenNest]; simp
  | (i :: l), z => by
      rw [eqLenNest, eqLenNest_spec P X Y l z]
      by_cases h : (P z).length = i
      · rw [if_pos h, if_pos (by rw [h]; exact List.mem_cons_self ..)]
      · rw [if_neg h]
        by_cases hm : (P z).length ∈ l
        · rw [if_pos hm, if_pos (List.mem_cons_of_mem _ hm)]
        · rw [if_neg hm, if_neg (by
            intro hc
            rcases List.mem_cons.mp hc with hc | hc
            · exact h hc
            · exact hm hc)]

lemma eqLenNest_mem_FP {P X Y : List Bool → List Bool} (hP : P ∈ FP) (hX : X ∈ FP)
    (hY : Y ∈ FP) : ∀ l : List ℕ, (fun z => eqLenNest P X Y l z) ∈ FP
  | [] => by
      have heq : (fun z => eqLenNest P X Y [] z) = Y := by funext z; rw [eqLenNest]
      rwa [heq]
  | (i :: l) => by
      have hrec := eqLenNest_mem_FP hP hX hY l
      have h := ifEqLen_mem_FP hP i hX hrec
      have heq : (fun z => if (P z).length = i then X z else eqLenNest P X Y l z)
          = fun z => eqLenNest P X Y (i :: l) z := by funext z; rw [eqLenNest]
      rwa [heq] at h

namespace BlockAutomaton

variable (A : BlockAutomaton)

/-- The accepting states, as an explicit list — finite because the state set is bounded. -/
def acceptList : List ℕ := (List.range (A.Q + 1)).filter fun i => A.accept i

lemma mem_acceptList {i : ℕ} (hi : i ≤ A.Q) : i ∈ A.acceptList ↔ A.accept i = true := by
  rw [acceptList, List.mem_filter]
  simp only [List.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩

/-- **Branching on "this automaton accepts this word's token stream" is polynomial time.**

The exact analogue of `TokenFold.ifMatch_mem_FP`, with a regular language in place of a
single constant run.

Proof kind: `C` composition.  Provenance: (a) `pass_mem_FP`, `length_pass`, `run_le`;
(b) `eqLenNest_mem_FP`.
Paper node: `app:ifp` -/
lemma ifAuto_mem_FP {S X Y : List Bool → List Bool} (hS : S ∈ FP) (hX : X ∈ FP)
    (hY : Y ∈ FP) :
    (fun z => if A.Accepts (decodeBits (S z)) = true then X z else Y z) ∈ FP := by
  have h := eqLenNest_mem_FP (A.pass_mem_FP hS) hX hY A.acceptList
  have heq : (fun z => eqLenNest (fun z => A.pass (S z)) X Y A.acceptList z)
      = fun z => if A.Accepts (decodeBits (S z)) = true then X z else Y z := by
    funext z
    rw [eqLenNest_spec, A.length_pass (S z)]
    by_cases hacc : A.Accepts (decodeBits (S z)) = true
    · rw [if_pos ((A.mem_acceptList (A.run_le _)).mpr hacc), if_pos hacc]
    · rw [if_neg (fun hc => hacc ((A.mem_acceptList (A.run_le _)).mp hc)), if_neg hacc]
  rwa [heq] at h

end BlockAutomaton

/-! ## Building one from a table

`BlockAutomaton` is an interface, and an interface with no inhabitant proves nothing.  This
section is the general inhabitant: **every** deterministic automaton whose state set is
bounded and whose token alphabet is bounded — tokens at or above the alphabet bound all
merged into one class — is a `BlockAutomaton`, hence decidable in polynomial time over a
machine's own output word.

The word step is a two-level nest of tests the toolkit already has: `ifEqLen_mem_FP` on the
client word's length, once per state, and inside each, `ifNumEq_mem_FP` on the token block
against a fixed numeral, once per letter.  Both levels are finite because both bounds are,
and the depth is a constant of the automaton rather than of the input.

The alphabet bound is not a limitation for the freeze's own use: the RPN grammar's framing
tokens are all small (tags `0`–`4`, the structured codec's `0`–`22`), and the one place a
token is *large* — an escape leaf's sentence code — is not a token the automaton branches on
by value, but one whose digit word a leaf test reads directly. -/

section Table

private def cliOf (v : List Bool) : List Bool := fstBlock (sndBlock v)
private def tokOf (v : List Bool) : List Bool := sndBlock (sndBlock v)

private lemma cliOf_pair (W cli tok : List Bool) : cliOf (pair W (pair cli tok)) = cli := by
  rw [cliOf, sndBlock_pair, fstBlock_pair]

private lemma tokOf_pair (W cli tok : List Bool) : tokOf (pair W (pair cli tok)) = tok := by
  rw [tokOf, sndBlock_pair, sndBlock_pair]

private lemma cliOf_mem_FP : cliOf ∈ FP := mem_FP_comp sndBlock_mem_FP fstBlock_mem_FP

private lemma tokOf_mem_FP : tokOf ∈ FP := mem_FP_comp sndBlock_mem_FP sndBlock_mem_FP

/-- The transition a table denotes: tokens at or above `A + 1` are one class, and the
result is clamped to the state bound so that `step_le` needs no hypothesis on `f`. -/
def tblStep (Q A : ℕ) (f : ℕ → ℕ → ℕ) (i t : ℕ) : ℕ := min (f i (min t (A + 1))) Q

lemma tblStep_le (Q A : ℕ) (f : ℕ → ℕ → ℕ) (i t : ℕ) : tblStep Q A f i t ≤ Q :=
  min_le_right _ _

/-- The inner nest: test the token block against each listed numeral, and fall through to
the merged class. -/
def tokNest (Q A : ℕ) (f : ℕ → ℕ → ℕ) (i : ℕ) : List ℕ → List Bool → List Bool
  | [], _ => List.replicate (min (f i (A + 1)) Q) true
  | t :: ts, v =>
      if NumEqBits t (tokOf v) then List.replicate (min (f i t) Q) true
      else tokNest Q A f i ts v

lemma length_tokNest_le (Q A : ℕ) (f : ℕ → ℕ → ℕ) (i : ℕ) :
    ∀ (l : List ℕ) (v : List Bool), (tokNest Q A f i l v).length ≤ Q
  | [], v => by rw [tokNest]; simp
  | (t :: l), v => by
      rw [tokNest]
      split_ifs
      · simp
      · exact length_tokNest_le Q A f i l v

lemma length_tokNest (Q A : ℕ) (f : ℕ → ℕ → ℕ) (i : ℕ) (W cli : List Bool) (cur : List ℕ)
    (hcur : ∀ d ∈ cur, d < 4) : ∀ (l : List ℕ), (∀ t ∈ l, t ≤ A) →
      (tokNest Q A f i l (pair W (pair cli (digitsToBits cur)))).length
        = if digitVal cur ∈ l then min (f i (digitVal cur)) Q else min (f i (A + 1)) Q
  | [], _ => by rw [tokNest]; simp
  | (t :: l), hl => by
      have hle : ∀ t' ∈ l, t' ≤ A := fun t' ht' => hl t' (List.mem_cons_of_mem _ ht')
      rw [tokNest, tokOf_pair]
      by_cases h : NumEqBits t (digitsToBits cur)
      · have hv : digitVal cur = t := (numEqBits_spec t cur hcur).mp h
        rw [if_pos h, if_pos (by rw [hv]; exact List.mem_cons_self ..), hv,
          List.length_replicate]
      · have hv : digitVal cur ≠ t := fun hc => h ((numEqBits_spec t cur hcur).mpr hc)
        rw [if_neg h, length_tokNest Q A f i W cli cur hcur l hle]
        by_cases hm : digitVal cur ∈ l
        · rw [if_pos hm, if_pos (List.mem_cons_of_mem _ hm)]
        · rw [if_neg hm, if_neg (by
            intro hc
            rcases List.mem_cons.mp hc with hc | hc
            · exact hv hc
            · exact hm hc)]

lemma tokNest_mem_FP (Q A : ℕ) (f : ℕ → ℕ → ℕ) (i : ℕ) :
    ∀ l : List ℕ, (fun v => tokNest Q A f i l v) ∈ FP
  | [] => by
      have heq : (fun v => tokNest Q A f i [] v)
          = fun _ : List Bool => List.replicate (min (f i (A + 1)) Q) true := by
        funext v; rw [tokNest]
      rw [heq]; exact constFn_mem_FP _
  | (t :: l) => by
      have hrec := tokNest_mem_FP Q A f i l
      have h := ifNumEq_mem_FP tokOf_mem_FP t
        (constFn_mem_FP (List.replicate (min (f i t) Q) true)) hrec
      have heq : (fun v => if NumEqBits t (tokOf v) then
            List.replicate (min (f i t) Q) true else tokNest Q A f i l v)
          = fun v => tokNest Q A f i (t :: l) v := by funext v; rw [tokNest]
      rwa [heq] at h

/-- The outer nest: dispatch on the state, carried as the client word's length. -/
def stNest (Q A : ℕ) (f : ℕ → ℕ → ℕ) : List ℕ → List Bool → List Bool
  | [], _ => []
  | i :: is, v =>
      if (cliOf v).length = i then tokNest Q A f i (List.range (A + 1)) v
      else stNest Q A f is v

lemma length_stNest_le (Q A : ℕ) (f : ℕ → ℕ → ℕ) :
    ∀ (l : List ℕ) (v : List Bool), (stNest Q A f l v).length ≤ Q
  | [], v => by rw [stNest]; simp
  | (i :: l), v => by
      rw [stNest]
      split_ifs
      · exact length_tokNest_le Q A f i _ v
      · exact length_stNest_le Q A f l v

lemma stNest_eq (Q A : ℕ) (f : ℕ → ℕ → ℕ) : ∀ (l : List ℕ) (v : List Bool),
    (cliOf v).length ∈ l →
    stNest Q A f l v = tokNest Q A f (cliOf v).length (List.range (A + 1)) v
  | [], v, hm => absurd hm (by simp)
  | (i :: l), v, hm => by
      rw [stNest]
      by_cases h : (cliOf v).length = i
      · rw [if_pos h, h]
      · rw [if_neg h]
        exact stNest_eq Q A f l v (by
          rcases List.mem_cons.mp hm with hc | hc
          · exact absurd hc h
          · exact hc)

lemma stNest_mem_FP (Q A : ℕ) (f : ℕ → ℕ → ℕ) :
    ∀ l : List ℕ, (fun v => stNest Q A f l v) ∈ FP
  | [] => by
      have heq : (fun v => stNest Q A f [] v) = fun _ : List Bool => ([] : List Bool) := by
        funext v; rw [stNest]
      rw [heq]; exact constFn_mem_FP _
  | (i :: l) => by
      have hrec := stNest_mem_FP Q A f l
      have h := ifEqLen_mem_FP cliOf_mem_FP i
        (tokNest_mem_FP Q A f i (List.range (A + 1))) hrec
      have heq : (fun v => if (cliOf v).length = i then
            tokNest Q A f i (List.range (A + 1)) v else stNest Q A f l v)
          = fun v => stNest Q A f (i :: l) v := by funext v; rw [stNest]
      rwa [heq] at h

/-- **Every bounded-state, bounded-alphabet automaton is a `BlockAutomaton`.**

The one non-formal content is that the two nests are *finite*: `List.range (Q + 1)` states
and `List.range (A + 1)` letters, so the word step is a fixed-depth composition of tests
already in the toolkit rather than a scan.

Kind `N+` non-vacuity witness — this is what makes `BlockAutomaton` inhabited.
Provenance: (a) `stNest_eq`, `length_tokNest`, `numEqBits_spec`;
(b) `TokenFold.ifEqLen_mem_FP`, `TokenFold.ifNumEq_mem_FP`. -/
def tableAutomaton (Q A : ℕ) (f : ℕ → ℕ → ℕ) (acc : ℕ → Bool) : BlockAutomaton where
  Q := Q
  step := tblStep Q A f
  step_le := fun i t _ => tblStep_le Q A f i t
  stepW := stNest Q A f (List.range (Q + 1))
  stepW_FP := stNest_mem_FP Q A f _
  stepW_len := fun v => length_stNest_le Q A f _ v
  stepW_spec := by
    intro W cli cur hcli hcur
    have hmem : (cliOf (pair W (pair cli (digitsToBits cur)))).length
        ∈ List.range (Q + 1) := by
      rw [cliOf_pair]; simp only [List.mem_range]; omega
    rw [stNest_eq Q A f _ _ hmem, cliOf_pair,
      length_tokNest Q A f cli.length W cli cur hcur (List.range (A + 1))
        (by intro t ht; simp only [List.mem_range] at ht; omega),
      tblStep]
    by_cases hv : digitVal cur ≤ A
    · have hm : min (digitVal cur) (A + 1) = digitVal cur := min_eq_left (by omega)
      rw [hm, if_pos (by simp only [List.mem_range]; omega)]
    · have hm : min (digitVal cur) (A + 1) = A + 1 := min_eq_right (by omega)
      rw [hm, if_neg (by simp only [List.mem_range]; omega)]
  accept := acc

@[simp] lemma tableAutomaton_Q (Q A : ℕ) (f : ℕ → ℕ → ℕ) (acc : ℕ → Bool) :
    (tableAutomaton Q A f acc).Q = Q := rfl

@[simp] lemma tableAutomaton_step (Q A : ℕ) (f : ℕ → ℕ → ℕ) (acc : ℕ → Bool) :
    (tableAutomaton Q A f acc).step = tblStep Q A f := rfl

@[simp] lemma tableAutomaton_accept (Q A : ℕ) (f : ℕ → ℕ → ℕ) (acc : ℕ → Bool) :
    (tableAutomaton Q A f acc).accept = acc := rfl

end Table

/-! ## Guards: dispatching on an arbitrary polynomial-time property of a token

`tableAutomaton` branches on a token's *value* against fixed numerals.  That is right for
framing tokens and useless at the one place a token is large: an escape leaf carries a whole
sentence code, and the question there is not "is this value `17`" but "does this code decode
to `χ`" — a polynomial-time property of the token's digit word that no finite alphabet
enumerates.

`TokGuard` is that generalization.  A guard is an `FP` word function together with the
value-level predicate it decides, the two tied by `gW_spec` at well-formed blocks; the
convention is that the word function returns a one-bit word on success and the empty word on
failure, so the branch is `TokenFold.ifEqLen_mem_FP` at `1`.  `litGuard` recovers the
fixed-numeral test, so `guardedAutomaton` subsumes `tableAutomaton` — the latter is kept
because it is much cheaper to instantiate when the alphabet really is finite.

This is the interface at which a *missing* primitive is isolated rather than diffused: an
automaton whose guards are all `litGuard`s is unconditionally available, and each guard that
needs real arithmetic on a token's digits is one named `FP` obligation, discharged or not on
its own. -/

/-- A polynomial-time test on one token, with the value-level predicate it decides. -/
structure TokGuard where
  /-- The predicate on the token's value. -/
  P : ℕ → Bool
  /-- The word-level test: a one-bit word on success, empty on failure. -/
  gW : List Bool → List Bool
  /-- It is polynomial time. -/
  gW_FP : gW ∈ FP
  /-- And it decides `P`, on every well-formed block. -/
  gW_spec : ∀ cur : List ℕ, (∀ d ∈ cur, d < 4) →
    ((gW (digitsToBits cur)).length = 1 ↔ P (digitVal cur) = true)

/-- The fixed-numeral guard. -/
def litGuard (t : ℕ) : TokGuard where
  P := fun u => decide (u = t)
  gW := fun w => if NumEqBits t w then [true] else []
  gW_FP := ifNumEq_mem_FP Complexity.id_mem_FP t (constFn_mem_FP [true]) (constFn_mem_FP [])
  gW_spec := by
    intro cur hcur
    by_cases h : NumEqBits t (digitsToBits cur)
    · rw [if_pos h]
      simp only [List.length_singleton, decide_eq_true_eq, true_iff]
      exact (numEqBits_spec t cur hcur).mp h
    · rw [if_neg h]
      simp only [List.length_nil, decide_eq_true_eq]
      constructor
      · intro hc; exact absurd hc (by omega)
      · intro hc; exact absurd ((numEqBits_spec t cur hcur).mpr hc) h

/-- One state's dispatch: try the guards in order, and fall through to `dflt`. -/
structure GuardRow where
  /-- The guards, each with the state it moves to. -/
  guards : List (TokGuard × ℕ)
  /-- Where an unguarded token goes. -/
  dflt : ℕ

/-- The value-level meaning of a row. -/
def rowStep : List (TokGuard × ℕ) → ℕ → ℕ → ℕ
  | [], d, _ => d
  | (g, q) :: gs, d, t => if g.P t = true then q else rowStep gs d t

/-- Its word-level nest. -/
def rowNest (Q : ℕ) : List (TokGuard × ℕ) → ℕ → List Bool → List Bool
  | [], d, _ => List.replicate (min d Q) true
  | (g, q) :: gs, d, v =>
      if (g.gW (tokOf v)).length = 1 then List.replicate (min q Q) true
      else rowNest Q gs d v

lemma length_rowNest_le (Q : ℕ) : ∀ (gs : List (TokGuard × ℕ)) (d : ℕ) (v : List Bool),
    (rowNest Q gs d v).length ≤ Q
  | [], d, v => by rw [rowNest]; simp
  | ((g, q) :: gs), d, v => by
      rw [rowNest]
      split_ifs
      · simp
      · exact length_rowNest_le Q gs d v

lemma length_rowNest (Q : ℕ) (W cli : List Bool) (cur : List ℕ) (hcur : ∀ d ∈ cur, d < 4) :
    ∀ (gs : List (TokGuard × ℕ)) (d : ℕ),
      (rowNest Q gs d (pair W (pair cli (digitsToBits cur)))).length
        = min (rowStep gs d (digitVal cur)) Q
  | [], d => by rw [rowNest, rowStep]; simp
  | ((g, q) :: gs), d => by
      rw [rowNest, rowStep, tokOf_pair]
      by_cases h : g.P (digitVal cur) = true
      · rw [if_pos ((g.gW_spec cur hcur).mpr h), if_pos h, List.length_replicate]
      · rw [if_neg (fun hc => h ((g.gW_spec cur hcur).mp hc)), if_neg h,
          length_rowNest Q W cli cur hcur gs d]

lemma rowNest_mem_FP (Q : ℕ) : ∀ (gs : List (TokGuard × ℕ)) (d : ℕ),
    (fun v => rowNest Q gs d v) ∈ FP
  | [], d => by
      have heq : (fun v => rowNest Q [] d v)
          = fun _ : List Bool => List.replicate (min d Q) true := by
        funext v; rw [rowNest]
      rw [heq]; exact constFn_mem_FP _
  | ((g, q) :: gs), d => by
      have hg : (fun v => g.gW (tokOf v)) ∈ FP := by
        simpa [Function.comp_def] using mem_FP_comp tokOf_mem_FP g.gW_FP
      have hrec := rowNest_mem_FP Q gs d
      have h := ifEqLen_mem_FP hg 1
        (constFn_mem_FP (List.replicate (min q Q) true)) hrec
      have heq : (fun v => if (g.gW (tokOf v)).length = 1 then
            List.replicate (min q Q) true else rowNest Q gs d v)
          = fun v => rowNest Q ((g, q) :: gs) d v := by funext v; rw [rowNest]
      rwa [heq] at h

/-- The outer nest over states, as in `stNest` but with a guard row per state. -/
def gstNest (Q : ℕ) (rows : ℕ → GuardRow) : List ℕ → List Bool → List Bool
  | [], _ => []
  | i :: is, v =>
      if (cliOf v).length = i then rowNest Q (rows i).guards (rows i).dflt v
      else gstNest Q rows is v

lemma length_gstNest_le (Q : ℕ) (rows : ℕ → GuardRow) :
    ∀ (l : List ℕ) (v : List Bool), (gstNest Q rows l v).length ≤ Q
  | [], v => by rw [gstNest]; simp
  | (i :: l), v => by
      rw [gstNest]
      split_ifs
      · exact length_rowNest_le Q _ _ v
      · exact length_gstNest_le Q rows l v

lemma gstNest_eq (Q : ℕ) (rows : ℕ → GuardRow) : ∀ (l : List ℕ) (v : List Bool),
    (cliOf v).length ∈ l →
    gstNest Q rows l v
      = rowNest Q (rows (cliOf v).length).guards (rows (cliOf v).length).dflt v
  | [], v, hm => absurd hm (by simp)
  | (i :: l), v, hm => by
      rw [gstNest]
      by_cases h : (cliOf v).length = i
      · rw [if_pos h, h]
      · rw [if_neg h]
        exact gstNest_eq Q rows l v (by
          rcases List.mem_cons.mp hm with hc | hc
          · exact absurd hc h
          · exact hc)

lemma gstNest_mem_FP (Q : ℕ) (rows : ℕ → GuardRow) :
    ∀ l : List ℕ, (fun v => gstNest Q rows l v) ∈ FP
  | [] => by
      have heq : (fun v => gstNest Q rows [] v)
          = fun _ : List Bool => ([] : List Bool) := by funext v; rw [gstNest]
      rw [heq]; exact constFn_mem_FP _
  | (i :: l) => by
      have hrec := gstNest_mem_FP Q rows l
      have h := ifEqLen_mem_FP cliOf_mem_FP i
        (rowNest_mem_FP Q (rows i).guards (rows i).dflt) hrec
      have heq : (fun v => if (cliOf v).length = i then
            rowNest Q (rows i).guards (rows i).dflt v else gstNest Q rows l v)
          = fun v => gstNest Q rows (i :: l) v := by funext v; rw [gstNest]
      rwa [heq] at h

/-- **A guarded automaton is a `BlockAutomaton`.**

Each state carries an ordered list of polynomial-time guards; the first that fires chooses
the successor.  With `litGuard`s this is `tableAutomaton`; with a guard that reads a token's
digits it is strictly more, and that is the whole point — the escape leaf's decode test is
one guard and one obligation.

Kind `N+` non-vacuity witness.  Provenance: (a) `gstNest_eq`, `length_rowNest`;
(b) `TokenFold.ifEqLen_mem_FP`.
Paper node: `app:ifp` -/
def guardedAutomaton (Q : ℕ) (rows : ℕ → GuardRow) (acc : ℕ → Bool) : BlockAutomaton where
  Q := Q
  step := fun i t => min (rowStep (rows i).guards (rows i).dflt t) Q
  step_le := fun _ _ _ => min_le_right _ _
  stepW := gstNest Q rows (List.range (Q + 1))
  stepW_FP := gstNest_mem_FP Q rows _
  stepW_len := fun v => length_gstNest_le Q rows _ v
  stepW_spec := by
    intro W cli cur hcli hcur
    have hmem : (cliOf (pair W (pair cli (digitsToBits cur)))).length
        ∈ List.range (Q + 1) := by
      rw [cliOf_pair]; simp only [List.mem_range]; omega
    rw [gstNest_eq Q rows _ _ hmem, cliOf_pair,
      length_rowNest Q W cli cur hcur (rows cli.length).guards (rows cli.length).dflt]
  accept := acc

@[simp] lemma guardedAutomaton_Q (Q : ℕ) (rows : ℕ → GuardRow) (acc : ℕ → Bool) :
    (guardedAutomaton Q rows acc).Q = Q := rfl

@[simp] lemma guardedAutomaton_step (Q : ℕ) (rows : ℕ → GuardRow) (acc : ℕ → Bool) :
    (guardedAutomaton Q rows acc).step
      = fun i t => min (rowStep (rows i).guards (rows i).dflt t) Q := rfl

@[simp] lemma guardedAutomaton_accept (Q : ℕ) (rows : ℕ → GuardRow) (acc : ℕ → Bool) :
    (guardedAutomaton Q rows acc).accept = acc := rfl


/-! ## Counters: when a bounded state set is not enough

`BlockAutomaton` fixes the number of states, which is the right shape for a propositional
spelling pattern — there the alternatives per node are two, and the whole nest is finite.
It is **not** enough for the structured arithmetic leaf, and the reason is worth recording
rather than discovering twice.

A structured leaf is spelled `[1, 0, pol] ++ 1^L ++ [0] ++ p ++ [19]`, where the unary field
`1^L` must equal the payload's own token count `|p|` (`parseStructuredPaperPrime` takes
`p.2.take p.1` and demands the parse consume all of it).  `L` is unbounded even for a fixed
target code, because `parseStructuredNat` has a self-loop at the numeral `0` — `1 :: rest ↦
2 * ·` maps `0` to `0`, so `1^k 0` spells the numeral `0` for every `k`.  Matching `1^L`
against `|p| = L` is `aⁿbⁿ`, and no finite-state device decides it.

What *is* available is a **counter**: `TokenFold.runFold_cli_mem_FP` bounds a step's output
by `cli.length + tok.length + c`, so a client state may grow by a constant per token and
still stay inside `Complexity.FP`.  `BlockMachine` is that relaxation — an arbitrary word
state, with acceptance decided by a client-supplied `FP` test rather than read off a finite
list.  The finite-state case remains available above and is cheaper to instantiate; use the
machine only where a count is genuinely needed.

The acceptance test is a *field* rather than a fixed convention (a leading bit, say) for a
concrete reason: a structured-leaf recognizer must carry both a finite payload-automaton
state and an unbounded counter, and the natural way to keep two fields in one `FP`-legible
word is `Complexity.Cobham.pair`, whose projections `fstBlock`/`sndBlock` are `FP` while its
*leading bit* is an artifact of the pairing rather than anything the client chose.  Fixing
acceptance to the leading bit would therefore have made the interface unusable by exactly
the client it exists for. -/

/-- **A polynomial-time transducer over a word's token blocks, with an unbounded state.**

The state is an arbitrary *word* rather than a bounded number, growing by at most `c` per
token — enough for a unary counter, which is exactly what the structured arithmetic leaf's
length field needs and what `BlockAutomaton` cannot supply.

Acceptance is the state's leading bit, so the state is required to be nonempty (`init_ne`,
`step_ne`): `Complexity.Cobham.selectHead` reads `head?`, and on the empty word it selects
neither branch. -/
structure BlockMachine where
  /-- The per-token growth allowance. -/
  c : ℕ
  /-- The initial state. -/
  init : List Bool
  /-- The transition, on a state word and a token value. -/
  step : List Bool → ℕ → List Bool
  /-- Which states accept. -/
  accept : List Bool → Bool
  /-- The word-level acceptance test: a one-bit word on success. -/
  acceptW : List Bool → List Bool
  /-- It is polynomial time. -/
  acceptW_FP : acceptW ∈ FP
  /-- And it decides `accept`. -/
  acceptW_spec : ∀ s : List Bool, (acceptW s).length = 1 ↔ accept s = true
  /-- The word-level transition. -/
  stepW : List Bool → List Bool
  /-- It is polynomial time. -/
  stepW_FP : stepW ∈ FP
  /-- Its output grows by at most a constant per token. -/
  stepW_len : ∀ W cli tok : List Bool,
    (stepW (pair W (pair cli tok))).length ≤ cli.length + tok.length + c
  /-- And on a well-formed block it computes `step`, ignoring the parameter block. -/
  stepW_spec : ∀ (W cli : List Bool) (cur : List ℕ), (∀ d ∈ cur, d < 4) →
    stepW (pair W (pair cli (digitsToBits cur))) = step cli (digitVal cur)

namespace BlockMachine

variable (M : BlockMachine)

/-- The state after reading a token list. -/
def run (b : List ℕ) : List Bool := b.foldl M.step M.init

/-- Whether the machine accepts a token list. -/
def Accepts (b : List ℕ) : Bool := M.accept (M.run b)

/-- The transition, at block granularity. -/
def stepR (cli : List Bool) (cur : List ℕ) : List Bool := M.step cli (digitVal cur)

lemma runFold_stepR (M : BlockMachine) : ∀ (rs : List (List ℕ)) (cli out : List Bool),
    (runFold M.stepR (fun _ _ => []) cli out rs).1 = List.foldl M.step cli (rs.map digitVal)
  | [], cli, out => by simp [runFold]
  | (r :: rs), cli, out => by
      rw [runFold, runFold_stepR M rs (M.stepR cli r) (out ++ []), List.map_cons,
        List.foldl_cons, stepR]

/-- The machine, run over a word's blocks. -/
def pass (w : List Bool) : List Bool :=
  (runFold M.stepR (fun _ _ => []) M.init [] (blockSplit (bitsToDigits w)).1).1

/-- **The pass computes the machine's state on the word's token stream.** -/
lemma pass_eq (w : List Bool) : M.pass w = M.run (decodeBits w) := by
  rw [pass, runFold_stepR, run, decodeBits, undigitize_eq_blockSplit]

lemma pass_mem_FP {Sf : List Bool → List Bool} (hSf : Sf ∈ FP) :
    (fun z => M.pass (Sf z)) ∈ FP :=
  runFold_cli_mem_FP (STEPr := fun _ cli cur => M.step cli (digitVal cur))
    (EMITr := fun _ _ _ => []) (c := M.c) (k := 0) (qQ := 0)
    M.stepW_FP (constFn_mem_FP []) (constFn_mem_FP []) hSf
    M.stepW_len (fun _ _ _ => by simp)
    (fun W cli cur h => M.stepW_spec W cli cur h) (fun _ _ _ _ => rfl) M.init []

/-- **Branching on "this machine accepts this word's token stream" is polynomial time.**

The counter analogue of `ifAuto_mem_FP`.

Proof kind: `C` composition.  Provenance: (a) `pass_eq`, `acceptW_spec`;
(b) `TokenFold.ifEqLen_mem_FP`. -/
lemma ifRun_mem_FP {S X Y : List Bool → List Bool} (hS : S ∈ FP) (hX : X ∈ FP)
    (hY : Y ∈ FP) :
    (fun z => if M.Accepts (decodeBits (S z)) = true then X z else Y z) ∈ FP := by
  have hacc : (fun z => M.acceptW (M.pass (S z))) ∈ FP := by
    simpa [Function.comp_def] using mem_FP_comp (M.pass_mem_FP hS) M.acceptW_FP
  have h := ifEqLen_mem_FP hacc 1 hX hY
  have heq : (fun z => if (M.acceptW (M.pass (S z))).length = 1 then X z else Y z)
      = fun z => if M.Accepts (decodeBits (S z)) = true then X z else Y z := by
    funext z
    have hspec := M.acceptW_spec (M.pass (S z))
    rw [M.pass_eq (S z)] at hspec
    by_cases hacc' : M.Accepts (decodeBits (S z)) = true
    · rw [if_pos (by rw [M.pass_eq (S z)]; exact hspec.mpr hacc'), if_pos hacc']
    · rw [if_neg (fun hc => hacc' (hspec.mp (by rw [← M.pass_eq (S z)]; exact hc))),
        if_neg hacc']
  rwa [heq] at h

end BlockMachine

#print axioms LogicalInduction.RunAuto.tableAutomaton
#print axioms LogicalInduction.RunAuto.guardedAutomaton
#print axioms LogicalInduction.RunAuto.BlockMachine.pass_eq
#print axioms LogicalInduction.RunAuto.BlockMachine.ifRun_mem_FP
#print axioms LogicalInduction.RunAuto.BlockAutomaton.length_pass
#print axioms LogicalInduction.RunAuto.BlockAutomaton.pass_mem_FP
#print axioms LogicalInduction.RunAuto.BlockAutomaton.ifAuto_mem_FP

end LogicalInduction.RunAuto
