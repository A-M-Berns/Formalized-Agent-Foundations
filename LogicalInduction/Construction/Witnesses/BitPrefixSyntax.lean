import LogicalInduction.Construction.Witnesses.BoundedEvaluation
import LogicalInduction.Properties.UniversalSemimeasure
import LogicalInduction.Framework.WriteOut

/-!
# Concrete Boolean-prefix syntax for `thm:dus`

Domination of the Universal Semimeasure (`thm:dus`) is stated over an abstract
`BitPrefixSentences` presentation.  This file supplies a concrete one, **fully witnessed**:
prefix sentences are literal finite conjunctions over an independent atom family, the
finite-string enumeration is the total decode-with-empty enumeration induced by the stock
`List Bool` encoding, and the presentation's efficient-naming field is discharged by an
explicit emitter (`ordinaryBitPrefixSentences`).

**Why the naming field is symbol-metered.**  The whole-value form of that field
(`PolySentenceCodes`) is *unsatisfiable* here, and that is proved rather than asserted:
`not_polySentenceCodes_bitPrefixSentence` shows a `⋏` node costs two nested `Nat.pair`s
while a `List Bool` cons costs one, so along the all-ones strings the prefix sentence's code
(`≥ 2 ^ 4 ^ m`) outruns every polynomial in its own enumeration index (`≤ 5 ^ 2 ^ m`).  The
repo's symbol-metered interface `BigSentenceCodes` (`Framework/RpnSplice.lean`) meters the
*canonical Polish run* instead, which for the length-`m` prefix conjunction is `Θ(m)` tiny
tokens — so the field becomes dischargeable without changing the sentences named.

**The emitter** (`BitChain`).  A stock `List Bool` code is a chain of `Nat.pair`s; walking it
is cheap in the `dd:fuel` model because `PolyFueled` meters fuel and output in the input
*numeric value*, and `Nat.unpair` is a primitive, so a depth-`chainLen i ≤ i` walk of code
`i` is polynomial.  Two `prec` scans over that walk give the chain's length and a global
head-validity count; a `concatVar` of two-or-four-token literal blocks, dispatched on
validity, emits the run.  `BitChain.decode_chain` proves that run really is the Polish run of
the sentence the abstract enumeration names — including the malformed case, where the stock
decoder collapses the *whole* string to `[]` (one bad head kills the applicative chain), so
the emitter must dispatch on a global scan rather than per position.
-/

namespace LogicalInduction

open LO.Propositional

/-! ### Literal conjunctions and their exact semantics -/

/-- The positive or negative literal selected by one prefix bit. -/
def bitPrefixLiteral (atom : ℕ → Sentence) (k : ℕ) (b : Bool) : Sentence :=
  if b then atom k else ∼atom k

/-- The concrete prefix sentence: one literal for every position, conjoined in index
order.  `List.conj` makes the empty prefix the true sentence `⊤`. -/
def bitPrefixSentence (atom : ℕ → Sentence) (σ : List Bool) : Sentence :=
  (List.ofFn fun k : Fin σ.length ↦ bitPrefixLiteral atom k (σ.get k)).conj

@[simp] lemma PCWorld.holds_bitPrefixLiteral
    (v : PCWorld) (atom : ℕ → Sentence) (k : ℕ) (b : Bool) :
    v.Holds (bitPrefixLiteral atom k b) ↔ (v.Holds (atom k) ↔ b = true) := by
  cases b <;>
    simp [bitPrefixLiteral, PCWorld.Holds, LO.Propositional.Formula.Boolean.val]

/-- Exact Boolean semantics of the literal conjunction, including the empty prefix. -/
@[simp] lemma PCWorld.holds_bitPrefixSentence
    (v : PCWorld) (atom : ℕ → Sentence) (σ : List Bool) :
    v.Holds (bitPrefixSentence atom σ) ↔
      ∀ k : Fin σ.length, (v.Holds (atom k) ↔ σ.get k = true) := by
  have hlist (l : List Sentence) :
      LO.Propositional.Formula.Boolean.val v l.conj ↔
        ∀ φ ∈ l, LO.Propositional.Formula.Boolean.val v φ := by
    induction l with
    | nil => simp [List.conj, LO.Propositional.Formula.Boolean.val]
    | cons φ l ih =>
        simp [List.conj, LO.Propositional.Formula.Boolean.val, ih]
  rw [bitPrefixSentence, show v.Holds
      (List.ofFn fun k : Fin σ.length ↦
        bitPrefixLiteral atom k (σ.get k)).conj =
      LO.Propositional.Formula.Boolean.val v
        (List.ofFn fun k : Fin σ.length ↦
          bitPrefixLiteral atom k (σ.get k)).conj from rfl]
  rw [hlist, List.forall_mem_ofFn_iff]
  apply forall_congr'
  intro k
  exact v.holds_bitPrefixLiteral atom k (σ.get k)

/-! ### Concrete total enumeration -/

/-- Decode a stock `List Bool` code, using the empty string for malformed codes. -/
def bitStringEnumeration (i : ℕ) : List Bool :=
  (Encodable.decode (α := List Bool) i).getD []

lemma bitStringEnumeration_covers (σ : List Bool) :
    ∃ i, bitStringEnumeration i = σ := by
  refine ⟨Encodable.encode σ, ?_⟩
  simp [bitStringEnumeration, Encodable.encodek]

/-! ### Non-vacuity of the independence premise -/

/-- The constantly empty deductive process used to witness that finite atom independence
is a genuine, inhabited premise. -/
def emptyBitDeductiveProcess : DeductiveProcess where
  D := fun _ ↦ ∅
  mono := fun _ φ hφ ↦ by simp at hφ

/-- Ordinary propositional atoms are independently realizable over the constantly empty
deductive process. -/
def ordinaryIndependentBitAtoms : IndependentBitAtoms emptyBitDeductiveProcess where
  atom := LO.Propositional.Formula.atom
  realizable := by
    intro n f
    refine ⟨fun a ↦ f a = true, ?_, ?_⟩
    · intro φ hφ
      simp [emptyBitDeductiveProcess] at hφ
    · intro k
      rfl

lemma independentBitAtoms_nonempty :
    ∃ DP : DeductiveProcess, Nonempty (IndependentBitAtoms DP) :=
  ⟨emptyBitDeductiveProcess, ⟨ordinaryIndependentBitAtoms⟩⟩

/-! ### Why the naming field is symbol-metered: the whole-value premise is unsatisfiable

The non-vacuity guard, run in the negative direction: a *whole-value* naming certificate
(`PolySentenceCodes`) for the prefix conjunctions has **no inhabitant**, for any atom family.
`PolyFueled` bundles `IsPolyBounded` of the computed function itself, so it suffices to
refute the output bound.  This is what forces `BitPrefixSentences.prefix_codes` to meter
symbols; the emitter discharging the symbol-metered form is built below.

`Nat.pair x y ≥ y * y` makes the conjunction code grow with exponent `4 ^ m` in the prefix
length `m`, whereas the stock `List Bool` code — the enumeration index the bound is measured
against — grows only with exponent `2 ^ m`.  The gap doubles the exponent per bit, so no
polynomial covers it.  This is exactly the whole-value/symbol-metered mismatch documented at
`BigSentenceCodes` (`Framework/RpnSplice.lean`), which meters symbols instead of the pair-code
value and is the interface a repair should use. -/

private lemma sq_le_pair (x y : ℕ) : y * y ≤ Nat.pair x y := by
  rw [Nat.pair]
  split
  · exact Nat.le_add_right _ _
  · next h =>
      have hxy : y ≤ x := Nat.le_of_not_lt h
      calc y * y ≤ x * x := Nat.mul_le_mul hxy hxy
        _ ≤ x * x + x + y := by omega

/-- A right-nested conjunction of `m` sentences has Gödel code at least `2 ^ 4 ^ m`, whatever
its conjuncts are: every `⋏` node is two nested pairings, and each pairing squares. -/
lemma two_pow_le_encode_conj (l : List Sentence) :
    2 ^ (4 ^ l.length) ≤ Encodable.encode l.conj := by
  induction l with
  | nil => decide
  | cons a l ih =>
      have hrw : Encodable.encode (a :: l).conj
          = Nat.pair 3 (Nat.pair (Encodable.encode a) (Encodable.encode l.conj)) + 1 := rfl
      set S := Encodable.encode l.conj with hS
      have h1 : S * S ≤ Nat.pair (Encodable.encode a) S := sq_le_pair _ _
      have h2 : (S * S) * (S * S) ≤ Nat.pair 3 (Nat.pair (Encodable.encode a) S) :=
        le_trans (Nat.mul_le_mul h1 h1) (sq_le_pair 3 _)
      have hexp : 4 ^ (l.length + 1)
          = 4 ^ l.length + 4 ^ l.length + (4 ^ l.length + 4 ^ l.length) := by
        rw [pow_succ]; ring
      have h4 : 2 ^ (4 ^ (l.length + 1)) ≤ (S * S) * (S * S) := by
        simp only [hexp, pow_add]
        exact Nat.mul_le_mul (Nat.mul_le_mul ih ih) (Nat.mul_le_mul ih ih)
      rw [hrw, List.length_cons]
      omega

/-- The stock `List Bool` code of the all-ones string of length `m` is below `5 ^ 2 ^ m`:
one pairing, hence one squaring, per bit. -/
lemma encode_replicate_true_le (m : ℕ) :
    Encodable.encode (List.replicate m true) + 3 ≤ 5 ^ 2 ^ m := by
  induction m with
  | zero => decide
  | succ m ih =>
      have hcons : Encodable.encode (List.replicate (m + 1) true)
          = Nat.pair 1 (Encodable.encode (List.replicate m true)) + 1 := rfl
      set E := Encodable.encode (List.replicate m true) with hE
      have hstep : Nat.pair 1 E + 1 + 3 ≤ (E + 3) * (E + 3) := by
        rw [Nat.pair]
        split
        · next h => nlinarith
        · next h => nlinarith
      calc Encodable.encode (List.replicate (m + 1) true) + 3
          ≤ (E + 3) * (E + 3) := by rw [hcons]; exact hstep
        _ ≤ (5 ^ 2 ^ m) * (5 ^ 2 ^ m) := Nat.mul_le_mul ih ih
        _ = 5 ^ 2 ^ (m + 1) := by rw [← pow_add, pow_succ]; ring_nf

/-- **The whole-value prefix-code bound fails.**  Reading the all-ones string of length `m`
off its own stock code puts a sentence of code `≥ 2 ^ 4 ^ m` at an index `≤ 5 ^ 2 ^ m`, and
`4 ^ m` outruns every `a * (n + 1) ^ k + a`. -/
lemma not_isPolyBounded_bitPrefixSentence_codes (atom : ℕ → Sentence) :
    ¬ IsPolyBounded
      (fun i ↦ Encodable.encode (bitPrefixSentence atom (bitStringEnumeration i))) := by
  rintro ⟨a, k, hk⟩
  obtain ⟨m, hm⟩ : ∃ m, m = a + 3 * k + 4 := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E, E = Encodable.encode (List.replicate m true) := ⟨_, rfl⟩
  have hdec : bitStringEnumeration E = List.replicate m true := by
    rw [hE]
    simp [bitStringEnumeration, Encodable.encodek]
  have hlen : (List.ofFn fun j : Fin (List.replicate m true).length ↦
      bitPrefixLiteral atom j ((List.replicate m true).get j)).length = m := by
    simp
  have hlow : 2 ^ 4 ^ m ≤
      Encodable.encode (bitPrefixSentence atom (List.replicate m true)) := by
    have h := two_pow_le_encode_conj (List.ofFn fun j : Fin (List.replicate m true).length ↦
      bitPrefixLiteral atom j ((List.replicate m true).get j))
    rw [hlen] at h
    exact h
  have hup := hk E
  simp only [hdec] at hup
  have hE1 : E + 1 ≤ 5 ^ 2 ^ m := by
    have h := encode_replicate_true_le m
    omega
  have hchain : 2 ^ 4 ^ m ≤ a * (5 ^ 2 ^ m) ^ k + a := by
    refine le_trans hlow (le_trans hup ?_)
    have hp : (E + 1) ^ k ≤ (5 ^ 2 ^ m) ^ k := Nat.pow_le_pow_left hE1 k
    exact Nat.add_le_add_right (Nat.mul_le_mul_left a hp) a
  have hpow5 : (5 ^ 2 ^ m) ^ k ≤ 2 ^ (3 * (k * 2 ^ m)) := by
    calc (5 ^ 2 ^ m) ^ k = 5 ^ (2 ^ m * k) := by rw [← pow_mul]
      _ ≤ 8 ^ (2 ^ m * k) := Nat.pow_le_pow_left (by norm_num) _
      _ = 2 ^ (3 * (k * 2 ^ m)) := by
          rw [show (8:ℕ) = 2 ^ 3 by norm_num, ← pow_mul]
          ring_nf
  have hfin : 2 ^ 4 ^ m ≤ 2 ^ (a + 2 + 3 * (k * 2 ^ m)) := by
    have hone : 1 ≤ (5 ^ 2 ^ m) ^ k := Nat.one_le_pow _ _ (by positivity)
    have h1 : a * (5 ^ 2 ^ m) ^ k + a ≤ (2 * (a + 1)) * (5 ^ 2 ^ m) ^ k := by nlinarith
    have h2 : 2 * (a + 1) ≤ 2 ^ (a + 2) := by
      have hlt := Nat.lt_two_pow_self (n := a + 1)
      calc 2 * (a + 1) ≤ 2 * 2 ^ (a + 1) := by omega
        _ = 2 ^ (a + 2) := by ring
    calc 2 ^ 4 ^ m ≤ (2 * (a + 1)) * (5 ^ 2 ^ m) ^ k := le_trans hchain h1
      _ ≤ 2 ^ (a + 2) * 2 ^ (3 * (k * 2 ^ m)) := Nat.mul_le_mul h2 hpow5
      _ = 2 ^ (a + 2 + 3 * (k * 2 ^ m)) := by rw [← pow_add]
  have hexp : 4 ^ m ≤ a + 2 + 3 * (k * 2 ^ m) :=
    (Nat.pow_le_pow_iff_right (by norm_num)).mp hfin
  have h2m : m + 1 ≤ 2 ^ m := Nat.lt_two_pow_self
  have h4m : 4 ^ m = 2 ^ m * 2 ^ m := by
    rw [show (4:ℕ) = 2 * 2 by norm_num, mul_pow]
  have hbig : (a + 3 * k + 4) * 2 ^ m ≤ 2 ^ m * 2 ^ m :=
    Nat.mul_le_mul_right _ (by omega)
  have hone : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  nlinarith [hexp, h4m, hbig, hone]

/-- **The whole-value naming certificate has no inhabitant.**  Consequently
`BitPrefixSentences.prefix_codes` cannot be metered in the pair-code value, which is why it
is stated with the symbol-metered `BigSentenceCodes`; `ordinaryBitPrefixCodes` below
discharges that form for exactly the same sentences.
Paper node: `thm:dus` -/
lemma not_polySentenceCodes_bitPrefixSentence (atom : ℕ → Sentence) :
    ¬ PolySentenceCodes (fun i ↦ bitPrefixSentence atom (bitStringEnumeration i)) := by
  rintro ⟨c, hc⟩
  obtain ⟨b, -, hpoly, -⟩ := hc
  exact not_isPolyBounded_bitPrefixSentence_codes atom hpoly

/-! ### The symbol-metered emitter

A stock `List Bool` code is a chain of `Nat.pair`s: `encode (b :: l) = pair ⌜b⌝ ⌜l⌝ + 1`.
`BitChain` walks that chain with two `prec` scans — one for its length, one for a *global*
head-validity count — and emits the canonical Polish run of the corresponding prefix
conjunction.  The validity scan is a correctness obligation, not a cost one: `Encodable Bool`
sends every code `≥ 2` to `none`, and `decode_list_succ` is applicative, so a single bad head
collapses the whole string to `[]` (the sentence becomes `⊤`) rather than truncating it. -/

namespace BitChain

/-- One step down a stock `List Bool` code chain. -/
def tailC (c : ℕ) : ℕ := (c - 1).unpair.2

/-- The head bit-code of a stock `List Bool` code chain. -/
def headC (c : ℕ) : ℕ := (c - 1).unpair.1

@[simp] lemma tailC_zero : tailC 0 = 0 := by simp [tailC]
@[simp] lemma headC_zero : headC 0 = 0 := by simp [headC]

lemma tailC_lt {c : ℕ} (h : c ≠ 0) : tailC c < c := by
  have h1 : (c - 1).unpair.2 ≤ c - 1 := Nat.unpair_right_le _
  unfold tailC; omega

lemma tailC_polyFueled : ∃ cc, PolyFueled cc tailC := by
  refine ⟨_, (PolyFueled.right.comp predc_polyFueled).of_eq (fun n => rfl)⟩

lemma headC_polyFueled : ∃ cc, PolyFueled cc headC := by
  refine ⟨_, (PolyFueled.left.comp predc_polyFueled).of_eq (fun n => rfl)⟩

lemma tailC_iterate_le (a : ℕ) : ∀ j, tailC^[j] a ≤ a := by
  intro j
  induction j generalizing a with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply]
      refine le_trans (ih _) ?_
      rcases Nat.eq_zero_or_pos a with rfl | h
      · simp
      · exact le_of_lt (tailC_lt (by omega))

/-- **The chain iterate is poly-fueled.** -/
lemma tailC_iterate_polyFueled :
    ∃ cc, PolyFueled cc (fun m => tailC^[m.unpair.2] m.unpair.1) := by
  obtain ⟨ct, ht⟩ := tailC_polyFueled
  have hst : IsPolyBounded (fun m => tailC^[m.unpair.2] m.unpair.1) :=
    isPolyBounded_fst.of_le (fun m => tailC_iterate_le _ _)
  refine ⟨_, PolyFueled.prec PolyFueled.id (ht.comp (PolyFueled.right.comp PolyFueled.right))
    (st := fun a j => tailC^[j] a) (fun a => by simp) (fun a j => ?_) hst⟩
  simp only [Nat.unpair_pair]
  rw [Function.iterate_succ_apply']

/-! ### Chain length -/

/-- Number of chain steps before the code reaches `0`. -/
def chainLen : ℕ → ℕ
  | 0 => 0
  | (c + 1) => chainLen (tailC (c + 1)) + 1
decreasing_by exact tailC_lt (Nat.succ_ne_zero c)

@[simp] lemma chainLen_zero : chainLen 0 = 0 := by simp [chainLen]

lemma chainLen_succ (c : ℕ) : chainLen (c + 1) = chainLen (tailC (c + 1)) + 1 := by
  rw [chainLen]

lemma chainLen_le : ∀ i, chainLen i ≤ i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    match i with
    | 0 => simp
    | (c + 1) =>
      rw [chainLen_succ]
      have hlt : tailC (c + 1) < c + 1 := tailC_lt (Nat.succ_ne_zero c)
      have := ih _ hlt
      omega

lemma iterate_eq_zero_iff : ∀ i j, tailC^[j] i = 0 ↔ chainLen i ≤ j := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    match i with
    | 0 => intro j; simp [Function.iterate_fixed]
    | (c + 1) =>
      intro j
      have hlt : tailC (c + 1) < c + 1 := tailC_lt (Nat.succ_ne_zero c)
      cases j with
      | zero => simp [chainLen_succ]
      | succ j =>
          rw [Function.iterate_succ_apply, ih _ hlt j, chainLen_succ]
          omega

/-! ### Chain validity -/

/-- Number of malformed heads seen in the first `j` chain positions. -/
def badCount (a : ℕ) : ℕ → ℕ
  | 0 => 0
  | (j + 1) => badCount a j + (if headC (tailC^[j] a) ≤ 1 then 0 else 1)

@[simp] lemma badCount_zero (a : ℕ) : badCount a 0 = 0 := rfl

lemma badCount_succ (a j : ℕ) :
    badCount a (j + 1) = badCount a j + (if headC (tailC^[j] a) ≤ 1 then 0 else 1) := rfl

lemma badCount_eq_zero_iff (a j : ℕ) :
    badCount a j = 0 ↔ ∀ i < j, headC (tailC^[i] a) ≤ 1 := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [badCount_succ]
      constructor
      · intro h i hi
        have h1 : badCount a j = 0 := by omega
        have h2 : headC (tailC^[j] a) ≤ 1 := by
          by_contra hc
          rw [if_neg hc] at h
          omega
        rcases Nat.lt_or_ge i j with hij | hij
        · exact (ih.mp h1) i hij
        · have : i = j := by omega
          subst this; exact h2
      · intro h
        rw [ih.mpr (fun i hi => h i (by omega)), if_pos (h j (by omega))]

/-- Every head along the whole chain is a legal `Bool` code. -/
def ChainOK (i : ℕ) : Prop := ∀ j, headC (tailC^[j] i) ≤ 1

lemma chainOK_iff_badCount (i : ℕ) : ChainOK i ↔ badCount i i = 0 := by
  rw [badCount_eq_zero_iff]
  constructor
  · intro h j _; exact h j
  · intro h j
    rcases Nat.lt_or_ge j i with hj | hj
    · exact h j hj
    · have : tailC^[j] i = 0 :=
        (iterate_eq_zero_iff i j).mpr (le_trans (chainLen_le i) hj)
      rw [this, headC_zero]; omega

instance : DecidablePred ChainOK :=
  fun i => decidable_of_iff _ (chainOK_iff_badCount i).symm

/-- The bits read off a chain code. -/
def chainBits (i : ℕ) : List Bool :=
  (List.range (chainLen i)).map (fun j => decide (headC (tailC^[j] i) = 1))

lemma decode_succ_headC (c : ℕ) :
    Encodable.decode (α := List Bool) (c + 1) =
      (fun (b : Bool) (l : List Bool) => b :: l) <$>
        Encodable.decode (α := Bool) (headC (c + 1)) <*>
        Encodable.decode (α := List Bool) (tailC (c + 1)) := by
  have h := Encodable.decode_list_succ (α := Bool) c
  simp [headC, tailC] at h ⊢

lemma decode_bool_of_le_one {h : ℕ} (hh : h ≤ 1) :
    Encodable.decode (α := Bool) h = some (decide (h = 1)) := by
  interval_cases h <;> simp

lemma decode_chain : ∀ i, Encodable.decode (α := List Bool) i =
    if ChainOK i then some (chainBits i) else none := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    match i with
    | 0 =>
        rw [if_pos]
        · simp [chainBits]
        · intro j; simp [Function.iterate_fixed]
    | (c + 1) =>
      have hlt : tailC (c + 1) < c + 1 := tailC_lt (Nat.succ_ne_zero c)
      rw [decode_succ_headC]
      by_cases hh : headC (c + 1) ≤ 1
      · rw [decode_bool_of_le_one hh, ih _ hlt]
        by_cases htail : ChainOK (tailC (c + 1))
        · rw [if_pos htail, if_pos]
          · rw [chainBits, chainBits, chainLen_succ, List.range_succ_eq_map,
              List.map_cons, List.map_map]
            simp only [Function.comp_def, Function.iterate_zero_apply,
              Function.iterate_succ_apply]
            rfl
          · intro j
            cases j with
            | zero => simpa using hh
            | succ j => simpa [Function.iterate_succ_apply] using htail j
        · rw [if_neg htail, if_neg]
          · rfl
          · intro hOK
            exact htail (fun j => by
              simpa [Function.iterate_succ_apply] using hOK (j + 1))
      · rw [Encodable.decode_ge_two _ (by omega), if_neg]
        · rfl
        · intro hOK
          exact hh (by simpa using hOK 0)

lemma bitStringEnumeration_eq (i : ℕ) :
    bitStringEnumeration i = if badCount i i = 0 then chainBits i else [] := by
  rw [bitStringEnumeration, decode_chain]
  by_cases h : ChainOK i
  · rw [if_pos h, if_pos ((chainOK_iff_badCount i).mp h)]; rfl
  · rw [if_neg h, if_neg (fun hb => h ((chainOK_iff_badCount i).mpr hb))]; rfl

/-! ### The two scans are poly-fueled -/

lemma chainLen_polyFueled : ∃ c, PolyFueled c chainLen := by
  obtain ⟨citer, hiter⟩ := tailC_iterate_polyFueled
  obtain ⟨cad, had⟩ := addc_polyFueled
  have aPF := PolyFueled.left
  have jPF := PolyFueled.left.comp PolyFueled.right
  have prevPF := PolyFueled.right.comp PolyFueled.right
  have xPF := hiter.comp (aPF.pair jPF)
  have indPF := ifzSel_polyFueled.comp ((PolyFueled.const (Nat.pair 0 1)).pair xPF)
  have stepPF := had.comp (prevPF.pair indPF)
  have hst : IsPolyBounded (fun m => min (chainLen m.unpair.1) m.unpair.2) :=
    isPolyBounded_snd.of_le (fun m => Nat.min_le_right _ _)
  have hscan := PolyFueled.prec (PolyFueled.const 0) stepPF
    (st := fun a j => min (chainLen a) j) (fun a => by simp)
    (fun a j => by
      simp only [Nat.unpair_pair, ifzSelFn]
      have hiff := iterate_eq_zero_iff a j
      by_cases h : tailC^[j] a = 0
      · rw [if_pos h]
        have : chainLen a ≤ j := hiff.mp h
        omega
      · rw [if_neg h]
        have : ¬ chainLen a ≤ j := fun hc => h (hiff.mpr hc)
        omega) hst
  refine ⟨_, (hscan.comp (PolyFueled.id.pair PolyFueled.id)).of_eq (fun t => ?_)⟩
  simp only [Nat.unpair_pair]
  exact min_eq_left (chainLen_le t)

lemma badCount_le (a : ℕ) : ∀ j, badCount a j ≤ j := by
  intro j
  induction j with
  | zero => simp
  | succ j ih => rw [badCount_succ]; split <;> omega

lemma badCount_diag_polyFueled : ∃ c, PolyFueled c (fun i => badCount i i) := by
  obtain ⟨citer, hiter⟩ := tailC_iterate_polyFueled
  obtain ⟨chead, hhead⟩ := headC_polyFueled
  obtain ⟨cad, had⟩ := addc_polyFueled
  have aPF := PolyFueled.left
  have jPF := PolyFueled.left.comp PolyFueled.right
  have prevPF := PolyFueled.right.comp PolyFueled.right
  have xPF := hiter.comp (aPF.pair jPF)
  have yPF := hhead.comp xPF
  have zPF := subc_polyFueled.comp (yPF.pair (PolyFueled.const 1))
  have indPF := ifzSel_polyFueled.comp ((PolyFueled.const (Nat.pair 0 1)).pair zPF)
  have stepPF := had.comp (prevPF.pair indPF)
  have hst : IsPolyBounded (fun m => badCount m.unpair.1 m.unpair.2) :=
    isPolyBounded_snd.of_le (fun m => badCount_le _ _)
  have hscan := PolyFueled.prec (PolyFueled.const 0) stepPF
    (st := fun a j => badCount a j) (fun a => by simp)
    (fun a j => by
      simp only [Nat.unpair_pair, ifzSelFn]
      rw [badCount_succ]
      by_cases h : headC (tailC^[j] a) - 1 = 0
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]) hst
  exact ⟨_, (hscan.comp (PolyFueled.id.pair PolyFueled.id)).of_eq (fun t => by
    simp only [Nat.unpair_pair])⟩

/-! ### The canonical Polish run of a prefix conjunction -/

/-- The Polish run of one prefix literal, with its enclosing `⋏` tag. -/
def bitBlock (j : ℕ) (b : Bool) : List ℕ :=
  if b then [3, j + 5] else [3, 2, j + 5, 0]

lemma rpn_bitPrefixLiteral (j : ℕ) (b : Bool) :
    3 :: rpn (bitPrefixLiteral Formula.atom j b) = bitBlock j b := by
  cases b <;> simp [bitPrefixLiteral, bitBlock, rpn]

lemma rpn_top : rpn (⊤ : Sentence) = [2, 0, 0] := by
  simp [rpn]

lemma rpn_and (φ ψ : Sentence) : rpn (φ ⋏ ψ) = 3 :: (rpn φ ++ rpn ψ) := rfl

lemma rpn_conj_ofFn : ∀ (σ : List Bool) (off : ℕ),
    rpn ((List.ofFn fun k : Fin σ.length =>
        bitPrefixLiteral Formula.atom (off + k) (σ.get k)).conj) =
      (List.range σ.length).flatMap (fun j => bitBlock (off + j) (σ.getD j false)) ++
        [2, 0, 0] := by
  intro σ
  induction σ with
  | nil => intro off; simpa using rpn_top
  | cons b τ ih =>
      intro off
      have key : (List.ofFn fun k : Fin (b :: τ).length =>
          bitPrefixLiteral Formula.atom (off + k) ((b :: τ).get k)) =
          bitPrefixLiteral Formula.atom off b ::
            (List.ofFn fun k : Fin τ.length =>
              bitPrefixLiteral Formula.atom (off + 1 + k) (τ.get k)) := by
        apply List.ext_getElem
        · simp
        · intro n h1 h2
          cases n with
          | zero => simp
          | succ n =>
              simp only [List.getElem_ofFn, List.get_eq_getElem, List.getElem_cons_succ]
              rw [show off + ((⟨n + 1, by simpa using h1⟩ : Fin (b :: τ).length) : ℕ) =
                off + 1 + ((⟨n, by simpa using h2⟩ : Fin τ.length) : ℕ) from by simp; omega]
      rw [key, List.conj_cons, rpn_and, ih (off + 1),
        show List.range (b :: τ).length = List.range (τ.length + 1) from rfl,
        List.range_succ_eq_map, List.flatMap_cons]
      simp only [List.flatMap_map, List.getD_cons_zero,
        List.getD_cons_succ, Nat.add_zero]
      rw [← rpn_bitPrefixLiteral off b]
      simp only [List.cons_append, List.append_assoc]
      congr 2
      congr 1
      apply List.flatMap_congr
      intro j _
      rw [show off + 1 + j = off + Nat.succ j from by omega]

lemma rpn_bitPrefixSentence (σ : List Bool) :
    rpn (bitPrefixSentence Formula.atom σ) =
      (List.range σ.length).flatMap (fun j => bitBlock j (σ.getD j false)) ++ [2, 0, 0] := by
  have h := rpn_conj_ofFn σ 0
  simp only [Nat.zero_add] at h
  rw [bitPrefixSentence]
  exact h

/-! ### The emitted canonical run -/

/-- The canonical Polish run of the prefix conjunction named by chain code `i`. -/
def prefixRun (i : ℕ) : List ℕ :=
  if badCount i i = 0 then
    (List.range (chainLen i)).flatMap
      (fun j => bitBlock j (decide (headC (tailC^[j] i) = 1))) ++ [2, 0, 0]
  else [2, 0, 0]

lemma prefixRun_eq (i : ℕ) :
    prefixRun i = rpn (bitPrefixSentence Formula.atom (bitStringEnumeration i)) := by
  rw [rpn_bitPrefixSentence, bitStringEnumeration_eq, prefixRun]
  by_cases h : badCount i i = 0
  · rw [if_pos h, if_pos h, chainBits, List.length_map, List.length_range]
    congr 1
    apply List.flatMap_congr
    intro j hj
    rw [List.mem_range] at hj
    congr 1
    rw [List.getD_eq_getElem _ _ (by simpa using hj)]
    simp
  · rw [if_neg h, if_neg h]
    simp

lemma prefixRun_polySegStream : PolySegStream prefixRun := by
  obtain ⟨citer, hiter⟩ := tailC_iterate_polyFueled
  obtain ⟨chead, hhead⟩ := headC_polyFueled
  obtain ⟨clen, hlen⟩ := chainLen_polyFueled
  obtain ⟨cbad, hbad⟩ := badCount_diag_polyFueled
  obtain ⟨cad, had⟩ := addc_polyFueled
  have hj5 : PolyFueled _ (fun z : ℕ => z.unpair.2 + 5) :=
    (had.comp (PolyFueled.right.pair (PolyFueled.const 5))).of_eq
      (fun z => by simp only [Nat.unpair_pair])
  have hh : PolyFueled _ (fun z : ℕ => headC (tailC^[z.unpair.2] z.unpair.1)) :=
    hhead.comp hiter
  have htest : PolyFueled _ (fun z : ℕ =>
      (headC (tailC^[z.unpair.2] z.unpair.1) - 1) +
        (1 - headC (tailC^[z.unpair.2] z.unpair.1))) :=
    (had.comp ((subc_polyFueled.comp (hh.pair (PolyFueled.const 1))).pair
      (subc_polyFueled.comp ((PolyFueled.const 1).pair hh)))).of_eq
      (fun z => by simp only [Nat.unpair_pair])
  have hpos : PolySegStream (fun z : ℕ => [3, z.unpair.2 + 5]) :=
    (PolySegStream.ofTokenStream
      ((PolyTokenStream.const 3).append (PolyTokenStream.polyTok hj5))).of_eq
      (fun z => by simp)
  have hneg : PolySegStream (fun z : ℕ => [3, 2, z.unpair.2 + 5, 0]) :=
    (PolySegStream.ofTokenStream
      (((PolyTokenStream.const 3).append (PolyTokenStream.const 2)).append
        ((PolyTokenStream.polyTok hj5).append (PolyTokenStream.const 0)))).of_eq
      (fun z => by simp)
  have hseg : PolySegStream (fun z : ℕ =>
      bitBlock z.unpair.2 (decide (headC (tailC^[z.unpair.2] z.unpair.1) = 1))) := by
    refine (PolySegStream.ifZero hpos hneg htest).of_eq (fun z => ?_)
    by_cases hb : headC (tailC^[z.unpair.2] z.unpair.1) = 1
    · rw [if_pos (by omega), hb]
      simp [bitBlock]
    · rw [if_neg (by omega)]
      simp [bitBlock, hb]
  have htail : PolySegStream (fun _ : ℕ => [2, 0, 0]) :=
    (PolySegStream.ofTokenStream
      (((PolyTokenStream.const 2).append (PolyTokenStream.const 0)).append
        (PolyTokenStream.const 0))).of_eq (fun _ => by simp)
  have hbody := (PolySegStream.concatVar hseg hlen).append htail
  refine (PolySegStream.ifZero hbody htail hbad).of_eq (fun i => ?_)
  rw [prefixRun]
  by_cases h : badCount i i = 0
  · rw [if_pos h, if_pos h]
    congr 1
    apply List.flatMap_congr
    intro j _
    simp only [Nat.unpair_pair]
  · rw [if_neg h, if_neg h]

/-- **The prefix-conjunction sequence is write-out metered efficiently computable.** -/
lemma bigSentenceCodes_bitPrefixSentence :
    BigSentenceCodes (fun i => bitPrefixSentence Formula.atom (bitStringEnumeration i)) :=
  BigSentenceCodes.ofCanonical
    (BigTokenStream.ofPolySegStream
      (prefixRun_polySegStream.of_eq (fun i => prefixRun_eq i)))

end BitChain

/-- **The concrete prefix conjunctions are efficiently nameable** (`dd:ec`, write-out metered):
the canonical Polish run of the length-`m` prefix conjunction is `3m + 3` tokens at worst,
emitted by walking the enumeration index's own `Nat.pair` chain.
Paper node: `thm:dus` -/
lemma ordinaryBitPrefixCodes :
    BigSentenceCodes (fun i ↦
      bitPrefixSentence ordinaryIndependentBitAtoms.atom (bitStringEnumeration i)) :=
  BitChain.bigSentenceCodes_bitPrefixSentence

/-- Construct the complete prefix presentation from independent atoms and a symbol-metered
naming certificate for the actual literal conjunctions.
Paper node: `thm:dus` -/
def bitPrefixSentencesOfIndependentAtoms
    {DP : DeductiveProcess} (I : IndependentBitAtoms DP)
    (C : BigSentenceCodes (fun i ↦ bitPrefixSentence I.atom (bitStringEnumeration i))) :
    BitPrefixSentences DP where
  atom := I.atom
  prefixSentence := bitPrefixSentence I.atom
  enumeration := bitStringEnumeration
  enumeration_covers := bitStringEnumeration_covers
  prefix_codes := C
  holds_prefix := fun v σ ↦ PCWorld.holds_bitPrefixSentence v I.atom σ
  realizable := I.realizable

/-- **The `thm:dus` / `thm:strict` presentation, inhabited.**  Ordinary propositional atoms
over the constantly-empty deductive process, with the naming certificate discharged by
`ordinaryBitPrefixCodes`.  This is the non-vacuity witness for `BitPrefixSentences`.
Paper node: `thm:dus` -/
def ordinaryBitPrefixSentences : BitPrefixSentences emptyBitDeductiveProcess :=
  bitPrefixSentencesOfIndependentAtoms ordinaryIndependentBitAtoms ordinaryBitPrefixCodes

/-- Domination of the universal semimeasure with the opaque `BitPrefixSentences` argument
discharged by the concrete Boolean-prefix constructor.  The semimeasure's from-below
approximation and its threshold emission remain caller inputs.

Inhabited: `ordinaryBitPrefixSentences` supplies `I` and `C` over the repo's own atoms.
Paper node: `thm:dus` -/
theorem lic_domination_universalSemimeasure_ofIndependentAtoms
    {DP : DeductiveProcess}
    (I : IndependentBitAtoms DP)
    (C : BigSentenceCodes (fun i ↦ bitPrefixSentence I.atom (bitStringEnumeration i)))
    {M : LowerSemicomputableContinuousSemimeasure}
    (A : DUSApproximationPresentation M
      (bitPrefixSentencesOfIndependentAtoms I C))
    (emit : DUSThresholdEmission A)
    (P : History) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ∃ K : ℝ, 0 < K ∧ ∀ σ,
      K * M.mass σ ≤ limitingBelief P
        (bitPrefixSentence I.atom σ) :=
  lic_domination_universalSemimeasure A emit P hworld

#print axioms PCWorld.holds_bitPrefixSentence
#print axioms bitStringEnumeration_covers
#print axioms two_pow_le_encode_conj
#print axioms encode_replicate_true_le
#print axioms not_isPolyBounded_bitPrefixSentence_codes
#print axioms not_polySentenceCodes_bitPrefixSentence
#print axioms ordinaryIndependentBitAtoms
#print axioms independentBitAtoms_nonempty
#print axioms BitChain.decode_chain
#print axioms ordinaryBitPrefixCodes
#print axioms bitPrefixSentencesOfIndependentAtoms
#print axioms ordinaryBitPrefixSentences
#print axioms lic_domination_universalSemimeasure_ofIndependentAtoms

end LogicalInduction
