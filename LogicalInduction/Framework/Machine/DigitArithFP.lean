import LogicalInduction.Framework.Machine.TokenFold
import Complexitylib.Classes.P

/-!
# Base-four arithmetic on digit words, in `Complexity.FP`

`Framework/Machine/DigitBits.lean` fixes the bit rendering of a base-four digit run
(`digitsToBits`, three bits per digit, most significant bit of the digit first) and
`Framework/DigitArith.lean` fixes the value it denotes (`digitVal`, little-endian).
`IsDigitWord` and `wordVal` are this file's two predicates over that representation, and the
file is the arithmetic on it: addition, truncated subtraction, predecessor, comparison,
integer square root with remainder, and `Nat.unpair` — each as a member of `Complexity.FP`
with a value specification.

Naming: a `…W` suffix marks a word-level function on digit words (`addW`, `subW`, `leW`,
`predW`, `sqrtRemW`, `unpairFstW`, `unpairSndW`), and `…W_spec` is its value specification.

## The one vehicle

Everything is built from `Complexity.Cobham.iterate_mem_FP`: an `FP` step applied
`(ruler z).length` times from an `FP` initial state, subject to a uniform width bound.
`TokenFold.dgFold_mem_FP` cannot serve here, because it gives the client no random access
into a *second* operand, and every operation below is binary.

Digits are consumed three bits at a time and reduced to *unary* immediately (`digU`), so all
in-step arithmetic is length arithmetic — append for addition, `drop` for truncated
subtraction, `TokenFold.leFlag` for comparison — and is written back as three bits by
`unDig`. A digit sum is at most `7`, so both conversions are constant-depth dispatches.

Trailing zero digits do not change `digitVal`, which is what makes the loops uniform: a loop
runs a fixed, generously over-estimated number of steps and the surplus steps append zero
digits. The width invariants (`AddBnd`, `SqBnd`) must therefore hold on *every* input, not
only on well-formed configurations, since `iterate_mem_FP`'s clamp has to be discharged on
malformed words too.

## Where it is used

`sqrtRemW_mem_FP` and `unpairW_spec` are the file's two paper-facing results
(`app:ifp`); their sole consumer is `Construction/Witnesses/FiberTestFP.lean`. Everything
else is infrastructure reached through them. Nothing else here is a paper claim, so the
remaining declarations are `lemma`s and `def`s carrying no `Paper node` line.
-/

namespace LogicalInduction.DigitFP

-- `Nat.sqrt` is opaque here so the square-root recurrence is driven by `sqrt_rec`'s four
-- Mathlib characterizations rather than unfolded by the `simp`/`omega` calls in the loop
-- proofs.
attribute [local irreducible] Nat.sqrt

open Complexity Complexity.Cobham LogicalInduction.TokenFold LogicalInduction.FPFold

/-! ## Digit words -/

/-- A word is a digit word when it is the bit encoding of a base-four digit run. -/
def IsDigitWord (w : List Bool) : Prop :=
  ∃ cur : List ℕ, (∀ d ∈ cur, d < 4) ∧ w = digitsToBits cur

/-- The little-endian base-four value a word denotes. -/
def wordVal (w : List Bool) : ℕ := digitVal (bitsToDigits w)

lemma isDigitWord_digitsToBits {cur : List ℕ} (h : ∀ d ∈ cur, d < 4) :
    IsDigitWord (digitsToBits cur) := ⟨cur, h, rfl⟩

/-- Reading back the bits of a digit run recovers its value.

Proof kind: `C` composition.  Provenance: (b) `bitsToDigits_digitsToBits`. -/
lemma wordVal_digitsToBits {cur : List ℕ} (hcur : ∀ d ∈ cur, d < 4) :
    wordVal (digitsToBits cur) = digitVal cur := by
  rw [wordVal, bitsToDigits_digitsToBits _ (fun d hd => lt_trans (hcur d hd) (by norm_num))]

/-! ## The two digit conversions

`digU` reads the leading three bits of a word as a unary count; `unDig` writes a unary
count below eight back as three bits.  Between them every in-step computation is length
arithmetic. -/

/-- Branch on the leading three bits of a word, delivering one of eight constants.
`Complexity.FP` has `selectHead` but no `tail`; `TokenFold.tail_mem_FP` supplies the
missing peel, so the three-deep nest is a constant-depth composition. -/
def dig3 (f : ℕ → List Bool) (u : List Bool) : List Bool :=
  selectHead u
    (selectHead u.tail
      (selectHead u.tail.tail (f 7) (f 6))
      (selectHead u.tail.tail (f 5) (f 4)))
    (selectHead u.tail
      (selectHead u.tail.tail (f 3) (f 2))
      (selectHead u.tail.tail (f 1) (f 0)))

@[simp] lemma dig3_nil (f : ℕ → List Bool) : dig3 f [] = [] := by
  simp [dig3, selectHead]

lemma dig3_digitBits (f : ℕ → List Bool) (d : ℕ) (hd : d < 8) (rest : List Bool) :
    dig3 f (digitBits d ++ rest) = f d := by
  interval_cases d <;> simp [dig3, digitBits, selectHead]

lemma dig3_mem_FP {A : List Bool → List Bool} (hA : A ∈ FP) (f : ℕ → List Bool) :
    (fun z => dig3 f (A z)) ∈ FP := by
  have h1 := tail_mem_FP hA
  have h2 := tail_mem_FP h1
  exact selectHeadFn_mem_FP hA
    (selectHeadFn_mem_FP h1
      (selectHeadFn_mem_FP h2 (constFn_mem_FP (f 7)) (constFn_mem_FP (f 6)))
      (selectHeadFn_mem_FP h2 (constFn_mem_FP (f 5)) (constFn_mem_FP (f 4))))
    (selectHeadFn_mem_FP h1
      (selectHeadFn_mem_FP h2 (constFn_mem_FP (f 3)) (constFn_mem_FP (f 2)))
      (selectHeadFn_mem_FP h2 (constFn_mem_FP (f 1)) (constFn_mem_FP (f 0))))

/-- The leading digit of a word, in unary. -/
def digU (u : List Bool) : List Bool := dig3 (fun d => List.replicate d true) u

@[simp] lemma digU_nil : digU [] = [] := by simp [digU]

lemma digU_digitBits (d : ℕ) (hd : d < 8) (rest : List Bool) :
    digU (digitBits d ++ rest) = List.replicate d true := by
  rw [digU, dig3_digitBits _ d hd]

lemma digU_mem_FP {A : List Bool → List Bool} (hA : A ∈ FP) :
    (fun z => digU (A z)) ∈ FP := dig3_mem_FP hA _

/-- Write a unary count below eight back as three bits.  The recursion is on the *literal*
bound, so the dispatch has constant depth. -/
def unDigAux : ℕ → List Bool → List Bool
  | 0, _ => digitBits 0
  | (k + 1), u => if u.length = k + 1 then digitBits (k + 1) else unDigAux k u

lemma unDigAux_spec : ∀ (k : ℕ) (u : List Bool), u.length ≤ k →
    unDigAux k u = digitBits u.length
  | 0, u, h => by rw [Nat.le_zero.mp h]; rfl
  | (k + 1), u, h => by
      rw [unDigAux]
      by_cases hu : u.length = k + 1
      · rw [if_pos hu, hu]
      · rw [if_neg hu]
        exact unDigAux_spec k u (by omega)

lemma unDigAux_mem_FP : ∀ (k : ℕ) {A : List Bool → List Bool}, A ∈ FP →
    (fun z => unDigAux k (A z)) ∈ FP
  | 0, _, _ => constFn_mem_FP _
  | (k + 1), A, hA => by
      exact ifEqLen_mem_FP hA (k + 1) (constFn_mem_FP _) (unDigAux_mem_FP k hA)

/-- The three bits of a unary count below eight. -/
def unDig (u : List Bool) : List Bool := unDigAux 7 u

lemma unDig_spec {u : List Bool} (h : u.length ≤ 7) : unDig u = digitBits u.length :=
  unDigAux_spec 7 u h

@[simp] lemma unDigAux_length : ∀ (k : ℕ) (u : List Bool), (unDigAux k u).length = 3
  | 0, _ => rfl
  | (k + 1), u => by
      rw [unDigAux]
      split
      · rfl
      · exact unDigAux_length k u

@[simp] lemma unDig_length (u : List Bool) : (unDig u).length = 3 := unDigAux_length 7 u

lemma unDig_mem_FP {A : List Bool → List Bool} (hA : A ∈ FP) :
    (fun z => unDig (A z)) ∈ FP := unDigAux_mem_FP 7 hA

/-! ## Addition

The configuration is `pair (pair carry out) (pair a b)`: a unary carry (zero or one
mark), the result digits emitted so far, and the two unconsumed operand suffixes.  One
step pops three bits off each operand, adds the two digits and the carry *in unary*, and
appends the low digit to `out`.

Surplus steps are harmless: once both operands are exhausted the step appends the carry
and then a zero digit forever, and trailing zero digits do not change `digitVal`. -/

private def aCar (v : List Bool) : List Bool := fstBlock (fstBlock v)
private def aOut (v : List Bool) : List Bool := sndBlock (fstBlock v)
private def aA (v : List Bool) : List Bool := fstBlock (sndBlock v)
private def aB (v : List Bool) : List Bool := sndBlock (sndBlock v)

private def three : List Bool := [false, false, false]
private def four : List Bool := [false, false, false, false]

/-- The digit sum of the step, in unary: at most seven marks. -/
private def aSum (v : List Bool) : List Bool := digU (aA v) ++ digU (aB v) ++ aCar v

/-- The low digit of the step's sum, still in unary. -/
private def aLow (v : List Bool) : List Bool :=
  if (aSum v).length ≤ 3 then aSum v else (aSum v).drop 4

/-- One digit of the addition loop. -/
def addStep (v : List Bool) : List Bool :=
  pair (pair (if (aSum v).length ≤ 3 then [] else [true]) (aOut v ++ unDig (aLow v)))
    (pair ((aA v).drop 3) ((aB v).drop 3))

private lemma aCar_mem_FP : aCar ∈ FP := mem_FP_comp fstBlock_mem_FP fstBlock_mem_FP
private lemma aOut_mem_FP : aOut ∈ FP := mem_FP_comp fstBlock_mem_FP sndBlock_mem_FP
private lemma aA_mem_FP : aA ∈ FP := mem_FP_comp sndBlock_mem_FP fstBlock_mem_FP
private lemma aB_mem_FP : aB ∈ FP := mem_FP_comp sndBlock_mem_FP sndBlock_mem_FP

private lemma aSum_mem_FP : aSum ∈ FP :=
  appendFn_mem_FP (appendFn_mem_FP (digU_mem_FP aA_mem_FP) (digU_mem_FP aB_mem_FP))
    aCar_mem_FP

private lemma aLow_mem_FP : aLow ∈ FP :=
  ifLeLen_mem_FP aSum_mem_FP 3 aSum_mem_FP
    (by simpa [four] using dropLenFn_mem_FP (constFn_mem_FP four) aSum_mem_FP)

/-- Proof kind: `C` composition.  Provenance: (b) `Complexity.Cobham` combinators,
(a) `TokenFold.dropLenFn_mem_FP`, `TokenFold.ifLeLen_mem_FP`. -/
lemma addStep_mem_FP : addStep ∈ FP :=
  pairFn_mem_FP
    (pairFn_mem_FP
      (ifLeLen_mem_FP aSum_mem_FP 3 (constFn_mem_FP []) (constFn_mem_FP [true]))
      (appendFn_mem_FP aOut_mem_FP (unDig_mem_FP aLow_mem_FP)))
    (pairFn_mem_FP
      (by simpa [three] using dropLenFn_mem_FP (constFn_mem_FP three) aA_mem_FP)
      (by simpa [three] using dropLenFn_mem_FP (constFn_mem_FP three) aB_mem_FP))

/-! ### The digit-level model -/

/-- The addition loop's configuration, written from digit runs. -/
private def addCfg (c : ℕ) (out as bs : List ℕ) : List Bool :=
  pair (pair (List.replicate c true) (digitsToBits out))
    (pair (digitsToBits as) (digitsToBits bs))

private lemma digU_digitsToBits {ds : List ℕ} (h : ∀ d ∈ ds, d < 4) :
    digU (digitsToBits ds) = List.replicate (ds.headD 0) true := by
  cases ds with
  | nil => simp
  | cons d ds =>
      rw [digitsToBits_cons, digU_digitBits d (by have := h d (by simp); omega)]
      simp

private lemma drop_digitsToBits (ds : List ℕ) :
    (digitsToBits ds).drop 3 = digitsToBits ds.tail := by
  cases ds with
  | nil => simp
  | cons d ds => rw [digitsToBits_cons]; simp

private lemma digitVal_headD (ds : List ℕ) :
    digitVal ds = ds.headD 0 + 4 * digitVal ds.tail := by
  cases ds with
  | nil => simp [digitVal]
  | cons d ds => rfl

/-- **One step of the addition loop, at the digit level.**

Proof kind: `P` proved.  Provenance: (a) `digU_digitBits`, `unDig_spec`. -/
private lemma addStep_addCfg {c : ℕ} (hc : c ≤ 1) (out as bs : List ℕ)
    (has : ∀ d ∈ as, d < 4) (hbs : ∀ d ∈ bs, d < 4) :
    addStep (addCfg c out as bs)
      = addCfg ((as.headD 0 + bs.headD 0 + c) / 4)
          (out ++ [(as.headD 0 + bs.headD 0 + c) % 4]) as.tail bs.tail := by
  have hda : as.headD 0 < 4 := by
    cases as with
    | nil => norm_num
    | cons d ds => exact has d (by simp)
  have hdb : bs.headD 0 < 4 := by
    cases bs with
    | nil => norm_num
    | cons d ds => exact hbs d (by simp)
  set s := as.headD 0 + bs.headD 0 + c with hsdef
  have hs7 : s ≤ 7 := by omega
  have hcar : aCar (addCfg c out as bs) = List.replicate c true := by
    simp [aCar, addCfg]
  have hAA : aA (addCfg c out as bs) = digitsToBits as := by simp [aA, addCfg]
  have hBB : aB (addCfg c out as bs) = digitsToBits bs := by simp [aB, addCfg]
  have hOO : aOut (addCfg c out as bs) = digitsToBits out := by simp [aOut, addCfg]
  have hsum : aSum (addCfg c out as bs) = List.replicate s true := by
    rw [aSum, hAA, hBB, hcar, digU_digitsToBits has, digU_digitsToBits hbs,
      ← List.replicate_add, ← List.replicate_add, hsdef]
  have hsumlen : (aSum (addCfg c out as bs)).length = s := by rw [hsum]; simp
  have hlow : unDig (aLow (addCfg c out as bs)) = digitBits (s % 4) := by
    rw [aLow, hsumlen, hsum]
    by_cases h : s ≤ 3
    · rw [if_pos h, unDig_spec (by simp; omega)]
      congr 1
      simp
      omega
    · rw [if_neg h, unDig_spec (by simp; omega)]
      congr 1
      simp
      omega
  have hflag : (if (aSum (addCfg c out as bs)).length ≤ 3 then ([] : List Bool) else [true])
      = List.replicate (s / 4) true := by
    rw [hsumlen]
    by_cases h : s ≤ 3
    · rw [if_pos h, show s / 4 = 0 from by omega]; rfl
    · rw [if_neg h, show s / 4 = 1 from by omega]; rfl
  rw [addStep, hflag, hOO, hlow, hAA, hBB, drop_digitsToBits, drop_digitsToBits, addCfg,
    digitsToBits_append]
  rfl

/-- **The addition loop, run to completion.**

Proof kind: `P` proved.  Provenance: (a) `addStep_addCfg`, `TokenFold.digitVal_append`. -/
private lemma addStep_iterate : ∀ (n c : ℕ) (out as bs : List ℕ), c ≤ 1 →
    (∀ d ∈ as, d < 4) → (∀ d ∈ bs, d < 4) → as.length ≤ n → bs.length ≤ n →
    ∃ res : List ℕ, (∀ d ∈ res, d < 4) ∧
      addStep^[n + 1] (addCfg c out as bs) = addCfg 0 (out ++ res) [] [] ∧
      digitVal (out ++ res)
        = digitVal out + 4 ^ out.length * (digitVal as + digitVal bs + c)
  | 0, c, out, as, bs, hc, has, hbs, hna, hnb => by
      have hasn : as = [] := List.eq_nil_of_length_eq_zero (by omega)
      have hbsn : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hasn; subst hbsn
      refine ⟨[c], ?_, ?_, ?_⟩
      · intro d hd; simp at hd; omega
      · rw [Function.iterate_one, addStep_addCfg hc out [] [] has hbs]
        simp only [List.headD_nil, List.tail_nil]
        rw [show (0 + 0 + c) / 4 = 0 from by omega, show (0 + 0 + c) % 4 = c from by omega]
      · rw [digitVal_append]
        simp [digitVal]
  | (n + 1), c, out, as, bs, hc, has, hbs, hna, hnb => by
      set da := as.headD 0 with hda
      set db := bs.headD 0 with hdb
      set s := da + db + c with hs
      have hda4 : da < 4 := by
        cases as with
        | nil => simp [hda]
        | cons d ds => exact has d (by simp)
      have hdb4 : db < 4 := by
        cases bs with
        | nil => simp [hdb]
        | cons d ds => exact hbs d (by simp)
      have hstep := addStep_addCfg hc out as bs has hbs
      have hc' : s / 4 ≤ 1 := by omega
      have hat : ∀ d ∈ as.tail, d < 4 := fun d hd => has d (List.mem_of_mem_tail hd)
      have hbt : ∀ d ∈ bs.tail, d < 4 := fun d hd => hbs d (List.mem_of_mem_tail hd)
      have hlat : as.tail.length ≤ n := by
        cases as with
        | nil => simp
        | cons d ds => simp at hna ⊢; omega
      have hlbt : bs.tail.length ≤ n := by
        cases bs with
        | nil => simp
        | cons d ds => simp at hnb ⊢; omega
      obtain ⟨res, hres4, hreseq, hresval⟩ :=
        addStep_iterate n (s / 4) (out ++ [s % 4]) as.tail bs.tail hc' hat hbt hlat hlbt
      refine ⟨s % 4 :: res, ?_, ?_, ?_⟩
      · intro d hd
        rcases List.mem_cons.mp hd with h | h
        · omega
        · exact hres4 d h
      · rw [Function.iterate_succ_apply, hstep, ← hs, hreseq]
        simp
      · have hsplit : out ++ (s % 4 :: res) = (out ++ [s % 4]) ++ res := by simp
        have hlen : (out ++ [s % 4]).length = out.length + 1 := by simp
        have hone : digitVal [s % 4] = s % 4 := by simp [digitVal]
        have hAs : digitVal as = da + 4 * digitVal as.tail := digitVal_headD as
        have hBs : digitVal bs = db + 4 * digitVal bs.tail := digitVal_headD bs
        have h4 : s % 4 + 4 * (s / 4) = s := by omega
        have hexp : digitVal as + digitVal bs + c
            = s % 4 + 4 * (s / 4) + 4 * digitVal as.tail + 4 * digitVal bs.tail := by
          rw [hAs, hBs]; omega
        rw [hsplit, hresval, hlen, digitVal_append, hone, pow_succ, hexp]
        ring

/-! ### The addition loop as a member of `FP`

The loop runs `|z| + 1` steps, which over-counts the digits of either operand by a wide
margin; the surplus steps append zero digits.  The width bound has to hold on *every*
input, not just on well-formed configurations, so it is carried by a shape invariant. -/

private def addInit (z : List Bool) : List Bool :=
  pair (pair [] []) (pair ((fstBlock z).take z.length) ((sndBlock z).take z.length))

private def addRuler (z : List Bool) : List Bool := z ++ [false]

private def addWidth (z : List Bool) : List Bool :=
  List.replicate ((addRuler z).length * (List.replicate 18 true).length) false

/-- Base-four addition on digit words, packed as `pair a b`. -/
def addW (z : List Bool) : List Bool := aOut (addStep^[(addRuler z).length] (addInit z))

/-- The shape and width invariant the loop maintains on arbitrary inputs. -/
private def AddBnd (m k : ℕ) (v : List Bool) : Prop :=
  ∃ c o a b : List Bool, v = pair (pair c o) (pair a b) ∧
    c.length ≤ 1 ∧ o.length ≤ m ∧ a.length ≤ k ∧ b.length ≤ k

private lemma AddBnd.mono {m m' k : ℕ} {v : List Bool} (h : AddBnd m k v) (hm : m ≤ m') :
    AddBnd m' k v := by
  obtain ⟨c, o, a, b, hv, hc, ho, ha, hb⟩ := h
  exact ⟨c, o, a, b, hv, hc, by omega, ha, hb⟩

private lemma AddBnd.step {m k : ℕ} {v : List Bool} (h : AddBnd m k v) :
    AddBnd (m + 3) k (addStep v) := by
  obtain ⟨c, o, a, b, rfl, hc, ho, ha, hb⟩ := h
  refine ⟨_, _, _, _, rfl, ?_, ?_, ?_, ?_⟩
  · split <;> simp
  · simp only [aOut, fstBlock_pair, sndBlock_pair, List.length_append, unDig_length]
    omega
  · simp only [aA, fstBlock_pair, sndBlock_pair, List.length_drop]
    omega
  · simp only [aB, sndBlock_pair, List.length_drop]
    omega

private lemma AddBnd.iterate {k : ℕ} : ∀ (n : ℕ) {m : ℕ} {v : List Bool}, AddBnd m k v →
    AddBnd (m + 3 * n) k (addStep^[n] v)
  | 0, m, v, h => by simpa using h
  | (n + 1), m, v, h => by
      rw [Function.iterate_succ_apply]
      exact (AddBnd.iterate n h.step).mono (by omega)

private lemma AddBnd.length_le {m k : ℕ} {v : List Bool} (h : AddBnd m k v) :
    v.length ≤ 2 * m + 3 * k + 12 := by
  obtain ⟨c, o, a, b, rfl, hc, ho, ha, hb⟩ := h
  simp only [pair_length]
  omega

private lemma addInit_bnd (z : List Bool) : AddBnd 0 z.length (addInit z) :=
  ⟨[], [], _, _, rfl, by simp, by simp, by simp, by simp⟩

private lemma addInit_mem_FP : addInit ∈ FP :=
  pairFn_mem_FP (pairFn_mem_FP (constFn_mem_FP []) (constFn_mem_FP []))
    (pairFn_mem_FP
      (by simpa using takeLenFn_mem_FP id_mem_FP fstBlock_mem_FP)
      (by simpa using takeLenFn_mem_FP id_mem_FP sndBlock_mem_FP))

private lemma addRuler_mem_FP : addRuler ∈ FP :=
  appendFn_mem_FP id_mem_FP (constFn_mem_FP [false])

private lemma addWidth_mem_FP : addWidth ∈ FP :=
  mulLenFn_mem_FP addRuler_mem_FP (constFn_mem_FP (List.replicate 18 true))

/-- Proof kind: `C` composition.  Provenance: (b) `Complexity.Cobham.iterate_mem_FP`,
(a) `addStep_mem_FP`, `AddBnd.iterate`. -/
lemma addW_mem_FP : addW ∈ FP := by
  have hbound : ∀ z, ∀ n ≤ (addRuler z).length,
      (addStep^[n] (addInit z)).length ≤ (addWidth z).length := by
    intro z n hn
    have hb := (AddBnd.iterate n (addInit_bnd z)).length_le
    have hr : (addRuler z).length = z.length + 1 := by simp [addRuler]
    have hw : (addWidth z).length = (z.length + 1) * 18 := by simp [addWidth, hr]
    rw [hr] at hn
    rw [hw]
    omega
  exact mem_FP_comp (iterate_mem_FP addStep_mem_FP addInit_mem_FP addRuler_mem_FP
    addWidth_mem_FP hbound) aOut_mem_FP

/-! ### The addition loop's value -/

private lemma aOut_addStep (v : List Bool) : aOut (addStep v) = aOut v ++ unDig (aLow v) := by
  simp [aOut, addStep]

private lemma aOut_length_iterate : ∀ (n : ℕ) (v : List Bool),
    (aOut (addStep^[n] v)).length = (aOut v).length + 3 * n
  | 0, v => by simp
  | (n + 1), v => by
      rw [Function.iterate_succ_apply, aOut_length_iterate n (addStep v), aOut_addStep]
      simp
      omega

private lemma addW_core {as bs : List ℕ} (has : ∀ d ∈ as, d < 4) (hbs : ∀ d ∈ bs, d < 4) :
    ∃ res : List ℕ, (∀ d ∈ res, d < 4) ∧
      addW (pair (digitsToBits as) (digitsToBits bs)) = digitsToBits res ∧
      digitVal res = digitVal as + digitVal bs := by
  have hla := length_digitsToBits as
  have hlb := length_digitsToBits bs
  have hzlen : (pair (digitsToBits as) (digitsToBits bs)).length
      = 2 * (digitsToBits as).length + 2 + (digitsToBits bs).length := pair_length _ _
  have hinit : addInit (pair (digitsToBits as) (digitsToBits bs)) = addCfg 0 [] as bs := by
    rw [addInit, fstBlock_pair, sndBlock_pair,
      List.take_of_length_le (by omega), List.take_of_length_le (by omega), addCfg]
    simp
  have hrul : (addRuler (pair (digitsToBits as) (digitsToBits bs))).length
      = (2 * (digitsToBits as).length + (digitsToBits bs).length + 2) + 1 := by
    simp only [addRuler, List.length_append, List.length_singleton, hzlen]
    omega
  obtain ⟨res, hres4, hreseq, hresval⟩ :=
    addStep_iterate (2 * (digitsToBits as).length + (digitsToBits bs).length + 2) 0 [] as bs
      (by omega) has hbs (by omega) (by omega)
  refine ⟨res, hres4, ?_, ?_⟩
  · rw [addW, hrul, hinit, hreseq]
    simp [aOut, addCfg]
  · simpa using hresval

lemma isDigitWord_addW {a b : List Bool} (ha : IsDigitWord a) (hb : IsDigitWord b) :
    IsDigitWord (addW (pair a b)) := by
  obtain ⟨as, has, rfl⟩ := ha
  obtain ⟨bs, hbs, rfl⟩ := hb
  obtain ⟨res, hres4, hreseq, _⟩ := addW_core has hbs
  exact ⟨res, hres4, hreseq⟩

/-- **Addition is correct.**

Proof kind: `P` proved.  Provenance: (a) `addStep_iterate`. -/
lemma wordVal_addW {a b : List Bool} (ha : IsDigitWord a) (hb : IsDigitWord b) :
    wordVal (addW (pair a b)) = wordVal a + wordVal b := by
  obtain ⟨as, has, rfl⟩ := ha
  obtain ⟨bs, hbs, rfl⟩ := hb
  obtain ⟨res, hres4, hreseq, hresval⟩ := addW_core has hbs
  rw [hreseq, wordVal_digitsToBits hres4, wordVal_digitsToBits has,
    wordVal_digitsToBits hbs, hresval]

/-! ## Subtraction, comparison, predecessor

The same configuration and the same loop, with a *borrow* in place of the carry.  The
loop is run on `pair a b` and its final borrow is the comparison `a < b`: once both
operands are exhausted a set borrow can never clear, so the flag is stable.  Truncated
subtraction and the `≤` test are two readings of that one loop. -/

private def rep4 : List Bool := List.replicate 4 true

/-- The subtrahend of the step — the second operand's digit plus the incoming borrow —
in unary. -/
private def sSub (v : List Bool) : List Bool := digU (aB v) ++ aCar v

/-- The step's output digit, still in unary; a borrow adds four before subtracting. -/
private def sDif (v : List Bool) : List Bool :=
  if (sSub v).length ≤ (digU (aA v)).length then (digU (aA v)).drop (sSub v).length
  else (digU (aA v) ++ rep4).drop (sSub v).length

/-- The outgoing borrow. -/
private def sBor (v : List Bool) : List Bool :=
  if (sSub v).length ≤ (digU (aA v)).length then [] else [true]

/-- One digit of the subtraction loop. -/
def subStep (v : List Bool) : List Bool :=
  pair (pair (sBor v) (aOut v ++ unDig (sDif v)))
    (pair ((aA v).drop 3) ((aB v).drop 3))

private lemma sSub_mem_FP : sSub ∈ FP :=
  appendFn_mem_FP (digU_mem_FP aB_mem_FP) aCar_mem_FP

private lemma sDif_mem_FP : sDif ∈ FP :=
  selectHeadFn_leFlag_mem_FP (digU_mem_FP aA_mem_FP) sSub_mem_FP
    (dropLenFn_mem_FP sSub_mem_FP (digU_mem_FP aA_mem_FP))
    (dropLenFn_mem_FP sSub_mem_FP
      (appendFn_mem_FP (digU_mem_FP aA_mem_FP) (constFn_mem_FP rep4)))

private lemma sBor_mem_FP : sBor ∈ FP :=
  selectHeadFn_leFlag_mem_FP (digU_mem_FP aA_mem_FP) sSub_mem_FP
    (constFn_mem_FP []) (constFn_mem_FP [true])

/-- Proof kind: `C` composition.  Provenance: (b) `Complexity.Cobham` combinators,
(a) `TokenFold.selectHeadFn_leFlag_mem_FP`, `TokenFold.dropLenFn_mem_FP`. -/
lemma subStep_mem_FP : subStep ∈ FP :=
  pairFn_mem_FP
    (pairFn_mem_FP sBor_mem_FP (appendFn_mem_FP aOut_mem_FP (unDig_mem_FP sDif_mem_FP)))
    (pairFn_mem_FP
      (by simpa [three] using dropLenFn_mem_FP (constFn_mem_FP three) aA_mem_FP)
      (by simpa [three] using dropLenFn_mem_FP (constFn_mem_FP three) aB_mem_FP))

private lemma AddBnd.stepSub {m k : ℕ} {v : List Bool} (h : AddBnd m k v) :
    AddBnd (m + 3) k (subStep v) := by
  obtain ⟨c, o, a, b, rfl, hc, ho, ha, hb⟩ := h
  refine ⟨_, _, _, _, rfl, ?_, ?_, ?_, ?_⟩
  · rw [sBor]; split <;> simp
  · simp only [aOut, fstBlock_pair, sndBlock_pair, List.length_append, unDig_length]
    omega
  · simp only [aA, fstBlock_pair, sndBlock_pair, List.length_drop]
    omega
  · simp only [aB, sndBlock_pair, List.length_drop]
    omega

private lemma AddBnd.iterateSub {k : ℕ} : ∀ (n : ℕ) {m : ℕ} {v : List Bool}, AddBnd m k v →
    AddBnd (m + 3 * n) k (subStep^[n] v)
  | 0, m, v, h => by simpa using h
  | (n + 1), m, v, h => by
      rw [Function.iterate_succ_apply]
      exact (AddBnd.iterateSub n h.stepSub).mono (by omega)

/-- The subtraction loop, run to exhaustion: the final borrow paired with the digits. -/
def subCore (z : List Bool) : List Bool := subStep^[(addRuler z).length] (addInit z)

lemma subCore_mem_FP : subCore ∈ FP := by
  have hbound : ∀ z, ∀ n ≤ (addRuler z).length,
      (subStep^[n] (addInit z)).length ≤ (addWidth z).length := by
    intro z n hn
    have hb := (AddBnd.iterateSub n (addInit_bnd z)).length_le
    have hr : (addRuler z).length = z.length + 1 := by simp [addRuler]
    have hw : (addWidth z).length = (z.length + 1) * 18 := by simp [addWidth, hr]
    rw [hr] at hn
    rw [hw]
    omega
  exact iterate_mem_FP subStep_mem_FP addInit_mem_FP addRuler_mem_FP addWidth_mem_FP hbound

/-- Truncated base-four subtraction on digit words, packed as `pair a b`. -/
def subW (z : List Bool) : List Bool :=
  selectHead (emptyFlag (aCar (subCore z))) (aOut (subCore z)) []

/-- The comparison `wordVal a ≤ wordVal b`, as `[true]` for yes and `[]` for no. -/
def leW (z : List Bool) : List Bool :=
  selectHead (emptyFlag (aCar (subCore (pair (sndBlock z) (fstBlock z))))) [true] []

/-- The digit word for `1`. -/
def oneW : List Bool := digitsToBits [1]

/-- The predecessor of a digit word. -/
def predW (w : List Bool) : List Bool := subW (pair w oneW)

lemma subW_mem_FP : subW ∈ FP := by
  have hc : (fun z => aCar (subCore z)) ∈ FP := by
    simpa [Function.comp_def] using mem_FP_comp subCore_mem_FP aCar_mem_FP
  have ho : (fun z => aOut (subCore z)) ∈ FP := by
    simpa [Function.comp_def] using mem_FP_comp subCore_mem_FP aOut_mem_FP
  exact selectHeadFn_mem_FP (emptyFlag_mem_FP hc) ho (constFn_mem_FP [])

lemma leW_mem_FP : leW ∈ FP := by
  have hs : (fun z => subCore (pair (sndBlock z) (fstBlock z))) ∈ FP := by
    simpa [Function.comp_def] using
      mem_FP_comp (pairFn_mem_FP sndBlock_mem_FP fstBlock_mem_FP) subCore_mem_FP
  have hc : (fun z => aCar (subCore (pair (sndBlock z) (fstBlock z)))) ∈ FP := by
    simpa [Function.comp_def] using mem_FP_comp hs aCar_mem_FP
  exact selectHeadFn_mem_FP (emptyFlag_mem_FP hc) (constFn_mem_FP [true]) (constFn_mem_FP [])

lemma predW_mem_FP : predW ∈ FP :=
  mem_FP_comp (pairFn_mem_FP id_mem_FP (constFn_mem_FP oneW)) subW_mem_FP

/-! ### The subtraction loop's value -/

/-- **One step of the subtraction loop, at the digit level.**

Proof kind: `P` proved.  Provenance: (a) `digU_digitBits`, `unDig_spec`. -/
private lemma subStep_addCfg {c : ℕ} (hc : c ≤ 1) (out as bs : List ℕ)
    (has : ∀ d ∈ as, d < 4) (hbs : ∀ d ∈ bs, d < 4) :
    ∃ dg bw : ℕ, dg < 4 ∧ bw ≤ 1 ∧ dg + (bs.headD 0 + c) = as.headD 0 + 4 * bw ∧
      subStep (addCfg c out as bs) = addCfg bw (out ++ [dg]) as.tail bs.tail := by
  have hda : as.headD 0 < 4 := by
    cases as with
    | nil => norm_num
    | cons d ds => exact has d (by simp)
  have hdb : bs.headD 0 < 4 := by
    cases bs with
    | nil => norm_num
    | cons d ds => exact hbs d (by simp)
  set da := as.headD 0 with hdadef
  set t := bs.headD 0 + c with htdef
  have hcar : aCar (addCfg c out as bs) = List.replicate c true := by simp [aCar, addCfg]
  have hAA : aA (addCfg c out as bs) = digitsToBits as := by simp [aA, addCfg]
  have hBB : aB (addCfg c out as bs) = digitsToBits bs := by simp [aB, addCfg]
  have hOO : aOut (addCfg c out as bs) = digitsToBits out := by simp [aOut, addCfg]
  have hdU : digU (aA (addCfg c out as bs)) = List.replicate da true := by
    rw [hAA, digU_digitsToBits has]
  have hsub : sSub (addCfg c out as bs) = List.replicate t true := by
    rw [sSub, hBB, hcar, digU_digitsToBits hbs, ← List.replicate_add]
  have hsublen : (sSub (addCfg c out as bs)).length = t := by rw [hsub]; simp
  have hdUlen : (digU (aA (addCfg c out as bs))).length = da := by rw [hdU]; simp
  by_cases h : t ≤ da
  · refine ⟨da - t, 0, by omega, by omega, by omega, ?_⟩
    have hbor : sBor (addCfg c out as bs) = List.replicate 0 true := by
      rw [sBor, hsublen, hdUlen, if_pos h]; rfl
    have hdif : unDig (sDif (addCfg c out as bs)) = digitBits (da - t) := by
      rw [sDif, hsublen, hdUlen, if_pos h, hdU, List.drop_replicate,
        unDig_spec (by simp; omega)]
      simp
    rw [subStep, hbor, hOO, hdif, hAA, hBB, drop_digitsToBits, drop_digitsToBits, addCfg,
      digitsToBits_append]
    rfl
  · refine ⟨da + 4 - t, 1, by omega, by omega, by omega, ?_⟩
    have hbor : sBor (addCfg c out as bs) = List.replicate 1 true := by
      rw [sBor, hsublen, hdUlen, if_neg h]; rfl
    have hrep : digU (aA (addCfg c out as bs)) ++ rep4 = List.replicate (da + 4) true := by
      rw [hdU, rep4, ← List.replicate_add]
    have hdif : unDig (sDif (addCfg c out as bs)) = digitBits (da + 4 - t) := by
      rw [sDif, hsublen, hdUlen, if_neg h, hrep, List.drop_replicate,
        unDig_spec (by simp; omega)]
      simp
    rw [subStep, hbor, hOO, hdif, hAA, hBB, drop_digitsToBits, drop_digitsToBits, addCfg,
      digitsToBits_append]
    rfl

/-- **The subtraction loop, run to completion.**  The digit run it emits has exactly
`n + 1` digits and the final borrow records whether the subtraction underflowed.

Proof kind: `P` proved.  Provenance: (a) `subStep_addCfg`. -/
private lemma subStep_iterate : ∀ (n c : ℕ) (as bs : List ℕ), c ≤ 1 →
    (∀ d ∈ as, d < 4) → (∀ d ∈ bs, d < 4) → as.length ≤ n → bs.length ≤ n →
    ∃ (res : List ℕ) (bfin : ℕ), (∀ d ∈ res, d < 4) ∧ res.length = n + 1 ∧ bfin ≤ 1 ∧
      digitVal res + (digitVal bs + c) = digitVal as + 4 ^ (n + 1) * bfin ∧
      ∀ out : List ℕ, subStep^[n + 1] (addCfg c out as bs) = addCfg bfin (out ++ res) [] []
  | 0, c, as, bs, hc, has, hbs, hna, hnb => by
      have hasn : as = [] := List.eq_nil_of_length_eq_zero (by omega)
      have hbsn : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hasn; subst hbsn
      obtain ⟨dg, bw, hdg, hbw, heq, hstep⟩ := subStep_addCfg hc [] [] [] has hbs
      refine ⟨[dg], bw, ?_, rfl, hbw, ?_, ?_⟩
      · intro d hd; simp at hd; omega
      · simp only [List.headD_nil] at heq
        simp only [digitVal]
        omega
      · intro out
        obtain ⟨dg', bw', hdg', hbw', heq', hstep'⟩ := subStep_addCfg hc out [] [] has hbs
        simp only [List.headD_nil] at heq heq'
        have h1 : dg' = dg := by omega
        have h2 : bw' = bw := by omega
        rw [Function.iterate_one, hstep', h1, h2]
        simp
  | (n + 1), c, as, bs, hc, has, hbs, hna, hnb => by
      obtain ⟨dg, bw, hdg, hbw, heq, hstep⟩ := subStep_addCfg hc [] as bs has hbs
      have hat : ∀ d ∈ as.tail, d < 4 := fun d hd => has d (List.mem_of_mem_tail hd)
      have hbt : ∀ d ∈ bs.tail, d < 4 := fun d hd => hbs d (List.mem_of_mem_tail hd)
      have hlat : as.tail.length ≤ n := by
        cases as with
        | nil => simp
        | cons d ds => simp at hna ⊢; omega
      have hlbt : bs.tail.length ≤ n := by
        cases bs with
        | nil => simp
        | cons d ds => simp at hnb ⊢; omega
      obtain ⟨res, bfin, hres4, hreslen, hbfin, hresval, hreseq⟩ :=
        subStep_iterate n bw as.tail bs.tail hbw hat hbt hlat hlbt
      refine ⟨dg :: res, bfin, ?_, by simp [hreslen], hbfin, ?_, ?_⟩
      · intro d hd
        rcases List.mem_cons.mp hd with h | h
        · omega
        · exact hres4 d h
      · have hAs : digitVal as = as.headD 0 + 4 * digitVal as.tail := digitVal_headD as
        have hBs : digitVal bs = bs.headD 0 + 4 * digitVal bs.tail := digitVal_headD bs
        have hd : digitVal (dg :: res) = dg + 4 * digitVal res := rfl
        have h4 : 4 * (digitVal res + (digitVal bs.tail + bw))
            = 4 * (digitVal as.tail + 4 ^ (n + 1) * bfin) := by rw [hresval]
        rw [hd, hAs, hBs, pow_succ]
        nlinarith [h4, heq]
      · intro out
        obtain ⟨dg', bw', hdg', hbw', heq', hstep'⟩ := subStep_addCfg hc out as bs has hbs
        have h1 : dg' = dg := by omega
        have h2 : bw' = bw := by omega
        rw [Function.iterate_succ_apply, hstep', h1, h2, hreseq (out ++ [dg])]
        simp

/-! ### Reading the subtraction loop -/

@[simp] lemma wordVal_nil : wordVal [] = 0 := rfl

lemma isDigitWord_nil : IsDigitWord [] := ⟨[], by simp, rfl⟩

@[simp] lemma wordVal_oneW : wordVal oneW = 1 := by
  rw [oneW, wordVal_digitsToBits (by intro d hd; simp at hd; omega)]
  rfl

lemma isDigitWord_oneW : IsDigitWord oneW := ⟨[1], by intro d hd; simp at hd; omega, rfl⟩

private lemma subCore_core {as bs : List ℕ} (has : ∀ d ∈ as, d < 4) (hbs : ∀ d ∈ bs, d < 4) :
    ∃ (res : List ℕ) (bfin : ℕ), (∀ d ∈ res, d < 4) ∧ bfin ≤ 1 ∧
      digitVal res + digitVal bs = digitVal as + 4 ^ res.length * bfin ∧
      digitVal res < 4 ^ res.length ∧
      subCore (pair (digitsToBits as) (digitsToBits bs)) = addCfg bfin res [] [] := by
  have hla := length_digitsToBits as
  have hlb := length_digitsToBits bs
  have hzlen : (pair (digitsToBits as) (digitsToBits bs)).length
      = 2 * (digitsToBits as).length + 2 + (digitsToBits bs).length := pair_length _ _
  have hinit : addInit (pair (digitsToBits as) (digitsToBits bs)) = addCfg 0 [] as bs := by
    rw [addInit, fstBlock_pair, sndBlock_pair,
      List.take_of_length_le (by omega), List.take_of_length_le (by omega), addCfg]
    simp
  have hrul : (addRuler (pair (digitsToBits as) (digitsToBits bs))).length
      = (2 * (digitsToBits as).length + (digitsToBits bs).length + 2) + 1 := by
    simp only [addRuler, List.length_append, List.length_singleton, hzlen]
    omega
  obtain ⟨res, bfin, hres4, hreslen, hbfin, hresval, hreseq⟩ :=
    subStep_iterate (2 * (digitsToBits as).length + (digitsToBits bs).length + 2) 0 as bs
      (by omega) has hbs (by omega) (by omega)
  refine ⟨res, bfin, hres4, hbfin, ?_, digitVal_lt res hres4, ?_⟩
  · rw [hreslen]
    simpa using hresval
  · rw [subCore, hrul, hinit]
    simpa using hreseq []

/-- The final borrow is clear exactly when the subtraction does not underflow. -/
private lemma borrow_eq_zero_iff {res bs as : List ℕ} {bfin n : ℕ} (hbfin : bfin ≤ 1)
    (hlen : res.length = n) (hval : digitVal res + digitVal bs = digitVal as + 4 ^ n * bfin)
    (hlt : digitVal res < 4 ^ n) : bfin = 0 ↔ digitVal bs ≤ digitVal as := by
  subst hlen
  constructor
  · intro h; subst h; omega
  · intro h
    by_contra hne
    have hb1 : bfin = 1 := by omega
    subst hb1
    omega

private lemma aCar_addCfg (c : ℕ) (out as bs : List ℕ) :
    aCar (addCfg c out as bs) = List.replicate c true := by simp [aCar, addCfg]

private lemma aOut_addCfg (c : ℕ) (out as bs : List ℕ) :
    aOut (addCfg c out as bs) = digitsToBits out := by simp [aOut, addCfg]

/-- **Truncated subtraction is correct**, and its result is again a digit word.

Proof kind: `P` proved.  Provenance: (a) `subStep_iterate`. -/
lemma subW_spec {a b : List Bool} (ha : IsDigitWord a) (hb : IsDigitWord b) :
    IsDigitWord (subW (pair a b)) ∧ wordVal (subW (pair a b)) = wordVal a - wordVal b := by
  obtain ⟨as, has, rfl⟩ := ha
  obtain ⟨bs, hbs, rfl⟩ := hb
  obtain ⟨res, bfin, hres4, hbfin, hval, hlt, hcore⟩ := subCore_core has hbs
  have hiff := borrow_eq_zero_iff (n := res.length) hbfin rfl hval hlt
  rw [wordVal_digitsToBits has, wordVal_digitsToBits hbs]
  rcases Nat.eq_zero_or_pos bfin with h0 | hpos
  · have hle : digitVal bs ≤ digitVal as := hiff.mp h0
    have hsub : subW (pair (digitsToBits as) (digitsToBits bs)) = digitsToBits res := by
      rw [subW, hcore, aCar_addCfg, aOut_addCfg, h0]
      exact selectHead_emptyFlag_nil _ _
    rw [hsub]
    refine ⟨⟨res, hres4, rfl⟩, ?_⟩
    rw [wordVal_digitsToBits hres4]
    subst h0
    omega
  · have hb1 : bfin = 1 := by omega
    have hgt : ¬ digitVal bs ≤ digitVal as := fun h => by
      have := hiff.mpr h; omega
    have hsub : subW (pair (digitsToBits as) (digitsToBits bs)) = [] := by
      rw [subW, hcore, aCar_addCfg, aOut_addCfg, hb1]
      exact selectHead_emptyFlag_cons _ _ _ _
    rw [hsub]
    exact ⟨isDigitWord_nil, by simp; omega⟩

lemma isDigitWord_subW {a b : List Bool} (ha : IsDigitWord a) (hb : IsDigitWord b) :
    IsDigitWord (subW (pair a b)) := (subW_spec ha hb).1

lemma wordVal_subW {a b : List Bool} (ha : IsDigitWord a) (hb : IsDigitWord b) :
    wordVal (subW (pair a b)) = wordVal a - wordVal b := (subW_spec ha hb).2

/-- **The comparison is correct.**  The convention is `[true]` for `≤` and `[]` otherwise.

Proof kind: `P` proved.  Provenance: (a) `subStep_iterate`. -/
lemma leW_spec {a b : List Bool} (ha : IsDigitWord a) (hb : IsDigitWord b) :
    leW (pair a b) = if wordVal a ≤ wordVal b then [true] else [] := by
  obtain ⟨as, has, rfl⟩ := ha
  obtain ⟨bs, hbs, rfl⟩ := hb
  obtain ⟨res, bfin, hres4, hbfin, hval, hlt, hcore⟩ := subCore_core hbs has
  have hiff := borrow_eq_zero_iff (n := res.length) hbfin rfl hval hlt
  have hrw : leW (pair (digitsToBits as) (digitsToBits bs))
      = selectHead (emptyFlag (List.replicate bfin true)) [true] [] := by
    rw [leW, sndBlock_pair, fstBlock_pair, hcore, aCar_addCfg]
  rw [hrw, wordVal_digitsToBits has, wordVal_digitsToBits hbs]
  rcases Nat.eq_zero_or_pos bfin with h0 | hpos
  · rw [h0, if_pos (hiff.mp h0)]
    exact selectHead_emptyFlag_nil _ _
  · have hb1 : bfin = 1 := by omega
    rw [hb1, if_neg (fun h => by have := hiff.mpr h; omega)]
    exact selectHead_emptyFlag_cons _ _ _ _

/-- **The predecessor is correct.**

Proof kind: `C` composition.  Provenance: (a) `subW_spec`. -/
lemma predW_spec {w : List Bool} (hw : IsDigitWord w) :
    IsDigitWord (predW w) ∧ wordVal (predW w) = wordVal w - 1 := by
  have h := subW_spec hw isDigitWord_oneW
  rw [wordVal_oneW] at h
  exact h

lemma isDigitWord_predW {w : List Bool} (hw : IsDigitWord w) : IsDigitWord (predW w) :=
  (predW_spec hw).1

lemma wordVal_predW {w : List Bool} (hw : IsDigitWord w) : wordVal (predW w) = wordVal w - 1 :=
  (predW_spec hw).2

/-! ## Integer square root

The loop reads the digit run from the *most* significant end and maintains the pair
`(s, r)` with `s = Nat.sqrt p` and `r = p - s²` for the prefix `p` read so far.  Appending
the next digit `d` replaces `p` by `4p + d`, hence `r` by `r' = 4r + d`, and the new root
is `2s + q` for the largest `q < 4` with `(4s + q)·q ≤ r'` — an identity that needs no
multiplier, because for `q ≤ 3` the product `(4s+q)·q` is at most two additions.

Nothing is truncated except the two carried registers, which are cut back to the width of
a fixed ruler at each step; `digitVal_take` is what makes that cut invisible. -/

/-- Cutting a digit run at a width its value fits inside does not change the value. -/
private lemma digitVal_take {ds : List ℕ} {m : ℕ} (h : digitVal ds < 4 ^ m) :
    digitVal (ds.take m) = digitVal ds := by
  by_cases hle : ds.length ≤ m
  · rw [List.take_of_length_le hle]
  · have hlt : m < ds.length := by omega
    have hlen : (ds.take m).length = m := by
      rw [List.length_take]; omega
    have key : digitVal ds = digitVal (ds.take m) + 4 ^ m * digitVal (ds.drop m) := by
      conv_lhs => rw [← List.take_append_drop m ds]
      rw [digitVal_append, hlen]
    have hd0 : digitVal (ds.drop m) = 0 := by
      by_contra hne
      have hpos : 0 < digitVal (ds.drop m) := Nat.pos_of_ne_zero hne
      have hge : 4 ^ m ≤ 4 ^ m * digitVal (ds.drop m) := Nat.le_mul_of_pos_right _ hpos
      rw [key] at h
      linarith
    rw [key, hd0]
    simp

/-- Cutting the *bits* of a digit run at a multiple of three cuts the run. -/
private lemma take_digitsToBits : ∀ (ds : List ℕ) (m : ℕ),
    (digitsToBits ds).take (3 * m) = digitsToBits (ds.take m)
  | [], m => by simp
  | (d :: ds), 0 => by simp
  | (d :: ds), (m + 1) => by
      rw [digitsToBits_cons, List.take_append, length_digitBits,
        List.take_of_length_le (by rw [length_digitBits]; omega),
        show 3 * (m + 1) - 3 = 3 * m from by omega, take_digitsToBits ds m]
      simp

/-- The digit the loop chooses: the largest `q < 4` with `(4s + q)·q ≤ r`. -/
private def sqDigit (s r : ℕ) : ℕ :=
  if (4 * s + 3) * 3 ≤ r then 3 else if (4 * s + 2) * 2 ≤ r then 2
  else if (4 * s + 1) * 1 ≤ r then 1 else 0

private lemma sqDigit_lt (s r : ℕ) : sqDigit s r < 4 := by
  rw [sqDigit]; split_ifs <;> omega

private lemma sqDigit_le (s r : ℕ) : (4 * s + sqDigit s r) * sqDigit s r ≤ r := by
  rw [sqDigit]; split_ifs <;> omega

private lemma sqDigit_max (s r : ℕ) : sqDigit s r = 3 ∨
    ¬ ((4 * s + sqDigit s r + 1) * (sqDigit s r + 1) ≤ r) := by
  rw [sqDigit]
  split_ifs with h3 h2 h1
  · exact Or.inl rfl
  · exact Or.inr (by simpa using h3)
  · exact Or.inr (by simpa using h2)
  · exact Or.inr (by simpa using h1)

/-- **The base-four square-root recurrence.**  Appending one digit to the prefix takes the
root to `2s + q` and the remainder to `r' - (4s+q)·q`.

Proof kind: `P` proved.  Provenance: (b) `Nat.sqrt_le`, `Nat.lt_succ_sqrt`, `Nat.le_sqrt`,
`Nat.sqrt_lt`. -/
private lemma sqrt_rec (p d : ℕ) (hd : d < 4) :
    Nat.sqrt (4 * p + d) = 2 * Nat.sqrt p +
      sqDigit (Nat.sqrt p) (4 * (p - Nat.sqrt p * Nat.sqrt p) + d)
      ∧ (4 * p + d) - Nat.sqrt (4 * p + d) * Nat.sqrt (4 * p + d)
        = (4 * (p - Nat.sqrt p * Nat.sqrt p) + d)
          - (4 * Nat.sqrt p + sqDigit (Nat.sqrt p) (4 * (p - Nat.sqrt p * Nat.sqrt p) + d))
              * sqDigit (Nat.sqrt p) (4 * (p - Nat.sqrt p * Nat.sqrt p) + d) := by
  set s := Nat.sqrt p with hsdef
  have hs1 : s * s ≤ p := Nat.sqrt_le p
  have hs2 : p < (s + 1) * (s + 1) := Nat.lt_succ_sqrt p
  have hexp : (s + 1) * (s + 1) = s * s + 2 * s + 1 := by ring
  set r := p - s * s with hrdef
  have hp : p = s * s + r := by omega
  have hr2 : r ≤ 2 * s := by omega
  set r' := 4 * r + d with hr'def
  set q := sqDigit s r' with hqdef
  have hq4 : q < 4 := sqDigit_lt s r'
  have hqle : (4 * s + q) * q ≤ r' := sqDigit_le s r'
  have hqmax := sqDigit_max s r'
  rw [← hqdef] at hqmax
  have hkk : (2 * s + q) * (2 * s + q) = 4 * (s * s) + (4 * s + q) * q := by ring
  have hkk1 : (2 * s + q + 1) * (2 * s + q + 1) = 4 * (s * s) + (4 * s + q + 1) * (q + 1) := by
    ring
  have hp' : 4 * p + d = 4 * (s * s) + r' := by omega
  have hlow : (2 * s + q) * (2 * s + q) ≤ 4 * p + d := by omega
  have hhigh : 4 * p + d < (2 * s + q + 1) * (2 * s + q + 1) := by
    rcases hqmax with h3 | hnot
    · have h4 : (4 * s + q + 1) * (q + 1) = 16 * s + 16 := by rw [h3]; ring
      omega
    · omega
  have h1 : 2 * s + q ≤ Nat.sqrt (4 * p + d) := Nat.le_sqrt.mpr hlow
  have h2 : Nat.sqrt (4 * p + d) < 2 * s + q + 1 := Nat.sqrt_lt.mpr hhigh
  have heq : Nat.sqrt (4 * p + d) = 2 * s + q := by omega
  refine ⟨heq, ?_⟩
  rw [heq]
  omega

/-! ### The square-root loop

The configuration is `pair (pair s r) (pair rest W)`: the root and remainder so far, the
unconsumed *low* end of the digit word, and a fixed ruler `W` at whose width the two
registers are cut back each step.  Digits are taken from the high end of `rest` — its last
three bits — so no reversal pass is needed. -/

/-- `digitBits q ++ s` is the digit word for `4·⟦s⟧ + q`. -/
private def shiftQ (q : ℕ) (s : List Bool) : List Bool := digitBits q ++ s

/-- The product `(4s + q)·q` for `q < 4`, as at most two additions. -/
private def prodQ : ℕ → List Bool → List Bool
  | 0, _ => []
  | 1, s => shiftQ 1 s
  | 2, s => addW (pair (shiftQ 2 s) (shiftQ 2 s))
  | 3, s => addW (pair (shiftQ 3 s) (addW (pair (shiftQ 3 s) (shiftQ 3 s))))
  | _, _ => []

/-- The remainder with the incoming digit shifted in. -/
private def qRp (v : List Bool) : List Bool :=
  (aA v).drop ((aA v).drop 3).length ++ aOut v

/-- What is left of the digit word after the incoming digit is taken off its high end. -/
private def qRest (v : List Bool) : List Bool := (aA v).take ((aA v).drop 3).length

/-- The configuration the loop moves to when it selects the digit `q`. -/
private def qBranch (q : ℕ) (v : List Bool) : List Bool :=
  pair
    (pair ((addW (pair (addW (pair (aCar v) (aCar v))) (digitsToBits [q]))).take (aB v).length)
      ((subW (pair (qRp v) (prodQ q (aCar v)))).take (aB v).length))
    (pair (qRest v) (aB v))

/-- A flag whose head is `true` exactly when `⟦x⟧ > ⟦y⟧`. -/
private def gtFlagW (x y : List Bool) : List Bool := emptyFlag (leW (pair x y))

/-- One digit of the square-root loop. -/
def sqStep (v : List Bool) : List Bool :=
  selectHead (emptyFlag (aA v)) v
    (selectHead (gtFlagW (prodQ 3 (aCar v)) (qRp v))
      (selectHead (gtFlagW (prodQ 2 (aCar v)) (qRp v))
        (selectHead (gtFlagW (prodQ 1 (aCar v)) (qRp v))
          (qBranch 0 v) (qBranch 1 v))
        (qBranch 2 v))
      (qBranch 3 v))

private lemma addWFn_mem_FP {X Y : List Bool → List Bool} (hX : X ∈ FP) (hY : Y ∈ FP) :
    (fun z => addW (pair (X z) (Y z))) ∈ FP := by
  simpa [Function.comp_def] using mem_FP_comp (pairFn_mem_FP hX hY) addW_mem_FP

private lemma subWFn_mem_FP {X Y : List Bool → List Bool} (hX : X ∈ FP) (hY : Y ∈ FP) :
    (fun z => subW (pair (X z) (Y z))) ∈ FP := by
  simpa [Function.comp_def] using mem_FP_comp (pairFn_mem_FP hX hY) subW_mem_FP

private lemma leWFn_mem_FP {X Y : List Bool → List Bool} (hX : X ∈ FP) (hY : Y ∈ FP) :
    (fun z => leW (pair (X z) (Y z))) ∈ FP := by
  simpa [Function.comp_def] using mem_FP_comp (pairFn_mem_FP hX hY) leW_mem_FP

private lemma shiftQ_mem_FP (q : ℕ) {S : List Bool → List Bool} (hS : S ∈ FP) :
    (fun z => shiftQ q (S z)) ∈ FP :=
  appendFn_mem_FP (constFn_mem_FP (digitBits q)) hS

private lemma prodQ_mem_FP : ∀ (q : ℕ) {S : List Bool → List Bool}, S ∈ FP →
    (fun z => prodQ q (S z)) ∈ FP
  | 0, _, _ => constFn_mem_FP []
  | 1, _, hS => shiftQ_mem_FP 1 hS
  | 2, _, hS => addWFn_mem_FP (shiftQ_mem_FP 2 hS) (shiftQ_mem_FP 2 hS)
  | 3, _, hS =>
      addWFn_mem_FP (shiftQ_mem_FP 3 hS)
        (addWFn_mem_FP (shiftQ_mem_FP 3 hS) (shiftQ_mem_FP 3 hS))
  | (_ + 4), _, _ => constFn_mem_FP []

private lemma qRp_mem_FP : qRp ∈ FP := by
  have hdrop3 : (fun v => (aA v).drop 3) ∈ FP := by
    simpa [three] using dropLenFn_mem_FP (constFn_mem_FP three) aA_mem_FP
  exact appendFn_mem_FP (dropLenFn_mem_FP hdrop3 aA_mem_FP) aOut_mem_FP

private lemma qRest_mem_FP : qRest ∈ FP := by
  have hdrop3 : (fun v => (aA v).drop 3) ∈ FP := by
    simpa [three] using dropLenFn_mem_FP (constFn_mem_FP three) aA_mem_FP
  exact takeLenFn_mem_FP hdrop3 aA_mem_FP

private lemma qBranch_mem_FP (q : ℕ) : qBranch q ∈ FP :=
  pairFn_mem_FP
    (pairFn_mem_FP
      (takeLenFn_mem_FP aB_mem_FP
        (addWFn_mem_FP (addWFn_mem_FP aCar_mem_FP aCar_mem_FP)
          (constFn_mem_FP (digitsToBits [q]))))
      (takeLenFn_mem_FP aB_mem_FP
        (subWFn_mem_FP qRp_mem_FP (prodQ_mem_FP q aCar_mem_FP))))
    (pairFn_mem_FP qRest_mem_FP aB_mem_FP)

private lemma gtFlagWFn_mem_FP (q : ℕ) :
    (fun v => gtFlagW (prodQ q (aCar v)) (qRp v)) ∈ FP :=
  emptyFlag_mem_FP (leWFn_mem_FP (prodQ_mem_FP q aCar_mem_FP) qRp_mem_FP)

/-- Proof kind: `C` composition.  Provenance: (b) `Complexity.Cobham` combinators,
(a) `addW_mem_FP`, `subW_mem_FP`, `leW_mem_FP`. -/
lemma sqStep_mem_FP : sqStep ∈ FP :=
  selectHeadFn_mem_FP (emptyFlag_mem_FP aA_mem_FP) id_mem_FP
    (selectHeadFn_mem_FP (gtFlagWFn_mem_FP 3)
      (selectHeadFn_mem_FP (gtFlagWFn_mem_FP 2)
        (selectHeadFn_mem_FP (gtFlagWFn_mem_FP 1) (qBranch_mem_FP 0) (qBranch_mem_FP 1))
        (qBranch_mem_FP 2))
      (qBranch_mem_FP 3))

/-! ### The square-root loop's width -/

private lemma selectHead_emptyFlag_cases (t X Y : List Bool) :
    selectHead (emptyFlag t) X Y = X ∨ selectHead (emptyFlag t) X Y = Y := by
  cases t with
  | nil => exact Or.inl (selectHead_emptyFlag_nil X Y)
  | cons b t => exact Or.inr (selectHead_emptyFlag_cons b t X Y)

private def SqBnd (w k : ℕ) (v : List Bool) : Prop :=
  ∃ s r rest W : List Bool, v = pair (pair s r) (pair rest W) ∧
    s.length ≤ w ∧ r.length ≤ w ∧ rest.length ≤ k ∧ W.length ≤ w

private lemma SqBnd.branch {w k q : ℕ} {v : List Bool} (h : SqBnd w k v) :
    SqBnd w k (qBranch q v) := by
  obtain ⟨s, r, rest, W, rfl, hs, hr, hrest, hW⟩ := h
  refine ⟨_, _, _, _, rfl, ?_, ?_, ?_, by simpa [aB] using hW⟩
  · simp only [aB, sndBlock_pair, List.length_take]
    omega
  · simp only [aB, sndBlock_pair, List.length_take]
    omega
  · simp only [qRest, aA, fstBlock_pair, sndBlock_pair, List.length_take, List.length_drop]
    omega

private lemma SqBnd.step {w k : ℕ} {v : List Bool} (h : SqBnd w k v) :
    SqBnd w k (sqStep v) := by
  rw [sqStep]
  rcases selectHead_emptyFlag_cases (aA v) v
      (selectHead (gtFlagW (prodQ 3 (aCar v)) (qRp v))
        (selectHead (gtFlagW (prodQ 2 (aCar v)) (qRp v))
          (selectHead (gtFlagW (prodQ 1 (aCar v)) (qRp v)) (qBranch 0 v) (qBranch 1 v))
          (qBranch 2 v))
        (qBranch 3 v)) with h1 | h1 <;> rw [h1]
  · exact h
  · rw [gtFlagW]
    rcases selectHead_emptyFlag_cases (leW (pair (prodQ 3 (aCar v)) (qRp v)))
        (selectHead (gtFlagW (prodQ 2 (aCar v)) (qRp v))
          (selectHead (gtFlagW (prodQ 1 (aCar v)) (qRp v)) (qBranch 0 v) (qBranch 1 v))
          (qBranch 2 v))
        (qBranch 3 v) with h2 | h2 <;> rw [h2]
    · rw [gtFlagW]
      rcases selectHead_emptyFlag_cases (leW (pair (prodQ 2 (aCar v)) (qRp v)))
          (selectHead (gtFlagW (prodQ 1 (aCar v)) (qRp v)) (qBranch 0 v) (qBranch 1 v))
          (qBranch 2 v) with h3 | h3 <;> rw [h3]
      · rw [gtFlagW]
        rcases selectHead_emptyFlag_cases (leW (pair (prodQ 1 (aCar v)) (qRp v)))
            (qBranch 0 v) (qBranch 1 v) with h4 | h4 <;> rw [h4]
        · exact h.branch
        · exact h.branch
      · exact h.branch
    · exact h.branch

private lemma SqBnd.iterate {w k : ℕ} : ∀ (n : ℕ) {v : List Bool}, SqBnd w k v →
    SqBnd w k (sqStep^[n] v)
  | 0, v, h => h
  | (n + 1), v, h => by
      rw [Function.iterate_succ_apply]
      exact SqBnd.iterate n h.step

private lemma SqBnd.length_le {w k : ℕ} {v : List Bool} (h : SqBnd w k v) :
    v.length ≤ 7 * w + 2 * k + 8 := by
  obtain ⟨s, r, rest, W, rfl, hs, hr, hrest, hW⟩ := h
  simp only [pair_length]
  omega

/-! ### `sqrtRemW` -/

private def sqInit (z : List Bool) : List Bool :=
  pair (pair [] []) (pair z (z ++ three))

private def sqWidth (z : List Bool) : List Bool :=
  List.replicate ((addRuler z).length * (List.replicate 40 true).length) false

private lemma sqInit_mem_FP : sqInit ∈ FP :=
  pairFn_mem_FP (pairFn_mem_FP (constFn_mem_FP []) (constFn_mem_FP []))
    (pairFn_mem_FP id_mem_FP (appendFn_mem_FP id_mem_FP (constFn_mem_FP three)))

private lemma sqWidth_mem_FP : sqWidth ∈ FP :=
  mulLenFn_mem_FP addRuler_mem_FP (constFn_mem_FP (List.replicate 40 true))

private lemma sqInit_bnd (z : List Bool) : SqBnd (z.length + 3) z.length (sqInit z) :=
  ⟨[], [], z, z ++ three, rfl, by simp, by simp, le_rfl, by simp [three]⟩

/-- The loop state after the run: the root and the remainder. -/
private def sqCore (z : List Bool) : List Bool :=
  sqStep^[(addRuler z).length] (sqInit z)

private lemma sqCore_mem_FP : sqCore ∈ FP := by
  have hbound : ∀ z, ∀ n ≤ (addRuler z).length,
      (sqStep^[n] (sqInit z)).length ≤ (sqWidth z).length := by
    intro z n _
    have hb := (SqBnd.iterate n (sqInit_bnd z)).length_le
    have hw : (sqWidth z).length = (z.length + 1) * 40 := by
      simp [sqWidth, addRuler]
    rw [hw]
    omega
  exact iterate_mem_FP sqStep_mem_FP sqInit_mem_FP addRuler_mem_FP sqWidth_mem_FP hbound

/-- **Integer square root with remainder** on a digit word: `pair s r` with
`⟦s⟧ = Nat.sqrt ⟦w⟧` and `⟦r⟧ = ⟦w⟧ - ⟦s⟧²`. -/
def sqrtRemW (z : List Bool) : List Bool := pair (aCar (sqCore z)) (aOut (sqCore z))

/-- **Base-four integer square root with remainder is a polynomial-time word function.**

`app:ifp` is the appendix proof of `thm:ifp`, whose efficiency step reads "only finitely many
constants … can be hard-coded into `F`". As printed, `thm:ifp` is false, and the corrected
statement this development proves carries **no** condition on the syntax of the moved
sentences: both halves of the `Recognizable` condition — the compatibility hypothesis of the
restricted form (`Construction/Witnesses/CanonicalCodes.lean`) — stand for `Complexity.FP`
devices, and this is one of the two the development builds instead of assuming
(`LogicalInduction/README.md`, *What differs from the paper*). The sole consumer is
`Construction/Witnesses/FiberTestFP.lean`.

Proof kind: `C` composition.  Provenance: (b) `Complexity.Cobham.iterate_mem_FP`,
(a) `sqStep_mem_FP`, `SqBnd.iterate`.
Paper node: `app:ifp` -/
lemma sqrtRemW_mem_FP : sqrtRemW ∈ FP := by
  have h1 : (fun z => aCar (sqCore z)) ∈ FP := by
    simpa [Function.comp_def] using mem_FP_comp sqCore_mem_FP aCar_mem_FP
  have h2 : (fun z => aOut (sqCore z)) ∈ FP := by
    simpa [Function.comp_def] using mem_FP_comp sqCore_mem_FP aOut_mem_FP
  exact pairFn_mem_FP h1 h2

/-! ### Reading the square-root loop -/

private lemma isDigitWord_cons {q : ℕ} (hq : q < 4) {sd : List ℕ} (hsd : ∀ x ∈ sd, x < 4) :
    IsDigitWord (digitsToBits (q :: sd)) :=
  isDigitWord_digitsToBits (by
    intro x hx
    rcases List.mem_cons.mp hx with h | h
    · omega
    · exact hsd x h)

private lemma wordVal_cons {q : ℕ} (hq : q < 4) {sd : List ℕ} (hsd : ∀ x ∈ sd, x < 4) :
    wordVal (digitsToBits (q :: sd)) = q + 4 * digitVal sd := by
  rw [wordVal_digitsToBits (by
    intro x hx
    rcases List.mem_cons.mp hx with h | h
    · omega
    · exact hsd x h)]
  rfl

private lemma shiftQ_digitsToBits (q : ℕ) (sd : List ℕ) :
    shiftQ q (digitsToBits sd) = digitsToBits (q :: sd) := rfl

private lemma prodQ_spec : ∀ (q : ℕ), q < 4 → ∀ {sd : List ℕ}, (∀ x ∈ sd, x < 4) →
    IsDigitWord (prodQ q (digitsToBits sd)) ∧
      wordVal (prodQ q (digitsToBits sd)) = (4 * digitVal sd + q) * q := by
  intro q hq sd hsd
  interval_cases q
  · exact ⟨isDigitWord_nil, by rw [prodQ]; simp⟩
  · rw [prodQ, shiftQ_digitsToBits]
    exact ⟨isDigitWord_cons (by norm_num) hsd, by rw [wordVal_cons (by norm_num) hsd]; ring⟩
  · rw [prodQ, shiftQ_digitsToBits]
    have hw := isDigitWord_cons (q := 2) (by norm_num) hsd
    refine ⟨isDigitWord_addW hw hw, ?_⟩
    rw [wordVal_addW hw hw, wordVal_cons (by norm_num) hsd]
    ring
  · rw [prodQ, shiftQ_digitsToBits]
    have hw := isDigitWord_cons (q := 3) (by norm_num) hsd
    refine ⟨isDigitWord_addW hw (isDigitWord_addW hw hw), ?_⟩
    rw [wordVal_addW hw (isDigitWord_addW hw hw), wordVal_addW hw hw,
      wordVal_cons (by norm_num) hsd]
    ring

private lemma selectHead_gtFlagW {x y : List Bool} (hx : IsDigitWord x) (hy : IsDigitWord y)
    (X Y : List Bool) :
    selectHead (gtFlagW x y) X Y = if wordVal x ≤ wordVal y then Y else X := by
  rw [gtFlagW, leW_spec hx hy]
  by_cases h : wordVal x ≤ wordVal y
  · rw [if_pos h, if_pos h]
    exact selectHead_emptyFlag_cons true [] X Y
  · rw [if_neg h, if_neg h]
    exact selectHead_emptyFlag_nil X Y

/-- Cutting a digit word at the ruler's width, when its value fits. -/
private lemma take_spec {m : ℕ} {W : List Bool} (hW : W.length = 3 * m) {X : List Bool}
    (hX : IsDigitWord X) (hlt : wordVal X < 4 ^ m) :
    ∃ xs : List ℕ, (∀ x ∈ xs, x < 4) ∧ 3 * xs.length ≤ W.length ∧
      digitVal xs = wordVal X ∧ X.take W.length = digitsToBits xs := by
  obtain ⟨xs0, hxs0, rfl⟩ := hX
  rw [wordVal_digitsToBits hxs0] at hlt
  refine ⟨xs0.take m, fun x hx => hxs0 x (List.mem_of_mem_take hx), ?_, ?_, ?_⟩
  · rw [hW, List.length_take]
    omega
  · rw [wordVal_digitsToBits hxs0]
    exact digitVal_take hlt
  · rw [hW, take_digitsToBits]

private lemma selectHead_emptyFlag_of_ne {t : List Bool} (h : t ≠ []) (X Y : List Bool) :
    selectHead (emptyFlag t) X Y = Y := by
  cases t with
  | nil => exact absurd rfl h
  | cons b t => exact selectHead_emptyFlag_cons b t X Y

/-- **One digit of the square-root loop.**  The loop takes the incoming digit off the high
end of the word, chooses the digit `sqDigit`, and cuts both registers back to the ruler.

Proof kind: `P` proved.  Provenance: (a) `sqrt_rec`, `take_spec`, `wordVal_addW`,
`subW_spec`, `leW_spec`. -/
private lemma sqStep_one {m : ℕ} {W : List Bool} (hW : W.length = 3 * m)
    {p d : ℕ} (hd : d < 4) {sd rd ds₀ : List ℕ}
    (hsd : ∀ x ∈ sd, x < 4) (hrd : ∀ x ∈ rd, x < 4)
    (hs : digitVal sd = Nat.sqrt p) (hr : digitVal rd = p - Nat.sqrt p * Nat.sqrt p)
    (hcap : 4 * p + d < 4 ^ m) :
    ∃ sd' rd' : List ℕ, (∀ x ∈ sd', x < 4) ∧ (∀ x ∈ rd', x < 4) ∧
      3 * sd'.length ≤ W.length ∧ 3 * rd'.length ≤ W.length ∧
      digitVal sd' = Nat.sqrt (4 * p + d) ∧
      digitVal rd' = (4 * p + d) - Nat.sqrt (4 * p + d) * Nat.sqrt (4 * p + d) ∧
      sqStep (pair (pair (digitsToBits sd) (digitsToBits rd))
          (pair (digitsToBits (ds₀ ++ [d])) W))
        = pair (pair (digitsToBits sd') (digitsToBits rd')) (pair (digitsToBits ds₀) W) := by
  set v := pair (pair (digitsToBits sd) (digitsToBits rd))
    (pair (digitsToBits (ds₀ ++ [d])) W) with hv
  have hCar : aCar v = digitsToBits sd := by simp [aCar, hv]
  have hOut : aOut v = digitsToBits rd := by simp [aOut, hv]
  have hBB : aB v = W := by simp [aB, hv]
  have hAA : aA v = digitsToBits ds₀ ++ digitBits d := by
    simp [aA, hv, digitsToBits_append]
  have hdrop3 : ((aA v).drop 3).length = (digitsToBits ds₀).length := by
    rw [hAA, List.length_drop, List.length_append, length_digitBits,
      length_digitsToBits]
    omega
  have hne : aA v ≠ [] := by
    rw [hAA]
    intro h
    have hlen := congrArg List.length h
    simp at hlen
  have hqRp : qRp v = digitsToBits (d :: rd) := by
    rw [qRp, hdrop3, hAA, List.drop_left, hOut]
    rfl
  have hqRest : qRest v = digitsToBits ds₀ := by
    rw [qRest, hdrop3, hAA, List.take_left]
  -- the arithmetic setting
  have hsql : Nat.sqrt p * Nat.sqrt p ≤ p := Nat.sqrt_le p
  have hr'eq : d + 4 * digitVal rd = 4 * (p - Nat.sqrt p * Nat.sqrt p) + d := by
    rw [hr]; ring
  have hSw : IsDigitWord (digitsToBits sd) := isDigitWord_digitsToBits hsd
  have hSwv : wordVal (digitsToBits sd) = digitVal sd := wordVal_digitsToBits hsd
  have hR'w : IsDigitWord (qRp v) := by rw [hqRp]; exact isDigitWord_cons hd hrd
  have hR'v : wordVal (qRp v) = d + 4 * digitVal rd := by
    rw [hqRp]; exact wordVal_cons hd hrd
  have hP : ∀ q : ℕ, q < 4 → IsDigitWord (prodQ q (aCar v)) ∧
      wordVal (prodQ q (aCar v)) = (4 * digitVal sd + q) * q := by
    intro q hq
    rw [hCar]
    exact prodQ_spec q hq hsd
  set q := sqDigit (Nat.sqrt p) (4 * (p - Nat.sqrt p * Nat.sqrt p) + d) with hqdef
  have hq4 : q < 4 := sqDigit_lt _ _
  have hchain : sqStep v = qBranch q v := by
    rw [sqStep, selectHead_emptyFlag_of_ne hne,
      selectHead_gtFlagW (hP 3 (by norm_num)).1 hR'w,
      selectHead_gtFlagW (hP 2 (by norm_num)).1 hR'w,
      selectHead_gtFlagW (hP 1 (by norm_num)).1 hR'w,
      (hP 3 (by norm_num)).2, (hP 2 (by norm_num)).2, (hP 1 (by norm_num)).2,
      hR'v, hs, hr'eq, hqdef, sqDigit]
    split_ifs <;> rfl
  -- the new root
  have hone : IsDigitWord (digitsToBits [q]) :=
    isDigitWord_digitsToBits (by intro x hx; simp at hx; omega)
  have honev : wordVal (digitsToBits [q]) = q := by
    rw [wordVal_digitsToBits (by intro x hx; simp at hx; omega)]
    rfl
  have hA1w : IsDigitWord (addW (pair (aCar v) (aCar v))) := by
    rw [hCar]; exact isDigitWord_addW hSw hSw
  have hA1v : wordVal (addW (pair (aCar v) (aCar v))) = 2 * digitVal sd := by
    rw [hCar, wordVal_addW hSw hSw, hSwv]; ring
  have hA2w : IsDigitWord (addW (pair (addW (pair (aCar v) (aCar v))) (digitsToBits [q]))) :=
    isDigitWord_addW hA1w hone
  have hA2v : wordVal (addW (pair (addW (pair (aCar v) (aCar v))) (digitsToBits [q])))
      = 2 * Nat.sqrt p + q := by
    rw [wordVal_addW hA1w hone, hA1v, honev, hs]
  have hrec := sqrt_rec p d hd
  rw [← hqdef] at hrec
  have hsqrt : Nat.sqrt (4 * p + d) = 2 * Nat.sqrt p + q := hrec.1
  have hA2lt : wordVal (addW (pair (addW (pair (aCar v) (aCar v))) (digitsToBits [q])))
      < 4 ^ m := by
    rw [hA2v, ← hsqrt]
    have := Nat.sqrt_le' (4 * p + d)
    have h2 : Nat.sqrt (4 * p + d) ≤ 4 * p + d := Nat.sqrt_le_self _
    omega
  obtain ⟨sd', hsd'4, hsd'l, hsd'v, hsd'eq⟩ := take_spec hW hA2w hA2lt
  -- the new remainder
  have hRw : IsDigitWord (subW (pair (qRp v) (prodQ q (aCar v)))) :=
    isDigitWord_subW hR'w (hP q hq4).1
  have hRv : wordVal (subW (pair (qRp v) (prodQ q (aCar v))))
      = (4 * p + d) - Nat.sqrt (4 * p + d) * Nat.sqrt (4 * p + d) := by
    rw [wordVal_subW hR'w (hP q hq4).1, hR'v, (hP q hq4).2, hs, hr'eq]
    exact hrec.2.symm ▸ rfl
  have hRlt : wordVal (subW (pair (qRp v) (prodQ q (aCar v)))) < 4 ^ m := by
    rw [hRv]; omega
  obtain ⟨rd', hrd'4, hrd'l, hrd'v, hrd'eq⟩ := take_spec hW hRw hRlt
  refine ⟨sd', rd', hsd'4, hrd'4, hsd'l, hrd'l, ?_, ?_, ?_⟩
  · rw [hsd'v, hA2v, hsqrt]
  · rw [hrd'v, hRv]
  · rw [hchain, qBranch, hBB, hsd'eq, hrd'eq, hqRest]

private lemma sqStep_nil {v : List Bool} (h : aA v = []) : sqStep v = v := by
  rw [sqStep, h]
  exact selectHead_emptyFlag_nil _ _

private lemma sqStep_iterate_nil {v : List Bool} (h : aA v = []) :
    ∀ j : ℕ, sqStep^[j] v = v
  | 0 => rfl
  | (j + 1) => by rw [Function.iterate_succ_apply, sqStep_nil h, sqStep_iterate_nil h j]

/-- **The square-root loop, run to completion.**

Proof kind: `P` proved.  Provenance: (a) `sqStep_one`. -/
private lemma sqStep_iterate {m : ℕ} {W : List Bool} (hW : W.length = 3 * m) :
    ∀ (ds : List ℕ), (∀ x ∈ ds, x < 4) →
    ∀ (p : ℕ) (sd rd : List ℕ), (∀ x ∈ sd, x < 4) → (∀ x ∈ rd, x < 4) →
      digitVal sd = Nat.sqrt p → digitVal rd = p - Nat.sqrt p * Nat.sqrt p →
      p * 4 ^ ds.length + digitVal ds < 4 ^ m →
    ∃ sd' rd' : List ℕ, (∀ x ∈ sd', x < 4) ∧ (∀ x ∈ rd', x < 4) ∧
      digitVal sd' = Nat.sqrt (p * 4 ^ ds.length + digitVal ds) ∧
      digitVal rd' = (p * 4 ^ ds.length + digitVal ds)
        - Nat.sqrt (p * 4 ^ ds.length + digitVal ds)
          * Nat.sqrt (p * 4 ^ ds.length + digitVal ds) ∧
      sqStep^[ds.length]
          (pair (pair (digitsToBits sd) (digitsToBits rd)) (pair (digitsToBits ds) W))
        = pair (pair (digitsToBits sd') (digitsToBits rd')) (pair [] W) := by
  intro ds
  induction ds using List.reverseRecOn with
  | nil =>
      intro _ p sd rd hsd hrd hs hr _
      exact ⟨sd, rd, hsd, hrd, by simpa using hs, by simpa using hr, by simp⟩
  | append_singleton ds₀ d ih =>
      intro hall p sd rd hsd hrd hs hr hcap
      have hd : d < 4 := hall d (by simp)
      have hds₀ : ∀ x ∈ ds₀, x < 4 := fun x hx => hall x (by simp [hx])
      have hlen : (ds₀ ++ [d]).length = ds₀.length + 1 := by simp
      have hkey : p * 4 ^ (ds₀ ++ [d]).length + digitVal (ds₀ ++ [d])
          = (4 * p + d) * 4 ^ ds₀.length + digitVal ds₀ := by
        rw [hlen, digitVal_append_singleton, pow_succ]
        ring
      rw [hkey] at hcap ⊢
      have hpos : 0 < 4 ^ ds₀.length := Nat.pos_of_neZero _
      have hle : 4 * p + d ≤ (4 * p + d) * 4 ^ ds₀.length :=
        Nat.le_mul_of_pos_right _ hpos
      obtain ⟨sd₁, rd₁, hsd₁, hrd₁, _, _, hs₁, hr₁, hstep⟩ :=
        sqStep_one (ds₀ := ds₀) hW hd hsd hrd hs hr (by omega)
      obtain ⟨sd', rd', hsd', hrd', hsv, hrv, hiter⟩ :=
        ih hds₀ (4 * p + d) sd₁ rd₁ hsd₁ hrd₁ hs₁ hr₁ hcap
      refine ⟨sd', rd', hsd', hrd', hsv, hrv, ?_⟩
      rw [hlen, Function.iterate_succ_apply, hstep, hiter]

/-- **`sqrtRemW` is correct.**  It returns the integer square root and the remainder of a
digit word, both again digit words.

Proof kind: `P` proved.  Provenance: (a) `sqStep_iterate`. -/
lemma sqrtRemW_spec {w : List Bool} (hw : IsDigitWord w) :
    ∃ s r : List Bool, sqrtRemW w = pair s r ∧ IsDigitWord s ∧ IsDigitWord r ∧
      wordVal s = Nat.sqrt (wordVal w) ∧
      wordVal r = wordVal w - (Nat.sqrt (wordVal w)) ^ 2 := by
  obtain ⟨ds, hds, rfl⟩ := hw
  set k := ds.length with hk
  have hwlen : (digitsToBits ds).length = 3 * k := length_digitsToBits ds
  have hW : (digitsToBits ds ++ three).length = 3 * (k + 1) := by
    rw [List.length_append, hwlen]
    simp [three]
    omega
  have hcap : 0 * 4 ^ ds.length + digitVal ds < 4 ^ (k + 1) := by
    have h1 : digitVal ds < 4 ^ k := digitVal_lt ds hds
    have h2 : (4 : ℕ) ^ k ≤ 4 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨sd', rd', hsd', hrd', hsv, hrv, hiter⟩ :=
    sqStep_iterate hW ds hds 0 [] [] (by simp) (by simp) (by simp) (by simp) hcap
  have hinit : sqInit (digitsToBits ds)
      = pair (pair (digitsToBits []) (digitsToBits [])) (pair (digitsToBits ds)
          (digitsToBits ds ++ three)) := by
    rw [sqInit]
    simp
  have hrul : (addRuler (digitsToBits ds)).length = (2 * k + 1) + k := by
    simp [addRuler, hwlen]
    omega
  have hfin : aA (pair (pair (digitsToBits sd') (digitsToBits rd'))
      (pair ([] : List Bool) (digitsToBits ds ++ three))) = [] := by
    simp [aA]
  have hcore : sqCore (digitsToBits ds)
      = pair (pair (digitsToBits sd') (digitsToBits rd'))
        (pair [] (digitsToBits ds ++ three)) := by
    rw [sqCore, hrul, Function.iterate_add_apply, hinit, hiter,
      sqStep_iterate_nil hfin]
  refine ⟨digitsToBits sd', digitsToBits rd', ?_, isDigitWord_digitsToBits hsd',
    isDigitWord_digitsToBits hrd', ?_, ?_⟩
  · rw [sqrtRemW, hcore]
    simp [aCar, aOut]
  · rw [wordVal_digitsToBits hsd', wordVal_digitsToBits hds, hsv]
    simp
  · rw [wordVal_digitsToBits hrd', wordVal_digitsToBits hds, hrv, sq]
    simp

/-! ## Unpairing

`Nat.unpair` is a case split on the square root and the remainder, both of which
`sqrtRemW` already carries; no squaring is needed. -/

private lemma sqrtFst_mem_FP : (fun w => fstBlock (sqrtRemW w)) ∈ FP := by
  simpa [Function.comp_def] using mem_FP_comp sqrtRemW_mem_FP fstBlock_mem_FP

private lemma sqrtSnd_mem_FP : (fun w => sndBlock (sqrtRemW w)) ∈ FP := by
  simpa [Function.comp_def] using mem_FP_comp sqrtRemW_mem_FP sndBlock_mem_FP

/-- The first component of `Nat.unpair`, on a digit word. -/
def unpairFstW (w : List Bool) : List Bool :=
  selectHead (gtFlagW (fstBlock (sqrtRemW w)) (sndBlock (sqrtRemW w)))
    (sndBlock (sqrtRemW w)) (fstBlock (sqrtRemW w))

/-- The second component of `Nat.unpair`, on a digit word. -/
def unpairSndW (w : List Bool) : List Bool :=
  selectHead (gtFlagW (fstBlock (sqrtRemW w)) (sndBlock (sqrtRemW w)))
    (fstBlock (sqrtRemW w))
    (subW (pair (sndBlock (sqrtRemW w)) (fstBlock (sqrtRemW w))))

private lemma gtFlagSq_mem_FP :
    (fun w => gtFlagW (fstBlock (sqrtRemW w)) (sndBlock (sqrtRemW w))) ∈ FP :=
  emptyFlag_mem_FP (leWFn_mem_FP sqrtFst_mem_FP sqrtSnd_mem_FP)

lemma unpairFstW_mem_FP : unpairFstW ∈ FP :=
  selectHeadFn_mem_FP gtFlagSq_mem_FP sqrtSnd_mem_FP sqrtFst_mem_FP

lemma unpairSndW_mem_FP : unpairSndW ∈ FP :=
  selectHeadFn_mem_FP gtFlagSq_mem_FP sqrtFst_mem_FP
    (subWFn_mem_FP sqrtSnd_mem_FP sqrtFst_mem_FP)

/-- **Unpairing is correct.** The two components `Nat.unpair` computes, read off the
square-root loop, on digit words and with their values specified.

This is the second of the two `Complexity.FP` devices that let the corrected `thm:ifp` drop
the `Recognizable` condition of the restricted form
(`Construction/Witnesses/CanonicalCodes.lean`; the paper states no such condition) — see
`sqrtRemW_mem_FP` above and
`LogicalInduction/README.md`, *What differs from the paper*. Its sole consumer is
`Construction/Witnesses/FiberTestFP.lean`.

Proof kind: `C` composition.  Provenance: (a) `sqrtRemW_spec`, `subW_spec`,
(b) `Nat.unpair`.
Paper node: `app:ifp` -/
lemma unpairW_spec {w : List Bool} (hw : IsDigitWord w) :
    IsDigitWord (unpairFstW w) ∧ IsDigitWord (unpairSndW w) ∧
      wordVal (unpairFstW w) = (Nat.unpair (wordVal w)).1 ∧
      wordVal (unpairSndW w) = (Nat.unpair (wordVal w)).2 := by
  obtain ⟨S, R, hpair, hSw, hRw, hSv, hRv⟩ := sqrtRemW_spec hw
  set n := wordVal w with hn
  set s := Nat.sqrt n with hs
  have hSv' : wordVal S = s := hSv
  have hRv' : wordVal R = n - s * s := by rw [hRv, sq]
  have hFst : unpairFstW w = if s ≤ n - s * s then S else R := by
    rw [unpairFstW, hpair, fstBlock_pair, sndBlock_pair,
      selectHead_gtFlagW hSw hRw, hSv', hRv']
  have hSnd : unpairSndW w = if s ≤ n - s * s then subW (pair R S) else S := by
    rw [unpairSndW, hpair, fstBlock_pair, sndBlock_pair,
      selectHead_gtFlagW hSw hRw, hSv', hRv']
  have hsub := subW_spec hRw hSw
  have hunpair : Nat.unpair n = if n - s * s < s then (n - s * s, s) else (s, n - s * s - s) := by
    rw [Nat.unpair, hs]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hFst]; split_ifs <;> assumption
  · rw [hSnd]; split_ifs
    · exact hsub.1
    · exact hSw
  · rw [hFst, hunpair]
    by_cases h : s ≤ n - s * s
    · rw [if_pos h, if_neg (by omega)]
      exact hSv'
    · rw [if_neg h, if_pos (by omega)]
      exact hRv'
  · rw [hSnd, hunpair]
    by_cases h : s ≤ n - s * s
    · rw [if_pos h, if_neg (by omega)]
      rw [hsub.2, hRv', hSv']
    · rw [if_neg h, if_pos (by omega)]
      exact hSv'

end LogicalInduction.DigitFP
