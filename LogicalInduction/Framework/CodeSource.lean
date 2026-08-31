import LogicalInduction.Framework.DigitArith
import Mathlib.Data.Nat.Digits.Defs

/-!
# Machine source encodings — the naming a polynomial-time writer can emit

Machines are `Nat.Partrec.Code`.  A trader that *names* a machine must write the name
down, so the naming map has to be one whose output length is controlled by the machine's
syntax (arXiv:1609.03543, §4.11).

The **source encoding** here is the postfix (reverse-Polish) tag stream of the code's
syntax tree — one tag per node, drawn from `1..8` — read as a base-`16` numeral,
most-significant tag first (`sourceNat`).  Since `16 = 4 ^ 2`, its base-4 digit count is
at most `2 * c.size`: **linear in the syntax tree** (`len4_sourceNat_le`).

Decoding is by `ofSource`, a *total* primitive recursive function (`ofSource_primrec`)
inverting `sourceNat` (`ofSource_sourceNat`).  Its cost is metered in peel steps, one per
base-4 digit of the name: `ofSource n` takes exactly `len4 n` steps (`ofSource_peelSteps`),
so decoding a machine name takes at most `2 * c.size` steps (`sourceNat_peelSteps_le`) —
**linear in the source length**.  That is the whole cost claim made here; no `PolyFueled`
or `Complexity.FP` certificate is proved for `ofSource`.

Mathlib's `Encodable.encode : Nat.Partrec.Code → ℕ` fails this.  `encodeCode` emits
`2 * (2 * Nat.pair (encode cf) (encode cg)) + 4` at every `pair`/`comp`/`prec` node, and
`Nat.pair` squares, so the *value* squares once per node.  For the family
`nest 0 = zero`, `nest (n+1) = pair (nest n) zero` — source length `n + 1` nodes on the
spine — the base-4 digit counts of `Encodable.encode (nest n)` are

    0, 2, 4, 8, 16, 33, 67, 134, …

i.e. the encoded *value* is doubly exponential in `n` (and so in the tree size `2 * n + 1`),
and its digit count — the length actually written down — is *exponential* in the tree size.
`sourceNat`'s digit count is linear in it.  `Encodable.encode` is therefore not used for
naming; `sourceNat` is.
-/

namespace LogicalInduction

open Nat.Partrec (Code)

-- Deep `Primrec`/`PolyFueled` compositions over paired inputs loop `whnf` on `Nat.sqrt`
-- (pair/unpair unfolding); keep it opaque throughout (the standard `dd:fuel` safeguard).
attribute [local irreducible] Nat.sqrt

/-! ## Base-16 digit extraction -/

/-- Reading a base-`16` little-endian digit list back out, position by position.  Beyond
the list the quotient has run out and the digit is `0`, which is exactly `getD`'s
default. -/
lemma ofDigits_div_pow_mod {b : ℕ} (hb : 1 < b) {L : List ℕ} (hd : ∀ d ∈ L, d < b)
    (i : ℕ) : Nat.ofDigits b L / b ^ i % b = L.getD i 0 := by
  rcases lt_or_ge i L.length with hi | hi
  · rw [Nat.ofDigits_div_pow_eq_ofDigits_drop i (lt_trans Nat.zero_lt_one hb) L hd,
      List.drop_eq_getElem_cons hi, Nat.ofDigits_cons]
    have hrw : (L[i] : ℕ) + b * Nat.ofDigits b (L.drop (i + 1)) =
        L[i] + Nat.ofDigits b (L.drop (i + 1)) * b := by ring
    rw [hrw, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt (hd _ (L.getElem_mem hi)), List.getD_eq_getElem _ _ hi]
  · have hlt : Nat.ofDigits b L < b ^ i :=
      lt_of_lt_of_le (Nat.ofDigits_lt_base_pow_length hb hd)
        (Nat.pow_le_pow_right (le_of_lt hb) hi)
    rw [Nat.div_eq_of_lt hlt, Nat.zero_mod, List.getD_eq_default _ _ hi]

/-- Base-4 digits of a base-16 numeral: `16 = 4 ^ 2`, so base-16 slot `j / 2` carries
base-4 digits `2 * (j / 2)` and `2 * (j / 2) + 1`. -/
lemma dig4_ofDigits_sixteen {L : List ℕ} (hd : ∀ d ∈ L, d < 16) (j : ℕ) :
    dig4 (Nat.ofDigits 16 L) j = L.getD (j / 2) 0 / 4 ^ (j % 2) % 4 := by
  have hdq : Nat.ofDigits 16 L / 16 ^ (j / 2) % 16 = L.getD (j / 2) 0 :=
    ofDigits_div_pow_mod (by norm_num) hd _
  have hsplit : (4 : ℕ) ^ j = 16 ^ (j / 2) * 4 ^ (j % 2) := by
    have h : j = 2 * (j / 2) + j % 2 := by omega
    calc (4 : ℕ) ^ j = 4 ^ (2 * (j / 2) + j % 2) := by rw [← h]
      _ = (4 ^ 2) ^ (j / 2) * 4 ^ (j % 2) := by rw [pow_add, pow_mul]
      _ = 16 ^ (j / 2) * 4 ^ (j % 2) := by norm_num
  rw [dig4, hsplit, ← Nat.div_div_eq_div_mul, ← hdq]
  set a := Nat.ofDigits 16 L / 16 ^ (j / 2) with ha
  have hr : j % 2 = 0 ∨ j % 2 = 1 := by omega
  rcases hr with hr | hr
  · rw [hr, pow_zero, Nat.div_one, Nat.div_one]
    exact (Nat.mod_mod_of_dvd a (by norm_num)).symm
  · have h1 : a % 16 / 4 = a / 4 % 4 := by
      have := Nat.mod_mul_right_div_self a 4 4
      norm_num at this
      exact this
    rw [hr, pow_one, h1]
    omega

/-! ## Transferring base-16 stream access to `BigDigits` -/

/-- Poly-fueled access to a base-16 tag stream gives poly-fueled base-4 digit access to
the numeral it denotes.  `16 = 4 ^ 2`, so tag `j` occupies base-4 digits `2 * j` and
`2 * j + 1`. -/
lemma BigDigits.ofBase16Digits {L : ℕ → List ℕ} {cl cd : Code}
    (hlen : PolyFueled cl (fun n => (L n).length))
    (hdig : PolyFueled cd (fun z => (L z.unpair.1).getD z.unpair.2 0))
    (hlt : ∀ n j, (L n).getD j 0 < 16) :
    BigDigits (fun n => Nat.ofDigits 16 (L n)) := by
  have hmem : ∀ n, ∀ d ∈ L n, d < 16 := by
    intro n d hd
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hd
    rw [← List.getD_eq_getElem (L n) 0 hi]
    exact hlt n i
  obtain ⟨cdm2, hdm2⟩ := divmodc_polyFueled 2 (by norm_num)
  obtain ⟨cdm4, hdm4⟩ := divmodc_polyFueled 4 (by norm_num)
  -- index `⟨n, j⟩ ↦ ⟨n, j / 2⟩`, then the digit of the base-16 slot
  have hhalf : PolyFueled _ (fun z : ℕ => z.unpair.2 / 2) :=
    (PolyFueled.left.comp (hdm2.comp PolyFueled.right)).of_eq
      (fun z => by simp only [Nat.unpair_pair])
  have hpar : PolyFueled _ (fun z : ℕ => z.unpair.2 % 2) :=
    (PolyFueled.right.comp (hdm2.comp PolyFueled.right)).of_eq
      (fun z => by simp only [Nat.unpair_pair])
  have hslot : PolyFueled _ (fun z : ℕ => (L z.unpair.1).getD (z.unpair.2 / 2) 0) :=
    (hdig.comp (PolyFueled.left.pair hhalf)).of_eq
      (fun z => by simp only [Nat.unpair_pair])
  have hlow : PolyFueled _ (fun z : ℕ => (L z.unpair.1).getD (z.unpair.2 / 2) 0 % 4) :=
    (PolyFueled.right.comp (hdm4.comp hslot)).of_eq
      (fun z => by simp only [Nat.unpair_pair])
  have hhigh : PolyFueled _ (fun z : ℕ => (L z.unpair.1).getD (z.unpair.2 / 2) 0 / 4) :=
    (PolyFueled.left.comp (hdm4.comp hslot)).of_eq
      (fun z => by simp only [Nat.unpair_pair])
  obtain ⟨cdig, hdigit⟩ : ∃ c, PolyFueled c
      (fun z : ℕ => dig4 (Nat.ofDigits 16 (L z.unpair.1)) z.unpair.2) := by
    refine ⟨_, (ifzSel_polyFueled.comp ((hlow.pair hhigh).pair hpar)).of_eq (fun z => ?_)⟩
    simp only [Nat.unpair_pair, ifzSelFn]
    rw [dig4_ofDigits_sixteen (hmem _)]
    by_cases hz : z.unpair.2 % 2 = 0
    · rw [if_pos hz, hz, pow_zero, Nat.div_one]
    · have hz1 : z.unpair.2 % 2 = 1 := by omega
      rw [if_neg hz, hz1, pow_one]
      exact (Nat.mod_eq_of_lt (by have := hlt z.unpair.1 (z.unpair.2 / 2); omega)).symm
  obtain ⟨cm, hcm⟩ := mulc_polyFueled 2
  obtain ⟨clen, hclen⟩ := BigDigits.len_of_digits hdigit (hcm.comp hlen) (fun n => by
    rw [len4_le_iff]
    calc Nat.ofDigits 16 (L n) < 16 ^ (L n).length :=
          Nat.ofDigits_lt_base_pow_length (by norm_num) (hmem n)
      _ = 4 ^ ((L n).length * 2) := by rw [mul_comm, pow_mul]; norm_num)
  exact ⟨_, _, hclen, hdigit⟩


/-! ## Base-`64` digit extraction, and naming a token run

`ofBase16Digits` serves alphabets of fewer than sixteen tags — `Code.sourceNat`'s `1..8`.
The paper's arithmetic *formula* alphabet is `0..18, 20..22`
(`ArithSource.sourceTokens`), which does not fit, so the same theory runs once more at
`64 = 4 ^ 3`: one base-`64` digit per emitted token.

`tokenListNat` is the resulting naming map for a token run.  It appends the sentinel
`63` — a value outside every alphabet used here — so that the top digit is never `0` and
therefore never lost to truncation; that makes the map injective and gives the decoder a
terminator to stop at.  Its base-`4` digit count is `3 * (n + 1)` for a run of `n`
tokens: **linear in the written text**, which is the whole point.  Compare the Godel code
of the formula that text denotes, which pairs at every node and is doubly exponential. -/

/-- Base-4 digits of a base-64 numeral: `64 = 4 ^ 3`, so base-64 slot `j / 3` carries
base-4 digits `3 * (j / 3)`, `3 * (j / 3) + 1` and `3 * (j / 3) + 2`. -/
lemma dig4_ofDigits_sixtyFour {L : List ℕ} (hd : ∀ d ∈ L, d < 64) (j : ℕ) :
    dig4 (Nat.ofDigits 64 L) j = L.getD (j / 3) 0 / 4 ^ (j % 3) % 4 := by
  have hdq : Nat.ofDigits 64 L / 64 ^ (j / 3) % 64 = L.getD (j / 3) 0 :=
    ofDigits_div_pow_mod (by norm_num) hd _
  have hsplit : (4 : ℕ) ^ j = 64 ^ (j / 3) * 4 ^ (j % 3) := by
    have h : j = 3 * (j / 3) + j % 3 := by omega
    calc (4 : ℕ) ^ j = 4 ^ (3 * (j / 3) + j % 3) := by rw [← h]
      _ = (4 ^ 3) ^ (j / 3) * 4 ^ (j % 3) := by rw [pow_add, pow_mul]
      _ = 64 ^ (j / 3) * 4 ^ (j % 3) := by norm_num
  rw [dig4, hsplit, ← Nat.div_div_eq_div_mul, ← hdq]
  set a := Nat.ofDigits 64 L / 64 ^ (j / 3) with ha
  have hr : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
  rcases hr with hr | hr | hr
  · rw [hr, pow_zero, Nat.div_one, Nat.div_one]
    exact (Nat.mod_mod_of_dvd a (by norm_num)).symm
  · have h1 : a % 64 / 4 = a / 4 % 16 := by
      have := Nat.mod_mul_right_div_self a 4 16
      norm_num at this
      exact this
    rw [hr, pow_one, h1]
    exact (Nat.mod_mod_of_dvd (a / 4) (by norm_num)).symm
  · have h2 : a % 64 / 16 = a / 16 % 4 := by
      have := Nat.mod_mul_right_div_self a 16 4
      norm_num at this
      exact this
    have h16 : (4 : ℕ) ^ (2 : ℕ) = 16 := by norm_num
    rw [hr, h16, h2, Nat.mod_mod_of_dvd (a / 16) (by norm_num)]

/-- Poly-fueled access to a base-64 tag stream gives poly-fueled base-4 digit access to
the numeral it denotes — the base-`64` twin of `BigDigits.ofBase16Digits`. -/
lemma BigDigits.ofBase64Digits {L : ℕ → List ℕ} {cl cd : Code}
    (hlen : PolyFueled cl (fun n => (L n).length))
    (hdig : PolyFueled cd (fun z => (L z.unpair.1).getD z.unpair.2 0))
    (hlt : ∀ n j, (L n).getD j 0 < 64) :
    BigDigits (fun n => Nat.ofDigits 64 (L n)) := by
  have hmem : ∀ n, ∀ d ∈ L n, d < 64 := by
    intro n d hd
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hd
    rw [← List.getD_eq_getElem (L n) 0 hi]
    exact hlt n i
  obtain ⟨cdm3, hdm3⟩ := divmodc_polyFueled 3 (by norm_num)
  obtain ⟨cdm4, hdm4⟩ := divmodc_polyFueled 4 (by norm_num)
  obtain ⟨cdm16, hdm16⟩ := divmodc_polyFueled 16 (by norm_num)
  -- index `⟨n, j⟩ ↦ ⟨n, j / 3⟩`, then the three base-4 digits of the base-64 slot
  have hthird : PolyFueled _ (fun z : ℕ => z.unpair.2 / 3) :=
    (PolyFueled.left.comp (hdm3.comp PolyFueled.right)).of_eq
      (fun z => by simp only [Nat.unpair_pair])
  have hres : PolyFueled _ (fun z : ℕ => z.unpair.2 % 3) :=
    (PolyFueled.right.comp (hdm3.comp PolyFueled.right)).of_eq
      (fun z => by simp only [Nat.unpair_pair])
  have hslot : PolyFueled _ (fun z : ℕ => (L z.unpair.1).getD (z.unpair.2 / 3) 0) :=
    (hdig.comp (PolyFueled.left.pair hthird)).of_eq
      (fun z => by simp only [Nat.unpair_pair])
  have hd0 : PolyFueled _ (fun z : ℕ => (L z.unpair.1).getD (z.unpair.2 / 3) 0 % 4) :=
    (PolyFueled.right.comp (hdm4.comp hslot)).of_eq
      (fun z => by simp only [Nat.unpair_pair])
  have hd1 : PolyFueled _ (fun z : ℕ => (L z.unpair.1).getD (z.unpair.2 / 3) 0 / 4 % 4) :=
    (PolyFueled.right.comp (hdm4.comp (PolyFueled.left.comp (hdm4.comp hslot)))).of_eq
      (fun z => by simp only [Nat.unpair_pair])
  have hd2 : PolyFueled _ (fun z : ℕ => (L z.unpair.1).getD (z.unpair.2 / 3) 0 / 16 % 4) :=
    (PolyFueled.right.comp (hdm4.comp (PolyFueled.left.comp (hdm16.comp hslot)))).of_eq
      (fun z => by simp only [Nat.unpair_pair])
  have hsub : PolyFueled _ (fun z : ℕ => z.unpair.2 % 3 - 1) :=
    (subc_polyFueled.comp (hres.pair (PolyFueled.const 1))).of_eq
      (fun z => by simp only [Nat.unpair_pair])
  obtain ⟨cdig, hdigit⟩ : ∃ c, PolyFueled c
      (fun z : ℕ => dig4 (Nat.ofDigits 64 (L z.unpair.1)) z.unpair.2) := by
    refine ⟨_, (ifzSel_polyFueled.comp
      ((hd0.pair (ifzSel_polyFueled.comp ((hd1.pair hd2).pair hsub))).pair hres)).of_eq
      (fun z => ?_)⟩
    simp only [Nat.unpair_pair, ifzSelFn]
    rw [dig4_ofDigits_sixtyFour (hmem _)]
    have hr : z.unpair.2 % 3 = 0 ∨ z.unpair.2 % 3 = 1 ∨ z.unpair.2 % 3 = 2 := by omega
    rcases hr with hr | hr | hr
    · rw [if_pos hr, hr, pow_zero, Nat.div_one]
    · rw [if_neg (by omega : ¬ z.unpair.2 % 3 = 0), hr]
      norm_num
    · rw [if_neg (by omega : ¬ z.unpair.2 % 3 = 0), hr]
      norm_num
  obtain ⟨cm, hcm⟩ := mulc_polyFueled 3
  obtain ⟨clen, hclen⟩ := BigDigits.len_of_digits hdigit (hcm.comp hlen) (fun n => by
    rw [len4_le_iff]
    calc Nat.ofDigits 64 (L n) < 64 ^ (L n).length :=
          Nat.ofDigits_lt_base_pow_length (by norm_num) (hmem n)
      _ = 4 ^ ((L n).length * 3) := by rw [mul_comm, pow_mul]; norm_num)
  exact ⟨_, _, hclen, hdigit⟩

/-- **The name of a token run**: one base-`64` digit per token, most significant last,
closed by the sentinel `63`. -/
def tokenListNat (ts : List ℕ) : ℕ := Nat.ofDigits 64 (ts ++ [63])

/-- Below its own length a list is unchanged by appending. -/
private lemma getD_append_of_lt {l l' : List ℕ} {i : ℕ} (hi : i < l.length) :
    (l ++ l').getD i 0 = l.getD i 0 := by
  have hi' : i < (l ++ l').length := by
    simp only [List.length_append]; omega
  rw [List.getD_eq_getElem _ _ hi', List.getD_eq_getElem _ _ hi,
    List.getElem_append_left hi]

/-- At its own length, a list with one element appended shows that element. -/
private lemma getD_append_singleton_length {l : List ℕ} {d : ℕ} :
    (l ++ [d]).getD l.length 0 = d := by
  have hi : l.length < (l ++ [d]).length := by
    simp only [List.length_append, List.length_singleton]; omega
  rw [List.getD_eq_getElem _ _ hi]
  simp

/-- Reading the name back out, digit by digit. -/
lemma tokenListNat_digit {ts : List ℕ} (hts : ∀ t ∈ ts, t < 63) (i : ℕ) :
    tokenListNat ts / 64 ^ i % 64 = (ts ++ [63]).getD i 0 := by
  unfold tokenListNat
  refine ofDigits_div_pow_mod (b := 64) (by norm_num) (fun d hd => ?_) i
  rcases List.mem_append.mp hd with h | h
  · exact lt_trans (hts d h) (by norm_num)
  · simp only [List.mem_singleton] at h
    omega

/-- Below the sentinel the name reproduces the run. -/
lemma tokenListNat_digit_lt {ts : List ℕ} (hts : ∀ t ∈ ts, t < 63) {i : ℕ}
    (hi : i < ts.length) : tokenListNat ts / 64 ^ i % 64 = ts.getD i 0 := by
  rw [tokenListNat_digit hts, getD_append_of_lt hi]

/-- At the run's length the name shows the sentinel. -/
lemma tokenListNat_digit_length {ts : List ℕ} (hts : ∀ t ∈ ts, t < 63) :
    tokenListNat ts / 64 ^ ts.length % 64 = 63 := by
  rw [tokenListNat_digit hts, getD_append_singleton_length]

/-- The run is shorter than its own name, so a search bounded by the name is long
enough to find the sentinel. -/
lemma length_lt_tokenListNat (ts : List ℕ) : ts.length < tokenListNat ts := by
  have h1 : ts.length < 2 ^ ts.length := Nat.lt_two_pow_self
  have h2 : (2 : ℕ) ^ ts.length ≤ 64 ^ ts.length := Nat.pow_le_pow_left (by norm_num) _
  have h3 : (64 : ℕ) ^ ts.length * 63 ≤ tokenListNat ts := by
    unfold tokenListNat
    rw [Nat.ofDigits_append]
    simp only [Nat.ofDigits_singleton]
    exact Nat.le_add_left _ _
  omega

/-- **The naming map is injective** on runs over an alphabet below the sentinel: distinct
written texts get distinct names, with no appeal to what they denote. -/
lemma tokenListNat_injective {ts us : List ℕ} (hts : ∀ t ∈ ts, t < 63)
    (hus : ∀ t ∈ us, t < 63) (h : tokenListNat ts = tokenListNat us) : ts = us := by
  have key : ∀ i, (ts ++ [63]).getD i 0 = (us ++ [63]).getD i 0 := fun i => by
    rw [← tokenListNat_digit hts, ← tokenListNat_digit hus, h]
  have hlen : ts.length = us.length := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have h1 := key ts.length
      rw [getD_append_singleton_length, getD_append_of_lt hlt] at h1
      have hmem : us.getD ts.length 0 ∈ us := by
        rw [List.getD_eq_getElem _ _ hlt]
        exact us.getElem_mem hlt
      have := hus _ hmem
      omega
    · have h1 := key us.length
      rw [getD_append_singleton_length, getD_append_of_lt hlt] at h1
      have hmem : ts.getD us.length 0 ∈ ts := by
        rw [List.getD_eq_getElem _ _ hlt]
        exact ts.getElem_mem hlt
      have := hts _ hmem
      omega
  refine List.ext_getElem hlen (fun i h₁ h₂ => ?_)
  have hi := key i
  rw [getD_append_of_lt h₁, getD_append_of_lt h₂,
    List.getD_eq_getElem _ _ h₁, List.getD_eq_getElem _ _ h₂] at hi
  exact hi

/-- **The naming map is primitive recursive.**  Mathlib has no `Primrec` fact about
`Nat.ofDigits` (verified absent), so this goes through the `foldr` form directly, in the
shape `Primrec.list_foldr` accepts.  Consumed by `combineSourceNats_primrec`, which names
a spliced day-window run. -/
lemma tokenListNat_primrec : Primrec tokenListNat := by
  have hfold : ∀ l : List ℕ,
      Nat.ofDigits 64 l = l.foldr (fun d r => d + 64 * r) 0 := by
    intro l
    induction l with
    | nil => rfl
    | cons d l ih => rw [Nat.ofDigits_cons, ih]; rfl
  have hlist : Primrec fun ts : List ℕ => ts ++ [63] :=
    Primrec.list_append.comp Primrec.id (Primrec.const [63])
  have hstep : Primrec₂ fun (_ : List ℕ) (p : ℕ × ℕ) => p.1 + 64 * p.2 :=
    show Primrec fun x : List ℕ × (ℕ × ℕ) => x.2.1 + 64 * x.2.2 from
      Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.nat_mul.comp (Primrec.const 64) (Primrec.snd.comp Primrec.snd))
  exact (Primrec.list_foldr hlist (Primrec.const 0) hstep).of_eq fun ts => by
    rw [tokenListNat, hfold]


/-- **The base-16 twin of `BigDigits.ofTokenListNat`**: a segment stream whose tokens are
all below `16` names a numeral with poly-fueled base-4 digit access.

Unlike the base-64 token-run map there is no sentinel here — `Code.sourceTags` never emits
the tag `0`, so the leading digit of a source numeral is already nonzero and nothing is
lost to truncation.  All this lemma does is clamp the stream's emitter to `0` outside the
emitted range (via `ifzSel` on `lenFn n - i`) and hand the result to
`BigDigits.ofBase16Digits`.

Kind C (composition).  Provenance: (a) derived in-project from `BigDigits.ofBase16Digits`
and the `PolySegStream` interface, following `BigDigits.ofTokenListNat` verbatim modulo
the base and the missing sentinel. -/
lemma BigDigits.ofBase16PolySegStream {L : ℕ → List ℕ} (h : PolySegStream L)
    (hlt : ∀ n, ∀ d ∈ L n, d < 16) : BigDigits (fun n => Nat.ofDigits 16 (L n)) := by
  obtain ⟨ct, cl, tokenFn, lenFn, htok, hlen, hslen, hget⟩ := h
  have hlenL : PolyFueled _ (fun n => (L n).length) :=
    hlen.of_eq (fun n => (hslen n).symm)
  have hlenN : PolyFueled _ (fun z : ℕ => lenFn z.unpair.1) := hlen.comp PolyFueled.left
  have ha : PolyFueled _ (fun z : ℕ => lenFn z.unpair.1 - z.unpair.2) :=
    (subc_polyFueled.comp (hlenN.pair PolyFueled.right)).of_eq
      (fun z => by simp only [Nat.unpair_pair])
  have hdig : PolyFueled _ (fun z : ℕ => (L z.unpair.1).getD z.unpair.2 0) :=
    (ifzSel_polyFueled.comp (((PolyFueled.const 0).pair htok).pair ha)).of_eq (fun z => by
      simp only [Nat.unpair_pair, ifzSelFn]
      have hlz : (L z.unpair.1).length = lenFn z.unpair.1 := hslen _
      rcases lt_or_ge z.unpair.2 (lenFn z.unpair.1) with hj | hj
      · rw [if_neg (by omega)]
        have hg := hget z.unpair.1 z.unpair.2 hj
        rwa [Nat.pair_unpair] at hg
      · rw [if_pos (by omega)]
        exact (List.getD_eq_default _ _ (by omega)).symm)
  have hbound : ∀ n j, (L n).getD j 0 < 16 := by
    intro n j
    rcases lt_or_ge j (L n).length with hj | hj
    · rw [List.getD_eq_getElem _ _ hj]
      exact hlt n _ ((L n).getElem_mem hj)
    · rw [List.getD_eq_default _ _ hj]
      norm_num
  exact BigDigits.ofBase16Digits hlenL hdig hbound

/-- **The delivery interface**: an efficiently emitted token run is efficiently *named*.
This is the write-out bridge the paper's `def:ec` needs for objects presented by source
text rather than by Godel code. -/
lemma BigDigits.ofTokenListNat {L : ℕ → List ℕ} (h : PolySegStream L)
    (hlt : ∀ n, ∀ t ∈ L n, t < 63) : BigDigits (fun n => tokenListNat (L n)) := by
  obtain ⟨ct, cl, tokenFn, lenFn, htok, hlen, hslen, hget⟩ := h
  have hlenM : PolyFueled _ (fun n => (L n ++ [63]).length) :=
    hlen.succ_comp.of_eq (fun n => by
      simp only [List.length_append, List.length_singleton, hslen n])
  have hlenN : PolyFueled _ (fun z : ℕ => lenFn z.unpair.1) := hlen.comp PolyFueled.left
  have ha : PolyFueled _ (fun z : ℕ => lenFn z.unpair.1 - z.unpair.2) :=
    (subc_polyFueled.comp (hlenN.pair PolyFueled.right)).of_eq
      (fun z => by simp only [Nat.unpair_pair])
  have hb : PolyFueled _ (fun z : ℕ => z.unpair.2 - lenFn z.unpair.1) :=
    (subc_polyFueled.comp (PolyFueled.right.pair hlenN)).of_eq
      (fun z => by simp only [Nat.unpair_pair])
  have hinner := ifzSel_polyFueled.comp
    (((PolyFueled.const 63).pair (PolyFueled.const 0)).pair hb)
  have houter := ifzSel_polyFueled.comp ((hinner.pair htok).pair ha)
  have hdigM : PolyFueled _ (fun z : ℕ => (L z.unpair.1 ++ [63]).getD z.unpair.2 0) :=
    houter.of_eq (fun z => by
    simp only [Nat.unpair_pair, ifzSelFn]
    have hlz : (L z.unpair.1).length = lenFn z.unpair.1 := hslen _
    rcases lt_trichotomy z.unpair.2 (lenFn z.unpair.1) with hj | hj | hj
    · have htz : tokenFn z = (L z.unpair.1).getD z.unpair.2 0 := by
        have hg := hget z.unpair.1 z.unpair.2 hj
        rwa [Nat.pair_unpair] at hg
      rw [if_neg (by omega), htz,
        getD_append_of_lt (by omega : z.unpair.2 < (L z.unpair.1).length)]
    · rw [if_pos (by omega), if_pos (by omega), hj, ← hlz,
        getD_append_singleton_length]
    · rw [if_pos (by omega), if_neg (by omega),
        List.getD_eq_default _ _ (by
          simp only [List.length_append, List.length_singleton]; omega)])
  have hbound : ∀ n j, (L n ++ [63]).getD j 0 < 64 := by
    intro n j
    rcases lt_or_ge j (L n ++ [63]).length with hj | hj
    · rw [List.getD_eq_getElem _ _ hj]
      rcases List.mem_append.mp ((L n ++ [63]).getElem_mem hj) with hm | hm
      · exact lt_trans (hlt n _ hm) (by norm_num)
      · simp only [List.mem_singleton] at hm
        omega
    · rw [List.getD_eq_default _ _ hj]
      norm_num
  have hbig : BigDigits (fun n => Nat.ofDigits 64 (L n ++ [63])) :=
    BigDigits.ofBase64Digits (L := fun n => L n ++ [63]) hlenM hdigM hbound
  exact hbig.of_eq (fun n => rfl)

end LogicalInduction

namespace Nat.Partrec.Code

open LogicalInduction

attribute [local irreducible] Nat.sqrt

/-! ## The tag stream -/

/-- Postfix (reverse-Polish) tag stream of a code's syntax tree: one tag per node,
`1 = zero, 2 = succ, 3 = left, 4 = right, 5 = pair, 6 = comp, 7 = prec, 8 = rfind'`.
Tag `0` is reserved (never emitted) so that it can act as a no-op pad. -/
def sourceTags : Code → List ℕ
  | .zero => [1]
  | .succ => [2]
  | .left => [3]
  | .right => [4]
  | .pair a b => sourceTags a ++ sourceTags b ++ [5]
  | .comp a b => sourceTags a ++ sourceTags b ++ [6]
  | .prec a b => sourceTags a ++ sourceTags b ++ [7]
  | .rfind' a => sourceTags a ++ [8]

/-- Number of nodes in a code's syntax tree. -/
def size : Code → ℕ
  | .zero => 1
  | .succ => 1
  | .left => 1
  | .right => 1
  | .pair a b => a.size + b.size + 1
  | .comp a b => a.size + b.size + 1
  | .prec a b => a.size + b.size + 1
  | .rfind' a => a.size + 1

lemma sourceTags_ne_nil (c : Code) : sourceTags c ≠ [] := by
  cases c <;> simp [sourceTags]

lemma sourceTags_lt_16 (c : Code) : ∀ t ∈ sourceTags c, 1 ≤ t ∧ t < 16 := by
  induction c with
  | zero | succ | left | right =>
      intro t ht; simp only [sourceTags, List.mem_singleton] at ht; omega
  | pair a b iha ihb | comp a b iha ihb | prec a b iha ihb =>
      intro t ht
      simp only [sourceTags, List.mem_append, List.mem_singleton] at ht
      rcases ht with (h | h) | h
      · exact iha t h
      · exact ihb t h
      · omega
  | rfind' a iha =>
      intro t ht
      simp only [sourceTags, List.mem_append, List.mem_singleton] at ht
      rcases ht with h | h
      · exact iha t h
      · omega

/-- The tag stream has one tag per node: its length is the size of the syntax tree. -/
lemma sourceTags_length (c : Code) : (sourceTags c).length = c.size := by
  induction c with
  | zero | succ | left | right => simp [sourceTags, size]
  | pair a b iha ihb | comp a b iha ihb | prec a b iha ihb =>
      simp only [sourceTags, size, List.length_append, iha, ihb, List.length_singleton]
  | rfind' a iha => simp [sourceTags, size, iha]

lemma size_pos (c : Code) : 0 < c.size := by
  cases c <;> simp [size]

/-! ## `sourceNat` -/

/-- **The source encoding of a machine.**  The tag stream read as a base-16 numeral,
most-significant tag first.  Its base-4 digit count is at most `2 * c.size`, i.e. LINEAR
in the syntax tree — unlike `Encodable.encode`, whose value squares at every
`pair`/`comp`/`prec` node.  This is the naming a polynomial-time writer can emit. -/
def sourceNat (c : Code) : ℕ := Nat.ofDigits 16 (sourceTags c).reverse

lemma sourceTags_reverse_lt_16 (c : Code) :
    ∀ d ∈ (sourceTags c).reverse, d < 16 := by
  intro d hd
  exact (sourceTags_lt_16 c d (List.mem_reverse.mp hd)).2

lemma sourceNat_lt (c : Code) : c.sourceNat < 16 ^ c.size := by
  have h := Nat.ofDigits_lt_base_pow_length (b := 16) (l := (sourceTags c).reverse)
    (by norm_num) (sourceTags_reverse_lt_16 c)
  simpa [sourceNat, sourceTags_length] using h

/-- The leading tag is nonzero, so the encoding is at least `16 ^ (size - 1)`. -/
lemma pow_pred_le_sourceNat (c : Code) : 16 ^ (c.size - 1) ≤ c.sourceNat := by
  set L := (sourceTags c).reverse with hL
  have hlen : L.length = c.size := by rw [hL, List.length_reverse, sourceTags_length]
  have hpos : 0 < c.size := size_pos c
  have hlt : c.size - 1 < L.length := by omega
  have hne : L.getD (c.size - 1) 0 ≠ 0 := by
    rw [List.getD_eq_getElem _ _ hlt]
    have hmem : L[c.size - 1] ∈ L := L.getElem_mem hlt
    have hmem' : L[c.size - 1] ∈ (sourceTags c).reverse := by rw [← hL]; exact hmem
    have := sourceTags_lt_16 c L[c.size - 1] (List.mem_reverse.mp hmem')
    omega
  have hmod : c.sourceNat / 16 ^ (c.size - 1) % 16 = L.getD (c.size - 1) 0 :=
    ofDigits_div_pow_mod (by norm_num) (sourceTags_reverse_lt_16 c) _
  have hq : 1 ≤ c.sourceNat / 16 ^ (c.size - 1) := by
    rcases Nat.eq_zero_or_pos (c.sourceNat / 16 ^ (c.size - 1)) with h | h
    · rw [h] at hmod; simp at hmod; exact absurd hmod.symm hne
    · exact h
  exact (Nat.one_le_div_iff (by positivity)).mp hq

lemma sourceNat_pos (c : Code) : 0 < c.sourceNat :=
  lt_of_lt_of_le (by positivity) (pow_pred_le_sourceNat c)

/-- **Linearity.**  The base-4 length of the source encoding is at most twice the number
of nodes. -/
lemma len4_sourceNat_le (c : Code) : len4 c.sourceNat ≤ 2 * c.size := by
  rw [len4_le_iff]
  calc c.sourceNat < 16 ^ c.size := sourceNat_lt c
    _ = 4 ^ (2 * c.size) := by rw [pow_mul]; norm_num

/-- The tag stream fits inside the base-4 length of the encoding: `16 ^ (size - 1) ≤
sourceNat` forces `2 * (size - 1) < len4 sourceNat`, and `size ≥ 1` closes the gap.  This
is what makes `len4 n` enough fuel for the decoder. -/
lemma size_le_len4_sourceNat (c : Code) : c.size ≤ len4 c.sourceNat := by
  have hpos : 0 < c.size := size_pos c
  have hpow : (4 : ℕ) ^ (2 * (c.size - 1)) ≤ c.sourceNat := by
    calc (4 : ℕ) ^ (2 * (c.size - 1)) = 16 ^ (c.size - 1) := by rw [pow_mul]; norm_num
      _ ≤ c.sourceNat := pow_pred_le_sourceNat c
  have := (lt_len4_iff c.sourceNat (2 * (c.size - 1))).mpr hpow
  omega

lemma size_le_sourceNat (c : Code) : c.size ≤ c.sourceNat := by
  refine le_trans ?_ (pow_pred_le_sourceNat c)
  have hpos : 0 < c.size := size_pos c
  have h2 : c.size - 1 < 2 ^ (c.size - 1) := Nat.lt_two_pow_self
  have h16 : (2 : ℕ) ^ (c.size - 1) ≤ 16 ^ (c.size - 1) :=
    Nat.pow_le_pow_left (by norm_num) _
  omega

/-! ## The decoder -/

/-- One step of the reverse-Polish stack machine over the tag stream.  A tag outside
`1..8`, or a stack underflow, leaves the stack unchanged — in particular the pad tag `0`
is a no-op. -/
def sourceStep (st : List Code) (t : ℕ) : List Code :=
  if t = 1 then Code.zero :: st
  else if t = 2 then Code.succ :: st
  else if t = 3 then Code.left :: st
  else if t = 4 then Code.right :: st
  else if t = 8 then
    (if 1 ≤ st.length then Code.rfind' (st.getD 0 Code.zero) :: st.tail else st)
  else if 2 ≤ st.length then
    (if t = 5 then
        Code.pair (st.getD 1 Code.zero) (st.getD 0 Code.zero) :: st.tail.tail
      else if t = 6 then
        Code.comp (st.getD 1 Code.zero) (st.getD 0 Code.zero) :: st.tail.tail
      else if t = 7 then
        Code.prec (st.getD 1 Code.zero) (st.getD 0 Code.zero) :: st.tail.tail
      else st)
  else st

lemma sourceStep_pad (st : List Code) : sourceStep st 0 = st := by
  simp [sourceStep]

lemma foldl_sourceStep_replicate (k : ℕ) (st : List Code) :
    (List.replicate k 0).foldl sourceStep st = st := by
  induction k generalizing st with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, List.foldl_cons, sourceStep_pad, ih]

/-- The stack machine reconstructs the code from its tag stream. -/
lemma sourceStep_tags : ∀ (c : Code) (st : List Code),
    (sourceTags c).foldl sourceStep st = c :: st := by
  intro c
  induction c with
  | zero | succ | left | right => intro st; simp [sourceTags, sourceStep]
  | pair a b iha ihb | comp a b iha ihb | prec a b iha ihb =>
      intro st
      simp only [sourceTags, List.foldl_append, iha, ihb, List.foldl_cons, List.foldl_nil]
      simp [sourceStep]
  | rfind' a iha =>
      intro st
      simp only [sourceTags, List.foldl_append, iha, List.foldl_cons, List.foldl_nil]
      simp [sourceStep]

/-- One digit-peeling step: shift out the least significant base-16 digit. -/
def peelStep (p : ℕ × List ℕ) : ℕ × List ℕ := (p.1 / 16, p.1 % 16 :: p.2)

/-- `f` peeling steps, accumulating the base-16 digits most-significant first.  No zero
guard: leading zeros are emitted as pad tags, which `sourceStep` ignores. -/
def peelIter (f n : ℕ) : ℕ × List ℕ :=
  Nat.rec (n, ([] : List ℕ)) (fun _ p => peelStep p) f

lemma peelIter_succ (f n : ℕ) : peelIter (f + 1) n = peelStep (peelIter f n) := rfl

lemma peelIter_fst (f n : ℕ) : (peelIter f n).1 = n / 16 ^ f := by
  induction f with
  | zero => simp [peelIter]
  | succ f ih =>
      rw [peelIter_succ]
      simp only [peelStep, ih]
      rw [Nat.div_div_eq_div_mul, ← pow_succ]

lemma peelIter_snd (f n : ℕ) :
    (peelIter f n).2 = (List.range f).reverse.map (fun i => n / 16 ^ i % 16) := by
  induction f with
  | zero => simp [peelIter]
  | succ f ih =>
      rw [peelIter_succ]
      simp only [peelStep, ih, peelIter_fst, List.range_succ, List.reverse_append,
        List.reverse_cons, List.reverse_nil, List.nil_append, List.map_cons,
        List.singleton_append]

lemma map_range_getD (M : List ℕ) : ∀ f, M.length ≤ f →
    (List.range f).map (fun i => M.getD i 0) = M ++ List.replicate (f - M.length) 0 := by
  induction M with
  | nil => intro f _; simp
  | cons a M ih =>
      intro f hf
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp at hf; omega⟩
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [Function.comp_def, List.getD_cons_zero, List.getD_cons_succ]
      rw [ih g (by simpa using hf)]
      simp

lemma map_range_reverse_getD (M : List ℕ) (f : ℕ) (hf : M.length ≤ f) :
    (List.range f).reverse.map (fun i => M.getD i 0)
      = List.replicate (f - M.length) 0 ++ M.reverse := by
  rw [List.map_reverse, map_range_getD M f hf, List.reverse_append, List.reverse_replicate]

/-- Peeling `f ≥ L.length` base-16 digits out of the numeral `L` denotes recovers `L`
behind a pad of leading zeros. -/
lemma peelIter_ofDigits (f : ℕ) (L : List ℕ) (hd : ∀ d ∈ L, d < 16) (hf : L.length ≤ f) :
    (peelIter f (Nat.ofDigits 16 L.reverse)).2
      = List.replicate (f - L.length) 0 ++ L := by
  have hM : ∀ d ∈ L.reverse, d < 16 := by simpa using hd
  have hfun : (fun i => Nat.ofDigits 16 L.reverse / 16 ^ i % 16)
      = fun i => L.reverse.getD i 0 :=
    funext fun i => ofDigits_div_pow_mod (by norm_num) hM i
  rw [peelIter_snd, hfun,
    map_range_reverse_getD _ f (by simpa using hf)]
  simp

/-- Total decoder: garbage decodes to `Nat.Partrec.Code.zero`.  The fuel is the base-4
digit count of the name, which dominates its base-16 digit count — one peel step per
base-4 digit, not per unit of the value. -/
def ofSource (n : ℕ) : Code :=
  ((peelIter (len4 n) n).2.foldl sourceStep []).headD Code.zero

/-- **Decoding cost.**  The decoder takes exactly `len4 n` peel steps on the name `n` —
one per base-4 digit. -/
lemma ofSource_peelSteps (n : ℕ) : ((peelIter (len4 n) n).2).length = len4 n := by
  rw [peelIter_snd]; simp

/-- **Decoding cost for a machine name.**  Decoding `c.sourceNat` takes at most `2 * c.size`
peel steps: linear in the syntax tree. -/
lemma sourceNat_peelSteps_le (c : Code) :
    ((peelIter (len4 c.sourceNat) c.sourceNat).2).length ≤ 2 * c.size := by
  rw [ofSource_peelSteps]; exact len4_sourceNat_le c

/-- **Roundtrip.** -/
lemma ofSource_sourceNat (c : Code) : ofSource c.sourceNat = c := by
  have hlt : ∀ d ∈ sourceTags c, d < 16 := fun d hd => (sourceTags_lt_16 c d hd).2
  have hlen : (sourceTags c).length ≤ len4 c.sourceNat := by
    rw [sourceTags_length]; exact size_le_len4_sourceNat c
  rw [ofSource, sourceNat, peelIter_ofDigits _ _ hlt (by rwa [← sourceNat]),
    List.foldl_append, foldl_sourceStep_replicate, sourceStep_tags]
  simp

lemma sourceNat_injective : Function.Injective sourceNat := by
  intro a b h
  rw [← ofSource_sourceNat a, ← ofSource_sourceNat b, h]

/-! ## The decoder is primitive recursive -/

lemma peelStep_primrec : _root_.Primrec peelStep := by
  have hq : _root_.Primrec (fun p : ℕ × List ℕ => p.1 / 16) :=
    _root_.Primrec.nat_div.comp _root_.Primrec.fst (_root_.Primrec.const 16)
  have hr : _root_.Primrec (fun p : ℕ × List ℕ => p.1 % 16) :=
    _root_.Primrec.nat_mod.comp _root_.Primrec.fst (_root_.Primrec.const 16)
  exact (_root_.Primrec.pair hq
    (_root_.Primrec.list_cons.comp hr _root_.Primrec.snd)).of_eq (fun _ => rfl)

lemma peelIter_primrec : _root_.Primrec (fun p : ℕ × ℕ => peelIter p.1 p.2) :=
  (_root_.Primrec.nat_rec' _root_.Primrec.fst
    (_root_.Primrec.pair _root_.Primrec.snd (_root_.Primrec.const ([] : List ℕ)))
    (peelStep_primrec.comp (_root_.Primrec.snd.comp _root_.Primrec.snd)).to₂).of_eq (fun _ => rfl)

lemma sourceStep_primrec : _root_.Primrec₂ sourceStep := by
  have hst : _root_.Primrec (fun p : List Code × ℕ => p.1) := _root_.Primrec.fst
  have htail : _root_.Primrec (fun p : List Code × ℕ => p.1.tail) :=
    _root_.Primrec.list_tail.comp hst
  have htail2 : _root_.Primrec (fun p : List Code × ℕ => p.1.tail.tail) :=
    _root_.Primrec.list_tail.comp htail
  have hg0 : _root_.Primrec (fun p : List Code × ℕ => p.1.getD 0 Code.zero) :=
    (_root_.Primrec.list_getD Code.zero).comp hst (_root_.Primrec.const 0)
  have hg1 : _root_.Primrec (fun p : List Code × ℕ => p.1.getD 1 Code.zero) :=
    (_root_.Primrec.list_getD Code.zero).comp hst (_root_.Primrec.const 1)
  have heq : ∀ k : ℕ, _root_.PrimrecPred (fun p : List Code × ℕ => p.2 = k) :=
    fun k => _root_.Primrec.eq.comp _root_.Primrec.snd (_root_.Primrec.const k)
  have hle : ∀ k : ℕ, _root_.PrimrecPred (fun p : List Code × ℕ => k ≤ p.1.length) :=
    fun k => _root_.Primrec.nat_le.comp (_root_.Primrec.const k)
      (_root_.Primrec.list_length.comp hst)
  have hpush : ∀ d : Code, _root_.Primrec (fun p : List Code × ℕ => d :: p.1) :=
    fun d => _root_.Primrec.list_cons.comp (_root_.Primrec.const d) hst
  have hbin : ∀ (op : Code → Code → Code), _root_.Primrec₂ op →
      _root_.Primrec (fun p : List Code × ℕ =>
        op (p.1.getD 1 Code.zero) (p.1.getD 0 Code.zero) :: p.1.tail.tail) :=
    fun _ hop => _root_.Primrec.list_cons.comp (hop.comp hg1 hg0) htail2
  have main : _root_.Primrec (fun p : List Code × ℕ =>
      if p.2 = 1 then Code.zero :: p.1
      else if p.2 = 2 then Code.succ :: p.1
      else if p.2 = 3 then Code.left :: p.1
      else if p.2 = 4 then Code.right :: p.1
      else if p.2 = 8 then
        (if 1 ≤ p.1.length then Code.rfind' (p.1.getD 0 Code.zero) :: p.1.tail else p.1)
      else if 2 ≤ p.1.length then
        (if p.2 = 5 then
            Code.pair (p.1.getD 1 Code.zero) (p.1.getD 0 Code.zero) :: p.1.tail.tail
          else if p.2 = 6 then
            Code.comp (p.1.getD 1 Code.zero) (p.1.getD 0 Code.zero) :: p.1.tail.tail
          else if p.2 = 7 then
            Code.prec (p.1.getD 1 Code.zero) (p.1.getD 0 Code.zero) :: p.1.tail.tail
          else p.1)
      else p.1) :=
    _root_.Primrec.ite (heq 1) (hpush Code.zero)
      (_root_.Primrec.ite (heq 2) (hpush Code.succ)
        (_root_.Primrec.ite (heq 3) (hpush Code.left)
          (_root_.Primrec.ite (heq 4) (hpush Code.right)
            (_root_.Primrec.ite (heq 8)
              (_root_.Primrec.ite (hle 1)
                (_root_.Primrec.list_cons.comp (Code.primrec_rfind'.comp hg0) htail) hst)
              (_root_.Primrec.ite (hle 2)
                (_root_.Primrec.ite (heq 5) (hbin Code.pair Code.primrec₂_pair)
                  (_root_.Primrec.ite (heq 6) (hbin Code.comp Code.primrec₂_comp)
                    (_root_.Primrec.ite (heq 7) (hbin Code.prec Code.primrec₂_prec) hst)))
                hst)))))
  exact main.of_eq (fun _ => rfl)

lemma ofSource_primrec : _root_.Primrec ofSource := by
  have hpeel : _root_.Primrec (fun n : ℕ => (peelIter (len4 n) n).2) :=
    _root_.Primrec.snd.comp
      (peelIter_primrec.comp (_root_.Primrec.pair len4_primrec _root_.Primrec.id))
  have hstep : _root_.Primrec₂ (fun (_ : ℕ) (q : List Code × ℕ) => sourceStep q.1 q.2) :=
    (_root_.Primrec.comp sourceStep_primrec _root_.Primrec.snd).to₂
  have hfold : _root_.Primrec (fun n : ℕ => (peelIter (len4 n) n).2.foldl sourceStep []) :=
    (_root_.Primrec.list_foldl hpeel (_root_.Primrec.const ([] : List Code))
      hstep).of_eq (fun _ => rfl)
  have hhd : ∀ (l : List Code) (d : Code), l.headD d = l.head?.getD d := by
    intro l d; cases l <;> rfl
  exact (_root_.Primrec.option_getD.comp (_root_.Primrec.list_head?.comp hfold)
    (_root_.Primrec.const Code.zero)).of_eq (fun n => (hhd _ _).symm)

lemma ofSource_computable : _root_.Computable ofSource := ofSource_primrec.to_comp

/-! ## The `nest` family -/

/-- The `nest` family: `nest 0 = zero`, `nest (n+1) = pair (nest n) zero`. -/
def nest : ℕ → Code
  | 0 => .zero
  | n + 1 => .pair (nest n) .zero

lemma sourceTags_nest (n : ℕ) :
    sourceTags (nest n) = 1 :: (List.replicate n [1, 5]).flatten := by
  induction n with
  | zero => simp [nest, sourceTags]
  | succ n ih =>
      show sourceTags (nest n) ++ sourceTags Code.zero ++ [5] = _
      rw [ih]
      simp [sourceTags, List.replicate_succ']

lemma size_nest (n : ℕ) : (nest n).size = 2 * n + 1 := by
  induction n with
  | zero => simp [nest, size]
  | succ n ih =>
      show (nest n).size + Code.zero.size + 1 = _
      rw [ih]; simp [size]; omega

lemma reverse_sourceTags_nest (n : ℕ) :
    (sourceTags (nest n)).reverse = (List.replicate n [5, 1]).flatten ++ [1] := by
  induction n with
  | zero => simp [nest, sourceTags]
  | succ n ih =>
      show (sourceTags (nest n) ++ sourceTags Code.zero ++ [5]).reverse = _
      simp only [List.reverse_append, ih, sourceTags, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.replicate_succ, List.flatten_cons]
      simp

/-- Closed form for the base-16 digits of `sourceNat (nest n)`, little-endian. -/
def nestDig (n j : ℕ) : ℕ :=
  if 2 * n < j then 0 else if j = 2 * n then 1 else if j % 2 = 0 then 5 else 1

lemma nestDig_lt (n j : ℕ) : nestDig n j < 16 := by
  unfold nestDig; split_ifs <;> omega

lemma getD_revTags (n : ℕ) : ∀ j,
    ((List.replicate n [5, 1]).flatten ++ [1]).getD j 0 = nestDig n j := by
  induction n with
  | zero =>
      intro j
      simp only [List.replicate_zero, List.flatten_nil, List.nil_append]
      match j with
      | 0 =>
          rw [List.getD_cons_zero]
          unfold nestDig; rw [if_neg (by omega), if_pos (by omega)]
      | (k + 1) =>
          rw [List.getD_eq_default _ _ (by simp)]
          unfold nestDig; rw [if_pos (by omega)]
  | succ n ih =>
      intro j
      have hcons : (List.replicate (n + 1) [5, 1]).flatten ++ [1]
          = 5 :: 1 :: ((List.replicate n [5, 1]).flatten ++ [1]) := by
        simp [List.replicate_succ]
      rw [hcons]
      match j with
      | 0 =>
          rw [List.getD_cons_zero]
          unfold nestDig
          rw [if_neg (by omega), if_neg (by omega), if_pos (by decide)]
      | 1 =>
          rw [List.getD_cons_succ, List.getD_cons_zero]
          unfold nestDig
          rw [if_neg (by omega), if_neg (by omega), if_neg (by decide)]
      | (k + 2) =>
          rw [List.getD_cons_succ, List.getD_cons_succ, ih k]
          unfold nestDig
          split_ifs <;> omega

lemma getD_reverse_sourceTags_nest (n j : ℕ) :
    (sourceTags (nest n)).reverse.getD j 0 = nestDig n j := by
  rw [reverse_sourceTags_nest]; exact getD_revTags n j

lemma bigDigits_sourceNat_nest : BigDigits (fun n => (nest n).sourceNat) := by
  obtain ⟨cdm2, hdm2⟩ := divmodc_polyFueled 2 (by norm_num)
  obtain ⟨cm, hcm⟩ := mulc_polyFueled 2
  -- length: `2 * n + 1`
  have hlen : PolyFueled _
      (fun n => ((sourceTags (nest n)).reverse).length) :=
    (hcm.succ_comp).of_eq (fun n => by
      rw [List.length_reverse, sourceTags_length, size_nest]; omega)
  -- digit: the `nestDig` selector chain
  have htwoN : PolyFueled _ (fun z : ℕ => 2 * z.unpair.1) :=
    (hcm.comp PolyFueled.left).of_eq (fun z => by omega)
  have hsel1 : PolyFueled _ (fun z : ℕ => 2 * z.unpair.1 + 1 - z.unpair.2) :=
    (subc_polyFueled.comp (htwoN.succ_comp.pair PolyFueled.right)).of_eq
      (fun z => by simp only [Nat.unpair_pair])
  have hsel2 : PolyFueled _ (fun z : ℕ => 2 * z.unpair.1 - z.unpair.2) :=
    (subc_polyFueled.comp (htwoN.pair PolyFueled.right)).of_eq
      (fun z => by simp only [Nat.unpair_pair])
  have hsel3 : PolyFueled _ (fun z : ℕ => z.unpair.2 % 2) :=
    (PolyFueled.right.comp (hdm2.comp PolyFueled.right)).of_eq
      (fun z => by simp only [Nat.unpair_pair])
  have hC : PolyFueled _ (fun z : ℕ => if z.unpair.2 % 2 = 0 then 5 else 1) :=
    (ifzSel_polyFueled.comp
      (((PolyFueled.const 5).pair (PolyFueled.const 1)).pair hsel3)).of_eq
      (fun z => by simp only [Nat.unpair_pair, ifzSelFn])
  have hB : PolyFueled _ (fun z : ℕ =>
      if 2 * z.unpair.1 - z.unpair.2 = 0 then 1
      else if z.unpair.2 % 2 = 0 then 5 else 1) :=
    (ifzSel_polyFueled.comp (((PolyFueled.const 1).pair hC).pair hsel2)).of_eq
      (fun z => by simp only [Nat.unpair_pair, ifzSelFn])
  obtain ⟨cA, hA⟩ : ∃ c, PolyFueled c (fun z : ℕ => nestDig z.unpair.1 z.unpair.2) := by
    refine ⟨_, (ifzSel_polyFueled.comp
      (((PolyFueled.const 0).pair hB).pair hsel1)).of_eq (fun z => ?_)⟩
    simp only [Nat.unpair_pair, ifzSelFn, nestDig]
    by_cases h1 : 2 * z.unpair.1 < z.unpair.2
    · rw [if_pos (by omega : 2 * z.unpair.1 + 1 - z.unpair.2 = 0), if_pos h1]
    · rw [if_neg (by omega : ¬ (2 * z.unpair.1 + 1 - z.unpair.2 = 0)), if_neg h1]
      by_cases h2 : z.unpair.2 = 2 * z.unpair.1
      · rw [if_pos (by omega : 2 * z.unpair.1 - z.unpair.2 = 0), if_pos h2]
      · rw [if_neg (by omega : ¬ (2 * z.unpair.1 - z.unpair.2 = 0)), if_neg h2]
  have hdig : PolyFueled _ (fun z : ℕ =>
      ((sourceTags (nest z.unpair.1)).reverse).getD z.unpair.2 0) :=
    hA.of_eq (fun z => (getD_reverse_sourceTags_nest _ _).symm)
  exact (BigDigits.ofBase16Digits hlen hdig
    (fun n j => by rw [getD_reverse_sourceTags_nest]; exact nestDig_lt n j)).of_eq
      (fun _ => rfl)

/-- An exponential lower bound on the `nest` family's source encoding: enough to refute
`IsPolyBounded` for it. -/
lemma two_pow_le_sourceNat_nest (n : ℕ) : 2 ^ n ≤ (nest n).sourceNat := by
  have h := pow_pred_le_sourceNat (nest n)
  rw [size_nest, Nat.add_sub_cancel] at h
  refine le_trans ?_ h
  calc (2 : ℕ) ^ n ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ ≤ 16 ^ (2 * n) := Nat.pow_le_pow_left (by norm_num) _

end Nat.Partrec.Code

#print axioms LogicalInduction.ofDigits_div_pow_mod
#print axioms LogicalInduction.dig4_ofDigits_sixteen
#print axioms LogicalInduction.BigDigits.ofBase16Digits
#print axioms LogicalInduction.BigDigits.ofBase16PolySegStream
#print axioms LogicalInduction.tokenListNat_primrec
#print axioms Nat.Partrec.Code.sourceTags
#print axioms Nat.Partrec.Code.size
#print axioms Nat.Partrec.Code.sourceTags_ne_nil
#print axioms Nat.Partrec.Code.sourceTags_lt_16
#print axioms Nat.Partrec.Code.sourceTags_length
#print axioms Nat.Partrec.Code.size_pos
#print axioms Nat.Partrec.Code.sourceNat
#print axioms Nat.Partrec.Code.sourceTags_reverse_lt_16
#print axioms Nat.Partrec.Code.sourceNat_lt
#print axioms Nat.Partrec.Code.pow_pred_le_sourceNat
#print axioms Nat.Partrec.Code.sourceNat_pos
#print axioms Nat.Partrec.Code.len4_sourceNat_le
#print axioms Nat.Partrec.Code.size_le_sourceNat
#print axioms Nat.Partrec.Code.size_le_len4_sourceNat
#print axioms Nat.Partrec.Code.sourceStep
#print axioms Nat.Partrec.Code.sourceStep_pad
#print axioms Nat.Partrec.Code.foldl_sourceStep_replicate
#print axioms Nat.Partrec.Code.sourceStep_tags
#print axioms Nat.Partrec.Code.peelStep
#print axioms Nat.Partrec.Code.peelIter
#print axioms Nat.Partrec.Code.peelIter_succ
#print axioms Nat.Partrec.Code.peelIter_fst
#print axioms Nat.Partrec.Code.peelIter_snd
#print axioms Nat.Partrec.Code.map_range_getD
#print axioms Nat.Partrec.Code.map_range_reverse_getD
#print axioms Nat.Partrec.Code.peelIter_ofDigits
#print axioms Nat.Partrec.Code.ofSource
#print axioms Nat.Partrec.Code.ofSource_peelSteps
#print axioms Nat.Partrec.Code.sourceNat_peelSteps_le
#print axioms Nat.Partrec.Code.ofSource_sourceNat
#print axioms Nat.Partrec.Code.sourceNat_injective
#print axioms Nat.Partrec.Code.peelStep_primrec
#print axioms Nat.Partrec.Code.peelIter_primrec
#print axioms Nat.Partrec.Code.sourceStep_primrec
#print axioms Nat.Partrec.Code.ofSource_primrec
#print axioms Nat.Partrec.Code.ofSource_computable
#print axioms Nat.Partrec.Code.nest
#print axioms Nat.Partrec.Code.sourceTags_nest
#print axioms Nat.Partrec.Code.size_nest
#print axioms Nat.Partrec.Code.reverse_sourceTags_nest
#print axioms Nat.Partrec.Code.nestDig
#print axioms Nat.Partrec.Code.nestDig_lt
#print axioms Nat.Partrec.Code.getD_revTags
#print axioms Nat.Partrec.Code.getD_reverse_sourceTags_nest
#print axioms Nat.Partrec.Code.bigDigits_sourceNat_nest
#print axioms Nat.Partrec.Code.two_pow_le_sourceNat_nest
