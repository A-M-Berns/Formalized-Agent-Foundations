import LogicalInduction.Framework.Emission.RpnSentence

/-!
# An exact finite automaton for one structured payload code

`Criterion.parseStructuredArithmeticFormula` is the numeric mirror of the structured
arithmetic codec: a fuel-clocked, input-directed parser that turns a token payload into a
Foundation formula code.  Downstream, the freeze needs to *recognize*, for one fixed code
`fc`, exactly the payloads that parse to it — and to do so with finite control, so that the
recognizer is a `RunAuto.BlockAutomaton` guard rather than an unbounded computation.

The language is infinite for most `fc` (a numeral may carry arbitrarily many leading `1`
padding tokens, and token `20` applies the De Morgan involution, so `[9]` and `[20, 20, 9]`
denote the same code), but it is regular for each fixed `fc`.  This file proves that, by
top-down predictive parsing against an *obligation stack*:

* `Obl.num n` — the next tokens must spell the numeral `n`;
* `Obl.trm c` — ... an arithmetic term with code `c`;
* `Obl.fml c β` — ... a formula whose code `d` satisfies `negFormulaCode^[β] d = c`.

The `β` bit is the device that keeps the state set finite: rather than inverting
`negFormulaCode` (which would push child targets outside any bound derived from `fc`), an
obligation carries the *parity of pending negations*, and every child code is an `unpair`
component of its parent.  Soundness of the parity bookkeeping at `β = true` is exactly the
statement that `negFormulaCode` is involutive, which is false in general (tags 2/3 with a
nonzero payload) but true on the parser's range — hence `WFCode` and
`wfCode_of_parseFormula`.

Finiteness is then a potential argument rather than a closure computation: `phi` sums
`code + 1` over the stack, every transition leaves it unchanged or decreases it, so from the
initial stack every reachable stack has `phi ≤ fc + 1`, bounding both the stack length and
every code in it.  `payStacks fc` enumerates that finite set; states are indices into it,
with `payQ fc` the absorbing reject state.

Everything here is construction infrastructure rather than a paper statement, so the
declarations are `lemma`s and `def`s.
-/

namespace LogicalInduction.PayAuto

open LogicalInduction

-- The `Nat.pair`/`unpair` reachable from the sentence codec unfolds `Nat.sqrt`'s
-- well-founded definition during `whnf` and loops; local opacity stops that.
-- See `notes/lean-gotchas.md`.
attribute [local irreducible] Nat.sqrt

def pnat (ts : List ℕ) : Option (ℕ × List ℕ) := parseStructuredNat ts.length ts
def ptrm (ts : List ℕ) : Option (ℕ × List ℕ) := parseStructuredArithmeticTerm ts.length 0 ts
def pfml (ts : List ℕ) : Option (ℕ × List ℕ) := parseStructuredArithmeticFormula ts.length 0 ts

lemma pnat_fuel {fuel fuel' : ℕ} {ts : List ℕ} (h : ts.length ≤ fuel) (h' : ts.length ≤ fuel') :
    parseStructuredNat fuel ts = parseStructuredNat fuel' ts := by
  induction fuel generalizing fuel' ts with
  | zero =>
      obtain rfl : ts = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp h)
      cases fuel' <;> simp [parseStructuredNat]
  | succ f ih =>
      rcases ts with _ | ⟨t, ts⟩
      · cases fuel' <;> simp [parseStructuredNat]
      · rcases fuel' with _ | f'
        · simp only [List.length_cons] at h'; omega
        · have hle : ts.length ≤ f := by simp only [List.length_cons] at h; omega
          have hle' : ts.length ≤ f' := by simp only [List.length_cons] at h'; omega
          rw [parseStructuredNat, parseStructuredNat, ih hle hle']

lemma ptrm_fuel {fuel fuel' d d' : ℕ} {ts : List ℕ} (h : ts.length ≤ fuel)
    (h' : ts.length ≤ fuel') :
    parseStructuredArithmeticTerm fuel d ts = parseStructuredArithmeticTerm fuel' d' ts := by
  induction fuel generalizing fuel' d d' ts with
  | zero =>
      obtain rfl : ts = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp h)
      cases fuel' <;> simp [parseStructuredArithmeticTerm]
  | succ f ih =>
      rcases ts with _ | ⟨t, ts⟩
      · cases fuel' <;> simp [parseStructuredArithmeticTerm]
      · rcases fuel' with _ | f'
        · simp only [List.length_cons] at h'; omega
        · have hle : ts.length ≤ f := by simp only [List.length_cons] at h; omega
          have hle' : ts.length ≤ f' := by simp only [List.length_cons] at h'; omega
          rw [parseStructuredArithmeticTerm, parseStructuredArithmeticTerm]
          by_cases h3 : t = 3
          · simp only [if_pos h3]
            rw [pnat_fuel hle hle']
          simp only [if_neg h3]
          by_cases h4 : t = 4
          · simp only [if_pos h4]
            rw [pnat_fuel hle hle']
          simp only [if_neg h4]
          by_cases h5 : t = 5
          · simp only [if_pos h5]
          simp only [if_neg h5]
          by_cases h6 : t = 6
          · simp only [if_pos h6]
          simp only [if_neg h6]
          by_cases h78 : t = 7 ∨ t = 8
          · simp only [if_pos h78]
            rw [ih (d := 0) (d' := 0) hle hle']
            rcases hp : parseStructuredArithmeticTerm f' 0 ts with _ | p
            · rfl
            · simp only [Option.bind_some]
              have hsub : p.2.length ≤ ts.length :=
                (parseStructuredArithmeticTerm_suffix hp).length_le
              rw [ih (d := 0) (d' := 0) (le_trans hsub hle) (le_trans hsub hle')]
          simp only [if_neg h78]

lemma pfml_fuel {fuel fuel' d d' : ℕ} {ts : List ℕ} (h : ts.length ≤ fuel)
    (h' : ts.length ≤ fuel') :
    parseStructuredArithmeticFormula fuel d ts
      = parseStructuredArithmeticFormula fuel' d' ts := by
  induction fuel generalizing fuel' d d' ts with
  | zero =>
      obtain rfl : ts = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp h)
      cases fuel' <;> simp [parseStructuredArithmeticFormula]
  | succ f ih =>
      rcases ts with _ | ⟨t, ts⟩
      · cases fuel' <;> simp [parseStructuredArithmeticFormula]
      · rcases fuel' with _ | f'
        · simp only [List.length_cons] at h'; omega
        · have hle : ts.length ≤ f := by simp only [List.length_cons] at h; omega
          have hle' : ts.length ≤ f' := by simp only [List.length_cons] at h'; omega
          rw [parseStructuredArithmeticFormula, parseStructuredArithmeticFormula]
          by_cases h9 : t = 9
          · simp only [if_pos h9]
          simp only [if_neg h9]
          by_cases h10 : t = 10
          · simp only [if_pos h10]
          simp only [if_neg h10]
          by_cases hrel : t = 11 ∨ t = 12 ∨ t = 13 ∨ t = 14
          · simp only [if_pos hrel]
            rw [ptrm_fuel (d := 0) (d' := 0) hle hle']
            rcases hp : parseStructuredArithmeticTerm f' 0 ts with _ | p
            · rfl
            · simp only [Option.bind_some]
              have hsub : p.2.length ≤ ts.length :=
                (parseStructuredArithmeticTerm_suffix hp).length_le
              rw [ptrm_fuel (d := 0) (d' := 0) (le_trans hsub hle) (le_trans hsub hle')]
          simp only [if_neg hrel]
          by_cases hbin : t = 15 ∨ t = 16
          · simp only [if_pos hbin]
            rw [ih (d := 0) (d' := 0) hle hle']
            rcases hp : parseStructuredArithmeticFormula f' 0 ts with _ | p
            · rfl
            · simp only [Option.bind_some]
              have hsub : p.2.length ≤ ts.length :=
                (parseStructuredArithmeticFormula_suffix hp).length_le
              rw [ih (d := 0) (d' := 0) (le_trans hsub hle) (le_trans hsub hle')]
          simp only [if_neg hbin]
          by_cases hq : t = 17 ∨ t = 18
          · simp only [if_pos hq]
            rw [ih (d := 0) (d' := 0) hle hle']
          simp only [if_neg hq]
          by_cases h20 : t = 20
          · simp only [if_pos h20]
            rw [ih (d := 0) (d' := 0) hle hle']
          simp only [if_neg h20]
          by_cases h21 : t = 21
          · simp only [if_pos h21]
            rw [ih (d := 0) (d' := 0) hle hle']
            rcases hp : parseStructuredArithmeticFormula f' 0 ts with _ | p
            · rfl
            · simp only [Option.bind_some]
              have hsub : p.2.length ≤ ts.length :=
                (parseStructuredArithmeticFormula_suffix hp).length_le
              rw [ih (d := 0) (d' := 0) (le_trans hsub hle) (le_trans hsub hle')]
          simp only [if_neg h21]
          by_cases h22 : t = 22
          · simp only [if_pos h22]
            rw [ih (d := 0) (d' := 0) hle hle']
            rcases hp : parseStructuredArithmeticFormula f' 0 ts with _ | p
            · rfl
            · simp only [Option.bind_some]
              have hsub : p.2.length ≤ ts.length :=
                (parseStructuredArithmeticFormula_suffix hp).length_le
              rw [ih (d := 0) (d' := 0) (le_trans hsub hle) (le_trans hsub hle')]
          simp only [if_neg h22]

lemma pnat_eq {fuel : ℕ} {ts : List ℕ} (h : ts.length ≤ fuel) :
    parseStructuredNat fuel ts = pnat ts :=
  pnat_fuel h le_rfl

lemma ptrm_eq {fuel d : ℕ} {ts : List ℕ} (h : ts.length ≤ fuel) :
    parseStructuredArithmeticTerm fuel d ts = ptrm ts :=
  ptrm_fuel h le_rfl

lemma pfml_eq {fuel d : ℕ} {ts : List ℕ} (h : ts.length ≤ fuel) :
    parseStructuredArithmeticFormula fuel d ts = pfml ts :=
  pfml_fuel h le_rfl

lemma pnat_nil : pnat [] = none := by simp [pnat, parseStructuredNat]
lemma ptrm_nil : ptrm [] = none := by simp [ptrm, parseStructuredArithmeticTerm]
lemma pfml_nil : pfml [] = none := by simp [pfml, parseStructuredArithmeticFormula]

lemma pnat_cons (t : ℕ) (rest : List ℕ) :
    pnat (t :: rest) =
      if t = 0 then some (0, rest)
      else if t = 1 then (pnat rest).map (fun p => (2 * p.1, p.2))
      else if t = 2 then (pnat rest).map (fun p => (2 * p.1 + 1, p.2))
      else none := by
  simp only [pnat, List.length_cons]
  rw [parseStructuredNat]

lemma ptrm_cons (t : ℕ) (rest : List ℕ) :
    ptrm (t :: rest) =
      if t = 3 then (pnat rest).map (fun p => (Nat.pair 0 p.1 + 1, p.2))
      else if t = 4 then (pnat rest).map (fun p => (Nat.pair 1 p.1 + 1, p.2))
      else if t = 5 then some (arithmeticFuncCode 0 0 0, rest)
      else if t = 6 then some (arithmeticFuncCode 0 1 0, rest)
      else if t = 7 ∨ t = 8 then
        (ptrm rest).bind (fun p => (ptrm p.2).map (fun q =>
          (arithmeticFuncCode 2 (if t = 7 then 0 else 1) (arithmeticVec2Code p.1 q.1), q.2)))
      else none := by
  simp only [pnat, ptrm, List.length_cons]
  rw [parseStructuredArithmeticTerm]
  by_cases h3 : t = 3
  · simp only [if_pos h3]
  simp only [if_neg h3]
  by_cases h4 : t = 4
  · simp only [if_pos h4]
  simp only [if_neg h4]
  by_cases h5 : t = 5
  · simp only [if_pos h5]
  simp only [if_neg h5]
  by_cases h6 : t = 6
  · simp only [if_pos h6]
  simp only [if_neg h6]
  by_cases h78 : t = 7 ∨ t = 8
  · simp only [if_pos h78]
    rcases hp : parseStructuredArithmeticTerm rest.length 0 rest with _ | p
    · rfl
    · simp only [Option.bind_some]
      have hsub : p.2.length ≤ rest.length :=
        (parseStructuredArithmeticTerm_suffix hp).length_le
      rw [ptrm_fuel (d := 0) (d' := 0) hsub le_rfl]
  simp only [if_neg h78]

lemma pfml_cons (t : ℕ) (rest : List ℕ) :
    pfml (t :: rest) =
      if t = 9 then some (Nat.pair 2 0 + 1, rest)
      else if t = 10 then some (Nat.pair 3 0 + 1, rest)
      else if t = 11 ∨ t = 12 ∨ t = 13 ∨ t = 14 then
        (ptrm rest).bind (fun p => (ptrm p.2).map (fun q =>
          (arithmeticRelCode (t = 12 ∨ t = 14) (if t = 11 ∨ t = 12 then 0 else 1) p.1 q.1, q.2)))
      else if t = 15 ∨ t = 16 then
        (pfml rest).bind (fun p => (pfml p.2).map (fun q =>
          (Nat.pair (if t = 15 then 4 else 5) (Nat.pair p.1 q.1) + 1, q.2)))
      else if t = 17 ∨ t = 18 then
        (pfml rest).map (fun p => (Nat.pair (if t = 17 then 6 else 7) p.1 + 1, p.2))
      else if t = 20 then (pfml rest).map (fun p => (negFormulaCode p.1, p.2))
      else if t = 21 then
        (pfml rest).bind (fun p => (pfml p.2).map (fun q =>
          (Nat.pair 5 (Nat.pair (negFormulaCode p.1) q.1) + 1, q.2)))
      else if t = 22 then
        (pfml rest).bind (fun p => (pfml p.2).map (fun q =>
          (Nat.pair 4 (Nat.pair (Nat.pair 5 (Nat.pair (negFormulaCode p.1) q.1) + 1)
            (Nat.pair 5 (Nat.pair (negFormulaCode q.1) p.1) + 1)) + 1, q.2)))
      else none := by
  simp only [pfml, ptrm, List.length_cons]
  rw [parseStructuredArithmeticFormula]
  by_cases h9 : t = 9
  · simp only [if_pos h9]
  simp only [if_neg h9]
  by_cases h10 : t = 10
  · simp only [if_pos h10]
  simp only [if_neg h10]
  by_cases hrel : t = 11 ∨ t = 12 ∨ t = 13 ∨ t = 14
  · simp only [if_pos hrel]
    rcases hp : parseStructuredArithmeticTerm rest.length 0 rest with _ | p
    · rfl
    · simp only [Option.bind_some]
      have hsub : p.2.length ≤ rest.length :=
        (parseStructuredArithmeticTerm_suffix hp).length_le
      rw [ptrm_fuel (d := 0) (d' := 0) hsub le_rfl]
  simp only [if_neg hrel]
  by_cases hbin : t = 15 ∨ t = 16
  · simp only [if_pos hbin]
    rcases hp : parseStructuredArithmeticFormula rest.length 0 rest with _ | p
    · rfl
    · simp only [Option.bind_some]
      have hsub : p.2.length ≤ rest.length :=
        (parseStructuredArithmeticFormula_suffix hp).length_le
      rw [pfml_fuel (d := 0) (d' := 0) hsub le_rfl]
  simp only [if_neg hbin]
  by_cases hq : t = 17 ∨ t = 18
  · simp only [if_pos hq]
  simp only [if_neg hq]
  by_cases h20 : t = 20
  · simp only [if_pos h20]
  simp only [if_neg h20]
  by_cases h21 : t = 21
  · simp only [if_pos h21]
    rcases hp : parseStructuredArithmeticFormula rest.length 0 rest with _ | p
    · rfl
    · simp only [Option.bind_some]
      have hsub : p.2.length ≤ rest.length :=
        (parseStructuredArithmeticFormula_suffix hp).length_le
      rw [pfml_fuel (d := 0) (d' := 0) hsub le_rfl]
  simp only [if_neg h21]
  by_cases h22 : t = 22
  · simp only [if_pos h22]
    rcases hp : parseStructuredArithmeticFormula rest.length 0 rest with _ | p
    · rfl
    · simp only [Option.bind_some]
      have hsub : p.2.length ≤ rest.length :=
        (parseStructuredArithmeticFormula_suffix hp).length_le
      rw [pfml_fuel (d := 0) (d' := 0) hsub le_rfl]
  simp only [if_neg h22]

lemma pnat_suffix {ts : List ℕ} {n : ℕ} {rest : List ℕ} (h : pnat ts = some (n, rest)) :
    rest <:+ ts :=
  parseStructuredNat_suffix h

lemma ptrm_suffix {ts : List ℕ} {c : ℕ} {rest : List ℕ} (h : ptrm ts = some (c, rest)) :
    rest <:+ ts :=
  parseStructuredArithmeticTerm_suffix h

lemma pfml_suffix {ts : List ℕ} {c : ℕ} {rest : List ℕ} (h : pfml ts = some (c, rest)) :
    rest <:+ ts :=
  parseStructuredArithmeticFormula_suffix h

/-! ## Part 1 — computation lemmas for `negFormulaCode` at each constructor tag -/

lemma neg_tag0 (p : ℕ) : negFormulaCode (Nat.pair 0 p + 1) = Nat.pair 1 p + 1 := by
  rw [negFormulaCode]; simp

lemma neg_tag1 (p : ℕ) : negFormulaCode (Nat.pair 1 p + 1) = Nat.pair 0 p + 1 := by
  rw [negFormulaCode]; simp

lemma neg_tag2 (p : ℕ) : negFormulaCode (Nat.pair 2 p + 1) = Nat.pair 3 0 + 1 := by
  rw [negFormulaCode]; simp

lemma neg_tag3 (p : ℕ) : negFormulaCode (Nat.pair 3 p + 1) = Nat.pair 2 0 + 1 := by
  rw [negFormulaCode]; simp

lemma neg_tag4 (x y : ℕ) : negFormulaCode (Nat.pair 4 (Nat.pair x y) + 1)
    = Nat.pair 5 (Nat.pair (negFormulaCode x) (negFormulaCode y)) + 1 := by
  rw [negFormulaCode]; simp

lemma neg_tag5 (x y : ℕ) : negFormulaCode (Nat.pair 5 (Nat.pair x y) + 1)
    = Nat.pair 4 (Nat.pair (negFormulaCode x) (negFormulaCode y)) + 1 := by
  rw [negFormulaCode]; simp

lemma neg_tag6 (x : ℕ) :
    negFormulaCode (Nat.pair 6 x + 1) = Nat.pair 7 (negFormulaCode x) + 1 := by
  rw [negFormulaCode]; simp

lemma neg_tag7 (x : ℕ) :
    negFormulaCode (Nat.pair 7 x + 1) = Nat.pair 6 (negFormulaCode x) + 1 := by
  rw [negFormulaCode]; simp

/-! ## Part 2 — the range predicate and the involution -/

/-- The range of the structured arithmetic formula parser: the codes on which
`negFormulaCode` is a genuine involution.  The `verum`/`falsum` tags `2`/`3` pin their
payload to `0`, because `negFormulaCode` normalizes it there; the relation tags `0`/`1`
need no constraint on their payload at all, which is exactly why the involution survives
the relation codes. -/
inductive WFCode : ℕ → Prop
  | tag0 (p : ℕ) : WFCode (Nat.pair 0 p + 1)
  | tag1 (p : ℕ) : WFCode (Nat.pair 1 p + 1)
  | tag2 : WFCode (Nat.pair 2 0 + 1)
  | tag3 : WFCode (Nat.pair 3 0 + 1)
  | tag4 {x y : ℕ} : WFCode x → WFCode y → WFCode (Nat.pair 4 (Nat.pair x y) + 1)
  | tag5 {x y : ℕ} : WFCode x → WFCode y → WFCode (Nat.pair 5 (Nat.pair x y) + 1)
  | tag6 {x : ℕ} : WFCode x → WFCode (Nat.pair 6 x + 1)
  | tag7 {x : ℕ} : WFCode x → WFCode (Nat.pair 7 x + 1)

lemma WFCode.ne_zero {c : ℕ} (h : WFCode c) : c ≠ 0 := by
  cases h <;> exact Nat.succ_ne_zero _

lemma wf_arithmeticRelCode (b : Bool) (s a c : ℕ) : WFCode (arithmeticRelCode b s a c) := by
  unfold arithmeticRelCode
  cases b
  · exact WFCode.tag0 _
  · exact WFCode.tag1 _

lemma WFCode.neg {c : ℕ} (h : WFCode c) : WFCode (negFormulaCode c) := by
  induction h with
  | tag0 p => rw [neg_tag0]; exact WFCode.tag1 p
  | tag1 p => rw [neg_tag1]; exact WFCode.tag0 p
  | tag2 => rw [neg_tag2]; exact WFCode.tag3
  | tag3 => rw [neg_tag3]; exact WFCode.tag2
  | tag4 _ _ ihx ihy => rw [neg_tag4]; exact WFCode.tag5 ihx ihy
  | tag5 _ _ ihx ihy => rw [neg_tag5]; exact WFCode.tag4 ihx ihy
  | tag6 _ ihx => rw [neg_tag6]; exact WFCode.tag7 ihx
  | tag7 _ ihx => rw [neg_tag7]; exact WFCode.tag6 ihx

lemma WFCode.invol {c : ℕ} (h : WFCode c) : negFormulaCode (negFormulaCode c) = c := by
  induction h with
  | tag0 p => rw [neg_tag0, neg_tag1]
  | tag1 p => rw [neg_tag1, neg_tag0]
  | tag2 => rw [neg_tag2, neg_tag3]
  | tag3 => rw [neg_tag3, neg_tag2]
  | tag4 _ _ ihx ihy => rw [neg_tag4, neg_tag5, ihx, ihy]
  | tag5 _ _ ihx ihy => rw [neg_tag5, neg_tag4, ihx, ihy]
  | tag6 _ ihx => rw [neg_tag6, neg_tag7, ihx]
  | tag7 _ ihx => rw [neg_tag7, neg_tag6, ihx]

/-! ## Part 3 — the parser's outputs are well-formed -/

lemma wfCode_of_parseFormula : ∀ {fuel depth : ℕ} {ts : List ℕ} {c : ℕ} {rest : List ℕ},
    parseStructuredArithmeticFormula fuel depth ts = some (c, rest) → WFCode c := by
  intro fuel
  induction fuel with
  | zero =>
      intro depth ts c rest h
      simp [parseStructuredArithmeticFormula] at h
  | succ fuel ih =>
      intro depth ts c rest h
      rcases ts with _ | ⟨t, ts⟩
      · simp [parseStructuredArithmeticFormula] at h
      rw [parseStructuredArithmeticFormula] at h
      by_cases h9 : t = 9
      · rw [if_pos h9] at h
        obtain ⟨rfl, -⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
        exact WFCode.tag2
      rw [if_neg h9] at h
      by_cases h10 : t = 10
      · rw [if_pos h10] at h
        obtain ⟨rfl, -⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
        exact WFCode.tag3
      rw [if_neg h10] at h
      by_cases hrel : t = 11 ∨ t = 12 ∨ t = 13 ∨ t = 14
      · rw [if_pos hrel] at h
        rcases hp : parseStructuredArithmeticTerm fuel 0 ts with _ | p <;> simp [hp] at h
        rcases hq : parseStructuredArithmeticTerm fuel 0 p.2 with _ | q <;> simp [hq] at h
        obtain ⟨a, rfl, rfl⟩ := h
        exact wf_arithmeticRelCode _ _ _ _
      rw [if_neg hrel] at h
      by_cases hbin : t = 15 ∨ t = 16
      · rw [if_pos hbin] at h
        rcases hp : parseStructuredArithmeticFormula fuel 0 ts with _ | p <;> simp [hp] at h
        rcases hq : parseStructuredArithmeticFormula fuel 0 p.2 with _ | q <;> simp [hq] at h
        obtain ⟨a, rfl, rfl⟩ := h
        split
        · exact WFCode.tag4 (ih hp) (ih hq)
        · exact WFCode.tag5 (ih hp) (ih hq)
      rw [if_neg hbin] at h
      by_cases hquant : t = 17 ∨ t = 18
      · rw [if_pos hquant] at h
        rcases hp : parseStructuredArithmeticFormula fuel 0 ts with _ | p <;> simp [hp] at h
        obtain ⟨rfl, -⟩ := h
        split
        · exact WFCode.tag6 (ih hp)
        · exact WFCode.tag7 (ih hp)
      rw [if_neg hquant] at h
      by_cases h20 : t = 20
      · rw [if_pos h20] at h
        rcases hp : parseStructuredArithmeticFormula fuel 0 ts with _ | p <;> simp [hp] at h
        obtain ⟨rfl, -⟩ := h
        exact (ih hp).neg
      rw [if_neg h20] at h
      by_cases h21 : t = 21
      · rw [if_pos h21] at h
        rcases hp : parseStructuredArithmeticFormula fuel 0 ts with _ | p <;> simp [hp] at h
        rcases hq : parseStructuredArithmeticFormula fuel 0 p.2 with _ | q <;> simp [hq] at h
        obtain ⟨a, rfl, rfl⟩ := h
        exact WFCode.tag5 (ih hp).neg (ih hq)
      rw [if_neg h21] at h
      by_cases h22 : t = 22
      · rw [if_pos h22] at h
        rcases hp : parseStructuredArithmeticFormula fuel 0 ts with _ | p <;> simp [hp] at h
        rcases hq : parseStructuredArithmeticFormula fuel 0 p.2 with _ | q <;> simp [hq] at h
        obtain ⟨a, rfl, rfl⟩ := h
        exact WFCode.tag4 (WFCode.tag5 (ih hp).neg (ih hq))
          (WFCode.tag5 (ih hq).neg (ih hp))
      rw [if_neg h22] at h
      simp at h

lemma invol_of_parse {fuel depth : ℕ} {ts : List ℕ} {c : ℕ} {rest : List ℕ}
    (h : parseStructuredArithmeticFormula fuel depth ts = some (c, rest)) :
    negFormulaCode (negFormulaCode c) = c :=
  (wfCode_of_parseFormula h).invol

lemma neg_ne_zero_of_parse {fuel depth : ℕ} {ts : List ℕ} {c : ℕ} {rest : List ℕ}
    (h : parseStructuredArithmeticFormula fuel depth ts = some (c, rest)) : c ≠ 0 :=
  (wfCode_of_parseFormula h).ne_zero

/-- Involutivity of `negFormulaCode` on the formula parser's range, in the canonical-fuel
spelling used throughout this file. -/
lemma invol_of_pfml {ts : List ℕ} {c : ℕ} {rest : List ℕ} (h : pfml ts = some (c, rest)) :
    negFormulaCode (negFormulaCode c) = c := invol_of_parse h

lemma ne_zero_of_pfml {ts : List ℕ} {c : ℕ} {rest : List ℕ} (h : pfml ts = some (c, rest)) :
    c ≠ 0 := neg_ne_zero_of_parse h

lemma neg_ne_zero_of_pfml {ts : List ℕ} {c : ℕ} {rest : List ℕ} (h : pfml ts = some (c, rest)) :
    negFormulaCode c ≠ 0 := (wfCode_of_parseFormula h).neg.ne_zero

/-! ## Obligations -/

inductive Obl
  | num (n : ℕ)
  | trm (c : ℕ)
  | fml (c : ℕ) (β : Bool)
  deriving DecidableEq

def Obl.code : Obl → ℕ
  | .num n => n
  | .trm c => c
  | .fml c _ => c

def nfB : Bool → ℕ → ℕ
  | false, c => c
  | true, c => negFormulaCode c

def oblStep : Obl → ℕ → Option (List Obl)
  | .num n, t =>
      if t = 0 then (if n = 0 then some [] else none)
      else if t = 1 then (if 2 * (n / 2) = n then some [Obl.num (n / 2)] else none)
      else if t = 2 then (if 2 * (n / 2) + 1 = n then some [Obl.num (n / 2)] else none)
      else none
  | .trm c, t =>
      if c = 0 then none else
      if t = 3 then (if (c - 1).unpair.1 = 0 then some [Obl.num (c - 1).unpair.2] else none)
      else if t = 4 then (if (c - 1).unpair.1 = 1 then some [Obl.num (c - 1).unpair.2] else none)
      else if t = 5 then (if c = arithmeticFuncCode 0 0 0 then some [] else none)
      else if t = 6 then (if c = arithmeticFuncCode 0 1 0 then some [] else none)
      else if t = 7 ∨ t = 8 then
        (if (c - 1).unpair.1 = 2 ∧ (c - 1).unpair.2.unpair.1 = 2
            ∧ (c - 1).unpair.2.unpair.2.unpair.1 = (if t = 7 then 0 else 1)
            ∧ (c - 1).unpair.2.unpair.2.unpair.2 ≠ 0
            ∧ ((c - 1).unpair.2.unpair.2.unpair.2 - 1).unpair.2 ≠ 0
            ∧ (((c - 1).unpair.2.unpair.2.unpair.2 - 1).unpair.2 - 1).unpair.2 = 0 then
          some [Obl.trm ((c - 1).unpair.2.unpair.2.unpair.2 - 1).unpair.1,
                Obl.trm ((((c - 1).unpair.2.unpair.2.unpair.2 - 1).unpair.2 - 1).unpair.1)]
         else none)
      else none
  | .fml c β, t =>
      if c = 0 then none else
      if t = 9 then (if c = Nat.pair (if β then 3 else 2) 0 + 1 then some [] else none)
      else if t = 10 then (if c = Nat.pair (if β then 2 else 3) 0 + 1 then some [] else none)
      else if t = 11 ∨ t = 12 ∨ t = 13 ∨ t = 14 then
        (if (c - 1).unpair.1 = (if xor (decide (t = 12 ∨ t = 14)) β then 1 else 0)
            ∧ (c - 1).unpair.2.unpair.1 = 2
            ∧ (c - 1).unpair.2.unpair.2.unpair.1 = (if t = 11 ∨ t = 12 then 0 else 1)
            ∧ (c - 1).unpair.2.unpair.2.unpair.2 ≠ 0
            ∧ ((c - 1).unpair.2.unpair.2.unpair.2 - 1).unpair.2 ≠ 0
            ∧ (((c - 1).unpair.2.unpair.2.unpair.2 - 1).unpair.2 - 1).unpair.2 = 0 then
          some [Obl.trm ((c - 1).unpair.2.unpair.2.unpair.2 - 1).unpair.1,
                Obl.trm ((((c - 1).unpair.2.unpair.2.unpair.2 - 1).unpair.2 - 1).unpair.1)]
         else none)
      else if t = 15 ∨ t = 16 then
        (if (c - 1).unpair.1 = (if t = 15 then (if β then 5 else 4) else (if β then 4 else 5)) then
          some [Obl.fml (c - 1).unpair.2.unpair.1 β, Obl.fml (c - 1).unpair.2.unpair.2 β]
         else none)
      else if t = 17 ∨ t = 18 then
        (if (c - 1).unpair.1 = (if t = 17 then (if β then 7 else 6) else (if β then 6 else 7)) then
          some [Obl.fml (c - 1).unpair.2 β]
         else none)
      else if t = 20 then
        (if β then
          (if negFormulaCode (negFormulaCode c) = c then some [Obl.fml c false] else none)
         else some [Obl.fml c true])
      else if t = 21 then
        (if β then
          (if (c - 1).unpair.1 = 4
              ∧ negFormulaCode (negFormulaCode (c - 1).unpair.2.unpair.1)
                  = (c - 1).unpair.2.unpair.1 then
            some [Obl.fml (c - 1).unpair.2.unpair.1 false, Obl.fml (c - 1).unpair.2.unpair.2 true]
           else none)
         else
          (if (c - 1).unpair.1 = 5 then
            some [Obl.fml (c - 1).unpair.2.unpair.1 true, Obl.fml (c - 1).unpair.2.unpair.2 false]
           else none))
      else if t = 22 then
        (if (c - 1).unpair.2.unpair.1 = 0 ∨ (c - 1).unpair.2.unpair.2 = 0 then none else
         if β then
          (if (c - 1).unpair.1 = 5
              ∧ ((c - 1).unpair.2.unpair.1 - 1).unpair.1 = 4
              ∧ ((c - 1).unpair.2.unpair.2 - 1).unpair.1 = 4
              ∧ ((c - 1).unpair.2.unpair.1 - 1).unpair.2.unpair.2
                  = negFormulaCode ((c - 1).unpair.2.unpair.2 - 1).unpair.2.unpair.1
              ∧ ((c - 1).unpair.2.unpair.2 - 1).unpair.2.unpair.2
                  = negFormulaCode ((c - 1).unpair.2.unpair.1 - 1).unpair.2.unpair.1
              ∧ negFormulaCode (negFormulaCode ((c - 1).unpair.2.unpair.1 - 1).unpair.2.unpair.1)
                  = ((c - 1).unpair.2.unpair.1 - 1).unpair.2.unpair.1
              ∧ negFormulaCode (negFormulaCode ((c - 1).unpair.2.unpair.2 - 1).unpair.2.unpair.1)
                  = ((c - 1).unpair.2.unpair.2 - 1).unpair.2.unpair.1 then
            some [Obl.fml ((c - 1).unpair.2.unpair.1 - 1).unpair.2.unpair.1 false,
                  Obl.fml ((c - 1).unpair.2.unpair.2 - 1).unpair.2.unpair.1 false]
           else none)
         else
          (if (c - 1).unpair.1 = 4
              ∧ ((c - 1).unpair.2.unpair.1 - 1).unpair.1 = 5
              ∧ ((c - 1).unpair.2.unpair.2 - 1).unpair.1 = 5
              ∧ ((c - 1).unpair.2.unpair.1 - 1).unpair.2.unpair.1
                  = negFormulaCode ((c - 1).unpair.2.unpair.2 - 1).unpair.2.unpair.2
              ∧ ((c - 1).unpair.2.unpair.2 - 1).unpair.2.unpair.1
                  = negFormulaCode ((c - 1).unpair.2.unpair.1 - 1).unpair.2.unpair.2 then
            some [Obl.fml ((c - 1).unpair.2.unpair.2 - 1).unpair.2.unpair.2 false,
                  Obl.fml ((c - 1).unpair.2.unpair.1 - 1).unpair.2.unpair.2 false]
           else none))
      else none

def stackStep : List Obl → ℕ → Option (List Obl)
  | [], _ => none
  | o :: S, t => (oblStep o t).map (fun L => L ++ S)

def stackRun : List Obl → List ℕ → Option (List Obl)
  | S, [] => some S
  | S, t :: ts => (stackStep S t).bind (fun S' => stackRun S' ts)

def SatObl : Obl → List ℕ → List ℕ → Prop
  | .num n, ts, rest => pnat ts = some (n, rest)
  | .trm c, ts, rest => ptrm ts = some (c, rest)
  | .fml c β, ts, rest => ∃ d, pfml ts = some (d, rest) ∧ nfB β d = c

def SatStack : List Obl → List ℕ → List ℕ → Prop
  | [], ts, rest => rest = ts
  | o :: S, ts, rest => ∃ mid, SatObl o ts mid ∧ SatStack S mid rest

lemma satStack_append (L S : List Obl) (ts rest : List ℕ) :
    SatStack (L ++ S) ts rest ↔ ∃ mid, SatStack L ts mid ∧ SatStack S mid rest := by
  induction L generalizing ts with
  | nil => simp [SatStack]
  | cons o L ih =>
      simp only [List.cons_append, SatStack, ih]
      constructor
      · rintro ⟨m, ho, m2, h1, h2⟩; exact ⟨m2, ⟨m, ho, h1⟩, h2⟩
      · rintro ⟨m2, ⟨m, ho, h1⟩, h2⟩; exact ⟨m, ho, m2, h1, h2⟩

lemma satStack_nil_iff (ts mid : List ℕ) : SatStack [] ts mid ↔ mid = ts := Iff.rfl

lemma satStack_one (o : Obl) (ts mid : List ℕ) : SatStack [o] ts mid ↔ SatObl o ts mid := by
  constructor
  · rintro ⟨m, h, rfl⟩; exact h
  · intro h; exact ⟨mid, h, rfl⟩

lemma satStack_two (o1 o2 : Obl) (ts mid : List ℕ) :
    SatStack [o1, o2] ts mid ↔ ∃ m, SatObl o1 ts m ∧ SatObl o2 m mid := by
  constructor
  · rintro ⟨m, h1, m2, h2, rfl⟩; exact ⟨m, h1, h2⟩
  · rintro ⟨m, h1, h2⟩; exact ⟨m, h1, mid, h2, rfl⟩

@[simp] lemma nfB_false (c : ℕ) : nfB false c = c := rfl
@[simp] lemma nfB_true (c : ℕ) : nfB true c = negFormulaCode c := rfl

@[simp] lemma unpair_pair_succ_fst (a b : ℕ) : (Nat.pair a b + 1 - 1).unpair.1 = a := by
  simp [Nat.unpair_pair]
@[simp] lemma unpair_pair_succ_snd (a b : ℕ) : (Nat.pair a b + 1 - 1).unpair.2 = b := by
  simp [Nat.unpair_pair]

/-- Reconstruction: a nonzero code is `Nat.pair` of its two unpaired fields, plus one. -/
lemma pair_unpair_succ {c : ℕ} (h : c ≠ 0) :
    Nat.pair (c - 1).unpair.1 (c - 1).unpair.2 + 1 = c := by
  rw [Nat.pair_unpair]; omega

lemma nfB_ne_zero {β : Bool} {ts : List ℕ} {d : ℕ} {rest : List ℕ}
    (h : pfml ts = some (d, rest)) : nfB β d ≠ 0 := by
  cases β
  · exact ne_zero_of_pfml h
  · exact neg_ne_zero_of_pfml h

lemma key_num (n t : ℕ) (ts mid : List ℕ) :
    (∃ L, oblStep (Obl.num n) t = some L ∧ SatStack L ts mid) ↔
      SatObl (Obl.num n) (t :: ts) mid := by
  simp only [SatObl, pnat_cons, oblStep]
  by_cases h0 : t = 0
  · simp only [if_pos h0]
    constructor
    · rintro ⟨L, hL, hS⟩
      by_cases hn : n = 0
      · subst hn
        rw [if_pos rfl] at hL
        have hL' : L = [] := (Option.some.inj hL).symm
        subst hL'
        rw [satStack_nil_iff] at hS
        subst hS
        rfl
      · rw [if_neg hn] at hL; exact absurd hL (by simp)
    · intro h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨[], by rw [if_pos rfl], rfl⟩
  by_cases h1 : t = 1
  · simp only [if_neg h0, if_pos h1, Option.map_eq_some_iff]
    constructor
    · rintro ⟨L, hL, hS⟩
      by_cases he : 2 * (n / 2) = n
      · rw [if_pos he] at hL
        have hL' : L = [Obl.num (n / 2)] := (Option.some.inj hL).symm
        subst hL'
        rw [satStack_one] at hS
        exact ⟨(n / 2, mid), hS, by rw [he]⟩
      · rw [if_neg he] at hL; exact absurd hL (by simp)
    · rintro ⟨⟨v, r⟩, hv, hq⟩
      simp only [Prod.mk.injEq] at hq
      obtain ⟨rfl, rfl⟩ := hq
      refine ⟨[Obl.num (2 * v / 2)], by rw [if_pos (show 2 * (2 * v / 2) = 2 * v by omega)], ?_⟩
      rw [satStack_one]
      show pnat ts = some (2 * v / 2, r)
      rw [show 2 * v / 2 = v by omega]; exact hv
  by_cases h2 : t = 2
  · simp only [if_neg h0, if_neg h1, if_pos h2, Option.map_eq_some_iff]
    constructor
    · rintro ⟨L, hL, hS⟩
      by_cases he : 2 * (n / 2) + 1 = n
      · rw [if_pos he] at hL
        have hL' : L = [Obl.num (n / 2)] := (Option.some.inj hL).symm
        subst hL'
        rw [satStack_one] at hS
        exact ⟨(n / 2, mid), hS, by rw [he]⟩
      · rw [if_neg he] at hL; exact absurd hL (by simp)
    · rintro ⟨⟨v, r⟩, hv, hq⟩
      simp only [Prod.mk.injEq] at hq
      obtain ⟨rfl, rfl⟩ := hq
      refine ⟨[Obl.num ((2 * v + 1) / 2)],
        by rw [if_pos (show 2 * ((2 * v + 1) / 2) + 1 = 2 * v + 1 by omega)], ?_⟩
      rw [satStack_one]
      show pnat ts = some ((2 * v + 1) / 2, r)
      rw [show (2 * v + 1) / 2 = v by omega]; exact hv
  · simp only [if_neg h0, if_neg h1, if_neg h2]
    constructor
    · rintro ⟨L, hL, -⟩; exact absurd hL (by simp)
    · intro h; exact absurd h (by simp)

/-! ## key_trm -/

/-- Auxiliary: rebuild a binary-function term code from `oblStep`'s six field guards. -/
lemma trm_code_rebuild {c s : ℕ} (hc0 : c ≠ 0)
    (hg1 : (c - 1).unpair.1 = 2)
    (hg2 : (c - 1).unpair.2.unpair.1 = 2)
    (hg3 : (c - 1).unpair.2.unpair.2.unpair.1 = s)
    (hg4 : (c - 1).unpair.2.unpair.2.unpair.2 ≠ 0)
    (hg5 : ((c - 1).unpair.2.unpair.2.unpair.2 - 1).unpair.2 ≠ 0)
    (hg6 : (((c - 1).unpair.2.unpair.2.unpair.2 - 1).unpair.2 - 1).unpair.2 = 0) :
    arithmeticFuncCode 2 s (arithmeticVec2Code
        ((c - 1).unpair.2.unpair.2.unpair.2 - 1).unpair.1
        ((((c - 1).unpair.2.unpair.2.unpair.2 - 1).unpair.2 - 1).unpair.1)) = c := by
  have e1 : Nat.pair ((((c - 1).unpair.2.unpair.2.unpair.2 - 1).unpair.2 - 1).unpair.1) 0 + 1
      = ((c - 1).unpair.2.unpair.2.unpair.2 - 1).unpair.2 := by
    rw [← hg6]; exact pair_unpair_succ hg5
  have e2 : Nat.pair (((c - 1).unpair.2.unpair.2.unpair.2 - 1).unpair.1)
      (((c - 1).unpair.2.unpair.2.unpair.2 - 1).unpair.2) + 1
      = (c - 1).unpair.2.unpair.2.unpair.2 := pair_unpair_succ hg4
  have e3 : Nat.pair s ((c - 1).unpair.2.unpair.2.unpair.2) = (c - 1).unpair.2.unpair.2 := by
    rw [← hg3]; exact Nat.pair_unpair _
  have e4 : Nat.pair 2 ((c - 1).unpair.2.unpair.2) = (c - 1).unpair.2 := by
    rw [← hg2]; exact Nat.pair_unpair _
  have e5 : Nat.pair 2 ((c - 1).unpair.2) + 1 = c := by
    rw [← hg1]; exact pair_unpair_succ hc0
  simp only [arithmeticFuncCode, arithmeticVec2Code]
  rw [e1, e2, e3, e4, e5]

/-- Auxiliary: the `t = 7 ∨ t = 8` branch of `key_trm`, with the symbol tag abstracted as `s`
(so that the payload conditional `if t = 7 then 0 else 1` never has to be split). -/
lemma key_trm_binary (s c : ℕ) (ts mid : List ℕ) :
    (∃ L, (if c = 0 then none else
      (if (c - 1).unpair.1 = 2 ∧ (c - 1).unpair.2.unpair.1 = 2
          ∧ (c - 1).unpair.2.unpair.2.unpair.1 = s
          ∧ (c - 1).unpair.2.unpair.2.unpair.2 ≠ 0
          ∧ ((c - 1).unpair.2.unpair.2.unpair.2 - 1).unpair.2 ≠ 0
          ∧ (((c - 1).unpair.2.unpair.2.unpair.2 - 1).unpair.2 - 1).unpair.2 = 0 then
        some [Obl.trm ((c - 1).unpair.2.unpair.2.unpair.2 - 1).unpair.1,
              Obl.trm ((((c - 1).unpair.2.unpair.2.unpair.2 - 1).unpair.2 - 1).unpair.1)]
       else none) : Option (List Obl)) = some L ∧ SatStack L ts mid) ↔
      (ptrm ts).bind (fun p => (ptrm p.2).map (fun q =>
        (arithmeticFuncCode 2 s (arithmeticVec2Code p.1 q.1), q.2))) = some (c, mid) := by
  constructor
  · rintro ⟨L, hL, hS⟩
    by_cases hc0 : c = 0
    · rw [if_pos hc0] at hL; exact absurd hL (by simp)
    rw [if_neg hc0] at hL
    by_cases hg : (c - 1).unpair.1 = 2 ∧ (c - 1).unpair.2.unpair.1 = 2
        ∧ (c - 1).unpair.2.unpair.2.unpair.1 = s
        ∧ (c - 1).unpair.2.unpair.2.unpair.2 ≠ 0
        ∧ ((c - 1).unpair.2.unpair.2.unpair.2 - 1).unpair.2 ≠ 0
        ∧ (((c - 1).unpair.2.unpair.2.unpair.2 - 1).unpair.2 - 1).unpair.2 = 0
    · rw [if_pos hg] at hL
      obtain ⟨hg1, hg2, hg3, hg4, hg5, hg6⟩ := hg
      have hLe := Option.some.inj hL
      subst hLe
      rw [satStack_two] at hS
      obtain ⟨m, h1, h2⟩ := hS
      simp only [SatObl] at h1 h2
      simp only [h1, Option.bind_some, h2, Option.map_some, Option.some.injEq, Prod.mk.injEq,
        and_true]
      exact trm_code_rebuild hc0 hg1 hg2 hg3 hg4 hg5 hg6
    · rw [if_neg hg] at hL; exact absurd hL (by simp)
  · intro h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨p, hp, h⟩ := h
    rw [Option.map_eq_some_iff] at h
    obtain ⟨q, hq, hqe⟩ := h
    simp only [Prod.mk.injEq] at hqe
    obtain ⟨hc, rfl⟩ := hqe
    subst hc
    refine ⟨[Obl.trm p.1, Obl.trm q.1], ?_, ?_⟩
    · simp [arithmeticFuncCode, arithmeticVec2Code]
    · rw [satStack_two]
      exact ⟨p.2, hp, hq⟩

lemma key_trm (c t : ℕ) (ts mid : List ℕ) :
    (∃ L, oblStep (Obl.trm c) t = some L ∧ SatStack L ts mid) ↔
      SatObl (Obl.trm c) (t :: ts) mid := by
  simp only [SatObl, ptrm_cons, oblStep]
  by_cases h3 : t = 3
  · simp only [if_pos h3, Option.map_eq_some_iff]
    constructor
    · rintro ⟨L, hL, hS⟩
      by_cases hc0 : c = 0
      · rw [if_pos hc0] at hL; exact absurd hL (by simp)
      rw [if_neg hc0] at hL
      by_cases hu : (c - 1).unpair.1 = 0
      · rw [if_pos hu] at hL
        have hLe := Option.some.inj hL
        subst hLe
        rw [satStack_one] at hS
        refine ⟨((c - 1).unpair.2, mid), hS, ?_⟩
        simp only [Prod.mk.injEq, and_true]
        have hpu := pair_unpair_succ hc0
        rw [hu] at hpu
        exact hpu
      · rw [if_neg hu] at hL; exact absurd hL (by simp)
    · rintro ⟨⟨v, r⟩, hv, hq⟩
      simp only [Prod.mk.injEq] at hq
      obtain ⟨hc, rfl⟩ := hq
      subst hc
      refine ⟨[Obl.num v], by simp, ?_⟩
      rw [satStack_one]
      exact hv
  by_cases h4 : t = 4
  · simp only [if_neg h3, if_pos h4, Option.map_eq_some_iff]
    constructor
    · rintro ⟨L, hL, hS⟩
      by_cases hc0 : c = 0
      · rw [if_pos hc0] at hL; exact absurd hL (by simp)
      rw [if_neg hc0] at hL
      by_cases hu : (c - 1).unpair.1 = 1
      · rw [if_pos hu] at hL
        have hLe := Option.some.inj hL
        subst hLe
        rw [satStack_one] at hS
        refine ⟨((c - 1).unpair.2, mid), hS, ?_⟩
        simp only [Prod.mk.injEq, and_true]
        have hpu := pair_unpair_succ hc0
        rw [hu] at hpu
        exact hpu
      · rw [if_neg hu] at hL; exact absurd hL (by simp)
    · rintro ⟨⟨v, r⟩, hv, hq⟩
      simp only [Prod.mk.injEq] at hq
      obtain ⟨hc, rfl⟩ := hq
      subst hc
      refine ⟨[Obl.num v], by simp, ?_⟩
      rw [satStack_one]
      exact hv
  by_cases h5 : t = 5
  · simp only [if_neg h3, if_neg h4, if_pos h5]
    constructor
    · rintro ⟨L, hL, hS⟩
      by_cases hc0 : c = 0
      · rw [if_pos hc0] at hL; exact absurd hL (by simp)
      rw [if_neg hc0] at hL
      by_cases hcc : c = arithmeticFuncCode 0 0 0
      · rw [if_pos hcc] at hL
        have hLe := Option.some.inj hL
        subst hLe
        rw [satStack_nil_iff] at hS
        subst hS
        rw [hcc]
      · rw [if_neg hcc] at hL; exact absurd hL (by simp)
    · intro h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hc, rfl⟩ := h
      subst hc
      exact ⟨[], by simp [arithmeticFuncCode], rfl⟩
  by_cases h6 : t = 6
  · simp only [if_neg h3, if_neg h4, if_neg h5, if_pos h6]
    constructor
    · rintro ⟨L, hL, hS⟩
      by_cases hc0 : c = 0
      · rw [if_pos hc0] at hL; exact absurd hL (by simp)
      rw [if_neg hc0] at hL
      by_cases hcc : c = arithmeticFuncCode 0 1 0
      · rw [if_pos hcc] at hL
        have hLe := Option.some.inj hL
        subst hLe
        rw [satStack_nil_iff] at hS
        subst hS
        rw [hcc]
      · rw [if_neg hcc] at hL; exact absurd hL (by simp)
    · intro h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hc, rfl⟩ := h
      subst hc
      exact ⟨[], by simp [arithmeticFuncCode], rfl⟩
  by_cases h78 : t = 7 ∨ t = 8
  · simp only [if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_pos h78]
    exact key_trm_binary _ c ts mid
  · simp only [if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h78]
    constructor
    · rintro ⟨L, hL, -⟩
      by_cases hc0 : c = 0
      · rw [if_pos hc0] at hL; exact absurd hL (by simp)
      · rw [if_neg hc0] at hL; exact absurd hL (by simp)
    · intro h; exact absurd h (by simp)

/-! ## key_fml_A : the `.fml` step for tokens 9–14 -/

/-- Auxiliary: `negFormulaCode` on a relation code is a pure tag flip (`neg_tag0`/
`neg_tag1` keep the payload), so a pending negation parity `β` simply xors into the
code's `negative` field. -/
lemma nfB_arithmeticRelCode (β bn : Bool) (sym a b : ℕ) :
    nfB β (arithmeticRelCode bn sym a b) = arithmeticRelCode (xor bn β) sym a b := by
  cases β <;> cases bn <;>
    simp [arithmeticRelCode, nfB, neg_tag0, neg_tag1]

/-- Auxiliary: the atomic-relation branch of the `.fml` step, for an arbitrary
polarity bit `bn`, symbol index `sym` and (abstracted) expected tag `tag`.  The tag is a
parameter rather than a literal `if` so that `split_ifs` cannot desynchronise the branch
structure by splitting it. -/
lemma key_fml_rel (c : ℕ) (β bn : Bool) (sym : ℕ) (ts mid : List ℕ) (hc : c ≠ 0)
    (tag : ℕ) (htag : tag = if xor bn β then 1 else 0) :
    (∃ L, (if (c - 1).unpair.1 = tag
              ∧ (c - 1).unpair.2.unpair.1 = 2
              ∧ (c - 1).unpair.2.unpair.2.unpair.1 = sym
              ∧ (c - 1).unpair.2.unpair.2.unpair.2 ≠ 0
              ∧ ((c - 1).unpair.2.unpair.2.unpair.2 - 1).unpair.2 ≠ 0
              ∧ (((c - 1).unpair.2.unpair.2.unpair.2 - 1).unpair.2 - 1).unpair.2 = 0 then
            some [Obl.trm ((c - 1).unpair.2.unpair.2.unpair.2 - 1).unpair.1,
                  Obl.trm ((((c - 1).unpair.2.unpair.2.unpair.2 - 1).unpair.2 - 1).unpair.1)]
           else none) = some L ∧ SatStack L ts mid) ↔
      (∃ d, ((ptrm ts).bind (fun p => (ptrm p.2).map (fun q =>
              (arithmeticRelCode bn sym p.1 q.1, q.2)))) = some (d, mid) ∧ nfB β d = c) := by
  constructor
  · rintro ⟨L, hL, hS⟩
    split_ifs at hL with hG
    · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hG
      have hL' : L = [Obl.trm ((c - 1).unpair.2.unpair.2.unpair.2 - 1).unpair.1,
            Obl.trm ((((c - 1).unpair.2.unpair.2.unpair.2 - 1).unpair.2 - 1).unpair.1)] :=
        (Option.some.inj hL).symm
      subst hL'
      rw [satStack_two] at hS
      obtain ⟨m, hm1, hm2⟩ := hS
      have ha : ptrm ts = some (((c - 1).unpair.2.unpair.2.unpair.2 - 1).unpair.1, m) := hm1
      have hb : ptrm m =
          some ((((c - 1).unpair.2.unpair.2.unpair.2 - 1).unpair.2 - 1).unpair.1, mid) := hm2
      -- rebuild `c` from the guard fields
      have hw := pair_unpair_succ h5
      rw [h6] at hw
      have hAA := pair_unpair_succ h4
      have hvec : arithmeticVec2Code ((c - 1).unpair.2.unpair.2.unpair.2 - 1).unpair.1
            ((((c - 1).unpair.2.unpair.2.unpair.2 - 1).unpair.2 - 1).unpair.1)
          = (c - 1).unpair.2.unpair.2.unpair.2 := by
        rw [arithmeticVec2Code, hw, hAA]
      have e3 : Nat.pair sym ((c - 1).unpair.2.unpair.2.unpair.2)
          = (c - 1).unpair.2.unpair.2 := by
        rw [← h3]; exact Nat.pair_unpair _
      have e2 : Nat.pair 2 ((c - 1).unpair.2.unpair.2) = (c - 1).unpair.2 := by
        rw [← h2]; exact Nat.pair_unpair _
      have e1 : Nat.pair tag ((c - 1).unpair.2) = c - 1 := by
        rw [← h1]; exact Nat.pair_unpair _
      have hrel : arithmeticRelCode (xor bn β) sym
            ((c - 1).unpair.2.unpair.2.unpair.2 - 1).unpair.1
            ((((c - 1).unpair.2.unpair.2.unpair.2 - 1).unpair.2 - 1).unpair.1) = c := by
        rw [arithmeticRelCode, hvec, e3, e2, ← htag, e1]
        omega
      refine ⟨arithmeticRelCode bn sym ((c - 1).unpair.2.unpair.2.unpair.2 - 1).unpair.1
          ((((c - 1).unpair.2.unpair.2.unpair.2 - 1).unpair.2 - 1).unpair.1), ?_, ?_⟩
      · simp [ha, hb]
      · rw [nfB_arithmeticRelCode]; exact hrel
  · rintro ⟨d, hd, hnf⟩
    rw [Option.bind_eq_some_iff] at hd
    obtain ⟨p, hp, hq⟩ := hd
    rw [Option.map_eq_some_iff] at hq
    obtain ⟨q, hq1, hq2⟩ := hq
    simp only [Prod.mk.injEq] at hq2
    obtain ⟨rfl, rfl⟩ := hq2
    rw [nfB_arithmeticRelCode] at hnf
    subst hnf
    split_ifs with hG
    · refine ⟨_, rfl, ?_⟩
      rw [satStack_two]
      refine ⟨p.2, ?_, ?_⟩
      · show ptrm ts = some (_, p.2)
        simpa [arithmeticRelCode, arithmeticVec2Code] using hp
      · show ptrm p.2 = some (_, q.2)
        simpa [arithmeticRelCode, arithmeticVec2Code] using hq1
    · exfalso
      apply hG
      simp [arithmeticRelCode, arithmeticVec2Code, htag]

lemma key_fml_A (c : ℕ) (β : Bool) (t : ℕ)
    (ht : t = 9 ∨ t = 10 ∨ t = 11 ∨ t = 12 ∨ t = 13 ∨ t = 14) (ts mid : List ℕ) :
    (∃ L, oblStep (Obl.fml c β) t = some L ∧ SatStack L ts mid) ↔
      SatObl (Obl.fml c β) (t :: ts) mid := by
  by_cases hc : c = 0
  · subst hc
    have hstep : oblStep (Obl.fml 0 β) t = none := by simp [oblStep]
    simp only [SatObl]
    constructor
    · rintro ⟨L, hL, -⟩; rw [hstep] at hL; exact absurd hL (by simp)
    · rintro ⟨d, hd, hnf⟩; exact absurd hnf (nfB_ne_zero hd)
  simp only [SatObl, pfml_cons, oblStep, if_neg hc]
  by_cases h9 : t = 9
  · simp only [if_pos h9]
    have hval : nfB β (Nat.pair 2 0 + 1) = Nat.pair (if β then 3 else 2) 0 + 1 := by
      cases β <;> simp [neg_tag2]
    constructor
    · rintro ⟨L, hL, hS⟩
      by_cases hcv : c = Nat.pair (if β then 3 else 2) 0 + 1
      · rw [if_pos hcv] at hL
        have hL' : L = [] := (Option.some.inj hL).symm
        subst hL'
        rw [satStack_nil_iff] at hS
        subst hS
        exact ⟨Nat.pair 2 0 + 1, rfl, by rw [hval, hcv]⟩
      · rw [if_neg hcv] at hL; exact absurd hL (by simp)
    · rintro ⟨d, hd, hnf⟩
      simp only [Option.some.injEq, Prod.mk.injEq] at hd
      obtain ⟨rfl, rfl⟩ := hd
      have hcv : c = Nat.pair (if β then 3 else 2) 0 + 1 := by rw [← hnf, hval]
      exact ⟨[], by rw [if_pos hcv], rfl⟩
  by_cases h10 : t = 10
  · simp only [if_neg h9, if_pos h10]
    have hval : nfB β (Nat.pair 3 0 + 1) = Nat.pair (if β then 2 else 3) 0 + 1 := by
      cases β <;> simp [neg_tag3]
    constructor
    · rintro ⟨L, hL, hS⟩
      by_cases hcv : c = Nat.pair (if β then 2 else 3) 0 + 1
      · rw [if_pos hcv] at hL
        have hL' : L = [] := (Option.some.inj hL).symm
        subst hL'
        rw [satStack_nil_iff] at hS
        subst hS
        exact ⟨Nat.pair 3 0 + 1, rfl, by rw [hval, hcv]⟩
      · rw [if_neg hcv] at hL; exact absurd hL (by simp)
    · rintro ⟨d, hd, hnf⟩
      simp only [Option.some.injEq, Prod.mk.injEq] at hd
      obtain ⟨rfl, rfl⟩ := hd
      have hcv : c = Nat.pair (if β then 2 else 3) 0 + 1 := by rw [← hnf, hval]
      exact ⟨[], by rw [if_pos hcv], rfl⟩
  · have hcond : t = 11 ∨ t = 12 ∨ t = 13 ∨ t = 14 := by omega
    simp only [if_neg h9, if_neg h10, if_pos hcond]
    exact key_fml_rel c β (decide (t = 12 ∨ t = 14)) (if t = 11 ∨ t = 12 then 0 else 1)
      ts mid hc _ rfl

/-! ## key_fml_B : the propositional-connective tokens (15,16,17,18,20) -/

/-- Auxiliary: the binary-connective step, parametric in the parser tag and the
`nfB`-image tag.  Used for tokens 15 (tag 4) and 16 (tag 5). -/
private lemma key_bin_aux (c : ℕ) (hc : c ≠ 0) (β : Bool) (tag T : ℕ)
    (hnf : ∀ x y : ℕ, nfB β (Nat.pair tag (Nat.pair x y) + 1)
        = Nat.pair T (Nat.pair (nfB β x) (nfB β y)) + 1)
    (ts mid : List ℕ) :
    (∃ L, (if (c - 1).unpair.1 = T then
             some [Obl.fml (c - 1).unpair.2.unpair.1 β, Obl.fml (c - 1).unpair.2.unpair.2 β]
           else none) = some L ∧ SatStack L ts mid) ↔
      ∃ d, ((pfml ts).bind (fun p => (pfml p.2).map (fun q =>
             (Nat.pair tag (Nat.pair p.1 q.1) + 1, q.2)))) = some (d, mid) ∧ nfB β d = c := by
  constructor
  · rintro ⟨L, hL, hS⟩
    by_cases hg : (c - 1).unpair.1 = T
    · rw [if_pos hg] at hL
      have hL' : L = [Obl.fml (c - 1).unpair.2.unpair.1 β, Obl.fml (c - 1).unpair.2.unpair.2 β] :=
        (Option.some.inj hL).symm
      subst hL'
      rw [satStack_two] at hS
      obtain ⟨m, h1, h2⟩ := hS
      obtain ⟨x, hx, hxe⟩ := h1
      obtain ⟨y, hy, hye⟩ := h2
      refine ⟨Nat.pair tag (Nat.pair x y) + 1, ?_, ?_⟩
      · rw [hx]; simp [hy]
      · rw [hnf, hxe, hye, ← hg, Nat.pair_unpair, pair_unpair_succ hc]
    · rw [if_neg hg] at hL; exact absurd hL (by simp)
  · rintro ⟨d, hd, hde⟩
    rw [Option.bind_eq_some_iff] at hd
    obtain ⟨⟨p1, p2⟩, hp, hq⟩ := hd
    rw [Option.map_eq_some_iff] at hq
    obtain ⟨⟨q1, q2⟩, hq1, hq2⟩ := hq
    rw [Prod.mk.injEq] at hq2
    obtain ⟨rfl, rfl⟩ := hq2
    rw [hnf] at hde
    subst hde
    simp only [unpair_pair_succ_fst, unpair_pair_succ_snd, Nat.unpair_pair]
    refine ⟨_, rfl, ?_⟩
    rw [satStack_two]
    exact ⟨p2, ⟨p1, hp, rfl⟩, ⟨q1, hq1, rfl⟩⟩

/-- Auxiliary: the unary-connective step.  Used for tokens 17 (tag 6) and 18 (tag 7). -/
private lemma key_un_aux (c : ℕ) (hc : c ≠ 0) (β : Bool) (tag T : ℕ)
    (hnf : ∀ x : ℕ, nfB β (Nat.pair tag x + 1) = Nat.pair T (nfB β x) + 1)
    (ts mid : List ℕ) :
    (∃ L, (if (c - 1).unpair.1 = T then some [Obl.fml (c - 1).unpair.2 β] else none)
        = some L ∧ SatStack L ts mid) ↔
      ∃ d, ((pfml ts).map (fun p => (Nat.pair tag p.1 + 1, p.2))) = some (d, mid)
        ∧ nfB β d = c := by
  constructor
  · rintro ⟨L, hL, hS⟩
    by_cases hg : (c - 1).unpair.1 = T
    · rw [if_pos hg] at hL
      have hL' : L = [Obl.fml (c - 1).unpair.2 β] := (Option.some.inj hL).symm
      subst hL'
      rw [satStack_one] at hS
      obtain ⟨x, hx, hxe⟩ := hS
      refine ⟨Nat.pair tag x + 1, ?_, ?_⟩
      · rw [Option.map_eq_some_iff]; exact ⟨(x, mid), hx, rfl⟩
      · rw [hnf, hxe, ← hg, pair_unpair_succ hc]
    · rw [if_neg hg] at hL; exact absurd hL (by simp)
  · rintro ⟨d, hd, hde⟩
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨⟨x1, x2⟩, hx, hq⟩ := hd
    rw [Prod.mk.injEq] at hq
    obtain ⟨rfl, rfl⟩ := hq
    rw [hnf] at hde
    subst hde
    simp only [unpair_pair_succ_fst, unpair_pair_succ_snd]
    refine ⟨_, rfl, ?_⟩
    rw [satStack_one]
    exact ⟨x1, hx, rfl⟩

lemma key_fml_B (c : ℕ) (β : Bool) (t : ℕ)
    (ht : t = 15 ∨ t = 16 ∨ t = 17 ∨ t = 18 ∨ t = 20) (ts mid : List ℕ) :
    (∃ L, oblStep (Obl.fml c β) t = some L ∧ SatStack L ts mid) ↔
      SatObl (Obl.fml c β) (t :: ts) mid := by
  by_cases hc : c = 0
  · subst hc
    constructor
    · rintro ⟨L, hL, -⟩
      rw [oblStep] at hL
      exact absurd hL (by simp)
    · rintro ⟨d, hd, hde⟩
      exact absurd hde (nfB_ne_zero hd)
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · simp only [SatObl, pfml_cons, oblStep, if_neg hc, Nat.reduceEqDiff, reduceIte,
      or_self, or_false]
    exact key_bin_aux c hc β 4 (if β then 5 else 4)
      (fun x y => by cases β <;> simp [neg_tag4]) ts mid
  · simp only [SatObl, pfml_cons, oblStep, if_neg hc, Nat.reduceEqDiff, reduceIte,
      or_self, or_true]
    exact key_bin_aux c hc β 5 (if β then 4 else 5)
      (fun x y => by cases β <;> simp [neg_tag5]) ts mid
  · simp only [SatObl, pfml_cons, oblStep, if_neg hc, Nat.reduceEqDiff, reduceIte,
      or_self, or_false]
    exact key_un_aux c hc β 6 (if β then 7 else 6)
      (fun x => by cases β <;> simp [neg_tag6]) ts mid
  · simp only [SatObl, pfml_cons, oblStep, if_neg hc, Nat.reduceEqDiff, reduceIte,
      or_self, or_true]
    exact key_un_aux c hc β 7 (if β then 6 else 7)
      (fun x => by cases β <;> simp [neg_tag7]) ts mid
  · simp only [SatObl, pfml_cons, oblStep, if_neg hc, Nat.reduceEqDiff, reduceIte,
      or_self]
    cases β
    · simp only [Bool.false_eq_true, if_false, nfB_false]
      constructor
      · rintro ⟨L, hL, hS⟩
        have hL' : L = [Obl.fml c true] := (Option.some.inj hL).symm
        subst hL'
        rw [satStack_one] at hS
        obtain ⟨x, hx, hxe⟩ := hS
        exact ⟨negFormulaCode x, by rw [Option.map_eq_some_iff]; exact ⟨(x, mid), hx, rfl⟩, hxe⟩
      · rintro ⟨d, hd, hde⟩
        rw [Option.map_eq_some_iff] at hd
        obtain ⟨⟨x1, x2⟩, hx, hq⟩ := hd
        rw [Prod.mk.injEq] at hq
        obtain ⟨rfl, rfl⟩ := hq
        refine ⟨[Obl.fml c true], rfl, ?_⟩
        rw [satStack_one]
        exact ⟨x1, hx, hde⟩
    · simp only [if_true, nfB_true]
      constructor
      · rintro ⟨L, hL, hS⟩
        by_cases hg : negFormulaCode (negFormulaCode c) = c
        · rw [if_pos hg] at hL
          have hL' : L = [Obl.fml c false] := (Option.some.inj hL).symm
          subst hL'
          rw [satStack_one] at hS
          obtain ⟨x, hx, hxe⟩ := hS
          rw [nfB_false] at hxe
          subst hxe
          exact ⟨negFormulaCode x, by rw [Option.map_eq_some_iff]; exact ⟨(x, mid), hx, rfl⟩, hg⟩
        · rw [if_neg hg] at hL; exact absurd hL (by simp)
      · rintro ⟨d, hd, hde⟩
        rw [Option.map_eq_some_iff] at hd
        obtain ⟨⟨x1, x2⟩, hx, hq⟩ := hd
        rw [Prod.mk.injEq] at hq
        obtain ⟨rfl, rfl⟩ := hq
        have hinv : negFormulaCode (negFormulaCode x1) = x1 := invol_of_pfml hx
        have hxc : x1 = c := by rw [← hde, hinv]
        subst hxc
        rw [if_pos hinv]
        refine ⟨[Obl.fml x1 false], rfl, ?_⟩
        rw [satStack_one]
        exact ⟨x1, hx, rfl⟩

/-- The `⟹` token (`t = 21`), which the parser contracts into NNF as `¬x ∨ y`. -/
lemma key_fml_C21 (c : ℕ) (β : Bool) (ts mid : List ℕ) :
    (∃ L, oblStep (Obl.fml c β) 21 = some L ∧ SatStack L ts mid) ↔
      SatObl (Obl.fml c β) (21 :: ts) mid := by
  cases β with
  | false =>
    simp only [SatObl, pfml_cons, oblStep, nfB_false, Nat.reduceEqDiff, or_self, if_true,
      if_false, reduceCtorEq]
    constructor
    · rintro ⟨L, hL, hS⟩
      by_cases hc : c = 0
      · rw [if_pos hc] at hL; exact absurd hL (by simp)
      rw [if_neg hc] at hL
      by_cases h5 : (Nat.unpair (c - 1)).1 = 5
      · rw [if_pos h5] at hL
        obtain rfl : L = _ := (Option.some.inj hL).symm
        rw [satStack_two] at hS
        obtain ⟨m, ⟨x, hx, hxX⟩, ⟨y, hy, hyY⟩⟩ := hS
        simp only [nfB_true] at hxX
        simp only [nfB_false] at hyY
        refine ⟨c, ?_, rfl⟩
        rw [hx]
        show Option.map (fun q => (Nat.pair 5 (Nat.pair (negFormulaCode x) q.1) + 1, q.2)) (pfml m)
            = some (c, mid)
        rw [hy]
        show some (Nat.pair 5 (Nat.pair (negFormulaCode x) y) + 1, mid) = some (c, mid)
        congr 1
        simp only [Prod.mk.injEq, and_true]
        rw [hxX, hyY, Nat.pair_unpair, ← h5, pair_unpair_succ hc]
      · rw [if_neg h5] at hL; exact absurd hL (by simp)
    · rintro ⟨d, hd, rfl⟩
      rw [Option.bind_eq_some_iff] at hd
      obtain ⟨⟨x, m⟩, hx, hd⟩ := hd
      rw [Option.map_eq_some_iff] at hd
      obtain ⟨⟨y, r⟩, hy, hd⟩ := hd
      simp only [Prod.mk.injEq] at hd
      obtain ⟨rfl, rfl⟩ := hd
      have hc0 : Nat.pair 5 (Nat.pair (negFormulaCode x) y) + 1 ≠ 0 := by omega
      refine ⟨[Obl.fml (negFormulaCode x) true, Obl.fml y false], ?_, ?_⟩
      · simp only [if_neg hc0, unpair_pair_succ_fst, unpair_pair_succ_snd, Nat.unpair_pair,
          if_pos]
      · rw [satStack_two]
        exact ⟨m, ⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩⟩
  | true =>
    simp only [SatObl, pfml_cons, oblStep, nfB_true, Nat.reduceEqDiff, or_self, if_true,
      if_false]
    constructor
    · rintro ⟨L, hL, hS⟩
      by_cases hc : c = 0
      · rw [if_pos hc] at hL; exact absurd hL (by simp)
      rw [if_neg hc] at hL
      by_cases hg : (Nat.unpair (c - 1)).1 = 4 ∧
          negFormulaCode (negFormulaCode (Nat.unpair (Nat.unpair (c - 1)).2).1)
            = (Nat.unpair (Nat.unpair (c - 1)).2).1
      · obtain ⟨h4, hinv⟩ := hg
        rw [if_pos ⟨h4, hinv⟩] at hL
        obtain rfl : L = _ := (Option.some.inj hL).symm
        rw [satStack_two] at hS
        obtain ⟨m, ⟨x, hx, rfl⟩, ⟨y, hy, hyY⟩⟩ := hS
        simp only [nfB_true] at hyY
        refine ⟨Nat.pair 5 (Nat.pair (negFormulaCode (Nat.unpair (Nat.unpair (c - 1)).2).1) y) + 1,
          ?_, ?_⟩
        · rw [hx]
          show Option.map (fun q => (Nat.pair 5 (Nat.pair
              (negFormulaCode (Nat.unpair (Nat.unpair (c - 1)).2).1) q.1) + 1, q.2)) (pfml m)
              = some (Nat.pair 5 (Nat.pair
                (negFormulaCode (Nat.unpair (Nat.unpair (c - 1)).2).1) y) + 1, mid)
          rw [hy]
          rfl
        · rw [neg_tag5, hinv, hyY, Nat.pair_unpair, ← h4, pair_unpair_succ hc]
      · rw [if_neg hg] at hL; exact absurd hL (by simp)
    · rintro ⟨d, hd, rfl⟩
      rw [Option.bind_eq_some_iff] at hd
      obtain ⟨⟨x, m⟩, hx, hd⟩ := hd
      rw [Option.map_eq_some_iff] at hd
      obtain ⟨⟨y, r⟩, hy, hd⟩ := hd
      simp only [Prod.mk.injEq] at hd
      obtain ⟨rfl, rfl⟩ := hd
      have hinvx : negFormulaCode (negFormulaCode x) = x := invol_of_pfml hx
      have hcval : negFormulaCode (Nat.pair 5 (Nat.pair (negFormulaCode x) y) + 1)
          = Nat.pair 4 (Nat.pair x (negFormulaCode y)) + 1 := by rw [neg_tag5, hinvx]
      rw [hcval]
      have hc0 : Nat.pair 4 (Nat.pair x (negFormulaCode y)) + 1 ≠ 0 := by omega
      refine ⟨[Obl.fml x false, Obl.fml (negFormulaCode y) true], ?_, ?_⟩
      · simp only [if_neg hc0, unpair_pair_succ_fst, unpair_pair_succ_snd, Nat.unpair_pair,
          hinvx, and_self, if_pos]
      · rw [satStack_two]
        exact ⟨m, ⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩⟩

/-- The `⟺` token (`t = 22`), which the parser expands into the NNF conjunction of the two
contracted implications. -/
lemma key_fml_C22 (c : ℕ) (β : Bool) (ts mid : List ℕ) :
    (∃ L, oblStep (Obl.fml c β) 22 = some L ∧ SatStack L ts mid) ↔
      SatObl (Obl.fml c β) (22 :: ts) mid := by
  cases β with
  | false =>
    simp only [SatObl, pfml_cons, oblStep, nfB_false, Nat.reduceEqDiff, or_self, if_true,
      if_false, reduceCtorEq]
    constructor
    · rintro ⟨L, hL, hS⟩
      by_cases hc : c = 0
      · rw [if_pos hc] at hL; exact absurd hL (by simp)
      rw [if_neg hc] at hL
      set A := (Nat.unpair (Nat.unpair (c - 1)).2).1 with hAdef
      set B := (Nat.unpair (Nat.unpair (c - 1)).2).2 with hBdef
      set X := (Nat.unpair (Nat.unpair (A - 1)).2).1 with hXdef
      set Y := (Nat.unpair (Nat.unpair (A - 1)).2).2 with hYdef
      set Z := (Nat.unpair (Nat.unpair (B - 1)).2).1 with hZdef
      set W := (Nat.unpair (Nat.unpair (B - 1)).2).2 with hWdef
      by_cases hz : A = 0 ∨ B = 0
      · rw [if_pos hz] at hL; exact absurd hL (by simp)
      rw [if_neg hz] at hL
      rw [not_or] at hz
      by_cases hg : (Nat.unpair (c - 1)).1 = 4 ∧ (Nat.unpair (A - 1)).1 = 5 ∧
          (Nat.unpair (B - 1)).1 = 5 ∧ X = negFormulaCode W ∧ Z = negFormulaCode Y
      · obtain ⟨h4, hA5, hB5, hXW, hZY⟩ := hg
        rw [if_pos ⟨h4, hA5, hB5, hXW, hZY⟩] at hL
        obtain rfl : L = _ := (Option.some.inj hL).symm
        rw [satStack_two] at hS
        obtain ⟨m, ⟨w, hw, rfl⟩, ⟨y, hy, rfl⟩⟩ := hS
        have eA : Nat.pair 5 (Nat.pair X Y) + 1 = A := by
          rw [hXdef, hYdef, Nat.pair_unpair, ← hA5, pair_unpair_succ hz.1]
        have eB : Nat.pair 5 (Nat.pair Z W) + 1 = B := by
          rw [hZdef, hWdef, Nat.pair_unpair, ← hB5, pair_unpair_succ hz.2]
        have eC : Nat.pair 4 (Nat.pair A B) + 1 = c := by
          rw [hAdef, hBdef, Nat.pair_unpair, ← h4, pair_unpair_succ hc]
        refine ⟨c, ?_, rfl⟩
        rw [hw]
        show Option.map (fun q => (Nat.pair 4
              (Nat.pair (Nat.pair 5 (Nat.pair (negFormulaCode W) q.1) + 1)
                (Nat.pair 5 (Nat.pair (negFormulaCode q.1) W) + 1)) + 1, q.2)) (pfml m)
            = some (c, mid)
        rw [hy]
        show some (Nat.pair 4 (Nat.pair (Nat.pair 5 (Nat.pair (negFormulaCode W) Y) + 1)
              (Nat.pair 5 (Nat.pair (negFormulaCode Y) W) + 1)) + 1, mid) = some (c, mid)
        rw [← hXW, ← hZY, eA, eB, eC]
      · rw [if_neg hg] at hL; exact absurd hL (by simp)
    · rintro ⟨d, hd, rfl⟩
      rw [Option.bind_eq_some_iff] at hd
      obtain ⟨⟨x, m⟩, hx, hd⟩ := hd
      rw [Option.map_eq_some_iff] at hd
      obtain ⟨⟨y, r⟩, hy, hd⟩ := hd
      simp only [Prod.mk.injEq] at hd
      obtain ⟨rfl, rfl⟩ := hd
      have hc0 : Nat.pair 4 (Nat.pair (Nat.pair 5 (Nat.pair (negFormulaCode x) y) + 1)
          (Nat.pair 5 (Nat.pair (negFormulaCode y) x) + 1)) + 1 ≠ 0 := by omega
      refine ⟨[Obl.fml x false, Obl.fml y false], ?_, ?_⟩
      · rw [if_neg hc0]
        simp only [unpair_pair_succ_fst, unpair_pair_succ_snd, Nat.unpair_pair]
        rw [if_neg (show ¬(Nat.pair 5 (Nat.pair (negFormulaCode x) y) + 1 = 0 ∨
          Nat.pair 5 (Nat.pair (negFormulaCode y) x) + 1 = 0) by omega)]
        simp only [and_self, if_true]
      · rw [satStack_two]
        exact ⟨m, ⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩⟩
  | true =>
    simp only [SatObl, pfml_cons, oblStep, nfB_true, Nat.reduceEqDiff, or_self, if_true,
      if_false]
    constructor
    · rintro ⟨L, hL, hS⟩
      by_cases hc : c = 0
      · rw [if_pos hc] at hL; exact absurd hL (by simp)
      rw [if_neg hc] at hL
      set A := (Nat.unpair (Nat.unpair (c - 1)).2).1 with hAdef
      set B := (Nat.unpair (Nat.unpair (c - 1)).2).2 with hBdef
      set X := (Nat.unpair (Nat.unpair (A - 1)).2).1 with hXdef
      set Y := (Nat.unpair (Nat.unpair (A - 1)).2).2 with hYdef
      set Z := (Nat.unpair (Nat.unpair (B - 1)).2).1 with hZdef
      set W := (Nat.unpair (Nat.unpair (B - 1)).2).2 with hWdef
      by_cases hz : A = 0 ∨ B = 0
      · rw [if_pos hz] at hL; exact absurd hL (by simp)
      rw [if_neg hz] at hL
      rw [not_or] at hz
      by_cases hg : (Nat.unpair (c - 1)).1 = 5 ∧ (Nat.unpair (A - 1)).1 = 4 ∧
          (Nat.unpair (B - 1)).1 = 4 ∧ Y = negFormulaCode Z ∧ W = negFormulaCode X ∧
          negFormulaCode (negFormulaCode X) = X ∧ negFormulaCode (negFormulaCode Z) = Z
      · obtain ⟨h5, hA4, hB4, hYZ, hWX, hinvX, hinvZ⟩ := hg
        rw [if_pos ⟨h5, hA4, hB4, hYZ, hWX, hinvX, hinvZ⟩] at hL
        obtain rfl : L = _ := (Option.some.inj hL).symm
        rw [satStack_two] at hS
        obtain ⟨m, ⟨x, hx, rfl⟩, ⟨z, hzz, rfl⟩⟩ := hS
        have eA : Nat.pair 4 (Nat.pair X Y) + 1 = A := by
          rw [hXdef, hYdef, Nat.pair_unpair, ← hA4, pair_unpair_succ hz.1]
        have eB : Nat.pair 4 (Nat.pair Z W) + 1 = B := by
          rw [hZdef, hWdef, Nat.pair_unpair, ← hB4, pair_unpair_succ hz.2]
        have eC : Nat.pair 5 (Nat.pair A B) + 1 = c := by
          rw [hAdef, hBdef, Nat.pair_unpair, ← h5, pair_unpair_succ hc]
        have eA0 : negFormulaCode (Nat.pair 5 (Nat.pair (negFormulaCode X) Z) + 1) = A := by
          rw [neg_tag5, hinvX, ← hYZ, eA]
        have eB0 : negFormulaCode (Nat.pair 5 (Nat.pair (negFormulaCode Z) X) + 1) = B := by
          rw [neg_tag5, hinvZ, ← hWX, eB]
        refine ⟨Nat.pair 4 (Nat.pair (Nat.pair 5 (Nat.pair (negFormulaCode X) Z) + 1)
          (Nat.pair 5 (Nat.pair (negFormulaCode Z) X) + 1)) + 1, ?_, ?_⟩
        · rw [hx]
          show Option.map (fun q => (Nat.pair 4
                (Nat.pair (Nat.pair 5 (Nat.pair (negFormulaCode X) q.1) + 1)
                  (Nat.pair 5 (Nat.pair (negFormulaCode q.1) X) + 1)) + 1, q.2)) (pfml m)
              = some (Nat.pair 4 (Nat.pair (Nat.pair 5 (Nat.pair (negFormulaCode X) Z) + 1)
                  (Nat.pair 5 (Nat.pair (negFormulaCode Z) X) + 1)) + 1, mid)
          rw [hzz]
          rfl
        · rw [neg_tag4, eA0, eB0, eC]
      · rw [if_neg hg] at hL; exact absurd hL (by simp)
    · rintro ⟨d, hd, rfl⟩
      rw [Option.bind_eq_some_iff] at hd
      obtain ⟨⟨x, m⟩, hx, hd⟩ := hd
      rw [Option.map_eq_some_iff] at hd
      obtain ⟨⟨y, r⟩, hy, hd⟩ := hd
      simp only [Prod.mk.injEq] at hd
      obtain ⟨rfl, rfl⟩ := hd
      have hinvx : negFormulaCode (negFormulaCode x) = x := invol_of_pfml hx
      have hinvy : negFormulaCode (negFormulaCode y) = y := invol_of_pfml hy
      have hcval : negFormulaCode (Nat.pair 4
            (Nat.pair (Nat.pair 5 (Nat.pair (negFormulaCode x) y) + 1)
              (Nat.pair 5 (Nat.pair (negFormulaCode y) x) + 1)) + 1)
          = Nat.pair 5 (Nat.pair (Nat.pair 4 (Nat.pair x (negFormulaCode y)) + 1)
              (Nat.pair 4 (Nat.pair y (negFormulaCode x)) + 1)) + 1 := by
        rw [neg_tag4, neg_tag5, neg_tag5, hinvx, hinvy]
      rw [hcval]
      have hc0 : Nat.pair 5 (Nat.pair (Nat.pair 4 (Nat.pair x (negFormulaCode y)) + 1)
          (Nat.pair 4 (Nat.pair y (negFormulaCode x)) + 1)) + 1 ≠ 0 := by omega
      refine ⟨[Obl.fml x false, Obl.fml y false], ?_, ?_⟩
      · rw [if_neg hc0]
        simp only [unpair_pair_succ_fst, unpair_pair_succ_snd, Nat.unpair_pair]
        rw [if_neg (show ¬(Nat.pair 4 (Nat.pair x (negFormulaCode y)) + 1 = 0 ∨
          Nat.pair 4 (Nat.pair y (negFormulaCode x)) + 1 = 0) by omega)]
        simp only [hinvx, hinvy, and_self, if_true]
      · rw [satStack_two]
        exact ⟨m, ⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩⟩

lemma key_fml_C (c : ℕ) (β : Bool) (t : ℕ) (ht : t = 21 ∨ t = 22) (ts mid : List ℕ) :
    (∃ L, oblStep (Obl.fml c β) t = some L ∧ SatStack L ts mid) ↔
      SatObl (Obl.fml c β) (t :: ts) mid := by
  rcases ht with rfl | rfl
  · exact key_fml_C21 c β ts mid
  · exact key_fml_C22 c β ts mid

lemma key_fml_D (c : ℕ) (β : Bool) (t : ℕ)
    (ht : ¬ (t = 9 ∨ t = 10 ∨ t = 11 ∨ t = 12 ∨ t = 13 ∨ t = 14 ∨ t = 15 ∨ t = 16 ∨ t = 17
      ∨ t = 18 ∨ t = 20 ∨ t = 21 ∨ t = 22)) (ts mid : List ℕ) :
    (∃ L, oblStep (Obl.fml c β) t = some L ∧ SatStack L ts mid) ↔
      SatObl (Obl.fml c β) (t :: ts) mid := by
  simp only [not_or] at ht
  obtain ⟨h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h20, h21, h22⟩ := ht
  simp only [SatObl, pfml_cons, oblStep, if_neg h9, if_neg h10,
    if_neg (show ¬ (t = 11 ∨ t = 12 ∨ t = 13 ∨ t = 14) by tauto),
    if_neg (show ¬ (t = 15 ∨ t = 16) by tauto),
    if_neg (show ¬ (t = 17 ∨ t = 18) by tauto), if_neg h20, if_neg h21, if_neg h22]
  by_cases hc : c = 0
  · simp only [if_pos hc]
    constructor
    · rintro ⟨L, hL, -⟩; exact absurd hL (by simp)
    · rintro ⟨d, hd, -⟩; exact absurd hd (by simp)
  · simp only [if_neg hc]
    constructor
    · rintro ⟨L, hL, -⟩; exact absurd hL (by simp)
    · rintro ⟨d, hd, -⟩; exact absurd hd (by simp)

lemma key (o : Obl) (t : ℕ) (ts mid : List ℕ) :
    (∃ L, oblStep o t = some L ∧ SatStack L ts mid) ↔ SatObl o (t :: ts) mid := by
  cases o with
  | num n => exact key_num n t ts mid
  | trm c => exact key_trm c t ts mid
  | fml c β =>
      by_cases ht : t = 9 ∨ t = 10 ∨ t = 11 ∨ t = 12 ∨ t = 13 ∨ t = 14
      · exact key_fml_A c β t ht ts mid
      by_cases ht2 : t = 15 ∨ t = 16 ∨ t = 17 ∨ t = 18 ∨ t = 20
      · exact key_fml_B c β t ht2 ts mid
      by_cases ht3 : t = 21 ∨ t = 22
      · exact key_fml_C c β t ht3 ts mid
      · exact key_fml_D c β t (by tauto) ts mid

lemma satObl_nil (o : Obl) (mid : List ℕ) : ¬ SatObl o [] mid := by
  cases o <;> simp [SatObl, pnat_nil, ptrm_nil, pfml_nil]

lemma satStack_nil_input (S : List Obl) (mid : List ℕ) :
    SatStack S [] mid ↔ (S = [] ∧ mid = []) := by
  cases S with
  | nil => simp [SatStack]
  | cons o S =>
      simp only [SatStack]
      constructor
      · rintro ⟨m, hm, -⟩; exact absurd hm (satObl_nil o m)
      · rintro ⟨h, -⟩; exact absurd h (by simp)

lemma stackRun_iff : ∀ (ts : List ℕ) (S : List Obl),
    stackRun S ts = some [] ↔ SatStack S ts [] := by
  intro ts
  induction ts with
  | nil =>
      intro S
      rw [stackRun, satStack_nil_input]
      constructor
      · intro h; exact ⟨Option.some.inj h, rfl⟩
      · rintro ⟨rfl, -⟩; rfl
  | cons t ts ih =>
      intro S
      cases S with
      | nil =>
          rw [stackRun, stackStep]
          simp [SatStack]
      | cons o S =>
          rw [stackRun, stackStep]
          simp only [Option.map_eq_some_iff, Option.bind_eq_some_iff, SatStack]
          constructor
          · rintro ⟨S', ⟨L, hL, rfl⟩, hrun⟩
            rw [ih] at hrun
            rw [satStack_append] at hrun
            obtain ⟨m, h1, h2⟩ := hrun
            exact ⟨m, (key o t ts m).mp ⟨L, hL, h1⟩, h2⟩
          · rintro ⟨m, ho, hS⟩
            obtain ⟨L, hL, h1⟩ := (key o t ts m).mpr ho
            refine ⟨L ++ S, ⟨L, hL, rfl⟩, ?_⟩
            rw [ih, satStack_append]
            exact ⟨m, h1, hS⟩

def payAccepts (fc : ℕ) (p : List ℕ) : Bool :=
  decide (stackRun [Obl.fml fc false] p = some [])

/-- **The obligation stack decides the payload language of one fixed formula code.**

Proof kind: `C` composition.  Provenance: (a) `stackRun_iff`.
Paper node: `app:ifp` -/
lemma payAccepts_iff (fc : ℕ) (p : List ℕ) :
    payAccepts fc p = true ↔
      parseStructuredArithmeticFormula p.length 0 p = some (fc, []) := by
  rw [payAccepts, decide_eq_true_iff, stackRun_iff]
  simp only [SatStack, SatObl, nfB_false]
  constructor
  · rintro ⟨m, ⟨d, hd, rfl⟩, rfl⟩; exact hd
  · intro h; exact ⟨[], ⟨fc, h, rfl⟩, rfl⟩

/-- **A complete structured payload parse never contains the block terminator.**

This is what makes a structured block self-delimiting, and it is consumed by
`SegCtr.segMatch_iff_relaxed_and_ctr`.

Proof kind: `C` composition.  Provenance: (b)
`parseStructuredArithmeticFormula_consumed_lt`.
Paper node: `app:ifp` -/
lemma nineteen_not_mem_of_parse {p : List ℕ} {c : ℕ}
    (h : parseStructuredArithmeticFormula p.length 0 p = some (c, [])) : 19 ∉ p := by
  obtain ⟨w, hw, hne⟩ := parseStructuredArithmeticFormula_consumed_lt h
  rw [List.append_nil] at hw
  subst hw
  exact fun hmem => hne 19 hmem rfl

/-! ## Finite state packaging -/

def phi : List Obl → ℕ
  | [] => 0
  | o :: S => o.code + 1 + phi S

lemma phi_append (L S : List Obl) : phi (L ++ S) = phi L + phi S := by
  induction L with
  | nil => simp [phi]
  | cons o L ih => simp only [List.cons_append, phi, ih]; omega

lemma oblStep_phi {o : Obl} {t : ℕ} {L : List Obl} (h : oblStep o t = some L) :
    phi L ≤ o.code + 1 := by
  cases o with
  | num n =>
      simp only [oblStep] at h
      split_ifs at h <;>
        (obtain rfl := (Option.some.inj h).symm; simp only [phi, Obl.code]; omega)
  | trm c =>
      by_cases hc : c = 0
      · simp only [oblStep, if_pos hc] at h; simp at h
      simp only [oblStep, if_neg hc] at h
      have hA : (c - 1).unpair.2.unpair.2.unpair.2 ≤ c - 1 :=
        le_trans (Nat.unpair_right_le _) (le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _))
      have h2 : ((c - 1).unpair.2.unpair.2.unpair.2 - 1).unpair.1
            + ((c - 1).unpair.2.unpair.2.unpair.2 - 1).unpair.2
          ≤ (c - 1).unpair.2.unpair.2.unpair.2 - 1 := Nat.unpair_add_le _
      have h3 : (((c - 1).unpair.2.unpair.2.unpair.2 - 1).unpair.2 - 1).unpair.1
          ≤ ((c - 1).unpair.2.unpair.2.unpair.2 - 1).unpair.2 - 1 := Nat.unpair_left_le _
      have hb : (c - 1).unpair.2 ≤ c - 1 := Nat.unpair_right_le _
      split_ifs at h <;>
        (obtain rfl := (Option.some.inj h).symm; simp only [phi, Obl.code]; omega)
  | fml c β =>
      by_cases hc : c = 0
      · simp only [oblStep, if_pos hc] at h; simp at h
      simp only [oblStep, if_neg hc] at h
      have hA : (c - 1).unpair.2.unpair.2.unpair.2 ≤ c - 1 :=
        le_trans (Nat.unpair_right_le _) (le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _))
      have h2 : ((c - 1).unpair.2.unpair.2.unpair.2 - 1).unpair.1
            + ((c - 1).unpair.2.unpair.2.unpair.2 - 1).unpair.2
          ≤ (c - 1).unpair.2.unpair.2.unpair.2 - 1 := Nat.unpair_add_le _
      have h3 : (((c - 1).unpair.2.unpair.2.unpair.2 - 1).unpair.2 - 1).unpair.1
          ≤ ((c - 1).unpair.2.unpair.2.unpair.2 - 1).unpair.2 - 1 := Nat.unpair_left_le _
      have hb : (c - 1).unpair.2 ≤ c - 1 := Nat.unpair_right_le _
      have hc1 : 1 ≤ c := Nat.one_le_iff_ne_zero.mpr hc
      have hpq : (c - 1).unpair.2.unpair.1 + (c - 1).unpair.2.unpair.2 ≤ (c - 1).unpair.2 :=
        Nat.unpair_add_le _
      have hAA : ((c - 1).unpair.2.unpair.1 - 1).unpair.2.unpair.1
          ≤ (c - 1).unpair.2.unpair.1 - 1 :=
        le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _)
      have hAB : ((c - 1).unpair.2.unpair.1 - 1).unpair.2.unpair.2
          ≤ (c - 1).unpair.2.unpair.1 - 1 :=
        le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _)
      have hBA : ((c - 1).unpair.2.unpair.2 - 1).unpair.2.unpair.1
          ≤ (c - 1).unpair.2.unpair.2 - 1 :=
        le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _)
      have hBB : ((c - 1).unpair.2.unpair.2 - 1).unpair.2.unpair.2
          ≤ (c - 1).unpair.2.unpair.2 - 1 :=
        le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _)
      by_cases h9 : t = 9
      · rw [if_pos h9] at h
        split_ifs at h <;>
          (obtain rfl := (Option.some.inj h).symm; simp only [phi, Obl.code]; omega)
      rw [if_neg h9] at h
      by_cases h10 : t = 10
      · rw [if_pos h10] at h
        split_ifs at h <;>
          (obtain rfl := (Option.some.inj h).symm; simp only [phi, Obl.code]; omega)
      rw [if_neg h10] at h
      by_cases h11 : t = 11 ∨ t = 12 ∨ t = 13 ∨ t = 14
      · rw [if_pos h11] at h
        split_ifs at h <;>
          (obtain rfl := (Option.some.inj h).symm; simp only [phi, Obl.code]; omega)
      rw [if_neg h11] at h
      by_cases h15 : t = 15 ∨ t = 16
      · rw [if_pos h15] at h
        split_ifs at h <;>
          (obtain rfl := (Option.some.inj h).symm; simp only [phi, Obl.code]; omega)
      rw [if_neg h15] at h
      by_cases h17 : t = 17 ∨ t = 18
      · rw [if_pos h17] at h
        split_ifs at h <;>
          (obtain rfl := (Option.some.inj h).symm; simp only [phi, Obl.code]; omega)
      rw [if_neg h17] at h
      by_cases h20 : t = 20
      · rw [if_pos h20] at h
        split_ifs at h <;>
          (obtain rfl := (Option.some.inj h).symm; simp only [phi, Obl.code]; omega)
      rw [if_neg h20] at h
      by_cases h21 : t = 21
      · rw [if_pos h21] at h
        split_ifs at h <;>
          (obtain rfl := (Option.some.inj h).symm; simp only [phi, Obl.code]; omega)
      rw [if_neg h21] at h
      by_cases h22 : t = 22
      · rw [if_pos h22] at h
        split_ifs at h <;>
          (obtain rfl := (Option.some.inj h).symm; simp only [phi, Obl.code]; omega)
      rw [if_neg h22] at h
      simp at h

lemma stackStep_phi {S S' : List Obl} {t : ℕ} (h : stackStep S t = some S') :
    phi S' ≤ phi S := by
  cases S with
  | nil => simp only [stackStep] at h; simp at h
  | cons o S =>
      rw [stackStep, Option.map_eq_some_iff] at h
      obtain ⟨L, hL, rfl⟩ := h
      rw [phi_append, phi]
      have := oblStep_phi hL
      omega

lemma stackRun_phi : ∀ (ts : List ℕ) {S S' : List Obl},
    stackRun S ts = some S' → phi S' ≤ phi S := by
  intro ts
  induction ts with
  | nil => intro S S' h; rw [stackRun] at h; rw [Option.some.inj h]
  | cons t ts ih =>
      intro S S' h
      rw [stackRun, Option.bind_eq_some_iff] at h
      obtain ⟨S'', h1, h2⟩ := h
      exact le_trans (ih h2) (stackStep_phi h1)

/-! ### The finite state set -/

def oblAlphabet (fc : ℕ) : List Obl :=
  (List.range (fc + 1)).flatMap fun c => [Obl.num c, Obl.trm c, Obl.fml c false, Obl.fml c true]

def stacksUpTo (alph : List Obl) : ℕ → List (List Obl)
  | 0 => [[]]
  | k + 1 => stacksUpTo alph k ++ alph.flatMap fun o => (stacksUpTo alph k).map (fun S => o :: S)

def payStacks (fc : ℕ) : List (List Obl) := stacksUpTo (oblAlphabet fc) (fc + 1)

lemma mem_oblAlphabet {fc : ℕ} {o : Obl} (h : o.code ≤ fc) : o ∈ oblAlphabet fc := by
  have hr : o.code ∈ List.range (fc + 1) := List.mem_range.mpr (by omega)
  refine List.mem_flatMap.mpr ⟨o.code, hr, ?_⟩
  cases o with
  | num n => simp [Obl.code]
  | trm c => simp [Obl.code]
  | fml c β => cases β <;> simp [Obl.code]

lemma mem_stacksUpTo {alph : List Obl} : ∀ {k : ℕ} {S : List Obl},
    S.length ≤ k → (∀ o ∈ S, o ∈ alph) → S ∈ stacksUpTo alph k := by
  intro k
  induction k with
  | zero =>
      intro S hlen _
      have : S = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
      subst this
      simp [stacksUpTo]
  | succ k ih =>
      intro S hlen hmem
      cases S with
      | nil => exact List.mem_append_left _ (ih (Nat.zero_le _) (by simp))
      | cons o S =>
          refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨o, hmem o (by simp), ?_⟩)
          refine List.mem_map.mpr ⟨S, ih ?_ ?_, rfl⟩
          · simpa using hlen
          · exact fun x hx => hmem x (List.mem_cons_of_mem _ hx)

lemma length_le_phi (S : List Obl) : S.length ≤ phi S := by
  induction S with
  | nil => simp [phi]
  | cons o S ih => simp only [List.length_cons, phi]; omega

lemma code_add_one_le_phi {S : List Obl} {o : Obl} (h : o ∈ S) : o.code + 1 ≤ phi S := by
  induction S with
  | nil => simp at h
  | cons a S ih =>
      rcases List.mem_cons.mp h with rfl | h'
      · simp only [phi]; omega
      · have := ih h'; simp only [phi]; omega

lemma mem_payStacks {fc : ℕ} {S : List Obl} (h : phi S ≤ fc + 1) : S ∈ payStacks fc := by
  refine mem_stacksUpTo (le_trans (length_le_phi S) h) (fun o ho => mem_oblAlphabet ?_)
  have := code_add_one_le_phi ho
  omega

/-! ### The automaton -/

def payQ (fc : ℕ) : ℕ := (payStacks fc).length

def payIdx (fc : ℕ) (S : List Obl) : ℕ := (payStacks fc).idxOf S

def payInit (fc : ℕ) : ℕ := payIdx fc [Obl.fml fc false]

def payStep (fc : ℕ) (i t : ℕ) : ℕ :=
  match (payStacks fc)[i]? with
  | none => payQ fc
  | some S =>
      match stackStep S t with
      | none => payQ fc
      | some S' => payIdx fc S'

def payAcceptState (fc : ℕ) (i : ℕ) : Bool :=
  match (payStacks fc)[i]? with
  | none => false
  | some S => S.isEmpty

lemma payIdx_le (fc : ℕ) (S : List Obl) : payIdx fc S ≤ payQ fc := List.idxOf_le_length

lemma payStep_le (fc : ℕ) : ∀ i t, i ≤ payQ fc → payStep fc i t ≤ payQ fc := by
  intro i t _
  rw [payStep]
  split
  · exact le_refl _
  · split
    · exact le_refl _
    · exact payIdx_le fc _

lemma payInit_le (fc : ℕ) : payInit fc ≤ payQ fc := payIdx_le fc _

lemma getElem?_payIdx {fc : ℕ} {S : List Obl} (h : S ∈ payStacks fc) :
    (payStacks fc)[payIdx fc S]? = some S := by
  have hlt : (payStacks fc).idxOf S < (payStacks fc).length := List.idxOf_lt_length_of_mem h
  rw [payIdx, List.getElem?_eq_getElem hlt]
  exact congrArg some (List.getElem_idxOf hlt)

lemma payStep_of_mem {fc : ℕ} {S : List Obl} (h : S ∈ payStacks fc) (t : ℕ) :
    payStep fc (payIdx fc S) t =
      match stackStep S t with
      | none => payQ fc
      | some S' => payIdx fc S' := by
  rw [payStep, getElem?_payIdx h]

lemma getElem?_payQ (fc : ℕ) : (payStacks fc)[payQ fc]? = none :=
  List.getElem?_eq_none_iff.mpr (le_refl _)

lemma payStep_payQ (fc t : ℕ) : payStep fc (payQ fc) t = payQ fc := by
  rw [payStep, getElem?_payQ]

lemma foldl_payQ (fc : ℕ) : ∀ ts : List ℕ, ts.foldl (payStep fc) (payQ fc) = payQ fc := by
  intro ts
  induction ts with
  | nil => rfl
  | cons t ts ih => rw [List.foldl_cons, payStep_payQ]; exact ih

lemma payFold_spec (fc : ℕ) : ∀ (ts : List ℕ) (S : List Obl), phi S ≤ fc + 1 →
    ts.foldl (payStep fc) (payIdx fc S) =
      match stackRun S ts with
      | some S' => payIdx fc S'
      | none => payQ fc := by
  intro ts
  induction ts with
  | nil => intro S _; rw [List.foldl_nil, stackRun]
  | cons t ts ih =>
      intro S hS
      rw [List.foldl_cons, payStep_of_mem (mem_payStacks hS), stackRun]
      cases hst : stackStep S t with
      | none => exact foldl_payQ fc ts
      | some S' => exact ih S' (le_trans (stackStep_phi hst) hS)

/-- **The same decision, packaged as a finite-state fold.**

Control states are indices into `payStacks fc`, which the potential argument shows is
exhaustive; `payQ fc` is the absorbing reject state.  This is the form
`SegAuto.PayRec` consumes.

Proof kind: `C` composition.  Provenance: (a) `payAccepts_iff`, `payFold_spec`.
Paper node: `app:ifp` -/
lemma payAuto_iff (fc : ℕ) (p : List ℕ) :
    payAcceptState fc (p.foldl (payStep fc) (payInit fc)) = true ↔
      parseStructuredArithmeticFormula p.length 0 p = some (fc, []) := by
  have hinit : phi [Obl.fml fc false] ≤ fc + 1 := by simp [phi, Obl.code]
  rw [payInit, payFold_spec fc p _ hinit, ← payAccepts_iff, payAccepts, decide_eq_true_iff]
  cases hr : stackRun [Obl.fml fc false] p with
  | none =>
      simp only [payAcceptState, getElem?_payQ]
      simp
  | some S' =>
      have hmem : S' ∈ payStacks fc :=
        mem_payStacks (le_trans (stackRun_phi p hr) hinit)
      simp only [payAcceptState, getElem?_payIdx hmem]
      constructor
      · intro h
        have : S' = [] := List.eq_nil_of_length_eq_zero (by simpa using List.isEmpty_iff.mp h)
        rw [this]
      · intro h
        have : S' = [] := Option.some.inj h
        subst this
        rfl

end LogicalInduction.PayAuto
