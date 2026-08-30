/-
# Primitive recursion for the RPN contraction

`unRpn` (through its code-level form `unRpnTokensC`) is primitive recursive: the
trading firm's compiler runs it to decode symbol-metered candidate traders.  Both
fuelled recursions are packaged for `Primrec.nat_strong_rec` on the paired index
`⟨fuel, encode ts⟩`; recursive calls strictly decrease it because every sub-parse
returns a suffix (list codes grow strictly along `cons`).

Paper node: `def:ec` (symbol-metered sentence slots).
-/
import LogicalInduction.Framework.Computable
import LogicalInduction.Framework.RpnSentence

namespace LogicalInduction

open Encodable LO.Propositional

/-! ## Suffix discipline of the parser -/

lemma parseRpn_suffix : ∀ (fuel : ℕ) (ts : List ℕ) (φ : Sentence) (rest : List ℕ),
    parseRpn fuel ts = some (φ, rest) → rest <:+ ts
  | 0, ts, φ, rest => by simp
  | fuel + 1, [], φ, rest => by simp
  | fuel + 1, t :: ts, φ, rest => by
      intro h
      rw [parseRpn_cons] at h
      by_cases h0 : t = 0
      · rw [if_pos h0] at h
        obtain ⟨-, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
        exact (List.suffix_cons t ts)
      rw [if_neg h0] at h
      by_cases h1 : t = 1
      · rw [if_pos h1] at h
        rcases ts with _ | ⟨c, ts'⟩
        · simp at h
        cases c with
        | zero =>
            exact (parseStructuredPaperPrime_suffix h).trans
              ((List.suffix_cons 0 ts').trans (List.suffix_cons t (0 :: ts')))
        | succ c =>
            rcases hdec : Encodable.decode (α := Sentence) (c + 1) with _ | ψ
            · simp [hdec] at h
            · simp only [hdec, Option.map_some] at h
              obtain ⟨-, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
              exact (List.suffix_cons (c + 1) ts').trans
                (List.suffix_cons t ((c + 1) :: ts'))
      rw [if_neg h1] at h
      have hbin : ∀ (mk : Sentence → Sentence → Sentence),
          ((parseRpn fuel ts).bind fun p =>
            (parseRpn fuel p.2).bind fun q =>
              some (mk p.1 q.1, q.2)) = some (φ, rest) →
          rest <:+ t :: ts := by
        intro mk hb
        rcases hp1 : parseRpn fuel ts with _ | ⟨φ1, r1⟩
        · rw [hp1] at hb
          simp at hb
        rw [hp1] at hb
        simp only [Option.bind_some] at hb
        rcases hp2 : parseRpn fuel r1 with _ | ⟨φ2, r2⟩
        · rw [hp2] at hb
          simp at hb
        rw [hp2] at hb
        simp only [Option.bind_some] at hb
        obtain ⟨-, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hb
        exact ((parseRpn_suffix fuel r1 φ2 r2 hp2).trans
          (parseRpn_suffix fuel ts φ1 r1 hp1)).trans (List.suffix_cons t ts)
      by_cases h2 : t = 2
      · rw [if_pos h2] at h
        exact hbin Formula.imp h
      rw [if_neg h2] at h
      by_cases h3 : t = 3
      · rw [if_pos h3] at h
        exact hbin Formula.and h
      rw [if_neg h3] at h
      by_cases h4 : t = 4
      · rw [if_pos h4] at h
        exact hbin Formula.or h
      rw [if_neg h4] at h
      obtain ⟨-, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
      exact (List.suffix_cons t ts)

lemma parseRpnC_suffix {fuel : ℕ} {ts : List ℕ} {e : ℕ} {rest : List ℕ}
    (h : parseRpnC fuel ts = some (e, rest)) : rest <:+ ts := by
  rw [parseRpnC_eq] at h
  rcases hp : parseRpn fuel ts with _ | ⟨φ, r⟩
  · rw [hp] at h
    simp at h
  · rw [hp] at h
    simp only [Option.map_some] at h
    obtain ⟨-, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
    exact parseRpn_suffix fuel ts φ r hp

/-! ## List codes grow along `cons` and shrink along suffixes -/

lemma encode_lt_encode_cons (a : ℕ) (l : List ℕ) :
    Encodable.encode l < Encodable.encode (a :: l) := by
  rw [Encodable.encode_list_cons]
  have := Nat.right_le_pair (Encodable.encode a) (Encodable.encode l)
  omega

lemma encode_le_of_suffix : ∀ {l₁ l₂ : List ℕ}, l₁ <:+ l₂ →
    Encodable.encode l₁ ≤ Encodable.encode l₂ := by
  intro l₁ l₂ h
  obtain ⟨p, rfl⟩ := h
  induction p with
  | nil => simp
  | cons a p ih =>
      calc Encodable.encode l₁ ≤ Encodable.encode (p ++ l₁) := ih
        _ ≤ Encodable.encode (a :: (p ++ l₁)) :=
            le_of_lt (encode_lt_encode_cons a _)
        _ = Encodable.encode ((a :: p) ++ l₁) := rfl

/-! ## Strong recursion for the structured natural decoder -/

public def structuredNatF (m : ℕ) : Option (ℕ × List ℕ) :=
  parseStructuredNat m.unpair.1 (Denumerable.ofNat (List ℕ) m.unpair.2)

public def structuredNatGCore (m : ℕ) (look : ℕ → Option (ℕ × List ℕ)) :
    Option (ℕ × List ℕ) :=
  match m.unpair.1, Denumerable.ofNat (List ℕ) m.unpair.2 with
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, t :: rest =>
      if t = 0 then some (0, rest)
      else if t = 1 then
        (look (Nat.pair fuel (Encodable.encode rest))).map fun p => (2 * p.1, p.2)
      else if t = 2 then
        (look (Nat.pair fuel (Encodable.encode rest))).map fun p => (2 * p.1 + 1, p.2)
      else none

private lemma structured_smaller_index {m fuel t rest}
    (hfuel : m.unpair.1 = fuel + 1)
    (hts : Denumerable.ofNat (List ℕ) m.unpair.2 = t :: rest) :
    Nat.pair fuel (Encodable.encode rest) < m := by
  have hm2 : Encodable.encode (t :: rest) = m.unpair.2 := by
    rw [← hts]
    exact Denumerable.encode_ofNat _
  calc
    Nat.pair fuel (Encodable.encode rest) ≤
        Nat.pair fuel (Encodable.encode (t :: rest)) :=
      pair_le_pair_right' fuel (le_of_lt (encode_lt_encode_cons t rest))
    _ < Nat.pair (fuel + 1) (Encodable.encode (t :: rest)) :=
      Nat.pair_lt_pair_left _ (Nat.lt_succ_self fuel)
    _ = m := by rw [hm2, ← hfuel, Nat.pair_unpair]

public lemma structuredNatGCore_spec (m : ℕ) (look : ℕ → Option (ℕ × List ℕ))
    (hlook : ∀ i, i < m → look i = structuredNatF i) :
    structuredNatGCore m look = structuredNatF m := by
  rw [structuredNatGCore, structuredNatF]
  rcases hf : m.unpair.1 with _ | fuel
  · rfl
  rcases hs : Denumerable.ofNat (List ℕ) m.unpair.2 with _ | ⟨t, rest⟩
  · rfl
  simp only [parseStructuredNat]
  by_cases h0 : t = 0 <;> simp only [h0, if_true, if_false]
  by_cases h1 : t = 1 <;> simp only [h1, if_true, if_false]
  · rw [hlook _ (structured_smaller_index hf hs), structuredNatF,
      Nat.unpair_pair, Denumerable.ofNat_encode]
  by_cases h2 : t = 2 <;> simp only [h2, if_true, if_false]
  rw [hlook _ (structured_smaller_index hf hs), structuredNatF,
    Nat.unpair_pair, Denumerable.ofNat_encode]

public def structuredNatG (prev : List (Option (ℕ × List ℕ))) :
    Option (Option (ℕ × List ℕ)) :=
  some (structuredNatGCore prev.length fun i => (prev[i]?).getD none)

public lemma structuredNatG_spec (m : ℕ) :
    structuredNatG ((List.range m).map structuredNatF) = some (structuredNatF m) := by
  rw [structuredNatG, show ((List.range m).map structuredNatF).length = m from by simp]
  congr 1
  refine structuredNatGCore_spec m _ fun i hi => ?_
  have hib : i < ((List.range m).map structuredNatF).length := by simpa using hi
  rw [List.getElem?_eq_getElem hib, Option.getD_some, List.getElem_map,
    List.getElem_range]

public def structuredTermF (m : ℕ) : Option (ℕ × List ℕ) :=
  parseStructuredArithmeticTerm m.unpair.1 0
    (Denumerable.ofNat (List ℕ) m.unpair.2)

public def structuredTermGCore (m : ℕ)
    (look : ℕ → Option (ℕ × List ℕ)) : Option (ℕ × List ℕ) :=
  match m.unpair.1, Denumerable.ofNat (List ℕ) m.unpair.2 with
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, t :: rest =>
      if t = 3 then
        (parseStructuredNat fuel rest).map fun p =>
          (Nat.pair 0 p.1 + 1, p.2)
      else if t = 4 then
        (parseStructuredNat fuel rest).map fun p => (Nat.pair 1 p.1 + 1, p.2)
      else if t = 5 then some (arithmeticFuncCode 0 0 0, rest)
      else if t = 6 then some (arithmeticFuncCode 0 1 0, rest)
      else if t = 7 ∨ t = 8 then
        (look (Nat.pair fuel (Encodable.encode rest))).bind fun p =>
          (look (Nat.pair fuel (Encodable.encode p.2))).map fun q =>
            (arithmeticFuncCode 2 (if t = 7 then 0 else 1)
              (arithmeticVec2Code p.1 q.1), q.2)
      else none

public lemma structuredTermGCore_spec (m : ℕ)
    (look : ℕ → Option (ℕ × List ℕ))
    (hlook : ∀ i, i < m → look i = structuredTermF i) :
    structuredTermGCore m look = structuredTermF m := by
  rw [structuredTermGCore, structuredTermF]
  rcases hf : m.unpair.1 with _ | fuel
  · rfl
  rcases hs : Denumerable.ofNat (List ℕ) m.unpair.2 with _ | ⟨t, rest⟩
  · rfl
  simp only [parseStructuredArithmeticTerm]
  by_cases h3 : t = 3 <;> simp only [h3, if_true, if_false]
  by_cases h4 : t = 4 <;> simp only [h4, if_true, if_false]
  by_cases h5 : t = 5 <;> simp only [h5, if_true, if_false]
  by_cases h6 : t = 6 <;> simp only [h6, if_true, if_false]
  by_cases hb : t = 7 ∨ t = 8 <;> simp only [hb, if_true, if_false]
  rw [hlook _ (structured_smaller_index hf hs), structuredTermF,
    Nat.unpair_pair, Denumerable.ofNat_encode]
  rcases hp : parseStructuredArithmeticTerm fuel 0 rest with _ | p
  · rfl
  simp only [Option.bind_some]
  have hpSuffix := parseStructuredArithmeticTerm_suffix hp
  have hidx : Nat.pair fuel (Encodable.encode p.2) < m := by
    calc
      Nat.pair fuel (Encodable.encode p.2) ≤
          Nat.pair fuel (Encodable.encode rest) :=
        pair_le_pair_right' fuel (encode_le_of_suffix hpSuffix)
      _ < m := structured_smaller_index hf hs
  rw [hlook _ hidx, structuredTermF, Nat.unpair_pair, Denumerable.ofNat_encode]

public def structuredTermG
    (prev : List (Option (ℕ × List ℕ))) : Option (Option (ℕ × List ℕ)) :=
  some (structuredTermGCore prev.length fun i => (prev[i]?).getD none)

public lemma structuredTermG_spec (m : ℕ) :
    structuredTermG ((List.range m).map structuredTermF) =
      some (structuredTermF m) := by
  rw [structuredTermG, show ((List.range m).map structuredTermF).length = m from by simp]
  congr 1
  refine structuredTermGCore_spec m _ fun i hi => ?_
  have hib : i < ((List.range m).map structuredTermF).length := by simpa using hi
  rw [List.getElem?_eq_getElem hib, Option.getD_some, List.getElem_map,
    List.getElem_range]

public def structuredFormulaF (m : ℕ) : Option (ℕ × List ℕ) :=
  parseStructuredArithmeticFormula m.unpair.1 0
    (Denumerable.ofNat (List ℕ) m.unpair.2)

public def structuredFormulaGCore (m : ℕ)
    (look : ℕ → Option (ℕ × List ℕ)) : Option (ℕ × List ℕ) :=
  match m.unpair.1, Denumerable.ofNat (List ℕ) m.unpair.2 with
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, t :: rest =>
      if t = 9 then some (Nat.pair 2 0 + 1, rest)
      else if t = 10 then some (Nat.pair 3 0 + 1, rest)
      else if t = 11 ∨ t = 12 ∨ t = 13 ∨ t = 14 then
        (parseStructuredArithmeticTerm fuel 0 rest).bind fun p =>
          (parseStructuredArithmeticTerm fuel 0 p.2).map fun q =>
            (arithmeticRelCode (t = 12 ∨ t = 14)
              (if t = 11 ∨ t = 12 then 0 else 1) p.1 q.1, q.2)
      else if t = 15 ∨ t = 16 then
        (look (Nat.pair fuel (Encodable.encode rest))).bind fun p =>
          (look (Nat.pair fuel (Encodable.encode p.2))).map fun q =>
            (Nat.pair (if t = 15 then 4 else 5) (Nat.pair p.1 q.1) + 1, q.2)
      else if t = 17 ∨ t = 18 then
        (look (Nat.pair fuel (Encodable.encode rest))).map fun p =>
          (Nat.pair (if t = 17 then 6 else 7) p.1 + 1, p.2)
      else if t = 20 then
        (look (Nat.pair fuel (Encodable.encode rest))).map fun p =>
          (negFormulaCode p.1, p.2)
      else if t = 21 then
        (look (Nat.pair fuel (Encodable.encode rest))).bind fun p =>
          (look (Nat.pair fuel (Encodable.encode p.2))).map fun q =>
            (Nat.pair 5 (Nat.pair (negFormulaCode p.1) q.1) + 1, q.2)
      else if t = 22 then
        (look (Nat.pair fuel (Encodable.encode rest))).bind fun p =>
          (look (Nat.pair fuel (Encodable.encode p.2))).map fun q =>
            (Nat.pair 4
              (Nat.pair (Nat.pair 5 (Nat.pair (negFormulaCode p.1) q.1) + 1)
                (Nat.pair 5 (Nat.pair (negFormulaCode q.1) p.1) + 1)) + 1, q.2)
      else none

public lemma structuredFormulaGCore_spec (m : ℕ)
    (look : ℕ → Option (ℕ × List ℕ))
    (hlook : ∀ i, i < m → look i = structuredFormulaF i) :
    structuredFormulaGCore m look = structuredFormulaF m := by
  rw [structuredFormulaGCore, structuredFormulaF]
  rcases hf : m.unpair.1 with _ | fuel
  · rfl
  rcases hs : Denumerable.ofNat (List ℕ) m.unpair.2 with _ | ⟨t, rest⟩
  · rfl
  simp only [parseStructuredArithmeticFormula]
  by_cases h9 : t = 9 <;> simp only [h9, if_true, if_false]
  by_cases h10 : t = 10 <;> simp only [h10, if_true, if_false]
  by_cases hrel : t = 11 ∨ t = 12 ∨ t = 13 ∨ t = 14 <;>
    simp only [hrel, if_true, if_false]
  by_cases hbin : t = 15 ∨ t = 16 <;> simp only [hbin, if_true, if_false]
  · rw [hlook _ (structured_smaller_index hf hs), structuredFormulaF,
      Nat.unpair_pair, Denumerable.ofNat_encode]
    rcases hp : parseStructuredArithmeticFormula fuel 0 rest with _ | p
    · rfl
    simp only [Option.bind_some]
    have hpSuffix := parseStructuredArithmeticFormula_suffix hp
    have hidx : Nat.pair fuel (Encodable.encode p.2) < m := by
      calc
        Nat.pair fuel (Encodable.encode p.2) ≤
            Nat.pair fuel (Encodable.encode rest) :=
          pair_le_pair_right' fuel (encode_le_of_suffix hpSuffix)
        _ < m := structured_smaller_index hf hs
    rw [hlook _ hidx, structuredFormulaF, Nat.unpair_pair,
      Denumerable.ofNat_encode]
  by_cases hquant : t = 17 ∨ t = 18 <;> simp only [hquant, if_true, if_false]
  · rw [hlook _ (structured_smaller_index hf hs), structuredFormulaF,
      Nat.unpair_pair, Denumerable.ofNat_encode]
  by_cases h20 : t = 20 <;> simp only [h20, if_true, if_false]
  · rw [hlook _ (structured_smaller_index hf hs), structuredFormulaF,
      Nat.unpair_pair, Denumerable.ofNat_encode]
  by_cases h21 : t = 21 <;> simp only [h21, if_true, if_false]
  · rw [hlook _ (structured_smaller_index hf hs), structuredFormulaF,
      Nat.unpair_pair, Denumerable.ofNat_encode]
    rcases hp : parseStructuredArithmeticFormula fuel 0 rest with _ | p
    · rfl
    simp only [Option.bind_some]
    have hpSuffix := parseStructuredArithmeticFormula_suffix hp
    have hidx : Nat.pair fuel (Encodable.encode p.2) < m := by
      calc
        Nat.pair fuel (Encodable.encode p.2) ≤
            Nat.pair fuel (Encodable.encode rest) :=
          pair_le_pair_right' fuel (encode_le_of_suffix hpSuffix)
        _ < m := structured_smaller_index hf hs
    rw [hlook _ hidx, structuredFormulaF, Nat.unpair_pair,
      Denumerable.ofNat_encode]
  by_cases h22 : t = 22 <;> simp only [h22, if_true, if_false]
  rw [hlook _ (structured_smaller_index hf hs), structuredFormulaF,
    Nat.unpair_pair, Denumerable.ofNat_encode]
  rcases hp : parseStructuredArithmeticFormula fuel 0 rest with _ | p
  · rfl
  simp only [Option.bind_some]
  have hpSuffix := parseStructuredArithmeticFormula_suffix hp
  have hidx : Nat.pair fuel (Encodable.encode p.2) < m := by
    calc
      Nat.pair fuel (Encodable.encode p.2) ≤
          Nat.pair fuel (Encodable.encode rest) :=
        pair_le_pair_right' fuel (encode_le_of_suffix hpSuffix)
      _ < m := structured_smaller_index hf hs
  rw [hlook _ hidx, structuredFormulaF, Nat.unpair_pair,
    Denumerable.ofNat_encode]

public def structuredFormulaG
    (prev : List (Option (ℕ × List ℕ))) : Option (Option (ℕ × List ℕ)) :=
  some (structuredFormulaGCore prev.length fun i => (prev[i]?).getD none)

public lemma structuredFormulaG_spec (m : ℕ) :
    structuredFormulaG ((List.range m).map structuredFormulaF) =
      some (structuredFormulaF m) := by
  rw [structuredFormulaG,
    show ((List.range m).map structuredFormulaF).length = m from by simp]
  congr 1
  refine structuredFormulaGCore_spec m _ fun i hi => ?_
  have hib : i < ((List.range m).map structuredFormulaF).length := by simpa using hi
  rw [List.getElem?_eq_getElem hib, Option.getD_some, List.getElem_map,
    List.getElem_range]

/-! ## The strong-recursion package -/

/-- `parseRpnC` on the paired index (list argument via the canonical `ofNat`). -/
def parseF (m : ℕ) : Option (ℕ × List ℕ) :=
  parseRpnC m.unpair.1 (Denumerable.ofNat (List ℕ) m.unpair.2)

/-- One strong-recursion step over an abstract lookup for the smaller indices. -/
def parseGCore (m : ℕ) (look : ℕ → Option (ℕ × List ℕ)) : Option (ℕ × List ℕ) :=
  match m.unpair.1, Denumerable.ofNat (List ℕ) m.unpair.2 with
  | 0, _ => none
  | _ + 1, [] => none
  | fuel' + 1, t :: rest =>
      if t = 0 then some (Nat.pair 0 0 + 1, rest)
      else if t = 1 then
        match rest with
        | 0 :: payload => parseStructuredPaperPrimeC payload
        | c :: tail =>
            if Encodable.encode (Encodable.decode (α := Sentence) c) = 0 then none
            else some (Encodable.encode (Encodable.decode (α := Sentence) c) - 1, tail)
        | [] => none
      else if t = 2 ∨ t = 3 ∨ t = 4 then
        (look (Nat.pair fuel' (Encodable.encode rest))).bind fun p =>
          (look (Nat.pair fuel' (Encodable.encode p.2))).bind fun q =>
            some (Nat.pair t (Nat.pair p.1 q.1) + 1, q.2)
      else some (Nat.pair 1 (t - 5) + 1, rest)

/-- The step law: any faithful lookup below `m` computes `parseF m`. -/
lemma parseGCore_spec (m : ℕ) (look : ℕ → Option (ℕ × List ℕ))
    (hlook : ∀ i, i < m → look i = parseF i) :
    parseGCore m look = parseF m := by
  rw [parseGCore]
  rcases hfuel : m.unpair.1 with _ | fuel'
  · rw [parseF, hfuel]
    rfl
  rcases hts : Denumerable.ofNat (List ℕ) m.unpair.2 with _ | ⟨t, rest⟩
  · rw [parseF, hfuel, hts]
    rfl
  have hm2 : Encodable.encode (t :: rest) = m.unpair.2 := by
    rw [← hts]
    exact Denumerable.encode_ofNat _
  have hrest_lt : Encodable.encode rest < m.unpair.2 := by
    rw [← hm2]
    exact encode_lt_encode_cons t rest
  have hidx : ∀ x, x ≤ Encodable.encode rest → Nat.pair fuel' x < m := by
    intro x hx
    calc Nat.pair fuel' x ≤ Nat.pair fuel' (Encodable.encode rest) :=
          pair_le_pair_right' fuel' hx
      _ < Nat.pair (fuel' + 1) (Encodable.encode rest) :=
          Nat.pair_lt_pair_left _ (Nat.lt_succ_self fuel')
      _ ≤ Nat.pair (fuel' + 1) m.unpair.2 :=
          pair_le_pair_right' _ (le_of_lt hrest_lt)
      _ = Nat.pair m.unpair.1 m.unpair.2 := by rw [hfuel]
      _ = m := Nat.pair_unpair m
  rw [parseF, hfuel, hts, parseRpnC_cons]
  simp only []
  by_cases h0 : t = 0
  · rw [if_pos h0, if_pos h0]
  rw [if_neg h0, if_neg h0]
  by_cases h1 : t = 1
  · rw [if_pos h1, if_pos h1]
    rfl
  rw [if_neg h1, if_neg h1]
  by_cases hb : t = 2 ∨ t = 3 ∨ t = 4
  · rw [if_pos hb]
    have h1st : look (Nat.pair fuel' (Encodable.encode rest)) =
        parseRpnC fuel' rest := by
      rw [hlook _ (hidx _ le_rfl), parseF, Nat.unpair_pair,
        Denumerable.ofNat_encode]
    rw [h1st]
    obtain ⟨hb2, hb3, hb4⟩ :
        (t = 2 → True) ∧ (t = 3 → True) ∧ (t = 4 → True) := ⟨fun _ => trivial,
          fun _ => trivial, fun _ => trivial⟩
    rcases hp1 : parseRpnC fuel' rest with _ | ⟨e1, r1⟩
    · rcases hb with rfl | rfl | rfl
      · rw [if_pos rfl]
        try rfl
      · rw [if_neg (by norm_num), if_pos rfl]
        try rfl
      · rw [if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]
        try rfl
    · have hsfx := parseRpnC_suffix hp1
      have h2nd : look (Nat.pair fuel' (Encodable.encode r1)) =
          parseRpnC fuel' r1 := by
        rw [hlook _ (hidx _ (encode_le_of_suffix hsfx)), parseF,
          Nat.unpair_pair, Denumerable.ofNat_encode]
      simp only [Option.bind_some]
      rw [h2nd]
      rcases hb with rfl | rfl | rfl
      · rw [if_pos rfl]
      · rw [if_neg (by norm_num), if_pos rfl]
      · rw [if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]
  · rw [if_neg hb]
    push_neg at hb
    obtain ⟨hb2, hb3, hb4⟩ := hb
    rw [if_neg hb2, if_neg hb3, if_neg hb4]

/-- The strong-recursion step over the value table. -/
def parseG (prev : List (Option (ℕ × List ℕ))) : Option (Option (ℕ × List ℕ)) :=
  some (parseGCore prev.length fun i => (prev[i]?).getD none)

lemma parseG_spec (m : ℕ) :
    parseG ((List.range m).map parseF) = some (parseF m) := by
  rw [parseG, show ((List.range m).map parseF).length = m from by simp]
  congr 1
  refine parseGCore_spec m _ fun i hi => ?_
  have hib : i < ((List.range m).map parseF).length := by simpa using hi
  rw [List.getElem?_eq_getElem hib, Option.getD_some, List.getElem_map,
    List.getElem_range]

/-! ## The strong-recursion package for the stream contraction -/

/-- `unRpnTokensC` on the paired index. -/
def unF (m : ℕ) : List ℕ :=
  unRpnTokensC m.unpair.1 (Denumerable.ofNat (List ℕ) m.unpair.2)

/-- One strong-recursion step over an abstract lookup for the smaller indices. -/
def unGCore (m : ℕ) (look : ℕ → List ℕ) : List ℕ :=
  match m.unpair.1, Denumerable.ofNat (List ℕ) m.unpair.2 with
  | _, [] => []
  | 0, _ :: _ => []
  | fuel' + 1, t :: rest =>
      if t = 0 then
        match parseRpnC rest.length rest with
        | none => [0, 0]
        | some (e, r1) =>
            match r1 with
            | [] => [0, e]
            | d :: r2 => 0 :: e :: d :: look (Nat.pair fuel' (Encodable.encode r2))
      else if t = 6 then
        match parseRpnC rest.length rest with
        | none => [6, 0]
        | some (e, r1) => 6 :: e :: look (Nat.pair fuel' (Encodable.encode r1))
      else if t = 1 then
        match rest with
        | [] => [1]
        | c :: r => 1 :: c :: look (Nat.pair fuel' (Encodable.encode r))
      else if t = 7 then
        match rest with
        | [] => [7]
        | c :: r => 7 :: c :: look (Nat.pair fuel' (Encodable.encode r))
      else t :: look (Nat.pair fuel' (Encodable.encode rest))

/-- The step law: any faithful lookup below `m` computes `unF m`. -/
lemma unGCore_spec (m : ℕ) (look : ℕ → List ℕ)
    (hlook : ∀ i, i < m → look i = unF i) :
    unGCore m look = unF m := by
  rw [unGCore]
  rcases hts : Denumerable.ofNat (List ℕ) m.unpair.2 with _ | ⟨t, rest⟩
  · rcases hfuel : m.unpair.1 with _ | fuel' <;>
      · rw [unF, hfuel, hts]
        rfl
  rcases hfuel : m.unpair.1 with _ | fuel'
  · rw [unF, hfuel, hts]
    rfl
  have hm2 : Encodable.encode (t :: rest) = m.unpair.2 := by
    rw [← hts]
    exact Denumerable.encode_ofNat _
  have hrest_lt : Encodable.encode rest < m.unpair.2 := by
    rw [← hm2]
    exact encode_lt_encode_cons t rest
  have hidx : ∀ x, x ≤ Encodable.encode rest → Nat.pair fuel' x < m := by
    intro x hx
    calc Nat.pair fuel' x ≤ Nat.pair fuel' (Encodable.encode rest) :=
          pair_le_pair_right' fuel' hx
      _ < Nat.pair (fuel' + 1) (Encodable.encode rest) :=
          Nat.pair_lt_pair_left _ (Nat.lt_succ_self fuel')
      _ ≤ Nat.pair (fuel' + 1) m.unpair.2 :=
          pair_le_pair_right' _ (le_of_lt hrest_lt)
      _ = Nat.pair m.unpair.1 m.unpair.2 := by rw [hfuel]
      _ = m := Nat.pair_unpair m
  have hlookAt : ∀ r : List ℕ, r <:+ rest →
      look (Nat.pair fuel' (Encodable.encode r)) = unRpnTokensC fuel' r := by
    intro r hr
    rw [hlook _ (hidx _ (encode_le_of_suffix hr)), unF, Nat.unpair_pair,
      Denumerable.ofNat_encode]
  rw [unF, hfuel, hts, unRpnTokensC_cons]
  simp only []
  by_cases h0 : t = 0
  · rw [if_pos h0, if_pos h0]
    rcases hp : parseRpnC rest.length rest with _ | ⟨e, r1⟩
    · rfl
    rcases r1 with _ | ⟨d, r2⟩
    · rfl
    simp only []
    have hsfx : r2 <:+ rest :=
      ((List.suffix_cons d r2).trans (parseRpnC_suffix hp))
    rw [hlookAt r2 hsfx]
  rw [if_neg h0, if_neg h0]
  by_cases h6 : t = 6
  · rw [if_pos h6, if_pos h6]
    rcases hp : parseRpnC rest.length rest with _ | ⟨e, r1⟩
    · rfl
    simp only []
    rw [hlookAt r1 (parseRpnC_suffix hp)]
  rw [if_neg h6, if_neg h6]
  by_cases h1 : t = 1
  · rw [if_pos h1, if_pos h1]
    rcases rest with _ | ⟨c, r⟩
    · rfl
    simp only []
    rw [hlookAt r (List.suffix_cons c r)]
  rw [if_neg h1, if_neg h1]
  by_cases h7 : t = 7
  · rw [if_pos h7, if_pos h7]
    rcases rest with _ | ⟨c, r⟩
    · rfl
    simp only []
    rw [hlookAt r (List.suffix_cons c r)]
  rw [if_neg h7, if_neg h7]
  rw [hlookAt rest List.suffix_rfl]

/-- The strong-recursion step over the value table. -/
def unG (prev : List (List ℕ)) : Option (List ℕ) :=
  some (unGCore prev.length fun i => (prev[i]?).getD [])

lemma unG_spec (m : ℕ) :
    unG ((List.range m).map unF) = some (unF m) := by
  rw [unG, show ((List.range m).map unF).length = m from by simp]
  congr 1
  refine unGCore_spec m _ fun i hi => ?_
  have hib : i < ((List.range m).map unF).length := by simpa using hi
  rw [List.getElem?_eq_getElem hib, Option.getD_some, List.getElem_map,
    List.getElem_range]

end LogicalInduction
