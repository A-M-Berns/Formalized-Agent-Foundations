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
        rw [List.head?_cons] at h
        rcases hdec : Encodable.decode (α := Sentence) c with _ | ψ
        · simp [hdec] at h
        · simp only [Option.bind_some, hdec, Option.map_some, List.tail_cons] at h
          obtain ⟨-, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
          exact (List.suffix_cons c ts').trans (List.suffix_cons t (c :: ts'))
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
        rest.head?.bind fun c =>
          if Encodable.encode (Encodable.decode (α := Sentence) c) = 0 then none
          else some (Encodable.encode (Encodable.decode (α := Sentence) c) - 1,
            rest.tail)
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
        try (rcases parseRpnC fuel' r1 with _ | ⟨e2, r2⟩ <;> rfl)
      · rw [if_neg (by norm_num), if_pos rfl]
        try (rcases parseRpnC fuel' r1 with _ | ⟨e2, r2⟩ <;> rfl)
      · rw [if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]
        try (rcases parseRpnC fuel' r1 with _ | ⟨e2, r2⟩ <;> rfl)
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

end LogicalInduction
