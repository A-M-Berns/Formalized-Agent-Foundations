import LogicalInduction.Properties.UniversalSemimeasure
import Mathlib.Computability.Halting


/-!
# Tranche S (`M7-STRICT-SEPARATORS`): the computable-enumeration obstruction

This file records what a *computably enumerable* family of nested bit prefixes can and
cannot do against a universal continuous semimeasure.

The intended target of the tranche was to inhabit `StrictSeparatorPresentation`
(`Properties/UniversalSemimeasure.lean`), whose fields ask for

* `prefixes : ℕ → List Bool`, nested, with lengths tending to infinity,
* an `EfficientRepeatedEnumeration` of the associated prefix sentences, and
* `mass_tendsto_zero : Tendsto (fun i ↦ M.mass (prefixes i)) atTop (𝓝 0)`.

`no_ce_null_prefix_family` below shows those fields are jointly **unsatisfiable** as soon
as the prefix strings admit a computable enumeration — which is exactly what
`EfficientRepeatedEnumeration` supplies once the prefix syntax can be decoded (its
`sequence` is emitted by a program, and its `sound`/`covers` fields say the emitted
sentences are precisely the `prefixSentence (prefixes i)`).

The argument is elementary and does not even need the lengths to grow.  A computable
enumeration of a *nested* (pairwise comparable) family of strings carries a
lower-semicomputable continuous semimeasure `ceNestedSemimeasure`, of mass `1` on every
string that is a prefix of an enumerated one and `0` elsewhere: comparability is exactly
what makes the two children of a node compete, so the semimeasure inequality holds.  A
universal `M` dominates it, so `M.mass (prefixes i)` stays above a fixed positive constant
forever, and cannot tend to `0`.

The reusable pieces are `ceNestedSemimeasure` (a concrete inhabitant of
`LowerSemicomputableContinuousSemimeasure`) and `exists_code_evaln_of_computable` (any
computable `ℕ × List Bool → ℚ` meets the bounded-fuel `approximation_computes` interface).

## Consequence for the boundary

The paper's proof (`app:strict`) never claims mass vanishes along one computable branch.
It applies Uniform Non-Dogmatism to the c.e. *constraint theory* of a recursively
inseparable pair — single-bit constraints `b_e` / `¬b_e`, which leave the undecided bits
free — and then argues that a universal semimeasure gives vanishing mass to the *class* of
length-`n` separator prefixes.  Faithfully formalizing `thm:strict` therefore requires the
boundary interface to carry a c.e. constraint theory plus a per-level *set* of consistent
strings, with the market half summing over that set (coherence + pigeonhole), rather than
a single nested prefix family.  See `notes/next-session.md`, Tranche S.
-/

namespace LogicalInduction

open Filter Topology

-- `Nat.unpair` reduction loops `whnf` on `Nat.sqrt` inside the `Primcodable` instances
-- for the product/list types used below (see the gotcha log in `notes/next-session.md`).
attribute [local irreducible] Nat.sqrt

/-! ### Pointwise prefix agreement

`List.IsPrefix` has no computability API in Mathlib, so the prefix relation is used here in
its pointwise form, which is directly decidable by a `List.range`/`getElem?` comparison. -/

/-- `PrefixAgree σ l` says `σ` is a prefix of `l`, stated pointwise. -/
def PrefixAgree (σ l : List Bool) : Prop :=
  ∀ (k : ℕ) (hk : k < σ.length), l[k]? = some σ[k]

lemma PrefixAgree.refl (σ : List Bool) : PrefixAgree σ σ := by
  intro k hk
  simp [List.getElem?_eq_getElem hk]

lemma PrefixAgree.trans {a b c : List Bool} (hab : PrefixAgree a b)
    (hbc : PrefixAgree b c) : PrefixAgree a c := by
  intro k hk
  have h1 := hab k hk
  have hkb : k < b.length := (List.getElem?_eq_some_iff.mp h1).1
  have hb : b[k] = a[k] := by
    rw [List.getElem?_eq_getElem hkb] at h1
    exact Option.some.inj h1
  rw [hbc k hkb, hb]

/-- A prefix of `σ ++ [b]` truncates to a prefix of `σ`. -/
lemma PrefixAgree.of_concat {σ : List Bool} {b : Bool} {l : List Bool}
    (h : PrefixAgree (σ ++ [b]) l) : PrefixAgree σ l := by
  intro k hk
  have hk' : k < (σ ++ [b]).length := by simp; omega
  have hres := h k hk'
  rwa [List.getElem_append_left hk] at hres

/-- Two opposite one-bit extensions of the same node cannot both be prefixes of one
string. -/
lemma PrefixAgree.concat_conflict {σ l : List Bool}
    (h0 : PrefixAgree (σ ++ [false]) l) (h1 : PrefixAgree (σ ++ [true]) l) : False := by
  have hk : σ.length < (σ ++ [false]).length := by simp
  have hk' : σ.length < (σ ++ [true]).length := by simp
  have e0 := h0 σ.length hk
  have e1 := h1 σ.length hk'
  rw [List.getElem_append_right (le_refl _)] at e0 e1
  simp only [Nat.sub_self, List.getElem_cons_zero] at e0 e1
  rw [e0] at e1
  exact absurd e1 (by simp)

/-- The decidable Boolean form of `PrefixAgree`, built from primitive-recursive list
operations. -/
def prefixAgreeB (σ l : List Bool) : Bool :=
  decide ((List.range σ.length).map (fun k ↦ l[k]?) = σ.map some)

lemma prefixAgreeB_iff (σ l : List Bool) :
    prefixAgreeB σ l = true ↔ PrefixAgree σ l := by
  rw [prefixAgreeB, decide_eq_true_iff]
  constructor
  · intro h k hk
    have hk1 : k < ((List.range σ.length).map (fun k ↦ l[k]?)).length := by simp [hk]
    have hk2 : k < (σ.map some).length := by simp [hk]
    have heq : ((List.range σ.length).map (fun k ↦ l[k]?))[k]'hk1 =
        (σ.map some)[k]'hk2 := by
      congr 1
    simp only [List.getElem_map, List.getElem_range] at heq
    exact heq
  · intro h
    apply List.ext_getElem
    · simp
    · intro k h1 h2
      have hk : k < σ.length := by simpa using h1
      simp only [List.getElem_map, List.getElem_range]
      rw [h k hk]

lemma prefixAgreeB_primrec :
    Primrec fun p : List Bool × List Bool ↦ prefixAgreeB p.1 p.2 := by
  have hleft : Primrec fun p : List Bool × List Bool ↦
      (List.range p.1.length).map (fun k ↦ p.2[k]?) :=
    Primrec.list_map (Primrec.list_range.comp (Primrec.list_length.comp Primrec.fst))
      (Primrec.list_getElem?.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
  have hright : Primrec fun p : List Bool × List Bool ↦
      p.1.map (some : Bool → Option Bool) :=
    Primrec.list_map Primrec.fst (Primrec.option_some.comp Primrec.snd).to₂
  exact Primrec.comp ((Primrec.eq (α := List (Option Bool))).decide) (hleft.pair hright)

/-! ### The semimeasure carried by a computably enumerated nested family -/

variable (enum : ℕ → List Bool)

/-- Stage-`n` approximation: `1` as soon as some `enum j` with `j ≤ n` extends `σ`. -/
def ceApprox : ℕ → List Bool → ℚ
  | 0, σ => if prefixAgreeB σ (enum 0) then 1 else 0
  | n + 1, σ => if prefixAgreeB σ (enum (n + 1)) then 1 else ceApprox n σ

open scoped Classical in
/-- Limit mass: `1` exactly on the strings extended by some enumerated string. -/
noncomputable def ceMass (σ : List Bool) : ℝ :=
  if ∃ j, PrefixAgree σ (enum j) then 1 else 0

variable {enum}

open scoped Classical in
lemma ceApprox_eq (n : ℕ) (σ : List Bool) :
    ceApprox enum n σ = if ∃ j, j ≤ n ∧ PrefixAgree σ (enum j) then 1 else 0 := by
  induction n with
  | zero =>
      simp only [ceApprox]
      by_cases h : PrefixAgree σ (enum 0)
      · rw [if_pos ((prefixAgreeB_iff σ (enum 0)).2 h), if_pos ⟨0, le_refl _, h⟩]
      · rw [if_neg (by simpa [prefixAgreeB_iff] using h)]
        refine (if_neg ?_).symm
        rintro ⟨j, hj, hja⟩
        exact h (by simpa [Nat.le_zero.mp hj] using hja)
  | succ n ih =>
      simp only [ceApprox, ih]
      by_cases hnew : PrefixAgree σ (enum (n + 1))
      · rw [if_pos ((prefixAgreeB_iff _ _).2 hnew), if_pos ⟨n + 1, le_refl _, hnew⟩]
      · rw [if_neg (by simpa [prefixAgreeB_iff] using hnew)]
        by_cases hold : ∃ j, j ≤ n ∧ PrefixAgree σ (enum j)
        · obtain ⟨j, hj, hja⟩ := hold
          rw [if_pos ⟨j, hj, hja⟩, if_pos ⟨j, hj.trans (Nat.le_succ n), hja⟩]
        · refine (if_neg hold).trans (if_neg ?_).symm
          rintro ⟨j, hj, hja⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hj) with h | h
          · exact hold ⟨j, Nat.lt_succ_iff.mp h, hja⟩
          · exact hnew (h ▸ hja)

lemma ceApprox_nonneg (n : ℕ) (σ : List Bool) : 0 ≤ ceApprox enum n σ := by
  classical
  rw [ceApprox_eq]; split <;> norm_num

lemma ceMass_nonneg (σ : List Bool) : 0 ≤ ceMass enum σ := by
  classical
  rw [ceMass]; split <;> norm_num

lemma ceApprox_le_ceMass (n : ℕ) (σ : List Bool) :
    ((ceApprox enum n σ : ℚ) : ℝ) ≤ ceMass enum σ := by
  classical
  rw [ceApprox_eq, ceMass]
  by_cases h : ∃ j, j ≤ n ∧ PrefixAgree σ (enum j)
  · obtain ⟨j, hjn, hja⟩ := h
    rw [if_pos (⟨j, hjn, hja⟩ : ∃ j, j ≤ n ∧ PrefixAgree σ (enum j)),
      if_pos (⟨j, hja⟩ : ∃ j, PrefixAgree σ (enum j))]
    norm_num
  · rw [if_neg h]
    split <;> norm_num

lemma ceApprox_mono (σ : List Bool) : Monotone fun n ↦ ceApprox enum n σ := by
  classical
  refine monotone_nat_of_le_succ fun n ↦ ?_
  rw [ceApprox_eq, ceApprox_eq]
  by_cases h : ∃ j, j ≤ n ∧ PrefixAgree σ (enum j)
  · obtain ⟨j, hj, hja⟩ := h
    rw [if_pos ⟨j, hj, hja⟩, if_pos ⟨j, hj.trans (Nat.le_succ n), hja⟩]
  · rw [if_neg h]
    split <;> norm_num

lemma ceApprox_tendsto (σ : List Bool) :
    Tendsto (fun n ↦ ((ceApprox enum n σ : ℚ) : ℝ)) atTop (𝓝 (ceMass enum σ)) := by
  classical
  by_cases h : ∃ j, PrefixAgree σ (enum j)
  · obtain ⟨j, hja⟩ := h
    have hev : ∀ᶠ n in atTop, ((ceApprox enum n σ : ℚ) : ℝ) = ceMass enum σ := by
      refine eventually_atTop.2 ⟨j, fun n hn ↦ ?_⟩
      rw [ceApprox_eq, if_pos (⟨j, hn, hja⟩ : ∃ j', j' ≤ n ∧ PrefixAgree σ (enum j')),
        ceMass, if_pos (⟨j, hja⟩ : ∃ j', PrefixAgree σ (enum j'))]
      norm_num
    exact Tendsto.congr' (hev.mono fun _ h ↦ h.symm) tendsto_const_nhds
  · have hev : ∀ n, ((ceApprox enum n σ : ℚ) : ℝ) = ceMass enum σ := by
      intro n
      rw [ceApprox_eq, if_neg (fun ⟨j, _, hja⟩ ↦ h ⟨j, hja⟩), ceMass, if_neg h]
      norm_num
    exact Tendsto.congr (fun n ↦ (hev n).symm) tendsto_const_nhds

/-- The `ℕ`-valued mirror of `ceApprox`: the approximants take only the two values `0`
and `1`, so their sentence codes are a choice between two constants.  Working with the
codes directly avoids needing a `Primcodable ℚ` instance whose `encode` would differ from
the `Encodable ℚ` one used by `approximation_computes`. -/
def ceApproxCodeVal (enum : ℕ → List Bool) : ℕ → List Bool → ℕ
  | 0, σ => if prefixAgreeB σ (enum 0) then Encodable.encode (1 : ℚ)
      else Encodable.encode (0 : ℚ)
  | n + 1, σ => if prefixAgreeB σ (enum (n + 1)) then Encodable.encode (1 : ℚ)
      else ceApproxCodeVal enum n σ

lemma ceApproxCodeVal_eq (n : ℕ) (σ : List Bool) :
    ceApproxCodeVal enum n σ = Encodable.encode (ceApprox enum n σ) := by
  induction n with
  | zero =>
      simp only [ceApproxCodeVal, ceApprox]
      by_cases h : prefixAgreeB σ (enum 0) <;> simp [h]
  | succ n ih =>
      simp only [ceApproxCodeVal, ceApprox]
      by_cases h : prefixAgreeB σ (enum (n + 1)) <;> simp [h, ih]

lemma ceApproxCodeVal_computable (henum : Computable enum) :
    Computable fun p : ℕ × List Bool ↦ ceApproxCodeVal enum p.1 p.2 := by
  have hbase : Computable fun p : ℕ × List Bool ↦
      if prefixAgreeB p.2 (enum 0) then Encodable.encode (1 : ℚ)
        else Encodable.encode (0 : ℚ) := by
    have hb : Computable fun p : ℕ × List Bool ↦ prefixAgreeB p.2 (enum 0) :=
      prefixAgreeB_primrec.to_comp.comp
        (Computable.snd.pair (Computable.const (enum 0)))
    exact (Computable.cond hb (Computable.const (Encodable.encode (1 : ℚ)))
      (Computable.const (Encodable.encode (0 : ℚ)))).of_eq
      (by intro p; by_cases h : prefixAgreeB p.2 (enum 0) <;> simp [h])
  have hstep : Computable₂ fun (p : ℕ × List Bool) (q : ℕ × ℕ) ↦
      if prefixAgreeB p.2 (enum (q.1 + 1)) then Encodable.encode (1 : ℚ) else q.2 := by
    have hb : Computable fun r : (ℕ × List Bool) × (ℕ × ℕ) ↦
        prefixAgreeB r.1.2 (enum (r.2.1 + 1)) :=
      prefixAgreeB_primrec.to_comp.comp
        ((Computable.snd.comp Computable.fst).pair
          (henum.comp (Computable.succ.comp (Computable.fst.comp Computable.snd))))
    exact (Computable.cond hb (Computable.const (Encodable.encode (1 : ℚ)))
      (Computable.snd.comp Computable.snd)).of_eq
      (by intro r; by_cases h : prefixAgreeB r.1.2 (enum (r.2.1 + 1)) <;> simp [h])
  refine (Computable.nat_rec Computable.fst hbase hstep).of_eq ?_
  rintro ⟨n, σ⟩
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [ceApproxCodeVal]
      by_cases h : prefixAgreeB σ (enum (n + 1)) <;> simp [h, ← ih]

/-- Every computable `ℕ × List Bool → ℕ` has a `Nat.Partrec.Code` computing it on the
paired encoding with the bounded-fuel interface that
`LowerSemicomputableContinuousSemimeasure.approximation_computes` demands. -/
lemma exists_code_evaln_of_computable {f : ℕ × List Bool → ℕ} (hf : Computable f) :
    ∃ c : Nat.Partrec.Code, ∀ (n : ℕ) (σ : List Bool), ∃ fuel,
      c.evaln fuel (Nat.pair n (Encodable.encode σ)) = some (f (n, σ)) := by
  have hnp : Nat.Partrec fun z ↦ Part.bind (Encodable.decode (α := ℕ × List Bool) z)
      fun a ↦ Part.map Encodable.encode (Part.some (f a)) := hf
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hnp
  refine ⟨c, fun n σ ↦ ?_⟩
  have hval : f (n, σ) ∈ c.eval (Nat.pair n (Encodable.encode σ)) := by
    rw [hc]
    simp [Encodable.decode_prod_val, Nat.unpair_pair, Encodable.encodek]
  obtain ⟨fuel, hfuel⟩ := Nat.Partrec.Code.evaln_complete.mp hval
  exact ⟨fuel, hfuel⟩

/-- The code chosen for the approximants of `ceNestedSemimeasure`. -/
noncomputable def ceApproxCode (henum : Computable enum) : Nat.Partrec.Code :=
  Classical.choose (exists_code_evaln_of_computable (ceApproxCodeVal_computable henum))

lemma ceApproxCode_spec (henum : Computable enum) (n : ℕ) (σ : List Bool) :
    ∃ fuel, (ceApproxCode henum).evaln fuel (Nat.pair n (Encodable.encode σ)) =
      some (Encodable.encode (ceApprox enum n σ)) := by
  obtain ⟨fuel, hfuel⟩ :=
    Classical.choose_spec (exists_code_evaln_of_computable
      (ceApproxCodeVal_computable henum)) n σ
  refine ⟨fuel, ?_⟩
  rw [ceApproxCode, hfuel, ceApproxCodeVal_eq]

/-- **The semimeasure of a computably enumerated nested family.**  Comparability of the
enumerated strings is exactly what makes the two children of a node compete, giving the
continuous-semimeasure inequality. -/
noncomputable def ceNestedSemimeasure (henum : Computable enum)
    (hcomparable : ∀ j j', PrefixAgree (enum j) (enum j') ∨ PrefixAgree (enum j') (enum j)) :
    LowerSemicomputableContinuousSemimeasure where
  mass := ceMass enum
  nonneg σ := ceMass_nonneg σ
  root_le_one := by classical rw [ceMass]; split <;> norm_num
  children_le σ := by
    classical
    by_cases h0 : ∃ j, PrefixAgree (σ ++ [false]) (enum j)
    · obtain ⟨j, hj⟩ := h0
      have hσ : ceMass enum σ = 1 := by
        rw [ceMass, if_pos (⟨j, hj.of_concat⟩ : ∃ j, PrefixAgree σ (enum j))]
      have h1 : ¬ ∃ j', PrefixAgree (σ ++ [true]) (enum j') := by
        rintro ⟨j', hj'⟩
        rcases hcomparable j j' with hcc | hcc
        · exact PrefixAgree.concat_conflict (hj.trans hcc) hj'
        · exact PrefixAgree.concat_conflict hj (hj'.trans hcc)
      have e0 : ceMass enum (σ ++ [false]) = 1 := by
        rw [ceMass, if_pos (⟨j, hj⟩ : ∃ j, PrefixAgree (σ ++ [false]) (enum j))]
      have e1 : ceMass enum (σ ++ [true]) = 0 := by rw [ceMass, if_neg h1]
      show ceMass enum (σ ++ [false]) + ceMass enum (σ ++ [true]) ≤ ceMass enum σ
      rw [hσ, e0, e1]
      norm_num
    · by_cases h1 : ∃ j, PrefixAgree (σ ++ [true]) (enum j)
      · obtain ⟨j, hj⟩ := h1
        have hσ : ceMass enum σ = 1 := by
          rw [ceMass, if_pos (⟨j, hj.of_concat⟩ : ∃ j, PrefixAgree σ (enum j))]
        have e0 : ceMass enum (σ ++ [false]) = 0 := by rw [ceMass, if_neg h0]
        have e1 : ceMass enum (σ ++ [true]) = 1 := by
          rw [ceMass, if_pos (⟨j, hj⟩ : ∃ j, PrefixAgree (σ ++ [true]) (enum j))]
        show ceMass enum (σ ++ [false]) + ceMass enum (σ ++ [true]) ≤ ceMass enum σ
        rw [hσ, e0, e1]
        norm_num
      · have e0 : ceMass enum (σ ++ [false]) = 0 := by rw [ceMass, if_neg h0]
        have e1 : ceMass enum (σ ++ [true]) = 0 := by rw [ceMass, if_neg h1]
        show ceMass enum (σ ++ [false]) + ceMass enum (σ ++ [true]) ≤ ceMass enum σ
        rw [e0, e1]
        simpa using ceMass_nonneg (enum := enum) σ
  approximation n σ := ceApprox enum n σ
  approximation_code := ceApproxCode henum
  approximation_computes n σ := ceApproxCode_spec henum n σ
  approximation_nonneg n σ := ceApprox_nonneg n σ
  approximation_mono σ := ceApprox_mono σ
  approximation_le n σ := ceApprox_le_ceMass n σ
  approximation_tendsto σ := ceApprox_tendsto σ

/-- **A universal semimeasure never abandons a computably enumerated nested family.**
Paper node: `thm:strict` -/
theorem exists_pos_mass_of_ce_nested (M : UniversalContinuousSemimeasure)
    (henum : Computable enum)
    (hcomparable : ∀ j j', PrefixAgree (enum j) (enum j') ∨ PrefixAgree (enum j') (enum j)) :
    ∃ c : ℝ, 0 < c ∧ ∀ j, c ≤ M.mass (enum j) := by
  classical
  obtain ⟨c, hc, hdom⟩ := M.universal (ceNestedSemimeasure henum hcomparable)
  refine ⟨c, hc, fun j ↦ ?_⟩
  have h := hdom (enum j)
  have hmass : (ceNestedSemimeasure henum hcomparable).mass (enum j) = 1 := by
    show ceMass enum (enum j) = 1
    rw [ceMass, if_pos ⟨j, PrefixAgree.refl _⟩]
  rw [hmass] at h
  simpa using h

/-! ### The obstruction to `StrictSeparatorPresentation` -/

/-- A family nested in the `∃ rest, prefixes (i+1) = prefixes i ++ rest` sense is pairwise
comparable. -/
lemma prefixAgree_of_nested {prefixes : ℕ → List Bool}
    (hnested : ∀ i, ∃ rest, prefixes (i + 1) = prefixes i ++ rest) :
    ∀ i i', PrefixAgree (prefixes i) (prefixes i') ∨
      PrefixAgree (prefixes i') (prefixes i) := by
  have hstep : ∀ i, PrefixAgree (prefixes i) (prefixes (i + 1)) := by
    intro i k hk
    obtain ⟨rest, hrest⟩ := hnested i
    rw [hrest, List.getElem?_append_left hk, List.getElem?_eq_getElem hk]
  have hmono : ∀ i d, PrefixAgree (prefixes i) (prefixes (i + d)) := by
    intro i d
    induction d with
    | zero => simpa using PrefixAgree.refl (prefixes i)
    | succ d ih => exact ih.trans (hstep (i + d))
  intro i i'
  rcases le_total i i' with h | h
  · exact Or.inl (by simpa [Nat.add_sub_cancel' h] using hmono i (i' - i))
  · exact Or.inr (by simpa [Nat.add_sub_cancel' h] using hmono i' (i - i'))

/-- **The core obstruction.**  No nested family of bit strings with a computable
enumeration can have vanishing universal-semimeasure mass.
Paper node: `thm:strict` -/
theorem no_ce_null_prefix_family (M : UniversalContinuousSemimeasure)
    (prefixes : ℕ → List Bool)
    (hnested : ∀ i, ∃ rest, prefixes (i + 1) = prefixes i ++ rest)
    (henum : Computable enum)
    (hsound : ∀ j, ∃ i, enum j = prefixes i)
    (hcov : ∀ i, ∃ j, enum j = prefixes i)
    (hmass : Tendsto (fun i ↦ M.mass (prefixes i)) atTop (𝓝 0)) : False := by
  have hcomparable : ∀ j j', PrefixAgree (enum j) (enum j') ∨
      PrefixAgree (enum j') (enum j) := by
    intro j j'
    obtain ⟨i, hi⟩ := hsound j
    obtain ⟨i', hi'⟩ := hsound j'
    rw [hi, hi']
    exact prefixAgree_of_nested hnested i i'
  obtain ⟨c, hc, hlow⟩ := exists_pos_mass_of_ce_nested M henum hcomparable
  have hall : ∀ i, c ≤ M.mass (prefixes i) := by
    intro i
    obtain ⟨j, hj⟩ := hcov i
    simpa [hj] using hlow j
  have hev : ∀ᶠ i in atTop, M.mass (prefixes i) < c := (tendsto_order.1 hmass).2 c hc
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  exact absurd (hN N le_rfl) (not_lt.2 (hall N))

/-- **`StrictSeparatorPresentation` is unsatisfiable for a computably enumerable prefix
family.**  Its `repetition` field asserts precisely that the prefix *sentences* are
enumerated by a program; whenever those sentences can be decoded back to their strings —
as they can for the concrete `bitPrefixSentence` syntax — the hypothesis below is met and
the presentation cannot exist.
Paper node: `thm:strict` -/
theorem strictSeparatorPresentation_not_ce
    {M : UniversalContinuousSemimeasure} {DP : DeductiveProcess}
    {B : BitPrefixSentences DP} (S : StrictSeparatorPresentation M B)
    (henum : Computable enum)
    (hsound : ∀ j, ∃ i, enum j = S.prefixes i)
    (hcov : ∀ i, ∃ j, enum j = S.prefixes i) : False :=
  no_ce_null_prefix_family M S.prefixes S.nested henum hsound hcov S.mass_tendsto_zero

#print axioms ceNestedSemimeasure
#print axioms exists_pos_mass_of_ce_nested
#print axioms no_ce_null_prefix_family
#print axioms strictSeparatorPresentation_not_ce

end LogicalInduction
