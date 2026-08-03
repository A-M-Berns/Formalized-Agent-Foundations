import LogicalInduction.Construction.Witnesses.BitPrefixSyntax
import Mathlib.Computability.Halting
import Mathlib.Data.List.Sections


/-!
# Separator data for strict domination of the universal semimeasure (`thm:strict`)

`thm:strict` says a logical inductor's limiting beliefs strictly dominate a universal
continuous semimeasure.  The paper's proof (`app:strict`) runs through a recursively
inseparable pair of c.e. sets: Uniform Non-Dogmatism (`thm:obu`) applied to the c.e.
*constraint theory* of the pair puts a positive floor on the inductor's limiting belief in
the separating bit strings, while a universal semimeasure gives vanishing mass to the
*class* of length-`n` separator prefixes.

This file builds that data over Kleene's pair `A₁ = {e : e(e) ↓ = 1}`, `A₀ = {e : e(e) ↓ =
0}` and discharges the boundary `StrictSeparatorPresentation`
(`Properties/UniversalSemimeasure.lean`): recursive inseparability of the pair, its
dovetailed stage decisions, the c.e. constraint theory they generate over an independent
atom family, the stagewise class of consistent bit strings, and the Kučera–Demuth argument
that a universal semimeasure's mass on those classes tends to zero.

## Why the interface carries a constraint theory and per-stage classes

The stage-`n` constraint is the conjunction of the literals for the bits *decided* by stage
`n`; the undecided bits stay free, so it is not a prefix sentence, and what it constrains
is a whole *set* of length-`n` strings rather than one string per stage.  The market half
of the argument accordingly sums over that set (coherence plus pigeonhole).

The obvious simpler interface — a single nested family of bit prefixes whose
universal-semimeasure mass tends to zero — is not merely inconvenient but impossible, and
`no_ce_null_prefix_family` below proves it: those requirements are jointly unsatisfiable as
soon as the prefix strings admit a computable enumeration, which is exactly what an
efficient repeated enumeration of the associated prefix sentences supplies.  The argument
is elementary and does not even need the lengths to grow.  A computable enumeration of a
*nested* (pairwise comparable) family of strings carries a lower-semicomputable continuous
semimeasure `ceNestedSemimeasure`, of mass `1` on every string that is a prefix of an
enumerated one and `0` elsewhere: comparability is exactly what makes the two children of a
node compete, so the semimeasure inequality holds.  A universal `M` dominates it, so
`M.mass (prefixes i)` stays above a fixed positive constant forever, and cannot tend to
`0`.

Two pieces of that argument are reusable elsewhere: `ceNestedSemimeasure`, a concrete
inhabitant of `LowerSemicomputableContinuousSemimeasure`, and
`exists_code_evaln_of_computable`, which says any computable `ℕ × List Bool → ℕ` meets the
bounded-fuel `approximation_computes` interface.
-/

namespace LogicalInduction

open Filter Topology

-- `Nat.unpair` reduction loops `whnf` on `Nat.sqrt` inside the `Primcodable` instances
-- for the product and list types used below, so `Nat.sqrt` is kept opaque in this file.
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

/-! ### No computably enumerated nested family is null -/

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

/-- No nested family of bit strings with a computable enumeration can have vanishing
universal-semimeasure mass.  This is what rules out presenting the separator data as a
single nested prefix family.
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

/-! ### Kleene's inseparable pair

`A₁ = {e : e(e) ↓ = 1}` and `A₀ = {e : e(e) ↓ = 0}` are disjoint c.e. sets with no
computable separator (`kleene_recursively_inseparable`).  Dovetailing them with `evaln`
gives, at each stage, a finite set of *decided* bits; the undecided bits stay free. -/

/-- The `b`-half of Kleene's diagonal pair: codes whose self-application returns the
numeral of `b`. -/
def kleeneSet (b : Bool) : Set ℕ :=
  {e | (if b then 1 else 0) ∈ (Denumerable.ofNat Nat.Partrec.Code e).eval e}

lemma kleeneSet_disjoint {e : ℕ} (h0 : e ∈ kleeneSet false) (h1 : e ∈ kleeneSet true) :
    False := by
  have h0' : (0 : ℕ) ∈ (Denumerable.ofNat Nat.Partrec.Code e).eval e := by
    simpa [kleeneSet] using h0
  have h1' : (1 : ℕ) ∈ (Denumerable.ofNat Nat.Partrec.Code e).eval e := by
    simpa [kleeneSet] using h1
  exact absurd (Part.mem_unique h0' h1') (by norm_num)

/-- **Recursive inseparability of Kleene's pair.**  No computable predicate contains `A₁`
and avoids `A₀`.  This is the computability-theoretic input behind `thm:strict`; it is what
makes the separator class contain no computable member.
Paper node: `thm:strict` -/
theorem kleene_recursively_inseparable (f : ℕ → Bool) (hf : Computable f)
    (h1 : ∀ e ∈ kleeneSet true, f e = true)
    (h0 : ∀ e ∈ kleeneSet false, f e = false) : False := by
  have hg : Nat.Partrec fun e : ℕ ↦ (Part.some (if f e then 0 else 1) : Part ℕ) := by
    refine Partrec.nat_iff.mp ?_
    exact (Computable.cond hf (Computable.const (0 : ℕ)) (Computable.const (1 : ℕ))).partrec.of_eq
      (fun e ↦ by by_cases h : f e <;> simp [h])
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hg
  set e₀ := Encodable.encode c with he₀
  have hdecode : Denumerable.ofNat Nat.Partrec.Code e₀ = c := by
    simp [he₀, Denumerable.ofNat_encode]
  have hval : (Denumerable.ofNat Nat.Partrec.Code e₀).eval e₀ =
      Part.some (if f e₀ then 0 else 1) := by
    rw [hdecode, hc]
  by_cases hfe : f e₀
  · have hmem : e₀ ∈ kleeneSet false := by
      simp only [kleeneSet, Set.mem_setOf_eq, if_neg (by simp : ¬ (false = true))]
      rw [hval, hfe]
      simp
    exact absurd (h0 e₀ hmem) (by simp [hfe])
  · have hmem : e₀ ∈ kleeneSet true := by
      simp only [kleeneSet, Set.mem_setOf_eq]
      rw [hval]
      simp [hfe]
    exact absurd (h1 e₀ hmem) (by simp [hfe])

/-- The intended (non-computable) separator: the characteristic function of `A₁`. -/
noncomputable def kleeneAssignment (e : ℕ) : Bool := by
  classical exact decide (e ∈ kleeneSet true)

/-- Stage-`n` dovetailed decision of bit `e`: `evaln` with fuel `n`. -/
def kleeneDecide (n e : ℕ) : Option Bool :=
  match Nat.Partrec.Code.evaln n (Denumerable.ofNat Nat.Partrec.Code e) e with
  | some 0 => some false
  | some 1 => some true
  | _ => none

lemma kleeneDecide_sound {n e : ℕ} {b : Bool} (h : kleeneDecide n e = some b) :
    e ∈ kleeneSet b := by
  unfold kleeneDecide at h
  rcases hev : Nat.Partrec.Code.evaln n (Denumerable.ofNat Nat.Partrec.Code e) e with _ | v
  · rw [hev] at h; simp at h
  · have hmem : v ∈ (Denumerable.ofNat Nat.Partrec.Code e).eval e :=
      Nat.Partrec.Code.evaln_sound hev
    rw [hev] at h
    match v, h with
    | 0, h => simpa [kleeneSet, (by simpa using h : b = false)] using hmem
    | 1, h => simpa [kleeneSet, (by simpa using h : b = true)] using hmem
    | (v + 2), h => simp at h

/-- A decided bit is decided the way the intended separator decides it. -/
lemma kleeneAssignment_of_decide {n e : ℕ} {b : Bool} (h : kleeneDecide n e = some b) :
    kleeneAssignment e = b := by
  classical
  have hmem := kleeneDecide_sound h
  cases b with
  | false =>
      have : e ∉ kleeneSet true := fun h1 ↦ kleeneSet_disjoint hmem h1
      simp [kleeneAssignment, this]
  | true => simp [kleeneAssignment, hmem]

/-! ### The constraint theory and its stagewise consistent class -/

/-- Stage-`n` constraint: the conjunction of the literals for the bits decided by stage
`n`.  Undecided bits are left free, so this is *not* a prefix sentence. -/
def separatorConstraintAux (atom : ℕ → Sentence) (n : ℕ) : ℕ → Sentence
  | 0 => ⊤
  | e + 1 =>
      match kleeneDecide n e with
      | none => separatorConstraintAux atom n e
      | some b => separatorConstraintAux atom n e ⋏ bitPrefixLiteral atom e b

/-- Stage-`n` constraint: the literals for all bits decided by stage `n`. -/
def separatorConstraint (atom : ℕ → Sentence) (n : ℕ) : Sentence :=
  separatorConstraintAux atom n n

lemma holds_separatorConstraintAux (v : PCWorld) (atom : ℕ → Sentence) (n : ℕ) :
    ∀ e, v.Holds (separatorConstraintAux atom n e) ↔
      ∀ e' < e, ∀ b, kleeneDecide n e' = some b → (v.Holds (atom e') ↔ b = true) := by
  intro e
  induction e with
  | zero =>
      simp [separatorConstraintAux, PCWorld.Holds,
        LO.Propositional.Formula.Boolean.val]
  | succ e ih =>
      rcases hb : kleeneDecide n e with _ | b
      · rw [show separatorConstraintAux atom n (e + 1) =
          separatorConstraintAux atom n e from by
            simp only [separatorConstraintAux, hb], ih]
        constructor
        · intro h e' he' b' hb'
          rcases Nat.lt_succ_iff_lt_or_eq.mp he' with h' | h'
          · exact h e' h' b' hb'
          · exact absurd (h' ▸ hb') (by rw [hb]; simp)
        · intro h e' he' b' hb'
          exact h e' (Nat.lt_succ_of_lt he') b' hb'
      · rw [show separatorConstraintAux atom n (e + 1) =
          separatorConstraintAux atom n e ⋏ bitPrefixLiteral atom e b from by
            simp only [separatorConstraintAux, hb], PCWorld.holds_and, ih,
          PCWorld.holds_bitPrefixLiteral]
        constructor
        · rintro ⟨hprev, hlit⟩ e' he' b' hb'
          rcases Nat.lt_succ_iff_lt_or_eq.mp he' with h' | h'
          · exact hprev e' h' b' hb'
          · subst h'
            rw [hb] at hb'
            simpa using (Option.some.inj hb') ▸ hlit
        · intro h
          exact ⟨fun e' he' b' hb' ↦ h e' (Nat.lt_succ_of_lt he') b' hb',
            h e (Nat.lt_succ_self e) b hb⟩

lemma holds_separatorConstraint (v : PCWorld) (atom : ℕ → Sentence) (n : ℕ) :
    v.Holds (separatorConstraint atom n) ↔
      ∀ e < n, ∀ b, kleeneDecide n e = some b → (v.Holds (atom e) ↔ b = true) :=
  holds_separatorConstraintAux v atom n n

/-! ### Gödel codes of the constraint sentences

Foundation's propositional encoding is a plain tagged pairing, so the conjunction /
negation / `⊤` shells are literal `Nat.pair` arithmetic (`rfl`).  That makes the whole
constraint stream computable by a `Nat.rec` over the decided bits, which is what
`CEEnumeration` — and hence `EfficientRepeatedEnumeration` — needs. -/

/-- Code of `φ ⋏ ψ` from the codes of `φ` and `ψ`. -/
def sepAndCode (x y : ℕ) : ℕ := Nat.pair 3 (Nat.pair x y) + 1

/-- Code of `∼φ` from the code of `φ`. -/
def sepNegCode (x : ℕ) : ℕ := Nat.pair 2 (Nat.pair x (Nat.pair 0 0 + 1)) + 1

/-- Code of `⊤`. -/
def sepTopCode : ℕ := Nat.pair 2 (Nat.pair (Nat.pair 0 0 + 1) (Nat.pair 0 0 + 1)) + 1

lemma encode_sepAnd (φ ψ : Sentence) :
    Encodable.encode (φ ⋏ ψ) = sepAndCode (Encodable.encode φ) (Encodable.encode ψ) := rfl

lemma encode_sepNeg (φ : Sentence) :
    Encodable.encode (∼φ) = sepNegCode (Encodable.encode φ) := rfl

lemma encode_sepTop : Encodable.encode (⊤ : Sentence) = sepTopCode := rfl

/-- The stage decision as a numeral: `0` undecided, `1` decided `false`, `2` decided
`true`.  This is the shape a `Nat.rec` can branch on. -/
def kleeneDecideNat (n e : ℕ) : ℕ :=
  match Nat.Partrec.Code.evaln n (Denumerable.ofNat Nat.Partrec.Code e) e with
  | some 0 => 1
  | some 1 => 2
  | _ => 0

lemma kleeneDecideNat_eq (n e : ℕ) :
    kleeneDecideNat n e =
      match kleeneDecide n e with
      | none => 0
      | some false => 1
      | some true => 2 := by
  unfold kleeneDecideNat kleeneDecide
  rcases Nat.Partrec.Code.evaln n (Denumerable.ofNat Nat.Partrec.Code e) e with _ | v
  · rfl
  · match v with
    | 0 => rfl
    | 1 => rfl
    | (v + 2) => rfl

/-- The code mirror of `separatorConstraintAux`. -/
def separatorConstraintCodeAux (atomCode : ℕ → ℕ) (n : ℕ) : ℕ → ℕ
  | 0 => sepTopCode
  | e + 1 =>
      if kleeneDecideNat n e = 0 then separatorConstraintCodeAux atomCode n e
      else sepAndCode (separatorConstraintCodeAux atomCode n e)
        (if kleeneDecideNat n e = 2 then atomCode e else sepNegCode (atomCode e))

lemma separatorConstraintCodeAux_eq (atom : ℕ → Sentence) (n : ℕ) :
    ∀ e, separatorConstraintCodeAux (fun k ↦ Encodable.encode (atom k)) n e =
      Encodable.encode (separatorConstraintAux atom n e) := by
  intro e
  induction e with
  | zero => simp [separatorConstraintCodeAux, separatorConstraintAux, encode_sepTop]
  | succ e ih =>
      rcases hb : kleeneDecide n e with _ | b
      · have h0 : kleeneDecideNat n e = 0 := by rw [kleeneDecideNat_eq, hb]
        rw [show separatorConstraintAux atom n (e + 1) =
            separatorConstraintAux atom n e from by simp only [separatorConstraintAux, hb]]
        simp only [separatorConstraintCodeAux, h0]
        exact ih
      · have hlit : separatorConstraintAux atom n (e + 1) =
            separatorConstraintAux atom n e ⋏ bitPrefixLiteral atom e b := by
          simp only [separatorConstraintAux, hb]
        cases b with
        | false =>
            have h1 : kleeneDecideNat n e = 1 := by rw [kleeneDecideNat_eq, hb]
            rw [hlit, encode_sepAnd, ← ih]
            simp [separatorConstraintCodeAux, h1, bitPrefixLiteral, encode_sepNeg]
        | true =>
            have h2 : kleeneDecideNat n e = 2 := by rw [kleeneDecideNat_eq, hb]
            rw [hlit, encode_sepAnd, ← ih]
            simp [separatorConstraintCodeAux, h2, bitPrefixLiteral]

lemma kleeneDecideNat_computable :
    Computable fun p : ℕ × ℕ ↦ kleeneDecideNat p.1 p.2 := by
  have hcode : Computable fun p : ℕ × ℕ ↦ Denumerable.ofNat Nat.Partrec.Code p.2 :=
    (Primrec.ofNat Nat.Partrec.Code).to_comp.comp Computable.snd
  have hev : Computable fun p : ℕ × ℕ ↦
      Nat.Partrec.Code.evaln p.1 (Denumerable.ofNat Nat.Partrec.Code p.2) p.2 :=
    Nat.Partrec.Code.primrec_evaln.to_comp.comp
      ((Computable.fst.pair hcode).pair Computable.snd)
  have hbranch : Computable fun w : ℕ ↦ if w = 0 then 1 else if w = 1 then 2 else 0 := by
    have h1 : Computable fun w : ℕ ↦ decide (w = 0) :=
      Computable.comp ((Primrec.eq (α := ℕ)).decide).to_comp
        (Computable.id.pair (Computable.const 0))
    have h2 : Computable fun w : ℕ ↦ decide (w = 1) :=
      Computable.comp ((Primrec.eq (α := ℕ)).decide).to_comp
        (Computable.id.pair (Computable.const 1))
    exact (Computable.cond h1 (Computable.const 1)
      (Computable.cond h2 (Computable.const 2) (Computable.const 0))).of_eq (by
        intro w
        by_cases hw0 : w = 0
        · simp [hw0]
        · by_cases hw1 : w = 1 <;> simp [hw0, hw1])
  refine (Computable.comp (Primrec.option_getD.to_comp)
    ((Computable.option_map hev (hbranch.comp Computable.snd).to₂).pair
      (Computable.const 0))).of_eq ?_
  rintro ⟨n, e⟩
  unfold kleeneDecideNat
  rcases Nat.Partrec.Code.evaln n (Denumerable.ofNat Nat.Partrec.Code e) e with _ | v
  · rfl
  · match v with
    | 0 => rfl
    | 1 => rfl
    | (v + 2) => simp

lemma separatorConstraintCodeAux_computable {atomCode : ℕ → ℕ}
    (hatom : Computable atomCode) :
    Computable fun p : ℕ × ℕ ↦ separatorConstraintCodeAux atomCode p.1 p.2 := by
  have hdec : Computable fun r : (ℕ × ℕ) × (ℕ × ℕ) ↦
      kleeneDecideNat r.1.1 r.2.1 :=
    kleeneDecideNat_computable.comp
      ((Computable.fst.comp Computable.fst).pair (Computable.fst.comp Computable.snd))
  have hzero : Computable fun r : (ℕ × ℕ) × (ℕ × ℕ) ↦
      decide (kleeneDecideNat r.1.1 r.2.1 = 0) :=
    Computable.comp ((Primrec.eq (α := ℕ)).decide).to_comp
      (hdec.pair (Computable.const 0))
  have htwo : Computable fun r : (ℕ × ℕ) × (ℕ × ℕ) ↦
      decide (kleeneDecideNat r.1.1 r.2.1 = 2) :=
    Computable.comp ((Primrec.eq (α := ℕ)).decide).to_comp
      (hdec.pair (Computable.const 2))
  have hatomAt : Computable fun r : (ℕ × ℕ) × (ℕ × ℕ) ↦ atomCode r.2.1 :=
    hatom.comp (Computable.fst.comp Computable.snd)
  have hlit : Computable fun r : (ℕ × ℕ) × (ℕ × ℕ) ↦
      if kleeneDecideNat r.1.1 r.2.1 = 2 then atomCode r.2.1
        else sepNegCode (atomCode r.2.1) := by
    have hneg : Computable fun r : (ℕ × ℕ) × (ℕ × ℕ) ↦ sepNegCode (atomCode r.2.1) := by
      unfold sepNegCode
      exact Computable.succ.comp (Computable₂.comp Primrec₂.natPair.to_comp
        (Computable.const 2)
        (Computable₂.comp Primrec₂.natPair.to_comp hatomAt
          (Computable.const (Nat.pair 0 0 + 1))))
    exact (Computable.cond htwo hatomAt hneg).of_eq (by
      intro r
      by_cases h : kleeneDecideNat r.1.1 r.2.1 = 2 <;> simp [h])
  have hand : Computable fun r : (ℕ × ℕ) × (ℕ × ℕ) ↦
      sepAndCode r.2.2 (if kleeneDecideNat r.1.1 r.2.1 = 2 then atomCode r.2.1
        else sepNegCode (atomCode r.2.1)) := by
    unfold sepAndCode
    exact Computable.succ.comp (Computable₂.comp Primrec₂.natPair.to_comp
      (Computable.const 3)
      (Computable₂.comp Primrec₂.natPair.to_comp
        (Computable.snd.comp Computable.snd) hlit))
  have hstep : Computable₂ fun (p : ℕ × ℕ) (q : ℕ × ℕ) ↦
      if kleeneDecideNat p.1 q.1 = 0 then q.2
      else sepAndCode q.2 (if kleeneDecideNat p.1 q.1 = 2 then atomCode q.1
        else sepNegCode (atomCode q.1)) :=
    (Computable.cond hzero (Computable.snd.comp Computable.snd) hand).of_eq (by
      intro r
      by_cases h : kleeneDecideNat r.1.1 r.2.1 = 0 <;> simp [h])
  refine (Computable.nat_rec Computable.snd (Computable.const sepTopCode) hstep).of_eq ?_
  rintro ⟨n, e⟩
  induction e with
  | zero => rfl
  | succ e ih =>
      simp only [separatorConstraintCodeAux]
      by_cases h : kleeneDecideNat n e = 0 <;> simp [h, ← ih]

/-- The constraint stream's Gödel codes are computable whenever the atom family's are. -/
lemma separatorConstraint_computable {atom : ℕ → Sentence}
    (hatom : Computable fun k ↦ Encodable.encode (atom k)) :
    Computable fun n ↦ Encodable.encode (separatorConstraint atom n) :=
  ((separatorConstraintCodeAux_computable hatom).comp
    (Computable.id.pair Computable.id)).of_eq (by
      intro n
      exact separatorConstraintCodeAux_eq atom n n)

/-- A program enumerating the constraint theory exists. -/
lemma exists_separatorConstraintCode {atom : ℕ → Sentence}
    (hatom : Computable fun k ↦ Encodable.encode (atom k)) :
    ∃ c : Nat.Partrec.Code,
      (∀ i, ∃ fuel, codeEvalnNat c (Nat.pair fuel i) =
        Encodable.encode (separatorConstraint atom i) + 1) ∧
      (∀ z, codeEvalnNat c z ≠ 0 →
        ∃ i, codeEvalnNat c z = Encodable.encode (separatorConstraint atom i) + 1) := by
  have hnp : Nat.Partrec fun z ↦ Part.bind (Encodable.decode (α := ℕ) z)
      fun a ↦ Part.map Encodable.encode
        (Part.some (Encodable.encode (separatorConstraint atom a))) :=
    separatorConstraint_computable hatom
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hnp
  have hval : ∀ i, Encodable.encode (separatorConstraint atom i) ∈ c.eval i := by
    intro i
    rw [hc]
    simp
  refine ⟨c, fun i ↦ ?_, fun z hz ↦ ?_⟩
  · obtain ⟨fuel, hfuel⟩ := Nat.Partrec.Code.evaln_complete.mp (hval i)
    refine ⟨fuel, ?_⟩
    rw [codeEvalnNat]
    simp only [Nat.unpair_pair]
    rw [Option.mem_def.mp hfuel]
  · rcases hev : Nat.Partrec.Code.evaln z.unpair.1 c z.unpair.2 with _ | w
    · rw [codeEvalnNat, hev] at hz
      simp at hz
    · refine ⟨z.unpair.2, ?_⟩
      have hmem : w ∈ c.eval z.unpair.2 := Nat.Partrec.Code.evaln_sound hev
      have hw := Part.mem_unique hmem (hval z.unpair.2)
      rw [codeEvalnNat, hev, hw]

/-- The constraint theory is computably enumerable, so `EfficientRepeatedEnumeration.ofCE`
supplies the interface's `repetition` field. -/
noncomputable def separatorConstraintCE {atom : ℕ → Sentence}
    (hatom : Computable fun k ↦ Encodable.encode (atom k)) :
    CEEnumeration (separatorConstraint atom) where
  code := Classical.choose (exists_separatorConstraintCode hatom)
  halts := (Classical.choose_spec (exists_separatorConstraintCode hatom)).1
  outputs_sound := (Classical.choose_spec (exists_separatorConstraintCode hatom)).2

/-- All bit strings of a given length. -/
def allBitStrings (n : ℕ) : List (List Bool) :=
  List.sections (List.replicate n [false, true])

lemma mem_allBitStrings {σ : List Bool} {n : ℕ} :
    σ ∈ allBitStrings n ↔ σ.length = n := by
  rw [allBitStrings, List.mem_sections]
  constructor
  · intro h
    simpa using h.length_eq
  · intro h
    subst h
    induction σ with
    | nil => simp
    | cons b σ ih =>
        rw [List.length_cons, List.replicate_succ]
        exact List.Forall₂.cons (by cases b <;> simp) ih

/-- The stage-`n` class: every length-`n` string agreeing with the bits decided by stage
`n`. -/
def separatorConsistentAt (n : ℕ) : List (List Bool) :=
  (allBitStrings n).filter fun σ ↦
    (List.range n).all fun e ↦
      match kleeneDecide n e with
      | none => true
      | some b => σ.getD e false == b

lemma mem_separatorConsistentAt {σ : List Bool} {n : ℕ} :
    σ ∈ separatorConsistentAt n ↔
      σ.length = n ∧ ∀ e < n, ∀ b, kleeneDecide n e = some b → σ.getD e false = b := by
  rw [separatorConsistentAt, List.mem_filter, mem_allBitStrings]
  constructor
  · rintro ⟨hlen, hall⟩
    refine ⟨hlen, fun e he b hb ↦ ?_⟩
    have := (List.all_eq_true.1 (by simpa using hall)) e (List.mem_range.2 he)
    rw [hb] at this
    simpa using this
  · rintro ⟨hlen, hall⟩
    refine ⟨hlen, ?_⟩
    simp only [List.all_eq_true]
    intro e he
    rcases hb : kleeneDecide n e with _ | b
    · rfl
    · simpa using hall e (List.mem_range.1 he) b hb

/-! ### The stage class masses are non-increasing

Nothing computability-theoretic is needed here.  A stage-`(n+1)` consistent string
truncates to a stage-`n` consistent one — stage decisions only grow with fuel — and
`children_le` bounds the two children of a node by the node itself.  So the class masses
form a non-increasing sequence, converging to an infimum `r ≥ 0`, and `thm:strict` becomes
the assertion that `r = 0`.

The sums are taken over `p`-selected parts of the class, because the Kučera–Demuth
argument below needs the same monotonicity for the parts on which a fixed bit is `0`
(resp. `1`). -/

lemma append_bit_inj {a b : List Bool} {x y : Bool} (h : a ++ [x] = b ++ [y]) :
    a = b ∧ x = y := by
  have hxy : x = y := by
    have hlast := congrArg List.getLast? h
    simpa [List.getLast?_concat] using hlast
  subst hxy
  exact ⟨List.append_cancel_right h, rfl⟩

/-- **Children never gain mass.**  If every member of `T` has length `n+1` and truncates
into `S`, then `T` carries at most the mass of `S`: this is `children_le` summed over the
fibres of the truncation map. -/
lemma ContinuousSemimeasure.sum_le_of_take (M : ContinuousSemimeasure) {n : ℕ}
    {S T : Finset (List Bool)}
    (hlen : ∀ σ ∈ T, σ.length = n + 1) (htake : ∀ σ ∈ T, σ.take n ∈ S) :
    ∑ σ ∈ T, M.mass σ ≤ ∑ τ ∈ S, M.mass τ := by
  classical
  have hsub : T ⊆ S.biUnion fun τ ↦ ({τ ++ [false], τ ++ [true]} : Finset (List Bool)) := by
    intro σ hσ
    refine Finset.mem_biUnion.2 ⟨σ.take n, htake σ hσ, ?_⟩
    obtain ⟨b, hb⟩ := List.length_eq_one_iff.mp
      (show (σ.drop n).length = 1 by simp [hlen σ hσ])
    have hsplit : σ.take n ++ [b] = σ := by rw [← hb, List.take_append_drop]
    cases b
    · exact Finset.mem_insert.2 (Or.inl hsplit.symm)
    · exact Finset.mem_insert_of_mem (Finset.mem_singleton.2 hsplit.symm)
  have hdisj : (S : Set (List Bool)).PairwiseDisjoint
      fun τ ↦ ({τ ++ [false], τ ++ [true]} : Finset (List Bool)) := by
    intro a _ b _ hab
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_insert,
      Finset.mem_singleton]
    rintro x (rfl | rfl) <;> rintro (h | h) <;> exact hab (append_bit_inj h).1
  calc ∑ σ ∈ T, M.mass σ
      ≤ ∑ σ ∈ S.biUnion fun τ ↦ ({τ ++ [false], τ ++ [true]} : Finset (List Bool)),
          M.mass σ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ ↦ M.nonneg i
    _ = ∑ τ ∈ S, ∑ σ ∈ ({τ ++ [false], τ ++ [true]} : Finset (List Bool)), M.mass σ :=
        Finset.sum_biUnion hdisj
    _ ≤ ∑ τ ∈ S, M.mass τ := Finset.sum_le_sum fun τ _ ↦ by
        rw [Finset.sum_pair (by simp)]
        exact M.children_le τ

lemma allBitStrings_succ (n : ℕ) :
    allBitStrings (n + 1) = (allBitStrings n).flatMap fun σ ↦ [false :: σ, true :: σ] := by
  simp [allBitStrings, List.replicate_succ]

lemma allBitStrings_nodup (n : ℕ) : (allBitStrings n).Nodup := by
  induction n with
  | zero => simp [allBitStrings]
  | succ n ih =>
      rw [allBitStrings_succ]
      refine List.nodup_flatMap.2 ⟨fun σ _ ↦ by simp, List.Pairwise.imp ?_ ih⟩
      intro a b hab
      simp only [Function.onFun, List.disjoint_left, List.mem_cons,
        List.not_mem_nil, or_false]
      rintro x (rfl | rfl) <;> rintro (h | h) <;> simp_all

lemma separatorConsistentAt_nodup (n : ℕ) : (separatorConsistentAt n).Nodup :=
  List.Nodup.filter _ (allBitStrings_nodup n)

/-- Stage decisions only grow: `evaln` is monotone in its fuel. -/
lemma kleeneDecide_mono {n n' e : ℕ} {b : Bool} (h : n ≤ n')
    (hd : kleeneDecide n e = some b) : kleeneDecide n' e = some b := by
  unfold kleeneDecide at hd ⊢
  rcases hev : Nat.Partrec.Code.evaln n (Denumerable.ofNat Nat.Partrec.Code e) e with _ | v
  · rw [hev] at hd; simp at hd
  · have hmono : Nat.Partrec.Code.evaln n' (Denumerable.ofNat Nat.Partrec.Code e) e =
        some v := Nat.Partrec.Code.evaln_mono h hev
    rw [hmono]
    rw [hev] at hd
    exact hd

lemma getD_take_of_lt {σ : List Bool} {n e : ℕ} (h : e < n) :
    (σ.take n).getD e false = σ.getD e false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt h,
    ← List.getD_eq_getElem?_getD]

lemma take_mem_separatorConsistentAt {σ : List Bool} {n : ℕ}
    (h : σ ∈ separatorConsistentAt (n + 1)) : σ.take n ∈ separatorConsistentAt n := by
  obtain ⟨hlen, hbits⟩ := mem_separatorConsistentAt.1 h
  refine mem_separatorConsistentAt.2 ⟨by simp [hlen], fun e he b hb ↦ ?_⟩
  rw [getD_take_of_lt he]
  exact hbits e (Nat.lt_succ_of_lt he) b (kleeneDecide_mono (Nat.le_succ n) hb)

/-- The mass of the part of the stage-`n` class selected by `p`. -/
noncomputable def classMass (M : ContinuousSemimeasure) (p : List Bool → Bool) (n : ℕ) :
    ℝ :=
  (((separatorConsistentAt n).filter p).map M.mass).sum

lemma classMass_eq_finsetSum (M : ContinuousSemimeasure) (p : List Bool → Bool) (n : ℕ) :
    classMass M p n = ∑ σ ∈ ((separatorConsistentAt n).filter p).toFinset, M.mass σ :=
  (List.sum_toFinset _ (List.Nodup.filter _ (separatorConsistentAt_nodup n))).symm

lemma classMass_nonneg (M : ContinuousSemimeasure) (p : List Bool → Bool) (n : ℕ) :
    0 ≤ classMass M p n := by
  rw [classMass_eq_finsetSum]
  exact Finset.sum_nonneg fun σ _ ↦ M.nonneg σ

/-- The unrestricted class mass is the sum appearing in `mass_class_tendsto_zero`. -/
lemma classMass_true (M : ContinuousSemimeasure) (n : ℕ) :
    classMass M (fun _ ↦ true) n = ((separatorConsistentAt n).map M.mass).sum := by
  simp [classMass]

/-- One antitonicity step, for any selector stable under truncation at length `n`. -/
lemma classMass_succ_le (M : ContinuousSemimeasure) {p : List Bool → Bool} {n : ℕ}
    (hp : ∀ σ : List Bool, σ.length = n + 1 → p σ = true → p (σ.take n) = true) :
    classMass M p (n + 1) ≤ classMass M p n := by
  rw [classMass_eq_finsetSum, classMass_eq_finsetSum]
  refine M.sum_le_of_take (n := n) ?_ ?_
  · intro σ hσ
    obtain ⟨hmem, -⟩ := List.mem_filter.1 (List.mem_toFinset.1 hσ)
    exact (mem_separatorConsistentAt.1 hmem).1
  · intro σ hσ
    obtain ⟨hmem, hpσ⟩ := List.mem_filter.1 (List.mem_toFinset.1 hσ)
    refine List.mem_toFinset.2 (List.mem_filter.2 ⟨take_mem_separatorConsistentAt hmem, ?_⟩)
    exact hp σ (mem_separatorConsistentAt.1 hmem).1 hpσ

/-- The class masses are non-increasing. -/
lemma classMass_antitone (M : ContinuousSemimeasure) :
    Antitone (classMass M fun _ ↦ true) :=
  antitone_nat_of_succ_le fun _ ↦ classMass_succ_le M fun _ _ _ ↦ rfl

/-- The same monotonicity for the part of the class fixing bit `j` to `b`, valid from
stage `j + 1` on (before that the bit is not even present in the strings). -/
lemma classMass_bit_le (M : ContinuousSemimeasure) (j : ℕ) (b : Bool) {n n' : ℕ}
    (hj : j < n) (hn : n ≤ n') :
    classMass M (fun σ ↦ σ.getD j false == b) n' ≤
      classMass M (fun σ ↦ σ.getD j false == b) n := by
  induction n', hn using Nat.le_induction with
  | base => exact le_rfl
  | succ m hm ih =>
      refine le_trans (classMass_succ_le M ?_) ih
      intro σ _ hpσ
      rw [getD_take_of_lt (lt_of_lt_of_le hj hm)]
      exact hpσ

/-! ### Splitting the class along one bit -/

private lemma sum_filter_add_sum_filter_not {α : Type*} (f : α → ℝ) (p : α → Bool) :
    ∀ L : List α,
      (((L.filter fun a ↦ p a).map f).sum + ((L.filter fun a ↦ !p a).map f).sum)
        = (L.map f).sum
  | [] => by simp
  | a :: L => by
      have ih := sum_filter_add_sum_filter_not f p L
      by_cases h : p a = true <;>
        simp [h] at ih ⊢ <;> linarith

/-- The class splits into the part where bit `j` is `b` and the part where it is not. -/
lemma classMass_bit_split (M : ContinuousSemimeasure) (j : ℕ) (b : Bool) (n : ℕ) :
    classMass M (fun σ ↦ σ.getD j false == b) n
        + classMass M (fun σ ↦ σ.getD j false == !b) n
      = classMass M (fun _ ↦ true) n := by
  have hnot : ∀ σ : List Bool, (!(σ.getD j false == b)) = (σ.getD j false == !b) := by
    intro σ; cases b <;> cases hσ : σ.getD j false <;> simp
  have h := sum_filter_add_sum_filter_not M.mass
    (fun σ : List Bool ↦ σ.getD j false == b) (separatorConsistentAt n)
  simp only [hnot] at h
  simp only [classMass, List.filter_true]
  exact h

/-- Once bit `j` is decided at stage `n`, the class holds no string disagreeing with it. -/
lemma classMass_bit_zero_of_decided (M : ContinuousSemimeasure) {j n : ℕ} {b : Bool}
    (hj : j < n) (hd : kleeneDecide n j = some b) :
    classMass M (fun σ ↦ σ.getD j false == !b) n = 0 := by
  have hnil : ((separatorConsistentAt n).filter fun σ ↦ σ.getD j false == !b) = [] := by
    rw [List.filter_eq_nil_iff]
    intro σ hσ hp
    rw [(mem_separatorConsistentAt.1 hσ).2 j hj b hd] at hp
    cases b <;> simp at hp
  rw [classMass, hnil]
  simp

/-- The decided half of Kleene's pair is eventually decided by the dovetailing. -/
lemma exists_kleeneDecide {e : ℕ} {b : Bool} (h : e ∈ kleeneSet b) :
    ∃ n, kleeneDecide n e = some b := by
  obtain ⟨n, hn⟩ := Nat.Partrec.Code.evaln_complete.mp h
  refine ⟨n, ?_⟩
  have hn' : Nat.Partrec.Code.evaln n (Denumerable.ofNat Nat.Partrec.Code e) e =
      some (if b then 1 else 0) := hn
  cases b <;> simp [kleeneDecide, hn']

/-- If bit `j` really belongs to the `b`-half of Kleene's pair, then from the pivot stage
`k` on, the *other* half of the class is small: the `b`-part keeps mass `≥ r` forever,
while the whole class never exceeds `6r/5`. -/
lemma classMass_wrong_bit_lt (M : ContinuousSemimeasure) {r : ℝ} {k : ℕ}
    (hle : ∀ n, r ≤ classMass M (fun _ ↦ true) n)
    (hk : classMass M (fun _ ↦ true) k < 6 * r / 5)
    {j : ℕ} {b : Bool} (hb : j ∈ kleeneSet b) {s : ℕ} (hks : k ≤ s) (hjs : j < s) :
    classMass M (fun σ ↦ σ.getD j false == !b) s < r / 5 := by
  obtain ⟨N, hN⟩ := exists_kleeneDecide hb
  set S := max (max s N) (j + 1) with hSdef
  have hsS : s ≤ S := le_trans (le_max_left s N) (le_max_left _ _)
  have hNS : N ≤ S := le_trans (le_max_right s N) (le_max_left _ _)
  have hjS : j < S := lt_of_lt_of_le (Nat.lt_succ_self j) (le_max_right _ _)
  have hzero : classMass M (fun σ ↦ σ.getD j false == !b) S = 0 :=
    classMass_bit_zero_of_decided M hjS (kleeneDecide_mono hNS hN)
  have hsplitS := classMass_bit_split M j b S
  have hsplits := classMass_bit_split M j b s
  have hbig : classMass M (fun σ ↦ σ.getD j false == b) S ≤
      classMass M (fun σ ↦ σ.getD j false == b) s := classMass_bit_le M j b hjs hsS
  have hks' : classMass M (fun _ ↦ true) s ≤ classMass M (fun _ ↦ true) k :=
    classMass_antitone M hks
  have hrS := hle S
  linarith

/-! ### Bounded-fuel access to the approximants

The search below must run the approximation program itself, so it works with the
*bounded-fuel* values: whatever `M.approximation_code` has printed within `fuel` steps, and
`0` where it has not printed yet.  Underestimating is harmless — the search only needs a
lower bound on the class mass, and each individual value is either the true approximant or
`0`, both of which are below the mass. -/

/-- The bounded-fuel reading of `M`'s approximation program. -/
def boundedApprox (M : LowerSemicomputableContinuousSemimeasure) (fuel t : ℕ)
    (σ : List Bool) : ℚ :=
  ((M.approximation_code.evaln fuel (Nat.pair t (Encodable.encode σ))).bind
    fun v ↦ Encodable.decode (α := ℚ) v).getD 0

lemma boundedApprox_eq (M : LowerSemicomputableContinuousSemimeasure) (fuel t : ℕ)
    (σ : List Bool) :
    boundedApprox M fuel t σ = 0 ∨ boundedApprox M fuel t σ = M.approximation t σ := by
  unfold boundedApprox
  rcases hev : M.approximation_code.evaln fuel (Nat.pair t (Encodable.encode σ)) with _ | v
  · exact Or.inl (by simp)
  · obtain ⟨fuel', hfuel'⟩ := M.approximation_computes t σ
    have h1 : v ∈ M.approximation_code.eval (Nat.pair t (Encodable.encode σ)) :=
      Nat.Partrec.Code.evaln_sound hev
    have h2 : Encodable.encode (M.approximation t σ) ∈
        M.approximation_code.eval (Nat.pair t (Encodable.encode σ)) :=
      Nat.Partrec.Code.evaln_sound hfuel'
    exact Or.inr (by simp [Part.mem_unique h1 h2, Encodable.encodek])

lemma boundedApprox_le_mass (M : LowerSemicomputableContinuousSemimeasure) (fuel t : ℕ)
    (σ : List Bool) : ((boundedApprox M fuel t σ : ℚ) : ℝ) ≤ M.mass σ := by
  rcases boundedApprox_eq M fuel t σ with h | h
  · rw [h]; simpa using M.nonneg σ
  · rw [h]; exact M.approximation_le t σ

/-- Enough fuel makes the program print on every string of a finite list. -/
lemma exists_fuel_evaln (M : LowerSemicomputableContinuousSemimeasure) (t : ℕ) :
    ∀ L : List (List Bool), ∃ fuel, ∀ σ ∈ L,
      M.approximation_code.evaln fuel (Nat.pair t (Encodable.encode σ)) =
        some (Encodable.encode (M.approximation t σ))
  | [] => ⟨0, by simp⟩
  | σ :: L => by
      obtain ⟨fuel, hfuel⟩ := exists_fuel_evaln M t L
      obtain ⟨fuel', hfuel'⟩ := M.approximation_computes t σ
      refine ⟨max fuel fuel', fun τ hτ ↦ ?_⟩
      rcases List.mem_cons.1 hτ with rfl | hτ
      · exact Nat.Partrec.Code.evaln_mono (le_max_right _ _) hfuel'
      · exact Nat.Partrec.Code.evaln_mono (le_max_left _ _) (hfuel τ hτ)

lemma exists_fuel_boundedApprox (M : LowerSemicomputableContinuousSemimeasure) (t : ℕ)
    (L : List (List Bool)) :
    ∃ fuel, ∀ σ ∈ L, boundedApprox M fuel t σ = M.approximation t σ := by
  obtain ⟨fuel, hfuel⟩ := exists_fuel_evaln M t L
  exact ⟨fuel, fun σ hσ ↦ by simp [boundedApprox, hfuel σ hσ, Encodable.encodek]⟩

/-! ### The stage classes and the search are programs

The Kučera–Demuth separator has to *run* on inputs, so every ingredient below is carried at
the `Primrec` level: the enumeration of bit strings, the stage class, the bounded-fuel
approximants, and the rational comparison against the threshold. -/

lemma allBitStrings_primrec : Primrec allBitStrings := by
  have hcons : Primrec fun y : (ℕ × (ℕ × List (List Bool))) × List Bool ↦
      [false :: y.2, true :: y.2] :=
    Primrec.list_cons.comp
      (Primrec.list_cons.comp (Primrec.const false) Primrec.snd)
      (Primrec.list_cons.comp
        (Primrec.list_cons.comp (Primrec.const true) Primrec.snd)
        (Primrec.const []))
  have hstep : Primrec₂ fun (_ : ℕ) (z : ℕ × List (List Bool)) ↦
      z.2.flatMap fun σ ↦ [false :: σ, true :: σ] :=
    Primrec.list_flatMap (Primrec.snd.comp Primrec.snd) hcons.to₂
  have h := Primrec.nat_rec' Primrec.id
    (Primrec.const ([[]] : List (List Bool))) hstep
  refine h.of_eq fun n ↦ ?_
  simp only [id_eq]
  induction n with
  | zero => simp [allBitStrings]
  | succ n ih => rw [allBitStrings_succ, ← ih]

/-- The stage decision in numeral form agreeing with a bit. -/
def decideAgrees (d : ℕ) (x : Bool) : Bool :=
  if d = 0 then true else cond x (decide (d = 2)) (decide (d = 1))

lemma decideAgrees_eq (n e : ℕ) (x : Bool) :
    decideAgrees (kleeneDecideNat n e) x =
      (match kleeneDecide n e with
        | none => true
        | some b => x == b) := by
  rw [kleeneDecideNat_eq]
  rcases kleeneDecide n e with _ | b
  · rfl
  · cases b <;> cases x <;> rfl

lemma separatorConsistentAt_eq (n : ℕ) :
    separatorConsistentAt n =
      (allBitStrings n).filter fun σ ↦
        decide (∀ e ∈ List.range n,
          decideAgrees (kleeneDecideNat n e) (σ.getD e false) = true) := by
  rw [separatorConsistentAt]
  congr 1
  funext σ
  rw [Bool.eq_iff_iff]
  simp only [List.all_eq_true, decide_eq_true_eq, List.mem_range]
  constructor
  · intro h e he
    rw [decideAgrees_eq]
    exact h e he
  · intro h e he
    rw [← decideAgrees_eq]
    exact h e he

lemma kleeneDecideNat_primrec : Primrec fun p : ℕ × ℕ ↦ kleeneDecideNat p.1 p.2 := by
  have hcode : Primrec fun p : ℕ × ℕ ↦ Denumerable.ofNat Nat.Partrec.Code p.2 :=
    (Primrec.ofNat Nat.Partrec.Code).comp Primrec.snd
  have hev : Primrec fun p : ℕ × ℕ ↦
      Nat.Partrec.Code.evaln p.1 (Denumerable.ofNat Nat.Partrec.Code p.2) p.2 :=
    Nat.Partrec.Code.primrec_evaln.comp ((Primrec.fst.pair hcode).pair Primrec.snd)
  have hbranch : Primrec fun w : ℕ ↦ if w = 0 then 1 else if w = 1 then 2 else 0 := by
    have h1 : PrimrecPred fun w : ℕ ↦ w = 0 :=
      Primrec.eq.comp Primrec.id (Primrec.const 0)
    have h2 : PrimrecPred fun w : ℕ ↦ w = 1 :=
      Primrec.eq.comp Primrec.id (Primrec.const 1)
    exact Primrec.ite h1 (Primrec.const 1) (Primrec.ite h2 (Primrec.const 2)
      (Primrec.const 0))
  refine (Primrec.option_getD.comp
    (Primrec.option_map hev (hbranch.comp Primrec.snd).to₂) (Primrec.const 0)).of_eq ?_
  rintro ⟨n, e⟩
  unfold kleeneDecideNat
  rcases Nat.Partrec.Code.evaln n (Denumerable.ofNat Nat.Partrec.Code e) e with _ | v
  · rfl
  · match v with
    | 0 => rfl
    | 1 => rfl
    | (v + 2) => simp

lemma separatorConsistentAt_primrec : Primrec separatorConsistentAt := by
  have hagree : Primrec fun z : (List Bool × ℕ) × ℕ ↦
      decideAgrees (kleeneDecideNat z.1.2 z.2) (z.1.1.getD z.2 false) := by
    have hd : Primrec fun z : (List Bool × ℕ) × ℕ ↦ kleeneDecideNat z.1.2 z.2 :=
      kleeneDecideNat_primrec.comp ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)
    have hx : Primrec fun z : (List Bool × ℕ) × ℕ ↦ z.1.1.getD z.2 false :=
      (Primrec.list_getD false).comp (Primrec.fst.comp Primrec.fst) Primrec.snd
    have h0 : PrimrecPred fun z : (List Bool × ℕ) × ℕ ↦ kleeneDecideNat z.1.2 z.2 = 0 :=
      Primrec.eq.comp hd (Primrec.const 0)
    have h1 : PrimrecPred fun z : (List Bool × ℕ) × ℕ ↦ kleeneDecideNat z.1.2 z.2 = 1 :=
      Primrec.eq.comp hd (Primrec.const 1)
    have h2 : PrimrecPred fun z : (List Bool × ℕ) × ℕ ↦ kleeneDecideNat z.1.2 z.2 = 2 :=
      Primrec.eq.comp hd (Primrec.const 2)
    have hb1 : Primrec fun z : (List Bool × ℕ) × ℕ ↦
        decide (kleeneDecideNat z.1.2 z.2 = 1) := h1.decide
    have hb2 : Primrec fun z : (List Bool × ℕ) × ℕ ↦
        decide (kleeneDecideNat z.1.2 z.2 = 2) := h2.decide
    exact (Primrec.ite h0 (Primrec.const true)
      (Primrec.cond hx hb2 hb1)).of_eq fun z ↦ rfl
  have hR : PrimrecRel fun (σ : List Bool) (n : ℕ) ↦
      ∀ e ∈ List.range n, decideAgrees (kleeneDecideNat n e) (σ.getD e false) = true := by
    have hbase : PrimrecRel fun (e : ℕ) (z : List Bool × ℕ) ↦
        decideAgrees (kleeneDecideNat z.2 e) (z.1.getD e false) = true := by
      have := hagree.comp (Primrec.snd.pair Primrec.fst)
      exact (Primrec.eq.comp this (Primrec.const true))
    have hforall := PrimrecRel.forall_mem_list hbase
    exact hforall.comp (Primrec.list_range.comp Primrec.snd) Primrec.id
  have hfilter := PrimrecRel.listFilter hR
  refine (hfilter.comp allBitStrings_primrec Primrec.id).of_eq fun n ↦ ?_
  simp only [id_eq]
  rw [separatorConsistentAt_eq]

private lemma list_sum_primrec : Primrec fun L : List ℚ ↦ L.sum := by
  have h := Primrec.list_foldr (α := List ℚ) Primrec.id (Primrec.const (0 : ℚ))
    (ratAdd_prim.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  refine h.of_eq fun L ↦ ?_
  simp only [id_eq]
  induction L with
  | nil => rfl
  | cons a L ih => simp only [List.foldr_cons, List.sum_cons, ih]

lemma boundedApprox_primrec (M : LowerSemicomputableContinuousSemimeasure) :
    Primrec fun z : (ℕ × ℕ) × List Bool ↦ boundedApprox M z.1.1 z.1.2 z.2 := by
  have harg : Primrec fun z : (ℕ × ℕ) × List Bool ↦
      Nat.pair z.1.2 (Encodable.encode z.2) :=
    Primrec₂.natPair.comp (Primrec.snd.comp Primrec.fst) (Primrec.encode.comp Primrec.snd)
  have hev : Primrec fun z : (ℕ × ℕ) × List Bool ↦
      M.approximation_code.evaln z.1.1 (Nat.pair z.1.2 (Encodable.encode z.2)) :=
    Nat.Partrec.Code.primrec_evaln.comp
      (((Primrec.fst.comp Primrec.fst).pair
        (Primrec.const M.approximation_code)).pair harg)
  have hdec : Primrec₂ fun (_ : (ℕ × ℕ) × List Bool) (w : ℕ) ↦
      Encodable.decode (α := ℚ) w := Primrec.decode.comp Primrec.snd
  exact Primrec.option_getD.comp (Primrec.option_bind hev hdec) (Primrec.const 0)

/-- The `(fuel, t)`-bounded approximation to the mass of the part of the stage-`s` class on
which bit `j` is `b`. -/
def sepApproxSum (M : LowerSemicomputableContinuousSemimeasure) (j : ℕ) (b : Bool)
    (s fuel t : ℕ) : ℚ :=
  (((separatorConsistentAt s).filter fun σ ↦ σ.getD j false == b).map
    (boundedApprox M fuel t)).sum

lemma sepApproxSum_primrec (M : LowerSemicomputableContinuousSemimeasure) (b : Bool) :
    Primrec fun z : (ℕ × ℕ) × ℕ × ℕ ↦ sepApproxSum M z.1.1 b z.1.2 z.2.1 z.2.2 := by
  have hbit : PrimrecRel fun (σ : List Bool) (j : ℕ) ↦ (σ.getD j false == b) = true := by
    have hx : Primrec fun z : List Bool × ℕ ↦ z.1.getD z.2 false :=
      (Primrec.list_getD false).comp Primrec.fst Primrec.snd
    exact Primrec.eq.comp (Primrec.beq.comp hx (Primrec.const b)) (Primrec.const true)
  have hclass : Primrec fun z : (ℕ × ℕ) × ℕ × ℕ ↦
      (separatorConsistentAt z.1.2).filter fun σ ↦ σ.getD z.1.1 false == b :=
    ((PrimrecRel.listFilter hbit).comp
      (separatorConsistentAt_primrec.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.fst.comp Primrec.fst)).of_eq fun z ↦ by
        refine congrArg (fun p ↦ List.filter p (separatorConsistentAt z.1.2)) ?_
        funext σ
        cases σ.getD z.1.1 false <;> cases b <;> rfl
  have happrox : Primrec₂ fun (z : (ℕ × ℕ) × ℕ × ℕ) (σ : List Bool) ↦
      boundedApprox M z.2.1 z.2.2 σ :=
    (boundedApprox_primrec M).comp
      (((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).pair Primrec.snd)
  exact list_sum_primrec.comp (Primrec.list_map hclass happrox)

/-- One dovetailed search step of the Kučera–Demuth separator: at search index `z` it looks
at stage `k + j + 1 + z.unpair.1` (above both the pivot `k` and the bit index `j`) with
fuel and approximation level read off `z.unpair.2`, and reports a bit whose part of the
class already approximates above the threshold `q`. -/
def sepGuard (M : LowerSemicomputableContinuousSemimeasure) (k : ℕ) (q : ℚ) (j z : ℕ) :
    Option ℕ :=
  if q < sepApproxSum M j true (k + j + 1 + z.unpair.1) z.unpair.2.unpair.1
      z.unpair.2.unpair.2 then some 1
  else if q < sepApproxSum M j false (k + j + 1 + z.unpair.1) z.unpair.2.unpair.1
      z.unpair.2.unpair.2 then some 0
  else none

lemma sepGuard_computable (M : LowerSemicomputableContinuousSemimeasure) (k : ℕ) (q : ℚ) :
    Computable₂ (sepGuard M k q) := by
  have hstage : Primrec fun p : ℕ × ℕ ↦ k + p.1 + 1 + p.2.unpair.1 :=
    Primrec.nat_add.comp
      (Primrec.nat_add.comp
        (Primrec.nat_add.comp (Primrec.const k) Primrec.fst) (Primrec.const 1))
      (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))
  have hfuel : Primrec fun p : ℕ × ℕ ↦ p.2.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp
      (Primrec.unpair.comp Primrec.snd)))
  have ht : Primrec fun p : ℕ × ℕ ↦ p.2.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp
      (Primrec.unpair.comp Primrec.snd)))
  have hsum : ∀ b : Bool, PrimrecPred fun p : ℕ × ℕ ↦
      q < sepApproxSum M p.1 b (k + p.1 + 1 + p.2.unpair.1) p.2.unpair.2.unpair.1
        p.2.unpair.2.unpair.2 := by
    intro b
    have happ : Primrec fun p : ℕ × ℕ ↦
        sepApproxSum M p.1 b (k + p.1 + 1 + p.2.unpair.1) p.2.unpair.2.unpair.1
          p.2.unpair.2.unpair.2 :=
      (sepApproxSum_primrec M b).comp ((Primrec.fst.pair hstage).pair (hfuel.pair ht))
    have hle : PrimrecPred fun p : ℕ × ℕ ↦
        sepApproxSum M p.1 b (k + p.1 + 1 + p.2.unpair.1) p.2.unpair.2.unpair.1
          p.2.unpair.2.unpair.2 ≤ q := ratLE_prim.comp happ (Primrec.const q)
    exact (PrimrecPred.of_eq hle.not fun p ↦ not_le)
  exact (Primrec.ite (hsum true) (Primrec.const (some 1))
    (Primrec.ite (hsum false) (Primrec.const (some 0)) (Primrec.const none))).to_comp.to₂

/-! ### Soundness and termination of the search -/

private lemma sum_boundedApprox_le (M : LowerSemicomputableContinuousSemimeasure)
    (fuel t : ℕ) : ∀ L : List (List Bool),
      (((L.map (boundedApprox M fuel t)).sum : ℚ) : ℝ) ≤ (L.map M.mass).sum
  | [] => by simp
  | σ :: L => by
      have ih := sum_boundedApprox_le M fuel t L
      have h := boundedApprox_le_mass M fuel t σ
      simp only [List.map_cons, List.sum_cons, Rat.cast_add]
      linarith

/-- The search never overstates: a fired guard really witnesses a heavy part of the
class. -/
lemma sepApproxSum_le (M : LowerSemicomputableContinuousSemimeasure) (j : ℕ) (b : Bool)
    (s fuel t : ℕ) :
    ((sepApproxSum M j b s fuel t : ℚ) : ℝ)
      ≤ classMass M.toContinuousSemimeasure (fun σ ↦ σ.getD j false == b) s :=
  sum_boundedApprox_le M fuel t _

private lemma tendsto_list_approx (M : LowerSemicomputableContinuousSemimeasure) :
    ∀ L : List (List Bool),
      Tendsto (fun t ↦ (((L.map (M.approximation t)).sum : ℚ) : ℝ)) atTop
        (𝓝 ((L.map M.mass).sum))
  | [] => by simp
  | σ :: L => by
      have ih := tendsto_list_approx M L
      have h := (M.approximation_tendsto σ).add ih
      simpa [List.map_cons, List.sum_cons] using h

/-- **Termination.**  Whatever `j` is, one of the two sides of the class carries more than
half of `r`, hence more than the threshold `q`, and the approximants eventually see it. -/
lemma exists_sepGuard (M : LowerSemicomputableContinuousSemimeasure) {r : ℝ} {q : ℚ}
    (k j : ℕ)
    (hle : ∀ n, r ≤ classMass M.toContinuousSemimeasure (fun _ ↦ true) n)
    (hq : 2 * (q : ℝ) < r) :
    ∃ z v, sepGuard M k q j z = some v := by
  set C := M.toContinuousSemimeasure with hC
  set s := k + j + 1 with hs
  have hsplit := classMass_bit_split C j true s
  have hside : ∃ b : Bool, (q : ℝ) < classMass C (fun σ ↦ σ.getD j false == b) s := by
    by_contra h
    push_neg at h
    have h1 := h true
    have h2 := h false
    have h3 := hle s
    simp only [Bool.not_true] at hsplit
    linarith
  obtain ⟨b, hb⟩ := hside
  have htend := tendsto_list_approx M
    ((separatorConsistentAt s).filter fun σ ↦ σ.getD j false == b)
  obtain ⟨t, ht⟩ := (htend.eventually_const_lt hb).exists
  obtain ⟨fuel, hfuel⟩ := exists_fuel_boundedApprox M t
    ((separatorConsistentAt s).filter fun σ ↦ σ.getD j false == b)
  have hval : sepApproxSum M j b s fuel t =
      (((separatorConsistentAt s).filter fun σ ↦ σ.getD j false == b).map
        (M.approximation t)).sum :=
    congrArg List.sum (List.map_congr_left hfuel)
  have hqlt : q < sepApproxSum M j b s fuel t := by
    rw [hval]; exact_mod_cast ht
  refine ⟨Nat.pair 0 (Nat.pair fuel t), ?_⟩
  unfold sepGuard
  simp only [Nat.unpair_pair, Nat.add_zero, ← hs]
  cases b
  · by_cases h1 : q < sepApproxSum M j true s fuel t
    · exact ⟨1, by simp [h1]⟩
    · exact ⟨0, by simp [h1, hqlt]⟩
  · exact ⟨1, by simp [hqlt]⟩

/-- **Soundness.**  A fired guard reports a bit whose part of the stage class really has
mass above the threshold. -/
lemma sepGuard_spec {M : LowerSemicomputableContinuousSemimeasure} {k : ℕ} {q : ℚ}
    {j z v : ℕ} (h : sepGuard M k q j z = some v) :
    ∃ b : Bool, v = (if b then 1 else 0) ∧
      (q : ℝ) < classMass M.toContinuousSemimeasure (fun σ ↦ σ.getD j false == b)
        (k + j + 1 + z.unpair.1) := by
  unfold sepGuard at h
  split_ifs at h with h1 h2
  · exact ⟨true, by simpa using (Option.some.inj h).symm,
      lt_of_lt_of_le (by exact_mod_cast h1) (sepApproxSum_le M j true _ _ _)⟩
  · exact ⟨false, by simpa using (Option.some.inj h).symm,
      lt_of_lt_of_le (by exact_mod_cast h2) (sepApproxSum_le M j false _ _ _)⟩

/-! ### The stage classes are null

If they were not, the search above would be a total computable separator for Kleene's
recursively inseparable pair. -/

/-- **The extraction.**  A positive floor `r` on the class masses, together with a pivot
stage `k` whose class mass is below `6r/5`, is contradictory: the dovetailed search
`sepGuard` then computes a total separator for Kleene's pair.

On input `j` the program searches over stages `s ≥ max k (j+1)`, approximation levels and
fuel, and reports the first bit `b` whose part of the stage class approximates above the
threshold `q` (`r/5 < q < r/2`).  It always halts, because the two parts sum to at least
`r > 2q`; and it is never wrong, because if `j` lies in the `b`-half of Kleene's pair then
the `b`-part keeps mass `≥ r` while the other part is below `6r/5 − r = r/5 < q`. -/
private lemma no_pos_class_floor (L : LowerSemicomputableContinuousSemimeasure) {r : ℝ}
    {k : ℕ} (hpos : 0 < r)
    (hle : ∀ n, r ≤ classMass L.toContinuousSemimeasure (fun _ ↦ true) n)
    (hk : classMass L.toContinuousSemimeasure (fun _ ↦ true) k < 6 * r / 5) : False := by
  obtain ⟨q, hq1, hq2⟩ : ∃ q : ℚ, r / 5 < (q : ℝ) ∧ (q : ℝ) < r / 2 :=
    exists_rat_btwn (by linarith)
  have hsearch : Partrec fun j ↦ Nat.rfindOpt (sepGuard L k q j) :=
    Partrec.rfindOpt (sepGuard_computable L k q)
  have hdom : ∀ j, (Nat.rfindOpt (sepGuard L k q j)).Dom := by
    intro j
    rw [Nat.rfindOpt_dom]
    obtain ⟨z, v, hzv⟩ := exists_sepGuard L k j hle (by linarith)
    exact ⟨z, v, hzv⟩
  have houtc : Computable fun j ↦ (Nat.rfindOpt (sepGuard L k q j)).get (hdom j) :=
    hsearch.of_eq_tot fun j ↦ Part.get_mem _
  have houtspec : ∀ j, ∃ z,
      sepGuard L k q j z = some ((Nat.rfindOpt (sepGuard L k q j)).get (hdom j)) :=
    fun j ↦ Nat.rfindOpt_spec (Part.get_mem (hdom j))
  have hone : Primrec fun x : ℕ ↦ decide (x = 1) :=
    (PrimrecPred.decide (p := fun x : ℕ ↦ x = 1)
      (Primrec.eq.comp Primrec.id (Primrec.const 1)))
  have hbit : ∀ (j : ℕ) (b : Bool), j ∈ kleeneSet b →
      (Nat.rfindOpt (sepGuard L k q j)).get (hdom j) = (if b then 1 else 0) := by
    intro j b hj
    obtain ⟨z, hz⟩ := houtspec j
    obtain ⟨b', hb', hmass⟩ := sepGuard_spec hz
    have hbb : b' = b := by
      by_contra hne
      have hnb : b' = !b := by
        cases b <;> cases b' <;>
          simp only [Bool.not_true, Bool.not_false] <;>
          first | rfl | exact absurd rfl hne
      subst hnb
      have hsmall := classMass_wrong_bit_lt L.toContinuousSemimeasure hle hk hj
        (s := k + j + 1 + z.unpair.1) (by omega) (by omega)
      linarith
    rw [hb', hbb]
  refine kleene_recursively_inseparable
    (fun j ↦ decide ((Nat.rfindOpt (sepGuard L k q j)).get (hdom j) = 1))
    (hone.to_comp.comp houtc) ?_ ?_
  · intro e he
    simp [hbit e true he]
  · intro e he
    simp [hbit e false he]

/-- **The separator classes are null (`thm:strict`, measure half).**  For a universal
continuous semimeasure the stage classes of the Kleene constraint theory carry vanishing
total mass: the class masses are antitone, so they converge to some `r ≥ 0`, and a positive
floor is refuted by `no_pos_class_floor` (Kučera–Demuth: the semimeasure's own
lower-semicomputable approximants would compute a separator by majority vote,
contradicting `kleene_recursively_inseparable`).
Paper node: `thm:strict` -/
theorem separatorClass_mass_tendsto_zero (M : UniversalContinuousSemimeasure) :
    Tendsto (fun n ↦ ((separatorConsistentAt n).map M.mass).sum) atTop (𝓝 0) := by
  have hrw : (fun n ↦ ((separatorConsistentAt n).map M.mass).sum)
      = classMass M.toLowerSemicomputableContinuousSemimeasure.toContinuousSemimeasure
        (fun _ ↦ true) :=
    funext fun n ↦ (classMass_true _ n).symm
  rw [hrw]
  set C := M.toLowerSemicomputableContinuousSemimeasure.toContinuousSemimeasure with hC
  have hnonneg : ∀ n, 0 ≤ classMass C (fun _ ↦ true) n := fun n ↦ classMass_nonneg C _ n
  have hbdd : BddBelow (Set.range (classMass C fun _ ↦ true)) := by
    refine ⟨0, ?_⟩
    rintro x ⟨n, rfl⟩
    exact hnonneg n
  have htend : Tendsto (classMass C fun _ ↦ true) atTop
      (𝓝 (⨅ n, classMass C (fun _ ↦ true) n)) :=
    tendsto_atTop_ciInf (classMass_antitone C) hbdd
  have hle : ∀ n, (⨅ n, classMass C (fun _ ↦ true) n) ≤ classMass C (fun _ ↦ true) n :=
    fun n ↦ ciInf_le hbdd n
  rcases eq_or_lt_of_le (le_ciInf hnonneg :
      (0 : ℝ) ≤ ⨅ n, classMass C (fun _ ↦ true) n) with hzero | hpos
  · rw [← hzero] at htend
    exact htend
  exfalso
  obtain ⟨k, hk⟩ : ∃ k, classMass C (fun _ ↦ true) k <
      6 * (⨅ n, classMass C (fun _ ↦ true) n) / 5 :=
    (htend.eventually_lt_const (by linarith)).exists
  exact no_pos_class_floor M.toLowerSemicomputableContinuousSemimeasure hpos hle hk

/-- The repo's concrete bit atoms have computable Gödel codes, so they meet the atom
hypothesis of the separator presentation.
Paper node: `thm:strict` -/
lemma ordinaryAtom_code_computable :
    Computable fun k ↦ Encodable.encode (ordinaryIndependentBitAtoms.atom k) := by
  have hpair : Computable fun k : ℕ ↦ Nat.pair 1 k + 1 :=
    Computable.succ.comp
      (Computable₂.comp Primrec₂.natPair.to_comp (Computable.const 1) Computable.id)
  exact hpair.of_eq (fun _ ↦ rfl)

/-! ### The separator presentation

Every field is discharged here.  Realizability of the non-computable target assignment
comes from `BitPrefixSentences.realizable` — the total form, which is exactly why that
field is total rather than finite-prefix (the constraint theory pins infinitely many bits);
the vanishing class mass is `separatorClass_mass_tendsto_zero` (Kučera–Demuth).  One input
is supplied by the caller:

* `hatom` — computability of the atom family's Gödel codes.  This is discharged for the
  repo's concrete atoms by `ordinaryAtom_code_computable`; from it the whole constraint
  theory's enumerator is *built* (`separatorConstraintCE`), so no formula-emission input is
  assumed here. -/

/-- The separator presentation of `thm:strict`, built from Kleene's recursively inseparable
pair: the constraint theory, its c.e. enumerator, the stagewise consistent classes, and
their vanishing mass are all constructed.
Paper node: `thm:strict` -/
noncomputable def strictSeparatorPresentationOfKleene
    {DP : DeductiveProcess} (M : UniversalContinuousSemimeasure)
    (B : BitPrefixSentences DP)
    (hatom : Computable fun k ↦ Encodable.encode (B.atom k)) :
    StrictSeparatorPresentation M B where
  constraint := separatorConstraint B.atom
  repetition := EfficientRepeatedEnumeration.ofCE (separatorConstraintCE hatom)
  jointly_possible n := by
    obtain ⟨v, hv, hbits⟩ := B.realizable n kleeneAssignment
    refine ⟨v, hv, fun i ↦ ?_⟩
    refine (holds_separatorConstraint v B.atom i).2 (fun e _ b hb ↦ ?_)
    rw [hbits e, kleeneAssignment_of_decide hb]
  consistentAt := separatorConsistentAt
  class_covers n v hv := by
    classical
    refine ⟨(List.range n).map fun k ↦ decide (v.Holds (B.atom k)), ?_, ?_⟩
    · refine mem_separatorConsistentAt.2 ⟨by simp, fun e he b hb ↦ ?_⟩
      have hlt : e < ((List.range n).map fun k ↦ decide (v.Holds (B.atom k))).length := by
        simpa using he
      rw [List.getD_eq_getElem _ _ hlt]
      simp only [List.getElem_map, List.getElem_range]
      have hiff := (holds_separatorConstraint v B.atom n).1 hv e he b hb
      cases b with
      | false =>
          simp only [decide_eq_false_iff_not]
          exact fun hh ↦ by simpa using hiff.mp hh
      | true => simpa using hiff.mpr rfl
    · refine (B.holds_prefix v _).2 (fun k ↦ ?_)
      have hk : (k : ℕ) < n := by simpa using k.isLt
      simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range,
        decide_eq_true_eq]
  mass_class_tendsto_zero := separatorClass_mass_tendsto_zero M

/-- **Strict domination with the separator argument discharged** (`thm:strict`).  The only
remaining input is computability of the atom family's Gödel codes, which
`ordinaryAtom_code_computable` proves for the repo's concrete atoms; the constraint theory,
its enumerator, the stage classes and their vanishing mass are all constructed here.

The `B : BitPrefixSentences DP` argument is inhabited over the repo's own atoms by
`ordinaryBitPrefixSentences` (`Construction/Witnesses/BitPrefixSyntax.lean`), and
`lic_strict_domination_universalSemimeasure_unconditional` closes this endpoint over the
constructed `LIA` and the constructed dovetail with no caller input.
Paper node: `thm:strict` -/
theorem lic_strict_domination_universalSemimeasure_ofAtomCodes
    {DP : DeductiveProcess} {M : UniversalContinuousSemimeasure}
    {B : BitPrefixSentences DP}
    (hatom : Computable fun k ↦ Encodable.encode (B.atom k))
    (P : History) [IsLogicalInductor P DP] :
    ∀ C : ℝ, 0 < C → ∃ σ : List Bool,
      limitingBelief P (B.prefixSentence σ) > C * M.mass σ :=
  lic_strict_domination_universalSemimeasure P (strictSeparatorPresentationOfKleene M B hatom)

#print axioms ceNestedSemimeasure
#print axioms exists_pos_mass_of_ce_nested
#print axioms no_ce_null_prefix_family
#print axioms kleene_recursively_inseparable
#print axioms separatorClass_mass_tendsto_zero
#print axioms strictSeparatorPresentationOfKleene
#print axioms lic_strict_domination_universalSemimeasure_ofAtomCodes

end LogicalInduction
