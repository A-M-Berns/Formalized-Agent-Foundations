import LogicalInduction.Construction.Witnesses.PrefixMachine
import LogicalInduction.Construction.Witnesses.QuoteCodeOfMarket

/-!
# Exact quoted products by definitional extension of the deductive process (`thm:ccee`)

`QuoteCodeOfMarket.lean`'s Part F builds the `thm:ccee` left product as a width-`n+1` mesh,
which reflects `x · w (f n)` only to within `1/(n+1)` — the one disclosed type-`(c)`
substitution of that endpoint.  The obstruction there is the *emitter*: a strategy block has
to be produced with polynomial fuel, and the exact threshold `⌜X > r / w (f n)⌝` names a
value the emitter cannot have.

A **deductive process** carries no such clock: it is only required computable.  So the exact
product is available as a *definitional extension of the process*, not of the theory: fresh
atoms `productAtom n r` standing for `⌜Xₙ · Wₙ > r⌝`, together with the defining schema
entered stagewise by an extra process.  Nothing in the first-order theory changes; the paper's
`Θ` contains the product term natively, and a fresh-atom definitional extension is the
propositional counterpart.

## The schema

Naming the *value* of the weight is what the emitter cannot do — but the schema never needs
it.  For rationals `s, t ≥ 0` the process enters

* `(⌜Xₙ > s⌝ ⋏ ⌜Wₙ > t⌝) 🡒 productAtom n r`   whenever `r ≤ s·t`,
* `productAtom n r 🡒 (⌜Xₙ > s⌝ ⋎ ⌜Wₙ > t⌝)`   whenever `s·t ≤ r`,
* `productAtom n r`                             whenever `r < 0`,

which mentions only the two source families' own threshold sentences and is decidable in
`(n, r, s, t)`.  In a world valuing `Xₙ` at `x` and `Wₙ` at `c`, density of ℚ in the two
factors pins `productAtom n r` to exactly `x·c > r`, in both directions — i.e.
`ValuesAt (productLUV n) (x·c)`, with **no slack** and with no positivity hypothesis on `c`
(the `c = 0` case is the `r < 0` axiom plus the negative schema, not a case split).

This is a strict improvement on the route scoped in `notes/ccee-exact-valuation-plan.md`,
which had the process compute `w (f n)` through `PGenerableRat.computable` and enter
`productAtom (n,r) ↔ (X n).gt (r / w (f n))`.  That is circular for a *closed* endpoint: the
process must be fixed before the market it induces exists, so a process that consults its own
market cannot be defined, and the weight would have to be narrowed from `def:pgen` to a
market-independent e.c. sequence.  The pair schema needs no weight value at all and so keeps
the paper's `w`.

## Freshness

The schema is jointly satisfiable only if the product atoms do not already occur inside the
source's own threshold sentences — an adversarial `X` with `(X n).gt s = ∼productAtom n r`
would make a stage unsatisfiable.  `ProductAtomFresh` is that side condition, stated
syntactically through `sentenceAtomCodes`.  Tag `productTag` is unused by every atom this
repo's processes emit (computation claims carry tags `0`–`3`, quotation claims tag `4`), so
the condition holds for every repo-constructed family; it is the propositional rendering's
residue, replacing the mesh route's slack disclosure with a strictly milder one.
-/

namespace LogicalInduction

open LO LO.Propositional

/-! ## Atom occurrences

Foundation's `Formula` carries no occurrence function, so the two facts the freshness
condition needs are proved here: the finite set of atoms of a sentence, and the substitution
lemma saying a world's verdict depends only on those. -/

/-- The atom indices occurring in a propositional sentence. -/
def sentenceAtomCodes : Sentence → Finset ℕ :=
  Formula.rec' ∅ (fun a => {a})
    (fun _ _ s t => s ∪ t) (fun _ _ s t => s ∪ t) (fun _ _ s t => s ∪ t)

@[simp] lemma sentenceAtomCodes_atom (a : ℕ) :
    sentenceAtomCodes (Formula.atom a) = {a} := rfl

@[simp] lemma sentenceAtomCodes_falsum :
    sentenceAtomCodes (⊥ : Sentence) = ∅ := rfl

@[simp] lemma sentenceAtomCodes_imp (φ ψ : Sentence) :
    sentenceAtomCodes (φ 🡒 ψ) = sentenceAtomCodes φ ∪ sentenceAtomCodes ψ := rfl

@[simp] lemma sentenceAtomCodes_and (φ ψ : Sentence) :
    sentenceAtomCodes (φ ⋏ ψ) = sentenceAtomCodes φ ∪ sentenceAtomCodes ψ := rfl

@[simp] lemma sentenceAtomCodes_or (φ ψ : Sentence) :
    sentenceAtomCodes (φ ⋎ ψ) = sentenceAtomCodes φ ∪ sentenceAtomCodes ψ := rfl

/-- **Substitution.** A p.c. world's verdict on `φ` depends only on the atoms occurring in
`φ`: two valuations agreeing there agree on `φ`. -/
lemma PCWorld.holds_congr_atomCodes {v v' : PCWorld} :
    ∀ φ : Sentence, (∀ a ∈ sentenceAtomCodes φ, (v a ↔ v' a)) →
      (v.Holds φ ↔ v'.Holds φ) := by
  intro φ
  induction φ using Formula.rec' with
  | hfalsum => intro _; exact Iff.rfl
  | hatom a => intro h; exact h a (by simp)
  | himp φ ψ ihφ ihψ =>
      intro h
      have hφ := ihφ (fun a ha => h a (by simp [ha]))
      have hψ := ihψ (fun a ha => h a (by simp [ha]))
      show (v.Holds φ → v.Holds ψ) ↔ (v'.Holds φ → v'.Holds ψ)
      rw [hφ, hψ]
  | hand φ ψ ihφ ihψ =>
      intro h
      have hφ := ihφ (fun a ha => h a (by simp [ha]))
      have hψ := ihψ (fun a ha => h a (by simp [ha]))
      show (v.Holds φ ∧ v.Holds ψ) ↔ (v'.Holds φ ∧ v'.Holds ψ)
      rw [hφ, hψ]
  | hor φ ψ ihφ ihψ =>
      intro h
      have hφ := ihφ (fun a ha => h a (by simp [ha]))
      have hψ := ihψ (fun a ha => h a (by simp [ha]))
      show (v.Holds φ ∨ v.Holds ψ) ↔ (v'.Holds φ ∨ v'.Holds ψ)
      rw [hφ, hψ]

/-! ## The fresh product atoms -/

/-- The atom tag reserved for quoted-product definitions.  Computation claims carry tags
`0`–`3` (`ComputationClaimKind.godelCode`) and quotation claims tag `4`
(`quotationClaimCode`), so `5` names no atom any process in this repo emits. -/
def productTag : ℕ := 5

/-- The fresh atom standing for `⌜Xₙ · Wₙ > r⌝`. -/
def productAtom (n : ℕ) (r : ℚ) : Sentence :=
  Formula.atom (Nat.pair productTag (Nat.pair n (Encodable.encode r)))

@[simp] lemma sentenceAtomCodes_productAtom (n : ℕ) (r : ℚ) :
    sentenceAtomCodes (productAtom n r) =
      {Nat.pair productTag (Nat.pair n (Encodable.encode r))} := rfl

/-- The quoted product LUV: its threshold family *is* the fresh atom family. -/
def productLUV (n : ℕ) : LUV := ⟨productAtom n⟩

@[simp] lemma productLUV_gt (n : ℕ) (r : ℚ) : (productLUV n).gt r = productAtom n r := rfl

/-- **The freshness side condition.**  No product atom occurs inside a source threshold
sentence.  Stated on the atom tag rather than on the exact index, so it is stable under the
choice of `n` and `r` and is discharged by inspection for every family this repo builds. -/
def ProductAtomFresh (X : ℕ → LUV) : Prop :=
  ∀ (n : ℕ) (r : ℚ), ∀ a ∈ sentenceAtomCodes ((X n).gt r), a.unpair.1 ≠ productTag

/-! ## The defining process -/

/-- One instance of the defining schema, in decoded form.  Guards that fail emit `⊤`, which
every world holds and no world is constrained by. -/
def productSchemaInstance (X W : ℕ → LUV) (n kind : ℕ) (r s t : ℚ) : Sentence :=
  if kind = 0 then
    (if 0 ≤ s ∧ 0 ≤ t ∧ r ≤ s * t then
      ((X n).gt s ⋏ (W n).gt t) 🡒 productAtom n r else ⊤)
  else if kind = 1 then
    (if 0 ≤ s ∧ 0 ≤ t ∧ s * t ≤ r then
      productAtom n r 🡒 ((X n).gt s ⋎ (W n).gt t) else ⊤)
  else
    (if r < 0 then productAtom n r else ⊤)

/-- The schema instance at the job code `e = ⟨n, ⟨kind, ⟨⌜r⌝, ⟨⌜s⌝, ⌜t⌝⟩⟩⟩⟩`. -/
def productDefSentence (X W : ℕ → LUV) (e : ℕ) : Sentence :=
  productSchemaInstance X W e.unpair.1 e.unpair.2.unpair.1
    (decodedQuotationRat e.unpair.2.unpair.2.unpair.1)
    (decodedQuotationRat e.unpair.2.unpair.2.unpair.2.unpair.1)
    (decodedQuotationRat e.unpair.2.unpair.2.unpair.2.unpair.2)

/-- Job codes revealed by day `k`: all of them up to `k`.  The schema is decidable, so no
dovetailing clock is needed — the process is a plain enumeration. -/
def productStageList (X W : ℕ → LUV) : ℕ → List Sentence
  | 0 => [productDefSentence X W 0]
  | k + 1 => productDefSentence X W (k + 1) :: productStageList X W k

lemma mem_productStageList {X W : ℕ → LUV} {e k : ℕ} (h : e ≤ k) :
    productDefSentence X W e ∈ productStageList X W k := by
  induction k with
  | zero => simp [productStageList, Nat.le_zero.mp h]
  | succ k ih =>
      rcases Nat.lt_or_ge e (k + 1) with hlt | hge
      · exact List.mem_cons_of_mem _ (ih (Nat.lt_succ_iff.mp hlt))
      · have : e = k + 1 := le_antisymm h hge
        simp [productStageList, this]

/-- The product-definition deductive process.
Paper node: `thm:ccee` -/
def productDefDP (X W : ℕ → LUV) : DeductiveProcess where
  D k := (productStageList X W k).toFinset
  mono k := by
    intro φ hφ
    simp only [List.mem_toFinset] at hφ ⊢
    exact List.mem_cons_of_mem _ hφ

lemma productDefSentence_mem_stage (X W : ℕ → LUV) (e : ℕ) :
    productDefSentence X W e ∈ (productDefDP X W).D e :=
  List.mem_toFinset.mpr (mem_productStageList (le_refl e))

/-- Every world consistent with the whole product-definition process holds every schema
instance. -/
lemma holds_productDefSentence {X W : ℕ → LUV} {v : PCWorld}
    (hv : v.ConsistentWithTheory (productDefDP X W)) (e : ℕ) :
    v.Holds (productDefSentence X W e) :=
  hv e _ (productDefSentence_mem_stage X W e)

/-! ### The three schema instances, read off at their job codes -/

section
-- `Nat.unpair` unfolds `Nat.sqrt`, which loops `whnf` under the schema's decidable guards.
attribute [local irreducible] Nat.sqrt

lemma productDefSentence_pair (X W : ℕ → LUV) (n kind : ℕ) (r s t : ℚ) :
    productDefSentence X W
        (Nat.pair n (Nat.pair kind (Nat.pair (Encodable.encode r)
          (Nat.pair (Encodable.encode s) (Encodable.encode t))))) =
      productSchemaInstance X W n kind r s t := by
  rw [productDefSentence]
  simp only [Nat.unpair_pair, decodedQuotationRat_encode]

lemma holds_productDef_pos {X W : ℕ → LUV} {v : PCWorld}
    (hv : v.ConsistentWithTheory (productDefDP X W)) (n : ℕ) {r s t : ℚ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : r ≤ s * t)
    (hX : v.Holds ((X n).gt s)) (hW : v.Holds ((W n).gt t)) :
    v.Holds (productAtom n r) := by
  have h := holds_productDefSentence hv
    (Nat.pair n (Nat.pair 0 (Nat.pair (Encodable.encode r)
      (Nat.pair (Encodable.encode s) (Encodable.encode t)))))
  rw [productDefSentence_pair, productSchemaInstance, if_pos rfl,
    if_pos (⟨hs, ht, hst⟩ : 0 ≤ s ∧ 0 ≤ t ∧ r ≤ s * t)] at h
  exact h ⟨hX, hW⟩

lemma not_holds_productDef_neg {X W : ℕ → LUV} {v : PCWorld}
    (hv : v.ConsistentWithTheory (productDefDP X W)) (n : ℕ) {r s t : ℚ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s * t ≤ r)
    (hX : ¬ v.Holds ((X n).gt s)) (hW : ¬ v.Holds ((W n).gt t)) :
    ¬ v.Holds (productAtom n r) := by
  have h := holds_productDefSentence hv
    (Nat.pair n (Nat.pair 1 (Nat.pair (Encodable.encode r)
      (Nat.pair (Encodable.encode s) (Encodable.encode t)))))
  rw [productDefSentence_pair, productSchemaInstance,
    if_neg (by decide : ¬ (1 : ℕ) = 0), if_pos rfl,
    if_pos (⟨hs, ht, hst⟩ : 0 ≤ s ∧ 0 ≤ t ∧ s * t ≤ r)] at h
  intro hcon
  rcases h hcon with hl | hr
  · exact hX hl
  · exact hW hr

lemma holds_productDef_below {X W : ℕ → LUV} {v : PCWorld}
    (hv : v.ConsistentWithTheory (productDefDP X W)) (n : ℕ) {r : ℚ} (hr : r < 0) :
    v.Holds (productAtom n r) := by
  have h := holds_productDefSentence hv
    (Nat.pair n (Nat.pair 2 (Nat.pair (Encodable.encode r)
      (Nat.pair (Encodable.encode (0 : ℚ)) (Encodable.encode (0 : ℚ))))))
  rw [productDefSentence_pair, productSchemaInstance,
    if_neg (by decide : ¬ (2 : ℕ) = 0), if_neg (by decide : ¬ (2 : ℕ) = 1),
    if_pos hr] at h
  exact h

end

/-! ### Rational brackets for a product of two reals -/

/-- Below a product: rationals `s < x`, `t < c` with `r ≤ s·t`, for `0 ≤ r < x·c`. -/
lemma exists_rat_pair_lt_mul {x c : ℝ} (hx0 : 0 ≤ x) (hc0 : 0 ≤ c) {r : ℚ}
    (hr0 : 0 ≤ r) (hr : (r : ℝ) < x * c) :
    ∃ s t : ℚ, 0 ≤ s ∧ 0 ≤ t ∧ r ≤ s * t ∧ (s : ℝ) < x ∧ (t : ℝ) < c := by
  have hr0R : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr0
  have hxc : 0 < x * c := lt_of_le_of_lt hr0R hr
  have hx : 0 < x := lt_of_le_of_ne hx0 (fun h => by simp [← h] at hxc)
  have hc : 0 < c := lt_of_le_of_ne hc0 (fun h => by simp [← h] at hxc)
  set ε : ℝ := min (min x c) ((x * c - (r : ℝ)) / (x + c + 1)) with hε
  have hsum : 0 < x + c + 1 := by linarith
  have hεpos : 0 < ε := lt_min (lt_min hx hc) (div_pos (by linarith) hsum)
  have hεx : ε ≤ x := le_trans (min_le_left _ _) (min_le_left _ _)
  have hεc : ε ≤ c := le_trans (min_le_left _ _) (min_le_right _ _)
  have hεr : ε * (x + c + 1) ≤ x * c - (r : ℝ) := by
    have := min_le_right (min x c) ((x * c - (r : ℝ)) / (x + c + 1))
    calc ε * (x + c + 1) ≤ ((x * c - (r : ℝ)) / (x + c + 1)) * (x + c + 1) := by
          exact mul_le_mul_of_nonneg_right this (le_of_lt hsum)
      _ = x * c - (r : ℝ) := by field_simp
  obtain ⟨s, hs1, hs2⟩ := exists_rat_btwn (show x - ε < x by linarith)
  obtain ⟨t, ht1, ht2⟩ := exists_rat_btwn (show c - ε < c by linarith)
  have hs0 : (0 : ℝ) ≤ (s : ℝ) := by linarith
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := by linarith
  have hprod : (r : ℝ) < (s : ℝ) * (t : ℝ) := by
    have h1 : (x - ε) * (c - ε) ≤ (s : ℝ) * (t : ℝ) :=
      mul_le_mul hs1.le ht1.le (by linarith) hs0
    nlinarith
  refine ⟨s, t, by exact_mod_cast hs0, by exact_mod_cast ht0, ?_, hs2, ht2⟩
  have : (r : ℝ) < ((s * t : ℚ) : ℝ) := by push_cast; exact hprod
  exact_mod_cast this.le

/-- Above a product: rationals `s > x`, `t > c` with `s·t ≤ r`, for `x·c < r`. -/
lemma exists_rat_pair_mul_lt {x c : ℝ} (hx0 : 0 ≤ x) (hc0 : 0 ≤ c) {r : ℚ}
    (hr : x * c < (r : ℝ)) :
    ∃ s t : ℚ, 0 ≤ s ∧ 0 ≤ t ∧ s * t ≤ r ∧ x < (s : ℝ) ∧ c < (t : ℝ) := by
  have hsum : 0 < x + c + 1 := by linarith
  set ε : ℝ := min 1 (((r : ℝ) - x * c) / (x + c + 1)) with hε
  have hεpos : 0 < ε := lt_min one_pos (div_pos (by linarith) hsum)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεr : ε * (x + c + 1) ≤ (r : ℝ) - x * c := by
    have := min_le_right (1 : ℝ) (((r : ℝ) - x * c) / (x + c + 1))
    calc ε * (x + c + 1) ≤ (((r : ℝ) - x * c) / (x + c + 1)) * (x + c + 1) :=
          mul_le_mul_of_nonneg_right this (le_of_lt hsum)
      _ = (r : ℝ) - x * c := by field_simp
  obtain ⟨s, hs1, hs2⟩ := exists_rat_btwn (show x < x + ε by linarith)
  obtain ⟨t, ht1, ht2⟩ := exists_rat_btwn (show c < c + ε by linarith)
  have hs0 : (0 : ℝ) ≤ (s : ℝ) := le_trans hx0 hs1.le
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := le_trans hc0 ht1.le
  have hprod : (s : ℝ) * (t : ℝ) ≤ (r : ℝ) := by
    have h1 : (s : ℝ) * (t : ℝ) ≤ (x + ε) * (c + ε) :=
      mul_le_mul hs2.le ht2.le ht0 (by linarith)
    nlinarith
  refine ⟨s, t, by exact_mod_cast hs0, by exact_mod_cast ht0, ?_, hs1, ht1⟩
  have : ((s * t : ℚ) : ℝ) ≤ (r : ℝ) := by push_cast; exact hprod
  exact_mod_cast this

/-! ## Exact reflection -/

/-- **The exact product law** (`thm:ccee`, `slack = 0`).  A world consistent with the
definitional-extension process that values the source at `x` and the weight family at `c`
values the quoted product at exactly `x · c`.

No positivity hypothesis on `c`: the `c = 0` case is covered by the same two schema
directions (with the `r < 0` axiom on the left), not by a case split.
Paper node: `thm:ccee` -/
theorem productLUV_valuesAt {X W : ℕ → LUV} {v : PCWorld}
    (hv : v.ConsistentWithTheory (productDefDP X W)) (n : ℕ) {x c : ℝ}
    (hx : v.ValuesAt (X n) x) (hc : v.ValuesAt (W n) c) :
    v.ValuesAt (productLUV n) (x * c) := by
  obtain ⟨hx0, hx1, hxthr⟩ := hx
  obtain ⟨hc0, hc1, hcthr⟩ := hc
  refine ⟨mul_nonneg hx0 hc0, by nlinarith, fun r => ⟨?_, ?_⟩⟩
  · intro hr
    rw [productLUV_gt]
    rcases lt_or_ge r 0 with hneg | hpos
    · exact holds_productDef_below hv n hneg
    · obtain ⟨s, t, hs0, ht0, hst, hsx, htc⟩ := exists_rat_pair_lt_mul hx0 hc0 hpos hr
      exact holds_productDef_pos hv n hs0 ht0 hst ((hxthr s).1 hsx) ((hcthr t).1 htc)
  · intro hr
    rw [productLUV_gt]
    obtain ⟨s, t, hs0, ht0, hst, hxs, hct⟩ := exists_rat_pair_mul_lt hx0 hc0 hr
    exact not_holds_productDef_neg hv n hs0 ht0 hst ((hxthr s).2 hxs) ((hcthr t).2 hct)

/-! ## Non-vacuity: every base world extends through the definitions

`productLUV_valuesAt` is worth nothing if no world is consistent with the extended process.
It is, and by construction rather than by a stand-in witness: a base world that already
values the two source families extends *uniquely on the product atoms* to a world consistent
with the union, provided the product tag occurs neither in the base stages nor in the two
families' threshold sentences.

The extension is the **least** assignment closed under the positive clauses.  That choice is
forced: `ValuesAt` deliberately leaves the threshold *at* the value undetermined, so a world
may affirm `⌜Xₙ > x⌝`; both a strict (`r < x·c`) and a lax (`r ≤ x·c`) product reading then
break one of the two schema directions at `r = x·c`, while the closure reading satisfies
both. -/

/-- The product-atom truth a base world already forces: the least assignment closed under the
positive schema clauses. -/
def ProductAtomTruth (X W : ℕ → LUV) (v₀ : PCWorld) (n : ℕ) (r : ℚ) : Prop :=
  r < 0 ∨ ∃ s t : ℚ, 0 ≤ s ∧ 0 ≤ t ∧ r ≤ s * t ∧
    v₀.Holds ((X n).gt s) ∧ v₀.Holds ((W n).gt t)

open Classical in
/-- `v₀` extended to the fresh product atoms by their definitions; unchanged elsewhere. -/
noncomputable def productExtensionWorld (X W : ℕ → LUV) (v₀ : PCWorld) : PCWorld := fun m =>
  if m.unpair.1 = productTag then
    ProductAtomTruth X W v₀ m.unpair.2.unpair.1 (decodedQuotationRat m.unpair.2.unpair.2)
  else v₀ m

section
attribute [local irreducible] Nat.sqrt

lemma productExtensionWorld_agree (X W : ℕ → LUV) (v₀ : PCWorld) {a : ℕ}
    (ha : a.unpair.1 ≠ productTag) :
    (productExtensionWorld X W v₀) a ↔ v₀ a := by
  simp only [productExtensionWorld, if_neg ha]

lemma productExtensionWorld_productAtom (X W : ℕ → LUV) (v₀ : PCWorld) (n : ℕ) (r : ℚ) :
    (productExtensionWorld X W v₀).Holds (productAtom n r) ↔
      ProductAtomTruth X W v₀ n r := by
  show (productExtensionWorld X W v₀)
    (Nat.pair productTag (Nat.pair n (Encodable.encode r))) ↔ _
  simp only [productExtensionWorld, Nat.unpair_pair, decodedQuotationRat_encode, if_true]

end

/-- Sentences free of the product tag are read the same way by the extension. -/
lemma productExtensionWorld_holds_iff (X W : ℕ → LUV) (v₀ : PCWorld) {φ : Sentence}
    (hφ : ∀ a ∈ sentenceAtomCodes φ, a.unpair.1 ≠ productTag) :
    (productExtensionWorld X W v₀).Holds φ ↔ v₀.Holds φ :=
  PCWorld.holds_congr_atomCodes φ (fun a ha => productExtensionWorld_agree X W v₀ (hφ a ha))

/-- A LUV whose thresholds avoid the product tag is valued the same by the extension. -/
lemma productExtensionWorld_valuesAt {X W : ℕ → LUV} {v₀ : PCWorld} {Y : ℕ → LUV}
    (hY : ProductAtomFresh Y) {n : ℕ} {y : ℝ} (hy : v₀.ValuesAt (Y n) y) :
    (productExtensionWorld X W v₀).ValuesAt (Y n) y := by
  obtain ⟨hy0, hy1, hythr⟩ := hy
  refine ⟨hy0, hy1, fun r => ⟨fun h => ?_, fun h => ?_⟩⟩
  · exact (productExtensionWorld_holds_iff X W v₀ (hY n r)).mpr ((hythr r).1 h)
  · exact fun hcon =>
      (hythr r).2 h ((productExtensionWorld_holds_iff X W v₀ (hY n r)).mp hcon)

/-- **The extension satisfies the whole defining schema.**  This is the load-bearing half of
non-vacuity: the fresh atoms can be assigned consistently with every clause at once.
Paper node: `thm:ccee` -/
lemma productExtensionWorld_holds_schema {X W : ℕ → LUV} {v₀ : PCWorld}
    (hX : ProductAtomFresh X) (hW : ProductAtomFresh W)
    (hXval : ∀ n, ∃ x, v₀.ValuesAt (X n) x) (hWval : ∀ n, ∃ c, v₀.ValuesAt (W n) c)
    (n kind : ℕ) (r s t : ℚ) :
    (productExtensionWorld X W v₀).Holds (productSchemaInstance X W n kind r s t) := by
  have hXtr : ∀ (m : ℕ) (q : ℚ),
      (productExtensionWorld X W v₀).Holds ((X m).gt q) ↔ v₀.Holds ((X m).gt q) :=
    fun m q => productExtensionWorld_holds_iff X W v₀ (hX m q)
  have hWtr : ∀ (m : ℕ) (q : ℚ),
      (productExtensionWorld X W v₀).Holds ((W m).gt q) ↔ v₀.Holds ((W m).gt q) :=
    fun m q => productExtensionWorld_holds_iff X W v₀ (hW m q)
  rw [productSchemaInstance]
  split_ifs with _ hg0 _ hg1 hneg
  · intro hc
    exact (productExtensionWorld_productAtom X W v₀ n r).mpr
      (Or.inr ⟨s, t, hg0.1, hg0.2.1, hg0.2.2, (hXtr n s).1 hc.1, (hWtr n t).1 hc.2⟩)
  · exact PCWorld.holds_top _
  · intro hp
    have hp' := (productExtensionWorld_productAtom X W v₀ n r).mp hp
    show (productExtensionWorld X W v₀).Holds ((X n).gt s) ∨
      (productExtensionWorld X W v₀).Holds ((W n).gt t)
    by_contra hcon
    push_neg at hcon
    obtain ⟨hnX, hnW⟩ := hcon
    obtain ⟨hs0, ht0, hst⟩ := hg1
    obtain ⟨x, hx0, _, hxthr⟩ := hXval n
    obtain ⟨c, hc0, _, hcthr⟩ := hWval n
    have hxs : x ≤ (s : ℝ) := by
      by_contra hcc
      push_neg at hcc
      exact hnX ((hXtr n s).2 ((hxthr s).1 hcc))
    have hct : c ≤ (t : ℝ) := by
      by_contra hcc
      push_neg at hcc
      exact hnW ((hWtr n t).2 ((hcthr t).1 hcc))
    rcases hp' with hrneg | ⟨s₁, t₁, hs₁, ht₁, hr₁, hXs₁, hWt₁⟩
    · nlinarith
    · have hs₁x : (s₁ : ℝ) ≤ x := by
        by_contra hcc
        push_neg at hcc
        exact (hxthr s₁).2 hcc hXs₁
      have ht₁c : (t₁ : ℝ) ≤ c := by
        by_contra hcc
        push_neg at hcc
        exact (hcthr t₁).2 hcc hWt₁
      have hs₁s : s₁ ≤ s := by exact_mod_cast le_trans hs₁x hxs
      have ht₁t : t₁ ≤ t := by exact_mod_cast le_trans ht₁c hct
      rcases eq_or_lt_of_le hs₁s with heq | hlt
      · exact hnX ((hXtr n s).2 (heq ▸ hXs₁))
      rcases eq_or_lt_of_le ht₁t with heq | hlt'
      · exact hnW ((hWtr n t).2 (heq ▸ hWt₁))
      nlinarith
  · exact PCWorld.holds_top _
  · exact (productExtensionWorld_productAtom X W v₀ n r).mpr (Or.inl hneg)
  · exact PCWorld.holds_top _

lemma exists_of_mem_productStageList {X W : ℕ → LUV} {φ : Sentence} {k : ℕ}
    (h : φ ∈ productStageList X W k) : ∃ e, φ = productDefSentence X W e := by
  induction k with
  | zero => exact ⟨0, by simpa [productStageList] using h⟩
  | succ k ih =>
      rcases List.mem_cons.mp h with h1 | h2
      · exact ⟨k + 1, h1⟩
      · exact ih h2

/-- **`hworld` for the definitional extension.**  The extension of a base world that values
both source families is consistent with every stage of the product-definition process.
Paper node: `thm:ccee` -/
theorem productExtensionWorld_consistentWithTheory {X W : ℕ → LUV} {v₀ : PCWorld}
    (hX : ProductAtomFresh X) (hW : ProductAtomFresh W)
    (hXval : ∀ n, ∃ x, v₀.ValuesAt (X n) x) (hWval : ∀ n, ∃ c, v₀.ValuesAt (W n) c) :
    (productExtensionWorld X W v₀).ConsistentWithTheory (productDefDP X W) := by
  intro k φ hφ
  obtain ⟨e, rfl⟩ := exists_of_mem_productStageList (List.mem_toFinset.mp hφ)
  rw [productDefSentence]
  exact productExtensionWorld_holds_schema hX hW hXval hWval _ _ _ _ _

/-- **`hworld` for the union.**  Every world of the base process that reads both source
families extends to a world of `base ∪ product-definitions` — so the exact certificate is
inhabited whenever the base one is, and the definitional extension is conservative on the
base language.
Paper node: `thm:ccee` -/
theorem productDefDP_union_consistentWithTheory {B : DeductiveProcess} {X W : ℕ → LUV}
    (hX : ProductAtomFresh X) (hW : ProductAtomFresh W)
    (hB : ∀ k, ∀ φ ∈ B.D k, ∀ a ∈ sentenceAtomCodes φ, a.unpair.1 ≠ productTag)
    {v₀ : PCWorld} (hv₀ : v₀.ConsistentWithTheory B)
    (hXval : ∀ n, ∃ x, v₀.ValuesAt (X n) x) (hWval : ∀ n, ∃ c, v₀.ValuesAt (W n) c) :
    (productExtensionWorld X W v₀).ConsistentWithTheory (B.union (productDefDP X W)) := by
  intro k
  refine ((productExtensionWorld X W v₀).consistentWith_union_iff B _ k).mpr ⟨?_, ?_⟩
  · intro φ hφ
    exact (productExtensionWorld_holds_iff X W v₀ (hB k φ hφ)).mpr (hv₀ k φ hφ)
  · exact productExtensionWorld_consistentWithTheory hX hW hXval hWval k

/-- Stages of the union constrain the extra process in particular. -/
lemma PCWorld.consistentWithTheory_union_right {v : PCWorld} {DP extra : DeductiveProcess}
    (h : v.ConsistentWithTheory (DP.union extra)) : v.ConsistentWithTheory extra :=
  fun n => ((v.consistentWith_union_iff DP extra n).mp (h n)).2

/-- **The exact product law over the union process.**  This is the shape
`ConditionalExpectationQuote.left_reflected` consumes, at `slack = 0`.
Paper node: `thm:ccee` -/
theorem productLUV_valuesAt_union {B : DeductiveProcess} {X W : ℕ → LUV} {v : PCWorld}
    (hv : v.ConsistentWithTheory (B.union (productDefDP X W))) (n : ℕ) {x c : ℝ}
    (hx : v.ValuesAt (X n) x) (hc : v.ValuesAt (W n) c) :
    v.ValuesAt (productLUV n) (x * c) :=
  productLUV_valuesAt (PCWorld.consistentWithTheory_union_right hv) n hx hc

/-! ## Threshold emission for the product family (`def:ec`)

The product LUV's threshold *is* a single fresh atom, so its emitter is the same shape as
the quotation atom's (`quoteAtom_mesh_encode_polyFueled`): a runtime `gcdc` reduction of the
mesh rational under a fixed atom shell.  Crucially the family does not mention `X`, `W` or
the weight at all — the emitted block is poly-sized in the index no matter what the weight
is, which is exactly the barrier that forced the mesh substitution on the scaled-threshold
route. -/

attribute [local irreducible] Nat.sqrt in
/-- One poly-fueled program emits the encoded product atom of day `m.unpair.1` at mesh
threshold `i/k` from the packed query `⟨n,⟨k,i⟩⟩`.
Paper node: `def:ec`, `thm:ccee` -/
lemma productAtom_mesh_encode_polyFueled :
    ∃ c, PolyFueled c (fun m => Encodable.encode (productAtom m.unpair.1
      ((m.unpair.2.unpair.2 : ℚ) / (m.unpair.2.unpair.1 : ℚ)))) := by
  obtain ⟨cg, hgcd⟩ := gcdc_polyFueled
  obtain ⟨cdm, hdm⟩ := divmod1_polyFueled
  obtain ⟨cad, had⟩ := addc_polyFueled
  have hn := PolyFueled.left
  have hk := PolyFueled.left.comp PolyFueled.right
  have hi := PolyFueled.right.comp PolyFueled.right
  have gPF := hgcd.comp (hi.pair hk)
  have pgPF := predc_polyFueled.comp gPF
  have numPF := PolyFueled.left.comp (hdm.comp (pgPF.pair hi))
  have denPF := PolyFueled.left.comp (hdm.comp (pgPF.pair hk))
  have h2num := had.comp (numPF.pair numPF)
  have meshPF := ifzSel_polyFueled.comp
    (((PolyFueled.const (Nat.pair 0 1)).pair (h2num.pair denPF)).pair hk)
  have fullPF := ((PolyFueled.const 1).pair
    ((PolyFueled.const productTag).pair (hn.pair meshPF))).succ_comp
  refine ⟨_, fullPF.of_eq (fun m => ?_)⟩
  rw [productAtom, encode_atom]
  simp only [Nat.unpair_pair, ifzSelFn]
  by_cases hk0 : m.unpair.2.unpair.1 = 0
  · rw [if_pos hk0, hk0]
    norm_num
    rfl
  · rw [if_neg hk0]
    have hg : 0 < Nat.gcd m.unpair.2.unpair.2 m.unpair.2.unpair.1 :=
      Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hk0)
    have hg1 : (Nat.gcd m.unpair.2.unpair.2 m.unpair.2.unpair.1).pred + 1
        = Nat.gcd m.unpair.2.unpair.2 m.unpair.2.unpair.1 :=
      Nat.succ_pred_eq_of_pos hg
    rw [hg1, encode_rat_natCast_div hk0, two_mul]

/-- The product family is polynomially threshold-codeable. -/
lemma productLUV_polyThresholdCodeSeq : LUV.PolyThresholdCodeSeq productLUV := by
  obtain ⟨c, hc⟩ := productAtom_mesh_encode_polyFueled
  exact ⟨c, hc.of_eq (fun m => by rw [productLUV_gt])⟩

/-- **`def:ec` for the quoted product.**  The block form used by
`ConditionalExpectationQuote.left_codes`.
Paper node: `def:ec`, `thm:ccee` -/
lemma productLUV_rpnThresholdCodeSeq : LUV.RpnThresholdCodeSeq productLUV :=
  LUV.RpnThresholdCodeSeq.ofPolyThresholdCodeSeq productLUV_polyThresholdCodeSeq

/-! ## Computability of the definitional-extension process

`def:dedproc` asks only for computability — no clock — which is the whole reason the exact
product is reachable here at all.  What the process does need is the two threshold families'
emitters *as data*: `LUV.RpnThresholdCodeSeq` is `∃`-shaped and certifies efficient emission
on the mesh index, whereas a process definition consumes a program.  This is the same
named-beside-existential pattern as `DeductiveProcessComputation` beside
`ComputableDeductiveProcess`. -/

/-- A named program emitting a LUV family's threshold sentences at arbitrary encoded rational
thresholds.
Paper node: `def:dedproc` -/
structure LUVThresholdComputation (X : ℕ → LUV) where
  code : Nat.Partrec.Code
  code_spec : ∀ m : ℕ,
    Encodable.encode ((X m.unpair.1).gt (decodedQuotationRat m.unpair.2)) ∈ code.eval m

lemma LUVThresholdComputation.computable {X : ℕ → LUV} (c : LUVThresholdComputation X) :
    Computable fun m : ℕ =>
      Encodable.encode ((X m.unpair.1).gt (decodedQuotationRat m.unpair.2)) := by
  have heval : Partrec fun m : ℕ => c.code.eval m :=
    Nat.Partrec.Code.eval_part.comp (Computable.const c.code) Computable.id
  exact heval.of_eq fun m => Part.eq_some_iff.mpr (c.code_spec m)

section
attribute [local irreducible] Nat.sqrt

/-- The schema instance is computable in its decoded arguments. -/
lemma productSchemaInstance_computable {X W : ℕ → LUV}
    (cX : LUVThresholdComputation X) (cW : LUVThresholdComputation W) :
    Computable fun p : ℕ × ℕ × ℚ × ℚ × ℚ =>
      productSchemaInstance X W p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 := by
  classical
  refine Computable.encode_iff.mp ?_
  have hn : Primrec fun p : ℕ × ℕ × ℚ × ℚ × ℚ => p.1 := Primrec.fst
  have hkind : Primrec fun p : ℕ × ℕ × ℚ × ℚ × ℚ => p.2.1 := Primrec.fst.comp Primrec.snd
  have hr : Primrec fun p : ℕ × ℕ × ℚ × ℚ × ℚ => p.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hs : Primrec fun p : ℕ × ℕ × ℚ × ℚ × ℚ => p.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have ht : Primrec fun p : ℕ × ℕ × ℚ × ℚ × ℚ => p.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have heX : Computable fun p : ℕ × ℕ × ℚ × ℚ × ℚ =>
      Encodable.encode ((X p.1).gt p.2.2.2.1) := by
    have h := cX.computable.comp
      (Primrec₂.natPair.to_comp.comp hn.to_comp (Primrec.encode.comp hs).to_comp)
    simpa only [Nat.unpair_pair, decodedQuotationRat_encode] using h
  have heW : Computable fun p : ℕ × ℕ × ℚ × ℚ × ℚ =>
      Encodable.encode ((W p.1).gt p.2.2.2.2) := by
    have h := cW.computable.comp
      (Primrec₂.natPair.to_comp.comp hn.to_comp (Primrec.encode.comp ht).to_comp)
    simpa only [Nat.unpair_pair, decodedQuotationRat_encode] using h
  have heP : Primrec fun p : ℕ × ℕ × ℚ × ℚ × ℚ =>
      Nat.pair 1 (Nat.pair productTag (Nat.pair p.1 (Encodable.encode p.2.2.1))) + 1 :=
    Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 1)
      (Primrec₂.natPair.comp (Primrec.const productTag)
        (Primrec₂.natPair.comp hn (Primrec.encode.comp hr))))
  have hk0 : PrimrecPred fun p : ℕ × ℕ × ℚ × ℚ × ℚ => p.2.1 = 0 :=
    Primrec.eq.comp hkind (Primrec.const 0)
  have hk1 : PrimrecPred fun p : ℕ × ℕ × ℚ × ℚ × ℚ => p.2.1 = 1 :=
    Primrec.eq.comp hkind (Primrec.const 1)
  have hmul : Primrec fun p : ℕ × ℕ × ℚ × ℚ × ℚ => p.2.2.2.1 * p.2.2.2.2 :=
    ratMul_prim.comp hs ht
  have hs0 : PrimrecPred fun p : ℕ × ℕ × ℚ × ℚ × ℚ => (0 : ℚ) ≤ p.2.2.2.1 :=
    ratLE_prim.comp (Primrec.const 0) hs
  have ht0 : PrimrecPred fun p : ℕ × ℕ × ℚ × ℚ × ℚ => (0 : ℚ) ≤ p.2.2.2.2 :=
    ratLE_prim.comp (Primrec.const 0) ht
  have hG0 : PrimrecPred fun p : ℕ × ℕ × ℚ × ℚ × ℚ =>
      (0 : ℚ) ≤ p.2.2.2.1 ∧ (0 : ℚ) ≤ p.2.2.2.2 ∧ p.2.2.1 ≤ p.2.2.2.1 * p.2.2.2.2 :=
    hs0.and (ht0.and (ratLE_prim.comp hr hmul))
  have hG1 : PrimrecPred fun p : ℕ × ℕ × ℚ × ℚ × ℚ =>
      (0 : ℚ) ≤ p.2.2.2.1 ∧ (0 : ℚ) ≤ p.2.2.2.2 ∧ p.2.2.2.1 * p.2.2.2.2 ≤ p.2.2.1 :=
    hs0.and (ht0.and (ratLE_prim.comp hmul hr))
  have hNeg : PrimrecPred fun p : ℕ × ℕ × ℚ × ℚ × ℚ => p.2.2.1 < 0 := by
    have h : PrimrecPred fun p : ℕ × ℕ × ℚ × ℚ × ℚ => (0 : ℚ) ≤ p.2.2.1 :=
      ratLE_prim.comp (Primrec.const 0) hr
    exact h.not.of_eq (fun p => by simp [not_le])
  have hAnd : Computable fun p : ℕ × ℕ × ℚ × ℚ × ℚ =>
      Nat.pair 2 (Nat.pair (Nat.pair 3
        (Nat.pair (Encodable.encode ((X p.1).gt p.2.2.2.1))
          (Encodable.encode ((W p.1).gt p.2.2.2.2))) + 1)
        (Nat.pair 1 (Nat.pair productTag
          (Nat.pair p.1 (Encodable.encode p.2.2.1))) + 1)) + 1 :=
    Primrec.succ.to_comp.comp (Primrec₂.natPair.to_comp.comp (Computable.const 2)
      (Primrec₂.natPair.to_comp.comp
        (Primrec.succ.to_comp.comp (Primrec₂.natPair.to_comp.comp (Computable.const 3)
          (Primrec₂.natPair.to_comp.comp heX heW)))
        heP.to_comp))
  have hOr : Computable fun p : ℕ × ℕ × ℚ × ℚ × ℚ =>
      Nat.pair 2 (Nat.pair
        (Nat.pair 1 (Nat.pair productTag
          (Nat.pair p.1 (Encodable.encode p.2.2.1))) + 1)
        (Nat.pair 4
          (Nat.pair (Encodable.encode ((X p.1).gt p.2.2.2.1))
            (Encodable.encode ((W p.1).gt p.2.2.2.2))) + 1)) + 1 :=
    Primrec.succ.to_comp.comp (Primrec₂.natPair.to_comp.comp (Computable.const 2)
      (Primrec₂.natPair.to_comp.comp heP.to_comp
        (Primrec.succ.to_comp.comp (Primrec₂.natPair.to_comp.comp (Computable.const 4)
          (Primrec₂.natPair.to_comp.comp heX heW)))))
  have hTop : Computable fun _ : ℕ × ℕ × ℚ × ℚ × ℚ =>
      Encodable.encode (⊤ : Sentence) := Computable.const _
  refine ((hk0.decide.to_comp.cond (hG0.decide.to_comp.cond hAnd hTop)
    (hk1.decide.to_comp.cond (hG1.decide.to_comp.cond hOr hTop)
      (hNeg.decide.to_comp.cond heP.to_comp hTop))).of_eq (fun p => ?_))
  rw [productSchemaInstance]
  split_ifs with h0 hg0 h1 hg1 hneg
  · simp only [h0, hg0, decide_true, cond_true, productAtom]
    rfl
  · simp [h0, hg0]
  · simp only [h0, h1, hg1, decide_true, decide_false, cond_true, cond_false, productAtom]
    rfl
  · simp [h0, h1, hg1]
  · simp only [h0, h1, hneg, decide_true, decide_false, cond_true, cond_false, productAtom]
    rfl
  · simp [h0, h1, hneg]

/-- The job-code decoding is primitive recursive, so the schema enumerator is computable. -/
lemma productDefSentence_computable {X W : ℕ → LUV}
    (cX : LUVThresholdComputation X) (cW : LUVThresholdComputation W) :
    Computable (productDefSentence X W) := by
  have hn : Primrec fun e : ℕ => e.unpair.1 := Primrec.fst.comp Primrec.unpair
  have h2 : Primrec fun e : ℕ => e.unpair.2 := Primrec.snd.comp Primrec.unpair
  have hkind : Primrec fun e : ℕ => e.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp h2)
  have h3 : Primrec fun e : ℕ => e.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp h2)
  have hcr : Primrec fun e : ℕ => e.unpair.2.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp h3)
  have h4 : Primrec fun e : ℕ => e.unpair.2.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp h3)
  have hcs : Primrec fun e : ℕ => e.unpair.2.unpair.2.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp h4)
  have hct : Primrec fun e : ℕ => e.unpair.2.unpair.2.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp h4)
  have hargs : Computable fun e : ℕ =>
      ((e.unpair.1, e.unpair.2.unpair.1,
        decodedQuotationRat e.unpair.2.unpair.2.unpair.1,
        decodedQuotationRat e.unpair.2.unpair.2.unpair.2.unpair.1,
        decodedQuotationRat e.unpair.2.unpair.2.unpair.2.unpair.2) :
        ℕ × ℕ × ℚ × ℚ × ℚ) :=
    (hn.pair (hkind.pair ((decodedQuotationRat_prim.comp hcr).pair
      ((decodedQuotationRat_prim.comp hcs).pair
        (decodedQuotationRat_prim.comp hct))))).to_comp
  exact (productSchemaInstance_computable cX cW).comp hargs

/-- **The product-definition process is computable** (`def:dedproc`).
Paper node: `def:dedproc`, `thm:ccee` -/
lemma productDefDP_computable {X W : ℕ → LUV}
    (cX : LUVThresholdComputation X) (cW : LUVThresholdComputation W) :
    ComputableDeductiveProcess (productDefDP X W) := by
  have hlist : Computable (productStageList X W) := by
    have hstep : Computable fun p : ℕ × List Sentence =>
        productDefSentence X W (p.1 + 1) :: p.2 :=
      Computable.list_cons.comp
        ((productDefSentence_computable cX cW).comp
          (Primrec.succ.to_comp.comp Computable.fst)) Computable.snd
    refine (Computable.nat_rec Computable.id
      (Computable.const [productDefSentence X W 0])
      (hstep.comp₂ Computable.snd.to₂)).of_eq (fun k => ?_)
    induction k with
    | zero => rfl
    | succ k ih => simpa [productStageList] using ih
  have hkey : Computable fun k => Encodable.encode
      ((sentenceDedup (productStageList X W k)).insertionSort sentenceCodeLE) :=
    Computable.encode.comp
      ((sentenceInsertionSort_prim.comp sentenceDedup_prim).to_comp.comp hlist)
  obtain ⟨code, hcode⟩ := Nat.Partrec.Code.exists_code.mp
    (Partrec.nat_iff.mp hkey)
  refine ⟨code, fun k => ?_⟩
  rw [hcode]
  exact Part.mem_some_iff.mpr (encode_toFinset_eq (productStageList X W k))

end

/-! ## The exact `thm:ccee` endpoint

`lic_no_expected_net_update_conditional` is deductive-process generic and consumes the
reflection slack through `slack_tendsto`, so `slack ≡ 0` is a special case and neither the
master theorem nor `ConditionalExpectationQuote` changes.  What changes is *which* process
the endpoint is stated over: `base ∪ product-definitions` rather than bare base.  That is
faithful — the paper's `Θ` contains the product term natively and a fresh-atom definitional
extension is its propositional counterpart — but it is a different rendering from the mesh
route's bare-base statement, and it is the honest cost of exactness here. -/

/-- **`thm:ccee` at exact reflection**, for an **arbitrary** e.c. source family `X`, over the
base process extended by the product definitions.  The left quoted product is the fresh atom
family `productLUV`; every completed-theory world of the extended process values it at
exactly `x · w (f n)`, with no slack and no positivity hypothesis on the weight.

The weight enters as in the paper (`def:pgen`): `P`-generable against the market, presented
through a LUV family `W` whose completed-world value *is* `w (f n)` — in the closed setting
that family is the deferred-weight quote code's own LUV.
Paper node: `thm:ccee` -/
theorem lic_no_expected_net_update_conditional_exact
    {P : History} {B : DeductiveProcess} {X W : ℕ → LUV}
    [IsLogicalInductor P (B.union (productDefDP X W))]
    (f : DeferralFunction) (Z' : ℕ → LUV) (w : ℕ → ℚ)
    (weight_mem : ∀ n, 0 ≤ w n ∧ w n ≤ 1)
    (weight_generable : PGenerableRat P w)
    (hX : LUV.RpnThresholdCodeSeq X) (hZ' : LUV.RpnThresholdCodeSeq Z')
    (source_valued : ∀ n (v : PCWorld),
      v.ConsistentWithTheory (B.union (productDefDP X W)) → ∃ x, v.ValuesAt (X n) x)
    (weight_valued : ∀ n (v : PCWorld),
      v.ConsistentWithTheory (B.union (productDefDP X W)) → v.ValuesAt (W n) (w (f n)))
    (right_reflected : ∀ n (v : PCWorld),
      v.ConsistentWithTheory (B.union (productDefDP X W)) →
        v.ValuesAt (Z' n) ((X n).expect P (f n) * w (f n)))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((B.union (productDefDP X W)).D n)) :
    (fun n ↦ (productLUV n).expect P n) ≈ₙ fun n ↦ (Z' n).expect P n :=
  lic_no_expected_net_update_conditional_ofRepresentation
    (DP := B.union (productDefDP X W)) f X productLUV Z' w
    weight_mem weight_generable hX productLUV_rpnThresholdCodeSeq hZ'
    (fun _ => 0) tendsto_const_nhds source_valued
    (fun n v hv x hx => ⟨x * (w (f n) : ℝ),
      productLUV_valuesAt_union hv n hx (weight_valued n v hv), by simp⟩)
    right_reflected hworld

#print axioms PCWorld.holds_congr_atomCodes
#print axioms productLUV_valuesAt
#print axioms productExtensionWorld_holds_schema
#print axioms productDefDP_union_consistentWithTheory
#print axioms productLUV_valuesAt_union
#print axioms productLUV_rpnThresholdCodeSeq
#print axioms productDefDP_computable
#print axioms lic_no_expected_net_update_conditional_exact

end LogicalInduction
