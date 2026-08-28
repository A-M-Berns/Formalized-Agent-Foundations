import LogicalInduction.Construction.Witnesses.ConditioningPresentation
import LogicalInduction.Construction.Witnesses.PrefixMachine
import LogicalInduction.Construction.Witnesses.QuoteCodeOfMarket
import LogicalInduction.Framework.WriteOut

/-!
# Diagnosing the `thm:ccee` product slack: exact reflection under a definitional extension

`QuoteCodeOfMarket.lean`'s Part F builds the `thm:ccee` left product as a width-`n+1` mesh,
which reflects `x · w (f n)` only to within `1/(n+1)` — the one disclosed type-`(c)`
substitution of that endpoint.  The obstruction there is the *emitter*: a strategy block has
to be produced with polynomial fuel, and the exact threshold `⌜X > r / w (f n)⌝` names a
value the emitter cannot have.

A **deductive process** carries no such clock: it is only required computable.  So an exact
product *is* available as a *definitional extension of the process*, not of the theory:
fresh atoms `productAtom n r` standing for `⌜Xₙ · Wₙ > r⌝`, together with the defining
schema entered stagewise by an extra process.  Nothing in the first-order theory changes;
the paper's `Θ` contains the product term natively, and a fresh-atom definitional extension
is the propositional counterpart.

**What this file is for.**  It shows that the mesh endpoint's slack is an artifact of the
propositional substrate rather than of logical induction: the same trader and the same
criterion give an exact conclusion as soon as the product exists syntactically.  It is
**not** a rendering of `thm:ccee` and does not supersede
`lic_no_expected_net_update_conditional_closed`, because the inductor here is `LIA` over the
*extended* process — a different inductor — and conservativity of completed-world truth does
not carry prices across.  The same caveat applies to the zero-slack endpoint
`lic_no_expected_net_update_conditional_exact_canonical`
(`Construction/Witnesses/SemanticLiftedCCEE.lean`), which buys exactness over
`liaHistory (canonicalCCEEDP T)` rather than over `liaHistory (theoremDP T)`.  A reader who
needs a statement about the latter market must use the mesh endpoint.

## The schema

Naming the *value* of the weight is what the emitter cannot do — but the schema never needs
it.  For nonnegative rational factors `s, t` — indexed as `i/k`, exactly the way `def:ec`'s
block interface already indexes threshold sentences — the process enters

* `(⌜Xₙ > s⌝ ⋏ ⌜Wₙ > t⌝) 🡒 productAtom n r`   whenever `r ≤ s·t`,
* `productAtom n r 🡒 (⌜Xₙ > s⌝ ⋎ ⌜Wₙ > t⌝)`   whenever `s·t ≤ r`,
* `productAtom n r`                             whenever `r < 0`,

which mentions only the two source families' own threshold sentences and is decidable in
`(n, r, s, t)`.  In a world valuing `Xₙ` at `x` and `Wₙ` at `c`, density of ℚ in the two
factors pins `productAtom n r` to exactly `x·c > r`, in both directions — i.e.
`ValuesAt (productLUV n) (x·c)`, with **no slack** and with no positivity hypothesis on `c`
(the `c = 0` case is the `r < 0` axiom plus the negative schema, not a case split).

Indexing the factors by `⟨k,i⟩` rather than by an encoded rational is what makes the
process's own emitter *derivable* from the two families' `def:ec` certificates
(`LUV.RpnThresholdCodeSeq`, via `BigSentenceCodes.primrec`) instead of an extra
caller-facing datum: the schema's threshold queries land on exactly the packed index
`⟨n,⟨k,i⟩⟩` that certificate is stated at.

This is a strict improvement on the obvious schema, which has the process compute `w (f n)`
through `PGenerableRat.computable` and enter
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

open LO LO.Propositional LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open Filter Topology

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

/-! ### Freshness by construction

For a *genuinely arbitrary* e.c. family, `ProductAtomFresh` must be assumed: a
`LUV.RpnThresholdCodeSeq` certificate constrains only the size of the emitted threshold
blocks, never which atoms they mention, so a poly-fueled emitter is free to emit tag-`5`
atoms.  For everything this repository constructs the condition is a *theorem*, and the
lemmas below are what discharge it: the constructed process's stages are images of
`eventAtom`, whose atoms carry the computation-claim tags `0`–`3` or the quotation tag `4`,
and every quotation threshold family carries tag `4`.  Nothing but `productLUV` uses tag
`productTag = 5`. -/

@[simp] lemma sentenceAtomCodes_neg (φ : Sentence) :
    sentenceAtomCodes (∼φ) = sentenceAtomCodes φ := by
  rw [Formula.neg_def, sentenceAtomCodes_imp, sentenceAtomCodes_falsum, Finset.union_empty]

@[simp] lemma sentenceAtomCodes_verum :
    sentenceAtomCodes (⊤ : Sentence) = ∅ := rfl

lemma sentenceAtomCodes_computationClaimSentence (c : ComputationClaim) :
    ∀ a ∈ sentenceAtomCodes (computationClaimSentence c), a.unpair.1 = c.kind.godelCode := by
  intro a ha
  rw [computationClaimSentence, sentenceAtomCodes_atom, Finset.mem_singleton] at ha
  subst ha
  simp [ComputationClaim.godelCode]

lemma sentenceAtomCodes_quoteAtom (w : ℕ) :
    ∀ a ∈ sentenceAtomCodes (quoteAtom w), a.unpair.1 = 4 := by
  intro a ha
  rw [quoteAtom, quotationClaimSentence, sentenceAtomCodes_atom, Finset.mem_singleton] at ha
  subst ha
  simp [quotationClaimCode]

/-- **The constructed process's literals never carry the product tag.**  Every atom of an
`eventAtom` is a computation claim (tags `0`–`3`) or a quotation claim (tag `4`). -/
lemma eventAtom_atomCodes_ne_productTag (e : ℕ) :
    ∀ a ∈ sentenceAtomCodes (eventAtom e), a.unpair.1 ≠ productTag := by
  intro a ha
  rcases h : e.unpair.1 with _ | _ | _ | _ | _ | _ | _ | _ | m
  all_goals simp only [eventAtom, h, sentenceAtomCodes_neg] at ha
  · exact fun hc => by
      simp [sentenceAtomCodes_computationClaimSentence _ a ha, haltingClaim,
        ComputationClaimKind.godelCode, productTag] at hc
  · exact fun hc => by
      simp [sentenceAtomCodes_computationClaimSentence _ a ha, haltingClaim,
        ComputationClaimKind.godelCode, productTag] at hc
  · exact fun hc => by
      simp [sentenceAtomCodes_computationClaimSentence _ a ha, boundedHaltingClaim,
        ComputationClaimKind.godelCode, productTag] at hc
  · exact fun hc => by
      simp [sentenceAtomCodes_computationClaimSentence _ a ha, boundedHaltingClaim,
        ComputationClaimKind.godelCode, productTag] at hc
  · exact fun hc => by
      simp [sentenceAtomCodes_computationClaimSentence _ a ha, inconsistencyClaim,
        ComputationClaimKind.godelCode, productTag] at hc
  · exact fun hc => by
      simp [sentenceAtomCodes_computationClaimSentence _ a ha, consistencyClaim,
        ComputationClaimKind.godelCode, productTag] at hc
  · exact fun hc => by simp [sentenceAtomCodes_quoteAtom _ a ha, productTag] at hc
  · exact fun hc => by simp [sentenceAtomCodes_quoteAtom _ a ha, productTag] at hc
  · simp at ha

/-- Every quotation threshold family is fresh for the product tag: its thresholds are
quotation atoms (tag `4`). -/
lemma arithmeticThresholdLUV_productAtomFresh (code : ℕ) :
    ProductAtomFresh (arithmeticThresholdLUV code) := by
  intro n r a ha
  have h := sentenceAtomCodes_quoteAtom _ a ha
  simp [h, productTag]

/-- A rational quote code's LUV family is fresh for the product tag. -/
lemma RationalQuoteCode.productAtomFresh {T : ArithmeticTheory} {value : ℕ → ℚ}
    (q : RationalQuoteCode T value) : ProductAtomFresh q.luv :=
  arithmeticThresholdLUV_productAtomFresh q.code

/-- **The base process is fresh for the product tag**, by construction: every stage of the
constructed provability process is an image of `eventAtom`.  This is the side condition
`productDefDP_union_consistentWithTheory` takes on the base process, discharged rather than
assumed. -/
lemma theoremDP_atomCodes_ne_productTag (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T]
    [T.SoundOnHierarchy 𝚺 1] (k : ℕ) :
    ∀ φ ∈ (theoremDP T).D k, ∀ a ∈ sentenceAtomCodes φ, a.unpair.1 ≠ productTag := by
  classical
  intro φ hφ
  simp only [theoremDP, theoremStage, Finset.mem_image, Finset.mem_filter,
    Finset.mem_range] at hφ
  obtain ⟨e, _, rfl⟩ := hφ
  exact eventAtom_atomCodes_ne_productTag e

/-! ## Mesh indices for the schema's two factors

`def:ec`'s block interface (`LUV.RpnThresholdCodeSeq`) emits `⌜Xₙ > i/k⌝` at the packed
index `⟨n,⟨k,i⟩⟩`.  The schema only ever needs *nonnegative* factors, and every nonnegative
rational is some `i/k`, so indexing the factors that way costs nothing and buys the
process's emitter outright. -/

/-- The nonnegative rational named by the packed mesh index `z = ⟨k,i⟩`, namely `i/k`.  The
degenerate index `k = 0` names `0`; that is harmless, since the schema is sound at every
nonnegative factor. -/
def meshIndexRat (z : ℕ) : ℚ := (z.unpair.2 : ℚ) / (z.unpair.1 : ℚ)

lemma meshIndexRat_nonneg (z : ℕ) : 0 ≤ meshIndexRat z := by
  unfold meshIndexRat; positivity

/-- Every nonnegative rational is named by a mesh index — the density fact the exact
product law needs, in index form. -/
lemma exists_meshIndexRat {q : ℚ} (hq : 0 ≤ q) : ∃ z, meshIndexRat z = q := by
  refine ⟨Nat.pair q.den q.num.toNat, ?_⟩
  have hnum : ((q.num.toNat : ℕ) : ℚ) = (q.num : ℚ) := by
    exact_mod_cast congrArg (fun i : ℤ => (i : ℚ)) (Int.toNat_of_nonneg (Rat.num_nonneg.mpr hq))
  simp only [meshIndexRat, Nat.unpair_pair, hnum]
  exact q.num_div_den

/-! ## The defining process -/

/-- One instance of the defining schema, in decoded form: the two factors arrive as mesh
indices `zs, zt`.  Guards that fail emit `⊤`, which every world holds and no world is
constrained by. -/
def productSchemaInstance (X W : ℕ → LUV) (n kind : ℕ) (r : ℚ) (zs zt : ℕ) : Sentence :=
  if kind = 0 then
    (if r ≤ meshIndexRat zs * meshIndexRat zt then
      ((X n).gt (meshIndexRat zs) ⋏ (W n).gt (meshIndexRat zt)) 🡒 productAtom n r else ⊤)
  else if kind = 1 then
    (if meshIndexRat zs * meshIndexRat zt ≤ r then
      productAtom n r 🡒 ((X n).gt (meshIndexRat zs) ⋎ (W n).gt (meshIndexRat zt)) else ⊤)
  else
    (if r < 0 then productAtom n r else ⊤)

/-- The schema instance at the job code `e = ⟨n, ⟨kind, ⟨⌜r⌝, ⟨zs, zt⟩⟩⟩⟩`. -/
def productDefSentence (X W : ℕ → LUV) (e : ℕ) : Sentence :=
  productSchemaInstance X W e.unpair.1 e.unpair.2.unpair.1
    (decodedQuotationRat e.unpair.2.unpair.2.unpair.1)
    e.unpair.2.unpair.2.unpair.2.unpair.1
    e.unpair.2.unpair.2.unpair.2.unpair.2

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

lemma productDefSentence_pair (X W : ℕ → LUV) (n kind : ℕ) (r : ℚ) (zs zt : ℕ) :
    productDefSentence X W
        (Nat.pair n (Nat.pair kind (Nat.pair (Encodable.encode r)
          (Nat.pair zs zt)))) =
      productSchemaInstance X W n kind r zs zt := by
  rw [productDefSentence]
  simp only [Nat.unpair_pair, decodedQuotationRat_encode]

lemma holds_productDef_pos {X W : ℕ → LUV} {v : PCWorld}
    (hv : v.ConsistentWithTheory (productDefDP X W)) (n : ℕ) {r : ℚ} {zs zt : ℕ}
    (hst : r ≤ meshIndexRat zs * meshIndexRat zt)
    (hX : v.Holds ((X n).gt (meshIndexRat zs)))
    (hW : v.Holds ((W n).gt (meshIndexRat zt))) :
    v.Holds (productAtom n r) := by
  have h := holds_productDefSentence hv
    (Nat.pair n (Nat.pair 0 (Nat.pair (Encodable.encode r) (Nat.pair zs zt))))
  rw [productDefSentence_pair, productSchemaInstance, if_pos rfl, if_pos hst] at h
  exact h ⟨hX, hW⟩

lemma not_holds_productDef_neg {X W : ℕ → LUV} {v : PCWorld}
    (hv : v.ConsistentWithTheory (productDefDP X W)) (n : ℕ) {r : ℚ} {zs zt : ℕ}
    (hst : meshIndexRat zs * meshIndexRat zt ≤ r)
    (hX : ¬ v.Holds ((X n).gt (meshIndexRat zs)))
    (hW : ¬ v.Holds ((W n).gt (meshIndexRat zt))) :
    ¬ v.Holds (productAtom n r) := by
  have h := holds_productDefSentence hv
    (Nat.pair n (Nat.pair 1 (Nat.pair (Encodable.encode r) (Nat.pair zs zt))))
  rw [productDefSentence_pair, productSchemaInstance,
    if_neg (by decide : ¬ (1 : ℕ) = 0), if_pos rfl, if_pos hst] at h
  intro hcon
  rcases h hcon with hl | hr
  · exact hX hl
  · exact hW hr

lemma holds_productDef_below {X W : ℕ → LUV} {v : PCWorld}
    (hv : v.ConsistentWithTheory (productDefDP X W)) (n : ℕ) {r : ℚ} (hr : r < 0) :
    v.Holds (productAtom n r) := by
  have h := holds_productDefSentence hv
    (Nat.pair n (Nat.pair 2 (Nat.pair (Encodable.encode r) (Nat.pair 0 0))))
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
      obtain ⟨zs, rfl⟩ := exists_meshIndexRat hs0
      obtain ⟨zt, rfl⟩ := exists_meshIndexRat ht0
      exact holds_productDef_pos hv n hst ((hxthr _).1 hsx) ((hcthr _).1 htc)
  · intro hr
    rw [productLUV_gt]
    obtain ⟨s, t, hs0, ht0, hst, hxs, hct⟩ := exists_rat_pair_mul_lt hx0 hc0 hr
    obtain ⟨zs, rfl⟩ := exists_meshIndexRat hs0
    obtain ⟨zt, rfl⟩ := exists_meshIndexRat ht0
    exact not_holds_productDef_neg hv n hst ((hxthr _).2 hxs) ((hcthr _).2 hct)

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
  r < 0 ∨ ∃ zs zt : ℕ, r ≤ meshIndexRat zs * meshIndexRat zt ∧
    v₀.Holds ((X n).gt (meshIndexRat zs)) ∧ v₀.Holds ((W n).gt (meshIndexRat zt))

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
    (n kind : ℕ) (r : ℚ) (zs zt : ℕ) :
    (productExtensionWorld X W v₀).Holds (productSchemaInstance X W n kind r zs zt) := by
  have hXtr : ∀ (m : ℕ) (q : ℚ),
      (productExtensionWorld X W v₀).Holds ((X m).gt q) ↔ v₀.Holds ((X m).gt q) :=
    fun m q => productExtensionWorld_holds_iff X W v₀ (hX m q)
  have hWtr : ∀ (m : ℕ) (q : ℚ),
      (productExtensionWorld X W v₀).Holds ((W m).gt q) ↔ v₀.Holds ((W m).gt q) :=
    fun m q => productExtensionWorld_holds_iff X W v₀ (hW m q)
  rw [productSchemaInstance]
  set s : ℚ := meshIndexRat zs with hsdef
  set t : ℚ := meshIndexRat zt with htdef
  have hs0 : 0 ≤ s := meshIndexRat_nonneg zs
  have ht0 : 0 ≤ t := meshIndexRat_nonneg zt
  split_ifs with _ hg0 _ hg1 hneg
  · intro hc
    exact (productExtensionWorld_productAtom X W v₀ n r).mpr
      (Or.inr ⟨zs, zt, hg0, (hXtr n s).1 hc.1, (hWtr n t).1 hc.2⟩)
  · exact PCWorld.holds_top _
  · intro hp
    have hp' := (productExtensionWorld_productAtom X W v₀ n r).mp hp
    show (productExtensionWorld X W v₀).Holds ((X n).gt s) ∨
      (productExtensionWorld X W v₀).Holds ((W n).gt t)
    by_contra hcon
    push_neg at hcon
    obtain ⟨hnX, hnW⟩ := hcon
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
    rcases hp' with hrneg | ⟨zs₁, zt₁, hr₁, hXs₁, hWt₁⟩
    · nlinarith
    · set s₁ : ℚ := meshIndexRat zs₁ with hs₁def
      set t₁ : ℚ := meshIndexRat zt₁ with ht₁def
      have hs₁ : 0 ≤ s₁ := meshIndexRat_nonneg zs₁
      have ht₁ : 0 ≤ t₁ := meshIndexRat_nonneg zt₁
      have hs₁x : (s₁ : ℝ) ≤ x := by
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
product is reachable here at all.  And because the schema's two factors are indexed the way
`def:ec`'s block interface already indexes thresholds, the process's own emitter is
*derived* from `LUV.RpnThresholdCodeSeq X` and `LUV.RpnThresholdCodeSeq W` — the very
premises the mesh endpoint already carries — rather than assumed as a new caller-facing
certificate.  `BigSentenceCodes.primrec` turns the `∃`-shaped block certificate into the
whole-value naming program a process definition consumes. -/

section
attribute [local irreducible] Nat.sqrt

/-- The mesh-index rational is primitive recursive. -/
lemma meshIndexRat_prim : Primrec meshIndexRat :=
  ratDiv_prim.comp (ratNatCast_prim.comp (Primrec.snd.comp Primrec.unpair))
    (ratNatCast_prim.comp (Primrec.fst.comp Primrec.unpair))

/-- **The schema enumerator is computable**, with its two threshold emitters read off the
source families' own `def:ec` block certificates at the packed index `⟨n,⟨k,i⟩⟩`. -/
lemma productDefSentence_computable {X W : ℕ → LUV}
    (hX : LUV.RpnThresholdCodeSeq X) (hW : LUV.RpnThresholdCodeSeq W) :
    Computable (productDefSentence X W) := by
  classical
  refine Computable.encode_iff.mp ?_
  -- Job-code components.
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
  have hzs : Primrec fun e : ℕ => e.unpair.2.unpair.2.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp h4)
  have hzt : Primrec fun e : ℕ => e.unpair.2.unpair.2.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp h4)
  have hr : Primrec fun e : ℕ => decodedQuotationRat e.unpair.2.unpair.2.unpair.1 :=
    decodedQuotationRat_prim.comp hcr
  have hs : Primrec fun e : ℕ => meshIndexRat e.unpair.2.unpair.2.unpair.2.unpair.1 :=
    meshIndexRat_prim.comp hzs
  have ht : Primrec fun e : ℕ => meshIndexRat e.unpair.2.unpair.2.unpair.2.unpair.2 :=
    meshIndexRat_prim.comp hzt
  -- The two threshold emitters, derived from the `def:ec` block certificates.
  have heX : Primrec fun e : ℕ => Encodable.encode
      ((X e.unpair.1).gt (meshIndexRat e.unpair.2.unpair.2.unpair.2.unpair.1)) := by
    have h := (BigSentenceCodes.primrec hX).comp (Primrec₂.natPair.comp hn hzs)
    simpa only [Nat.unpair_pair, meshIndexRat] using h
  have heW : Primrec fun e : ℕ => Encodable.encode
      ((W e.unpair.1).gt (meshIndexRat e.unpair.2.unpair.2.unpair.2.unpair.2)) := by
    have h := (BigSentenceCodes.primrec hW).comp (Primrec₂.natPair.comp hn hzt)
    simpa only [Nat.unpair_pair, meshIndexRat] using h
  -- The fresh product atom's code.
  have heP : Primrec fun e : ℕ =>
      Nat.pair 1 (Nat.pair productTag (Nat.pair e.unpair.1
        (Encodable.encode (decodedQuotationRat e.unpair.2.unpair.2.unpair.1)))) + 1 :=
    Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 1)
      (Primrec₂.natPair.comp (Primrec.const productTag)
        (Primrec₂.natPair.comp hn (Primrec.encode.comp hr))))
  -- The three decidable guards.
  have hk0 : PrimrecPred fun e : ℕ => e.unpair.2.unpair.1 = 0 :=
    Primrec.eq.comp hkind (Primrec.const 0)
  have hk1 : PrimrecPred fun e : ℕ => e.unpair.2.unpair.1 = 1 :=
    Primrec.eq.comp hkind (Primrec.const 1)
  have hmul : Primrec fun e : ℕ =>
      meshIndexRat e.unpair.2.unpair.2.unpair.2.unpair.1 *
        meshIndexRat e.unpair.2.unpair.2.unpair.2.unpair.2 := ratMul_prim.comp hs ht
  have hG0 : PrimrecPred fun e : ℕ =>
      decodedQuotationRat e.unpair.2.unpair.2.unpair.1 ≤
        meshIndexRat e.unpair.2.unpair.2.unpair.2.unpair.1 *
          meshIndexRat e.unpair.2.unpair.2.unpair.2.unpair.2 := ratLE_prim.comp hr hmul
  have hG1 : PrimrecPred fun e : ℕ =>
      meshIndexRat e.unpair.2.unpair.2.unpair.2.unpair.1 *
          meshIndexRat e.unpair.2.unpair.2.unpair.2.unpair.2 ≤
        decodedQuotationRat e.unpair.2.unpair.2.unpair.1 := ratLE_prim.comp hmul hr
  have hNeg : PrimrecPred fun e : ℕ =>
      decodedQuotationRat e.unpair.2.unpair.2.unpair.1 < 0 := by
    have h : PrimrecPred fun e : ℕ =>
        (0 : ℚ) ≤ decodedQuotationRat e.unpair.2.unpair.2.unpair.1 :=
      ratLE_prim.comp (Primrec.const 0) hr
    exact h.not.of_eq (fun e => by simp [not_le])
  -- The two compound schema bodies.
  have hAnd : Primrec fun e : ℕ =>
      Nat.pair 2 (Nat.pair (Nat.pair 3
        (Nat.pair (Encodable.encode
            ((X e.unpair.1).gt (meshIndexRat e.unpair.2.unpair.2.unpair.2.unpair.1)))
          (Encodable.encode
            ((W e.unpair.1).gt (meshIndexRat e.unpair.2.unpair.2.unpair.2.unpair.2)))) + 1)
        (Nat.pair 1 (Nat.pair productTag
          (Nat.pair e.unpair.1
            (Encodable.encode (decodedQuotationRat e.unpair.2.unpair.2.unpair.1)))) + 1)) + 1 :=
    Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 2)
      (Primrec₂.natPair.comp
        (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 3)
          (Primrec₂.natPair.comp heX heW)))
        heP))
  have hOr : Primrec fun e : ℕ =>
      Nat.pair 2 (Nat.pair
        (Nat.pair 1 (Nat.pair productTag
          (Nat.pair e.unpair.1
            (Encodable.encode (decodedQuotationRat e.unpair.2.unpair.2.unpair.1)))) + 1)
        (Nat.pair 4
          (Nat.pair (Encodable.encode
              ((X e.unpair.1).gt (meshIndexRat e.unpair.2.unpair.2.unpair.2.unpair.1)))
            (Encodable.encode
              ((W e.unpair.1).gt (meshIndexRat e.unpair.2.unpair.2.unpair.2.unpair.2)))) + 1)) + 1 :=
    Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 2)
      (Primrec₂.natPair.comp heP
        (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 4)
          (Primrec₂.natPair.comp heX heW)))))
  have hTop : Primrec fun _ : ℕ => Encodable.encode (⊤ : Sentence) := Primrec.const _
  refine (((hk0.decide.cond (hG0.decide.cond hAnd hTop)
    (hk1.decide.cond (hG1.decide.cond hOr hTop)
      (hNeg.decide.cond heP hTop))).to_comp).of_eq (fun e => ?_))
  rw [productDefSentence, productSchemaInstance]
  split_ifs with h0 hg0 h1 hg1 hneg
  · simp only [h0, hg0, decide_true, cond_true, productAtom]
    rfl
  · simp [h0, hg0]
  · simp only [h1, hg1, decide_true, cond_true, productAtom]
    rfl
  · simp [h1, hg1]
  · simp only [h0, h1, hneg, decide_true, decide_false, cond_true, cond_false, productAtom]
    rfl
  · simp [h0, h1, hneg]

/-- **The product-definition process is computable** (`def:dedproc`), from nothing but the
two source families' own `def:ec` threshold certificates.
Paper node: `def:dedproc`, `thm:ccee` -/
lemma productDefDP_computable {X W : ℕ → LUV}
    (hX : LUV.RpnThresholdCodeSeq X) (hW : LUV.RpnThresholdCodeSeq W) :
    ComputableDeductiveProcess (productDefDP X W) := by
  have hlist : Computable (productStageList X W) := by
    have hstep : Computable fun p : ℕ × List Sentence =>
        productDefSentence X W (p.1 + 1) :: p.2 :=
      Computable.list_cons.comp
        ((productDefSentence_computable hX hW).comp
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

/-! ## Exact reflection over an extended process, process-generic form

`lic_no_expected_net_update_conditional` is deductive-process generic and consumes the
reflection slack through `slack_tendsto`, so `slack ≡ 0` is a special case and neither the
master theorem nor `ConditionalExpectationQuote` changes.  What changes is *which* process
the statement is about: `base ∪ product-definitions` rather than bare base.

That is a statement about a **different inductor**, and it is not a rendering of `thm:ccee`
— the `thm:ccee` endpoint of record is
`lic_no_expected_net_update_conditional_closed`, at the disclosed `1/(n+1)` slack over the
base `LIA`.  What the statement below is *for* is the diagnosis: it isolates the slack as an
artifact of the propositional substrate by showing that the same trader and the same
criterion give an exact conclusion the moment the product exists syntactically.  See the
obstruction-closure section further down for the full framing and its two costs. -/

/-- **Exact reflection over a definitional extension**, for a source family `X` with `def:ec`
threshold codes, over any base process extended by the product definitions.  The left quoted
product is the fresh atom family `productLUV`; every completed-theory world of the extended
process values it at exactly `x · w (f n)`, with no slack and no positivity hypothesis on
the weight.

The weight enters as in the paper (`def:pgen`): `P`-generable against the market, presented
through a LUV family `W` whose completed-world value *is* `w (f n)`.

Note `[IsLogicalInductor P (B.union (productDefDP X W))]`: the conclusion is about the
market `P` of the *extended* process.  It says nothing about a market over `B` alone —
conservativity of completed-world truth does not carry prices across.
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

/-! ## The obstruction-closure demonstration

Everything above is process-generic.  What follows discharges the four semantic premises
over a *constructed* inductor, so that the exact statement stands with no inductor, market,
presentation or `hworld` hypothesis left open.

**What this section is for, and what it is not.**  It is **not** a rendering of `thm:ccee`,
and it does not compete with `lic_no_expected_net_update_conditional_closed`, which remains
the `thm:ccee` endpoint of record at the disclosed `1/(n+1)` slack.  It is the
*obstruction-closure demonstration* for the `thm:ccee` substrate boundary: it establishes
that the mesh endpoint's slack is an artifact of the **propositional substrate**, not of
logical induction, because in any definitional extension where the quoted product exists
syntactically the theorem holds *exactly* — same trader, same criterion, `slack = 0`.  What
the paper's first-order `Θ` supplies by having a product term, this supplies by adding
fresh atoms and their defining schema to the deductive process; the mathematics of
`thm:ccee` does not notice the difference, and that is the whole content of the
demonstration.

This theorem establishes nothing about the base inductor's conditional expectations: `LIA`
over the extended process is a different inductor, and conservativity of completed-world
truth does not carry prices across.  `productDefDP_union_consistentWithTheory` shows the
extension adds no completed-world commitments in the base language; it does **not** show
that the two markets price the base language alike, and no such market-preservation
correspondence is proved anywhere in this repository.  A reader who wants a statement about
the market `liaHistory (theoremDP T)` must use the mesh endpoint.

Two further costs of the demonstration, stated plainly rather than buried:

* **Freshness is a real restriction, not a formality.**  `ProductAtomFresh X` excludes
  source families whose own threshold sentences mention the product tag, so the
  demonstration does **not** run at a genuinely arbitrary e.c. `X` the way the mesh endpoint
  does.  It is not an artifact — an adversarial `X` with `(X n).gt s = ∼productAtom n r`
  makes a stage unsatisfiable — and it is discharged by construction for every family this
  repository builds, but in the flat propositional atom space it is a genuine narrowing of
  the source class.
* **The weight needs generability at the extended market.**  `def:pgen` against
  `liaHistory (theoremDP T)` does not give `def:pgen` against the extension's market: a
  `GeneratedRatFeature`'s `denote` field is evaluated *at the history*, and the two
  histories differ.  So the demonstration carries that premise separately.  Narrowing `w`
  to `PolyRatCodes` would remove it, at the cost of dropping the paper's own worked example
  for this theorem (tex:2077) — a strictly worse trade, and not taken.

Reading this section as `thm:ccee` at an instance is therefore wrong, for exactly the
price-transport reason above; the renderings rank mesh > this > weight-narrowing, and the
framing above is the ranked one. -/

/-- Stages of the union constrain the base process in particular. -/
lemma PCWorld.consistentWithTheory_union_left {v : PCWorld} {DP extra : DeductiveProcess}
    (h : v.ConsistentWithTheory (DP.union extra)) : v.ConsistentWithTheory DP :=
  fun n => ((v.consistentWith_union_iff DP extra n).mp (h n)).1

/-- **`QuotationTheoryPresentation` lifts along a process extension.**  Every field is
either theory-side or an "enters some stage" claim, and the latter is monotone in the
process; only the stage program has to be supplied afresh for the larger process.
Paper node: `thm:ccee` -/
noncomputable def QuotationTheoryPresentation.mono {DP DP' : DeductiveProcess}
    {T : ArithmeticTheory} (Q : QuotationTheoryPresentation DP T)
    (hsub : ∀ k, DP.D k ⊆ DP'.D k) (proc : DeductiveProcessComputation DP') :
    QuotationTheoryPresentation DP' T where
  theory_deltaOne := Q.theory_deltaOne
  process := proc
  halting_enters z h := (Q.halting_enters z h).imp fun k hk => hsub k hk
  halting_refutes z h := (Q.halting_refutes z h).imp fun k hk => hsub k hk
  boundedHalting_enters z h := (Q.boundedHalting_enters z h).imp fun k hk => hsub k hk
  boundedFailure_refutes z h := (Q.boundedFailure_refutes z h).imp fun k hk => hsub k hk
  inconsistency_enters z h := (Q.inconsistency_enters z h).imp fun k hk => hsub k hk
  inconsistency_refutesConsistency z h :=
    (Q.inconsistency_refutesConsistency z h).imp fun k hk => hsub k hk
  theory_sigmaOne := Q.theory_sigmaOne
  quote_positive_enters c i h := (Q.quote_positive_enters c i h).imp fun k hk => hsub k hk
  quote_negative_refutes c i h := (Q.quote_negative_refutes c i h).imp fun k hk => hsub k hk

section ExactClosed

variable (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
variable (f : DeferralFunction) (w : ℕ → ℚ)
  (weight_mem : ∀ n, 0 ≤ w n ∧ w n ≤ 1)
  (weight_generable : PGenerableRat (liaHistory (theoremDP T)) w)

/-- The weight family of the exact route: the deferred-weight quote LUV, built against the
**base** market.  This is where the circularity of §(A2) is broken — the quote code needs
`Computable (w ∘ f)`, which `PGenerableRat.computable` supplies from a market, and the only
market available before the extended process exists is the base one.
Paper node: `thm:ccee` -/
noncomputable def exactWeightLUV : ℕ → LUV :=
  (theoremDeferredWeightQuoteCode T f w weight_generable weight_mem).luv

/-- **The definitional extension.**  The constructed provability process, extended by the
schema defining the fresh product atoms for the source family `X` and the deferred-weight
quote family.  Adding defining biconditionals for fresh atoms is a conservative
*definitional* extension; `productDefDP_union_consistentWithTheory` is that conservativity,
proved.
Paper node: `thm:ccee` -/
noncomputable def exactProductDP (X : ℕ → LUV) : DeductiveProcess :=
  (theoremDP T).union (productDefDP X (exactWeightLUV T f w weight_mem weight_generable))

lemma exactProductDP_computable {X : ℕ → LUV} (hX : LUV.RpnThresholdCodeSeq X) :
    ComputableDeductiveProcess (exactProductDP T f w weight_mem weight_generable X) :=
  DeductiveProcessComputation.union_toComputable
    (theoremDP_computable T).nonemptyComputation.some
    (productDefDP_computable hX
      (theoremDeferredWeightQuoteCode T f w weight_generable weight_mem).poly
        ).nonemptyComputation.some

/-- The extended process's own exact market program. -/
noncomputable def exactProductMarket {X : ℕ → LUV} (hX : LUV.RpnThresholdCodeSeq X) :
    MarketComputation (liaHistory (exactProductDP T f w weight_mem weight_generable X)) :=
  liaMarketComputation _ (exactProductDP_computable T f w weight_mem weight_generable hX)

/-- **`hworld` for the extension, by construction.**  The provability world of the base
process — the very world `theoremDP_hworld` exhibits — extends through the product
definitions, so the extended process is stage-wise satisfiable whenever the base one is.
No stand-in witness: the world is the base construction's own.
Paper node: `thm:ccee` -/
lemma exactProductDP_hworld {X : ℕ → LUV} (hXfresh : ProductAtomFresh X)
    (source_valued : ∀ n (v : PCWorld), v.ConsistentWithTheory (theoremDP T) →
      ∃ x, v.ValuesAt (X n) x)
    (n : ℕ) :
    ∃ v : PCWorld,
      v.ConsistentWith ((exactProductDP T f w weight_mem weight_generable X).D n) := by
  classical
  set q := theoremDeferredWeightQuoteCode T f w weight_generable weight_mem with hq
  have hbase : (provabilityWorld T).ConsistentWithTheory (theoremDP T) :=
    fun k => theoremDP_hworld T k
  exact ⟨productExtensionWorld X (exactWeightLUV T f w weight_mem weight_generable)
      (provabilityWorld T),
    productDefDP_union_consistentWithTheory hXfresh q.productAtomFresh
      (theoremDP_atomCodes_ne_productTag T) hbase
      (fun m => source_valued m _ hbase)
      (fun m => ⟨(w (f m) : ℝ),
        RationalQuoteCode.reflected (quotationPresentation T) q m _ hbase⟩) n⟩

/-- **The `thm:ccee` slack is substrate-shaped: exact reflection over a definitional
extension.**  Over the constructed provability process extended by the product definitions,
the left quoted product is the fresh atom family `productLUV`, every completed-theory world
of the extended process values it at *exactly* `x · w (f n)` — `slack = 0`, no positivity
hypothesis on the weight — and the right product is the extended market's own deferred
weighted expectation, quoted.  Same trader, same criterion, same conclusion shape as
`lic_no_expected_net_update_conditional_closed`, with the slack gone.

**This theorem establishes nothing about the base inductor's conditional expectations:
`LIA` over the extended process is a different inductor, and conservativity of
completed-world truth does not carry prices across.**  It is therefore not a replacement
for, and not a strengthening of, `lic_no_expected_net_update_conditional_closed`, which
remains the `thm:ccee` endpoint of record.  What it *does* establish is the diagnosis: the
`1/(n+1)` reflection slack the mesh endpoint carries is forced by the propositional
substrate's lack of a product term, not by anything in logical induction — give the process
a syntactic product and the theorem is exact.

Two costs of the demonstration, neither of which the mesh endpoint pays:

* `atom_fresh` — a genuine narrowing of the source class, not a formality.  No product atom
  may occur inside a source threshold sentence, so this does **not** run at the arbitrary
  e.c. `X` the mesh endpoint takes.  It is also not an artifact: an adversarial `X` with
  `(X n).gt s = ∼productAtom n r` makes a stage unsatisfiable.  In the paper the product is
  a term over a *new function symbol*, so freshness comes from the language; a flat
  propositional atom space has to state it.  Discharged by inspection for every family this
  repository builds (`arithmeticThresholdLUV_productAtomFresh`,
  `theoremDP_atomCodes_ne_productTag`).
* `weight_generable_extended` — `def:pgen` for `w` against the **extended** market, carried
  separately because a `GeneratedRatFeature`'s `denote` is evaluated at the history and the
  two histories differ.  Narrowing `w` to `PolyRatCodes` would remove it and drop the
  paper's own worked example at tex:2077; not taken.

Proof kind `C` (composition over `lic_no_expected_net_update_conditional_ofRepresentation`).
Provenance: `hworld` (a) `exactProductDP_hworld`; `source_valued` (a) transported along
`consistentWithTheory_union_left`; `left_reflected` (a) `productLUV_valuesAt_union` at zero
slack; `weight_valued` (a) `RationalQuoteCode.reflected` through the lifted presentation;
`right_reflected` (a) `MarketComputation.expectQuoteAt_cast`; `atom_fresh` and
`weight_generable_extended` (c) — modeling substitutions disclosed at the statement, in
`LogicalInduction/README.md`, and in `scripts/coverage-classification.md`.
Paper node: `thm:ccee` -/
theorem lic_no_expected_net_update_conditional_exact_productExtension
    (X : ℕ → LUV) (hX : LUV.RpnThresholdCodeSeq X)
    (source_valued : ∀ n (v : PCWorld), v.ConsistentWithTheory (theoremDP T) →
      ∃ x, v.ValuesAt (X n) x)
    (atom_fresh : ProductAtomFresh X)
    (weight_generable_extended :
      PGenerableRat (liaHistory (exactProductDP T f w weight_mem weight_generable X)) w) :
    (fun n ↦ (productLUV n).expect
        (liaHistory (exactProductDP T f w weight_mem weight_generable X)) n) ≈ₙ
      fun n ↦ ((conditionalExpectationQuoteCode T
          (exactProductMarket T f w weight_mem weight_generable hX) f X hX w
          weight_generable_extended weight_mem).luv n).expect
        (liaHistory (exactProductDP T f w weight_mem weight_generable X)) n := by
  classical
  haveI : IsLogicalInductor
      (liaHistory (exactProductDP T f w weight_mem weight_generable X))
      (exactProductDP T f w weight_mem weight_generable X) :=
    LIA_is_logical_inductor _ (exactProductDP_computable T f w weight_mem weight_generable hX)
  -- The quotation presentation, lifted from the base process to the extension.
  have hQ : QuotationTheoryPresentation
      (exactProductDP T f w weight_mem weight_generable X) T :=
    (quotationPresentation T).mono (fun _ => Finset.subset_union_left)
      (exactProductDP_computable T f w weight_mem weight_generable hX).nonemptyComputation.some
  have hweight : ∀ n (v : PCWorld),
      v.ConsistentWithTheory (exactProductDP T f w weight_mem weight_generable X) →
        v.ValuesAt (exactWeightLUV T f w weight_mem weight_generable n) (w (f n)) :=
    fun n v hv => RationalQuoteCode.reflected hQ
      (theoremDeferredWeightQuoteCode T f w weight_generable weight_mem) n v hv
  refine lic_no_expected_net_update_conditional_ofRepresentation
    (P := liaHistory (exactProductDP T f w weight_mem weight_generable X))
    (DP := exactProductDP T f w weight_mem weight_generable X)
    f X productLUV _ w weight_mem weight_generable_extended hX
    productLUV_rpnThresholdCodeSeq
    (conditionalExpectationQuoteCode T
      (exactProductMarket T f w weight_mem weight_generable hX) f X hX w
      weight_generable_extended weight_mem).poly
    (fun _ => 0) tendsto_const_nhds
    (fun n v hv => source_valued n v (PCWorld.consistentWithTheory_union_left hv))
    (fun n v hv x hx => ⟨x * (w (f n) : ℝ),
      productLUV_valuesAt_union hv n hx (hweight n v hv), by simp⟩)
    (fun n v hv => ?_)
    (exactProductDP_hworld T f w weight_mem weight_generable atom_fresh source_valued)
  have h := RationalQuoteCode.reflected hQ
    (conditionalExpectationQuoteCode T
      (exactProductMarket T f w weight_mem weight_generable hX) f X hX w
      weight_generable_extended weight_mem) n v hv
  rwa [Rat.cast_mul, ← (exactProductMarket T f w weight_mem weight_generable hX).expectQuoteAt_cast
    X n (f.f n)] at h

end ExactClosed

/-! ### Non-vacuity of the demonstration

A demonstration whose hypotheses nothing satisfies demonstrates nothing, and two of these
hypotheses — the freshness restriction and generability at the extended market — are the
substrate's cost rather than the paper's.  So the joint satisfiability of the whole premise
set is exhibited, not argued, and by an **index-varying** construction at both ends: the
weight is the harmonic sequence `1/(n+1)` (efficiently codeable, so `def:pgen` holds against
*every* market, the extended one included) and the source is that sequence's own quotation
threshold family, whose day-`n` LUV is a distinct family of atoms for each `n`. -/

/-- The harmonic weight `n ↦ 1/(n+1)`: efficiently codeable, `[0,1]`-valued, and not
eventually constant. -/
lemma harmonicWeight_polyRatCodes : PolyRatCodes (fun n : ℕ => 1 / ((n : ℚ) + 1)) := by
  refine ⟨_, ((PolyFueled.const 2).pair PolyFueled.id.succ_comp).of_eq (fun n => ?_)⟩
  have h : (1 : ℚ) / ((n : ℚ) + 1) = (((n + 1 : ℕ) : ℚ))⁻¹ := by push_cast; rw [one_div]
  show Nat.pair 2 (n + 1) = Encodable.encode ((1 : ℚ) / ((n : ℚ) + 1))
  rw [h, encode_rat_inv_natCast n.succ_pos]

lemma harmonicWeight_mem (n : ℕ) : 0 ≤ 1 / ((n : ℚ) + 1) ∧ 1 / ((n : ℚ) + 1) ≤ 1 := by
  have hpos : (0 : ℚ) < (n : ℚ) + 1 := by positivity
  exact ⟨by positivity, by rw [div_le_one hpos]; linarith [Nat.cast_nonneg (α := ℚ) n]⟩

lemma harmonicWeight_not_constant : ¬ ∀ m n : ℕ, 1 / ((m : ℚ) + 1) = 1 / ((n : ℚ) + 1) := by
  intro h
  have := h 0 1
  norm_num at this

/-- Every efficiently codeable rational sequence is `def:pgen` against **every** market,
through its constant feature. -/
lemma PGenerableRat.ofPolyRatCodes {q : ℕ → ℚ} (hq : PolyRatCodes q) (P : History) :
    PGenerableRat P q :=
  ⟨ratCodeFeature q, ratCodeFeature_generated P q hq⟩

/-- **N±.**  The obstruction-closure demonstration's whole premise set is jointly
satisfiable, by an index-varying construction rather than a stand-in witness: the `def:ec`
threshold codes, the completed-world source values, the atom-freshness restriction and
`def:pgen` at the **extended** market all hold at once, of a weight sequence that is
provably non-constant and a source family whose day-`n` LUV is a distinct atom family.  So
the demonstration is not vacuous — neither the freshness restriction nor the extended-market
generability premise empties it, and neither is jointly unsatisfiable with the paper's own
premises.

This says nothing about the base inductor either; it witnesses that
`lic_no_expected_net_update_conditional_exact_productExtension` has instances, not that its
conclusion transfers to `liaHistory (theoremDP T)`.
Paper node: `thm:ccee` -/
theorem lic_no_expected_net_update_conditional_exact_productExtension_nonvacuous
    (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1] [𝗥₀ ⪯ T]
    (f : DeferralFunction) :
    ∃ (w : ℕ → ℚ) (weight_mem : ∀ n, 0 ≤ w n ∧ w n ≤ 1)
      (weight_generable : PGenerableRat (liaHistory (theoremDP T)) w) (X : ℕ → LUV),
      ¬ (∀ m n, w m = w n) ∧
      LUV.RpnThresholdCodeSeq X ∧
      (∀ n (v : PCWorld), v.ConsistentWithTheory (theoremDP T) → ∃ x, v.ValuesAt (X n) x) ∧
      ProductAtomFresh X ∧
      PGenerableRat (liaHistory (exactProductDP T f w weight_mem weight_generable X)) w := by
  classical
  set w : ℕ → ℚ := fun n => 1 / ((n : ℚ) + 1) with hw
  have hpoly : PolyRatCodes w := harmonicWeight_polyRatCodes
  set q := RationalQuoteCode.ofComputable T hpoly.computable harmonicWeight_mem with hq
  refine ⟨w, harmonicWeight_mem, PGenerableRat.ofPolyRatCodes hpoly _, q.luv,
    harmonicWeight_not_constant, q.poly, fun n v hv => ⟨(w n : ℝ), ?_⟩,
    q.productAtomFresh, PGenerableRat.ofPolyRatCodes hpoly _⟩
  exact RationalQuoteCode.reflected (quotationPresentation T) q n v hv

#print axioms PCWorld.holds_congr_atomCodes
#print axioms productLUV_valuesAt
#print axioms productExtensionWorld_holds_schema
#print axioms productDefDP_union_consistentWithTheory
#print axioms productLUV_valuesAt_union
#print axioms productLUV_rpnThresholdCodeSeq
#print axioms productDefDP_computable
#print axioms lic_no_expected_net_update_conditional_exact
#print axioms eventAtom_atomCodes_ne_productTag
#print axioms QuotationTheoryPresentation.mono
#print axioms exactProductDP_hworld
#print axioms lic_no_expected_net_update_conditional_exact_productExtension
#print axioms lic_no_expected_net_update_conditional_exact_productExtension_nonvacuous

end LogicalInduction
