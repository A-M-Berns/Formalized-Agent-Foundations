/-
# Spike: *Communication & Trust* (Abram Demski, 16 Sep 2025) — feasibility probe.

Two things are checked here with the compiler as referee:

1. **The substrate.** §4's partition calculus (Definitions 1–6) against Mathlib's
   `Setoid`/`Setoid.classes`, including the order-convention question that bit the
   Finite Factored Sets development, and a proved characterization of the paper's
   Definition 5 (partition factorization) that its prose only asserts.

2. **A defect in Theorem 1.** Its printed conclusion is a tautology; the statement it
   *proves* is strictly stronger. Both are stated below so the gap is not a matter of
   opinion.
-/
import Mathlib

namespace CTSpike

variable {Ω : Type*}

/-! ## §4.1 — refinement, meet, join

**Finding (order convention).** Demski's Definition 1, "`X ≤ Y` iff every `x ∈ X` is a
subset of some `y ∈ Y`" (`X` refines `Y`), is *Mathlib's* `X ≤ Y` on `Setoid Ω`, and his
meet `∧` (coarsest common refinement) is Mathlib's `⊓`.

This is the **opposite** of the situation in `FiniteFactoredSets/`, where Garrabrant's
paper writes the common refinement as `⋁` and the repo carries a standing `dd:order-flip`
disclosure. Anyone porting intuitions from FFS to this paper will get it backwards.
The two lemmas below pin the alignment down mechanically. -/

/-- Definition 1, spelled out on parts, agrees with Mathlib's `≤`. -/
theorem refines_iff_le (X Y : Setoid Ω) :
    (∀ x ∈ X.classes, ∃ y ∈ Y.classes, x ⊆ y) ↔ X ≤ Y := by
  constructor
  · intro h a b hab
    obtain ⟨y, hy, hsub⟩ := h _ (X.mem_classes b)
    have ha : a ∈ y := hsub hab
    have hb : b ∈ y := hsub (X.refl' b)
    exact (Setoid.rel_iff_exists_classes Y).mpr ⟨y, hy, ha, hb⟩
  · rintro h x ⟨b, rfl⟩
    exact ⟨{a | Y a b}, Y.mem_classes b, fun a ha => h ha⟩

/-- Demski's meet `X ∧ Y` (the coarsest common refinement) is Mathlib's `X ⊓ Y`;
its parts are the nonempty intersections, exactly as Definition 3 says. -/
theorem classes_inf (X Y : Setoid Ω) :
    (X ⊓ Y).classes = {c | ∃ x ∈ X.classes, ∃ y ∈ Y.classes, c = x ∩ y ∧ (x ∩ y).Nonempty} := by
  ext c
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨{a | X a b}, X.mem_classes b, {a | Y a b}, Y.mem_classes b, rfl,
      ⟨b, X.refl' b, Y.refl' b⟩⟩
  · rintro ⟨x, ⟨bx, rfl⟩, y, ⟨by', rfl⟩, rfl, ⟨w, hwx, hwy⟩⟩
    refine ⟨w, ?_⟩
    ext a
    exact ⟨fun ⟨h1, h2⟩ => ⟨X.trans' h1 (X.symm' hwx), Y.trans' h2 (Y.symm' hwy)⟩,
           fun ⟨h1, h2⟩ => ⟨X.trans' h1 hwx, Y.trans' h2 hwy⟩⟩

/-! ## §4.2 — Definition 5, partition factorization

The paper *asserts* the relationship between factorization and the meet:

> `X = Y ∧ Z` tells us that if we know `Y` and `Z`, we have enough information to
> compute `X`; however, this does not guarantee that arbitrary `y ∈ Y` and `z ∈ Z` are
> compatible. […] "`X` factors as `(Y, Z)`" makes this further promise.

`factorsAs_iff` below turns that paragraph into a theorem. It is the cleanest working
form of Definition 5 and is what a real development should be stated over. -/

/-- **Definition 5**: `X` factors as `(Y, Z)` iff `X = {y ∩ z : y ∈ Y, z ∈ Z}`. -/
def FactorsAs (X Y Z : Setoid Ω) : Prop :=
  X.classes = {c | ∃ y ∈ Y.classes, ∃ z ∈ Z.classes, c = y ∩ z}

/-- Definition 5's own parenthetical — "this implies `y ∩ z` is nonempty for all
`y ∈ Y, z ∈ Z`" — is correct, and the reason is that partition parts are nonempty. -/
theorem FactorsAs.nonempty_inter {X Y Z : Setoid Ω} (h : FactorsAs X Y Z)
    {y z : Set Ω} (hy : y ∈ Y.classes) (hz : z ∈ Z.classes) : (y ∩ z).Nonempty := by
  have : y ∩ z ∈ X.classes := h ▸ ⟨y, hy, z, hz, rfl⟩
  rcases Set.eq_empty_or_nonempty (y ∩ z) with he | hne
  · exact absurd (he ▸ this) Setoid.empty_notMem_classes
  · exact hne

/-- **The characterization.**  Factoring is exactly "the meet, *plus* total pairwise
compatibility of the factors' parts". -/
theorem factorsAs_iff (X Y Z : Setoid Ω) :
    FactorsAs X Y Z ↔
      X = Y ⊓ Z ∧ ∀ y ∈ Y.classes, ∀ z ∈ Z.classes, (y ∩ z).Nonempty := by
  constructor
  · intro h
    refine ⟨Setoid.classes_inj.mpr ?_, fun y hy z hz => h.nonempty_inter hy hz⟩
    rw [h, classes_inf]
    ext c
    exact ⟨fun ⟨y, hy, z, hz, hc⟩ => ⟨y, hy, z, hz, hc, hc ▸ h.nonempty_inter hy hz⟩,
           fun ⟨y, hy, z, hz, hc, _⟩ => ⟨y, hy, z, hz, hc⟩⟩
  · rintro ⟨rfl, hcompat⟩
    rw [FactorsAs, classes_inf]
    ext c
    exact ⟨fun ⟨y, hy, z, hz, hc, _⟩ => ⟨y, hy, z, hz, hc⟩,
           fun ⟨y, hy, z, hz, hc⟩ => ⟨y, hy, z, hz, hc, hcompat y hy z hz⟩⟩

/-- Definition 4 (restriction map), for the record.  Note the paper immediately uses it
at a type it does not fit — Definition 5's `m : Y × Z → X` has a *product* domain, not a
partition — so "restriction map" is being used in two senses. -/
def IsRestrictionMap (X Y : Setoid Ω) (f : X.classes → Y.classes) : Prop :=
  ∀ x : X.classes, (f x : Set Ω) ⊆ (x : Set Ω)

/-! ## §7 — the defect in Theorem 1

Theorem 1 concludes, verbatim:

>  `m(Π*(ȯö,ö) = aö) > min_{a'ö ∈ Aö} m(Π*(ȯö,ö) = a'ö)`
>  `⟹  E[U | Π*(ȯö,ö) = aö] ≤ max_{a'ö ∈ Aö} E[U | Π*(ȯö,ö) = a'ö]`

Since `aö ∈ Aö`, the consequent is a tautology: it holds with no hypotheses at all, for
any real-valued function whatsoever.  `printed_conclusion_is_vacuous` below is that
observation, and it takes none of the paper's three conditions as input. -/

section Vacuity
variable {A : Type*} [Fintype A] [Nonempty A] [DecidableEq A]

/-- Theorem 1's printed conclusion, with *no* hypotheses. -/
theorem printed_conclusion_is_vacuous (E : A → ℝ) (a : A) :
    E a ≤ Finset.univ.sup' Finset.univ_nonempty E :=
  Finset.le_sup' E (Finset.mem_univ a)

/-- Definition 17: `a` is minimally modifying. -/
def MinModifying (m : A → ℝ) (a : A) : Prop := ∀ b, m a ≤ m b

/-- What Theorem 1's *proof* actually establishes: a non-minimally-modifying action is
dominated by *some minimally modifying* action — namely its communicative alternative
`ca a`, which Definition 18(1) guarantees is minimally modifying.  Restricting the
comparison class is exactly what the printed `max_{a' ∈ Aö}` drops. -/
def IntendedConclusion (m E : A → ℝ) : Prop :=
  ∀ a : A, ¬ MinModifying m a → ∃ a', MinModifying m a' ∧ E a ≤ E a'

/-- And the intended conclusion really is stronger: unlike the printed one, it is not a
tautology.  Witness: two actions, the modifying one strictly better. -/
example : ¬ ∀ m E : Bool → ℝ, IntendedConclusion m E := by
  intro h
  obtain ⟨a', hmin, hle⟩ :=
    h (fun b => if b then 1 else 0) (fun b => if b then 1 else 0) true
      (by intro hm; have := hm false; norm_num at this)
  have : a' = false := by
    by_contra hne
    have ha' : a' = true := by cases a' <;> simp_all
    have := hmin false
    rw [ha'] at this
    norm_num at this
  rw [this] at hle
  norm_num at hle

end Vacuity

end CTSpike

/-! ## Axiom audit for the spike surface -/

section Audit
#print axioms CTSpike.refines_iff_le
#print axioms CTSpike.classes_inf
#print axioms CTSpike.FactorsAs.nonempty_inter
#print axioms CTSpike.factorsAs_iff
#print axioms CTSpike.printed_conclusion_is_vacuous
end Audit
