# Foundation Survey for Critch Setup

Foundation commit surveyed: `c28942b7d9d0df41ee5b736602c3f27b8643532c`.

## Provability abstraction

`Foundation/FirstOrder/Incompleteness/ProvabilityAbstraction/Basic.lean` defines
the abstract provability interface in namespace
`LO.FirstOrder.ProvabilityAbstraction`.

The core signature is:

```lean
abbrev Language.ReferenceableBy (L L₀ : Language) :=
  Semiterm.Operator.GödelNumber L₀ (Sentence L)

structure Provability [L.ReferenceableBy L₀] (T₀ : Theory L₀) (T : Theory L) where
  prov : Semisentence L₀ 1
  bew_def {σ : Sentence L} : T ⊢ σ → T₀ ⊢ prov/[⌜σ⌝]
```

`Provability.pr` gives the coercion `𝔅 σ : Sentence L₀`. The HBL classes are:

```lean
class HBL2 (𝔅 : Provability T₀ T) where
  D2 {σ τ : Sentence L} : T₀ ⊢ 𝔅 (σ 🡒 τ) 🡒 𝔅 σ 🡒 𝔅 τ

class HBL3 (𝔅 : Provability T₀ T) where
  D3 {σ : Sentence L} : T₀ ⊢ 𝔅 σ 🡒 𝔅 (𝔅 σ)

class HBL extends 𝔅.HBL2, 𝔅.HBL3
```

There are also `Mono`, `Ext`, `Rosser`, formalized completeness, Kreisel, and
soundness classes. `Diagonalization` is a separate class with:

```lean
class Diagonalization [L.ReferenceableBy L] (T : Theory L) where
  fixedpoint : Semisentence L 1 → Sentence L
  diag (θ : Semisentence L 1) : T ⊢ fixedpoint θ 🡘 θ/[⌜fixedpoint θ⌝]
```

`löb_theorem` is generic over a `Provability T T`, an HBL instance, and a
diagonalization instance. The Critch `BoundedProvability` interface should keep
the same separation: a small structure containing the predicate, typeclasses for
bounded D1/D2/D3-like assumptions, and diagonalization supplied separately.

## Restricted provability

`Foundation/FirstOrder/Incompleteness/RestrictedProvability.lean` defines:

```lean
def RestrictedProvable (e : ℕ) (T : Theory L) [T.Δ₁] (φ : V) :=
  ∃ d < Exp.exp (ORingStructure.numeral e), T.Proof d φ

noncomputable def restrictedProvable (e : ℕ) : 𝚷₁.Semisentence 1 :=
  .mkPi “φ. ∀ E, !expDef E !e → ∃ d < E, !T.proof.pi d φ”
```

The corresponding sentence-level abbreviation is:

```lean
noncomputable abbrev restrictedProvabilityPred (e : ℕ) (σ : Sentence L) :
    ArithmeticSentence :=
  (T.restrictedProvable e).val/[⌜σ⌝]
```

I did not find a packaged monotonicity lemma of the form
`e ≤ e' → T.RestrictedProvable e φ → T.RestrictedProvable e' φ`, nor a theorem-level
version for `restrictedProvabilityPred`. The file imports exponential monotonicity,
and `Exp.exp` has `exp_monotone_le`, so the semantic monotonicity proof should be
straightforward. The internalized/provable version still needs to be added for
Layer B if monotonicity is part of the bounded interface.

The current scaffold packages `T.restrictedProvable e` as a `BoundedProvability`
predicate but does not provide bounded HBL instances.

## Standard provability instance pattern

`Foundation/FirstOrder/Incompleteness/StandardProvability.lean` is the model for
Layer B. It builds:

```lean
noncomputable abbrev Theory.standardProvability : Provability 𝗜𝚺₁ T where
  prov := T.provable
  bew_def := provable_D1
```

Then it separately registers HBL2, HBL3, and HBL instances from the bootstrapped
D1/D2/D3 files. Layer B should follow this shape: first define the bounded
predicate wrapper, then add bounded D1/D2/D3 instances in separate files.

## Parametric diagonalization

The plan expected Critch's Proposition 1 to require a new parametric diagonal
construction. On the pinned Foundation commit, this is already present:

```lean
noncomputable def parameterizedFixedpoint
    (θ : Semisentence ℒₒᵣ (k + 1)) : Semisentence ℒₒᵣ k

theorem parameterized_diagonal
    (θ : Semisentence ℒₒᵣ (k + 1)) :
  T ⊢ ∀⁰* (parameterizedFixedpoint θ 🡘
    “!θ !!(⌜parameterizedFixedpoint θ⌝) ⋯”)
```

There is also a one-parameter specialization `parameterized_diagonal₁`. This is
not the same as `multidiagonal`: `multidiagonal` produces mutually fixed
sentences, while `parameterized_diagonal` produces a formula with `k` remaining
free variables. This appears to match Critch Proposition 4.3 directly, modulo
adapting the object language and notation.

## Proof encoding and MP/cut bounds

`Foundation/FirstOrder/Bootstrapping/Syntax/Proof/Basic.lean` represents proofs
as encoded derivation trees. The relevant definitions are:

```lean
def DerivationOf (d s : V) : Prop := fstIdx d = s ∧ T.Derivation d
def Proof (d φ : V) : Prop := T.DerivationOf d {φ}
def Provable (φ : V) : Prop := ∃ d, T.Proof d φ
```

The inference corresponding to modus ponens is a sequent `cutRule`:

```lean
noncomputable def cutRule (s p d₁ d₂ : V) : V :=
  ⟪s, 8, p, d₁, d₂⟫ + 1
```

Foundation proves component lower bounds such as `d₁_lt_cutRule` and
`d₂_lt_cutRule`, and `Theory.Derivable.cut` constructs a derivation using this
constructor.

The pairing function is explicit:

```lean
c = ⟪a, b⟫ ↔ (a < b ∧ c = b * b + a) ∨
              (b ≤ a ∧ c = a * a + a + b)
```

It has monotonicity and boundedness instances, so the encoding is not hostile.
However, I did not find a ready-made upper bound lemma for
`cutRule s p d₁ d₂` in terms of only `d₁` and `d₂`.

A clean Layer B bound should be derivable but is not packaged. The likely route is:

1. Use `DerivationOf d₁ (insert p s)` and `DerivationOf d₂ (insert (neg L p) s)`
   to bound the sequent/formula side data by the proof codes.
2. Use monotonicity and the polynomial shape of nested pairing to bound
   `⟪s, 8, p, d₁, d₂⟫ + 1` by a fixed polynomial in `max d₁ d₂`.
3. Translate a polynomial bound on proof Gödel numbers into an additive or linear
   overhead in the exponent `e` because `RestrictedProvable e` means proof code
   `< 2^e`.

This makes Phase 6 feasible in principle, but it is a real proof-engineering task,
not an already-available Foundation lemma.
