/-
# Scratchpad — substrate verification (M0)

NOT part of the formalization. This file exists to answer two M0 questions against the
*actually installed* packages, with the compiler as referee:

  1. Does the Mathlib machinery we depend on (limits/asymptotics, Bochner integration,
     compact-convex topology, and Brouwer) exist and import cleanly?
  2. What does Foundation actually give us for `def:lang` / `def:ec` — in particular, a
     *computable encoding* of propositional sentences, plus `⊢` and consistency?

Findings are recorded inline and summarized in `PROGRESS.md`. Delete this file once its
conclusions are absorbed into the real modules.

⚠ HEADLINE FINDING (M0) — a scoped Foundation/Mathlib co-import conflict:

  `Foundation.Vorspiel.Matrix` (line 245) defines its own `Matrix.map`
  `(f : α → β) : (Fin k → α) → (Fin k → β)` — a *vector* map that shadows Mathlib's
  `Matrix.map`. Both auto-generate `Matrix.map.eq_1`, so importing Foundation together
  with any Mathlib module that materializes Mathlib's `Matrix.map.eq_1` fails with:
    `import Foundation.Vorspiel.Matrix failed, environment already contains
     'Matrix.map.eq_1' from Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber`
  Because `Vorspiel.Matrix` sits in Foundation's prelude (`Vorspiel.List.Basic` →
  `Vorspiel.Matrix`), *every* Foundation module is affected.

  Empirically the boundary is:
    Foundation + filters / topology / `Analysis.SpecificLimits` / Convex / Compact /
      ContinuousMap                                            → ✓ co-build
    Foundation + Bochner integration (`MeasureTheory.integral`) → ✗ clash
  i.e. the conflict spares the convergence/coherence/probability tail but bites the
  **LUV expectation bridge (M3+)** and, almost certainly, the **finite-dimensional
  analysis behind Brouwer (M6)**.

  RECOMMENDED FIX (cheap, needs Anson's ok — it edits a pinned dep): fork the Foundation
  pin and rename `Foundation.Vorspiel.Matrix.map` out of the `Matrix` namespace (e.g.
  `vecMap`), fixing the `⨟` notation. There are 0 qualified `Matrix.map` usages, so this
  is a one-file change. Do this before M3.

Until then: targeted Mathlib imports only, and no Bochner alongside Foundation (below).
-/
import Mathlib.Analysis.SpecificLimits.Basic        -- Tendsto, atTop, nhds, Eventually
import Mathlib.Analysis.Convex.Basic                -- Convex
import Mathlib.Topology.Compactness.Compact         -- IsCompact
import Mathlib.Topology.ContinuousMap.Basic         -- ContinuousMap
-- import Mathlib.MeasureTheory.Integral.Bochner.Basic  -- ✗ clashes (see HEADLINE FINDING)
import Foundation.Propositional.Logic.Basic
import Foundation.Propositional.Hilbert.Minimal.Basic  -- the classical system `Hilbert.Cl`
import Foundation.Logic.Entailment

namespace LogicalInduction.Scratchpad

/-! ## 1. Mathlib substrate -/

section Mathlib

-- Asymptotics vocabulary (`dd:asymp`): `Tendsto (·−·) atTop (𝓝 0)` and `∀ᶠ n in atTop`.
#check @Filter.Tendsto
#check (Filter.atTop : Filter ℕ)
#check @nhds
#check @Filter.Eventually
example : Prop := ∀ᶠ n in Filter.atTop, (0 : ℝ) ≤ n  -- the eventually-idiom elaborates

-- Bochner integral, for the LUV expectation bridge (`lem:limexpapprox`). The audit rule
-- says expectations route through `MeasureTheory.integral`, not hand-computation. The
-- def is confirmed present at `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`, but
-- CANNOT be imported alongside Foundation until the `Vorspiel.Matrix` clash above is
-- fixed — hence it is not `#check`ed here. This is the M3 blocker to resolve first.

-- Compact-convex topology, the home of the price-adjustment fixed point (`lem:fpl`).
#check @IsCompact
#check @Convex

-- ⚠ Brouwer: `exact?`/grep find NO Brouwer (or Schauder/Kakutani) fixed-point theorem in
-- the installed Mathlib — only Brouwerian/Heyting *algebras* and Riesz–Markov–Kakutani
-- (a measure theorem). So the roadmap's "use Mathlib's Brouwer" is currently false.
-- Intentionally left unimported; M6 is gated on resolving this. Sanity check that the
-- relevant ambient API (continuous self-maps of a convex compact) at least exists:
#check @ContinuousMap

end Mathlib

/-! ## 2. Foundation substrate (`def:lang` / `def:ec`) -/

section Foundation

open LO LO.Propositional

-- The propositional sentence type. Atoms over `ℕ` give us a concrete, countable language.
#check @Formula              -- LO.Propositional.Formula : Type u → Type u
example : Type := Formula ℕ

-- KEYSTONE ANSWER for `def:ec`: sentences are *computably encodable*. Foundation ships
-- `instance : Encodable (Formula α)` (a `toNat`/`pair` coding) for `[Encodable α]`, and
-- `DecidableEq` is derived. So a clocked interpreter (`dd:fuel`) can read sentence codes
-- off `ℕ` — we do NOT need to build our own Gödel numbering.
example : Encodable (Formula ℕ) := inferInstance
example : DecidableEq (Formula ℕ) := inferInstance

-- Derivability and consistency come from the generic `LO.Entailment` layer:
--   `𝓢 ⊢ φ`  provable,  `𝓢 ⊬ φ`  unprovable,  `Consistent 𝓢`  not-inconsistent.
#check @LO.Entailment.Provable
#check @LO.Entailment.Consistent

-- Classical propositional logic is `Hilbert.Cl` (a deductive system) / `Cl` (its logic).
-- This is the propositional-consistency notion `def:world` / `def:worlds` will use.
#check @LO.Propositional.Hilbert.Cl

end Foundation

/-
## Verdict (M0)

* Mathlib + Foundation co-build under `leanprover/lean4:v4.28.0-rc1`; both are
  precompiled (Foundation already `require`s mathlib).
* `def:lang` is well-served: `Formula ℕ` + `Encodable` + `DecidableEq` + `LO.Entailment`
  (`⊢`/`⊬`/`Consistent`) + `Hilbert.Cl`. The computable-encoding worry for `def:ec` is
  resolved in our favor — wrap these behind `LogicalInduction.Sentence`.
* OPEN RISK 1 (M3): the Foundation `Vorspiel.Matrix.map` clash blocks Bochner
  integration alongside Foundation. Fix by renaming in a Foundation fork (one file) before
  the expectation bridge. See HEADLINE FINDING at the top.
* OPEN RISK 2 (M6): no Brouwer/Kakutani fixed point in Mathlib — must contribute it
  upstream or find an alternate route. The single biggest schedule risk. (Brouwer's
  finite-dimensional analysis will also re-trigger OPEN RISK 1, so fix that first.)
-/

end LogicalInduction.Scratchpad
