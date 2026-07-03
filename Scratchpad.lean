/-
# Scratchpad — substrate verification (M0)

NOT part of the formalization. This file exists to answer two M0 questions against the
*actually installed* packages, with the compiler as referee:

  1. Does the Mathlib machinery we depend on (limits/asymptotics, Bochner integration,
     compact-convex topology, and Brouwer) exist and import cleanly?
  2. What does Foundation actually give us for `def:lang` / `def:ec` — in particular, a
     *computable encoding* of propositional sentences, plus `⊢` and consistency?

Findings are recorded inline and summarized in `PROGRESS.md`. It is kept green as a
standing regression guard for the substrate (see the Bochner section: the co-import it
checks is exactly the one OPEN RISK 1 was about).

✅ RESOLVED (was HEADLINE FINDING, M0): `Foundation.Vorspiel.Matrix` used to define its
own `Matrix.map : (Fin k → α) → (Fin k → β)`, shadowing Mathlib's `Matrix.map`; both
generated `Matrix.map.eq_1`, so Foundation could not be imported alongside any Mathlib
module that materialized it (Bochner integration, matrix-heavy analysis). Fixed by
pinning the fork `A-M-Berns/Foundation@0939b51`, which renames the def to
`Matrix.vecMap` (one-file change; notation `⨟` and lemmas unchanged). The Bochner
import below is the live proof that the clash is gone. Discipline note kept: still never
`import Mathlib` (umbrella) alongside Foundation in Parts I–III files — use targeted
imports. (`Construction/Brouwer.lean` is the one disclosed exception; it imports no
Foundation and predates its import trim.)
-/
import Mathlib.Analysis.SpecificLimits.Basic        -- Tendsto, atTop, nhds, Eventually
import Mathlib.Analysis.Convex.Basic                -- Convex
import Mathlib.Topology.Compactness.Compact         -- IsCompact
import Mathlib.Topology.ContinuousMap.Basic         -- ContinuousMap
import Mathlib.MeasureTheory.Integral.Bochner.Basic -- ✓ co-imports since the fork (OPEN RISK 1 resolved)
import Foundation.Propositional.Logic.Basic
import Foundation.Propositional.Hilbert.Minimal.Basic  -- the classical system `Hilbert.Cl`
import Foundation.Logic.Entailment

namespace LogicalInduction.Scratchpad

/-! ## 1. Mathlib substrate -/

section Mathlib

-- Asymptotics vocabulary (`dd:asymp`): `Tendsto (·−·) atTop (𝓝 0)` and `∀ᶠ n in atTop`.
-- Now packaged once in `LogicalInduction.Asymptotics` (`≈ₙ`, `≲ₙ`, `≳ₙ`, …).
#check @Filter.Tendsto
#check (Filter.atTop : Filter ℕ)
#check @nhds
#check @Filter.Eventually
example : Prop := ∀ᶠ n in Filter.atTop, (0 : ℝ) ≤ n  -- the eventually-idiom elaborates

-- Bochner integral, for the LUV expectation bridge (`lem:limexpapprox`). The audit rule
-- says expectations route through `MeasureTheory.integral`, not hand-computation. This
-- `#check`, co-resident with the Foundation imports above, is the standing regression
-- guard that OPEN RISK 1 stays resolved across Foundation/Mathlib pin bumps.
#check @MeasureTheory.integral

-- Compact-convex topology, the home of the price-adjustment fixed point (`lem:fpl`).
#check @IsCompact
#check @Convex

-- ✅ Brouwer (was OPEN RISK 2): the installed Mathlib still has NO Brouwer (or
-- Schauder/Kakutani) fixed-point theorem — only Brouwerian/Heyting *algebras* and
-- Riesz–Markov–Kakutani (a measure theorem). Resolved in-project instead:
-- `LogicalInduction.Construction.Brouwer` now PROVES `brouwer_fixed_point` from scratch
-- (Sperner/Kuhn), axioms = [propext, Classical.choice, Quot.sound]. Not imported here
-- (it is heavy); see that file.
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
## Verdict (M0, updated at M0 close-out)

* Mathlib + Foundation co-build under `leanprover/lean4:v4.28.0-rc1`, **including Bochner
  integration** (the import above) — the full-stack co-build is verified, not assumed.
* `def:lang` is well-served: `Formula ℕ` + `Encodable` + `DecidableEq` + `LO.Entailment`
  (`⊢`/`⊬`/`Consistent`) + `Hilbert.Cl`. The computable-encoding worry for `def:ec` is
  resolved in our favor — wrap these behind `LogicalInduction.Sentence`.
* ✅ OPEN RISK 1 resolved via the Foundation fork (`Matrix.map` → `Matrix.vecMap`).
* ✅ OPEN RISK 2 resolved in-project: `brouwer_fixed_point` proved (Sperner/Kuhn route,
  autoformalized by Aristotle, revalidated on this toolchain) in
  `LogicalInduction/Construction/Brouwer.lean`. Upstreaming to Mathlib remains desirable
  but no longer gates M6.
-/

end LogicalInduction.Scratchpad
