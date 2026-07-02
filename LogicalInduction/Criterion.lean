/-
# Part I — Criterion (`LogicalInduction.Criterion`)

The expressible-feature DSL keystone, traders, and the Logical Induction Criterion. The
DSL is the keystone — invest disproportionately and add non-vacuity examples. Nodes
hosted here (see roadmap §3, Part I):

* `def:tf` (keystone) → `EF`, `EF.denote`, `EF.cost`, `instCommRing EF_n`. An inductive
  syntax over price features `pf φ`, `ℚ`, `+`, `×`, `max(·,·)`, safe reciprocation
  `max(1,·)⁻¹`, with two semantics:
    - `EF.denote : EF → (History → ℝ)` — continuous ℝ-valued; feeds Brouwer.
    - `EF.cost   : EF → ℕ` — syntactic size; certifies efficient computability in the
      construction **and in every property proof's exploiting trader**.
  `EF_n` (rank ≤ `n`) is a commutative ring. The continuity of `denote` is *stated* here;
  its proof may defer.
* `def:valfeature` → `ValuationFeature` — semantic target `EF.denote` lands in.
* `def:tradestrat` → `TradingStrategy` — affine combo `cash + Σ ef_i · φ_i`.
* `def:trader`     → `Trader` — sequence of `n`-strategies.
* `def:exploitation` → `Exploits` — plausible-world values bounded below, `sup = +∞`.
* `def:lic`        → `IsLogicalInductor` — "no e.c. trader exploits the market." The
  hypothesis the entire property tail is conditioned on.

TODO(blueprint:def:tf): inductive `EF`, `EF.denote`, `EF.cost`, `CommRing EF_n`, and the
  statement of `EF.denote` continuity. Add ≥2 concrete `EF` examples as non-vacuity
  witnesses.
-/

namespace LogicalInduction

end LogicalInduction
