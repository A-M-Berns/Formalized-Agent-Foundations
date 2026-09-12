# Tranche E design note — program games, instructions, and the hooks for participation / foreknowledge independence

**Status:** design for review (2026-09-12). No Lean yet. Follows RULING 3 (concrete program
language with private seeds and classical code equality) and RULING 9 (participation
independence and foreknowledge independence must be *stateable*). Everything the 2022
paper needs is in §1–§3; §4 is what RULING 9 adds, and it is marked as substrate beyond the
paper wherever that is so.

## 0. What the paper gives us (Appendix A)

A *program game* for `Γ = (A, u)` is a set `PROG = PROG₁ × ⋯ × PROGₙ` and a
non-deterministic map `exec : PROG ⇝ A`; the induced game has action sets `PROGᵢ` and
utilities `U(c) = E[u(exec(c))]`. A *program equilibrium* is a Nash equilibrium of that
game. The language is left unspecified beyond three features Algorithm 2 uses: compare
the whole profile of submitted code with one's own, play a fixed (mixed) action, and call
the black box `Πᵢ(Γ′)` for a subset game `Γ′`. Proposition 18: with Algorithm 2 submitted
by everyone and `Π(Γ)` guaranteeing each player their threat point in expectation, the
profile is a program equilibrium with `exec = Π(Γˢ)`. Theorem 1 follows.

Two things the paper does not say and we must (erratum D8): where the randomness of
`exec` comes from (Algorithm 2's punishment is a *mixed* strategy, and the threat-point
bound needs the deviator's realized action independent of the punishers' draws), and that
the deviator's payoff is *at most* the threat point, not equal to it.

## 1. The abstract interface: `ProgramGame`

Following the repo's implementation-independence rule (abstract interface first, our
realization as a separate theorem):

```
structure ProgramGame (Γ₀ : Game N 𝒜) (X : Play N 𝒜 Ω) where
  Instr : N → Type                          -- PROGᵢ
  Σ : N → Type                              -- private seed of player i's execution
  [mΣ : ∀ i, MeasurableSpace (Σ i)] (ν : ∀ i, Measure (Σ i)) [∀ i, IsProbabilityMeasure (ν i)]
  exec : (∀ i, Instr i) → Ω → (∀ i, Σ i) → (∀ i, 𝒜 i)   -- everybody's code, Π's sample point, the seeds
  exec_mem : ∀ c ω σ, exec c ω σ ∈ Γ₀.profiles
  exec_local : ∀ c ω σ σ' i, (∀ j, j ≠ i → …) → …      -- see §1.2
```

- **One sample space for `Π`, one private seed per player.** `exec` reads `Ω` (so that a
  `Πᵢ(Γ′)` call is the *same* random variable the rest of the paper talks about — this
  is what makes `exec(c) = Π(Γˢ)` a statement about `Π`) and a product of private seeds
  (so that mixed-strategy instructions can be executed with randomness the other programs
  cannot see). `dd:exec-seeds`.
- **The induced game is an EconCSLib `StrategicGame`**: `strategy i := Instr i`,
  `payoff c i := ∫ u(exec c ω σ) i d(μ ⊗ ν)`. A program equilibrium is literally
  EconCSLib's `IsNashEquilibrium` of that game — the second place the dependency carries
  weight, and the reason to build on it rather than redefine Nash.
- **Locality (`exec_local`)**: player `i`'s realized action depends on the seeds only
  through `σ i` (each program reads its own seed). This is the axiom that makes the
  independence argument in Proposition 18 go through; it is stated on the interface so a
  reader can see exactly what the equilibrium proof consumes.

`ProgramGame.threatPoint i` (the paper's `vᵢ`): `min` over `σ₋ᵢ ∈ ×ⱼ≠ᵢ Δ(Aⱼ)` of `max` over
`σᵢ ∈ Δ(Aᵢ)` of expected `uᵢ` — independent mixtures, existence by compactness of the
product of standard simplices and continuity of the multilinear payoff (Mathlib), *not* by
LP; EconCSLib's two-player matrix minimax is used only to instantiate the paper's remark
that for `n = 2` the threat point is the maximin value. `minimax i j : Δ(Aⱼ)` is a chosen
minimizer, fixed by `Classical.choice` consistently across players as the paper stipulates.

## 2. The concrete language: `Prog`

A minimal inductive syntax closed under Algorithm 2's three instructions:

```
inductive Prog (Γ₀ : Game N 𝒜)
  | play (σ : ∀ i, Δ(Γ₀.S i))                   -- play a mixed action (own coordinate, by own seed)
  | delegate (Γ′ : Game N 𝒜) (h : Γ′.IsSubsetGameOf Γ₀)   -- "play Πᵢ(Γ′)"
  | ifAllSame (then_ : Prog) (punish : N → Prog)   -- if every other code equals mine, then_, else punish j for the first j whose code differs
```

- **Same code for everyone.** A `Prog` is player-agnostic; the player index is a runtime
  input to `exec`, as the paper does it so that Algorithm 2 can be submitted verbatim by
  every player and `cⱼ ≠ cᵢ` is a comparison of identical syntax.
- **Code equality is classical.** `Prog` contains real payoffs (through the embedded
  subset games) so `DecidableEq Prog` is `Classical.dec`; the meta-game is a mathematical
  object, exactly as the paper's Lisp-with-real-payoffs is. `dd:code-eq`.
- **`exec` by structural recursion** on `cᵢ` with the full profile `c` in scope:
  `play σ ↦ σ i` sampled from seed `σ i`; `delegate Γ′ ↦ X.play Γ′ ω i`;
  `ifAllSame t p ↦ if ∀ j ≠ i, c j = c i then exec t else exec (p j₀)` with `j₀` the least
  differing index (any fixed choice; the paper's loop picks the first).
- **Realization theorem**: `Prog` with this `exec` is a `ProgramGame` (locality holds by
  construction). Proposition 18 is proved once over the interface and instantiated here.

Algorithm 2 is then the term
`ifAllSame (delegate Γˢ) (fun j => play (minimax i j))` — with the caveat that
`minimax i j` depends on `i`, so the "same code" reading needs the punishment to be
indexed by the runtime player: store `punish : N → N → Δ` and let `exec` apply it at
`(i, j)`. That is the one place the syntax has to know it will be run by different
players; the note flags it because it is where "identical source code" is easiest to
get subtly wrong.

**Proposition 18 (corrected, D8):** if `Π(Γ)` guarantees every player at least `vᵢ` in
expectation and `Γˢ` is an SPI on `Γ`, then the Algorithm-2 profile is a program
equilibrium and its execution is `Π(Γˢ)` at every sample point. The deviation case:
`E[uᵢ(exec(c₋ᵢ, c′ᵢ))] ≤ vᵢ`, because the others play the fixed product mixture
`minimax i ·` from their own seeds and `i`'s action is independent of those seeds by
locality, so `i`'s expected payoff is at most the max over `i`'s mixtures against that
product, i.e. `vᵢ`. **Theorem 1** is the existential wrapper.

## 3. What Theorem 1 needs from the rest of the library

`Play.IsSPI` (Definition 1) at `L = ae μ`; `Representatives` for the expectations
(`exec` payoffs are integrals over `μ ⊗ ν`, so the program game lives at the
probabilistic instance, not the filter level — Theorem 1 is the one node stated for
`Representatives` rather than `Play`); the finite-support integration lemmas that §5 will
also use (`u ∘ exec` is a simple function). No new paper-facing definitions.

## 4. Hooks for participation and foreknowledge independence (beyond the paper; RULING 9)

The CLR agenda's notions, informally: an agent satisfies **participation independence
(PI)** if its bargaining demands are the same as they would have been had the counterpart
not participated in the SPI; **foreknowledge independence (FI)** if its demands are the
same as they would have been had it known in advance that the counterpart would not
participate. Both are properties of *instructions*, compared across counterfactual
instruction profiles, and FI additionally needs an information stage. The design makes
each of the three ingredients a first-class object, without asserting any theorem about
them (those belong to the later papers):

1. **A default (non-participation) instruction.** `ProgramGame.default : ∀ i, Instr i`
   with the semantic axiom `exec default ω σ = X.play Γ₀ ω` (everybody delegating the
   original game *is* the paper's default). In `Prog`: `default := delegate Γ₀`. "Player `j`
   did not participate" is then the profile `c[j := default j]`. `dd:default-instr`.

2. **Demands as a projection of instructions.** A `Demand` interface:
   `demand : Instr i → Ω → Σ i → Option (𝒜 i)` — what the instruction commits its player to
   *in the base game* when the SPI is not in force (for Algorithm 2: the punishment; for a
   PI-respecting instruction: the default). With it, **PI is stateable**:
   `PI c i := ∀ j ≠ i, ∀ ω σ, exec (c[j := default j]) ω σ i = exec (default) ω σ i` —
   when `j` drops out, `i` behaves exactly as under its own default. Algorithm 2 provably
   *fails* PI (it punishes); the "dove-ish" instruction of §6 (comply with any SPI that
   cannot be further safely improved, otherwise default) satisfies it. Both are good
   non-vacuity witnesses for the definition and are cheap once the layer exists.

3. **An information stage for FI.** Instructions chosen *as a function of a signal*:
   `Signal i : Type` with a distinguished value `willNotParticipate j` for each counterpart,
   and `policy : Signal i → Instr i`. **FI is stateable** as: the demand under
   `policy (noInfo)` when `j` in fact drops out equals the demand under
   `policy (willNotParticipate j)` — the agent would have demanded the same had it known.
   This is a two-stage object the 2022 paper has no counterpart for; it is added as
   substrate, disclosed as such, and carries no `Paper node`.

What is deliberately *not* built: any bargaining-solution structure, any claim that PI or
FI hold of a particular SPI scheme (those are research results for later formalizations),
and any change to the paper-facing definitions of §3–§5.

## 5. Tranche plan

E1. `ProgramGame` interface, threat point, induced `StrategicGame`, program equilibrium =
    EconCSLib Nash; the corrected Proposition 18 over the interface (`dd:exec-seeds`, D8).
E2. `Prog`, its `exec`, the realization theorem; Algorithm 2 as a term; Theorem 1.
E3. `default`, `Demand`, `Signal`/`policy`; the PI and FI *definitions* with the two
    Algorithm-2 / dove-ish witnesses. No theorems beyond non-vacuity.

Effort: E1 ≈ 0.15 FFS (compactness argument for the threat point is the only real proof),
E2 ≈ 0.2 FFS (the independence bookkeeping in Proposition 18), E3 ≈ 0.1 FFS. Rulings
needed before Lean: none beyond confirming this note; the two design tags
`dd:exec-seeds` and `dd:code-eq` will be added to the glossary when E1 lands.
