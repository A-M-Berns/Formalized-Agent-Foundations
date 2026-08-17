# Spike: how hard is *A Theory of Bounded Inductive Rationality* (arXiv:2307.05068)?

Caspar Oesterheld, Abram Demski, Vincent Conitzer, TARK 2023 (EPTCS 379, pp. 421–440).

Feasibility / representation probe. Not a formalization, not registered in
`scripts/papers.py`, not on the trust surface, not in `AxiomAudit`.

Compiled artifact: `BoundedInductiveRationality/Spike.lean` — 1434 lines, 98 top-level declarations, **zero
`sorry`**, every listed endpoint axiom-clean (`propext`, `Classical.choice`, `Quot.sound`
only; the `#print axioms` block at the end of the file is part of the build).
Build it with `./BoundedInductiveRationality/spike-build.sh
BoundedInductiveRationality/Spike.lean`.

Source committed under `notes/`: `2307.05068v1-main.tex` and `2307.05068v1.pdf`.

---

## A. Executive verdict

> **RED/YELLOW — LI-like representation project**, with an unusually clean and
> unusually *separable* extensional core.

The separability is the finding. This paper is not uniformly hard: it is one
short, ordinary piece of real analysis wrapped around one genuinely unformalizable
computational claim, and the seam between them is sharp enough to cut on. Everything
the paper proves *about* BRIAs, including the existence theorem's whole mathematical
content, went from nothing to compiling in a single session. Everything the paper says
about *computing* BRIAs — Theorem 1's algorithm and runtime, Theorem 2's lower bound,
Theorem 3's and Theorem 4's "e.c." closure conditions, Definition 8's selector
quantifier — rests on a machine model the paper never specifies and on conventions
(promise representation, input size, exact comparison) it never states.

Per-layer:

| Layer | Rating | One-line reason |
|---|---|---|
| Extensional BRIA mathematics (Defs 1–7, Lemma 6) | **GREEN — CF-like** | Compiled, with reading lemmas; the only design decision that mattered was rendering "the sequence indexed by `B` tends to `−∞`", and `atTop ⊓ 𝓟 B` settles it. |
| BRIA construction — Theorem 1's mathematical half | **GREEN/YELLOW — FSM-like** | One representation choice (total `pickWinner` + a separate attainment proof), then routine. Full extensional existence theorem compiled over a genuinely countable family. |
| Computability (Thm 1 part 4, Thm 2, "e.c." in Thms 3/4) | **RED/YELLOW — LI-like** | No machine model in the paper; LI's `dd:fuel` class is hardwired *polynomial* and its lower-calibration is the open direction Theorem 2 needs. |
| Runtime complexity (`O(g(t)q(t))`) | **RED — not presently formalizable faithfully** | The printed bound is not a well-formed claim: `q` is defined to contain a factor `g`, so "arbitrarily slow-growing `q`" is false whenever `g` is unbounded (E16), and there is no input-size convention (E17). |
| vMWC randomness (Def 8, Thm 4; Defs 9–10, Thm 9) | **RED/YELLOW** | **Definition 8 as printed is unsatisfiable** on binary sequences with mean 1/2 — the paper's own π-digits example (E6, proved). The corrected notion is formalizable, but its quantifier ranges over sets "decidable from available information", a phrase never defined (E15). |
| Game theory (Thm 5) | **YELLOW** | The converse half is a corollary of Theorem 3 — compiled, with a Prisoner's Dilemma instance — and the minimax theorem, stated as Lemma 7, is **never used and is malformed as printed** (E11, E26). But the folk theorem's *headline* claim, that the empirical distribution converges to `c′`, **is never proved in the paper at all** (E24): the printed proof establishes only no-overestimation and coverage. That is missing mathematics, not missing formalization. |

---

## B. Node inventory

The source uses `\newtheorem{definition}{Definition}` and `\newtheorem{theorem}{Theorem}`
with `\newtheorem{lemma}[theorem]{Lemma}` — two independent global counters that never
reset, with lemmas sharing the theorem counter. That is FFS's `printed-independent`
scheme. Some but not all nodes carry `\label`s (`def:BRIA`, `thm:computable-BRIAs`,
`thm:no-ec-BRIA`, `thm:lower-bounds-from-easy-options`, `def:bounded-vMWC-randomness`,
`thm:pseudo-lotteries`, `thm:folk-theorem`, `lemma:testing-positive-estimate`), so as in
Cartesian Frames and ModalAgents the **printed numbers are the provenance key**.

**A provenance trap worth knowing before anyone writes a checker.** The committed
`main.tex` can build *two different papers*. `\extendedonlybit{…}` / `\abridgedonlybit{…}`
(tex lines 91/94) and the `extendedonlyblock` environment switch on an `extendedversion`
boolean, which the committed source sets to `false` (tex line 86) — so the file as
committed *does* build the published abridged paper, and the PDF matches it. But the
extended-only material is still physically present in the file, and a checker that
emulates LaTeX counters by scanning `\begin{theorem}` will count it.
The extended build contains two further conjectures, three further theorems and six
further propositions (tex lines 755–1240) that do not exist in the published paper —
and, because the counters are global, it **renumbers everything after them**. The
cheapest demonstration: an extra `\begin{theorem}` sits inside an `extendedonlyblock` at
tex line 763, between Appendix A.3 (Theorem 2's proof) and Appendix A.4 (Theorem 3's) —
so in the extended build, every theorem from the published "Theorem 3" onward shifts by
one. A node checker must strip both the macro and the block before counting, and the
ruling must be that the abridged build is the spec.

### The 19 published numbered nodes

| # | Node | Where | Tranche |
|---|---|---|---|
| Def 1 | cumulative overestimation `L_T` | §4.2 | elementary |
| Def 2 | does not overestimate | §4.2 | asymptotics |
| Def 3 | outpromises / rejects | §4.3 | elementary |
| Def 4 | test set | §4.3 | elementary |
| Def 5 | empirical record `l_T` | §4.3 | elementary |
| Def 6 | covers | §4.3 | asymptotics (divergence along a subsequence) |
| Def 7 | BRIA | §4.4 | composite |
| Thm 1 | existence + computability + `O(g q)` | §5, App A.2 | construction **+ computability + complexity** |
| Thm 2 | no e.c. BRIA (diagonalization) | §5, App A.3 | **computability + complexity** |
| Thm 3 | guaranteed payoffs | §6, App A.4 | asymptotics **+ computability closure** |
| Def 8 | bounded vMWC randomness | §6, App A.5 | **computability + randomness** |
| Thm 4 | vMWC payoffs | §6, App A.5 | asymptotics **+ randomness + computability** |
| Thm 5 | folk theorem (two halves) | §7, App A.6 | game theory **+ probability + construction** |
| Lem 6 | trimming zero-promise rounds | App A.1 | elementary |
| Lem 7 | minimax (von Neumann, cited) | App A.6 | external — **and unused** |
| Thm 8 | random payoffs | App B | probability (SLLN along an adapted selection) |
| Def 9 | martingale | App E | probability |
| Def 10 | bounded Schnorr randomness | App E | **computability + randomness** |
| Thm 9 | Schnorr payoffs | App E | probability + **computability** |

### Difficulty tranches (nodes may appear in more than one)

| Tranche | Count | Nodes |
|---|---|---|
| pure elementary analysis / combinatorics | 5 | Defs 1, 3, 4, 5; Lem 6 |
| requires asymptotics (limits, `limsup`, divergence, Cesàro) | 5 | Defs 2, 6, 7; Thms 3, 4 |
| requires an explicit computability model | 7 | Thm 1 (part 4), Thm 2, Thm 3 (closure), Def 8, Thm 4, Def 10, Thm 9 |
| requires complexity analysis (asymptotic *runtime*) | 2 | Thm 1, Thm 2 |
| requires probability / algorithmic randomness | 6 | Def 8, Thm 4, Thm 8, Def 9, Def 10, Thm 9 |
| requires game theory / external results | 2 | Thm 5, Lem 7 |

### Load-bearing unnumbered claims

Nine, and they carry more weight than several of the numbered nodes:

1. §2 — `DP ∈ Fin(T)`, agent as a sequence, rewards in `[0,1]`, **no counterfactual
   rewards**, and "the sequence of decision problems `DP_t` may in turn be calculated
   depending on the agent's choices".
2. §4.1 — "A hypothesis `h` has the same type signature as an estimating agent." This
   is the entire typing discipline (`hᶜ_t ∈ DP_t`, `hᵉ_t ∈ [0,1]`) and it is the reason
   Theorem 3 needs `L_t ∈ [0,1]` (E7) and Theorem 4 needs `max(μ_t − ε, 0)`.
3. §4.4 — "whenever `ᾱ` is a BRIA, we will imagine that the test sets are given as a
   part of `ᾱ`". Load-bearing for Theorem 4: it is what makes the test set decidable.
4. App A.2 part 1 — the three allowance requirements and display (1).
5. App A.2 part 1 — display (2), the `arg max` (see E1).
6. App A.2 part 1 — the wealth update rule.
7. App A.2 part 4 — active hypotheses, `A` with finite e.c. support, `C_max(t)`,
   `h_b(t)`, and `q(t) = h_b(t)C_max(t)g(t)` (see E16).
8. §7 — the game, correlated strategy profile, strict individual rationality, and the
   `DP^{ᾱ_i} = A_i` embedding.
9. App A.6 — the `p_c` / `p_{a_i}` / `v_i` randomisation defining the folk theorem's two
   agents.

### Dependency graph (published nodes)

```
Defs 1,2 ──────────────┐
Defs 3,4,5 ── Def 6 ── Def 7 (BRIA) ──┬── Thm 1  (App A.2: allowance, argmax, wealth)
                │                     ├── Thm 2  (App A.3: diagonal)
              Lem 6 ──────────────────┼── Thm 3  (App A.4)  ── Thm 5 converse (App A.6)
                │                     │      │
                └─────────────────────┼── Def 8 ── Thm 4  (App A.5)
                                      ├── Thm 8  (App B: SLLN)
                                      ├── Defs 9,10 ── Thm 9 (App E)
                                      └── Thm 5 constructive (App A.6) ←╌╌ Lem 7 (declared, unused)
```

Note what the graph shows: **Theorem 1 is a leaf**. Nothing downstream uses the
auction — Theorems 3, 4, 5, 8, 9 all argue directly from Definition 7. A formalization
can defer Theorem 1 entirely without blocking anything else, and conversely Theorem 1
can be done first for its own sake. That is unusual and it is the single most useful
scheduling fact in this report.

---

## C. Recommended representation

Actual signatures from the spike.

```lean
structure Agent (DP : ℕ → Finset Action) where
  choice          : ℕ → Action
  estimate        : ℕ → ℝ
  choice_mem      : ∀ t, choice t ∈ DP t
  estimate_nonneg : ∀ t, 0 ≤ estimate t
  estimate_le_one : ∀ t, estimate t ≤ 1

abbrev Hypothesis (DP : ℕ → Finset Action) := Agent DP
```

Three decisions, all disclosed at the definitions:

* **`dd:realrewards`** — plain `ℝ` with `[0,1]` as *fields*, not `↥(Set.Icc 0 1)`. Every
  paper argument is an inequality chain fed to `linarith`; a subtype puts a
  `Subtype.val` in each one. The bounds are genuinely load-bearing in only a handful of
  places (`hᵉ ≤ 1` in the auction's coverage step; `L_t ≤ 1` in the Cesàro transfer),
  and carrying them as fields makes those places visible rather than automatic.
* **`dd:index0`** — time from `0`, `∑_{t=1}^T` read as `∑ t ∈ Finset.range T`. This also
  resolves the paper's own `t ≤ T` / `t < T` inconsistency (E4); the cost is bounded by
  `record_shift_le_one`, proved.
* **`dd:agentbundle`** — one structure for agents and hypotheses, per §4.1. Faithful
  *extensionally*; §I is where the extensional/intensional slippage is charged.

The decision that actually mattered:

```lean
abbrev alongAtTop (B : Set ℕ) : Filter ℕ := atTop ⊓ 𝓟 B

def Covers (α : Agent DP) (r : ℕ → ℝ) (h : Hypothesis DP) (M : Set ℕ) : Prop :=
  (rejectionSet α h).Finite ∨
    Tendsto (record r M h) (alongAtTop (rejectionSet α h)) atBot
```

with three obligations discharged rather than assumed:

* `covers_iff_forall` — the filter form unfolds to exactly "for every `C` there is an
  `N` past which every *rejection time* `T ∈ B` has record below `C`". The quantifier
  is over `T ∈ B` and nothing else.
* `covers_iff_tendsto` — **the printed disjunction is redundant.** When `B` is finite,
  `alongAtTop B = ⊥` and `Tendsto f ⊥ l` holds for every `f`, so Definition 6 *is* the
  single filter statement. This saves a case split at every use site.
* an explicit counterexample separating `Tendsto f (alongAtTop B) atBot` from
  `Tendsto f atTop atBot`, so nobody quietly upgrades the definition. The auction proof
  makes the distinction bite: the record bound there holds **only** at rejection times
  (it needs `w_T(i) < 1`, which is what rejection gives), so a global reading would be
  unprovable, not merely stronger.

The allowance function is a bundled structure carrying the paper's three requirements
verbatim, and it is inhabited:

```lean
structure Allowance where
  A                   : ℕ → ℕ → ℝ
  nonneg              : ∀ n i, 0 ≤ A n i
  rowSummable         : ∀ n, Summable (A n)                      -- round total finite
  colNotSummable      : ∀ i, ¬ Summable (fun n => A n i)         -- ∑_n A(n,i) = ∞
  avgTotalTendstoZero : Tendsto (fun N => (∑ n ∈ range N, ∑' i, A n i) / N) atTop (𝓝 0)

noncomputable def harmonicSquare : Allowance   -- A(n,i) = (n+1)⁻¹(i+1)⁻², all three proved
```

---

## D. What compiled

Every item below is in `Spike.lean`, proved, no `sorry`.

**Definitions.** 1, 2, 3, 4, 5, 6, 7 (`cumOver`, `NoOverestimation`, `Rejects`,
`IsTestSet`, `record`, `Covers`, `IsBRIA`); 8 in *both* readings (`VMWCPrinted`,
`VMWCAveraged`).

**Reading / equivalence lemmas.** `alongAtTop_neBot_iff`, `alongAtTop_eq_bot_of_finite`,
`covers_iff_tendsto`, `covers_iff_forall`, `covers_of_tendsto_atBot`,
`noOverestimation_iff_limsup`, `record_shift_le_one`, plus the compiled counterexample
that global divergence is strictly stronger than divergence along `B`.

**Generic machinery.** `record_nonneg`, `rejectionSet_finite_of_record_bddBelow` (the
lever every positive theorem in the paper pulls), `bddBelow_of_eventually_nonneg`,
`avg_ge_of_eventually_estimate_ge` (the Cesàro/finite-prefix transfer),
`avgTotal_of_tendsto_zero`.

**Lemma 6.** `lemma6`.

**Theorem 3.** `theorem3_core` and `theorem3`, with the class-membership condition an
*explicit* hypothesis (`∃ i, (H i).choice = a ∧ (H i).estimate = L`), never a predicate
named `EfficientlyComputable`.

**Theorem 1, mathematical half — in full.** `theorem1_extensional`:

> For any countably enumerated family `H : ℕ → Hypothesis DP`, any `Allowance`, and any
> `[0,1]`-valued reward stream, the first-price auction construction is a BRIA covering
> `H`, with the winning rounds as test sets.

built from `wealth`, `bid`, `winner`, `auctionAgent`, `winSet`, and proved via
`wealth_nonneg`, `wealth_tendsto_zero`, `exists_max_of_tendsto_zero`, `exists_max_bid`,
`winner_isMax`, `isTestSet_winSet` (part 3B), `wealth_eq_allowance_add_net`,
`record_le_wealth_sub_allowance`, `wealth_lt_one_of_rejects`, `covers_all` (part 3C),
`summable_wealth`, `tsum_wealth_eq`, `noOverestimation_auction` (part 2). Part 3A is
proved separately (`wealth_eq_of_no_win`, `winSet_infinite_of_rejected_infinitely`) even
though it is not needed — see E21. Non-vacuity witnessed by an explicit instantiation at
`harmonicSquare`.

So **all four numbered parts of the printed proof are covered except part 4**, which is
the computability and complexity argument. That is the seam.

**Allowance schedule.** `harmonicSquare` with `summable_invSq`, `not_summable_invLin`.

**Theorem 2.** `diagChoice`, `diagHyp`, `rejectionSet_diagHyp`,
`testSet_diagHyp_disjoint`, `theorem2_extensional`, `theorem2_no_bria`.

**Definition 8 / Theorem 4.** `vmwcPrinted_forces_pointwise`,
`vmwcPrinted_vacuous_on_bits` (the refutation), `record_bddBelow_of_vmwc`,
`theorem4_single` (using Lemma 6 for the paper's WLOG), `theorem4`.

**Theorem 5, converse half.** `theorem5_converse`, plus `pdRow` / `pdRow_maximin` and a
Prisoner's Dilemma instance exercising the actual construction.

**Computability interface.** `PromiseRepresentation` with `ratPromises` and
`realPromises`, and `DiagonalObligations`.

**Non-vacuity witnesses.** `boolDP`, `constAgent`, and the three required examples: a
hypothesis covered because it stops outpromising; one covered because repeated tests
drive its record to `−∞`; one **not** covered because it keeps its promises while
outpromising infinitely often.

Two things the paper does not do, done here because they are load-bearing:

* **The `arg max` of display (2) is over infinitely many hypotheses and the paper never
  argues it is attained.** It is — but only because the per-round allowance total is
  finite, which forces `w_t(i) → 0` as `i → ∞`. `wealth_tendsto_zero` +
  `exists_max_of_tendsto_zero` + `exists_max_bid`. Without this the construction is not
  even well-defined.
* **The wealth identity in part 3C is false and the correct version is an inequality.**
  See E2.

---

## E. Theorem 1 autopsy

Theorem 1 is three claims wearing one number. Splitting them is the most useful thing
this spike did.

### E.1 `Theorem 1a` — mathematical existence

> Given a countable enumerated hypothesis family and an allowance schedule satisfying
> the three requirements, the auction construction extensionally defines a BRIA
> covering the family.

* **Formalizable now?** Done. `theorem1_extensional`.
* **Representation needed?** One decision: make the winner-selection function *total*
  (`pickWinner b = if h : ∃ i, ∀ j, b j ≤ b i then h.choose else 0`) and prove
  separately that the fallback is never taken (`winner_isMax`). A partial `arg max`
  inside the `Nat.rec` defining `wealth` would drag the whole attainment invariant into
  the definition and make every subsequent lemma dependently typed. This is the
  FSM-like moment of the paper and it costs about forty lines.
* **Existing substrate?** Mathlib only: `Summable`, `tsum_add`, `tsum_eq_single`,
  `summable_of_hasFiniteSupport`, `not_summable_iff_tendsto_nat_atTop_of_nonneg`,
  `Filter.Tendsto.cesaro`. Nothing from `LogicalInduction`.
* **Difficulty?** Low, now that it is written. It is ~250 lines.
* **Paper-strength?** **Yes**, for the existence half. And note the scope: the family is
  genuinely `ℕ`-indexed with a possibly-infinitely-supported allowance (the tsum
  accounting is real, not a finite-support dodge). A finite-hypothesis toy would have
  proved nothing; this does not use one.

Three by-products worth recording:

* **Part 3A is redundant.** The paper separately proves that `M_i` is infinite. Nothing
  in Definitions 6 or 7 requires it, and part 3C alone establishes coverage —
  `theorem1_extensional` compiles without any infinitude claim. It is nevertheless
  proved (`winSet_infinite_of_rejected_infinitely`), because it is the step where
  requirement (i) does its intended work, and because a test set that is never used
  would make the construction uninteresting even where it is formally adequate.
* **`B⁺_T` is vestigial.** Wealth is nonnegative from round zero (`wealth_nonneg`), so
  part 2's bookkeeping over "hypotheses with positive wealth at some time" is
  unnecessary; the whole argument is one telescoping `tsum` identity
  (`tsum_wealth_eq`).
* **Requirement (ii) is not an extra condition.** Display (1) follows from "per-round
  total allowance `→ 0`" by Cesàro (`avgTotal_of_tendsto_zero`, one line over
  `Filter.Tendsto.cesaro`).

### E.2 `Theorem 1b` — effective computability

> The construction can be implemented by an algorithm.

* **Formalizable now?** Not faithfully. Four things are needed and none is supplied by
  the paper:
  1. **A representation of promises with decidable order.** The auction computes
     `arg max_i min(hᵉ_{i,t}, w_t(i))`. If promises are computable reals, `<` is
     undecidable and the algorithm does not exist. The paper never says what a promise
     *is* (E18). `PromiseRepresentation` in the spike is the interface; `ℚ` inhabits it.
  2. **A computable tie-break.** "with arbitrary tie breaking" is free classically and
     is a decision procedure computationally.
  3. **An input-size convention.** `O(g(t))` is asymptotic in the round index `t`, but
     the round-`t` input includes `DP_t`, a finite set of terms in an unspecified
     language `T`. Nothing bounds `|DP_t|` or its encoding length, so even *reading the
     input* is not `O(g(t))` for any `g` (E17).
  4. **`H` as programs, not sequences.** §4.1 defines a hypothesis extensionally, as a
     sequence. §5 quantifies over "a computably enumerable set consisting of
     `O(g(t))`-computable hypotheses" — a set of programs. §2 then says `DP_t` "may be
     calculated depending on the agent's choices", which makes the sequence reading
     circular in exactly the cases (SAO, games) the paper is *for*. The extended build
     of the source says the quiet part out loud in a sentence cut from the published
     version: "But technically we can consider an agent who chooses `c̄` in the
     beginning without ever looking at `D̄P` or `r̄`" (tex line 172). The published
     paper does not make the intensional reading available.
* **Representation needed?** A machine model in which programs, not functions, are the
  objects, plus a `PromiseRepresentation` fixed by ruling.
* **Existing substrate?** See §F. Not `LogicalInduction`'s: its class is hardwired
  polynomial.
* **Difficulty?** High. This is the LI-shaped part.
* **Paper-strength?** **No.** The most an honest formalization can do is state 1b
  relative to a named interface, disclose it as a type-`(c)` substitution, and say so.

### E.3 `Theorem 1c` — the runtime bound `O(g(t)q(t))`

* **Formalizable now?** **No — and the printed claim is not well-formed.** Part 4 sets
  `q(t) = h_b(t)·C_max(t)·g(t)` and then asserts the algorithm runs in `O(g(t)q(t))`
  "for arbitrarily slow-growing, `O(g(t))`-computable `q` with `q(t) → ∞`". Two
  problems, both structural:
  1. The cost actually computed in part 4 is `h_b(t)·C_max(t)·g(t)`, which *is* `q(t)`.
     So the claimed bound `O(g·q)` overcounts `g` by one factor.
  2. With `q(t) ≥ g(t)` by construction and `g ∈ Ω(log)` unbounded by hypothesis, `q`
     **cannot** be "arbitrarily slow-growing". The intended statement is presumably
     `q(t) = h_b(t)·C_max(t)` with runtime `O(g(t)q(t))`, which is coherent — but that
     is a repair, not a reading.

  There is also a quantifier mismatch. The theorem reads as ∀`q`∃algorithm ("for
  arbitrarily slow-growing `q`"); the proof delivers ∃`q` determined by the chosen `A`
  and the enumeration of `H`. The charitable reading — the overhead factor can be made
  to grow as slowly as one likes by activating hypotheses late enough — is defensible
  and is probably what is meant, but it needs `C_max` to be slowable too, and `C_max` is
  fixed by `H` unless the *activation schedule* is what slows it. The paper does not say
  this.
* **Difficulty?** Beyond the machine model, this needs an asymptotic-complexity calculus
  for a *specific algorithm* with a *parametric* bound `g`. Nothing in Lean has this.
* **Paper-strength?** **No**, and not because of Lean. The statement needs repair at
  source first.

### E.4 Two strategies for a computational Theorem 1, compared

**Strategy 1 — extensional theorem plus an abstract-complexity interface.**
Prove Theorem 1a as it stands (done), then bundle the computational side into a
structure whose fields are the properties the paper's proof actually uses: a type of
programs, a denotation into `Hypothesis DP`, a cost function, a `RunsIn g` predicate, a
surjection from `ℕ` onto the programs (c.e. enumeration), and the closure lemmas
Theorems 3 and 4 need. State 1b and 1c as theorems *taking that structure as a
hypothesis*.

* Proves: 1a in full; 1b and 1c **conditionally**.
* Becomes assumptions: every field — in particular the closure properties, which are
  where the real content is.
* Modeling substitutions: **none**, provided the structure is never instantiated by a
  dummy and never named something that reads as a proof (`EfficientlyComputable` is
  exactly the name not to use). A conditional theorem honestly labelled is not a
  substitution.
* Paper-strength: 1a yes, 1b/1c no.
* Cost: days. This is the spike's `PromiseRepresentation` / `DiagonalObligations` pattern
  scaled up.
* Risk, and it is the real one: a reader takes the conditional theorem for the paper's.
  Mitigation is FAF's existing discipline — the interface must be listed as an
  *uninhabited* trust boundary in the README, not merely disclosed in a docstring.

**Strategy 2 — an actual executable machine model.**
Build a machine with counted steps, an `O(g)` class parametric in `g`, a c.e.
enumeration with a cost-accounted universal simulator, and a fixed promise
representation with decidable order.

* Proves: 1b in full, and 1c *after* the source defects are repaired.
* Becomes assumptions: the input-size convention (E17) and the promise representation
  (E18). Neither is in the paper, so both are **rulings**, and both are type-`(c)`
  substitutions requiring a model card.
* Paper-strength: 1b yes within the chosen conventions; 1c **no**, because the printed
  statement does not typecheck as written (E16) — no amount of Lean fixes that.
* Cost: research-scale. See §H.

**Recommendation: Strategy 1**, with the interface left uninhabited and marked as such.
Strategy 2 buys 1b at the price of a multi-year substrate and still does not buy 1c,
which is the claim anyone actually cares about. That asymmetry — the expensive path does
not reach the interesting statement — is the single strongest argument for scoping BIR
to its extensional half.

---

## F. LI reuse assessment

Searched: `LogicalInduction/Framework/`, `Construction/`, `Properties/`, `API.lean`,
`README.md`, `notes/boundary-efficiency-model.md`, `notes/consolidation.md`.

| BIR need | LI declaration / module | Verdict | Reason |
|---|---|---|---|
| limit vocabulary `f ≥ g as T → ∞` | `AsympLE` / `AsympGE` / `AsympEq`, `Framework/Asymptotics.lean` | **exact reuse of the definitions — copy, do not import** | `AsympLE f g := ∀ ε>0, ∀ᶠ n, f n ≤ g n + ε` is *literally* Definition 2's own gloss and Theorem 3's conclusion. But it is `LogicalInduction`-namespaced, and CLAUDE.md's "one `Asymptotics` module owns the limit vocabulary" is a per-library rule. Copy three definitions; a cross-paper import would couple two trust surfaces for no gain. |
| enumerated hypothesis family | `Construction/TraderEnumeration.lean` (`TraderProgram`, `traderProgramAt`, `enumeratedTrader`, `exists_enumeratedTrader_eq`) | **superficially similar — do not reuse** | The index decodes *two* `Nat.Partrec.Code`s plus a **polynomial** clock (`TraderProgram.clock p n = a*(n+1)^k + a`). BIR needs a c.e. family under an `O(g)` clock for arbitrary non-decreasing `g`. The shape is right; every constant in it is wrong. |
| the `O(g(t))`-computable hypothesis class | `EfficientlyComputable`, `Framework/Criterion.lean:1765` | **semantically wrong for BIR** | Hardwired polynomial: `clockedTrader lengthCode tokenCode (fun n => a*(n+1)^k + a) = Tr`. Not parametric in `g`. Generalising is not a rename: `Framework/Emission.lean` and `Framework/Computable.lean` state every closure and emission lemma at `IsPolyBounded`/`PolyFueled`. |
| an upper cost bound for a specific algorithm | `Fueled c f b`, `Framework/Computable.lean:64` | **reusable with a small adapter — upper bound only** | `Fueled` takes an *arbitrary* bound `b`, so "`b ∈ O(g)`" is expressible without touching the definition. This is the one genuine transfer in the computability layer. |
| **runtime lower bound (Theorem 2)** | — | **nothing transfers** | LI's only separation is `not_polyFueled_two_pow`, an *output-size* result. The `dd:fuel` model card is explicit: "a time-based lower bound (small output, provably superpolynomial fuel) … not claimed", and `notes/boundary-efficiency-model.md` marks the converse inclusion "**Stage 4 — do not attempt**". Theorem 2 is precisely a time lower bound. **BIR needs the direction LI declared out of scope.** |
| budget/allowance distribution over an infinite family | `Construction/Budgeter.lean`, `Construction/TradingFirm.lean` | **superficially similar — do not reuse** | LI's firm is a doubly-infinite geometric mixture of *budgeted* traders with a bankruptcy test "discontinuous in past prices"; BIR's is a first-price auction with a wealth ledger and a winner-takes-all update. The shared *idea* — a finite active set with gates opening over time — is a pattern to copy, not code. BIR's version is much simpler and the spike already has it. |
| pseudorandomness / vMWC | `Properties/Pseudorandomness.lean` (`def:pseudorandom`, `def:seqprand`, `thm:prand`, `DeferralPatient`) | **superficially similar — do not reuse** | LI's pseudorandomness is about sequences of *sentences* with e.c.-generable subsequences and market prices, under a bounded-window deferral condition. BIR's Definition 8 is about real-valued reward streams and selection sets. Different objects; the deferral machinery does not apply. |
| Cesàro, p-series, filters, `atBot` | Mathlib, not LI | **use Mathlib directly** | All confirmed present at the pin: `Filter.Tendsto.cesaro`, `Real.summable_one_div_nat_pow`, `Real.not_summable_one_div_natCast`, `not_summable_iff_tendsto_nat_atTop_of_nonneg`, `Nat.frequently_atTop_iff_infinite`. The spike uses exactly these. |
| minimax | absent from both | **not needed** — see E11 | |
| **the disclosure apparatus** | `dd:fuel` model card, `notes/boundary-efficiency-model.md`, README "The two modeling boundaries", `scripts/coverage-classification.md` | **exact reuse — of the method, and it is the most valuable transfer** | BIR needs the same three artifacts: a named type-`(c)` substitution at the statement, a model card proving its calibration facts, and a boundary memo pricing the closure. The LI precedent tells us what "honest" looks like here and saves the argument. |

Summary in one sentence: **the answer to "can BIR reuse LI's computability layer?" is
no, and the reason is not aesthetic** — LI's class is polynomial where BIR's is `O(g)`,
and LI's separation is by output size where BIR's Theorem 2 needs one by time.

---

## G. Source ambiguities and errata

Thirty-four findings — twenty-three from the spike, eleven more from an independent
fresh-context re-reading (§M), which also confirmed all twenty-three. Each is classified
as **typo**, **harmless omitted convention**, **missing hypothesis**, **genuine
mathematical gap**, **formalization choice**, or **theorem-strength reduction**. References are to the arXiv v1 PDF / the committed
`main.tex`.

### Genuine mathematical gaps

**E1. Display (2)'s `arg max` is not shown to be attained.** App A.2 part 1
(`eq:highest-hypothesis`, tex 667): `i*_t ∈ arg max_{i∈ℕ} min(hᵉ_{i,t}, w_t(i))` over
infinitely many hypotheses. A supremum over `ℕ` need not be attained, and if it is not,
the construction is undefined. It *is* attained — but only via a lemma the paper never
states: requirement (iii) forces `A(n,·) → 0`, hence `w_t(·) → 0`, hence only finitely
many bids exceed any `ε`. **Repaired and proved** (`exists_max_of_tendsto_zero`,
`wealth_tendsto_zero`, `exists_max_bid`), ~40 lines. *Missing lemma.*

**E6. Definition 8 is missing its normalization, and as printed Theorem 4's hypothesis
is unsatisfiable.** §6 / App A.5 (`def:bounded-vMWC-randomness`, tex 410). Printed:
`lim_{T→∞} ∑_{t∈S_{≤T}} y_t − μ_t = 0`. That is a *sum*. The notion it generalises
(Downey–Hirschfeldt Def 7.4.1, cited) is a limiting relative *frequency*, and Theorem
4's own proof divides by `|M_{i,≤T}|`. Under the literal reading the partial sums along
`S` converge, so the increments vanish, so `y_t → μ_t` along every selectable set — a
`{0,1}`-valued sequence with means `1/2` can never satisfy it. The cheapest instance
needs no computability at all: take `S = ℕ`, which is infinite and decidable under any
reading of "decidable from available information". That is the paper's own
motivating example (the `2^t`-th binary digits of π, §4.5). **Proved**
(`vmwcPrinted_forces_pointwise`, `vmwcPrinted_vacuous_on_bits`). The proof of Theorem 4
happens to survive under *either* reading, which is why the slip went unnoticed: it only
shows up when you ask whether the hypothesis is inhabited. *Genuine mathematical error;
must be fixed by ruling before Theorem 4 is formalized.*

**E16. Theorem 1's complexity bookkeeping double-counts `g` and contradicts its own
"arbitrarily slow-growing".** App A.2 part 4. `q(t) := h_b(t)C_max(t)g(t)` while the
computed cost is `h_b(t)C_max(t)g(t) = q(t)`, so the claimed `O(g·q)` overcounts by a
factor `g`; and since `q ≥ g` and `g ∈ Ω(log)` is unbounded, `q` cannot be "arbitrarily
slow-growing". There is also a quantifier mismatch: the statement reads ∀`q`∃algorithm,
the proof delivers ∃`q`. *Genuine gap in the complexity claim.*

**E23. Theorem 8 applies the SLLN along a reward-dependent selection.** App B. The test
set `M` "may depend on `r̄` and inherit its stochasticity. This will not matter for the
following, though." It does matter: the plain Kolmogorov SLLN is for a fixed index set.
The rescue is that `t ∈ M` is decided *before* `r_t` is revealed, so the selection is
predictable and a martingale argument applies — but that is a different theorem from the
one invoked, and Mathlib's `strong_law_ae` additionally requires identically distributed
variables, which Theorem 8 does not have. *Genuine gap; repairable at real cost.*

### Missing hypotheses

**E7. Theorem 3 never requires `L̄ ⊆ [0,1]`.** `thm:lower-bounds-from-easy-options`.
The proof's hypothesis is `h_{i,t} = (a_t, L_t)`, and §4.1's type signature demands
`hᵉ ∈ [0,1]`. Without `L_t ≤ 1` the constructed hypothesis is ill-typed; without
`L_t ≥ 0` it is illegal. (Theorem 4's proof handles exactly this with `max(μ_t − ε, 0)`
plus Lemma 6; Theorem 3's does not.) The spike's `theorem3` carries `hL0`/`hL1`
explicitly. *Missing hypothesis.*

**E14. Theorem 9 never states that rewards are binary.** App E. Definitions 9 and 10 are
over `B*` and `B^ω`; the martingale in the proof bets on bits and the conclusion is
`≥ 1/2`. Also "the values `r_t` in the rounds `t` with `α^c_t`" is an incomplete
sentence (missing `= a_t`), and the success bound `(1+δ)^{T+εT}(1−δ)^T` is written in
`T` where it must be in `|M_{≤T}|`. *Missing hypothesis + typos.*

**E19. `g ∈ Ω(log)` is silently used but never invoked.** Theorem 1. The phrase occurs
exactly once in the source, in the statement; the four-part proof never mentions it. It
is not idle, though: part 4 indexes `h_b(t)` hypotheses and performs `O(h_b(t))`
additions on `Θ(log t)`-bit quantities, which cannot fit in `O(g·q)` unless
`g ∈ Ω(log)`. So the honest description is *silently used, never invoked* — which is
worse than an idle hypothesis for a formalizer, because the place it is needed is
exactly the place the paper's cost accounting is least explicit. *Unstated dependency.*

### Undefined computational terms

**E15. "decidable from available information" is never defined.** Definition 8 quantifies
over infinite `S ⊆ ℕ` "decidable (in `O(h(t))` time) from available information";
Definition 10 over martingales "computed (in `O(g(t))`) given everything revealed by time
`t`". Neither phrase is defined anywhere. Theorem 4's proof then asserts "`M` is by
assumption computable in `O(h(t))` given the information available at time `t`", leaning
on §4.4's convention that test sets are output alongside `α` — which gives a *list of
tested hypotheses*, not membership in `M_i` for a specific `i`, unless one also fixes the
index of `h̄_{a,ε}` in the enumeration. **This is the load-bearing undefined term.** It
is what makes the vMWC layer a computability-interface problem rather than a probability
problem. *Genuine underspecification.*

**E17. No input-size convention behind `O(g(t))`.** The bound is asymptotic in the round
index `t`, but the round-`t` input includes `DP_t ∈ Fin(T)` for an unspecified language
`T`. Nothing bounds `|DP_t|` or the encoding length of its elements. Theorem 3 papers
over this with "the `a_t` are efficiently identifiable from the sets `DP_t`", itself
undefined; Theorem 2's diagonal hypothesis must *search* `DP_t`. *Missing convention.*

**E18. Exact comparison of real-valued promises is assumed twice.** Theorem 1's `arg max`
compares `min(hᵉ, w)` across hypotheses; Theorem 2's diagonal hypothesis tests
`αᵉ_t < 1`. Both are undecidable for computable reals. The paper never fixes a
representation for promises. *Missing convention with theorem-strength consequences.*

### Typos and vestigial text

**E2. The wealth identity in App A.2 part 3C is false as an equality.** Printed:
`w_T(i) = ∑_{n=1}^T A(n,i) + ∑_{t∈M_i:t<T} r_t − hᵉ_{i,t}`. The winner pays its
*wealth-bounded* bid `min(hᵉ, w)`, not `hᵉ`. Correct identity:
`wealth_eq_allowance_add_net`. The argument survives because the error points the way it
needs — `record_le_wealth_sub_allowance` gives `≤`, which is what the coverage step
consumes. *Erratum with a proved repair.*

**E3. Index slips in App A.2 part 3C.** "`w_T(i, j) < hᵉ_{i,t}(DP_T)`" has a stray
second index `j` and should be `w_t(i) < hᵉ_{i,t}`; "for all `T ∈ B_i`" then mixes `t`
and `T`. Also, `hᵉ_{i,t}(DP_T)` is the only place in the paper where a promise is written
as a *function of* `DP` — which is the intensional reading §4.1 does not license (cf.
E.2 item 4). *Typos, but the last one is diagnostic.*

**E4. `M_{≤T}` versus `t < T`.** Definition 5 defines `M_{≤T} = {t ∈ M | t ≤ T}`; the
proofs of Theorems 1 and 3 use `t ∈ M_i : t < T`. The two records differ by at most one
term, of size at most `1` since rewards and promises are in `[0,1]`, so no asymptotic
statement is affected. **Proved** (`record_shift_le_one`). *Harmless omitted convention.*

**E8. Theorem 3's proof sketch mentions an undefined `S`.** §6: "the hypothesis that
estimates `L_t` and recommends `a_t` if `t ∈ S` and promises 0 otherwise". `S` is never
introduced; the appendix proof drops it (`h_{i,t} = (a_t, L_t)`). *Vestigial text.*

**E9. Theorem 5's reward definition has the wrong player index.** §7:
`r_{i,t} = u_i(α^c_{1,t}, α^c_{1,t})` should be `u_i(α^c_{1,t}, α^c_{2,t})`. *Typo.*

**E10. Theorem 5's no-overestimation step states the wrong bound.** App A.6:
`L_T(ᾱ_i,r̄_i)/T = ∑(v_i − r_{i,t})/T ≤ v_i − u_i(c)`. The long-run average reward under
the construction is `p_c u_i(c) + ∑_a p_a u_i(…)`, so the derivable bound is
`v_i − p_c u_i(c)` — which is exactly what `v_i < p_c u_i(c)` was chosen to make
negative. The conclusion holds; the displayed intermediate does not follow. It is also a
law-of-large-numbers statement written as a deterministic one. *Typo + missing "almost
surely".*

**E20. Theorem 2's proof has a gap that the abridgement introduced.** App A.3 says the
diagonal hypothesis "promises 0 otherwise" without specifying `hᶜ` there — so as printed
it is not a total hypothesis, since §4.1 requires a choice `hᶜ_t ∈ DP_t` at *every* `t`.
Worse, the proof's conclusion "but is never tested" is **false** as printed: nothing
stops the agent testing it on the promises-`0` rounds. The tex shows why — the
justification is extended-only
(`\extendedonlybit{, see Lemma \Cref{lemma:testing-positive-estimate}}`), so the
abridged build deleted the citation to Lemma 6 that closes the hole, while keeping Lemma
6 itself in the paper. The repair is one line and the spike carries it: the record on
the promises-`0` rounds is `∑ r_t ≥ 0`, so coverage fails either way
(`theorem2_extensional`). *Missing hypothesis + a genuine gap in the published proof,
both repairable.*

**E22. `B⁺_T` is vestigial and part 2 has a stray quantifier.** App A.2 part 2 introduces
`B⁺_T`, the hypotheses with positive wealth at some time `≤ T`. With the example
allowance every hypothesis has positive wealth from round 1, so `B⁺_T = ℕ`; and since
wealth is nonnegative from the start the set is not needed at all. "Note that all
highest-bidding hypotheses in rounds `1,…,T` are in `B⁺_T` for all `j`" has no `j` in
scope. *Vestigial + typo.*

### Structural observations (not errors)

**E5. Definition 6's disjunction is redundant.** Proved (`covers_iff_tendsto`).
*Formalization observation.*

**E11. Lemma 7 (the minimax theorem) is declared and never used.** App A.6 states it,
cites von Neumann, and then proves Theorem 5 entirely with the **pure**-strategy maximin
`max_{a_i} min_{a_{-i}} u_i(a_i, a_{-i})` — in the definition of strict individual
rationality, in the choice of `v_i`, and in the coverage bound. No mixed strategy ever
appears on the minimising side. **The paper's one external mathematical dependency is,
in the printed argument, spurious.** This is good news: Mathlib has no minimax theorem
and no game theory at all at the pin, and it turns out not to matter. *Spurious
dependency.*

**E12/E13. Theorem 5's existence claim is probabilistic.** App A.6 constructs the two
BRIAs from a joint randomisation; footnote 3 concedes "we here use true randomization for
simplicity. The same can be achieved using algorithmic randomness" (unproved). The
coverage step's opening move — "in particular `h̄_i` outbids infinitely often in rounds
in which `h̄_i` recommends some `a_i` and `α^c_{i,t} = a_i`" — needs the randomisation to
hit each `p_{a_i}` branch infinitely often among the outbidding rounds, which holds
almost surely, not always. The theorem is stated as plain existence. Recoverable
(probability-one existence implies existence) but only after building the probability
space. *Theorem-strength / modeling.*

Two mechanisms in that construction are worth recording, because they explain otherwise
puzzling features of the statement and they price the constructive half:

* **Why the theorem says "there exists `c′` arbitrarily close to `c`" rather than `c`.**
  The target profile is implemented "by deterministically cycling through the different
  strategies in the appropriate numbers" — a deterministic cycle realises only *rational*
  frequencies. So `c′` is a rational approximation of `c` inside `Δ(A₁ × A₂)`. That is a
  small, real formalization obligation (rational points are dense in the finite simplex,
  with the coordinates still summing to 1) which Mathlib does not supply off the shelf,
  and it is the whole reason the statement is an approximation.
* **How the coverage test sets are arranged.** In the `p_c` branch, "no hypotheses are
  tested"; in the `p_{a_i}` branch, "Player `i` … tests every hypothesis that estimates
  more than `v_i`" while player `−i` best-responds. So the test sets are exactly the
  punishment rounds, and coverage holds because on those rounds the tested hypothesis
  receives at most `max_{a_i} min_{a_{−i}} u_i` while having promised more than `v_i >`
  that. This is why the construction needs no auction and does not invoke Theorem 1 —
  and why it is the randomisation, not the mechanism, that carries the weight.

**E21. Theorem 1's part 3A is redundant.** See §E.1. *Redundant proof step.*

---

### Found by the independent fresh-context check

The claims above were re-adjudicated by a reviewer who was given the paper and the claim
list but not this report or the Lean file (§M). All were confirmed. The reviewer also
found ten further defects of its own, four of which are more serious than anything in the
original list.

**E24. Theorem 5's headline conclusion is never proved.** §7 claims "the empirical
distribution of `(αᶜ₁, αᶜ₂)` converges to `c′`, i.e. for all `a`,
`1/T ∑_{t=1}^T 1[(αᶜ₁,αᶜ₂) = a] → c′_a`". The Appendix A.6 proof consists of the
construction, a no-overestimation paragraph, and a coverage paragraph. It **never argues
that the empirical distribution converges**, never identifies `c′`, and never shows `c′`
can be taken arbitrarily close to `c`. Those are the folk theorem's actual content. This
is missing mathematics, not missing formalization — and it is what downgrades the game
layer from GREEN/YELLOW to YELLOW. (The argument is not hard: the `p_c`/`p_{a_i}`
randomisation gives an i.i.d. round-type sequence, so the empirical distribution
converges a.s. by the SLLN to a mixture whose `c`-component has weight `p_c`, and `c′` is
that mixture. But it has to be written, and it needs the probability layer.) *Genuine
mathematical gap — the headline claim.*

**E25. Theorems 4 and 9 are missing the efficient-identifiability assumption that
Theorems 3 and 8 carry.** Theorem 3 says "We require also that the `a_t` are efficiently
identifiable from the sets `DP_t`", and Theorem 8 repeats it. Theorem 4 (tex 420) and
Theorem 9 (tex 1188) do not — yet both proofs construct a hypothesis "that … recommends
`a_t`" and need it to lie in the covered e.c. class. Without the assumption the
constructed hypothesis need not be in `H` and the proof collapses. *Missing hypothesis,
in two theorems.*

**E26. Lemma 7 is malformed as printed.** `max_{σ_i ∈ Δ(A_i)} min_{a_{-i} ∈ A_{-i}}
u_i(σ_i, σ_{-i}) = min_{σ_{-i} ∈ Δ(A_{-i})} max_{a_i ∈ A_i} u_i(σ_i, σ_{-i})`: the
left-hand side binds `a_{-i}` but the body mentions `σ_{-i}`; the right-hand side binds
`a_i` but the body mentions `σ_i`. Both bound variables are free in the body on both
sides. And "Let `(A₁, A₂, u₁, u₂)` be **any** game" invites a general-sum reading of a
statement that is only true as minimax for the zero-sum game `(u_i, −u_i)`. Combined with
E11 — the lemma is never used and carries no `\label`, so it is not even referenceable —
the right disposition is: **delete it from scope**. *Malformed + unused.*

**E27. Definition 10 defines computable randomness, not Schnorr randomness.**
Definition 9 says `d` succeeds on `w` if `limsup d(w₁…w_n) = ∞`; Definition 10 forbids
success by any computable `d`. Schnorr randomness additionally requires success to be
*fast* relative to a computable order function; without that clause the notion defined is
computable randomness, which is strictly stronger. The section title, the name, and the
citations [26, 1, 33, 30] are all misapplied. Theorem 9 is presumably still true (the
notion is stronger, so the hypothesis is stronger), but it is a theorem about a different
concept from the one it names. *Definitional misnaming with a citation error.*

**E28. The martingale in Appendix E is not well-defined on `B*`.** Definition 9 requires
`d : B* → [0,∞)`. The proof defines `d` by cases on "whether `T` is not in `M`" — but its
argument is the *compressed* subsequence `(r_t)_{t<T : αᶜ_t = a_t}`, from which the real
time `T` is not recoverable, and it is specified only along prefixes of the actual reward
sequence rather than on all of `B*`. "Clearly, `d` thus defined is a martingale that is
computable based on `ᾱ, M`" is carrying the whole construction. *Genuine gap.*

**E29. Theorem 5's converse does not literally follow from Theorem 3 as stated.**
Appendix A.6 says it "follows directly from Theorem 3", but Theorem 3 is stated for a
BRIA "for `DP, r̄` and **the set of e.c. hypotheses**", whereas Theorem 5's converse
assumes only that `H_i` "contain at least the constant-time deterministic hypotheses".
The substance is fine — Theorem 3's proof needs only the single hypothesis `(a_t, L_t)` to
be covered — but the printed implication does not typecheck. **This is exactly the defect
the spike's `theorem3_core` fixes by construction**: it takes an index `i` rather than a
class, so the constant-hypothesis instance applies directly, which is why
`theorem5_converse` compiles as a one-line corollary. *Statement/proof mismatch, repaired
by the right representation.*

**E30. Theorem 5's construction misdescribes what is tested.** "Player `i` … tests every
hypothesis that estimates more than `v_i`." By Definition 4 a round `t` tests only
hypotheses with `hᶜ_{i,t} = αᶜ_{i,t} = a_i`; a hypothesis promising more than `v_i` but
recommending a different action is not tested that round. The coverage argument later
silently uses the correct, restricted version. *Typo in the construction, corrected
implicitly.*

**E31. `H`'s countability is asserted in Definition 7 and dropped in Theorem 5.**
Definition 7 writes `H = {h₁, h₂, …}` and hangs the test-set list `M₁, M₂, …` off that
enumeration. Theorem 5 assumes "any sets of hypotheses `H₁, H₂`", which need not be
countable — in which case Definition 7's `M₁, M₂, …` is undefined. The spike's `IsBRIA`
indexes by an arbitrary `ι`, which makes the uncountable case well-formed; Theorem 1
separately needs `ι = ℕ`. *Missing hypothesis / representation mismatch.*

**E32. Appendix B repeats the Definition 8 normalization slip.** One line establishes
`(1/|M_{i,≤T}|) l_T = (1/|M_{i,≤T}|) ∑_{t∈M_{i,≤T}} r_t − (μ_t − ε)`; the next asserts
`∑_{t∈M_{i,≤T}} r_t − (μ_t − ε) → ε` with the `1/|M_{i,≤T}|` dropped. As written the
limit is `+∞`, not `ε`. Same family as E6. *Typo, but the second instance of the same
confusion.*

**E33. A cluster of index and wording slips**, none load-bearing individually, listed so
a formalizer does not stop to wonder: `h_b(t)` is introduced as "**the set** of active
hypotheses" and then used as a number throughout; part 4 says "compute a **minimum** of a
finite set in line 2" where display (2) is an `arg max`; the wealth recursion accumulates
`∑_{n=1}^{T−1} A(n,i)` but both displays write `∑_{n=1}^{T}`; Theorem 8's conclusion
prints `∑ r_r/T` for `∑ r_t/T`; Theorem 4's display carries a stray "w.p. 1" under a
limit arrow in a theorem with no probability space, and indexes objects as `M_i, h̄_i`
though the proof introduced them as `M` and `h̄_{a,ε}` (copy-paste residue from Appendix
B); Theorem 9 defines `M_ε` and then uses only `M`, and re-binds `ε` to a different value
mid-proof.

**E34. The conclusion overclaims.** §9: "we demonstrated the theory's utility by using it
to **justify Nash equilibrium play**." The paper proves a folk theorem about *correlated*
strategy profiles and a pure-maximin lower bound. Nash equilibrium is never established —
and is listed two sentences later as open: "Do the frequencies with which BRIAs play the
given pure strategies of a game converge to mixed Nash and correlated equilibria?"
*Overclaim in prose, not in a theorem; relevant only to how the formalization's README
should describe the paper.*

---

## H. External dependencies

| Dependency | Needed by | Status at the pin | Classification |
|---|---|---|---|
| von Neumann minimax (Lemma 7) | nominally Thm 5 | **absent from Mathlib entirely** — there is no `Mathlib/GameTheory`, no normal-form games, no Nash, no minimax. `Mathlib/Order/GameAdd.lean` is unrelated. | **(4) avoidable** — the printed proof uses only pure maximin (E11). Do not prove minimax. |
| SLLN for independent, *non*-identically-distributed bounded variables, along a predictable selection | Thm 8 | `ProbabilityTheory.strong_law_ae` exists but requires `IdentDistrib`. The martingale library is complete (`Probability/Martingale/{Convergence,OptionalStopping,BorelCantelli,Upcrossing}`). **Kronecker's lemma is not in Mathlib.** | **(3) substantial but bounded** — derivable from martingale convergence + Kronecker; budget the Kronecker lemma and the non-iid SLLN as new work. |
| Cesàro convergence | Def 2, Thm 3, allowance req. (ii) | `Filter.Tendsto.cesaro` / `.cesaro_smul`, `Analysis/Asymptotics/SpecificAsymptotics.lean` | **(1) in Mathlib** |
| p-series / harmonic divergence | allowance schedule | `Real.summable_one_div_nat_pow`, `Real.not_summable_one_div_natCast`, `not_summable_iff_tendsto_nat_atTop_of_nonneg` | **(1) in Mathlib** |
| divergence along a subsequence | Def 6 | `atTop ⊓ 𝓟 B` + `Nat.frequently_atTop_iff_infinite` + `frequently_iff_neBot` | **(1) in Mathlib** |
| algorithmic randomness (vMWC, Schnorr) | Defs 8–10, Thms 4, 9 | absent everywhere | **(2) small bespoke definitions** — but see E15: the *quantifier* is the problem, not the analysis. |
| complexity theory: a counted machine model, an `O(g)` class, a c.e. enumeration with a universal simulator, time lower bounds | Thms 1b/1c, 2 | Verified at the pin: `Turing.TM2ComputableInPolyTime` (`Computability/TuringMachine/Computable.lean:179`) exists but its **composition closure is an open `proof_wanted`** at line 284 of that same file — Mathlib itself flags that the class has no theory. And `Turing.Respects` (`Computability/StateTransition.lean:150`) is defined through reflexive-transitive closure, so every simulation theorem in Mathlib discards step counts *by construction*. LI's own memo prices the retrofit at 8–15 months / 8–13k lines *for polynomial time alone* and marks the lower-bound direction "do not attempt". | **(3) research-scale — this is the kill criterion** |

No third-party Lean library was found that helps. (The PFR-style vendoring question does
not arise: there is nothing to vendor.)

---

## I. Full-project estimate

Anchors: **Cartesian Frames** = 60 numbered nodes, node-complete, no modeling
substitutions. **Finite Factored Sets** = 96 in-scope nodes, 14 files, complete.

| Tranche | Contents | Estimate |
|---|---|---|
| **1. Extensional core** | Defs 1–7, Lemma 6, Theorem 1a, Theorem 3, Theorem 5-converse, the asymptotic toolkit, non-vacuity witnesses — plus FAF completion overhead: provenance annotations, node checker (with the `\extendedonlybit` stripping), trust-surface entry, consumer API, client tests, adversarial audit, read-through. | **0.25–0.4 FFS** ≈ **0.4–0.6 CF**. The mathematics is already in `Spike.lean`; almost all remaining cost is the completion apparatus, not proving. |
| **2. All mathematical theorems, complexity abstracted** | Adds Theorem 4 in full, Theorem 8, Theorem 9 (martingales over `B*` + Schnorr), and Theorem 5's constructive half. Binding constraints: a probability space and empirical-frequency layer for Theorems 5 and 8; the non-iid SLLN along a predictable selection (+ Kronecker) for Theorem 8; a bespoke martingale/Schnorr layer for Theorem 9; a **ruling on Definition 8** (E6) before Theorem 4 means anything; and — the item the fresh-context check added — **supplying the folk theorem's empirical-distribution argument, which the paper does not contain** (E24), plus repairing Definitions 9/10 (E27) and the Appendix E martingale (E28). | **+0.7–1.2 FFS** (raised from +0.5–0.9 by E24, E27, E28). Cumulative: **0.95–1.6 FFS** ≈ **1.5–2.4 CF**. |
| **3. Literal computational and runtime claims** | Theorem 1b, Theorem 1c, Theorem 2 at paper strength, the "e.c." closure conditions of Theorems 3/4, and Definition 8's selector quantifier. Requires: a counted machine model; an `O(g)` class parametric in `g`; a c.e. enumeration with a cost-accounted universal simulator; a promise representation with decidable order; an input-size convention; and — for Theorem 2 — a genuine **time lower bound**. | **+2–4 FFS minimum, realistically research-scale.** LI's boundary memo prices the machine-model retrofit at 8–15 months for polynomial time alone, and BIR needs strictly more (parametric `g`, and the lower-bound direction LI declared out of scope). **Do not attempt.** |

Restated in the format the brief asked for:

> extensional paper: **0.3 FFS**
> all mathematics with complexity abstracted: **1.2 FFS** — and this figure now includes
> writing mathematics the paper does not contain (E24)
> paper-strength computational theorems: **+3 FFS of new infrastructure, and that is a
> floor, not an estimate**

---

## J. Critical path

0. **Settle the three source defects that are not formalization questions**, ideally by
   asking the authors: Definition 8's missing normalization (E6), Theorem 5's unproved
   empirical-distribution claim (E24), and Definition 10's misnaming (E27). Each changes
   what there is to formalize, not merely how.
1. **Rule on Definition 8 first.** Adopt the averaged reading, record E6 in
   `paper-errata.md`, and note that the printed reading makes Theorem 4 vacuous. Nothing
   in the randomness layer should be written before this ruling, because the printed
   reading is *provably* the wrong one. In the same pass, **drop Lemma 7 from scope**: it
   is unused (E11) and malformed as printed (E26).
2. **Land the extensional layer** (Defs 1–7 with the three reading lemmas, Lemma 6, the
   asymptotic toolkit, the non-vacuity witnesses). Straight lift from `Spike.lean`.
3. **Theorem 3**, with the class-membership condition as an explicit named hypothesis.
   It is the engine for Theorems 4, 5-converse, 8 and 9; landing it early pays four
   times.
4. **Theorem 5's converse half** — free once step 3 exists, and it retires the minimax
   question (E11) with compiled evidence rather than a promise.
5. **Theorem 1a**, the extensional auction. It is a *leaf* (see §B): nothing depends on
   it, so it can slot anywhere, but doing it here keeps the existence theorem alongside
   the criterion it satisfies. Includes the E1 attainment lemma and the E2 repair, both
   disclosed as corrections in `paper-errata.md`.
6. **Theorem 2's extensional core**, with the complexity-preservation step isolated as
   the named `DiagonalObligations` interface. This is where the disclosure discipline
   starts.
7. **Write the boundary memo** — the BIR analogue of
   `LogicalInduction/notes/boundary-efficiency-model.md` — *before* attempting any of
   Theorem 1b/1c/2's computational content, so the scope decision is made on paper
   rather than discovered mid-build.
8. **Theorem 4** on the corrected Definition 8, with the selector's decidability as an
   explicit hypothesis (never a class named `EfficientlyDecidable`).
9. **The probability layer**: probability space, empirical frequencies, Kronecker,
   non-iid SLLN along a predictable selection. Then **Theorem 8**, then **Theorem 5's
   constructive half** (as an almost-sure statement, disclosed per E12) — including the
   empirical-distribution argument the paper omits (E24), which must be written and
   attributed as *supplied*, not formalized.
10. **Theorem 9** (martingales over `B*`, Schnorr randomness) last — it is self-contained
    and the least connected.
11. **Stop.** Tranche 3 is out of scope; state the computational claims relative to named
    interfaces and disclose.

---

## K. Kill criteria

All four of the brief's example criteria are **met**, which is why the recommendation is
to scope rather than to proceed:

1. **Faithfully formalizing `O(g(t))` requires building a generic complexity theory
   larger than the paper.** Confirmed. Mathlib's poly-time class has zero theory and no
   timed simulation exists; LI's fuel model is hardwired polynomial and its lower
   calibration is open; BIR additionally needs a *time lower bound* (Theorem 2), the one
   direction LI's boundary memo marks "do not attempt".
2. **The complexity claim is underspecified without a machine model.** Confirmed, and
   worse: it is underspecified *with* one, because the input-size convention (E17), the
   promise representation (E18) and the meaning of "efficiently identifiable" (E17) are
   all absent, and the bound itself does not typecheck as stated (E16).
3. **Theorem 5 depends on a large unformalized game-theory theorem.** **Refuted** — this
   was the criterion the spike expected to trip and it does not. Lemma 7 is never used
   (E11).
4. **vMWC randomness relies on an undefined notion of accessible information.**
   Confirmed (E15), *and* the definition as printed is unsatisfiable in the paper's own
   motivating case (E6).

Two additional criteria this spike would add:

5. **A headline definition that is provably vacuous is a source problem, not a
   formalization problem.** E6 must be resolved by ruling — ideally by asking the
   authors — before Theorem 4 is registered as formalized at any strength.
6. **A headline theorem whose conclusion the paper never argues is a source problem
   too.** Theorem 5's empirical-distribution claim (E24) has no proof in the paper. FAF
   can supply one, but supplying it is *doing the authors' mathematics*, which under this
   repository's provenance rules must be marked as such rather than recorded as
   formalizing a paper result. If we are not willing to write and own that argument,
   Theorem 5's constructive half should be out of scope.

---

## L. Recommendation

**Formalize the extensional core only, now; build no prerequisite; postpone the
computational layer indefinitely.**

Concretely:

* Register BIR with `status: "in-progress"` and scope it, by ruling, to Tranches 1 and 2.
* State Theorems 1, 2, 3, 4 and 9 at **extensional strength**, with every computability
  and complexity condition appearing as an *explicit, named hypothesis* in the theorem
  statement — exactly as `theorem3` carries `∃ i, (H i).choice = a ∧ (H i).estimate = L`
  rather than a predicate called `EfficientlyComputable`. This is the difference between
  an honest reduction and an oversold stub, and the spike is the demonstration that the
  honest version is achievable.
* Record Theorem 1c as **out of scope by ruling, with the source defect (E16) as the
  reason**, in the README and the errata. Do not declare an axiom for it.
* Raise E6, E24 and E27 with the authors before scoping Theorem 4, Theorem 5's
  constructive half, or Theorem 9. All three are cheap to fix at source and expensive to
  work around downstream.
* Write the boundary memo before anyone is tempted.

The paper is worth formalizing. Its extensional half is clean, short, genuinely
interesting, and now largely written. Its computational half is not presently
formalizable faithfully by anyone, and the honest thing is to say so at the statement,
in the README, and in the trust surface — which is the discipline this repository
already has.

---

## M. Fresh-context adversarial audit

Per §17 of the brief, a fresh reviewer was given the compiled spike and the paper, denied
this report's conclusions, and asked: *what would make this spike falsely classify BIR as
easy?* Findings and dispositions are in the next section.
