# Logical Induction

A Lean 4 formalization of Garrabrant, Benson-Tilsen, Critch, Soares, Taylor,
[*Logical Induction*](https://arxiv.org/abs/1609.03543) (arXiv:1609.03543v5).

The paper's three pieces are all here. The **logical induction criterion** (§3) is stated at
the paper's own quantifier — no polynomial-time trader exploits the market. The **§4 property
tail** — convergence and coherence, provability induction, timely learning, calibration and
unbiasedness, pseudorandomness, logical relationships, non-dogmatism and its Occam forms,
universal-semimeasure domination, closure under conditioning and perturbation, expectations,
introspection, paradox resistance, self-trust — is proved for *every* logical inductor, and
then instantiated over a concrete one. The **§5 existence theorem** is proved in the paper's
full sense: the algorithm is built (market maker via a from-scratch Sperner/Brouwer fixed
point, budgeter, trading firm over a universal trader enumeration) and shown to satisfy the
criterion. Zero `sorry`, zero `axiom` declarations; every public endpoint reports only
Lean's standard `propext`, `Classical.choice`, `Quot.sound`, enforced by the build.

Formalizing it turned up six defects in the paper, recorded with their repairs in
[`notes/paper-errata.md`](notes/paper-errata.md). One is not a repairable slip: **closure
under finite perturbations is false as printed**, and is refuted here, with a corrected
finite-support theorem proved in its place.

## How logical induction is modeled

### The objects

| Paper | Lean |
|---|---|
| sentence φ of the market language | `Sentence` — Foundation's propositional `Formula` |
| the market 𝕡, prices ℙₙ(φ) | `History` — day and sentence to a price in `[0,1]` |
| deductive process `D₁ ⊆ D₂ ⊆ …` (`def:dedproc`) | `DeductiveProcess` |
| a world consistent with stage `n` | `PCWorld`, `PCWorld.ConsistentWith` |
| expressible feature (`def:tf`) | `EF` — a reified expression in prices and rationals, with a denotation (`dd:dsl`) |
| trading strategy for day `n` (`def:tradestrat`) | `Strategy` — a finite list of (feature, sentence) trades |
| trader (`def:trader`) | `Trader` — a day-indexed family of strategies |
| exploitation (`def:exploitation`) | `Trader.Exploits P DP` |
| affine combination of sentences (`def:affcomsen`) | `AffineCombination` |
| logically uncertain variable (`def:luv`) | `LUV`, with `LUV.expect` its market expectation |
| the criterion (`def:lic`) | `IsMachineLogicalInductor` |
| the algorithm (`def:lia`) | `LIA`, `liaHistory` |

Limit vocabulary — `≈ₙ`, `≳ₙ`, `≲ₙ`, `ConvergesTo` — lives in one module,
`Framework/Asymptotics`, built on Mathlib's `Tendsto` and `∀ᶠ n in atTop` (`dd:asymp`).

### Efficient computability, and why there are two classes

The paper's `def:ec` is ordinary machine polynomial time, and so is the class the criterion
quantifies over: `MachineEfficientTrader Tr` says some function in `Complexity.FP` maps the
*unary* day `n` to a word decoding to `Tr`'s day-`n` strategy. `IsMachineLogicalInductor` is
`def:lic` over that class, and it is what the construction discharges
(`LIA_isMachineLogicalInductor`). The trading firm genuinely enumerates that class —
`enumeratedTrader` is both sound (`enumeratedTrader_machineEfficient`) and covering
(`exists_enumeratedTrader_eq`) — so the enumeration is an enumeration *of* machine-efficient
traders, not merely one that happens to cover them, and LIA satisfies LIC at the paper's own
quantifier.

Exhibiting a `Complexity.FP` witness by hand is unpleasant, so the development also carries a
compositional **certificate calculus**: `EfficientlyComputable` / `PolyFueled` (`dd:fuel`) ask
for a `Nat.Partrec.Code` pair emitting the trade stream inside a polynomial fuel bound on
Mathlib's `evaln`. This is *certification technology*, not a rival definition of efficiency,
and the whole relationship between the two is one theorem:

```text
EfficientlyComputable Tr  ──EfficientlyComputable.toMachine──▶  MachineEfficientTrader Tr
```

proved through a real `evaln` → Turing-machine compiler with concrete register and step
bounds. **The converse is neither proved nor claimed**, and nothing paper-facing needs it: a
fuel certificate is a sufficient route into the paper's class, and every concrete exploiting
trader in the §4 proofs is built that way. `IsLogicalInductor` — the criterion over the
fuel-certified class — is kept as a compatibility interface, since the §4 theorems are stated
against it and `IsMachineLogicalInductor.toIsLogicalInductor` carries all of them to a machine
logical inductor unchanged.

A second question about metering is settled inside the certificate layer, and it matters
because getting it wrong silently narrows the paper's class. `def:ec` bounds how many symbols
a poly-time writer *emits*; it does not bound their magnitudes. So the certificate classes the
property tail takes are the **write-out** ones — `BigSentenceCodes` for sentences, `BigDigits`
for naturals, `DigitRatCodes` for rationals, `DigitMachineCodes` for machine codes, with
`BigTokenStream` / `BigSpliceStream` on the emission surface — under which `δₙ = 2⁻ⁿ`, an
`n`-bit string, and the Gödel code of a sentence naming an `n`-bit machine are all admissible,
as they are for the paper. Value-bounded metering would exclude them, and that exclusion is
proved rather than argued (`bigDigits_two_pow_not_polyNatCodes`,
`not_polySentenceCodes_bitPrefixSentence`, and three more). One retention is left on the
paper-facing surface and is disclosed at its node: `thm:scon`'s conditioning certificate asks
for the narrower `RpnSentenceCodes` on the *condition*, which restricts which conditioning
data a caller may supply and does not touch what is concluded.

The paper is explicit, immediately after `def:ec`, that its framework "is not wedded to this
definition" and that a different efficiency class with suitable closure properties yields
logical inductors with different runtime/strength trade-offs (tex:757). So the choice of class
is a variation the paper anticipates. What is *not* thereby licensed is any claim that the
fuel class contains the paper's; the `dd:fuel` model card in `Framework/Computable.lean`
states that open question, and it is why the machine class, not the fuel class, is what the
criterion quantifies over.

### Sentences, the market language, and the arithmetic theory

The market prices propositional sentences. The paper's background theory Θ is first-order, and
it enters through explicit interfaces rather than by making the market's language first-order.
The two layers meet in the deductive process: `paperTheoryDP T` enumerates Θ's theorems as
propositional atoms, and `theoremDP T` is the literal provability/quotation stream the quote
codes are read off.

First-order claims are therefore *compiled* into the market. A day-`n` claim's subject matter
is written into its sentence as an argument, spelled by the compact Horner `ℒₒᵣ` term
`binNumeral` (`O(log v)` symbols, so `def:ec`'s write-out metering can pay for it); what is
*represented* inside Θ is universal and fixed once per theorem — the r.e. `universalHaltingSchema`
on the unbounded lane, one `γ` per horizon program on the bounded lane. That the family
genuinely separates its data is proved, not assumed
(`haltingArgClaimSentence_ne_of_halts_ne`, `representedClaimSentence_ne_of_runValue_ne`).

Formula families are metered on the language the paper actually writes in. The paper's
connectives include `⟺` as a primitive (tex:560); Foundation's `Semiformula` is a
negation-normal-form datatype with no such constructor, so metering the normal form would
charge exponentially for a left-nested biconditional chain. Nothing here meters the normal
form: `ArithSource` carries the paper's primitives, `def:ec`'s condition is
`PolyArithmeticSourceSeq` — one emitted token per node *as the paper writes it* — and
normal-form expansion happens inside the parser and is never charged. That two-layer
architecture is what `dd:nnf` labels, and the inclusion is proved strict rather than asserted.

**LUVs are presented by thresholds.** A logically uncertain variable reaches downstream results
as its family of threshold sentences `⌜X > r⌝`. This is a representation interface, not a
substitution: the paper's literal first-order object exists as `PaperLUV` — an actual
one-variable arithmetic formula carrying object-level Θ-proofs of unique existence and `[0,1]`
membership — and compiles into the carrier, so results stated against the carrier apply to
more families than the paper's, with `PaperLUV` showing that the paper's own are among them.
The frontend is inhabited at concrete families across the range the paper writes
(`unitFracPaperLUVSeq` at `1/(n+1)`, `dyadicPaperLUVSeq` at `2⁻ⁿ`). What remains charged here
is narrow and stated where it bites: a `PaperLUV`'s object-level value is named by a
numerator/denominator pair code rather than by a canonical rational arithmetic inside `ℒₒᵣ`.

### What is assumed about the background theory

The paper's §2 fixes one standing assumption on Θ, and the arithmetic-theory family is stated
at it. `RepresentsComputations T` (`Framework/RepresentsComputations.lean`) is that assumption
verbatim: for every total computable `f` there is a Θ-formula `γ_f` with
`y = f n ↔ Θ ⊢ ∀ν (γ_f(n̄, ν) ⟺ ν = ȳ)`. It is a condition on what Θ *derives*, with no
reference to truth in ℕ, and it already forces Θ consistent (`RepresentsComputations.consistent`,
the paper's own tex:604 observation). Consuming the class never uses semantics; *verifying* it
for a particular theory does, and `representsComputations_of_peanoMinus` registers instances at
`𝗣𝗔⁻`, `𝗜𝚺₁` and `𝗣𝗔`, so a client instantiating at one of those supplies nothing.

Three further binders appear, and they are of two different kinds:

* **`[T.Δ₁]`** — a `Δ₁`-definable axiom set, where the paper asks only that Θ be computably
  enumerable. This is representation infrastructure: by Craig's trick every c.e. theory has a
  deductively equivalent `Δ₁` axiomatization, and every statement here is about `T ⊢ ·`, which
  such a re-axiomatization preserves. That transfer step is not formalized here, and that is
  the honest residual. What consumes the binder is the enumeration of Θ's theorems, never a
  step of a paper proof.
* **`[𝗜𝚺₁ ⪯ T]`** — likewise infrastructure, on three endpoints only, where the substrate's
  Gödel fixed point (`thm:lp`) and rational-cut arithmetic are indexed at `𝗜𝚺₁`.
* **`[𝗣𝗔⁻ ⪯ T]`** — a **genuine, if small, strengthening**, and the one item here that is not
  infrastructure. It is *not* implied by "Θ represents computations": that premise yields
  `Θ ⊬ n̄ = m̄` for `n ≠ m` but never `Θ ⊢ n̄ ≠ m̄`, and Robinson's R represents every
  computable function without containing `𝗣𝗔⁻`. Two steps spend it — moving provability across
  the compact numeral spelling that `def:ec` forces, and the object-level exclusivity of the
  quotation schema's two fibers. What it bought is worth the trade and is the reason it is
  here: it let **Σ₁-soundness be removed from the entire development**. No declaration in
  `LogicalInduction/` carries a soundness instance binder — the paper treats soundness as a
  further assumption it explicitly declines (tex:2673), and nothing here takes it. Every theory
  in the paper's intended range satisfies `𝗣𝗔⁻`: `𝗜𝚺₁`, `𝗣𝗔`, `𝗣𝗔 + Con(𝗣𝗔)`, and the
  arithmetic of ZFC.

Two places additionally need a *counting convention*, because the paper fixes none and one is
unavoidable. `dd:symbolcount` is §4.10's symbol measure on derivations (`dSize`, with the bound
inclusive, as the paper's "ν or fewer symbols" is); `dd:machinetheory` is how a machine is read
as a theory in `thm:incons` (`theoryOf`, with admission of an output as an axiom name *decided*
rather than assumed). Both are conventions rather than substitutions — each can only
over-count or under-admit, and the truth of every instance is proved independently of it — and
both are stated in full at their modules and in the glossary in `LogicalInduction.lean`.

### One market, and how to read the closed forms

The paper builds one market over one deductive process and prices every §4 property in it. So
does this development: every canonical endpoint whose statement names a market names
`liaHistory (paperDP T)`, where `paperDP T` is the union of the theorem enumeration and the
literal quotation stream. There is **one documented exception**: `thm:ccee` is priced over
`canonicalCCEEDP T`, by ruling, because the fixed enlarged language that lane needs for exact
semantic multiplication puts it outside the shared one.

The §4 content is carried in two layers, and both are inventoried. The **generic carriers**
(`lic_provind_true`, `lic_introspection`, …) quantify over any market with
`[IsLogicalInductor P DP]` and take their day-data through constructed interfaces; they hold
the paper's universal quantifier. The **closed forms** (`_unconditional` / `_closed`) discharge
every one of those interfaces over the constructed inductor, and are the fully-assembled
corollaries a client can apply with no inputs beyond the theory instances. So when a closed
form names `LIA`, the universal statement is the generic carrier one import away; that is the
reading of the two layers, not a loss.

One non-vacuity caveat is worth stating because it is easy to miss. The *input-free* universal
semimeasure endpoints (`lic_domination_everyLowerSemicomputable_unconditional`,
`lic_strict_domination_universalSemimeasure_unconditional`) hold over the constantly-empty
deductive process, where atom independence and realizability are discharged by "no stage
asserts anything". They are real theorems, but the paper frames those results as fresh symbols
added *to* a theory, so cite instead the substantive layer over `paperDP T`
(`lic_domination_dovetailSemimeasure_paperDP`,
`lic_domination_everyLowerSemicomputable_paperDP`) when asked whether the premises are
non-vacuously satisfiable.

## What differs from the paper

* **Closure under finite perturbations (`thm:ifp`) is false as printed, and is refuted here.**
  The paper has finitely many changed *days*, not finitely many changed `(day, sentence)`
  constants — and a single day is an infinite pricing function, so it can carry unbounded
  computational advice that an efficient trader reads off historical price features without
  ever computing it. `not_overgeneral_ifp` proves the unrestricted statement false at the
  paper's own quantifier. The corrected theorem is finite *support*, which is exactly the case
  in which the appendix's "hard-code the constants" step is literally valid, and is strictly
  stronger than the printed tail agreement. Details and the counterexample mechanism:
  [`notes/paper-errata.md`](notes/paper-errata.md), PE1.
* **Two printed statements are defective in repairable ways and are proved corrected**
  (`thm:prand`, `thm:recurringunbiasednessexp`). Three further printed defects — a decidability
  claim, a missing monotonicity assumption, and a printed proof that does not follow from its
  printed hypotheses — are recorded with the repository's response at each. All six are in the
  errata ledger.
* **Some statements come out stronger than printed.** `thm:scon` is proved at the machine
  quantifier in all three forms; `thm:lp` *constructs* the paradoxical sequence the paper
  merely posits; §4 properties that the paper states only for a hypothetical inductor are
  additionally instantiated over the concrete one built here; and the presentations that
  `thm:dus` and `thm:strict` quantify over are constructed rather than assumed.
* **Genuine modeling boundaries**, all disclosed above and at their statements: the fuel
  calculus is a certification device whose relation to polynomial time is one-directional; the
  corrected `thm:ifp` retains a `Recognizable` condition on the syntax of the moved sentences,
  standing for two `Complexity.FP` primitives this toolkit lacks (integer square root; a
  structured-payload parser) — the unrestricted finite-support statement is, as far as this
  development can tell, true, and is unproved here; the fuel-class perturbation certificates
  `EfficientPrefixPatch` and `FiniteSupportPatch` are **uninhabited**, which is why the machine
  form is the one to use; and `thm:ccee`'s `dd:mesh` reading carries a per-day reflection slack
  in an explicit `slack` field, with an exact (`slack = 0`) endpoint available over the renamed
  process — the two are incomparable, and you choose by which market you need.

For the theorem-by-theorem correspondence and the exact strength classification of every node,
see [`scripts/coverage-classification.md`](../scripts/coverage-classification.md) and the
generated read-through guide [`docs/trust-surface.html`](../docs/trust-surface.html).

## How to use it

```lean
import LogicalInduction.API
```

That is the supported interface for downstream theoretical work: the semantic objects, both
efficiency notions and the bridge between them, the criterion, the §4 library, and the two
criterion-preserving transforms. `LogicalInduction/API.lean`'s module documentation is the map;
`APITests/LogicalInduction.lean` is a worked client session against it.

Deeper imports, and what each is for:

| Import | For |
|---|---|
| `LogicalInduction.Framework.RepresentsComputations` | stating your own theory's standing assumption |
| `LogicalInduction.Construction.Witnesses.R0Representability` | discharging it at `𝗣𝗔⁻`, `𝗜𝚺₁` or `𝗣𝗔` |
| `LogicalInduction.Construction.Witnesses.ComputationRepresented` | the §4.10 endpoints over `liaHistory (paperDP T)` |
| `LogicalInduction.Construction.LIACompiler` | the §5 construction and its existence endpoints |
| `LogicalInduction.Construction.Witnesses.ArithmeticSource` | building a new literal first-order LUV family |
| `LogicalInduction` | the whole development |

A handful of names to orient by:

* `MachineEfficientTrader` — `def:ec`, the paper-facing trader class.
* `IsMachineLogicalInductor` — `def:lic` over that class. `IsLogicalInductor` is the
  compatibility form the §4 theorems are stated against; state new consequences of the
  criterion against *it*, so they are available at both.
* `EfficientlyComputable.toMachine` — the one bridge from a fuel certificate into the class.
* `LIA_isMachineLogicalInductor` — the constructed inductor satisfies the criterion.
  `exists_machine_logical_inductor` is the bare existence statement, and
  `exists_computable_beliefSequence_logical_inductor` the form that hands back a computable
  sequence of explicit finite-support rational belief states.
* `lic_provind`, `lic_persistence_of_knowledge`, `lic_lex_tendsto_zero`, … — the §4 library,
  named after the paper's labels.
* `lic_conditioned_machine` — closure under conditioning (`thm:scon`).
* `lic_iff_of_recognizableSupportPerturbation` — the corrected `thm:ifp`.

## Where the accounting lives

This file explains the mathematics and how to start using it. The rest is deliberately
elsewhere, each artifact answering one question:

* **Which Lean statement carries which paper node, and how strong is it?** —
  [`scripts/coverage-classification.md`](../scripts/coverage-classification.md), machine-checked
  against the endpoint inventory, and rendered for reading at
  [`docs/trust-surface.html`](../docs/trust-surface.html).
* **What does each endpoint depend on?** — `AxiomAudit.lean`, which enumerates the public
  surface and fails compilation on any axiom regression or disappearance.
* **What is wrong with the paper?** — [`notes/paper-errata.md`](notes/paper-errata.md).
* **Where exactly does an implementation boundary sit?** — the declaration's own docstring and
  its module header; `dd:*` design-decision labels are defined in the glossary in
  `LogicalInduction.lean`.

## Layout

* `Framework/` — §2–3: sentences, markets, features, traders, exploitation, the criterion,
  efficient computability, expectations, and the asymptotic vocabulary.
* `Properties/` — the §4 property tail, one file per theorem family.
* `Construction/` — the §5 existence proof, with `Construction/Witnesses/` holding the
  constructed representation machinery that discharges the property tail's interfaces over the
  concrete inductor.
