import ShannonInformation.API
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Spike: a renderable, manipulable calculus of approximate Bayes-net diagrams

Feasibility probe for `NaturalLatents/diagram-calculus/SPEC.md`.  **Not** a formalization
of *Natural Latents*, and not the proposed encoding — it exists to answer three questions
before anyone commits to a design:

* **Q1 / R2.1** — can nodes be split from variables so that one variable may sit at two
  nodes (`Y ← X → Y`)?  → `detDiagram`, `detInterp` below.  Yes, and cheaply.
* **Q2 / F2** — does the factorization `∏ᵢ P[Yᵢ | Y_pa(i)]` need measure-theoretic
  disintegration?  → `factorized` below.  **No**, not in the finite discrete case: it is
  pointwise arithmetic.  This is the cost finding.
* **Q3 / F3** — can a diagram render to TikZ mechanically?  → `render`.  Yes, ~40 lines.

The R3.2 acceptance test is **stated as a `Prop` and deliberately left unproved** — see
`AcceptanceTest` at the bottom and SPEC.md §7.  It is the design target, not an omission:
how cleanly it proves is the measure of whether an encoding is right.  This file is
`sorry`-free; the open goal is a `Prop`, in the same style as
`FiniteFactoredSets/Conjecture.lean`.
-/

namespace NLDiagramSpike

open Finset Real MeasureTheory ProbabilityTheory

/-! ## Finite discrete distributions

Deliberately bespoke and tiny.  Finding F2 is that the calculus does not need the vendored
measure-theoretic layer for its *semantics*; it needs it only for the entropy bridge. -/

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- A probability mass function on a finite type. -/
structure FinPMF (A : Type*) [Fintype A] where
  p : A → ℝ
  nonneg : ∀ a, 0 ≤ p a
  total : ∑ a, p a = 1

/-! ## Diagrams

A diagram is a parent map plus a **rank**, which is how acyclicity is witnessed.  Using a
rank rather than an abstract acyclicity predicate is a deliberate choice: the Frankenstein
rule's hypothesis is "there exists an ordering respecting the topological order of all the
diagrams simultaneously", and with ranks that hypothesis becomes a statement about
numbers rather than an existential over orderings. -/

/-- A Bayes-net diagram over a node type `N`.  Purely structural: no variables, no `ε`,
no layout.  Those are separate concerns by design (R4). -/
structure Diagram (N : Type*) [DecidableEq N] where
  parents : N → Finset N
  rank : N → ℕ
  parent_rank_lt : ∀ n, ∀ m ∈ parents n, rank m < rank n

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- A node is never its own parent — the first thing acyclicity should buy you. -/
theorem Diagram.not_self_parent (D : Diagram N) (n : N) : n ∉ D.parents n := fun h =>
  absurd (D.parent_rank_lt n n h) (lt_irrefl _)

/-! ## Interpretations — the crux (R2.1)

`var` assigns a random variable to each node and is **not required to be injective**.  That
is what lets `Y ← X → Y` be a diagram with three nodes and two variables, and it is what
makes the Dangly Bit Lemma statable at all. -/

/-- An interpretation of a diagram's nodes as random variables on a finite sample space.

**Spike simplification, and an open design question.**  `Val` is a *single* value type here,
so every node carries a variable of the same type.  The paper's nodes are heterogeneous
(`Λ` and `Xᵢ` need not share a value type), so the real encoding needs `Val : N → Type`.
That is deferred deliberately: it is orthogonal to the crux (R2.1) and it makes the example
constructions fight `fin_cases`, which cannot eliminate into `Type`.  Whoever designs the
encoding must decide how to carry per-node `Fintype`/`DecidableEq` instances — see the
prompt in `DESIGN-PROMPT.md`. -/
structure Interp (N : Type*) (Ω : Type*) where
  Val : Type
  valFintype : Fintype Val
  valDecEq : DecidableEq Val
  var : N → Ω → Val

attribute [instance] Interp.valFintype Interp.valDecEq

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- A joint assignment of values to every node. -/
abbrev Interp.Assign (ι : Interp N Ω) := N → ι.Val

instance (ι : Interp N Ω) : Fintype ι.Assign := Pi.instFintype
instance (ι : Interp N Ω) : DecidableEq ι.Assign := fun _ _ => Fintype.decidablePiFintype _ _

/-- The joint node-valued variable induced by an interpretation. -/
def Interp.joint (ι : Interp N Ω) (ω : Ω) : ι.Assign := fun n => ι.var n ω

/-- `P[Y_J = a_J]`: the probability that the nodes in `J` take the values `a` prescribes. -/
noncomputable def marginal (P : FinPMF Ω) (ι : Interp N Ω) (J : Finset N)
    (a : ι.Assign) : ℝ :=
  ∑ ω ∈ univ.filter (fun ω => ∀ n ∈ J, ι.var n ω = a n), P.p ω

theorem marginal_nonneg (P : FinPMF Ω) (ι : Interp N Ω) (J : Finset N) (a : ι.Assign) :
    0 ≤ marginal P ι J a :=
  Finset.sum_nonneg fun ω _ => P.nonneg ω

/-! ## The factorization — finding F2

`P[Yₙ | Y_pa(n)]` as a ratio of marginals, with the usual `0/0 = 0` convention supplied by
`Real`'s division.  No kernels, no disintegration: the whole semantics of a diagram is
elementary arithmetic once the sample space is finite. -/

/-- The conditional probability of node `n`'s value given its parents' values. -/
noncomputable def condFactor (P : FinPMF Ω) (ι : Interp N Ω) (D : Diagram N)
    (a : ι.Assign) (n : N) : ℝ :=
  marginal P ι (insert n (D.parents n)) a / marginal P ι (D.parents n) a

/-- `∏ᵢ P[Yᵢ | Y_pa(i)]` evaluated at an assignment — the distribution the diagram asserts. -/
noncomputable def factorized (P : FinPMF Ω) (ι : Interp N Ω) (D : Diagram N)
    (a : ι.Assign) : ℝ :=
  ∏ n, condFactor P ι D a n

/-- The induced distribution on assignments. -/
noncomputable def pushforward (P : FinPMF Ω) (ι : Interp N Ω) (a : ι.Assign) : ℝ :=
  marginal P ι univ a

/-- **The semantics (R3.1).**  `P` satisfies `D` under `ι` to within `ε` iff the KL
divergence from the pushforward to the diagram's factorization is at most `ε`.  This is the
paper's own definition, with the factorization built from `P` itself. -/
noncomputable def Satisfies (P : FinPMF Ω) (ι : Interp N Ω) (D : Diagram N) (ε : ℝ) : Prop :=
  ε ≥ ∑ a : ι.Assign,
    pushforward P ι a * Real.log (pushforward P ι a / factorized P ι D a)

/-- Satisfaction is monotone in the approximation budget (R3.3).  Trivial, but it is the
property every `ε`-bookkeeping step in Figure 9 silently uses. -/
theorem Satisfies.mono {P : FinPMF Ω} {ι : Interp N Ω} {D : Diagram N} {ε ε' : ℝ}
    (h : Satisfies P ι D ε) (hle : ε ≤ ε') : Satisfies P ι D ε' :=
  le_trans h hle

/-! ## Q1: the repeated-variable pattern typechecks

`Y ← X → Y` as three nodes and two variables.  Node `0` carries `X`; nodes `1` and `2` both
carry the *same* `Y`.  Nothing in the API objects, which is finding F1. -/

/-- The determinism diagram `y₁ ← x → y₂` on nodes `Fin 3`. -/
def detDiagram : Diagram (Fin 3) where
  parents := ![∅, {0}, {0}]
  rank := ![0, 1, 1]
  parent_rank_lt := by decide

/-- Its interpretation: **two distinct nodes, one random variable**.  Node `0` carries `X`;
nodes `1` and `2` both carry the *same* `Y`.  This is the pattern R2.1 exists to permit, and
an encoding that identifies nodes with variables cannot express it. -/
def detInterp {V : Type} [Fintype V] [DecidableEq V] (X Y : Ω → V) : Interp (Fin 3) Ω where
  Val := V
  valFintype := inferInstance
  valDecEq := inferInstance
  var := ![X, Y, Y]

/-- The repeated-variable property, stated so it cannot be lost by a later refactor: two
*distinct* nodes carry the *same* variable. -/
theorem detInterp_repeats {V : Type} [Fintype V] [DecidableEq V] (X Y : Ω → V) :
    (1 : Fin 3) ≠ 2 ∧ (detInterp X Y).var 1 = (detInterp X Y).var 2 :=
  ⟨by decide, rfl⟩

/-- The mediation diagram `X₁ ← Λ → X₂` (the paper's Figure 1) — same shape, but here the
three nodes carry three *different* variables.  Shape and interpretation are independent,
which is the point of the split. -/
def mediationDiagram : Diagram (Fin 3) := detDiagram

/-! ## Q3: rendering (R1)

A total `Diagram → String`.  Layout data (labels, the `ε` expression, group captions) is
passed separately so that `Diagram` stays purely semantic — the renderer consumes *the same
value the theorems are about* (R1.5), decorated for display. -/

/-- Display data for a diagram: node labels and the `ε` expression to print beneath. -/
structure Layout (N : Type*) where
  label : N → String
  eps : String
  caption : String

/-- Emit TikZ for a diagram.  Nodes are laid out by rank (rank = row), which is why the
rank field earns its keep twice. -/
def render (D : Diagram N) (L : Layout N) (nodes : List N) : String :=
  let nodeLine (n : N) : String :=
    "  \\node (" ++ toString (nodes.idxOf n) ++ ") at ("
      ++ toString (nodes.idxOf n) ++ ", -" ++ toString (D.rank n) ++ ") {$"
      ++ L.label n ++ "$};\n"
  let edgeLines (n : N) : String :=
    String.join ((nodes.filter (fun m => m ∈ D.parents n)).map fun m =>
      "  \\draw[->] (" ++ toString (nodes.idxOf m) ++ ") -- ("
        ++ toString (nodes.idxOf n) ++ ");\n")
  "\\begin{tikzpicture}[every node/.style={draw=none}]\n"
    ++ "  % " ++ L.caption ++ "\n"
    ++ String.join (nodes.map nodeLine)
    ++ String.join (nodes.map edgeLines)
    ++ "  \\node at (1, -2.2) {$\\varepsilon \\geq " ++ L.eps ++ "$};\n"
    ++ "\\end{tikzpicture}\n"

/-- Layout for the paper's Figure 1 (mediation). -/
def mediationLayout : Layout (Fin 3) where
  label := ![ "\\Lambda", "X_1", "X_2" ]
  eps := "\\varepsilon_{\\mathrm{med}}"
  caption := "Figure 1: the Mediation condition"

/-- Layout for the determinism diagram, showing the repeated label. -/
def detLayout : Layout (Fin 3) where
  label := ![ "\\Lambda", "\\Lambda'", "\\Lambda'" ]
  eps := "\\varepsilon_{\\mathrm{red}}"
  caption := "Determinism: Lambda' <- Lambda -> Lambda'"

-- Sample output is committed as `rendered/mediation.tex` and `rendered/determinism.tex`.
#eval IO.println (render mediationDiagram mediationLayout [0, 1, 2])
#eval IO.println (render detDiagram detLayout [0, 1, 2])

/-! ## The acceptance test (R3.2) — stated, deliberately unproved

The one diagram identity the paper writes out in text rather than drawing (p. 2):
satisfaction of `Y ← X → Y` to within `ε` is exactly `ε ≥ H[Y | X]`.

It is the bridge between this calculus and the entropy layer, and it is the only point at
which the formal semantics can be checked against *text* rather than against a picture — so
it should be proved before anything is built on top.

Independently re-derived, agreeing with the paper:

```
D_KL(P ‖ q) = Σ_{a,b,b'} P(a,b,b') log( P(a,b,b') / (P(a)·P(b|a)·P(b'|a)) )
            = Σ_{a,b}    P(a,b)    log( P(a,b)   / (P(a,b)·P(b|a)) )
            = Σ_{a,b}    P(a,b) · (−log P(b|a))
            = H(Y|X)
```

the collapse being that the pushforward is supported on the diagonal `b = b'`.

Stated as a `Prop` rather than a `sorry`ed theorem, in the style of
`FiniteFactoredSets/Conjecture.lean`: nothing in this file has this type, so no downstream
result can silently rest on it. -/

/-- **The design target.**  An encoding is good exactly insofar as this proves cleanly. -/
def AcceptanceTest : Prop :=
  ∀ {Ω : Type} [Fintype Ω] [DecidableEq Ω] {V : Type} [Fintype V] [DecidableEq V]
    (P : FinPMF Ω) (X Y : Ω → V) (ε : ℝ),
    Satisfies P (detInterp X Y) detDiagram ε ↔
      ε ≥ -∑ a : (detInterp X Y).Assign,
        marginal P (detInterp X Y) {0, 1} a *
          Real.log (condFactor P (detInterp X Y) detDiagram a 1)

end NLDiagramSpike
