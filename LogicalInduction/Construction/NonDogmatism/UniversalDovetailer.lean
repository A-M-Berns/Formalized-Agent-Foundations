import LogicalInduction.Properties.UniversalSemimeasure
import LogicalInduction.Construction.Primcodable

/-!
# The universal dovetailer

`Properties/UniversalSemimeasure.lean` states `thm:dus` (Domination of the Universal
Semimeasure) for an arbitrary `UniversalContinuousSemimeasure`.  This file *constructs*
one: an explicit dovetail over `Nat.Partrec.Code` with a stage clock.

## The construction

For a program `c` the **raw clocked table** `rawTable c n σ` is the running maximum, over
the first `n` dovetail readings, of the rational read off `c.evaln f ⟪m, σ⟫` (zero when the
machine has not halted within the clock or the output does not decode).  Reading the pair
`(m, f) = n.unpair` at stage `n` makes the table monotone in the single stage clock while
still eventually catching every `(index, fuel)` pair: no unbounded search occurs at any
stage.

A raw table is *not* a semimeasure, so each stage is **trimmed** top-down along the tree
(`trimStage`): the root is capped at `1`, the `false` child at the mass still available at
its parent, and the `true` child at what the `false` child left over.  Trimming a stage in
isolation is not monotone in `n` — the sibling subtraction moves the wrong way — so each
trimmed value additionally remembers the previous stage (`max (prev _) _`).  That memory is
exactly what makes `trim c` a *monotone* sequence of semimeasures, and it costs nothing in
the limit: `trim_tendsto_of_exact` shows the trimming is **exact** whenever the raw table
converges from below to a genuine continuous semimeasure, which is the case for the program
of any lower-semicomputable continuous semimeasure.

The mixture `universalMass σ = ∑' c, (1/2) ^ (c+1) * dovetailMass c σ` is then a continuous
semimeasure dominating every lower-semicomputable one, with constant `(1/2) ^ (c+1)` where
`c` is the index of its approximation program.

## The emission program

`approximation_computes` is discharged by **column tabulation**.  `trim` is a `Nat.rec`
over the stage clock whose state is a *function* on strings, which no `Primcodable` state
can hold; the transposition tabulates the whole clock-column at one string and recurses
structurally on the *reversed* string, so extension by one bit is `cons` and the carried
state is a plain `List ℚ` (`tabCol`, `Primrec.list_rec`).  The two children of a node must
be emitted together — the `true` child reads the `false` child's freshly computed value —
so one `ℕ`-recursion carrying `ℚ × ℚ` (`childPair`) produces both columns from the parent
column.  Rational arithmetic is the repository's own primitive-recursive toolkit
(`ratPrimcodable`, `ratAdd_prim`, `ratMul_prim`, `ratMax_prim`, `ratMin_prim`,
`ratSub_prim`, `ratLE_prim` in `Construction/Primcodable.lean`).

## What this file discharges

Every field of `UniversalContinuousSemimeasure` is proved or constructed: the semimeasure
laws, the monotone from-below stage table with its limit, the domination constant, and the
emission program.  `universalSemimeasure` is axiom-clean.

## The stage table for the polynomial clock

`dusApprox` *selects* an exact stage value under the self-clamping clock `⟪z, z⟫`, so its
values are exact and monotonicity survives; `dusApproximationPresentation` and
`dusThresholdEmission` use `dusApprox`.

The self-clamped route works because `Code.evaln` guards `n ≤ k` in every clause: a fixed
code run with fuel `k` can neither read an input above `k` nor return a value above
`codeEvalBound c k`, which is polynomial in `k`.  That is exactly the clamp `PolyFueled.prec`
needs, and it is already present in `evaln`'s definition.  Scanning the stages that finished
within the clock therefore emits an exact stage value at a stage that grows without bound, so
`DUSApproximationPresentation` and `DUSThresholdEmission` are constructed objects and
`lic_domination_dovetailSemimeasure_unconditional` carries no semimeasure input at all.
-/

namespace LogicalInduction

open Filter Topology

namespace Dovetail

/-! ## The raw clocked table -/

/-- The rational read off program `c` at approximation index `m` with fuel `f` on the
string `σ`; `0` when the machine has not halted within the clock or its output does not
decode to a rational.  Negative readings are clamped away.
Paper node: `thm:dus` -/
def rawVal (c : Nat.Partrec.Code) (m f : ℕ) (σ : List Bool) : ℚ :=
  max 0
    (((c.evaln f (Nat.pair m (Encodable.encode σ))).bind
      (Encodable.decode (α := ℚ))).getD 0)

/-- One dovetail step: stage `n` reads index `n.unpair.1` with fuel `n.unpair.2`. -/
def rawStep (c : Nat.Partrec.Code) (n : ℕ) (σ : List Bool) : ℚ :=
  rawVal c n.unpair.1 n.unpair.2 σ

/-- The running maximum of the first `n` dovetail readings.  Monotone in `n` by
construction, and every `(index, fuel)` pair is read at stage `Nat.pair m f`. -/
def rawTable (c : Nat.Partrec.Code) : ℕ → List Bool → ℚ
  | 0 => fun _ => 0
  | n + 1 => fun σ => max (rawTable c n σ) (rawStep c n σ)

lemma rawTable_nonneg (c : Nat.Partrec.Code) : ∀ n σ, 0 ≤ rawTable c n σ
  | 0, _ => le_refl 0
  | n + 1, σ => le_trans (rawTable_nonneg c n σ) (le_max_left _ _)

@[simp] lemma rawTable_zero (c : Nat.Partrec.Code) (σ : List Bool) :
    rawTable c 0 σ = 0 := rfl

lemma rawTable_succ (c : Nat.Partrec.Code) (n : ℕ) (σ : List Bool) :
    rawTable c (n + 1) σ = max (rawTable c n σ) (rawStep c n σ) := rfl

lemma rawTable_le_succ (c : Nat.Partrec.Code) (n : ℕ) (σ : List Bool) :
    rawTable c n σ ≤ rawTable c (n + 1) σ := le_max_left _ _

lemma rawTable_mono (c : Nat.Partrec.Code) (σ : List Bool) :
    Monotone (fun n ↦ rawTable c n σ) :=
  monotone_nat_of_le_succ (fun n ↦ rawTable_le_succ c n σ)

lemma rawVal_le_rawTable (c : Nat.Partrec.Code) (m f : ℕ) (σ : List Bool) :
    rawVal c m f σ ≤ rawTable c (Nat.pair m f + 1) σ := by
  have hstep : rawStep c (Nat.pair m f) σ = rawVal c m f σ := by
    simp [rawStep, Nat.unpair_pair]
  rw [rawTable_succ, hstep]
  exact le_max_right _ _

/-- The reading is exactly the encoded rational when the machine halts with one. -/
lemma rawVal_eq_of_evaln {c : Nat.Partrec.Code} {m f : ℕ} {σ : List Bool} {q : ℚ}
    (hq : 0 ≤ q)
    (h : c.evaln f (Nat.pair m (Encodable.encode σ)) = some (Encodable.encode q)) :
    rawVal c m f σ = q := by
  simp [rawVal, h, Encodable.encodek, max_eq_right hq]

lemma rawVal_le_real {c : Nat.Partrec.Code} {m f : ℕ} {σ : List Bool} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ y, c.evaln f (Nat.pair m (Encodable.encode σ)) = some y →
      (((Encodable.decode (α := ℚ) y).getD 0 : ℚ) : ℝ) ≤ B) :
    ((rawVal c m f σ : ℚ) : ℝ) ≤ B := by
  rw [rawVal]
  push_cast
  refine max_le hB ?_
  cases hy : c.evaln f (Nat.pair m (Encodable.encode σ)) with
  | none => simpa [hy] using hB
  | some y => simpa [hy] using h y hy

lemma rawTable_le_of_forall_real {c : Nat.Partrec.Code} {σ : List Bool} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ m f, ((rawVal c m f σ : ℚ) : ℝ) ≤ B) : ∀ n, ((rawTable c n σ : ℚ) : ℝ) ≤ B
  | 0 => by simpa [rawTable_zero] using hB
  | n + 1 => by
      rw [rawTable_succ]
      push_cast
      exact max_le (rawTable_le_of_forall_real hB h n) (h _ _)

/-! ## Trimming a stage into a semimeasure -/

/-- Value assigned to the `false` child of `σ` at the new stage: the previous value, raised
to the raw reading but never beyond the mass its parent has left after the previous stage's
`true` child. -/
def child0 (prev rw : List Bool → ℚ) (p : ℚ) (σ : List Bool) : ℚ :=
  max (prev (σ ++ [false])) (min (rw (σ ++ [false])) (p - prev (σ ++ [true])))

/-- Value assigned to the `b` child of `σ` at the new stage.  The `true` child sees the
`false` child's *new* value, which is what makes the two children fit inside the parent. -/
def childVal (prev rw : List Bool → ℚ) (p : ℚ) (σ : List Bool) : Bool → ℚ
  | false => child0 prev rw p σ
  | true =>
      max (prev (σ ++ [true])) (min (rw (σ ++ [true])) (p - child0 prev rw p σ))

@[simp] lemma childVal_false (prev rw : List Bool → ℚ) (p : ℚ) (σ : List Bool) :
    childVal prev rw p σ false = child0 prev rw p σ := rfl

@[simp] lemma childVal_true (prev rw : List Bool → ℚ) (p : ℚ) (σ : List Bool) :
    childVal prev rw p σ true =
      max (prev (σ ++ [true])) (min (rw (σ ++ [true])) (p - child0 prev rw p σ)) := rfl

/-- One trimmed stage, built top-down from the root. -/
def trimStage (prev rw : List Bool → ℚ) (σ : List Bool) : ℚ :=
  List.reverseRecOn σ (min (rw []) 1) (fun τ b ih ↦ childVal prev rw ih τ b)

@[simp] lemma trimStage_nil (prev rw : List Bool → ℚ) :
    trimStage prev rw [] = min (rw []) 1 := by
  unfold trimStage
  exact List.reverseRecOn_nil _ _

lemma trimStage_concat (prev rw : List Bool → ℚ) (σ : List Bool) (b : Bool) :
    trimStage prev rw (σ ++ [b]) = childVal prev rw (trimStage prev rw σ) σ b := by
  unfold trimStage
  exact List.reverseRecOn_concat _ _ _ _

/-- The stage table of the dovetail: stage `0` is empty, stage `n+1` trims the raw table at
clock `n+1` against the previous stage. -/
def trim (c : Nat.Partrec.Code) : ℕ → List Bool → ℚ
  | 0 => fun _ => 0
  | n + 1 => trimStage (trim c n) (rawTable c (n + 1))

@[simp] lemma trim_zero (c : Nat.Partrec.Code) (σ : List Bool) : trim c 0 σ = 0 := rfl

lemma trim_succ (c : Nat.Partrec.Code) (n : ℕ) (σ : List Bool) :
    trim c (n + 1) σ = trimStage (trim c n) (rawTable c (n + 1)) σ := rfl

/-! ### The stage invariants -/

section Stage

variable {prev rw : List Bool → ℚ}

/-- Every trimmed value is nonnegative and at least the previous stage's value. -/
lemma trimStage_nonneg_and_ge
    (h0 : ∀ σ, 0 ≤ prev σ)
    (hroot : prev [] ≤ min (rw []) 1)
    (hrw : ∀ σ, 0 ≤ rw σ) :
    ∀ σ, 0 ≤ trimStage prev rw σ ∧ prev σ ≤ trimStage prev rw σ := by
  intro σ
  induction σ using List.reverseRecOn with
  | nil =>
      refine ⟨?_, by simpa using hroot⟩
      simpa using le_min (hrw []) zero_le_one
  | append_singleton τ b _ =>
      rw [trimStage_concat]
      cases b with
      | false => exact ⟨le_trans (h0 _) (le_max_left _ _), le_max_left _ _⟩
      | true => exact ⟨le_trans (h0 _) (le_max_left _ _), le_max_left _ _⟩

lemma trimStage_nonneg
    (h0 : ∀ σ, 0 ≤ prev σ) (hroot : prev [] ≤ min (rw []) 1) (hrw : ∀ σ, 0 ≤ rw σ)
    (σ : List Bool) : 0 ≤ trimStage prev rw σ :=
  (trimStage_nonneg_and_ge h0 hroot hrw σ).1

lemma le_trimStage
    (h0 : ∀ σ, 0 ≤ prev σ) (hroot : prev [] ≤ min (rw []) 1) (hrw : ∀ σ, 0 ≤ rw σ)
    (σ : List Bool) : prev σ ≤ trimStage prev rw σ :=
  (trimStage_nonneg_and_ge h0 hroot hrw σ).2

/-- The trimmed stage is a semimeasure: the two children fit inside the parent. -/
lemma trimStage_children
    (h0 : ∀ σ, 0 ≤ prev σ)
    (hc : ∀ σ, prev (σ ++ [false]) + prev (σ ++ [true]) ≤ prev σ)
    (hroot : prev [] ≤ min (rw []) 1)
    (hrw : ∀ σ, 0 ≤ rw σ)
    (σ : List Bool) :
    trimStage prev rw (σ ++ [false]) + trimStage prev rw (σ ++ [true])
      ≤ trimStage prev rw σ := by
  have hprev : prev σ ≤ trimStage prev rw σ := le_trimStage h0 hroot hrw σ
  have hfalse : trimStage prev rw (σ ++ [false])
      = child0 prev rw (trimStage prev rw σ) σ := by
    rw [trimStage_concat]; rfl
  have htrue : trimStage prev rw (σ ++ [true])
      = max (prev (σ ++ [true]))
          (min (rw (σ ++ [true]))
            (trimStage prev rw σ - child0 prev rw (trimStage prev rw σ) σ)) := by
    rw [trimStage_concat]; rfl
  have hstep : child0 prev rw (trimStage prev rw σ) σ
      ≤ trimStage prev rw σ - prev (σ ++ [true]) := by
    refine max_le ?_ (min_le_right _ _)
    have := hc σ
    linarith
  have h2 : trimStage prev rw (σ ++ [true])
      ≤ trimStage prev rw σ - child0 prev rw (trimStage prev rw σ) σ := by
    rw [htrue]
    exact max_le (by linarith) (min_le_right _ _)
  rw [hfalse]
  linarith

end Stage

/-! ### The dovetail stage table is a monotone sequence of semimeasures -/

lemma trim_root_le (c : Nat.Partrec.Code) (n : ℕ) :
    trim c n [] ≤ min (rawTable c (n + 1) []) 1 := by
  cases n with
  | zero => simpa using le_min (rawTable_nonneg c 1 []) zero_le_one
  | succ k =>
      rw [trim_succ, trimStage_nil]
      exact min_le_min (rawTable_le_succ c (k + 1) []) (le_refl 1)

lemma trim_props (c : Nat.Partrec.Code) : ∀ n,
    (∀ σ, 0 ≤ trim c n σ) ∧
      (∀ σ, trim c n (σ ++ [false]) + trim c n (σ ++ [true]) ≤ trim c n σ)
  | 0 => ⟨fun _ ↦ le_refl 0, fun _ ↦ by simp⟩
  | n + 1 => by
      obtain ⟨h0, hc⟩ := trim_props c n
      refine ⟨fun σ ↦ ?_, fun σ ↦ ?_⟩
      · rw [trim_succ]
        exact trimStage_nonneg h0 (trim_root_le c n) (rawTable_nonneg c (n + 1)) σ
      · simp only [trim_succ]
        exact trimStage_children h0 hc (trim_root_le c n) (rawTable_nonneg c (n + 1)) σ

lemma trim_nonneg (c : Nat.Partrec.Code) (n : ℕ) (σ : List Bool) : 0 ≤ trim c n σ :=
  (trim_props c n).1 σ

lemma trim_children (c : Nat.Partrec.Code) (n : ℕ) (σ : List Bool) :
    trim c n (σ ++ [false]) + trim c n (σ ++ [true]) ≤ trim c n σ :=
  (trim_props c n).2 σ

lemma trim_le_succ (c : Nat.Partrec.Code) (n : ℕ) (σ : List Bool) :
    trim c n σ ≤ trim c (n + 1) σ := by
  rw [trim_succ]
  exact le_trimStage (trim_props c n).1 (trim_root_le c n) (rawTable_nonneg c (n + 1)) σ

lemma trim_mono (c : Nat.Partrec.Code) (σ : List Bool) :
    Monotone (fun n ↦ trim c n σ) :=
  monotone_nat_of_le_succ (fun n ↦ trim_le_succ c n σ)

lemma trim_child_le (c : Nat.Partrec.Code) (n : ℕ) (σ : List Bool) (b : Bool) :
    trim c n (σ ++ [b]) ≤ trim c n σ := by
  have h := trim_children c n σ
  have h0 := trim_nonneg c n (σ ++ [false])
  have h1 := trim_nonneg c n (σ ++ [true])
  cases b <;> linarith

lemma trim_root_le_one (c : Nat.Partrec.Code) (n : ℕ) : trim c n [] ≤ 1 := by
  cases n with
  | zero => simp
  | succ k => rw [trim_succ, trimStage_nil]; exact min_le_right _ _

lemma trim_le_one (c : Nat.Partrec.Code) (n : ℕ) (σ : List Bool) : trim c n σ ≤ 1 := by
  induction σ using List.reverseRecOn with
  | nil => exact trim_root_le_one c n
  | append_singleton τ b ih => exact le_trans (trim_child_le c n τ b) ih

/-- Unfolding of the `false` child of a stage. -/
lemma trim_succ_false (c : Nat.Partrec.Code) (n : ℕ) (τ : List Bool) :
    trim c (n + 1) (τ ++ [false]) =
      max (trim c n (τ ++ [false]))
        (min (rawTable c (n + 1) (τ ++ [false]))
          (trim c (n + 1) τ - trim c n (τ ++ [true]))) := by
  show trimStage (trim c n) (rawTable c (n + 1)) (τ ++ [false]) = _
  rw [trimStage_concat]
  rfl

/-- Unfolding of the `true` child of a stage: it sees the `false` child's *new* value. -/
lemma trim_succ_true (c : Nat.Partrec.Code) (n : ℕ) (τ : List Bool) :
    trim c (n + 1) (τ ++ [true]) =
      max (trim c n (τ ++ [true]))
        (min (rawTable c (n + 1) (τ ++ [true]))
          (trim c (n + 1) τ - trim c (n + 1) (τ ++ [false]))) := by
  have hf : child0 (trim c n) (rawTable c (n + 1))
      (trimStage (trim c n) (rawTable c (n + 1)) τ) τ = trim c (n + 1) (τ ++ [false]) := by
    show _ = trimStage (trim c n) (rawTable c (n + 1)) (τ ++ [false])
    rw [trimStage_concat]
    rfl
  show trimStage (trim c n) (rawTable c (n + 1)) (τ ++ [true]) = _
  rw [trimStage_concat, childVal_true, hf]
  rfl

/-! ## Exactness of the trimming -/

section Exact

variable {c : Nat.Partrec.Code} {V : List Bool → ℝ}

/-- A trimmed stage never exceeds any real upper bound on the raw table. -/
lemma trim_le_of_raw_le
    (hV0 : ∀ σ, 0 ≤ V σ)
    (hle : ∀ n σ, ((rawTable c n σ : ℚ) : ℝ) ≤ V σ) :
    ∀ n σ, ((trim c n σ : ℚ) : ℝ) ≤ V σ := by
  intro n
  induction n with
  | zero => intro σ; simpa using hV0 σ
  | succ k ih =>
      intro σ
      induction σ using List.reverseRecOn with
      | nil =>
          rw [trim_succ, trimStage_nil]
          push_cast
          exact le_trans (min_le_left _ _) (hle (k + 1) [])
      | append_singleton τ b _ =>
          cases b with
          | false =>
              rw [trim_succ_false]
              push_cast
              exact max_le (ih _) (le_trans (min_le_left _ _) (hle _ _))
          | true =>
              rw [trim_succ_true]
              push_cast
              exact max_le (ih _) (le_trans (min_le_left _ _) (hle _ _))

/-- A monotone sequence bounded by `L` which dominates every term of a sequence converging
to `L` converges to `L`. -/
lemma tendsto_of_mono_of_dom {f g : ℕ → ℝ} {L : ℝ}
    (hmono : Monotone f) (hle : ∀ n, f n ≤ L)
    (hg : Tendsto g atTop (𝓝 L)) (hdom : ∀ m, ∃ n, g m ≤ f n) :
    Tendsto f atTop (𝓝 L) := by
  have hbdd : BddAbove (Set.range f) := ⟨L, by rintro _ ⟨n, rfl⟩; exact hle n⟩
  have h1 : Tendsto f atTop (𝓝 (⨆ n, f n)) := tendsto_atTop_ciSup hmono hbdd
  have h2 : (⨆ n, f n) ≤ L := ciSup_le hle
  have h3 : L ≤ ⨆ n, f n := by
    refine le_of_tendsto hg ?_
    filter_upwards with m
    obtain ⟨n, hn⟩ := hdom m
    exact hn.trans (le_ciSup hbdd n)
  rwa [le_antisymm h2 h3] at h1

/-- **Exactness.** If the raw table converges from below to a genuine continuous
semimeasure `V`, then the trimmed stages converge to `V` as well: the trimming loses
nothing in the limit. Paper node: `thm:dus` -/
theorem trim_tendsto_of_exact
    (hV0 : ∀ σ, 0 ≤ V σ) (hVone : V [] ≤ 1)
    (hVchild : ∀ σ, V (σ ++ [false]) + V (σ ++ [true]) ≤ V σ)
    (hle : ∀ n σ, ((rawTable c n σ : ℚ) : ℝ) ≤ V σ)
    (hlim : ∀ σ, Tendsto (fun n ↦ ((rawTable c n σ : ℚ) : ℝ)) atTop (𝓝 (V σ))) :
    ∀ σ, Tendsto (fun n ↦ ((trim c n σ : ℚ) : ℝ)) atTop (𝓝 (V σ)) := by
  have hAmono : ∀ σ, Monotone (fun n ↦ ((trim c n σ : ℚ) : ℝ)) := by
    intro σ a b hab
    show ((trim c a σ : ℚ) : ℝ) ≤ ((trim c b σ : ℚ) : ℝ)
    exact_mod_cast trim_mono c σ hab
  have hAle : ∀ n σ, ((trim c n σ : ℚ) : ℝ) ≤ V σ := trim_le_of_raw_le hV0 hle
  have hbdd : ∀ σ, BddAbove (Set.range fun n ↦ ((trim c n σ : ℚ) : ℝ)) := by
    intro σ
    exact ⟨V σ, by rintro _ ⟨n, rfl⟩; exact hAle n σ⟩
  set L : List Bool → ℝ := fun σ ↦ ⨆ n, ((trim c n σ : ℚ) : ℝ) with hL
  have hAt : ∀ σ, Tendsto (fun n ↦ ((trim c n σ : ℚ) : ℝ)) atTop (𝓝 (L σ)) :=
    fun σ ↦ tendsto_atTop_ciSup (hAmono σ) (hbdd σ)
  have hLle : ∀ σ, L σ ≤ V σ := fun σ ↦ ciSup_le (fun n ↦ hAle n σ)
  have key : ∀ σ, L σ = V σ := by
    intro σ
    induction σ using List.reverseRecOn with
    | nil =>
        have h1 : Tendsto (fun n ↦ ((trim c (n + 1) [] : ℚ) : ℝ)) atTop
            (𝓝 (min (V []) 1)) := by
          have : ∀ n : ℕ, ((trim c (n + 1) [] : ℚ) : ℝ)
              = min ((rawTable c (n + 1) [] : ℚ) : ℝ) 1 := by
            intro n
            rw [trim_succ, trimStage_nil]
            push_cast
            rfl
          simp only [this]
          exact ((hlim []).comp (tendsto_add_atTop_nat 1)).min tendsto_const_nhds
        have h2 : Tendsto (fun n ↦ ((trim c (n + 1) [] : ℚ) : ℝ)) atTop (𝓝 (L [])) :=
          (hAt []).comp (tendsto_add_atTop_nat 1)
        have hmin : min (V []) 1 = V [] := min_eq_left hVone
        rw [tendsto_nhds_unique h2 h1, hmin]
    | append_singleton τ b ih =>
        have hchildren : V (τ ++ [false]) ≤ L (τ ++ [false]) ∧
            V (τ ++ [true]) ≤ L (τ ++ [true]) := by
          have hm0 : min (V (τ ++ [false])) (L τ - L (τ ++ [true])) ≤ L (τ ++ [false]) := by
            refine le_of_tendsto_of_tendsto'
              (((hlim (τ ++ [false])).comp (tendsto_add_atTop_nat 1)).min
                (((hAt τ).comp (tendsto_add_atTop_nat 1)).sub (hAt (τ ++ [true]))))
              ((hAt (τ ++ [false])).comp (tendsto_add_atTop_nat 1)) ?_
            intro n
            rw [Function.comp_apply, Function.comp_apply, Function.comp_apply,
              trim_succ_false]
            push_cast
            exact le_max_right _ _
          have hm1 : min (V (τ ++ [true])) (L τ - L (τ ++ [false])) ≤ L (τ ++ [true]) := by
            refine le_of_tendsto_of_tendsto'
              (((hlim (τ ++ [true])).comp (tendsto_add_atTop_nat 1)).min
                (((hAt τ).comp (tendsto_add_atTop_nat 1)).sub
                  ((hAt (τ ++ [false])).comp (tendsto_add_atTop_nat 1))))
              ((hAt (τ ++ [true])).comp (tendsto_add_atTop_nat 1)) ?_
            intro n
            rw [Function.comp_apply, Function.comp_apply, Function.comp_apply,
              Function.comp_apply, trim_succ_true]
            push_cast
            exact le_max_right _ _
          rw [ih] at hm0 hm1
          have e0 := hLle (τ ++ [false])
          have e1 := hLle (τ ++ [true])
          have e2 := hVchild τ
          rcases min_cases (V (τ ++ [false])) (V τ - L (τ ++ [true])) with
            ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at hm0
          · refine ⟨hm0, ?_⟩
            rcases min_cases (V (τ ++ [true])) (V τ - L (τ ++ [false])) with
              ⟨he2, _⟩ | ⟨he2, _⟩ <;> rw [he2] at hm1 <;> linarith
          · exact ⟨by linarith, by linarith⟩
        cases b with
        | false => exact le_antisymm (hLle _) hchildren.1
        | true => exact le_antisymm (hLle _) hchildren.2
  intro σ
  rw [← key σ]
  exact hAt σ

end Exact

/-! ## The dovetailed limit of one program -/

lemma trim_bddAbove (c : Nat.Partrec.Code) (σ : List Bool) :
    BddAbove (Set.range fun n ↦ ((trim c n σ : ℚ) : ℝ)) :=
  ⟨1, by
    rintro _ ⟨n, rfl⟩
    show ((trim c n σ : ℚ) : ℝ) ≤ 1
    exact_mod_cast trim_le_one c n σ⟩

lemma trim_mono_real (c : Nat.Partrec.Code) (σ : List Bool) :
    Monotone (fun n ↦ ((trim c n σ : ℚ) : ℝ)) := by
  intro a b hab
  show ((trim c a σ : ℚ) : ℝ) ≤ ((trim c b σ : ℚ) : ℝ)
  exact_mod_cast trim_mono c σ hab

/-- The semimeasure computed by program `c` under the dovetail: the limit of its trimmed
stages.
Paper node: `thm:dus` -/
noncomputable def dovetailMass (c : Nat.Partrec.Code) (σ : List Bool) : ℝ :=
  ⨆ n, ((trim c n σ : ℚ) : ℝ)

lemma trim_le_dovetailMass (c : Nat.Partrec.Code) (n : ℕ) (σ : List Bool) :
    ((trim c n σ : ℚ) : ℝ) ≤ dovetailMass c σ :=
  le_ciSup (trim_bddAbove c σ) n

lemma dovetailMass_tendsto (c : Nat.Partrec.Code) (σ : List Bool) :
    Tendsto (fun n ↦ ((trim c n σ : ℚ) : ℝ)) atTop (𝓝 (dovetailMass c σ)) :=
  tendsto_atTop_ciSup (trim_mono_real c σ) (trim_bddAbove c σ)

lemma dovetailMass_nonneg (c : Nat.Partrec.Code) (σ : List Bool) : 0 ≤ dovetailMass c σ := by
  simpa using trim_le_dovetailMass c 0 σ

lemma dovetailMass_le_one (c : Nat.Partrec.Code) (σ : List Bool) : dovetailMass c σ ≤ 1 :=
  ciSup_le fun n ↦ by
    show ((trim c n σ : ℚ) : ℝ) ≤ 1
    exact_mod_cast trim_le_one c n σ

lemma dovetailMass_children (c : Nat.Partrec.Code) (σ : List Bool) :
    dovetailMass c (σ ++ [false]) + dovetailMass c (σ ++ [true]) ≤ dovetailMass c σ :=
  le_of_tendsto_of_tendsto'
    ((dovetailMass_tendsto c (σ ++ [false])).add (dovetailMass_tendsto c (σ ++ [true])))
    (dovetailMass_tendsto c σ)
    (fun n ↦ by
      show ((trim c n (σ ++ [false]) : ℚ) : ℝ) + ((trim c n (σ ++ [true]) : ℚ) : ℝ)
        ≤ ((trim c n σ : ℚ) : ℝ)
      exact_mod_cast trim_children c n σ)

/-! ### The dovetail is exact on lower-semicomputable continuous semimeasures -/

section OfLower

variable (ν : LowerSemicomputableContinuousSemimeasure)

lemma rawTable_le_mass (n : ℕ) (σ : List Bool) :
    ((rawTable ν.approximation_code n σ : ℚ) : ℝ) ≤ ν.mass σ := by
  refine rawTable_le_of_forall_real (ν.nonneg σ) (fun m f ↦ rawVal_le_real (ν.nonneg σ) ?_) n
  intro y hy
  obtain ⟨fuel, hfuel⟩ := ν.approximation_computes m σ
  have h1 := Nat.Partrec.Code.evaln_mono (le_max_left f fuel) (Option.mem_def.mpr hy)
  have h2 := Nat.Partrec.Code.evaln_mono (le_max_right f fuel) (Option.mem_def.mpr hfuel)
  have hyeq : y = Encodable.encode (ν.approximation m σ) :=
    Option.some_injective _ ((Option.mem_def.mp h1).symm.trans (Option.mem_def.mp h2))
  rw [hyeq]
  simpa [Encodable.encodek] using ν.approximation_le m σ

lemma rawTable_tendsto_mass (σ : List Bool) :
    Tendsto (fun n ↦ ((rawTable ν.approximation_code n σ : ℚ) : ℝ)) atTop (𝓝 (ν.mass σ)) := by
  refine tendsto_of_mono_of_dom ?_ (fun n ↦ rawTable_le_mass ν n σ)
    (ν.approximation_tendsto σ) ?_
  · intro a b hab
    show ((rawTable ν.approximation_code a σ : ℚ) : ℝ)
      ≤ ((rawTable ν.approximation_code b σ : ℚ) : ℝ)
    exact_mod_cast rawTable_mono ν.approximation_code σ hab
  · intro m
    obtain ⟨fuel, hfuel⟩ := ν.approximation_computes m σ
    refine ⟨Nat.pair m fuel + 1, ?_⟩
    have hval : rawVal ν.approximation_code m fuel σ = ν.approximation m σ :=
      rawVal_eq_of_evaln (ν.approximation_nonneg m σ) hfuel
    have := rawVal_le_rawTable ν.approximation_code m fuel σ
    rw [hval] at this
    exact_mod_cast this

/-- The dovetail run on `ν`'s own approximation program reproduces `ν` exactly.
Paper node: `thm:dus` -/
lemma dovetailMass_eq_mass (σ : List Bool) :
    dovetailMass ν.approximation_code σ = ν.mass σ :=
  tendsto_nhds_unique (dovetailMass_tendsto _ σ)
    (trim_tendsto_of_exact ν.nonneg ν.root_le_one ν.children_le
      (fun n σ ↦ rawTable_le_mass ν n σ) (rawTable_tendsto_mass ν) σ)

end OfLower

/-! ## The mixture -/

/-- The program of dovetail index `i`. -/
def codeOf (i : ℕ) : Nat.Partrec.Code := Denumerable.ofNat Nat.Partrec.Code i

/-- The dovetail weight of index `i`. -/
noncomputable def wt (i : ℕ) : ℝ := (1 / 2 : ℝ) ^ (i + 1)

lemma wt_pos (i : ℕ) : 0 < wt i := by
  unfold wt; positivity

lemma summable_wt : Summable wt := by
  have h : Summable fun i : ℕ ↦ (1 / 2 : ℝ) ^ i * (1 / 2) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right _
  have he : wt = fun i : ℕ ↦ (1 / 2 : ℝ) ^ i * (1 / 2) := by
    funext i
    simp [wt, pow_succ]
  rw [he]
  exact h

lemma tsum_wt : ∑' i, wt i = 1 := by
  have h : ∑' i : ℕ, (1 / 2 : ℝ) ^ i = 2 := by
    rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  calc ∑' i, wt i = ∑' i : ℕ, (1 / 2 : ℝ) ^ i * (1 / 2) := by simp [wt, pow_succ]
    _ = (∑' i : ℕ, (1 / 2 : ℝ) ^ i) * (1 / 2) := tsum_mul_right
    _ = 1 := by rw [h]; norm_num

/-- The universal continuous semimeasure: the weighted mixture of every program's
dovetailed limit.
Paper node: `thm:dus` -/
noncomputable def universalMass (σ : List Bool) : ℝ :=
  ∑' i, wt i * dovetailMass (codeOf i) σ

lemma summable_universal (σ : List Bool) :
    Summable fun i ↦ wt i * dovetailMass (codeOf i) σ := by
  refine Summable.of_nonneg_of_le (fun i ↦ ?_) (fun i ↦ ?_) summable_wt
  · exact mul_nonneg (wt_pos i).le (dovetailMass_nonneg _ _)
  · exact mul_le_of_le_one_right (wt_pos i).le (dovetailMass_le_one _ _)

lemma universalMass_nonneg (σ : List Bool) : 0 ≤ universalMass σ :=
  tsum_nonneg fun i ↦ mul_nonneg (wt_pos i).le (dovetailMass_nonneg _ _)

lemma universalMass_root_le_one : universalMass [] ≤ 1 := by
  calc universalMass [] ≤ ∑' i, wt i :=
        Summable.tsum_le_tsum
          (fun i ↦ mul_le_of_le_one_right (wt_pos i).le (dovetailMass_le_one _ _))
          (summable_universal _) summable_wt
    _ = 1 := tsum_wt

lemma universalMass_children (σ : List Bool) :
    universalMass (σ ++ [false]) + universalMass (σ ++ [true]) ≤ universalMass σ := by
  rw [universalMass, universalMass, universalMass,
    ← Summable.tsum_add (summable_universal _) (summable_universal _)]
  refine Summable.tsum_le_tsum (fun i ↦ ?_)
    ((summable_universal _).add (summable_universal _)) (summable_universal _)
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (dovetailMass_children _ _) (wt_pos i).le

/-- Single-term domination: every program's dovetailed limit is dominated by the mixture,
with the program's own weight as the constant. -/
lemma wt_mul_dovetailMass_le (i : ℕ) (σ : List Bool) :
    wt i * dovetailMass (codeOf i) σ ≤ universalMass σ :=
  Summable.le_tsum (summable_universal σ) i
    (fun j _ ↦ mul_nonneg (wt_pos j).le (dovetailMass_nonneg _ _))

/-! ## The clocked stage approximation of the mixture -/

/-- Stage `n` of the mixture: the first `n` programs, each run to trimmed stage `n`.  This
is the object whose polynomial emission `DUSApproximationPresentation` asks for; the bound
is on the *stage*, not the limit.
Paper node: `thm:dus` -/
def universalApprox (n : ℕ) (σ : List Bool) : ℚ :=
  ∑ i ∈ Finset.range n, (1 / 2 : ℚ) ^ (i + 1) * trim (codeOf i) n σ

lemma universalApprox_cast (n : ℕ) (σ : List Bool) :
    ((universalApprox n σ : ℚ) : ℝ)
      = ∑ i ∈ Finset.range n, wt i * ((trim (codeOf i) n σ : ℚ) : ℝ) := by
  unfold universalApprox wt
  push_cast
  ring_nf

lemma universalApprox_nonneg (n : ℕ) (σ : List Bool) : 0 ≤ universalApprox n σ :=
  Finset.sum_nonneg fun i _ ↦ by
    have := trim_nonneg (codeOf i) n σ
    positivity

lemma universalApprox_mono (σ : List Bool) : Monotone fun n ↦ universalApprox n σ := by
  refine monotone_nat_of_le_succ fun n ↦ ?_
  calc universalApprox n σ
      ≤ ∑ i ∈ Finset.range n, (1 / 2 : ℚ) ^ (i + 1) * trim (codeOf i) (n + 1) σ := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        exact mul_le_mul_of_nonneg_left (trim_le_succ _ n σ) (by positivity)
    _ ≤ universalApprox (n + 1) σ := by
        have hsub : Finset.range n ⊆ Finset.range (n + 1) :=
          Finset.range_subset_range.mpr (Nat.le_succ n)
        refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ ↦ ?_
        have := trim_nonneg (codeOf i) (n + 1) σ
        positivity

lemma universalApprox_le (n : ℕ) (σ : List Bool) :
    ((universalApprox n σ : ℚ) : ℝ) ≤ universalMass σ := by
  rw [universalApprox_cast]
  calc ∑ i ∈ Finset.range n, wt i * ((trim (codeOf i) n σ : ℚ) : ℝ)
      ≤ ∑ i ∈ Finset.range n, wt i * dovetailMass (codeOf i) σ := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        exact mul_le_mul_of_nonneg_left (trim_le_dovetailMass _ n σ) (wt_pos i).le
    _ ≤ universalMass σ :=
        Summable.sum_le_tsum _
          (fun i _ ↦ mul_nonneg (wt_pos i).le (dovetailMass_nonneg _ _))
          (summable_universal σ)

lemma universalApprox_tendsto (σ : List Bool) :
    Tendsto (fun n ↦ ((universalApprox n σ : ℚ) : ℝ)) atTop (𝓝 (universalMass σ)) := by
  set f : ℕ → ℝ := fun n ↦ ((universalApprox n σ : ℚ) : ℝ) with hf
  have hmono : Monotone f := by
    intro a b hab
    show ((universalApprox a σ : ℚ) : ℝ) ≤ ((universalApprox b σ : ℚ) : ℝ)
    exact_mod_cast universalApprox_mono σ hab
  have hle : ∀ n, f n ≤ universalMass σ := fun n ↦ universalApprox_le n σ
  have hbdd : BddAbove (Set.range f) := ⟨universalMass σ, by rintro _ ⟨n, rfl⟩; exact hle n⟩
  have h1 : Tendsto f atTop (𝓝 (⨆ n, f n)) := tendsto_atTop_ciSup hmono hbdd
  have hsup_le : (⨆ n, f n) ≤ universalMass σ := ciSup_le hle
  have hge : universalMass σ ≤ ⨆ n, f n := by
    have hpart : ∀ N, ∑ i ∈ Finset.range N, wt i * dovetailMass (codeOf i) σ ≤ ⨆ n, f n := by
      intro N
      have hlimN : Tendsto
          (fun n ↦ ∑ i ∈ Finset.range N, wt i * ((trim (codeOf i) n σ : ℚ) : ℝ)) atTop
          (𝓝 (∑ i ∈ Finset.range N, wt i * dovetailMass (codeOf i) σ)) :=
        tendsto_finsetSum _ fun i _ ↦ (dovetailMass_tendsto (codeOf i) σ).const_mul _
      refine le_of_tendsto hlimN ?_
      filter_upwards [eventually_ge_atTop N] with n hn
      calc ∑ i ∈ Finset.range N, wt i * ((trim (codeOf i) n σ : ℚ) : ℝ)
          ≤ ∑ i ∈ Finset.range n, wt i * ((trim (codeOf i) n σ : ℚ) : ℝ) := by
            have hsub : Finset.range N ⊆ Finset.range n := Finset.range_subset_range.mpr hn
            refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
            intro i _ _
            have := trim_nonneg (codeOf i) n σ
            have h0 : (0 : ℝ) ≤ ((trim (codeOf i) n σ : ℚ) : ℝ) := by exact_mod_cast this
            exact mul_nonneg (wt_pos i).le h0
        _ = f n := (universalApprox_cast n σ).symm
        _ ≤ ⨆ n, f n := le_ciSup hbdd n
    exact le_of_tendsto (summable_universal σ).hasSum.tendsto_sum_nat
      (Eventually.of_forall hpart)
  rwa [le_antisymm hsup_le hge] at h1

/-! ## Packaging

### The unconditional part

`universalMass` is a continuous semimeasure and dominates every lower-semicomputable
continuous semimeasure, with an explicit constant.  Neither statement mentions a program
for the mixture's own stage table, so both are independent of the emission machinery
below. -/

/-- The mixture as a continuous semimeasure.  Unconditional.
Paper node: `thm:dus` -/
noncomputable def continuousSemimeasure : ContinuousSemimeasure where
  mass := universalMass
  nonneg := universalMass_nonneg
  root_le_one := universalMass_root_le_one
  children_le := universalMass_children

/-- **Universality, unconditionally.**  The dovetail mixture multiplicatively dominates
every lower-semicomputable continuous semimeasure; the constant is the dovetail weight of
`ν`'s own approximation program.  This is the mathematical content of
`UniversalContinuousSemimeasure.universal`, proved without any appeal to an emission
program.
Paper node: `thm:dus` -/
theorem universalMass_dominates (ν : LowerSemicomputableContinuousSemimeasure) :
    ∃ K : ℝ, 0 < K ∧ ∀ σ, K * ν.mass σ ≤ universalMass σ :=
  ⟨wt (Encodable.encode ν.approximation_code), wt_pos _, fun σ ↦ by
    have h := wt_mul_dovetailMass_le (Encodable.encode ν.approximation_code) σ
    rw [codeOf, Denumerable.ofNat_encode, dovetailMass_eq_mass ν σ] at h
    exact h⟩

/-! ## The emission program: column tabulation -/

/-- The root column: `rootVal c n = trim c n []`. -/
def rootVal (c : Nat.Partrec.Code) (n : ℕ) : ℚ :=
  if n = 0 then 0 else min (rawTable c n []) 1

lemma rootVal_eq (c : Nat.Partrec.Code) (n : ℕ) : rootVal c n = trim c n [] := by
  cases n with
  | zero => simp [rootVal]
  | succ k => simp [rootVal, trim_succ, trimStage_nil]

/-- Stage-`n` values of the two children of `r.reverse`, computed from the parent's column
`pcol`.  Finite state (`ℚ × ℚ`), one `ℕ`-recursion. -/
def childPair (c : Nat.Partrec.Code) (r : List Bool) (pcol : List ℚ) : ℕ → ℚ × ℚ
  | 0 => (0, 0)
  | n + 1 =>
      let ab := childPair c r pcol n
      let p := pcol.getD (n + 1) 0
      let f := max ab.1 (min (rawTable c (n + 1) (r.reverse ++ [false])) (p - ab.2))
      (f, max ab.2 (min (rawTable c (n + 1) (r.reverse ++ [true])) (p - f)))

lemma childPair_zero (c : Nat.Partrec.Code) (r : List Bool) (pcol : List ℚ) :
    childPair c r pcol 0 = (0, 0) := rfl

lemma childPair_succ (c : Nat.Partrec.Code) (r : List Bool) (pcol : List ℚ) (n : ℕ) :
    childPair c r pcol (n + 1) =
      (max (childPair c r pcol n).1
          (min (rawTable c (n + 1) (r.reverse ++ [false]))
            (pcol.getD (n + 1) 0 - (childPair c r pcol n).2)),
        max (childPair c r pcol n).2
          (min (rawTable c (n + 1) (r.reverse ++ [true]))
            (pcol.getD (n + 1) 0 -
              max (childPair c r pcol n).1
                (min (rawTable c (n + 1) (r.reverse ++ [false]))
                  (pcol.getD (n + 1) 0 - (childPair c r pcol n).2))))) := rfl

/-- `childPair` reproduces the two child columns of `trim`, given a correct parent
column. -/
lemma childPair_eq (c : Nat.Partrec.Code) (r : List Bool) (pcol : List ℚ) {N : ℕ}
    (hp : ∀ m, m ≤ N → pcol.getD m 0 = trim c m r.reverse) :
    ∀ n, n ≤ N → childPair c r pcol n
      = (trim c n (r.reverse ++ [false]), trim c n (r.reverse ++ [true])) := by
  intro n
  induction n with
  | zero => intro _; simp [childPair_zero]
  | succ k ih =>
      intro hk
      have hk' : k ≤ N := Nat.le_of_succ_le hk
      have hab := ih hk'
      have hpar : pcol.getD (k + 1) 0 = trim c (k + 1) r.reverse := hp (k + 1) hk
      have hf : max (childPair c r pcol k).1
          (min (rawTable c (k + 1) (r.reverse ++ [false]))
            (pcol.getD (k + 1) 0 - (childPair c r pcol k).2))
          = trim c (k + 1) (r.reverse ++ [false]) := by
        rw [hab, hpar, trim_succ_false]
      rw [childPair_succ, hf, hab, hpar, trim_succ_true]

/-- One column of the tabulation, from the parent column. -/
def colOf (c : Nat.Partrec.Code) (N : ℕ) (b : Bool) (r : List Bool) (pcol : List ℚ) :
    List ℚ :=
  (List.range (N + 1)).map fun n ↦
    if b then (childPair c r pcol n).2 else (childPair c r pcol n).1

/-- **Column tabulation.**  `tabCol c N r` is the clock-column
`[trim c 0 r.reverse, …, trim c N r.reverse]`, by structural recursion on `r`. -/
def tabCol (c : Nat.Partrec.Code) (N : ℕ) : List Bool → List ℚ
  | [] => (List.range (N + 1)).map (rootVal c)
  | b :: r => colOf c N b r (tabCol c N r)

lemma tabCol_eq (c : Nat.Partrec.Code) (N : ℕ) : ∀ r : List Bool,
    tabCol c N r = (List.range (N + 1)).map fun n ↦ trim c n r.reverse := by
  intro r
  induction r with
  | nil => simp [tabCol, rootVal_eq]
  | cons b r ih =>
      have hp : ∀ m, m ≤ N → (tabCol c N r).getD m 0 = trim c m r.reverse := by
        intro m hm
        rw [ih, AffineCombination.getD_map_range _ _ (Nat.lt_succ_of_le hm)]
      have hcp := childPair_eq c r (tabCol c N r) hp
      show colOf c N b r (tabCol c N r) = _
      unfold colOf
      refine List.map_congr_left ?_
      intro n hn
      have hn' : n ≤ N := Nat.lt_succ_iff.mp (List.mem_range.mp hn)
      rw [hcp n hn']
      cases b <;> simp

/-- The stage table read off its own column. -/
lemma trim_eq_tabCol (c : Nat.Partrec.Code) (n : ℕ) (σ : List Bool) :
    trim c n σ = (tabCol c n σ.reverse).getD n 0 := by
  rw [tabCol_eq, AffineCombination.getD_map_range _ _ (Nat.lt_succ_self n), List.reverse_reverse]

/-! ### The mixture's stage table as a list -/

/-- `halfPow i = (1/2) ^ (i+1)`, by a `ℕ`-recursion in `ℚ` (no numeral cast needed). -/
def halfPow : ℕ → ℚ
  | 0 => 1 / 2
  | i + 1 => halfPow i * (1 / 2)

lemma halfPow_eq : ∀ i, halfPow i = (1 / 2 : ℚ) ^ (i + 1)
  | 0 => by simp [halfPow]
  | i + 1 => by rw [halfPow, halfPow_eq i, pow_succ]; ring

/-- The stage table as an explicit list sum. -/
def approxList (n : ℕ) (σ : List Bool) : List ℚ :=
  (List.range n).map fun i ↦ halfPow i * trim (codeOf i) n σ

lemma universalApprox_eq_sum (n : ℕ) (σ : List Bool) :
    universalApprox n σ = (approxList n σ).sum := by
  rw [approxList, list_range_map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [halfPow_eq]

/-! ## Primitive recursion of the emission program -/

section Emission

attribute [local irreducible] Nat.sqrt

/-- The dovetail's single clocked reading is primitive recursive: `evaln` is, and the
rational decode is the repository's canonical rational `Primcodable`. -/
lemma rawStep_prim :
    Primrec fun x : (Nat.Partrec.Code × ℕ) × List Bool ↦ rawStep x.1.1 x.1.2 x.2 := by
  have hc : Primrec fun x : (Nat.Partrec.Code × ℕ) × List Bool ↦ x.1.1 :=
    Primrec.fst.comp Primrec.fst
  have hn : Primrec fun x : (Nat.Partrec.Code × ℕ) × List Bool ↦ x.1.2 :=
    Primrec.snd.comp Primrec.fst
  have hs : Primrec fun x : (Nat.Partrec.Code × ℕ) × List Bool ↦ x.2 := Primrec.snd
  have hup : Primrec fun x : (Nat.Partrec.Code × ℕ) × List Bool ↦ x.1.2.unpair :=
    Primrec.unpair.comp hn
  have hm : Primrec fun x : (Nat.Partrec.Code × ℕ) × List Bool ↦ x.1.2.unpair.1 :=
    Primrec.fst.comp hup
  have hf : Primrec fun x : (Nat.Partrec.Code × ℕ) × List Bool ↦ x.1.2.unpair.2 :=
    Primrec.snd.comp hup
  have harg : Primrec fun x : (Nat.Partrec.Code × ℕ) × List Bool ↦
      Nat.pair x.1.2.unpair.1 (Encodable.encode x.2) :=
    Primrec₂.natPair.comp hm (Primrec.encode.comp hs)
  have hev : Primrec fun x : (Nat.Partrec.Code × ℕ) × List Bool ↦
      Nat.Partrec.Code.evaln x.1.2.unpair.2 x.1.1
        (Nat.pair x.1.2.unpair.1 (Encodable.encode x.2)) :=
    Nat.Partrec.Code.primrec_evaln.comp ((hf.pair hc).pair harg)
  have hdec : Primrec fun x : (Nat.Partrec.Code × ℕ) × List Bool ↦
      (Nat.Partrec.Code.evaln x.1.2.unpair.2 x.1.1
        (Nat.pair x.1.2.unpair.1 (Encodable.encode x.2))).bind
          (Encodable.decode (α := ℚ)) :=
    Primrec.option_bind hev ((Primrec.decode (α := ℚ)).comp₂ Primrec₂.right)
  have hgd : Primrec fun x : (Nat.Partrec.Code × ℕ) × List Bool ↦
      ((Nat.Partrec.Code.evaln x.1.2.unpair.2 x.1.1
        (Nat.pair x.1.2.unpair.1 (Encodable.encode x.2))).bind
          (Encodable.decode (α := ℚ))).getD 0 :=
    Primrec.option_getD.comp hdec (Primrec.const 0)
  exact (ratMax_prim.comp (Primrec.const 0) hgd).of_eq fun x ↦ rfl

lemma rawTable_rec (c : Nat.Partrec.Code) (σ : List Bool) : ∀ n,
    rawTable c n σ = n.rec (motive := fun _ ↦ ℚ) 0 fun k IH ↦ max IH (rawStep c k σ)
  | 0 => rfl
  | n + 1 => by rw [rawTable_succ, rawTable_rec c σ n]

attribute [local irreducible] rawStep rawVal in
lemma rawTable_prim :
    Primrec₂ fun (a : Nat.Partrec.Code × List Bool) (n : ℕ) ↦ rawTable a.1 n a.2 := by
  have hstep : Primrec₂ fun (a : Nat.Partrec.Code × List Bool) (p : ℕ × ℚ) ↦
      max p.2 (rawStep a.1 p.1 a.2) := by
    have hraw : Primrec fun y : (Nat.Partrec.Code × List Bool) × ℕ × ℚ ↦
        rawStep y.1.1 y.2.1 y.1.2 :=
      rawStep_prim.comp (((Primrec.fst.comp Primrec.fst).pair
        (Primrec.fst.comp Primrec.snd)).pair (Primrec.snd.comp Primrec.fst))
    exact (ratMax_prim.comp (Primrec.snd.comp Primrec.snd) hraw).to₂
  exact (Primrec.nat_rec (Primrec.const (0 : ℚ)) hstep).of_eq fun a n ↦
    (rawTable_rec a.1 a.2 n).symm

/-! ### The child pair and the tabulation -/

lemma childPair_rec (c : Nat.Partrec.Code) (r : List Bool) (pcol : List ℚ) : ∀ n,
    childPair c r pcol n =
      n.rec (motive := fun _ ↦ ℚ × ℚ) (0, 0) fun k IH ↦
        (max IH.1
            (min (rawTable c (k + 1) (r.reverse ++ [false]))
              (pcol.getD (k + 1) 0 - IH.2)),
          max IH.2
            (min (rawTable c (k + 1) (r.reverse ++ [true]))
              (pcol.getD (k + 1) 0 -
                max IH.1
                  (min (rawTable c (k + 1) (r.reverse ++ [false]))
                    (pcol.getD (k + 1) 0 - IH.2)))))
  | 0 => rfl
  | n + 1 => by rw [childPair_succ, childPair_rec c r pcol n]

attribute [local irreducible] rawStep rawVal in
lemma childPair_prim :
    Primrec₂ fun (a : Nat.Partrec.Code × List Bool × List ℚ) (n : ℕ) ↦
      childPair a.1 a.2.1 a.2.2 n := by
  set A := Nat.Partrec.Code × List Bool × List ℚ with hA
  have hc : Primrec fun y : A × ℕ × (ℚ × ℚ) ↦ y.1.1 := Primrec.fst.comp Primrec.fst
  have hr : Primrec fun y : A × ℕ × (ℚ × ℚ) ↦ y.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hpcol : Primrec fun y : A × ℕ × (ℚ × ℚ) ↦ y.1.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hk1 : Primrec fun y : A × ℕ × (ℚ × ℚ) ↦ y.2.1 + 1 :=
    Primrec.succ.comp (Primrec.fst.comp Primrec.snd)
  have hih1 : Primrec fun y : A × ℕ × (ℚ × ℚ) ↦ y.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hih2 : Primrec fun y : A × ℕ × (ℚ × ℚ) ↦ y.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hp : Primrec fun y : A × ℕ × (ℚ × ℚ) ↦ y.1.2.2.getD (y.2.1 + 1) 0 :=
    (Primrec.list_getD (0 : ℚ)).comp hpcol hk1
  have hs0 : Primrec fun y : A × ℕ × (ℚ × ℚ) ↦ y.1.2.1.reverse ++ [false] :=
    Primrec.list_append.comp (Primrec.list_reverse.comp hr) (Primrec.const [false])
  have hs1 : Primrec fun y : A × ℕ × (ℚ × ℚ) ↦ y.1.2.1.reverse ++ [true] :=
    Primrec.list_append.comp (Primrec.list_reverse.comp hr) (Primrec.const [true])
  have hraw0 : Primrec fun y : A × ℕ × (ℚ × ℚ) ↦
      rawTable y.1.1 (y.2.1 + 1) (y.1.2.1.reverse ++ [false]) :=
    rawTable_prim.comp (hc.pair hs0) hk1
  have hraw1 : Primrec fun y : A × ℕ × (ℚ × ℚ) ↦
      rawTable y.1.1 (y.2.1 + 1) (y.1.2.1.reverse ++ [true]) :=
    rawTable_prim.comp (hc.pair hs1) hk1
  have hf : Primrec fun y : A × ℕ × (ℚ × ℚ) ↦
      max y.2.2.1
        (min (rawTable y.1.1 (y.2.1 + 1) (y.1.2.1.reverse ++ [false]))
          (y.1.2.2.getD (y.2.1 + 1) 0 - y.2.2.2)) :=
    ratMax_prim.comp hih1 (ratMin_prim.comp hraw0 (ratSub_prim.comp hp hih2))
  have ht : Primrec fun y : A × ℕ × (ℚ × ℚ) ↦
      max y.2.2.2
        (min (rawTable y.1.1 (y.2.1 + 1) (y.1.2.1.reverse ++ [true]))
          (y.1.2.2.getD (y.2.1 + 1) 0 -
            max y.2.2.1
              (min (rawTable y.1.1 (y.2.1 + 1) (y.1.2.1.reverse ++ [false]))
                (y.1.2.2.getD (y.2.1 + 1) 0 - y.2.2.2)))) :=
    ratMax_prim.comp hih2 (ratMin_prim.comp hraw1 (ratSub_prim.comp hp hf))
  exact (Primrec.nat_rec (Primrec.const ((0 : ℚ), (0 : ℚ))) (hf.pair ht).to₂).of_eq
    fun a n ↦ (childPair_rec a.1 a.2.1 a.2.2 n).symm

attribute [local irreducible] rawStep rawVal childPair in
lemma colOf_prim :
    Primrec fun y : (Nat.Partrec.Code × ℕ) × Bool × List Bool × List ℚ ↦
      colOf y.1.1 y.1.2 y.2.1 y.2.2.1 y.2.2.2 := by
  set B := (Nat.Partrec.Code × ℕ) × Bool × List Bool × List ℚ with hB
  have hrange : Primrec fun y : B ↦ List.range (y.1.2 + 1) :=
    Primrec.list_range.comp (Primrec.succ.comp (Primrec.snd.comp Primrec.fst))
  have hargs : Primrec fun z : B × ℕ ↦
      ((z.1.1.1, z.1.2.2.1, z.1.2.2.2) : Nat.Partrec.Code × List Bool × List ℚ) :=
    (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
      ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).pair
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
  have hcp : Primrec fun z : B × ℕ ↦ childPair z.1.1.1 z.1.2.2.1 z.1.2.2.2 z.2 :=
    childPair_prim.comp hargs Primrec.snd
  have hsel : Primrec₂ fun (y : B) (n : ℕ) ↦
      if y.2.1 then (childPair y.1.1 y.2.2.1 y.2.2.2 n).2
      else (childPair y.1.1 y.2.2.1 y.2.2.2 n).1 := by
    refine (Primrec.cond (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.snd.comp hcp) (Primrec.fst.comp hcp)).to₂.of_eq ?_
    intro y n
    cases hb : y.2.1 <;> simp
  exact Primrec.list_map hrange hsel

attribute [local irreducible] rawStep rawVal childPair in
lemma rootVal_prim :
    Primrec fun x : Nat.Partrec.Code × ℕ ↦ rootVal x.1 x.2 := by
  have hz : PrimrecPred fun x : Nat.Partrec.Code × ℕ ↦ x.2 = 0 :=
    Primrec.eq.comp Primrec.snd (Primrec.const 0)
  have hraw : Primrec fun x : Nat.Partrec.Code × ℕ ↦ rawTable x.1 x.2 [] :=
    rawTable_prim.comp (Primrec.fst.pair (Primrec.const [])) Primrec.snd
  exact (Primrec.ite hz (Primrec.const 0)
    (ratMin_prim.comp hraw (Primrec.const 1))).of_eq fun x ↦ rfl

attribute [local irreducible] rawStep rawVal childPair colOf in
lemma tabCol_prim :
    Primrec fun x : (Nat.Partrec.Code × ℕ) × List Bool ↦ tabCol x.1.1 x.1.2 x.2 := by
  set A := Nat.Partrec.Code × ℕ with hA
  have hbase : Primrec fun a : A ↦ (List.range (a.2 + 1)).map (rootVal a.1) := by
    refine Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp Primrec.snd)) ?_
    exact (rootVal_prim.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂
  have hh : Primrec₂ fun (x : A × List Bool) (w : Bool × List Bool × List ℚ) ↦
      colOf x.1.1 x.1.2 w.1 w.2.1 w.2.2 :=
    (colOf_prim.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂
  have hlr := Primrec.list_rec (f := fun x : A × List Bool ↦ x.2)
    (g := fun x : A × List Bool ↦ (List.range (x.1.2 + 1)).map (rootVal x.1.1))
    (h := fun (x : A × List Bool) (w : Bool × List Bool × List ℚ) ↦
      colOf x.1.1 x.1.2 w.1 w.2.1 w.2.2)
    Primrec.snd (hbase.comp Primrec.fst) hh
  refine hlr.of_eq fun x ↦ ?_
  obtain ⟨a, r⟩ := x
  induction r with
  | nil => rfl
  | cons b r ih => simpa [tabCol] using congrArg (colOf a.1 a.2 b r) ih

attribute [local irreducible] rawStep rawVal childPair colOf rootVal in
lemma trim_prim :
    Primrec fun x : (Nat.Partrec.Code × ℕ) × List Bool ↦ trim x.1.1 x.1.2 x.2 := by
  have htab : Primrec fun x : (Nat.Partrec.Code × ℕ) × List Bool ↦
      tabCol x.1.1 x.1.2 x.2.reverse :=
    tabCol_prim.comp (Primrec.fst.pair (Primrec.list_reverse.comp Primrec.snd))
  exact ((Primrec.list_getD (0 : ℚ)).comp htab
    (Primrec.snd.comp Primrec.fst)).of_eq fun x ↦ (trim_eq_tabCol x.1.1 x.1.2 x.2).symm

/-! ### The mixture's stage table -/

lemma halfPow_rec : ∀ i,
    halfPow i = i.rec (motive := fun _ ↦ ℚ) (1 / 2) fun _ ih ↦ ih * (1 / 2)
  | 0 => rfl
  | i + 1 => by rw [halfPow, halfPow_rec i]

lemma halfPow_prim : Primrec halfPow := by
  have hstep : Primrec₂ fun (_ : ℕ) (ih : ℚ) ↦ ih * (1 / 2) :=
    (ratMul_prim.comp Primrec.snd (Primrec.const (1 / 2 : ℚ))).to₂
  exact (Primrec.nat_rec₁ (1 / 2 : ℚ) hstep).of_eq fun i ↦ (halfPow_rec i).symm

attribute [local irreducible] rawStep rawVal childPair colOf rootVal tabCol in
lemma approxList_prim :
    Primrec fun x : ℕ × List Bool ↦ approxList x.1 x.2 := by
  refine Primrec.list_map (Primrec.list_range.comp Primrec.fst) ?_
  have hcode : Primrec fun y : (ℕ × List Bool) × ℕ ↦ codeOf y.2 :=
    (Primrec.ofNat Nat.Partrec.Code).comp Primrec.snd
  have hn : Primrec fun y : (ℕ × List Bool) × ℕ ↦ y.1.1 :=
    Primrec.fst.comp Primrec.fst
  have hσ : Primrec fun y : (ℕ × List Bool) × ℕ ↦ y.1.2 :=
    Primrec.snd.comp Primrec.fst
  have htrim : Primrec fun y : (ℕ × List Bool) × ℕ ↦ trim (codeOf y.2) y.1.1 y.1.2 :=
    trim_prim.comp ((hcode.pair hn).pair hσ)
  exact (ratMul_prim.comp (halfPow_prim.comp Primrec.snd) htrim).to₂

attribute [local irreducible] rawStep rawVal childPair colOf rootVal tabCol trim in
lemma universalApprox_prim :
    Primrec fun x : ℕ × List Bool ↦ universalApprox x.1 x.2 := by
  exact (ratListSum_prim.comp approxList_prim).of_eq fun x ↦
    (universalApprox_eq_sum x.1 x.2).symm

/-! ### The emission program -/

/-- The emission program's arithmetic form: stage index and string code in one `Nat.pair`
argument, encoded rational result. -/
def approxEmit (z : ℕ) : ℕ :=
  Encodable.encode
    (universalApprox z.unpair.1 ((Encodable.decode (α := List Bool) z.unpair.2).getD []))

attribute [local irreducible] rawStep rawVal childPair colOf rootVal tabCol trim
  universalApprox in
lemma approxEmit_prim : Primrec approxEmit := by
  have hup : Primrec fun z : ℕ ↦ z.unpair := Primrec.unpair
  have hσ : Primrec fun z : ℕ ↦ ((Encodable.decode (α := List Bool) z.unpair.2).getD []) :=
    Primrec.option_getD.comp
      ((Primrec.decode (α := List Bool)).comp (Primrec.snd.comp hup)) (Primrec.const [])
  exact Primrec.encode.comp
    (universalApprox_prim.comp ((Primrec.fst.comp hup).pair hσ))

/-- **The emission obligation, discharged.**  One fixed program emits the encoded stage
table on `⟪n, σ⟫`; the fuel is whatever `evaln` needs, since only lower-semicomputability
(not a polynomial clock) is at stake here.
Paper node: `thm:dus` -/
theorem exists_universalApprox_code :
    ∃ c : Nat.Partrec.Code, ∀ n σ, ∃ fuel,
      c.evaln fuel (Nat.pair n (Encodable.encode σ)) =
        some (Encodable.encode (universalApprox n σ)) := by
  obtain ⟨code, hcode⟩ := Nat.Partrec.Code.exists_code.mp
    (Nat.Partrec.of_primrec (Primrec.nat_iff.mp approxEmit_prim))
  refine ⟨code, fun n σ ↦ ?_⟩
  have hval : approxEmit (Nat.pair n (Encodable.encode σ))
      = Encodable.encode (universalApprox n σ) := by
    simp [approxEmit, Nat.unpair_pair, Encodable.encodek]
  have hmem : Encodable.encode (universalApprox n σ) ∈
      code.eval (Nat.pair n (Encodable.encode σ)) := by
    rw [hcode, ← hval]
    exact Part.mem_some _
  obtain ⟨fuel, hfuel⟩ := Nat.Partrec.Code.evaln_complete.mp hmem
  exact ⟨fuel, Option.mem_def.mp hfuel⟩

end Emission

/-! ### The packaging

Every analytic field of both structures is proved above; the emission field is the
constructed program `exists_universalApprox_code`. -/

/-- The dovetail as a lower-semicomputable continuous semimeasure.
Paper node: `thm:dus` -/
noncomputable def lowerSemicomputable : LowerSemicomputableContinuousSemimeasure where
  mass := universalMass
  nonneg := universalMass_nonneg
  root_le_one := universalMass_root_le_one
  children_le := universalMass_children
  approximation := universalApprox
  approximation_code := exists_universalApprox_code.choose
  approximation_computes := exists_universalApprox_code.choose_spec
  approximation_nonneg := universalApprox_nonneg
  approximation_mono := universalApprox_mono
  approximation_le := universalApprox_le
  approximation_tendsto := universalApprox_tendsto

/-- **The constructed universal continuous semimeasure.**  Domination of an arbitrary
lower-semicomputable `ν` holds with the explicit constant `wt (encode ν.approximation_code)`
— the dovetail weight of `ν`'s own approximation program.
Paper node: `thm:dus` -/
noncomputable def universalSemimeasure : UniversalContinuousSemimeasure where
  toLowerSemicomputableContinuousSemimeasure := lowerSemicomputable
  universal := fun ν ↦ universalMass_dominates ν

/-! ## Self-clamped stage tables

Two lanes here read an *exact* stage table under a polynomial clock and keep the best
stage that finished: the dovetail's mixture approximation below, and the universal prefix
machine's complexity table (`Construction/NonDogmatism/UniversalPrefix.lean`).  The
construction is the same in both, and it is written once here.

Fix a code `c` whose `eval` is total — think of it as an exact stage emitter, returning
`⌜tab j i⌝` on the packed input `⟪j, i⟫`.  Then:

* `read c F j i` is one clocked reading of that emitter, `0` when the clock `F` ran out;
* `fuel z = ⟪z, z⟫` is the clock offered at query `z`, which grows past every fixed bound;
* `stage c z j` is the stage the last successful reading below `j` came from, and
  `state c z j` is that reading's value, carried as `⌜tab (stage …) i⌝ + 1`;
* `selCode c z = state c z z.1 - 1` is the emitted code, and `selCode_polyFueled` is its
  `dd:fuel` certificate.

What makes this work is that `Code.evaln` is **self-clamping**: every clause guards `n ≤ k`,
so a code run with fuel `k` can neither read an input above `k` nor return a value above
`codeEvalBound c k`, which for a *fixed* `c` is polynomial in `k`.  That is exactly the
clamp `PolyFueled.prec` needs, and it is free.  The emitted value is not an approximation
of the exact table but a *selection* from it, so the values stay exact and monotonicity
survives; a caller supplies only the table's own analytic facts. -/

namespace SelfClamped

-- The `dd:fuel` elaboration safeguard; see `Framework/Emission/Computable.lean`.
attribute [local irreducible] Nat.sqrt

variable (c : Nat.Partrec.Code)

/-- One clocked reading of the exact table: stage `j`, index `i`, clock `F`.
`0` means "the clock ran out". -/
noncomputable def read (F j i : ℕ) : ℕ :=
  codeEvalnNat c (Nat.pair F (Nat.pair j i))

lemma read_le (F j i : ℕ) : read c F j i ≤ codeEvalBound c F + 1 := by
  simpa [read] using codeEvalnNat_le c (Nat.pair F (Nat.pair j i))

variable {c}

/-- A successful reading returns the emitter's value, offset by one. -/
lemma read_eq_of_ne_zero {val : ℕ → ℕ} (hc : ∀ x, c.eval x = Part.some (val x))
    {F j i : ℕ} (h : read c F j i ≠ 0) :
    read c F j i = val (Nat.pair j i) + 1 := by
  rw [read, codeEvalnNat] at h ⊢
  simp only [Nat.unpair_pair] at h ⊢
  cases hev : c.evaln F (Nat.pair j i) with
  | none => rw [hev] at h; simp at h
  | some out =>
      have hmem : out ∈ c.eval (Nat.pair j i) := Nat.Partrec.Code.evaln_sound hev
      rw [hc] at hmem
      simp only [Part.mem_some_iff] at hmem
      rw [hmem]

/-- Every reading succeeds once the clock is large enough. -/
lemma read_ne_zero {val : ℕ → ℕ} (hc : ∀ x, c.eval x = Part.some (val x)) (j i : ℕ) :
    ∃ F₀, ∀ F, F₀ ≤ F → read c F j i ≠ 0 := by
  have hmem : val (Nat.pair j i) ∈ c.eval (Nat.pair j i) := by
    rw [hc]; exact Part.mem_some _
  obtain ⟨F₀, hF₀⟩ := Nat.Partrec.Code.evaln_complete.mp hmem
  refine ⟨F₀, fun F hF => ?_⟩
  have heq : c.evaln F (Nat.pair j i) = some (val (Nat.pair j i)) :=
    Nat.Partrec.Code.evaln_mono hF hF₀
  rw [read, codeEvalnNat]
  simp [Nat.unpair_pair, heq]

variable (c)

/-- The polynomial clock offered at query `z`. -/
def fuel (z : ℕ) : ℕ := Nat.pair z z

lemma le_fuel (z : ℕ) : z ≤ fuel z := Nat.left_le_pair z z

/-- The stage that the last successful reading below `j` came from. -/
noncomputable def stage (z : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => if read c (fuel z) j z.unpair.2 = 0 then stage z j else j

/-- The carried encoded state of the scan: `⌜tab (stage z j) i⌝ + 1`. -/
noncomputable def state (z : ℕ) : ℕ → ℕ
  | 0 => 2
  | j + 1 =>
      ifzSelFn (Nat.pair (state z j) (read c (fuel z) j z.unpair.2))
        (read c (fuel z) j z.unpair.2)

@[simp] lemma state_zero (z : ℕ) : state c z 0 = 2 := rfl

lemma state_le (z : ℕ) : ∀ j, state c z j ≤ codeEvalBound c (fuel z) + 2
  | 0 => by rw [state]; omega
  | j + 1 => by
      rw [state, ifzSelFn]
      by_cases h : read c (fuel z) j z.unpair.2 = 0
      · rw [if_pos h, Nat.unpair_pair]; exact state_le z j
      · rw [if_neg h, Nat.unpair_pair]
        have := read_le c (fuel z) j z.unpair.2
        omega

variable {c}

/-- The scan's state is exactly the emitter's value at the recorded stage.  The caller
supplies only that the emitter returns `1` at stage `0` — the code of the rational `0`. -/
lemma state_eq {val : ℕ → ℕ} (hc : ∀ x, c.eval x = Part.some (val x))
    (hval0 : ∀ i, val (Nat.pair 0 i) = 1) (z : ℕ) :
    ∀ j, state c z j = val (Nat.pair (stage c z j) z.unpair.2) + 1
  | 0 => by rw [state, stage, hval0]
  | j + 1 => by
      rw [state, stage, ifzSelFn]
      by_cases h : read c (fuel z) j z.unpair.2 = 0
      · rw [if_pos h, if_pos h, Nat.unpair_pair]
        exact state_eq hc hval0 z j
      · rw [if_neg h, if_neg h, Nat.unpair_pair]
        exact read_eq_of_ne_zero hc h

/-- A stage whose reading succeeds is never lost: the recorded stage only grows. -/
lemma le_stage {z j N : ℕ} (hj : j < N) (h : read c (fuel z) j z.unpair.2 ≠ 0) :
    j ≤ stage c z N := by
  induction N with
  | zero => omega
  | succ N ih =>
      rw [stage]
      by_cases hN : read c (fuel z) N z.unpair.2 = 0
      · rw [if_pos hN]
        rcases Nat.lt_or_ge j N with hlt | hge
        · exact ih hlt
        · have hjN : j = N := by omega
          subst hjN
          exact absurd hN h
      · rw [if_neg hN]; omega

/-- **Every fixed stage is eventually recorded.**  The clock `⟪⟪n,i⟫,⟪n,i⟫⟫` grows past the
fuel stage `m` needs, and `le_stage` never lets the recorded stage slip back. -/
lemma eventually_le_stage {val : ℕ → ℕ} (hc : ∀ x, c.eval x = Part.some (val x)) (m i : ℕ) :
    ∀ᶠ n in Filter.atTop, m ≤ stage c (Nat.pair n i) n := by
  obtain ⟨F₀, hF₀⟩ := read_ne_zero hc m i
  refine Filter.eventually_atTop.2 ⟨max (m + 1) F₀, fun n hn => ?_⟩
  have hni : n ≤ Nat.pair n i := Nat.left_le_pair n i
  have hfuel : F₀ ≤ fuel (Nat.pair n i) :=
    le_trans (le_trans (le_max_right _ _) hn) (le_trans hni (le_fuel _))
  have hsnd : (Nat.pair n i).unpair.2 = i := by simp
  have hne : read c (fuel (Nat.pair n i)) m (Nat.pair n i).unpair.2 ≠ 0 := by
    rw [hsnd]; exact hF₀ _ hfuel
  have hlt : m < n := lt_of_lt_of_le (Nat.lt_succ_self m) (le_trans (le_max_left _ _) hn)
  exact le_stage hlt hne

variable (c)

/-! ### The emission certificate

`PolyFueled.prec` over the packed input `w = ⟪z, ⟪j, prev⟫⟫`.  The only nontrivial input is
the clocked reading, which is `codeEvalnNat c` at a `Nat.pair`-assembled argument —
poly-fueled because `c` is a *fixed* code.  The state bound is `codeEvalBound c ⟪z,z⟫ + 2`,
polynomial in `z` for the same reason. -/

/-- The scan's step function on the packed `prec` input `w = ⟪z, ⟪j, prev⟫⟫`. -/
noncomputable def step (w : ℕ) : ℕ :=
  ifzSelFn
    (Nat.pair w.unpair.2.unpair.2
      (codeEvalnNat c
        (Nat.pair (Nat.pair w.unpair.1 w.unpair.1)
          (Nat.pair w.unpair.2.unpair.1 w.unpair.1.unpair.2))))
    (codeEvalnNat c
      (Nat.pair (Nat.pair w.unpair.1 w.unpair.1)
        (Nat.pair w.unpair.2.unpair.1 w.unpair.1.unpair.2)))

lemma state_succ (z j : ℕ) :
    state c z (j + 1) = step c (Nat.pair z (Nat.pair j (state c z j))) := by
  rw [step]
  simp only [Nat.unpair_pair]
  rfl

lemma step_polyFueled : ∃ cc, PolyFueled cc (step c) := by
  obtain ⟨cR, hR⟩ := codeEvalnNat_polyFueled c
  have hz : PolyFueled _ (fun w : ℕ => w.unpair.1) := PolyFueled.left
  have hr : PolyFueled _ (fun w : ℕ => w.unpair.2) := PolyFueled.right
  have hj := PolyFueled.left.comp hr
  have hprev := PolyFueled.right.comp hr
  have hi := PolyFueled.right.comp hz
  have hv := hR.comp ((hz.pair hz).pair (hj.pair hi))
  exact ⟨_, (ifzSel_polyFueled.comp ((hprev.pair hv).pair hv)).of_eq
    (fun w => by simp only [Nat.unpair_pair, step])⟩

/-- **The code the scan emits** at query `z = ⟪n, i⟫`: the encoded exact value at whatever
stage `< n` the clock last completed on index `i`. -/
noncomputable def selCode (z : ℕ) : ℕ := state c z z.unpair.1 - 1

lemma selCode_polyFueled : ∃ cc, PolyFueled cc (selCode c) := by
  obtain ⟨cs, hs⟩ := step_polyFueled c
  have hst : IsPolyBounded (fun m => state c m.unpair.1 m.unpair.2) := by
    refine IsPolyBounded.of_le
      (b' := fun m => codeEvalBound c (Nat.pair m.unpair.1 m.unpair.1) + 1 + 1)
      (((codeEvalBound_poly c).comp
        (isPolyBounded_fst.pair isPolyBounded_fst)).add_one.add_one) (fun m => ?_)
    have := state_le c m.unpair.1 m.unpair.2
    simpa [fuel] using this
  have hprec := PolyFueled.prec (PolyFueled.const 2) hs (st := state c)
    (state_zero c) (state_succ c) hst
  have hstate : PolyFueled _ (fun z => state c z z.unpair.1) :=
    (hprec.comp (PolyFueled.id.pair PolyFueled.left)).of_eq
      (fun z => by simp only [Nat.unpair_pair])
  exact ⟨_, (predc_polyFueled.comp hstate).of_eq (fun z => rfl)⟩

end SelfClamped

/-! ## The polynomial clock: the self-clamped stage table

The exact emitter `approxEmit` is *primitive* recursive, not poly-fueled: at stage `n` its
`(1/2)^(i+1)` weights already carry denominators of order `2^n`.  The fix is not to make it
cheaper but to let the interpreter's own clock decide how far it gets.

`Code.evaln` is **self-clamping**: every clause guards `n ≤ k`, so a code run with fuel `k`
can neither read an input above `k` nor return a value above `codeEvalBound c k`, which for
a *fixed* `c` is polynomial in `k` (`codeEvaln_result_le`, `codeEvalBound_poly`).  That is
the clamp the recursion needs, and it is free — it is already in `evaln`'s definition.  So
instead of re-engineering the dovetail's arithmetic, the poly-fuel emitter *runs the exact
emitter under a polynomial clock and keeps the best stage that finished*.  That scan is
`SelfClamped` above, instantiated here at `approxCode`: `SelfClamped.stage approxCode z n`
names the stage the last successful reading came from, so the emitted rational is literally
`universalApprox (stage …) σ` — hence nonneg, below the mass, and (since every fixed stage
eventually fits the growing clock, and the table is monotone) convergent to it.  All this
lane supplies is `approxCode`'s own totality and the analytic facts about
`universalApprox`. -/

/-- The exact stage emitter as a total program.  `approxEmit_prim` is primitive recursive,
so `Code.exists_code` names a code whose `eval` is total and equal to it. -/
noncomputable def approxCode : Nat.Partrec.Code :=
  (Nat.Partrec.Code.exists_code.mp
    (Nat.Partrec.of_primrec (Primrec.nat_iff.mp approxEmit_prim))).choose

lemma approxCode_eval : approxCode.eval = fun z ↦ Part.some (approxEmit z) :=
  (Nat.Partrec.Code.exists_code.mp
    (Nat.Partrec.of_primrec (Primrec.nat_iff.mp approxEmit_prim))).choose_spec

/-- The exact emitter is total on every input, in the form the self-clamped scan asks for. -/
lemma approxCode_eval_apply (x : ℕ) : approxCode.eval x = Part.some (approxEmit x) :=
  congrFun approxCode_eval x

/-- The string named by an index, as the exact emitter decodes it. -/
def dusString (i : ℕ) : List Bool := (Encodable.decode (α := List Bool) i).getD []

lemma universalApprox_zero (σ : List Bool) : universalApprox 0 σ = 0 := by
  simp [universalApprox]

/-- The exact emitter's value at stage `0` is the code of the rational `0`: the base case
`SelfClamped.state_eq` asks for. -/
lemma approxEmit_zero (i : ℕ) : approxEmit (Nat.pair 0 i) = 1 := by
  rw [approxEmit, Nat.unpair_pair, universalApprox_zero]
  rfl

/-! ### The emitted table -/

/-- **The poly-fuel stage table.**  On query `z = ⟪n, i⟫` it is the exact stage table at
whatever stage `< n` the clock `⟪z, z⟫` last completed on string `σᵢ`.
Paper node: `thm:dus` -/
noncomputable def dusApprox (z : ℕ) : ℚ :=
  universalApprox (SelfClamped.stage approxCode z z.unpair.1) (dusString z.unpair.2)

lemma dusApprox_nonneg (z : ℕ) : 0 ≤ dusApprox z := universalApprox_nonneg _ _

lemma dusApprox_le_mass (z : ℕ) :
    ((dusApprox z : ℚ) : ℝ) ≤ universalMass (dusString z.unpair.2) :=
  universalApprox_le _ _

lemma encode_dusApprox (z : ℕ) :
    Encodable.encode (dusApprox z) = SelfClamped.selCode approxCode z := by
  rw [SelfClamped.selCode,
    SelfClamped.state_eq approxCode_eval_apply approxEmit_zero z z.unpair.1]
  rw [dusApprox, approxEmit]
  simp only [Nat.unpair_pair, dusString]
  omega

/-- Every fixed stage is eventually reached: the clock `⟪⟪n,i⟫,⟪n,i⟫⟫` grows past the fuel
that stage `m` needs, and `SelfClamped.le_stage` never lets the stage slip back. -/
lemma dusApprox_eventually_ge (m i : ℕ) :
    ∀ᶠ n in atTop, universalApprox m (dusString i) ≤ dusApprox (Nat.pair n i) := by
  filter_upwards [SelfClamped.eventually_le_stage approxCode_eval_apply m i] with n hn
  rw [dusApprox]
  simp only [Nat.unpair_pair]
  exact universalApprox_mono _ hn

/-- The clocked table converges to the mass: it is below the mass at every stage, and above
every fixed stage of the exact table eventually.
Paper node: `thm:dus` -/
lemma dusApprox_tendsto (i : ℕ) :
    Tendsto (fun n ↦ ((dusApprox (Nat.pair n i) : ℚ) : ℝ)) atTop
      (𝓝 (universalMass (dusString i))) := by
  refine tendsto_order.2 ⟨fun a ha ↦ ?_, fun b hb ↦ ?_⟩
  · obtain ⟨m, hm⟩ := ((universalApprox_tendsto (dusString i)).eventually
      (eventually_gt_nhds ha)).exists
    filter_upwards [dusApprox_eventually_ge m i] with n hn
    exact lt_of_lt_of_le hm (by exact_mod_cast hn)
  · refine Filter.Eventually.of_forall fun n ↦ lt_of_le_of_lt ?_ hb
    have h := dusApprox_le_mass (Nat.pair n i)
    simpa using h

/-- **The poly-fuel emission certificate for the stage table.**  The whole argument is
`SelfClamped.selCode_polyFueled` at `approxCode`; the table's own arithmetic never enters.
Paper node: `thm:dus` -/
theorem dusApprox_polyRatCodes : PolyRatCodes dusApprox := by
  obtain ⟨c, hc⟩ := SelfClamped.selCode_polyFueled approxCode
  exact ⟨_, hc.of_eq (fun z ↦ (encode_dusApprox z).symm)⟩

/-! ### The approximation presentation -/

@[simp] lemma lowerSemicomputable_mass : lowerSemicomputable.mass = universalMass := rfl

/-- **`DUSApproximationPresentation` for the constructed universal semimeasure.**
Every field is discharged by this file: the table is the exact stage
table read under a polynomial clock, so it is nonneg and below the mass by construction,
converges because the clock eventually reaches every stage, and is poly-emitted because the
simulated code is fixed.
Paper node: `thm:dus` -/
noncomputable def dusApproximationPresentation {DP : DeductiveProcess}
    (B : BitPrefixSentences DP) (hB : ∀ i, B.enumeration i = dusString i) :
    DUSApproximationPresentation lowerSemicomputable B where
  approximation := fun n i ↦ dusApprox (Nat.pair n i)
  nonneg := fun _ _ ↦ dusApprox_nonneg _
  le_mass := fun n i ↦ by
    rw [hB i]
    show ((dusApprox (Nat.pair n i) : ℚ) : ℝ) ≤ universalMass (dusString i)
    simpa using dusApprox_le_mass (Nat.pair n i)
  tendsto := fun i ↦ by
    rw [hB i]
    show Tendsto (fun n ↦ ((dusApprox (Nat.pair n i) : ℚ) : ℝ)) atTop
      (𝓝 (universalMass (dusString i)))
    exact dusApprox_tendsto i

/-! ### The threshold emission

Both gate streams are rational arithmetic on the emitted stage rational: with
`q = N / D` in lowest terms and rung scale `k`, the base is `N / (4(k+1)D)`, so the
threshold sum is `N / (2(k+1)D)` and the inverse width is `4(k+1)D / N` (both zero when
`N = 0`, matching `ℚ`'s `x / 0 = 0`).  Both run on the shared `gcd`-reduced quotient emitter
`encode_natDiv_polyFueled` (`Framework/Emission/Computable.lean`). -/

/-- The gate query's stage-table argument: day `z.2`, string index `z.2.2`. -/
def dusQuery (z : ℕ) : ℕ := Nat.pair z.unpair.2 z.unpair.2.unpair.2

/-- Reduced numerator of the emitted stage rational at the gate query. -/
noncomputable def dusNum (z : ℕ) : ℕ :=
  (Encodable.encode (dusApprox (dusQuery z))).unpair.1 / 2

/-- Reduced denominator of the emitted stage rational at the gate query. -/
noncomputable def dusDen (z : ℕ) : ℕ :=
  (Encodable.encode (dusApprox (dusQuery z))).unpair.2

lemma dusNum_eq (z : ℕ) : dusNum z = (dusApprox (dusQuery z)).num.toNat := by
  rw [dusNum, encode_rat_of_nonneg (dusApprox_nonneg _), Nat.unpair_pair]
  omega

lemma dusDen_eq (z : ℕ) : dusDen z = (dusApprox (dusQuery z)).den := by
  rw [dusDen, encode_rat_of_nonneg (dusApprox_nonneg _), Nat.unpair_pair]

lemma dusDen_pos (z : ℕ) : 0 < dusDen z := by
  rw [dusDen_eq]; exact (dusApprox (dusQuery z)).den_pos

lemma dusApprox_query_eq (z : ℕ) :
    dusApprox (dusQuery z) = (dusNum z : ℚ) / (dusDen z : ℚ) := by
  have hnn : 0 ≤ (dusApprox (dusQuery z)).num := Rat.num_nonneg.mpr (dusApprox_nonneg _)
  have hcast : ((dusApprox (dusQuery z)).num.toNat : ℚ) = ((dusApprox (dusQuery z)).num : ℚ) := by
    exact_mod_cast congrArg (fun n : ℤ ↦ (n : ℚ)) (Int.toNat_of_nonneg hnn)
  rw [dusNum_eq, dusDen_eq, hcast]
  exact (Rat.num_div_den _).symm

lemma dusNum_polyFueled : ∃ c, PolyFueled c dusNum := by
  obtain ⟨c, hc⟩ := dusApprox_polyRatCodes
  obtain ⟨cdm, hdm⟩ := divmodc_polyFueled 2 (by norm_num)
  have hq : PolyFueled _ (fun z ↦ Nat.pair z.unpair.2 z.unpair.2.unpair.2) :=
    PolyFueled.right.pair (PolyFueled.right.comp PolyFueled.right)
  exact ⟨_, (PolyFueled.left.comp (hdm.comp (PolyFueled.left.comp (hc.comp hq)))).of_eq
    (fun z ↦ by simp only [Nat.unpair_pair]; rfl)⟩

lemma dusDen_polyFueled : ∃ c, PolyFueled c dusDen := by
  obtain ⟨c, hc⟩ := dusApprox_polyRatCodes
  have hq : PolyFueled _ (fun z ↦ Nat.pair z.unpair.2 z.unpair.2.unpair.2) :=
    PolyFueled.right.pair (PolyFueled.right.comp PolyFueled.right)
  exact ⟨_, (PolyFueled.right.comp (hc.comp hq)).of_eq (fun z ↦ rfl)⟩

/-- `z ↦ dusDen z * (w * (z.1 + 1))`, the gate denominators for `w = 2` and `w = 4`. -/
lemma dusGateDen_polyFueled (w : ℕ) :
    ∃ c, PolyFueled c (fun z ↦ dusDen z * (w * (z.unpair.1 + 1))) := by
  obtain ⟨cd, hd⟩ := dusDen_polyFueled
  obtain ⟨cm, hm⟩ := mul_polyFueled
  have hk1 := PolyFueled.left.succ_comp
  have hw := (hm.comp ((PolyFueled.const w).pair hk1)).of_eq
    (f' := fun z ↦ w * (z.unpair.1 + 1)) (fun z ↦ by simp only [Nat.unpair_pair])
  exact ⟨_, (hm.comp (hd.pair hw)).of_eq (fun z ↦ by simp only [Nat.unpair_pair])⟩

section Emission

-- The gate identities unfold `dusEmitBase` through nested `Nat.unpair`s; keep `Nat.sqrt`
-- opaque so `whnf` does not descend into the pairing implementation.
attribute [local irreducible] Nat.sqrt dusApprox dusNum dusDen

variable {DP : DeductiveProcess} (B : BitPrefixSentences DP)
  (hB : ∀ i, B.enumeration i = dusString i)

lemma dusEmitBase_eq (z : ℕ) :
    dusEmitBase (dusApproximationPresentation B hB) z
      = (dusNum z : ℚ) / ((dusDen z * (4 * (z.unpair.1 + 1)) : ℕ) : ℚ) := by
  have hD : (0 : ℚ) < (dusDen z : ℚ) := by exact_mod_cast dusDen_pos z
  have hk : (0 : ℚ) < ((z.unpair.1 : ℚ) + 1) := by positivity
  show dusApprox (dusQuery z) / (4 * ((z.unpair.1 : ℚ) + 1)) = _
  rw [dusApprox_query_eq]
  push_cast
  field_simp

lemma dusEmitSum_eq (z : ℕ) :
    dusEmitBase (dusApproximationPresentation B hB) z
        + dusEmitBase (dusApproximationPresentation B hB) z
      = (dusNum z : ℚ) / ((dusDen z * (2 * (z.unpair.1 + 1)) : ℕ) : ℚ) := by
  have hD : (0 : ℚ) < (dusDen z : ℚ) := by exact_mod_cast dusDen_pos z
  have hk : (0 : ℚ) < ((z.unpair.1 : ℚ) + 1) := by positivity
  rw [dusEmitBase_eq B hB]
  push_cast
  field_simp
  ring

lemma dusEmitRecip_eq (z : ℕ) :
    1 / dusEmitBase (dusApproximationPresentation B hB) z
      = ((dusDen z * (4 * (z.unpair.1 + 1)) : ℕ) : ℚ) / (dusNum z : ℚ) := by
  rw [dusEmitBase_eq B hB, one_div_div]

/-- **`DUSThresholdEmission` for the constructed universal semimeasure.**
Paper node: `thm:dus` -/
theorem dusThresholdEmission : DUSThresholdEmission (dusApproximationPresentation B hB) where
  threshold_sum_codes := by
    have hpoly : PolyRatCodes (fun z ↦
        dusEmitBase (dusApproximationPresentation B hB) z +
          dusEmitBase (dusApproximationPresentation B hB) z) := by
      obtain ⟨cn, hn⟩ := dusNum_polyFueled
      obtain ⟨cd, hd⟩ := dusGateDen_polyFueled 2
      obtain ⟨c, hc⟩ := encode_natDiv_polyFueled hn hd
      exact ⟨c, hc.of_eq (fun z ↦ by simp only [dusEmitSum_eq B hB])⟩
    exact DigitRatCodes.toMachine (DigitRatCodes.ofPolyRatCodes hpoly)
  inverse_width_codes := by
    have hpoly : PolyRatCodes (fun z ↦
        1 / dusEmitBase (dusApproximationPresentation B hB) z) := by
      obtain ⟨cn, hn⟩ := dusGateDen_polyFueled 4
      obtain ⟨cd, hd⟩ := dusNum_polyFueled
      obtain ⟨c, hc⟩ := encode_natDiv_polyFueled hn hd
      exact ⟨c, hc.of_eq (fun z ↦ by simp only [dusEmitRecip_eq B hB])⟩
    exact DigitRatCodes.toMachine (DigitRatCodes.ofPolyRatCodes hpoly)

end Emission

end Dovetail

end LogicalInduction
