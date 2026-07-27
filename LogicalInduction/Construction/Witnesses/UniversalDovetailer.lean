import LogicalInduction.Properties.UniversalSemimeasure

/-!
# The universal dovetailer (`M7-DUS-APPROX`, stage 1)

`Properties/UniversalSemimeasure.lean` states `thm:dus` for an arbitrary
`UniversalContinuousSemimeasure`.  This file *constructs* one: an explicit dovetail over
`Nat.Partrec.Code` with a stage clock.

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

## Disclosure (recorded at proof time)

The `approximation_computes` field of `LowerSemicomputableContinuousSemimeasure` — a
`Nat.Partrec.Code` for the stage table `universalApprox` — is **not** discharged here; see
`TODO(blueprint:M7-DUS-APPROX)` at `universalApprox_computes`.  Everything else in this file
is proved: each field of `ContinuousSemimeasure`, the monotone from-below stage
approximation with its limit, and the domination constant.
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

lemma rawVal_nonneg (c : Nat.Partrec.Code) (m f : ℕ) (σ : List Bool) :
    0 ≤ rawVal c m f σ := le_max_left _ _

lemma rawVal_le {c : Nat.Partrec.Code} {m f : ℕ} {σ : List Bool} {B : ℚ} (hB : 0 ≤ B)
    (h : ∀ y, c.evaln f (Nat.pair m (Encodable.encode σ)) = some y →
      ((Encodable.decode (α := ℚ) y).getD 0 : ℚ) ≤ B) :
    rawVal c m f σ ≤ B := by
  refine max_le hB ?_
  cases hy : c.evaln f (Nat.pair m (Encodable.encode σ)) with
  | none => simpa [hy] using hB
  | some y => simpa [hy] using h y hy

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

lemma rawTable_le_of_forall {c : Nat.Partrec.Code} {σ : List Bool} {B : ℚ} (hB : 0 ≤ B)
    (h : ∀ m f, rawVal c m f σ ≤ B) : ∀ n, rawTable c n σ ≤ B
  | 0 => hB
  | n + 1 => max_le (rawTable_le_of_forall hB h n) (h _ _)

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
    trimStage prev rw [] = min (rw []) 1 :=
  List.reverseRecOn_nil _ _

lemma trimStage_concat (prev rw : List Bool → ℚ) (σ : List Bool) (b : Bool) :
    trimStage prev rw (σ ++ [b]) = childVal prev rw (trimStage prev rw σ) σ b :=
  List.reverseRecOn_concat _ _ _ _

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
nothing in the limit. -/
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

/-- The dovetail run on `ν`'s own approximation program reproduces `ν` exactly. -/
theorem dovetailMass_eq_mass (σ : List Bool) :
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
is the object whose polynomial emission the `M7-DUS-APPROX` boundary asks for; note the
bound is on the *stage*, not the limit.
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
        tendsto_finset_sum _ fun i _ ↦ (dovetailMass_tendsto (codeOf i) σ).const_mul _
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
for the mixture's own stage table, so neither depends on the disclosed gap below. -/

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
`UniversalContinuousSemimeasure.universal`, proved without the disclosed emission gap.
Paper node: `thm:dus` -/
theorem universalMass_dominates (ν : LowerSemicomputableContinuousSemimeasure) :
    ∃ K : ℝ, 0 < K ∧ ∀ σ, K * ν.mass σ ≤ universalMass σ :=
  ⟨wt (Encodable.encode ν.approximation_code), wt_pos _, fun σ ↦ by
    have h := wt_mul_dovetailMass_le (Encodable.encode ν.approximation_code) σ
    rw [codeOf, Denumerable.ofNat_encode, dovetailMass_eq_mass ν σ] at h
    exact h⟩

/-! ### The one undischarged obligation of this file. -/

/-- **Disclosed gap (`M7-DUS-APPROX`).**  `universalApprox` is a manifestly effective
table — stage `n` runs the first `n` programs of the dovetail for at most `n` clock ticks
each, with no unbounded search — but the `Nat.Partrec.Code` witnessing that, and hence the
`approximation_computes` field of `LowerSemicomputableContinuousSemimeasure`, is not
constructed here.

TODO(blueprint:M7-DUS-APPROX): need a `Nat.Partrec.Code` for
`fun z ↦ Encodable.encode (universalApprox z.unpair.1 ((Encodable.decode z.unpair.2).getD []))`.
The obstruction is purely presentational: `trim` is a `Nat.rec` over the stage clock whose
state is a *function* on strings, which no `Primcodable` state can hold.  The finite-state
reformulation that removes it is **column tabulation**, transposing the recursion so that
the induction is on the string and the clock is tabulated:

  `tabCol c r N : List ℚ`, the column `[trim c 0 r.reverse, …, trim c N r.reverse]`,
  by structural recursion on the *reversed* string `r` (so extension is `cons`):
  * `tabCol c [] N = (List.range (N+1)).map (root value at that stage)`;
  * both children of `r` must be produced together, since the `true` child reads the
    `false` child's new value — so the step is a single `List.foldl` over
    `List.range N` carrying `(ℚ × ℚ)` and emitting the two child columns from the
    parent column.

  The state is then `List ℚ` (`Primcodable`, via this repo's `ratPrimcodable`), the
  recursion is `Primrec.list_rec`, and `trim c n σ = (tabCol c σ.reverse n).getD n 0`.
  Rational arithmetic is already available primitively recursively in
  `Construction/LIACompiler.lean` (`ratAdd_prim`, `ratMul_prim`, `ratDiv_prim`,
  `ratMax_prim`, `ratLE_prim`, `ratPrimcodable`); `rawTable` needs only
  `Nat.Partrec.Code.primrec_evaln` and `Primrec.decode`.  Finish with
  `Nat.Partrec.Code.exists_code` + `Nat.Partrec.Code.evaln_complete`, as in
  `Construction/Witnesses/ComputationDP.lean`.

The polynomial refinement (`PolyRatCodes`, needed for `DUSApproximationPresentation` and
so for the fully-discharged `thm:dus` endpoint) is a further, strictly larger step on top
of this one. -/
theorem exists_universalApprox_code :
    ∃ c : Nat.Partrec.Code, ∀ n σ, ∃ fuel,
      c.evaln fuel (Nat.pair n (Encodable.encode σ)) =
        some (Encodable.encode (universalApprox n σ)) := by
  sorry

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
  universal := fun ν ↦
    ⟨wt (Encodable.encode ν.approximation_code), wt_pos _, fun σ ↦ by
      have h := wt_mul_dovetailMass_le (Encodable.encode ν.approximation_code) σ
      rw [codeOf, Denumerable.ofNat_encode, dovetailMass_eq_mass ν σ] at h
      exact h⟩

#print axioms continuousSemimeasure
#print axioms universalMass_dominates
#print axioms dovetailMass_eq_mass
#print axioms trim_tendsto_of_exact
#print axioms universalApprox_tendsto
#print axioms universalSemimeasure

end Dovetail

end LogicalInduction
