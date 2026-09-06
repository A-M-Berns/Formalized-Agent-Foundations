import LogicalInduction.Construction.Freeze.PatternAutomaton
import LogicalInduction.Construction.Freeze.StructuredPatterns

/-!
# The finite-state half of the segment recognizer

Renders `app:ifp` (tex:6018): a `RunAuto.BlockAutomaton` deciding `SegMatchRelaxed` exactly.

`StructPat.SegMatch` is what the freeze must decide, and it is not regular: a structured
block's unary length field must agree with its payload's token count, an `aⁿbⁿ` constraint
that no `BlockAutomaton` expresses (see `RunAutomaton.lean`'s `BlockMachine`).  The decision
therefore splits, and this module carries the **regular half** — `SegMatchRelaxed`, which is
`SegMatch` with the length field left unchecked.  The counting half is a one-counter walk
over the same segment structure and lives in `SegmentCounter.lean`.

* `PayRec fc` is the payload-recognizer interface: a deterministic finite recognizer deciding
  `parseStructuredArithmeticFormula`'s complete-parse condition for one fixed formula code.
  Nothing here inhabits it; `SegRec.payRec` does.
* `payload_tokens_lt_23`: every token the structured grammar consumes is a tag below `23`,
  which is what the automaton's payload row enumerates.
* State encoding with `segK p = p.length + 1` and stride `segM`: control states `k`, `K + k`,
  `2K + k`, `3K + k`, payload states `4K + M * k + q`, and `segQ` the absorbing failure state
  and bound.
* `segRows` is the dispatch table, its polarity row guarded by `pol ≤ 1` because
  `StructBlockRelaxed` demands it; `segAuto` is the automaton.
* The run is proved phase by phase (`foldl_spay`, `foldl_slen`, `foldl_s2`, `foldl_s1`,
  `foldl_pos_struct`) and assembled by `foldl_segAuto` into `segAuto_accepts`.

Consumed by `SegmentRecognizer.lean`; `segAuto_accepts` is in `AxiomAudit.lean`.
-/

namespace LogicalInduction.SegAuto

open Complexity LogicalInduction.RunAuto LogicalInduction.StructPat

attribute [local irreducible] Nat.sqrt

/-! ## The payload recognizer, as an interface -/

/-- A deterministic finite recognizer for the payload language of one fixed formula code. -/
structure PayRec (fc : ℕ) where
  /-- The state bound. -/
  Q : ℕ
  /-- The initial state. -/
  init : ℕ
  /-- The transition function. -/
  step : ℕ → ℕ → ℕ
  /-- The accepting states. -/
  accept : ℕ → Bool
  /-- The initial state is below the bound. -/
  init_le : init ≤ Q
  /-- States stay below the bound. -/
  step_le : ∀ i t, i ≤ Q → step i t ≤ Q
  /-- And it decides a complete structured payload parse to `fc`. -/
  spec : ∀ q : List ℕ, accept (q.foldl step init) = true ↔
    parseStructuredArithmeticFormula q.length 0 q = some (fc, [])

/-! ## The relaxed language -/

lemma segMatchRelaxed_nil (b : List ℕ) : SegMatchRelaxed [] b ↔ b = [] := by
  constructor
  · rintro ⟨bs, hf, rfl⟩
    rw [List.forall₂_nil_left_iff.mp hf]
    rfl
  · rintro rfl
    exact ⟨[], List.Forall₂.nil, rfl⟩

lemma segMatchRelaxed_cons_left_iff {σ : StructPat.PatSeg} {p : List StructPat.PatSeg}
    {b : List ℕ} :
    SegMatchRelaxed (σ :: p) b ↔
      ∃ b₁ b₂, PatSeg.MatchesRelaxed σ b₁ ∧ SegMatchRelaxed p b₂ ∧ b = b₁ ++ b₂ := by
  constructor
  · rintro ⟨bs, hf, rfl⟩
    obtain ⟨b₁, bs', h₁, hrest, rfl⟩ := List.forall₂_cons_left_iff.mp hf
    exact ⟨b₁, bs'.flatten, h₁, ⟨bs', hrest, rfl⟩, by simp⟩
  · rintro ⟨b₁, b₂, h₁, ⟨bs, hf, rfl⟩, rfl⟩
    exact ⟨b₁ :: bs, List.Forall₂.cons h₁ hf, by simp⟩

/-- No pattern segment matches the empty run. -/
lemma patSegMatchesRelaxed_ne_nil {σ : StructPat.PatSeg} {b : List ℕ}
    (h : PatSeg.MatchesRelaxed σ b) : b ≠ [] := by
  cases σ with
  | lit t => rw [PatSeg.MatchesRelaxed] at h; simp [h]
  | hole χ =>
      obtain ⟨c, rfl, -⟩ := h
      simp
  | struct pol fc =>
      obtain ⟨L, q, rfl, -, -, -⟩ := h
      simp

lemma segMatchRelaxed_nil_right (p : List StructPat.PatSeg) :
    SegMatchRelaxed p [] ↔ p = [] := by
  cases p with
  | nil => simp [segMatchRelaxed_nil]
  | cons σ p =>
      constructor
      · intro h
        obtain ⟨b₁, b₂, h₁, -, hb⟩ := segMatchRelaxed_cons_left_iff.mp h
        exact absurd (List.append_eq_nil_iff.mp hb.symm).1 (patSegMatchesRelaxed_ne_nil h₁)
      · intro h; exact absurd h (by simp)

/-! ## Payload tokens are small

`parseStructuredArithmeticFormula_consumed_lt` concludes `x ≠ 19`, which is what its own
consumers need.  The automaton's payload row enumerates the token values `0 … 22`, so it
needs the numeric bound as well: everything the structured grammar consumes is a tag below
`23`.  This is that lemma; the term and numeral sub-grammars already have the stronger
`< 19` bound. -/
private lemma parseFormula_consumed_lt_23 :
    ∀ {fuel depth : ℕ} {ts : List ℕ} {code : ℕ} {rest : List ℕ},
      parseStructuredArithmeticFormula fuel depth ts = some (code, rest) →
      ∃ w, ts = w ++ rest ∧ ∀ x ∈ w, x < 23 := by
  intro fuel
  induction fuel with
  | zero =>
      intro depth ts code rest h
      simp [parseStructuredArithmeticFormula] at h
  | succ fuel ih =>
      intro depth ts code rest h
      rcases ts with _ | ⟨t, ts⟩
      · simp [parseStructuredArithmeticFormula] at h
      rw [parseStructuredArithmeticFormula] at h
      by_cases h9 : t = 9
      · rw [if_pos h9] at h
        obtain ⟨-, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
        exact ⟨[t], rfl, by simp [h9]⟩
      rw [if_neg h9] at h
      by_cases h10 : t = 10
      · rw [if_pos h10] at h
        obtain ⟨-, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
        exact ⟨[t], rfl, by simp [h10]⟩
      rw [if_neg h10] at h
      by_cases hrel : t = 11 ∨ t = 12 ∨ t = 13 ∨ t = 14
      · rw [if_pos hrel] at h
        rcases hp : parseStructuredArithmeticTerm fuel 0 ts with _ | q <;> simp [hp] at h
        rcases hq : parseStructuredArithmeticTerm fuel 0 q.2 with _ | r <;> simp [hq] at h
        obtain ⟨a, rfl, -⟩ := h
        obtain ⟨w₁, hts, hw₁⟩ := parseStructuredArithmeticTerm_consumed_lt hp
        obtain ⟨w₂, hp2, hw₂⟩ := parseStructuredArithmeticTerm_consumed_lt hq
        refine ⟨t :: w₁ ++ w₂, by rw [hts, hp2]; simp, ?_⟩
        rintro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · omega
        · rcases List.mem_append.mp hx' with hx₁ | hx₂
          · have := hw₁ x hx₁; omega
          · have := hw₂ x hx₂; omega
      rw [if_neg hrel] at h
      by_cases hbin : t = 15 ∨ t = 16
      · rw [if_pos hbin] at h
        rcases hp : parseStructuredArithmeticFormula fuel 0 ts with _ | q <;> simp [hp] at h
        rcases hq : parseStructuredArithmeticFormula fuel 0 q.2 with _ | r <;> simp [hq] at h
        obtain ⟨a, rfl, -⟩ := h
        obtain ⟨w₁, hts, hw₁⟩ := ih hp
        obtain ⟨w₂, hp2, hw₂⟩ := ih hq
        refine ⟨t :: w₁ ++ w₂, by rw [hts, hp2]; simp, ?_⟩
        rintro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · omega
        · rcases List.mem_append.mp hx' with hx₁ | hx₂
          · exact hw₁ x hx₁
          · exact hw₂ x hx₂
      rw [if_neg hbin] at h
      by_cases hquant : t = 17 ∨ t = 18
      · rw [if_pos hquant] at h
        rcases hp : parseStructuredArithmeticFormula fuel 0 ts with _ | q <;> simp [hp] at h
        rcases h with ⟨-, hrest⟩
        subst rest
        obtain ⟨w₁, hts, hw₁⟩ := ih hp
        refine ⟨t :: w₁, by rw [hts]; simp, ?_⟩
        rintro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · omega
        · exact hw₁ x hx'
      rw [if_neg hquant] at h
      by_cases h20 : t = 20
      · rw [if_pos h20] at h
        rcases hp : parseStructuredArithmeticFormula fuel 0 ts with _ | q <;> simp [hp] at h
        rcases h with ⟨-, hrest⟩
        subst rest
        obtain ⟨w₁, hts, hw₁⟩ := ih hp
        refine ⟨t :: w₁, by rw [hts]; simp, ?_⟩
        rintro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · omega
        · exact hw₁ x hx'
      rw [if_neg h20] at h
      by_cases h21 : t = 21
      · rw [if_pos h21] at h
        rcases hp : parseStructuredArithmeticFormula fuel 0 ts with _ | q <;> simp [hp] at h
        rcases hq : parseStructuredArithmeticFormula fuel 0 q.2 with _ | r <;> simp [hq] at h
        obtain ⟨a, rfl, -⟩ := h
        obtain ⟨w₁, hts, hw₁⟩ := ih hp
        obtain ⟨w₂, hp2, hw₂⟩ := ih hq
        refine ⟨t :: w₁ ++ w₂, by rw [hts, hp2]; simp, ?_⟩
        rintro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · omega
        · rcases List.mem_append.mp hx' with hx₁ | hx₂
          · exact hw₁ x hx₁
          · exact hw₂ x hx₂
      rw [if_neg h21] at h
      by_cases h22 : t = 22
      · rw [if_pos h22] at h
        rcases hp : parseStructuredArithmeticFormula fuel 0 ts with _ | q <;> simp [hp] at h
        rcases hq : parseStructuredArithmeticFormula fuel 0 q.2 with _ | r <;> simp [hq] at h
        obtain ⟨a, rfl, -⟩ := h
        obtain ⟨w₁, hts, hw₁⟩ := ih hp
        obtain ⟨w₂, hp2, hw₂⟩ := ih hq
        refine ⟨t :: w₁ ++ w₂, by rw [hts, hp2]; simp, ?_⟩
        rintro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · omega
        · rcases List.mem_append.mp hx' with hx₁ | hx₂
          · exact hw₁ x hx₁
          · exact hw₂ x hx₂
      rw [if_neg h22] at h
      exact absurd h (by simp)

lemma payload_tokens_lt_23 {q : List ℕ} {fc : ℕ}
    (h : parseStructuredArithmeticFormula q.length 0 q = some (fc, [])) :
    ∀ x ∈ q, x < 23 := by
  obtain ⟨w, hw, hlt⟩ := parseFormula_consumed_lt_23 h
  rw [List.append_nil] at hw
  subst hw
  exact hlt

/-! ## Row-table arithmetic -/

/-- `rowStep` scans its guards in order, so an appended table is tried after the prefix. -/
lemma rowStep_append : ∀ (l₁ l₂ : List (TokGuard × ℕ)) (d t : ℕ),
    rowStep (l₁ ++ l₂) d t = rowStep l₁ (rowStep l₂ d t) t
  | [], l₂, d, t => by rw [List.nil_append, rowStep]
  | (g, q) :: l₁, l₂, d, t => by
      rw [List.cons_append, rowStep, rowStep, rowStep_append l₁ l₂ d t]

/-- A full dispatch on the token values below `n`. -/
lemma rowStep_range (f : ℕ → ℕ) : ∀ (n d t : ℕ),
    rowStep ((List.range n).map (fun u => (litGuard u, f u))) d t = if t < n then f t else d
  | 0, d, t => by simp [rowStep]
  | n + 1, d, t => by
      rw [List.range_succ, List.map_append, rowStep_append, rowStep_range f n]
      simp only [List.map_cons, List.map_nil, rowStep, litGuard, decide_eq_true_eq]
      by_cases h1 : t < n
      · rw [if_pos h1, if_pos (show t < n + 1 by omega)]
      · rw [if_neg h1]
        by_cases h2 : t = n
        · rw [if_pos h2, if_pos (show t < n + 1 by omega), h2]
        · rw [if_neg h2, if_neg (show ¬ t < n + 1 by omega)]

/-! ## The state encoding

With `K := p.length + 1` and `M` one more than the largest payload-recognizer bound
occurring in `p`, the control states are

* `k` — about to start segment `k` (`k ≤ p.length`; accepting at `k = p.length`);
* `K + k` — inside struct segment `k`, having read the `1`, expecting the `0`;
* `2 * K + k` — expecting the polarity token;
* `3 * K + k` — inside the unary length field;
* `4 * K + M * k + q` — inside the payload, at payload-recognizer state `q < M`;
* `segQ R p = 4 * K + M * K` — the absorbing failure state.
-/

/-- The payload-recognizer bound a segment contributes. -/
def payQOf (R : ∀ fc, PayRec fc) : StructPat.PatSeg → ℕ
  | .struct _ fc => (R fc).Q
  | _ => 0

/-- The number of control states per phase. -/
def segK (p : List StructPat.PatSeg) : ℕ := p.length + 1

/-- The payload state stride: one more than the largest payload bound in `p`. -/
def segM (R : ∀ fc, PayRec fc) (p : List StructPat.PatSeg) : ℕ :=
  ((p.map (payQOf R)).foldr max 0) + 1

/-- The absorbing failure state, and the automaton's state bound. -/
def segQ (R : ∀ fc, PayRec fc) (p : List StructPat.PatSeg) : ℕ :=
  4 * segK p + segM R p * segK p

/-- The one statement of the control-slot count, used wherever a state decoding is unfolded
into arithmetic. -/
lemma segK_eq (p : List StructPat.PatSeg) : segK p = p.length + 1 := rfl

lemma segM_pos (R : ∀ fc, PayRec fc) (p : List StructPat.PatSeg) : 0 < segM R p :=
  Nat.succ_pos _

lemma four_segK_le_segQ (R : ∀ fc, PayRec fc) (p : List StructPat.PatSeg) :
    4 * segK p ≤ segQ R p := Nat.le_add_right _ _

private lemma le_foldr_max : ∀ (l : List ℕ) {x : ℕ}, x ∈ l → x ≤ l.foldr max 0
  | [], x, hx => absurd hx (by simp)
  | a :: l, x, hx => by
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact le_max_left _ _
      · exact le_trans (le_foldr_max l hx') (le_max_right _ _)

/-- Every payload bound occurring in `p` is below the stride. -/
lemma payQ_lt_segM (R : ∀ fc, PayRec fc) {p : List StructPat.PatSeg} {k pol fc : ℕ}
    (hk : k < p.length) (hs : p[k] = StructPat.PatSeg.struct pol fc) :
    (R fc).Q < segM R p := by
  have hmem : (R fc).Q ∈ p.map (payQOf R) := by
    refine List.mem_map.mpr ⟨p[k], List.getElem_mem hk, ?_⟩
    rw [hs, payQOf]
  have := le_foldr_max _ hmem
  rw [segM]
  omega

/-- The payload states really are below the bound. -/
lemma spay_lt {M k q K : ℕ} (hk : k + 1 ≤ K) (hq : q + 1 ≤ M) : M * k + q < M * K := by
  calc M * k + q < M * k + M := by omega
    _ = M * (k + 1) := by ring
    _ ≤ M * K := Nat.mul_le_mul_left _ hk

/-! ## The row table -/

/-- The dispatch table.  The index is decoded by comparing against `K`, `2K`, `3K`, `4K`,
and then dividing by the payload stride.

The polarity row is guarded by `pol ≤ 1`: `StructBlockRelaxed` demands it, and without the
guard the automaton would accept a polarity token no structured block may carry. -/
def segRows (H : PatAuto.HoleGuards) (R : ∀ fc, PayRec fc) (p : List StructPat.PatSeg)
    (i : ℕ) : GuardRow :=
  if i < segK p then
    match p[i]? with
    | some (.lit t) => ⟨[(litGuard t, i + 1)], segQ R p⟩
    | some (.hole χ) => ⟨[(H.guard χ, i + 1)], segQ R p⟩
    | some (.struct _ _) => ⟨[(litGuard 1, segK p + i)], segQ R p⟩
    | none => ⟨[], segQ R p⟩
  else if i < 2 * segK p then
    ⟨[(litGuard 0, 2 * segK p + (i - segK p))], segQ R p⟩
  else if i < 3 * segK p then
    match p[i - 2 * segK p]? with
    | some (.struct pol _) =>
        if pol ≤ 1 then ⟨[(litGuard pol, 3 * segK p + (i - 2 * segK p))], segQ R p⟩
        else ⟨[], segQ R p⟩
    | _ => ⟨[], segQ R p⟩
  else if i < 4 * segK p then
    match p[i - 3 * segK p]? with
    | some (.struct _ fc) =>
        ⟨[(litGuard 1, i),
          (litGuard 0, 4 * segK p + (segM R p * (i - 3 * segK p) + (R fc).init))], segQ R p⟩
    | _ => ⟨[], segQ R p⟩
  else if i < segQ R p then
    match p[(i - 4 * segK p) / segM R p]? with
    | some (.struct _ fc) =>
        ⟨(List.range 23).map (fun t =>
            (litGuard t,
              if t = 19 then
                (if (R fc).accept ((i - 4 * segK p) % segM R p) then
                    (i - 4 * segK p) / segM R p + 1
                  else segQ R p)
              else 4 * segK p +
                (segM R p * ((i - 4 * segK p) / segM R p)
                  + (R fc).step ((i - 4 * segK p) % segM R p) t))),
          segQ R p⟩
    | _ => ⟨[], segQ R p⟩
  else ⟨[], segQ R p⟩

/-- **The finite automaton for one segment pattern.** -/
def segAuto (H : PatAuto.HoleGuards) (R : ∀ fc, PayRec fc) (p : List StructPat.PatSeg) :
    BlockAutomaton :=
  guardedAutomaton (segQ R p) (segRows H R p) (fun i => decide (i = p.length))

section Steps

variable {H : PatAuto.HoleGuards} {R : ∀ fc, PayRec fc} {p : List StructPat.PatSeg}

lemma segAuto_step_eq (i t : ℕ) :
    (segAuto H R p).step i t
      = min (rowStep (segRows H R p i).guards (segRows H R p i).dflt t) (segQ R p) := rfl

lemma length_lt_segQ (R : ∀ fc, PayRec fc) (p : List StructPat.PatSeg) :
    p.length < segQ R p := by
  have h4 := four_segK_le_segQ R p
  have hKe := segK_eq p
  omega

/-- The failure state absorbs. -/
lemma step_rej (t : ℕ) : (segAuto H R p).step (segQ R p) t = segQ R p := by
  have h4 := four_segK_le_segQ R p
  have hKe := segK_eq p
  have hrow : segRows H R p (segQ R p) = ⟨[], segQ R p⟩ := by
    unfold segRows
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]
  rw [segAuto_step_eq, hrow]
  simp [rowStep]

lemma foldl_rej : ∀ b : List ℕ, List.foldl (segAuto H R p).step (segQ R p) b = segQ R p
  | [] => rfl
  | t :: b => by rw [List.foldl_cons, step_rej t]; exact foldl_rej b

lemma step_pos_end (t : ℕ) : (segAuto H R p).step p.length t = segQ R p := by
  have h4 := four_segK_le_segQ R p
  have hKe := segK_eq p
  have hrow : segRows H R p p.length = ⟨[], segQ R p⟩ := by
    unfold segRows
    rw [if_pos (by omega), List.getElem?_eq_none (le_refl _)]
  rw [segAuto_step_eq, hrow]
  simp [rowStep]

lemma step_pos_lit {k t₀ : ℕ} (hk : k < p.length) (hs : p[k] = StructPat.PatSeg.lit t₀)
    (t : ℕ) : (segAuto H R p).step k t = if t = t₀ then k + 1 else segQ R p := by
  have h4 := four_segK_le_segQ R p
  have hKe := segK_eq p
  have hrow : segRows H R p k = ⟨[(litGuard t₀, k + 1)], segQ R p⟩ := by
    unfold segRows
    rw [if_pos (by omega), List.getElem?_eq_getElem hk, hs]
  rw [segAuto_step_eq, hrow]
  simp only [rowStep, litGuard, decide_eq_true_eq]
  split_ifs <;> omega

lemma step_pos_hole {k : ℕ} {χ : Sentence} (hk : k < p.length)
    (hs : p[k] = StructPat.PatSeg.hole χ) (t : ℕ) :
    (segAuto H R p).step k t = if (H.guard χ).P t = true then k + 1 else segQ R p := by
  have h4 := four_segK_le_segQ R p
  have hKe := segK_eq p
  have hrow : segRows H R p k = ⟨[(H.guard χ, k + 1)], segQ R p⟩ := by
    unfold segRows
    rw [if_pos (by omega), List.getElem?_eq_getElem hk, hs]
  rw [segAuto_step_eq, hrow]
  simp only [rowStep]
  split_ifs <;> omega

lemma step_pos_struct {k pol fc : ℕ} (hk : k < p.length)
    (hs : p[k] = StructPat.PatSeg.struct pol fc) (t : ℕ) :
    (segAuto H R p).step k t = if t = 1 then segK p + k else segQ R p := by
  have h4 := four_segK_le_segQ R p
  have hKe := segK_eq p
  have hrow : segRows H R p k = ⟨[(litGuard 1, segK p + k)], segQ R p⟩ := by
    unfold segRows
    rw [if_pos (by omega), List.getElem?_eq_getElem hk, hs]
  rw [segAuto_step_eq, hrow]
  simp only [rowStep, litGuard, decide_eq_true_eq]
  split_ifs <;> omega

lemma step_s1 {k : ℕ} (hk : k < p.length) (t : ℕ) :
    (segAuto H R p).step (segK p + k) t = if t = 0 then 2 * segK p + k else segQ R p := by
  have h4 := four_segK_le_segQ R p
  have hKe := segK_eq p
  have hrow : segRows H R p (segK p + k) = ⟨[(litGuard 0, 2 * segK p + k)], segQ R p⟩ := by
    unfold segRows
    have hsub : segK p + k - segK p = k := by omega
    rw [if_neg (by omega), if_pos (by omega), hsub]
  rw [segAuto_step_eq, hrow]
  simp only [rowStep, litGuard, decide_eq_true_eq]
  split_ifs <;> omega

lemma step_s2 {k pol fc : ℕ} (hk : k < p.length)
    (hs : p[k] = StructPat.PatSeg.struct pol fc) (hpol : pol ≤ 1) (t : ℕ) :
    (segAuto H R p).step (2 * segK p + k) t =
      if t = pol then 3 * segK p + k else segQ R p := by
  have h4 := four_segK_le_segQ R p
  have hKe := segK_eq p
  have hsub : 2 * segK p + k - 2 * segK p = k := by omega
  have hrow : segRows H R p (2 * segK p + k)
      = ⟨[(litGuard pol, 3 * segK p + k)], segQ R p⟩ := by
    unfold segRows
    rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), hsub,
      List.getElem?_eq_getElem hk, hs]
    dsimp only
    rw [if_pos hpol]
  rw [segAuto_step_eq, hrow]
  simp only [rowStep, litGuard, decide_eq_true_eq]
  split_ifs <;> omega

lemma step_s2_bad {k pol fc : ℕ} (hk : k < p.length)
    (hs : p[k] = StructPat.PatSeg.struct pol fc) (hpol : ¬ pol ≤ 1) (t : ℕ) :
    (segAuto H R p).step (2 * segK p + k) t = segQ R p := by
  have h4 := four_segK_le_segQ R p
  have hKe := segK_eq p
  have hsub : 2 * segK p + k - 2 * segK p = k := by omega
  have hrow : segRows H R p (2 * segK p + k) = ⟨[], segQ R p⟩ := by
    unfold segRows
    rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), hsub,
      List.getElem?_eq_getElem hk, hs]
    dsimp only
    rw [if_neg hpol]
  rw [segAuto_step_eq, hrow]
  simp [rowStep]

lemma step_slen {k pol fc : ℕ} (hk : k < p.length)
    (hs : p[k] = StructPat.PatSeg.struct pol fc) (t : ℕ) :
    (segAuto H R p).step (3 * segK p + k) t =
      if t = 1 then 3 * segK p + k
      else if t = 0 then 4 * segK p + (segM R p * k + (R fc).init)
      else segQ R p := by
  have h4 := four_segK_le_segQ R p
  have hKe := segK_eq p
  have hsub : 3 * segK p + k - 3 * segK p = k := by omega
  have hrow : segRows H R p (3 * segK p + k) =
      ⟨[(litGuard 1, 3 * segK p + k),
        (litGuard 0, 4 * segK p + (segM R p * k + (R fc).init))], segQ R p⟩ := by
    unfold segRows
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega), hsub,
      List.getElem?_eq_getElem hk, hs]
  have hinit : segM R p * k + (R fc).init < segM R p * segK p :=
    spay_lt (by omega) (by have := payQ_lt_segM R hk hs; have := (R fc).init_le; omega)
  rw [segAuto_step_eq, hrow]
  simp only [rowStep, litGuard, decide_eq_true_eq]
  by_cases h1 : t = 1
  · rw [if_pos h1]; omega
  · rw [if_neg h1]
    by_cases h0 : t = 0
    · rw [if_pos h0]
      exact Nat.min_eq_left (Nat.le_of_lt (Nat.add_lt_add_left hinit (4 * segK p)))
    · rw [if_neg h0]; omega

lemma step_spay {k q pol fc : ℕ} (hk : k < p.length)
    (hs : p[k] = StructPat.PatSeg.struct pol fc) (hq : q ≤ (R fc).Q) (t : ℕ) :
    (segAuto H R p).step (4 * segK p + (segM R p * k + q)) t =
      if t < 23 then
        (if t = 19 then (if (R fc).accept q = true then k + 1 else segQ R p)
         else 4 * segK p + (segM R p * k + (R fc).step q t))
      else segQ R p := by
  have h4 := four_segK_le_segQ R p
  have hKe := segK_eq p
  have hqm : q < segM R p := by have := payQ_lt_segM R hk hs; omega
  have hlt : segM R p * k + q < segM R p * segK p := spay_lt (by omega) (by omega)
  have hsub : 4 * segK p + (segM R p * k + q) - 4 * segK p = segM R p * k + q :=
    Nat.add_sub_cancel_left (4 * segK p) (segM R p * k + q)
  have hdiv : (segM R p * k + q) / segM R p = k := by
    rw [Nat.mul_add_div (segM_pos R p), Nat.div_eq_of_lt hqm, Nat.add_zero]
  have hmod : (segM R p * k + q) % segM R p = q := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hqm]
  have hrow : segRows H R p (4 * segK p + (segM R p * k + q)) =
      ⟨(List.range 23).map (fun t =>
          (litGuard t,
            if t = 19 then (if (R fc).accept q = true then k + 1 else segQ R p)
            else 4 * segK p + (segM R p * k + (R fc).step q t))), segQ R p⟩ := by
    unfold segRows
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_pos (show 4 * segK p + (segM R p * k + q) < segQ R p from
        Nat.add_lt_add_left hlt (4 * segK p)), hsub, hdiv, hmod,
      List.getElem?_eq_getElem hk, hs]
  rw [segAuto_step_eq, hrow]
  simp only [rowStep_range]
  by_cases h23 : t < 23
  · rw [if_pos h23]
    by_cases h19 : t = 19
    · rw [if_pos h19]
      by_cases ha : (R fc).accept q = true
      · rw [if_pos ha]; omega
      · rw [if_neg ha]; omega
    · rw [if_neg h19]
      have hstep : (R fc).step q t ≤ (R fc).Q := (R fc).step_le q t hq
      have hlt' : segM R p * k + (R fc).step q t < segM R p * segK p :=
        spay_lt (by omega) (by have := payQ_lt_segM R hk hs; omega)
      exact Nat.min_eq_left (Nat.le_of_lt (Nat.add_lt_add_left hlt' (4 * segK p)))
  · rw [if_neg h23]; omega

/-! ### Non-accepting states

Only `pos p.length` accepts, and every other control state is numerically above it. -/

lemma rej_ne : segQ R p ≠ p.length := Nat.ne_of_gt (length_lt_segQ R p)

lemma s1_ne (k : ℕ) : segK p + k ≠ p.length := by
  have hKe := segK_eq p
  omega

lemma s2_ne (k : ℕ) : 2 * segK p + k ≠ p.length := by
  have hKe := segK_eq p
  omega

lemma slen_ne (k : ℕ) : 3 * segK p + k ≠ p.length := by
  have hKe := segK_eq p
  omega

lemma spay_ne (X : ℕ) : 4 * segK p + X ≠ p.length := by
  have hKe := segK_eq p
  omega

end Steps

/-! ## The run, phase by phase -/

section Runs

variable {H : PatAuto.HoleGuards} {R : ∀ fc, PayRec fc} {p : List StructPat.PatSeg}

/-- **The payload phase simulates the payload recognizer.**

From a payload state the automaton stays in the payload phase exactly while it reads
tokens below `23` other than the terminator `19`, and leaves it accepting exactly when the
recognizer accepts what it has read. -/
lemma foldl_spay {k pol fc : ℕ} (hk : k < p.length)
    (hs : p[k] = StructPat.PatSeg.struct pol fc) :
    ∀ (b : List ℕ) (q : ℕ), q ≤ (R fc).Q →
      (List.foldl (segAuto H R p).step (4 * segK p + (segM R p * k + q)) b = p.length ↔
        ∃ q' rest, b = q' ++ 19 :: rest ∧ 19 ∉ q' ∧ (∀ x ∈ q', x < 23) ∧
          (R fc).accept (q'.foldl (R fc).step q) = true ∧
          List.foldl (segAuto H R p).step (k + 1) rest = p.length)
  | [], q, _ => by
      rw [List.foldl_nil]
      constructor
      · intro h; exact absurd h (spay_ne _)
      · rintro ⟨q', rest, hb, -, -, -, -⟩; simp at hb
  | (t :: b), q, hq => by
      rw [List.foldl_cons, step_spay hk hs hq t]
      by_cases h23 : t < 23
      · rw [if_pos h23]
        by_cases h19 : t = 19
        · subst h19
          rw [if_pos rfl]
          by_cases ha : (R fc).accept q = true
          · rw [if_pos ha]
            constructor
            · intro h
              exact ⟨[], b, rfl, by simp, by simp, by simpa using ha, h⟩
            · rintro ⟨q', rest, hb, hn, -, -, hfin⟩
              cases q' with
              | nil =>
                  rw [List.nil_append] at hb
                  obtain ⟨-, rfl⟩ := List.cons.inj hb
                  exact hfin
              | cons c q'' =>
                  rw [List.cons_append] at hb
                  obtain ⟨rfl, -⟩ := List.cons.inj hb
                  exact absurd (List.mem_cons_self ..) hn
          · rw [if_neg ha, foldl_rej]
            constructor
            · intro h; exact absurd h rej_ne
            · rintro ⟨q', rest, hb, hn, -, hacc, -⟩
              cases q' with
              | nil =>
                  rw [List.foldl_nil] at hacc
                  exact absurd hacc ha
              | cons c q'' =>
                  rw [List.cons_append] at hb
                  obtain ⟨rfl, -⟩ := List.cons.inj hb
                  exact absurd (List.mem_cons_self ..) hn
        · rw [if_neg h19]
          rw [foldl_spay hk hs b ((R fc).step q t) ((R fc).step_le q t hq)]
          constructor
          · rintro ⟨q'', rest, rfl, hn, hlt, hacc, hfin⟩
            refine ⟨t :: q'', rest, rfl, ?_, ?_, ?_, hfin⟩
            · intro hc
              rcases List.mem_cons.mp hc with hc' | hc'
              · exact h19 hc'.symm
              · exact hn hc'
            · intro x hx
              rcases List.mem_cons.mp hx with rfl | hx'
              · exact h23
              · exact hlt x hx'
            · rwa [List.foldl_cons]
          · rintro ⟨q', rest, hb, hn, hlt, hacc, hfin⟩
            cases q' with
            | nil =>
                rw [List.nil_append] at hb
                exact absurd (List.cons.inj hb).1 h19
            | cons c q'' =>
                rw [List.cons_append] at hb
                obtain ⟨rfl, rfl⟩ := List.cons.inj hb
                refine ⟨q'', rest, rfl, fun hc => hn (List.mem_cons_of_mem _ hc),
                  fun x hx => hlt x (List.mem_cons_of_mem _ hx), ?_, hfin⟩
                rwa [List.foldl_cons] at hacc
      · rw [if_neg h23, foldl_rej]
        constructor
        · intro h; exact absurd h rej_ne
        · rintro ⟨q', rest, hb, -, hlt, -, -⟩
          cases q' with
          | nil =>
              rw [List.nil_append] at hb
              rw [(List.cons.inj hb).1] at h23
              exact absurd (by omega : (19 : ℕ) < 23) h23
          | cons c q'' =>
              rw [List.cons_append] at hb
              obtain ⟨rfl, -⟩ := List.cons.inj hb
              exact absurd (hlt t (List.mem_cons_self ..)) h23

/-- **The unary length field is read but not counted.** -/
lemma foldl_slen {k pol fc : ℕ} (hk : k < p.length)
    (hs : p[k] = StructPat.PatSeg.struct pol fc) :
    ∀ b : List ℕ,
      (List.foldl (segAuto H R p).step (3 * segK p + k) b = p.length ↔
        ∃ L rest, b = List.replicate L 1 ++ 0 :: rest ∧
          List.foldl (segAuto H R p).step
            (4 * segK p + (segM R p * k + (R fc).init)) rest = p.length)
  | [] => by
      rw [List.foldl_nil]
      constructor
      · intro h; exact absurd h (slen_ne k)
      · rintro ⟨L, rest, hb, -⟩
        cases L <;> simp [List.replicate_succ] at hb
  | (t :: b) => by
      rw [List.foldl_cons, step_slen hk hs t]
      by_cases h1 : t = 1
      · subst h1
        rw [if_pos rfl, foldl_slen hk hs b]
        constructor
        · rintro ⟨L, rest, rfl, hfin⟩
          exact ⟨L + 1, rest, by simp [List.replicate_succ], hfin⟩
        · rintro ⟨L, rest, hb, hfin⟩
          cases L with
          | zero => rw [List.replicate_zero, List.nil_append] at hb; simp at hb
          | succ L =>
              rw [List.replicate_succ, List.cons_append] at hb
              obtain ⟨-, rfl⟩ := List.cons.inj hb
              exact ⟨L, rest, rfl, hfin⟩
      · rw [if_neg h1]
        by_cases h0 : t = 0
        · subst h0
          rw [if_pos rfl]
          constructor
          · intro h; exact ⟨0, b, by simp, h⟩
          · rintro ⟨L, rest, hb, hfin⟩
            cases L with
            | zero =>
                rw [List.replicate_zero, List.nil_append] at hb
                obtain ⟨-, rfl⟩ := List.cons.inj hb
                exact hfin
            | succ L =>
                rw [List.replicate_succ, List.cons_append] at hb
                exact absurd (List.cons.inj hb).1 h1
        · rw [if_neg h0, foldl_rej]
          constructor
          · intro h; exact absurd h rej_ne
          · rintro ⟨L, rest, hb, -⟩
            cases L with
            | zero =>
                rw [List.replicate_zero, List.nil_append] at hb
                exact absurd (List.cons.inj hb).1 h0
            | succ L =>
                rw [List.replicate_succ, List.cons_append] at hb
                exact absurd (List.cons.inj hb).1 h1

/-- **The polarity token**: the pattern's own polarity must both name it and allow it. -/
lemma foldl_s2 {k pol fc : ℕ} (hk : k < p.length)
    (hs : p[k] = StructPat.PatSeg.struct pol fc) (b : List ℕ) :
    List.foldl (segAuto H R p).step (2 * segK p + k) b = p.length ↔
      pol ≤ 1 ∧ ∃ rest, b = pol :: rest ∧
        List.foldl (segAuto H R p).step (3 * segK p + k) rest = p.length := by
  by_cases hpol : pol ≤ 1
  · cases b with
    | nil =>
        rw [List.foldl_nil]
        constructor
        · intro h; exact absurd h (s2_ne k)
        · rintro ⟨-, rest, hb, -⟩; simp at hb
    | cons t b =>
        rw [List.foldl_cons, step_s2 hk hs hpol t]
        by_cases h : t = pol
        · rw [if_pos h]
          constructor
          · intro hh; exact ⟨hpol, b, by rw [h], hh⟩
          · rintro ⟨-, rest, hb, hr⟩
            obtain ⟨-, rfl⟩ := List.cons.inj hb
            exact hr
        · rw [if_neg h, foldl_rej]
          constructor
          · intro hh; exact absurd hh rej_ne
          · rintro ⟨-, rest, hb, -⟩
            exact absurd (List.cons.inj hb).1 h
  · cases b with
    | nil =>
        rw [List.foldl_nil]
        constructor
        · intro h; exact absurd h (s2_ne k)
        · rintro ⟨h, -⟩; exact absurd h hpol
    | cons t b =>
        rw [List.foldl_cons, step_s2_bad hk hs hpol t, foldl_rej]
        constructor
        · intro h; exact absurd h rej_ne
        · rintro ⟨h, -⟩; exact absurd h hpol

/-- **The `0` following the block's opening `1`.** -/
lemma foldl_s1 {k : ℕ} (hk : k < p.length) (b : List ℕ) :
    List.foldl (segAuto H R p).step (segK p + k) b = p.length ↔
      ∃ rest, b = 0 :: rest ∧
        List.foldl (segAuto H R p).step (2 * segK p + k) rest = p.length := by
  cases b with
  | nil =>
      rw [List.foldl_nil]
      constructor
      · intro h; exact absurd h (s1_ne k)
      · rintro ⟨rest, hb, -⟩; simp at hb
  | cons t b =>
      rw [List.foldl_cons, step_s1 hk t]
      by_cases h : t = 0
      · rw [if_pos h]
        constructor
        · intro hh; exact ⟨b, by rw [h], hh⟩
        · rintro ⟨rest, hb, hr⟩
          obtain ⟨-, rfl⟩ := List.cons.inj hb
          exact hr
      · rw [if_neg h, foldl_rej]
        constructor
        · intro hh; exact absurd hh rej_ne
        · rintro ⟨rest, hb, -⟩
          exact absurd (List.cons.inj hb).1 h

lemma structBlockRelaxed_ne_nil {pol fc : ℕ} {b : List ℕ}
    (h : StructBlockRelaxed pol fc b) : b ≠ [] := by
  obtain ⟨L, q, rfl, -, -, -⟩ := h
  simp

/-- **The whole structured-block phase.** -/
lemma foldl_pos_struct {k pol fc : ℕ} (hk : k < p.length)
    (hs : p[k] = StructPat.PatSeg.struct pol fc) (b : List ℕ) :
    List.foldl (segAuto H R p).step k b = p.length ↔
      ∃ b₁ b₂, StructBlockRelaxed pol fc b₁ ∧
        List.foldl (segAuto H R p).step (k + 1) b₂ = p.length ∧ b = b₁ ++ b₂ := by
  cases b with
  | nil =>
      rw [List.foldl_nil]
      constructor
      · intro h; omega
      · rintro ⟨b₁, b₂, hblk, -, hb⟩
        exact absurd (List.append_eq_nil_iff.mp hb.symm).1 (structBlockRelaxed_ne_nil hblk)
  | cons t b =>
      rw [List.foldl_cons, step_pos_struct hk hs t]
      by_cases h1 : t = 1
      · subst h1
        rw [if_pos rfl, foldl_s1 hk b]
        constructor
        · rintro ⟨rest, rfl, hrest⟩
          rw [foldl_s2 hk hs] at hrest
          obtain ⟨hpol, rest2, rfl, hrest2⟩ := hrest
          rw [foldl_slen hk hs] at hrest2
          obtain ⟨L, rest3, rfl, hrest3⟩ := hrest2
          rw [foldl_spay hk hs _ _ (R fc).init_le] at hrest3
          obtain ⟨q', rest4, rfl, hn, -, hacc, hfin⟩ := hrest3
          refine ⟨[1, 0, pol] ++ List.replicate L 1 ++ 0 :: q' ++ [19], rest4,
            ⟨L, q', rfl, hpol, ((R fc).spec q').mp hacc, hn⟩, hfin, by simp⟩
        · rintro ⟨b₁, b₂, ⟨L, q', rfl, hpol, hparse, hn⟩, hfin, hb⟩
          simp only [List.cons_append, List.nil_append, List.append_assoc,
            List.cons.injEq, true_and] at hb
          subst hb
          refine ⟨_, rfl, ?_⟩
          rw [foldl_s2 hk hs]
          refine ⟨hpol, _, rfl, ?_⟩
          rw [foldl_slen hk hs]
          refine ⟨L, _, rfl, ?_⟩
          rw [foldl_spay hk hs _ _ (R fc).init_le]
          exact ⟨q', b₂, by simp, hn, payload_tokens_lt_23 hparse,
            ((R fc).spec q').mpr hparse, hfin⟩
      · rw [if_neg h1, foldl_rej]
        constructor
        · intro h; exact absurd h rej_ne
        · rintro ⟨b₁, b₂, ⟨L, q', rfl, -, -, -⟩, -, hb⟩
          simp only [List.cons_append, List.nil_append, List.cons.injEq] at hb
          exact absurd hb.1 h1

/-! ## The main induction -/

/-- **The fold reaches the end state exactly on a relaxed match**, from any segment
boundary. -/
lemma foldl_segAuto (H : PatAuto.HoleGuards) (R : ∀ fc, PayRec fc)
    (p : List StructPat.PatSeg) :
    ∀ (n : ℕ) (b : List ℕ), b.length ≤ n → ∀ k, k ≤ p.length →
      (List.foldl (segAuto H R p).step k b = p.length ↔ SegMatchRelaxed (p.drop k) b) := by
  have hnil : ∀ (k : ℕ), k ≤ p.length →
      (List.foldl (segAuto H R p).step k ([] : List ℕ) = p.length ↔
        SegMatchRelaxed (p.drop k) []) := by
    intro k hk
    rw [List.foldl_nil, segMatchRelaxed_nil_right]
    constructor
    · intro h; subst h; simp
    · intro h; have := List.drop_eq_nil_iff.mp h; omega
  intro n
  induction n with
  | zero =>
      intro b hb k hk
      have hb0 : b = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hb0
      exact hnil k hk
  | succ n ih =>
      intro b hb k hk
      cases b with
      | nil => exact hnil k hk
      | cons t b =>
          rw [List.length_cons] at hb
          have hbn : b.length ≤ n := by omega
          by_cases hlt : k < p.length
          · rw [List.drop_eq_getElem_cons hlt, segMatchRelaxed_cons_left_iff]
            cases hseg : p[k] with
            | lit t₀ =>
                rw [List.foldl_cons, step_pos_lit hlt hseg]
                by_cases hgt : t = t₀
                · rw [if_pos hgt, ih b hbn (k + 1) (by omega)]
                  constructor
                  · intro h
                    exact ⟨[t], b, by rw [PatSeg.MatchesRelaxed, hgt], h, rfl⟩
                  · rintro ⟨b₁, b₂, hm, h2, heq⟩
                    rw [PatSeg.MatchesRelaxed] at hm
                    subst hm
                    rw [List.singleton_append] at heq
                    obtain ⟨-, rfl⟩ := List.cons.inj heq
                    exact h2
                · rw [if_neg hgt, foldl_rej]
                  constructor
                  · intro h; exact absurd h rej_ne
                  · rintro ⟨b₁, b₂, hm, -, heq⟩
                    rw [PatSeg.MatchesRelaxed] at hm
                    subst hm
                    rw [List.singleton_append] at heq
                    exact absurd (List.cons.inj heq).1 hgt
            | hole χ =>
                rw [List.foldl_cons, step_pos_hole hlt hseg]
                by_cases hgt : (H.guard χ).P t = true
                · rw [if_pos hgt, ih b hbn (k + 1) (by omega)]
                  constructor
                  · intro h
                    exact ⟨[t], b, ⟨t, rfl, (H.guard_spec χ t).mp hgt⟩, h, rfl⟩
                  · rintro ⟨b₁, b₂, ⟨c, rfl, -⟩, h2, heq⟩
                    rw [List.singleton_append] at heq
                    obtain ⟨-, rfl⟩ := List.cons.inj heq
                    exact h2
                · rw [if_neg hgt, foldl_rej]
                  constructor
                  · intro h; exact absurd h rej_ne
                  · rintro ⟨b₁, b₂, ⟨c, rfl, hc⟩, -, heq⟩
                    rw [List.singleton_append] at heq
                    obtain ⟨rfl, -⟩ := List.cons.inj heq
                    exact absurd ((H.guard_spec χ t).mpr hc) hgt
            | struct pol fc =>
                rw [foldl_pos_struct hlt hseg]
                constructor
                · rintro ⟨b₁, b₂, hblk, hfin, heq⟩
                  have hlen : b₂.length ≤ n := by
                    have hl := congrArg List.length heq
                    rw [List.length_cons, List.length_append] at hl
                    have h1 : 0 < b₁.length :=
                      List.length_pos_iff.mpr (structBlockRelaxed_ne_nil hblk)
                    omega
                  exact ⟨b₁, b₂, hblk, (ih b₂ hlen (k + 1) (by omega)).mp hfin, heq⟩
                · rintro ⟨b₁, b₂, hblk, hm, heq⟩
                  have hlen : b₂.length ≤ n := by
                    have hl := congrArg List.length heq
                    rw [List.length_cons, List.length_append] at hl
                    have h1 : 0 < b₁.length :=
                      List.length_pos_iff.mpr (structBlockRelaxed_ne_nil hblk)
                    omega
                  exact ⟨b₁, b₂, hblk, (ih b₂ hlen (k + 1) (by omega)).mpr hm, heq⟩
          · have hkk : k = p.length := by omega
            subst hkk
            rw [List.foldl_cons, step_pos_end, foldl_rej, List.drop_length,
              segMatchRelaxed_nil]
            constructor
            · intro h; exact absurd h rej_ne
            · intro h; exact absurd h (by simp)

/-- **The automaton decides the relaxed segment language.**

Paper node: `app:ifp` -/
lemma segAuto_accepts (H : PatAuto.HoleGuards) (R : ∀ fc, PayRec fc)
    (p : List StructPat.PatSeg) (b : List ℕ) :
    (segAuto H R p).Accepts b = true ↔ SegMatchRelaxed p b := by
  rw [BlockAutomaton.Accepts, segAuto, guardedAutomaton_accept, decide_eq_true_eq,
    BlockAutomaton.run]
  have h := foldl_segAuto H R p b.length b (le_refl _) 0 (Nat.zero_le _)
  rw [List.drop_zero] at h
  exact h

end Runs

end LogicalInduction.SegAuto
