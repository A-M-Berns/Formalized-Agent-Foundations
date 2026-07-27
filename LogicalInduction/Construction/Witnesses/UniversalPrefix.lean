import LogicalInduction.Construction.Witnesses.PrefixMachine
import LogicalInduction.Construction.Witnesses.UniversalDovetailer

/-!
# A universal prefix machine and its prefix complexity (`M7-PREFIX-UNIVERSAL`)

`PrefixMachine.lean` instantiates the Occam boundary at the length function of a *fixed*
computable self-delimiting code.  This file removes that restriction: it constructs a
genuine **self-delimiting universal machine** `U` and instantiates the same boundary at
its prefix complexity `κ_U`.

## The machine

`U` reads a self-delimiting tag off the front of its input and then dispatches to one of
three families.  Writing `⌜φ⌝` for `Encodable.encode φ` and `natCode n` for the
self-delimiting integer code of `PrefixMachine.lean`:

| codeword | value |
| --- | --- |
| `0 ∷ natCode n` | `n` |
| `1 ∷ 0 ∷ v` | `¬`-code of `U v` |
| `1 ∷ 1 ∷ natCode e ++ w` | `φ_e(w)`, when `w` is in the prefix-free domain carved out for machine `e` |

The three families are separated by their tags, each is prefix-free, and the second is
prefix-free *because* the whole domain is (structural recursion on the codeword length),
so `dom U` is prefix-free by construction — no Kraft hypothesis is ever assumed.

* Family 1 is the **coverage** family: every value is reachable, so `κ_U` is total and
  finite, and no separate surjectivity argument is needed.
* Family 2 is the hard-wired **negation instruction**: it makes the additive negation
  overhead of `PrefixNegationCompiler` an explicit `2` rather than the size of a compiler
  index.  Hard-wiring finitely many instructions into a universal machine is standard and
  changes `κ_U` only by an additive constant.
* Family 3 is the **universal** family, and it is what earns the name: `acc` prefix-ifies
  the dovetailed enumeration of all `Nat.Partrec.Code`s on all bit strings — a string is
  accepted for machine `e` only if it halts and is incomparable with every string already
  accepted for `e`.  For a machine whose halting domain is *already* prefix-free (i.e. an
  honest prefix machine) nothing is ever rejected, so its domain survives intact.  That is
  the invariance theorem `kappaU_le_of_prefixMachine`: `κ_U ≤ κ_M + O(1)` for every prefix
  machine `M`, with the constant `2·size(⌜M⌝+1) + 3`.

`κ_U φ` is the least codeword length reaching `⌜φ⌝`, plus one slack bit — i.e. the length
function of "discard one bit, then run `U`", still a universal prefix machine.  The slack
bit is what pays for the multiplicity-two sentence enumeration in the Kraft field, exactly
as in `PrefixMachine.lean`.

## What is *not* claimed

`κ_U` is uncomputable (as universal prefix complexity must be), so the boundary's
approximation field does real work here: `kappaStage n` is the from-below stage table,
mining only the codewords discovered by stage `n`.  It is antitone, and *eventually equal*
to `κ_U` pointwise, which is what makes the weights lower-semicomputable.  That stage table
*is* computable — a bounded search over codewords of length `≤ |natCode ⌜φ⌝| + 1` — and its
program (`uCode`) is constructed here, so the boundary instantiation has no operational
input left over.
Paper node: `thm:ob`
-/

namespace LogicalInduction

open LO.Propositional Filter Topology

namespace UPrefix

/-! ## Decoding the self-delimiting integer code

`natVal` inverts `natCode` by bounded search: a codeword of length `ℓ` can only encode a
number below `2 ^ ℓ`, so the search range is explicit. -/

/-- Bounded inverse of `natCode`. -/
def natVal (u : List Bool) : Option ℕ :=
  ((List.range (2 ^ u.length)).filter (fun n => decide (natCode n = u))).head?

lemma natVal_spec {u : List Bool} {n : ℕ} (h : natVal u = some n) : natCode n = u := by
  have hmem : n ∈ (List.range (2 ^ u.length)).filter (fun m => decide (natCode m = u)) :=
    List.mem_of_mem_head? h
  simpa using (List.mem_filter.mp hmem).2

lemma natVal_natCode (n : ℕ) : natVal (natCode n) = some n := by
  have hlt : n < 2 ^ (natCode n).length := by
    have h1 : n + 1 < 2 ^ (n + 1).size := Nat.lt_size_self (n + 1)
    have h2 : (2 : ℕ) ^ (n + 1).size ≤ 2 ^ (natCode n).length := by
      apply Nat.pow_le_pow_right (by norm_num)
      rw [natCode_length]; omega
    omega
  have hmem : n ∈ (List.range (2 ^ (natCode n).length)).filter
      (fun m => decide (natCode m = natCode n)) := by
    simp [List.mem_filter, hlt]
  set L := (List.range (2 ^ (natCode n).length)).filter
    (fun m => decide (natCode m = natCode n)) with hL
  cases hcase : L with
  | nil => rw [hcase] at hmem; simp at hmem
  | cons m l =>
      have hm : m ∈ L := by rw [hcase]; simp
      have : natCode m = natCode n := by simpa using (List.mem_filter.mp hm).2
      have : m = n := natCode_prefix_inj (this ▸ List.prefix_refl _)
      rw [natVal, ← hL, hcase]
      simp [this]

/-! ## The prefix-ified dovetail

At stage `t = ⟪e, ⟪⌜w⌝, f⟫⟫` the candidate is "machine `e` on string `w` with fuel `f`".
It is accepted when the run finishes *and* `w` is incomparable with every string already
accepted for `e`.  A string comparable with an accepted one — in particular an already
accepted string itself — is therefore never accepted twice, and the accepted set for each
machine is an antichain by construction. -/

/-- The machine index examined at stage `t`. -/
def candCode (t : ℕ) : ℕ := t.unpair.1

/-- The candidate string examined at stage `t`. -/
def candWord (t : ℕ) : List Bool :=
  (Encodable.decode (α := List Bool) t.unpair.2.unpair.1).getD []

/-- The fuel offered at stage `t`. -/
def candFuel (t : ℕ) : ℕ := t.unpair.2.unpair.2

/-- The clocked run examined at stage `t`. -/
def candHit (t : ℕ) : Option ℕ :=
  (Denumerable.ofNat Nat.Partrec.Code (candCode t)).evaln (candFuel t)
    (Encodable.encode (candWord t))

/-- The acceptance guard: the run finished, and the candidate is incomparable with every
string already accepted for the same machine. -/
def accOK (t : ℕ) (L : List (ℕ × List Bool)) : Bool :=
  (candHit t).isSome &&
    L.all (fun p => !(decide (p.1 = candCode t) &&
      (decide (p.2 <+: candWord t) || decide (candWord t <+: p.2))))

/-- The strings accepted after `t` stages. -/
def acc : ℕ → List (ℕ × List Bool)
  | 0 => []
  | t + 1 => if accOK t (acc t) then (candCode t, candWord t) :: acc t else acc t

/-- Membership in the prefix-free domain carved out for machine `e`. -/
def Accepted (e : ℕ) (w : List Bool) : Prop := ∃ t, (e, w) ∈ acc t

lemma acc_succ_subset (t : ℕ) : acc t ⊆ acc (t + 1) := by
  intro p hp
  rw [acc]
  by_cases h : accOK t (acc t) <;> simp [h, hp]

lemma acc_mono {t s : ℕ} (h : t ≤ s) : acc t ⊆ acc s := by
  induction s with
  | zero => simp [Nat.le_zero.mp h]
  | succ s ih =>
      rcases Nat.lt_or_ge t (s + 1) with hlt | hge
      · exact fun p hp => acc_succ_subset s (ih (by omega) hp)
      · have : t = s + 1 := by omega
        subst this; exact fun p hp => hp

/-- Everything accepted really halts. -/
lemma acc_halts : ∀ (t : ℕ), ∀ p ∈ acc t,
    ∃ y, y ∈ (Denumerable.ofNat Nat.Partrec.Code p.1).eval (Encodable.encode p.2)
  | 0 => by simp [acc]
  | t + 1 => by
      intro p hp
      rw [acc] at hp
      by_cases h : accOK t (acc t)
      · rw [if_pos h] at hp
        rcases List.mem_cons.mp hp with rfl | hp'
        · have hs : (candHit t).isSome := by
            simpa using (Bool.and_eq_true .. ▸ h : (candHit t).isSome = true ∧ _).1
          obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hs
          exact ⟨y, Nat.Partrec.Code.evaln_sound hy⟩
        · exact acc_halts t p hp'
      · rw [if_neg h] at hp; exact acc_halts t p hp

/-- The guard, read backwards: an accepted candidate is incomparable with everything
already accepted for its machine. -/
lemma accOK_guard {t : ℕ} {L : List (ℕ × List Bool)} (h : accOK t L = true)
    {p : ℕ × List Bool} (hp : p ∈ L) (he : p.1 = candCode t) :
    ¬ p.2 <+: candWord t ∧ ¬ candWord t <+: p.2 := by
  rw [accOK, Bool.and_eq_true] at h
  have := List.all_eq_true.mp h.2 p hp
  simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
    Bool.or_eq_false_iff] at this
  rcases this with hne | ⟨h1, h2⟩
  · exact absurd he hne
  · exact ⟨by simpa using h1, by simpa using h2⟩

/-- The accepted strings of each machine form an antichain — the prefix-freeness that the
Kraft budget rests on, built in rather than assumed. -/
lemma acc_antichain : ∀ (t : ℕ) (p q : ℕ × List Bool), p ∈ acc t → q ∈ acc t →
    p.1 = q.1 → p.2 <+: q.2 → p = q
  | 0 => by simp [acc]
  | t + 1 => by
      intro p q hp hq hcode hpre
      rw [acc] at hp hq
      by_cases h : accOK t (acc t)
      · rw [if_pos h] at hp hq
        rcases List.mem_cons.mp hp with rfl | hp' <;> rcases List.mem_cons.mp hq with rfl | hq'
        · rfl
        · exact absurd hpre (accOK_guard h hq' hcode.symm).2
        · exact absurd hpre (accOK_guard h hp' hcode).1
        · exact acc_antichain t p q hp' hq' hcode hpre
      · rw [if_neg h] at hp hq
        exact acc_antichain t p q hp hq hcode hpre

lemma Accepted.halts {e : ℕ} {w : List Bool} (h : Accepted e w) :
    ∃ y, y ∈ (Denumerable.ofNat Nat.Partrec.Code e).eval (Encodable.encode w) := by
  obtain ⟨t, ht⟩ := h
  exact acc_halts t (e, w) ht

lemma Accepted.antichain {e : ℕ} {w w' : List Bool} (h : Accepted e w) (h' : Accepted e w')
    (hpre : w <+: w') : w = w' := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨s, hs⟩ := h'
  have ht' : (e, w) ∈ acc (max t s) := acc_mono (le_max_left t s) ht
  have hs' : (e, w') ∈ acc (max t s) := acc_mono (le_max_right t s) hs
  exact congrArg Prod.snd (acc_antichain _ (e, w) (e, w') ht' hs' rfl hpre)

/-! ## The machine -/

/-- Code-level negation: `negCode ⌜φ⌝ = ⌜∼φ⌝` (Foundation's `∼φ` is literally `φ 🡒 ⊥`,
and `⌜⊥⌝ = 1`). -/
def negCode (y : ℕ) : ℕ := Nat.pair 2 (Nat.pair y 1) + 1

lemma negCode_encode (φ : Sentence) : negCode (Encodable.encode φ) = Encodable.encode (∼φ) :=
  rfl

/-- **The universal prefix machine.**  `UHalt v y` says that `U` on codeword `v` halts
with value `y`.  The three families are separated by the leading tag bits, so the union is
prefix-free (`UHalt_prefixFree`) and single-valued (`UHalt_functional`).
Paper node: `thm:ob` -/
def UHalt : List Bool → ℕ → Prop
  | [], _ => False
  | false :: u, y => natVal u = some y
  | [true], _ => False
  | true :: false :: v, y => ∃ x, UHalt v x ∧ y = negCode x
  | true :: true :: v, y =>
      ∃ e w, natCode e ++ w = v ∧ Accepted e w ∧
        y ∈ (Denumerable.ofNat Nat.Partrec.Code e).eval (Encodable.encode w)

@[simp] lemma UHalt_builtin (u : List Bool) (y : ℕ) :
    UHalt (false :: u) y ↔ natVal u = some y := Iff.rfl

@[simp] lemma UHalt_neg (v : List Bool) (y : ℕ) :
    UHalt (true :: false :: v) y ↔ ∃ x, UHalt v x ∧ y = negCode x := Iff.rfl

@[simp] lemma UHalt_univ (v : List Bool) (y : ℕ) :
    UHalt (true :: true :: v) y ↔
      ∃ e w, natCode e ++ w = v ∧ Accepted e w ∧
        y ∈ (Denumerable.ofNat Nat.Partrec.Code e).eval (Encodable.encode w) := Iff.rfl

lemma UHalt_natCode (n : ℕ) : UHalt (false :: natCode n) n := by
  simp [natVal_natCode]

/-- Splitting a family-3 codeword: the machine index is determined, and the residual
strings inherit the prefix relation. -/
lemma natCode_append_prefix {e e' : ℕ} {w w' : List Bool}
    (h : natCode e ++ w <+: natCode e' ++ w') : e = e' ∧ w <+: w' := by
  have h1 : natCode e <+: natCode e' ++ w' := (List.prefix_append _ _).trans h
  have h2 : natCode e' <+: natCode e' ++ w' := List.prefix_append _ _
  have he : e = e' := by
    rcases le_total (natCode e).length (natCode e').length with hle | hle
    · exact natCode_prefix_inj (List.prefix_of_prefix_length_le h1 h2 hle)
    · exact (natCode_prefix_inj (List.prefix_of_prefix_length_le h2 h1 hle)).symm
  subst he
  exact ⟨rfl, List.prefix_append_right_inj _ |>.mp h⟩

/-- `U` is a partial *function*. -/
lemma UHalt_functional : ∀ (v : List Bool) (y y' : ℕ), UHalt v y → UHalt v y' → y = y'
  | [], _, _, h, _ => absurd h (by simp [UHalt])
  | false :: _, _, _, h, h' => by
      rw [UHalt_builtin] at h h'; rw [h] at h'; exact Option.some_injective _ h'
  | [true], _, _, h, _ => absurd h (by simp [UHalt])
  | true :: false :: v, _, _, h, h' => by
      obtain ⟨x, hx, rfl⟩ := h
      obtain ⟨x', hx', rfl⟩ := h'
      rw [UHalt_functional v x x' hx hx']
  | true :: true :: v, _, _, h, h' => by
      obtain ⟨e, w, hv, _, hy⟩ := h
      obtain ⟨e', w', hv', _, hy'⟩ := h'
      have hsame : natCode e ++ w = natCode e' ++ w' := hv.trans hv'.symm
      have hpre : natCode e ++ w <+: natCode e' ++ w' := by
        rw [hsame]
      obtain ⟨he, -⟩ := natCode_append_prefix hpre
      subst he
      have hww : w = w' := List.append_cancel_left hsame
      subst hww
      exact Part.mem_unique hy hy'

/-- **`dom U` is prefix-free** — by construction, not by hypothesis. -/
lemma UHalt_prefixFree : ∀ (n : ℕ) (v v' : List Bool) (y y' : ℕ), v.length ≤ n →
    UHalt v y → UHalt v' y' → v <+: v' → v = v' := by
  intro n
  induction n with
  | zero =>
      intro v v' y y' hlen h _ _
      have : v = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
      subst this; exact absurd h (by simp [UHalt])
  | succ n ih =>
      intro v v' y y' hlen h h' hpre
      match v, v' with
      | [], _ => exact absurd h (by simp [UHalt])
      | _, [] => simp only [List.prefix_nil] at hpre; exact hpre
      | false :: u, false :: u' =>
          have hu : u <+: u' := (List.cons_prefix_cons.mp hpre).2
          rw [UHalt_builtin] at h h'
          rw [← natVal_spec h, ← natVal_spec h'] at hu ⊢
          rw [natCode_prefix_inj hu]
      | false :: _, true :: _ => simp at hpre
      | true :: _, false :: _ => simp at hpre
      | [true], _ => exact absurd h (by simp [UHalt])
      | true :: false :: v, [true] =>
          exact absurd (List.IsPrefix.length_le hpre) (by simp)
      | true :: true :: v, [true] =>
          exact absurd (List.IsPrefix.length_le hpre) (by simp)
      | true :: false :: v, true :: false :: v' =>
          have hv : v <+: v' := (List.cons_prefix_cons.mp
            (List.cons_prefix_cons.mp hpre).2).2
          obtain ⟨x, hx, -⟩ := h
          obtain ⟨x', hx', -⟩ := h'
          rw [ih v v' x x' (by simp at hlen; omega) hx hx' hv]
      | true :: false :: v, true :: true :: v' =>
          exact absurd (List.cons_prefix_cons.mp (List.cons_prefix_cons.mp hpre).2).1
            (by simp)
      | true :: true :: v, true :: false :: v' =>
          exact absurd (List.cons_prefix_cons.mp (List.cons_prefix_cons.mp hpre).2).1
            (by simp)
      | true :: true :: v, true :: true :: v' =>
          have hv : v <+: v' := (List.cons_prefix_cons.mp
            (List.cons_prefix_cons.mp hpre).2).2
          obtain ⟨e, w, rfl, ha, -⟩ := h
          obtain ⟨e', w', rfl, ha', -⟩ := h'
          obtain ⟨he, hw⟩ := natCode_append_prefix hv
          subst he
          rw [ha.antichain ha' hw]

/-- The prefix-freeness of `dom U`, in the form the Kraft argument uses. -/
lemma UHalt_prefix_eq {v v' : List Bool} {y y' : ℕ} (h : UHalt v y) (h' : UHalt v' y')
    (hpre : v <+: v') : v = v' :=
  UHalt_prefixFree v.length v v' y y' le_rfl h h' hpre

/-! ## The prefix complexity `κ_U` -/

/-- The set of codeword lengths reaching the value `y`. -/
def uLenSet (y : ℕ) : Set ℕ := {ℓ | ∃ v, UHalt v y ∧ v.length = ℓ}

lemma uLenSet_nonempty (y : ℕ) : (uLenSet y).Nonempty := by
  refine ⟨(false :: natCode y).length, ?_⟩
  exact ⟨false :: natCode y, UHalt_natCode y, rfl⟩

/-- The minimum is attained. -/
lemma uLenSet_sInf_mem (y : ℕ) : ∃ v, UHalt v y ∧ v.length = sInf (uLenSet y) :=
  Nat.sInf_mem (uLenSet_nonempty y)

/-- **Universal prefix complexity**: the least `U`-codeword length reaching `⌜φ⌝`, plus one
slack bit (the length function of "discard one bit, then run `U`").
Paper node: `thm:ob` -/
noncomputable def kappaU (φ : Sentence) : ℕ := sInf (uLenSet (Encodable.encode φ)) + 1

lemma kappaU_le_of_halt {φ : Sentence} {v : List Bool}
    (h : UHalt v (Encodable.encode φ)) : kappaU φ ≤ v.length + 1 := by
  have hmem : v.length ∈ uLenSet (Encodable.encode φ) := ⟨v, h, rfl⟩
  exact Nat.add_le_add_right (Nat.sInf_le hmem) 1

/-- A shortest codeword for `φ`. -/
noncomputable def uWord (φ : Sentence) : List Bool :=
  (uLenSet_sInf_mem (Encodable.encode φ)).choose

lemma uWord_spec (φ : Sentence) :
    UHalt (uWord φ) (Encodable.encode φ) ∧
      (uWord φ).length = sInf (uLenSet (Encodable.encode φ)) :=
  (uLenSet_sInf_mem (Encodable.encode φ)).choose_spec

lemma uWord_halt (φ : Sentence) : UHalt (uWord φ) (Encodable.encode φ) := (uWord_spec φ).1

lemma uWord_length (φ : Sentence) : (uWord φ).length + 1 = kappaU φ := by
  rw [kappaU, (uWord_spec φ).2]

/-- The shortest codewords are prefix-free and separate sentences: exactly the input the
generic Kraft half-budget lemma asks for. -/
lemma uWord_prefix_inj {φ ψ : Sentence} (h : uWord φ <+: uWord ψ) : φ = ψ := by
  have heq : uWord φ = uWord ψ := UHalt_prefix_eq (uWord_halt φ) (uWord_halt ψ) h
  have := UHalt_functional (uWord ψ) _ _ (heq ▸ uWord_halt φ) (uWord_halt ψ)
  exact Encodable.encode_injective this

/-- **The Kraft budget of the universal machine.**
Paper node: `thm:ob` -/
lemma kappaU_kraft (N : ℕ) :
    ∑ i ∈ Finset.range N, prefixWeight kappaU (prefixSentenceEnum i) ≤ 1 :=
  prefixKraft_of_code uWord uWord_length (fun _ _ h => uWord_prefix_inj h) N

/-! ## The hard-wired negation instruction -/

/-- **The negation compiler of the universal machine**, overhead `2`: family 2 of `U` *is*
the negation instruction, so prefixing `1 ∷ 0` to a shortest codeword for `φ` is a codeword
for `∼φ`.
Paper node: `thm:ob` -/
def kappaUNegationCompiler : PrefixNegationCompiler kappaU where
  overhead := 2
  complexity_neg_le := fun φ => by
    have h : UHalt (true :: false :: uWord φ) (Encodable.encode (∼φ)) :=
      ⟨Encodable.encode φ, uWord_halt φ, (negCode_encode φ).symm⟩
    have := kappaU_le_of_halt h
    have hlen : (true :: false :: uWord φ).length = (uWord φ).length + 2 := by simp
    rw [hlen] at this
    rw [← uWord_length φ]
    omega

/-! ## Universality (the invariance theorem)

A *prefix machine* is a code whose halting domain is prefix-free.  For such a machine the
prefix-ification `acc` rejects nothing, so its whole domain reappears inside family 3 and
`κ_U` undercuts its codeword lengths by a constant depending only on the machine. -/

/-- Every halting string of a prefix machine is accepted.  (If the guard blocks the
candidate, the blocking string is comparable with it and also halts, hence *equals* it by
prefix-freeness — so the string was already accepted.) -/
lemma accepted_of_prefixFree {c : Nat.Partrec.Code}
    (hpf : ∀ u v : List Bool, (∃ y, y ∈ c.eval (Encodable.encode u)) →
      (∃ y, y ∈ c.eval (Encodable.encode v)) → u <+: v → u = v)
    {w : List Bool} {y : ℕ} (hy : y ∈ c.eval (Encodable.encode w)) :
    Accepted (Encodable.encode c) w := by
  classical
  obtain ⟨f, hf⟩ := Nat.Partrec.Code.evaln_complete.mp hy
  set e := Encodable.encode c with he
  set t := Nat.pair e (Nat.pair (Encodable.encode w) f) with ht
  have hcode : candCode t = e := by simp [candCode, ht]
  have hword : candWord t = w := by simp [candWord, ht]
  have hfuel : candFuel t = f := by simp [candFuel, ht]
  have hofNat : Denumerable.ofNat Nat.Partrec.Code e = c := by
    rw [he]; exact Denumerable.ofNat_encode c
  have hhit : (candHit t).isSome := by
    rw [candHit, hcode, hfuel, hword, hofNat, hf]
    rfl
  by_contra hcon
  -- the guard must pass: a blocking string halts and is comparable with `w`, hence
  -- *equals* `w` by prefix-freeness, so `w` would already be accepted
  have hok : accOK t (acc t) = true := by
    rw [accOK, Bool.and_eq_true]
    refine ⟨hhit, List.all_eq_true.mpr fun p hp => ?_⟩
    simp only [Bool.not_eq_true', Bool.and_eq_false_iff, Bool.or_eq_false_iff,
      decide_eq_false_iff_not]
    by_cases hpe : p.1 = candCode t
    · refine Or.inr ⟨fun hc => hcon ?_, fun hc => hcon ?_⟩ <;>
        [skip; skip] <;>
      · rw [hcode] at hpe
        have hph : ∃ z, z ∈ c.eval (Encodable.encode p.2) := by
          have := acc_halts t p hp
          rw [hpe, hofNat] at this
          exact this
        have hpw : p.2 = w := by
          rw [hword] at hc
          first
            | exact hpf _ _ hph ⟨y, hy⟩ hc
            | exact (hpf _ _ ⟨y, hy⟩ hph hc).symm
        exact ⟨t, by rw [← hpe, ← hpw]; exact hp⟩
    · exact Or.inl hpe
  exact hcon ⟨t + 1, by
    rw [acc, if_pos hok]
    exact List.mem_cons.mpr (Or.inl (by rw [hcode, hword]))⟩

/-- **Invariance / universality.**  For every prefix machine `M` (a code with prefix-free
halting domain), `κ_U` undercuts `M`'s codeword lengths by an additive constant that
depends only on `M`.  This is the property that makes `κ_U` *universal* prefix complexity
rather than the length function of some particular code.
Paper node: `thm:ob` -/
theorem kappaU_le_of_prefixMachine (c : Nat.Partrec.Code)
    (hpf : ∀ u v : List Bool, (∃ y, y ∈ c.eval (Encodable.encode u)) →
      (∃ y, y ∈ c.eval (Encodable.encode v)) → u <+: v → u = v) :
    ∃ K : ℕ, ∀ (w : List Bool) (φ : Sentence),
      Encodable.encode φ ∈ c.eval (Encodable.encode w) → kappaU φ ≤ w.length + K := by
  refine ⟨(natCode (Encodable.encode c)).length + 3, fun w φ hw => ?_⟩
  have hacc : Accepted (Encodable.encode c) w := accepted_of_prefixFree hpf hw
  have h : UHalt (true :: true :: (natCode (Encodable.encode c) ++ w))
      (Encodable.encode φ) := by
    refine ⟨Encodable.encode c, w, rfl, hacc, ?_⟩
    rwa [Denumerable.ofNat_encode c]
  have := kappaU_le_of_halt h
  simp only [List.length_cons, List.length_append] at this
  omega

/-! ## The from-below stage table

`κ_U` is uncomputable, so the boundary's approximation field carries real content: the
stage table mines only what the dovetail has *discovered* by stage `n` — the strings
accepted in `acc n`, run with fuel `n`.  It is antitone in the stage and, pointwise,
eventually **equal** to `κ_U` (the minimum is attained by a single codeword, and that
codeword shows up at some finite stage), which is exactly lower semicomputability of the
weights `2^{-κ_U}`. -/

/-- The stage-`n` restriction of `U`: only codewords whose universal part is already
accepted, and whose run finishes within fuel `n`. -/
def UHaltBy (n : ℕ) : List Bool → ℕ → Prop
  | [], _ => False
  | false :: u, y => natVal u = some y
  | [true], _ => False
  | true :: false :: v, y => ∃ x, UHaltBy n v x ∧ y = negCode x
  | true :: true :: v, y =>
      ∃ e w, natCode e ++ w = v ∧ (e, w) ∈ acc n ∧
        (Denumerable.ofNat Nat.Partrec.Code e).evaln n (Encodable.encode w) = some y

lemma UHaltBy_mono : ∀ (v : List Bool) (n m y : ℕ), n ≤ m → UHaltBy n v y → UHaltBy m v y
  | [], _, _, _, _, h => absurd h (by simp [UHaltBy])
  | false :: _, _, _, _, _, h => h
  | [true], _, _, _, _, h => absurd h (by simp [UHaltBy])
  | true :: false :: v, n, m, _, hnm, ⟨x, hx, hy⟩ =>
      ⟨x, UHaltBy_mono v n m x hnm hx, hy⟩
  | true :: true :: _, _, _, _, hnm, ⟨e, w, hv, ha, hy⟩ =>
      ⟨e, w, hv, acc_mono hnm ha, Nat.Partrec.Code.evaln_mono hnm hy⟩

lemma UHalt_of_UHaltBy : ∀ (v : List Bool) (n y : ℕ), UHaltBy n v y → UHalt v y
  | [], _, _, h => absurd h (by simp [UHaltBy])
  | false :: _, _, _, h => h
  | [true], _, _, h => absurd h (by simp [UHaltBy])
  | true :: false :: v, n, _, ⟨x, hx, hy⟩ => ⟨x, UHalt_of_UHaltBy v n x hx, hy⟩
  | true :: true :: _, n, _, ⟨e, w, hv, ha, hy⟩ =>
      ⟨e, w, hv, ⟨n, ha⟩, Nat.Partrec.Code.evaln_sound hy⟩

lemma UHaltBy_of_UHalt : ∀ (v : List Bool) (y : ℕ), UHalt v y → ∃ n, UHaltBy n v y
  | [], _, h => absurd h (by simp [UHalt])
  | false :: _, _, h => ⟨0, h⟩
  | [true], _, h => absurd h (by simp [UHalt])
  | true :: false :: v, _, ⟨x, hx, hy⟩ => by
      obtain ⟨n, hn⟩ := UHaltBy_of_UHalt v x hx
      exact ⟨n, x, hn, hy⟩
  | true :: true :: _, _, ⟨e, w, hv, ⟨t, ht⟩, hy⟩ => by
      obtain ⟨f, hf⟩ := Nat.Partrec.Code.evaln_complete.mp hy
      refine ⟨max t f, e, w, hv, acc_mono (le_max_left t f) ht, ?_⟩
      exact Nat.Partrec.Code.evaln_mono (le_max_right t f) hf

/-- Codeword lengths discovered by stage `n`. -/
def uLenSetBy (n y : ℕ) : Set ℕ := {ℓ | ∃ v, UHaltBy n v y ∧ v.length = ℓ}

lemma uLenSetBy_nonempty (n y : ℕ) : (uLenSetBy n y).Nonempty := by
  refine ⟨(false :: natCode y).length, ?_⟩
  exact ⟨false :: natCode y, by simp [UHaltBy, natVal_natCode], rfl⟩

lemma uLenSetBy_subset (n y : ℕ) : uLenSetBy n y ⊆ uLenSet y := by
  rintro ℓ ⟨v, hv, rfl⟩
  exact ⟨v, UHalt_of_UHaltBy v n _ hv, rfl⟩

/-- **The from-below stage table.**
Paper node: `thm:ob` -/
noncomputable def kappaStage (n y : ℕ) : ℕ := sInf (uLenSetBy n y) + 1

lemma kappaU_le_kappaStage (n : ℕ) (φ : Sentence) :
    kappaU φ ≤ kappaStage n (Encodable.encode φ) := by
  have hmem := Nat.sInf_mem (uLenSetBy_nonempty n (Encodable.encode φ))
  exact Nat.add_le_add_right
    (Nat.sInf_le (uLenSetBy_subset n (Encodable.encode φ) hmem)) 1

lemma kappaStage_antitone {n m y : ℕ} (h : n ≤ m) : kappaStage m y ≤ kappaStage n y := by
  obtain ⟨v, hv, hlen⟩ := Nat.sInf_mem (uLenSetBy_nonempty n y)
  exact Nat.add_le_add_right (hlen ▸ Nat.sInf_le ⟨v, UHaltBy_mono v n m _ h hv, rfl⟩) 1

/-- The stage table is *eventually exact*: the shortest codeword is discovered at some
finite stage, and from then on the table reports the true complexity. -/
lemma kappaStage_eventually_eq (φ : Sentence) :
    ∀ᶠ n in atTop, kappaStage n (Encodable.encode φ) = kappaU φ := by
  obtain ⟨n₀, hn₀⟩ := UHaltBy_of_UHalt (uWord φ) _ (uWord_halt φ)
  refine Filter.eventually_atTop.2 ⟨n₀, fun n hn => ?_⟩
  refine le_antisymm ?_ (kappaU_le_kappaStage n φ)
  have hmem : (uWord φ).length ∈ uLenSetBy n (Encodable.encode φ) :=
    ⟨uWord φ, UHaltBy_mono _ n₀ n _ hn hn₀, rfl⟩
  calc kappaStage n (Encodable.encode φ) ≤ (uWord φ).length + 1 :=
        Nat.add_le_add_right (Nat.sInf_le hmem) 1
    _ = kappaU φ := uWord_length φ

/-! ## The approximation and the assembled boundary -/

/-- The stage-`n` weight of the `i`-th enumerated sentence. -/
noncomputable def uApprox (n i : ℕ) : ℚ :=
  1 / 2 ^ kappaStage n (Encodable.encode (prefixSentenceEnum i))

lemma uApprox_nonneg (n i : ℕ) : 0 ≤ uApprox n i := by
  rw [uApprox]; positivity

lemma uApprox_le (n i : ℕ) :
    ((uApprox n i : ℚ) : ℝ) ≤ prefixWeight kappaU (prefixSentenceEnum i) := by
  rw [uApprox, prefixWeight]
  push_cast
  exact one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_right₀ (by norm_num) (kappaU_le_kappaStage n _))

lemma uApprox_tendsto (i : ℕ) :
    Tendsto (fun n => ((uApprox n i : ℚ) : ℝ)) atTop
      (𝓝 (prefixWeight kappaU (prefixSentenceEnum i))) := by
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [kappaStage_eventually_eq (prefixSentenceEnum i)] with n hn
  rw [prefixWeight, uApprox, hn]
  push_cast
  norm_num

lemma uApprox_mono {n m : ℕ} (h : n ≤ m) (i : ℕ) : uApprox n i ≤ uApprox m i := by
  rw [uApprox, uApprox]
  have := kappaStage_antitone (y := Encodable.encode (prefixSentenceEnum i)) h
  apply one_div_le_one_div_of_le (by positivity)
  exact pow_le_pow_right₀ (by norm_num) this

/-! ## The polynomial clock: the self-clamped stage table

The exact stage table is *not* poly-fueled — reading stage `n` means running the dovetail
for `n` stages — so, exactly as for the universal dovetailer (`Dovetail.dusApprox`,
`M7-DUS-APPROX`), the emitted table does not approximate the exact one but **selects**
from it.  `Code.evaln` is self-clamping, so running the exact emitter under the polynomial
clock `⟪z,z⟫` and keeping the last stage that finished yields an *exact* stage value, at a
stage that grows without bound.  `nonneg` and `le` are then inherited verbatim and
`tendsto` is a two-sided squeeze.

All this needs of the exact table is that it has a **code** at all, which is `uCode`
above — a computability fact about a bounded search, carrying no complexity claim, no
market prices and no Occam conclusion.  `uTab` shifts the stage index
by one so that the scan's initial state is a *constant* (the rational `0`), which is what
`PolyFueled.prec` needs of a base case. -/

/-- The exact stage table, shifted so that stage `0` reads `0`. -/
noncomputable def uTab (j i : ℕ) : ℚ := if j = 0 then 0 else uApprox (j - 1) i

@[simp] lemma uTab_zero (i : ℕ) : uTab 0 i = 0 := rfl

lemma uTab_succ (j i : ℕ) : uTab (j + 1) i = uApprox j i := by simp [uTab]

lemma uTab_nonneg (j i : ℕ) : 0 ≤ uTab j i := by
  rcases j with _ | j
  · simp
  · rw [uTab_succ]; exact uApprox_nonneg _ _

lemma uTab_mono {j j' : ℕ} (h : j ≤ j') (i : ℕ) : uTab j i ≤ uTab j' i := by
  rcases j with _ | j
  · simpa using uTab_nonneg j' i
  · rcases j' with _ | j'
    · omega
    · rw [uTab_succ, uTab_succ]
      exact uApprox_mono (by omega) i

lemma uTab_le (j i : ℕ) :
    ((uTab j i : ℚ) : ℝ) ≤ prefixWeight kappaU (prefixSentenceEnum i) := by
  rcases j with _ | j
  · simpa using (prefixWeight_pos kappaU (prefixSentenceEnum i)).le
  · rw [uTab_succ]; exact uApprox_le _ _

lemma uTab_tendsto (i : ℕ) :
    Tendsto (fun j => ((uTab j i : ℚ) : ℝ)) atTop
      (𝓝 (prefixWeight kappaU (prefixSentenceEnum i))) := by
  have h1 : Tendsto (fun j : ℕ => ((uApprox (j - 1) i : ℚ) : ℝ)) atTop
      (𝓝 (prefixWeight kappaU (prefixSentenceEnum i))) :=
    (uApprox_tendsto i).comp (Filter.tendsto_sub_atTop_nat 1)
  refine Filter.Tendsto.congr' ?_ h1
  filter_upwards [Filter.eventually_gt_atTop 0] with j hj
  rw [uTab, if_neg (by omega)]

/-- The exact stage table, as a natural-number stream. -/
noncomputable def uEmit (z : ℕ) : ℕ := Encodable.encode (uTab z.unpair.1 z.unpair.2)


/-! ## The exact stage table is computable

`kappaStage` is a *bounded* search: a codeword reaching `y` at stage `n` can be assumed no
longer than `|natCode y| + 1`, since `0 ∷ natCode y` always reaches `y`.  So the exact
table is decided by enumerating the finitely many bit strings of length `≤ |natCode y| + 1`
and running the stage-`n` decision procedure `uVal` on each.  Everything here is plain
primitive recursion — **no complexity claim is made or needed**: the polynomial clock of
the next section is constructed on top of the code produced here. -/

lemma size_prim : Primrec Nat.size := sizec_polyFueled.choose_spec.primrec

lemma pow2_prim : Primrec (fun k : ℕ => 2 ^ k) :=
  (Primrec₂.unpaired'.mp Nat.Primrec.pow).comp (Primrec.const 2) Primrec.id

lemma testBit_prim : Primrec₂ (fun n i : ℕ => n.testBit i) := by
  have : Primrec₂ (fun n i : ℕ => decide (n / 2 ^ i % 2 = 1)) :=
    Primrec₂.mk (primrecPred_iff_primrec_decide.mp (Primrec.eq.comp
      (Primrec.nat_mod.comp
        (Primrec.nat_div.comp Primrec.fst (pow2_prim.comp Primrec.snd)) (Primrec.const 2))
      (Primrec.const 1)))
  exact this.of_eq (fun n i => Nat.testBit_eq_decide_div_mod_eq.symm)

lemma natCode_prim : Primrec natCode := by
  have hs : Primrec (fun n : ℕ => (n + 1).size) := size_prim.comp Primrec.succ
  have hrep : Primrec (fun n : ℕ => List.replicate ((n + 1).size - 1) true) := by
    have := Primrec.list_map (Primrec.list_range.comp
      (Primrec.nat_sub.comp hs (Primrec.const 1)))
      (Primrec.const true : Primrec (fun _ : ℕ × ℕ => true)).to₂
    exact this.of_eq (fun n => by simp)
  have hbits : Primrec (fun n : ℕ => (List.range (n + 1).size).map (n + 1).testBit) :=
    Primrec.list_map (Primrec.list_range.comp hs)
      (testBit_prim.comp (Primrec.succ.comp Primrec.fst) Primrec.snd).to₂
  exact (Primrec.list_append.comp hrep
    (Primrec.list_cons.comp (Primrec.const false) hbits)).of_eq (fun n => rfl)

lemma natVal_prim : Primrec natVal := by
  have hf : Primrec (fun u : List Bool => List.range (2 ^ u.length)) :=
    Primrec.list_range.comp (pow2_prim.comp Primrec.list_length)
  have hg : Primrec₂ (fun (u : List Bool) (n : ℕ) => if natCode n = u then some n else none) :=
    Primrec.ite (Primrec.eq.comp (natCode_prim.comp Primrec.snd) Primrec.fst)
      (Primrec.option_some.comp Primrec.snd) (Primrec.const none)
  refine ((Primrec.list_head?.comp (Primrec.listFilterMap hf hg)).of_eq (fun u => ?_))
  rw [natVal]
  congr 1
  induction (List.range (2 ^ u.length)) with
  | nil => rfl
  | cons a l ih =>
      by_cases h : natCode a = u <;> simp [h, ih]

/-- All bit strings of a given length. -/
def wordsLen : ℕ → List (List Bool)
  | 0 => [[]]
  | k + 1 => (wordsLen k).flatMap (fun w => [false :: w, true :: w])

lemma mem_wordsLen : ∀ (k : ℕ) (v : List Bool), v ∈ wordsLen k ↔ v.length = k
  | 0, v => by cases v <;> simp [wordsLen]
  | k + 1, v => by
      rw [wordsLen]
      constructor
      · intro h
        simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at h
        obtain ⟨w, hw, hv⟩ := h
        have := (mem_wordsLen k w).mp hw
        rcases hv with rfl | rfl <;> simp [this]
      · intro h
        match v with
        | [] => simp at h
        | b :: w =>
            have hw : w ∈ wordsLen k := (mem_wordsLen k w).mpr (by simpa using h)
            refine List.mem_flatMap.mpr ⟨w, hw, ?_⟩
            cases b <;> simp

lemma wordsLen_prim : Primrec wordsLen := by
  have hcons : Primrec₂ (fun (_ : ℕ × List (List Bool)) (w : List Bool) =>
      [false :: w, true :: w]) :=
    Primrec₂.mk (Primrec.list_cons.comp (Primrec.list_cons.comp (Primrec.const false) Primrec.snd)
      (Primrec.list_cons.comp (Primrec.list_cons.comp (Primrec.const true) Primrec.snd)
        (Primrec.const ([] : List (List Bool)))))
  have hstep : Primrec₂ (fun (_ : ℕ) (l : List (List Bool)) =>
      l.flatMap (fun w => [false :: w, true :: w])) :=
    Primrec₂.mk (Primrec.list_flatMap Primrec.snd hcons)
  refine (Primrec.nat_rec₁ ([[]] : List (List Bool)) hstep).of_eq (fun k => ?_)
  induction k with
  | zero => rfl
  | succ k ih => rw [wordsLen, ← ih]

lemma prefix_iff_mem_wordsLen (u v : List Bool) :
    u <+: v ↔ ∃ w ∈ wordsLen (v.length - u.length), u ++ w = v := by
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w, (mem_wordsLen _ w).mpr (by simp), rfl⟩
  · rintro ⟨w, -, rfl⟩
    exact List.prefix_append _ _

lemma isPrefix_prim : PrimrecRel (fun u v : List Bool => u <+: v) := by
  have hR : PrimrecRel (fun (w : List Bool) (p : List Bool × List Bool) => p.1 ++ w = p.2) :=
    Primrec.eq.comp (Primrec.list_append.comp (Primrec.fst.comp Primrec.snd) Primrec.fst)
      (Primrec.snd.comp Primrec.snd)
  have hL : Primrec (fun p : List Bool × List Bool =>
      wordsLen (p.2.length - p.1.length)) :=
    wordsLen_prim.comp (Primrec.nat_sub.comp (Primrec.list_length.comp Primrec.snd)
      (Primrec.list_length.comp Primrec.fst))
  have h := (PrimrecRel.exists_mem_list hR).comp₂
    (Primrec₂.mk (f := fun u v : List Bool => wordsLen (v.length - u.length)) hL)
    (Primrec₂.mk (f := fun u v : List Bool => (u, v)) (Primrec.fst.pair Primrec.snd))
  exact h.of_eq (fun u v => (prefix_iff_mem_wordsLen u v).symm)

lemma candCode_prim : Primrec candCode := Primrec.fst.comp Primrec.unpair

lemma candFuel_prim : Primrec candFuel :=
  Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))

lemma candWord_prim : Primrec candWord :=
  Primrec.option_getD.comp
    ((Primrec.decode (α := List Bool)).comp
      (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))
    (Primrec.const [])

lemma candHit_prim : Primrec candHit :=
  Nat.Partrec.Code.primrec_evaln.comp
    ((candFuel_prim.pair ((Primrec.ofNat Nat.Partrec.Code).comp candCode_prim)).pair
      (Primrec.encode.comp candWord_prim))

lemma accOK_iff (t : ℕ) (L : List (ℕ × List Bool)) :
    accOK t L = true ↔ (candHit t).isSome = true ∧
      ∀ p ∈ L, ¬ (p.1 = candCode t ∧ (p.2 <+: candWord t ∨ candWord t <+: p.2)) := by
  rw [accOK, Bool.and_eq_true, List.all_eq_true]
  refine and_congr Iff.rfl (forall_congr' fun p => forall_congr' fun _ => ?_)
  simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
    Bool.or_eq_false_iff, not_and, not_or]
  tauto

lemma accOK_prim : Primrec₂ accOK := by
  have hR : PrimrecRel (fun (p : ℕ × List Bool) (t : ℕ) =>
      ¬ (p.1 = candCode t ∧ (p.2 <+: candWord t ∨ candWord t <+: p.2))) := by
    have h1 : PrimrecRel (fun (p : ℕ × List Bool) (t : ℕ) => p.1 = candCode t) :=
      Primrec.eq.comp (Primrec.fst.comp Primrec.fst) (candCode_prim.comp Primrec.snd)
    have h2 : PrimrecRel (fun (p : ℕ × List Bool) (t : ℕ) => p.2 <+: candWord t) :=
      isPrefix_prim.comp (Primrec.snd.comp Primrec.fst) (candWord_prim.comp Primrec.snd)
    have h3 : PrimrecRel (fun (p : ℕ × List Bool) (t : ℕ) => candWord t <+: p.2) :=
      isPrefix_prim.comp (candWord_prim.comp Primrec.snd) (Primrec.snd.comp Primrec.fst)
    exact (h1.and (h2.or h3)).not
  have hall := PrimrecRel.forall_mem_list hR
  have hswap : PrimrecRel (fun (t : ℕ) (L : List (ℕ × List Bool)) =>
      ∀ p ∈ L, ¬ (p.1 = candCode t ∧ (p.2 <+: candWord t ∨ candWord t <+: p.2))) :=
    hall.comp₂ (Primrec₂.mk (f := fun (_ : ℕ) (L : List (ℕ × List Bool)) => L) Primrec.snd)
      (Primrec₂.mk (f := fun (t : ℕ) (_ : List (ℕ × List Bool)) => t) Primrec.fst)
  have hsome : PrimrecPred (fun t : ℕ => (candHit t).isSome = true) :=
    Primrec.eq.comp (Primrec.option_isSome.comp candHit_prim) (Primrec.const true)
  have : PrimrecRel (fun (t : ℕ) (L : List (ℕ × List Bool)) =>
      (candHit t).isSome = true ∧
      ∀ p ∈ L, ¬ (p.1 = candCode t ∧ (p.2 <+: candWord t ∨ candWord t <+: p.2))) :=
    (hsome.comp Primrec.fst).and hswap
  refine Primrec₂.mk (Primrec.of_eq (primrecPred_iff_primrec_decide.mp this) (fun p => ?_))
  have h := accOK_iff p.1 p.2
  by_cases hb : accOK p.1 p.2 = true
  · rw [hb]; exact decide_eq_true (h.mp hb)
  · rw [Bool.not_eq_true] at hb
    rw [hb]
    exact decide_eq_false (fun hc => by rw [h.mpr hc] at hb; exact absurd hb (by simp))

lemma acc_prim : Primrec acc := by
  have hstep : Primrec₂ (fun (t : ℕ) (l : List (ℕ × List Bool)) =>
      if accOK t l then (candCode t, candWord t) :: l else l) := by
    refine Primrec₂.mk (Primrec.of_eq
      (Primrec.cond (accOK_prim.comp Primrec.fst Primrec.snd)
        (Primrec.list_cons.comp
          ((candCode_prim.comp Primrec.fst).pair (candWord_prim.comp Primrec.fst))
          Primrec.snd)
        Primrec.snd) (fun p => ?_))
    cases h : accOK p.1 p.2 <;> simp
  refine (Primrec.nat_rec₁ ([] : List (ℕ × List Bool)) hstep).of_eq (fun t => ?_)
  induction t with
  | zero => rfl
  | succ t ih => rw [acc, ← ih]

/-! ### The stage-`n` decision procedure -/

/-- The value of a stage-`n` family-3 codeword, by a search through the finite accepted
list `acc n`: at most one accepted pair splits `v` as `natCode e ++ w`. -/
def uUniv (n : ℕ) (v : List Bool) : Option ℕ :=
  (((acc n).filterMap (fun p => if natCode p.1 ++ p.2 = v then some p else none)).head?).bind
    (fun p => (Denumerable.ofNat Nat.Partrec.Code p.1).evaln n (Encodable.encode p.2))

lemma uUniv_spec (n : ℕ) (v : List Bool) (y : ℕ) :
    uUniv n v = some y ↔ ∃ e w, natCode e ++ w = v ∧ (e, w) ∈ acc n ∧
      (Denumerable.ofNat Nat.Partrec.Code e).evaln n (Encodable.encode w) = some y := by
  set L := (acc n).filterMap
    (fun p => if natCode p.1 ++ p.2 = v then some p else none) with hL
  have hmem : ∀ p : ℕ × List Bool, p ∈ L ↔ p ∈ acc n ∧ natCode p.1 ++ p.2 = v := by
    intro p
    rw [hL, List.mem_filterMap]
    constructor
    · rintro ⟨q, hq, hq2⟩
      by_cases h : natCode q.1 ++ q.2 = v
      · rw [if_pos h] at hq2
        obtain rfl : q = p := by simpa using hq2
        exact ⟨hq, h⟩
      · rw [if_neg h] at hq2; simp at hq2
    · rintro ⟨hp, hv⟩
      exact ⟨p, hp, by rw [if_pos hv]⟩
  have huniq : ∀ p q : ℕ × List Bool, p ∈ L → q ∈ L → p = q := by
    rintro ⟨p1, p2⟩ ⟨q1, q2⟩ hp hq
    have h1 := (hmem (p1, p2)).mp hp
    have h2 := (hmem (q1, q2)).mp hq
    have hsame : natCode p1 ++ p2 = natCode q1 ++ q2 := by
      simp only at h1 h2; rw [h1.2, h2.2]
    have hpre : natCode p1 ++ p2 <+: natCode q1 ++ q2 := by rw [hsame]
    obtain ⟨he, -⟩ := natCode_append_prefix hpre
    subst he
    rw [List.append_cancel_left hsame]
  rw [uUniv, ← hL]
  constructor
  · intro h
    obtain ⟨p, hp, hev⟩ := Option.bind_eq_some_iff.mp h
    have := (hmem p).mp (List.mem_of_mem_head? hp)
    exact ⟨p.1, p.2, this.2, this.1, hev⟩
  · rintro ⟨e, w, hv, ha, hev⟩
    have hmemL : (e, w) ∈ L := (hmem (e, w)).mpr ⟨ha, hv⟩
    cases hh : L.head? with
    | none => rw [List.head?_eq_none_iff] at hh; rw [hh] at hmemL; simp at hmemL
    | some p =>
        have hpL : p ∈ L := List.mem_of_mem_head? hh
        obtain rfl : p = (e, w) := huniq p (e, w) hpL hmemL
        simpa using hev

/-- The stage-`n` value of a codeword: the decision procedure behind `UHaltBy`. -/
def uVal (n : ℕ) : List Bool → Option ℕ
  | [] => none
  | false :: u => natVal u
  | [true] => none
  | true :: false :: v => (uVal n v).map negCode
  | true :: true :: v => uUniv n v

lemma uVal_spec (n : ℕ) : ∀ (v : List Bool) (y : ℕ), uVal n v = some y ↔ UHaltBy n v y
  | [], y => by simp [uVal, UHaltBy]
  | false :: u, y => by simp [uVal, UHaltBy]
  | [true], y => by simp [uVal, UHaltBy]
  | true :: false :: v, y => by
      rw [uVal, UHaltBy, Option.map_eq_some_iff]
      constructor
      · rintro ⟨x, hx, rfl⟩; exact ⟨x, (uVal_spec n v x).mp hx, rfl⟩
      · rintro ⟨x, hx, rfl⟩; exact ⟨x, (uVal_spec n v x).mpr hx, rfl⟩
  | true :: true :: v, y => by rw [uVal, UHaltBy]; exact uUniv_spec n v y

lemma uUniv_prim : Primrec₂ uUniv := by
  have hlist : Primrec (fun x : ℕ × List Bool =>
      (acc x.1).filterMap (fun p => if natCode p.1 ++ p.2 = x.2 then some p else none)) := by
    refine Primrec.listFilterMap (acc_prim.comp Primrec.fst) ?_
    refine Primrec₂.mk (Primrec.ite ?_ (Primrec.option_some.comp Primrec.snd)
      (Primrec.const none))
    exact Primrec.eq.comp
      (Primrec.list_append.comp (natCode_prim.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp Primrec.fst)
  have hbind : Primrec₂ (fun (x : ℕ × List Bool) (p : ℕ × List Bool) =>
      (Denumerable.ofNat Nat.Partrec.Code p.1).evaln x.1 (Encodable.encode p.2)) :=
    Primrec₂.mk (Nat.Partrec.Code.primrec_evaln.comp
      (((Primrec.fst.comp Primrec.fst).pair
        ((Primrec.ofNat Nat.Partrec.Code).comp (Primrec.fst.comp Primrec.snd))).pair
        (Primrec.encode.comp (Primrec.snd.comp Primrec.snd))))
  exact Primrec₂.mk (Primrec.option_bind (Primrec.list_head?.comp hlist) hbind)

/-- One step of the codeword scan, in the shape `Primrec.list_rec` consumes. -/
noncomputable def uValStep (n : ℕ) (b : Bool) (r : List Bool) (pt : Option ℕ) : Option ℕ :=
  bif b then (r.head?.bind (fun c => bif c then uUniv n r.tail else pt.map negCode))
  else natVal r

/-- The scan state: the value of the codeword and of its tail. -/
noncomputable def uValP (n : ℕ) : List Bool → Option ℕ × Option ℕ
  | [] => (none, none)
  | b :: r => (uValStep n b r (uValP n r).2, (uValP n r).1)

lemma uValP_eq (n : ℕ) : ∀ l : List Bool, uValP n l = (uVal n l, uVal n l.tail)
  | [] => rfl
  | b :: r => by
      rw [uValP, uValP_eq n r]
      simp only [List.tail_cons]
      refine Prod.ext ?_ rfl
      simp only
      cases b
      · rw [uValStep, uVal]; rfl
      · match r with
        | [] => rw [uValStep, uVal]; rfl
        | false :: v => rw [uValStep, uVal]; rfl
        | true :: v => rw [uValStep, uVal]; rfl

lemma negCode_prim : Primrec negCode :=
  Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 2)
    (Primrec₂.natPair.comp Primrec.id (Primrec.const 1)))

lemma uValP_prim : Primrec (fun x : ℕ × List Bool => uValP x.1 x.2) := by
  set A := ℕ × List Bool with hA
  set S := Option ℕ × Option ℕ with hS
  have hstep : Primrec₂ (fun (x : A) (w : Bool × List Bool × S) =>
      ((uValStep x.1 w.1 w.2.1 w.2.2.2, w.2.2.1) : S)) := by
    have hn : Primrec (fun y : A × (Bool × List Bool × S) => y.1.1) :=
      Primrec.fst.comp Primrec.fst
    have hb : Primrec (fun y : A × (Bool × List Bool × S) => y.2.1) :=
      Primrec.fst.comp Primrec.snd
    have hr : Primrec (fun y : A × (Bool × List Bool × S) => y.2.2.1) :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
    have e1 : Primrec (fun y : A × (Bool × List Bool × S) => y.2) := Primrec.snd
    have e2 : Primrec (fun y : A × (Bool × List Bool × S) => y.2.2) :=
      Primrec.snd.comp e1
    have e3 : Primrec (fun y : A × (Bool × List Bool × S) => y.2.2.2) :=
      Primrec.snd.comp e2
    have hpt : Primrec (fun y : A × (Bool × List Bool × S) => y.2.2.2.2) :=
      Primrec.snd.comp e3
    have hinner : Primrec₂ (fun (y : A × (Bool × List Bool × S)) (c : Bool) =>
        bif c then uUniv y.1.1 y.2.2.1.tail else y.2.2.2.2.map negCode) :=
      Primrec₂.mk (Primrec.cond Primrec.snd
        (uUniv_prim.comp (hn.comp Primrec.fst)
          (Primrec.list_tail.comp (hr.comp Primrec.fst)))
        (Primrec.option_map (hpt.comp Primrec.fst)
          (negCode_prim.comp Primrec.snd).to₂))
    have hval : Primrec (fun y : A × (Bool × List Bool × S) =>
        uValStep y.1.1 y.2.1 y.2.2.1 y.2.2.2.2) :=
      (Primrec.cond hb
        (Primrec.option_bind (Primrec.list_head?.comp hr) hinner)
        (natVal_prim.comp hr))
    have hih1 : Primrec (fun y : A × (Bool × List Bool × S) => y.2.2.2.1) :=
      Primrec.fst.comp e3
    exact Primrec₂.mk (hval.pair hih1)
  refine (Primrec.list_rec Primrec.snd (Primrec.const ((none, none) : S)) hstep).of_eq
    (fun x => ?_)
  obtain ⟨n, l⟩ := x
  induction l with
  | nil => rfl
  | cons b r ih => rw [uValP, ← ih]

lemma uVal_prim : Primrec₂ uVal :=
  Primrec₂.mk ((Primrec.fst.comp uValP_prim).of_eq (fun x => by rw [uValP_eq]))

/-! ### The bounded search -/

/-- All bit strings of length at most `L`. -/
def wordsUpto (L : ℕ) : List (List Bool) := (List.range (L + 1)).flatMap wordsLen

lemma mem_wordsUpto (L : ℕ) (v : List Bool) : v ∈ wordsUpto L ↔ v.length ≤ L := by
  rw [wordsUpto, List.mem_flatMap]
  constructor
  · rintro ⟨k, hk, hv⟩
    rw [mem_wordsLen] at hv
    rw [hv]
    simpa using Nat.lt_succ_iff.mp (List.mem_range.mp hk)
  · intro h
    exact ⟨v.length, List.mem_range.mpr (by omega), (mem_wordsLen _ _).mpr rfl⟩

lemma wordsUpto_prim : Primrec wordsUpto :=
  Primrec.list_flatten.comp
    (Primrec.list_map (Primrec.list_range.comp Primrec.succ) (wordsLen_prim.comp Primrec.snd).to₂)

/-- The stage-`n` codeword lengths for `y` discovered by the bounded search. -/
def uLenList (n y : ℕ) : List ℕ :=
  (wordsUpto ((natCode y).length + 1)).filterMap
    (fun v => if uVal n v = some y then some v.length else none)

/-- The exact from-below stage value, as a bounded search. -/
def uMinLen (n y : ℕ) : ℕ := (uLenList n y).foldr min ((natCode y).length + 1)

lemma foldr_min_le : ∀ (l : List ℕ) (d a : ℕ), a ∈ l → l.foldr min d ≤ a
  | [], _, _, h => absurd h (by simp)
  | b :: l, d, a, h => by
      rcases List.mem_cons.mp h with rfl | h'
      · exact Nat.min_le_left _ _
      · exact le_trans (Nat.min_le_right _ _) (foldr_min_le l d a h')

lemma foldr_min_mem : ∀ (l : List ℕ) (d : ℕ), l.foldr min d ∈ l ∨ l.foldr min d = d
  | [], _ => Or.inr rfl
  | b :: l, d => by
      rcases Nat.le_total b (l.foldr min d) with h | h
      · exact Or.inl (by rw [List.foldr_cons, Nat.min_eq_left h]; simp)
      · rw [List.foldr_cons, Nat.min_eq_right h]
        rcases foldr_min_mem l d with h' | h'
        · exact Or.inl (List.mem_cons_of_mem _ h')
        · exact Or.inr h'

lemma mem_uLenList {n y m : ℕ} (h : m ∈ uLenList n y) :
    ∃ v : List Bool, UHaltBy n v y ∧ v.length = m := by
  rw [uLenList, List.mem_filterMap] at h
  obtain ⟨v, -, hv⟩ := h
  by_cases hc : uVal n v = some y
  · rw [if_pos hc] at hv
    exact ⟨v, (uVal_spec n v y).mp hc, by simpa using hv⟩
  · rw [if_neg hc] at hv; simp at hv

lemma uMinLen_eq (n y : ℕ) : uMinLen n y = sInf (uLenSetBy n y) := by
  have hdefault : ((natCode y).length + 1) ∈ uLenSetBy n y :=
    ⟨false :: natCode y, by simp [UHaltBy, natVal_natCode], by simp⟩
  have hmem : uMinLen n y ∈ uLenSetBy n y := by
    rcases foldr_min_mem (uLenList n y) ((natCode y).length + 1) with h | h
    · obtain ⟨v, hv, hlen⟩ := mem_uLenList h
      exact ⟨v, hv, hlen⟩
    · rw [uMinLen, h]; exact hdefault
  refine le_antisymm ?_ (Nat.sInf_le hmem)
  obtain ⟨v, hv, hlen⟩ := Nat.sInf_mem (uLenSetBy_nonempty n y)
  have hle : sInf (uLenSetBy n y) ≤ (natCode y).length + 1 := Nat.sInf_le hdefault
  have hvm : v ∈ wordsUpto ((natCode y).length + 1) :=
    (mem_wordsUpto _ v).mpr (by omega)
  have : sInf (uLenSetBy n y) ∈ uLenList n y := by
    rw [uLenList, List.mem_filterMap]
    exact ⟨v, hvm, by rw [if_pos ((uVal_spec n v y).mpr hv), hlen]⟩
  exact foldr_min_le _ _ _ this

lemma kappaStage_eq (n y : ℕ) : kappaStage n y = uMinLen n y + 1 := by
  rw [kappaStage, uMinLen_eq]

lemma uMinLen_prim : Primrec₂ uMinLen := by
  have hL : Primrec (fun x : ℕ × ℕ => (natCode x.2).length + 1) :=
    Primrec.succ.comp (Primrec.list_length.comp (natCode_prim.comp Primrec.snd))
  have hlist : Primrec (fun x : ℕ × ℕ => uLenList x.1 x.2) := by
    refine Primrec.listFilterMap (wordsUpto_prim.comp hL) ?_
    refine Primrec₂.mk (Primrec.ite ?_
      (Primrec.option_some.comp (Primrec.list_length.comp Primrec.snd)) (Primrec.const none))
    exact Primrec.eq.comp (uVal_prim.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
      (Primrec.option_some.comp (Primrec.snd.comp Primrec.fst))
  have hmin : Primrec₂ (fun (_ : ℕ × ℕ) (w : ℕ × ℕ) => min w.1 w.2) :=
    Primrec₂.mk (Primrec.nat_min.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd))
  exact Primrec₂.mk ((Primrec.list_foldr hlist hL hmin).of_eq (fun p => rfl))

/-! ### The emission program -/

lemma encodeEnum_prim : Primrec (fun i => Encodable.encode (prefixSentenceEnum i)) := by
  have hinv : Primrec invalidBit := invalidBit_polyFueled.choose_spec.primrec
  have hpred : PrimrecPred (fun i : ℕ => invalidBit i = 0) :=
    Primrec.eq.comp hinv (Primrec.const 0)
  refine (Primrec.ite hpred Primrec.id
    (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 1) Primrec.id))).of_eq
    (fun i => ?_)
  rw [encode_prefixSentenceEnum]
  by_cases hv : validCode i
  · rw [if_pos hv, if_pos (by simp [invalidBit, hv])]; rfl
  · rw [if_neg hv, if_neg (by simp [invalidBit, hv])]; rfl

lemma uApprox_eq_halfPow (n i : ℕ) :
    uApprox n i = Dovetail.halfPow (uMinLen n (Encodable.encode (prefixSentenceEnum i))) := by
  rw [uApprox, Dovetail.halfPow_eq, kappaStage_eq]
  rw [div_pow]
  norm_num

lemma uEmit_prim : Primrec uEmit := by
  have hj : Primrec (fun z : ℕ => z.unpair.1) := Primrec.fst.comp Primrec.unpair
  have hi : Primrec (fun z : ℕ => z.unpair.2) := Primrec.snd.comp Primrec.unpair
  have hy : Primrec (fun z : ℕ => Encodable.encode (prefixSentenceEnum z.unpair.2)) :=
    encodeEnum_prim.comp hi
  have hm : Primrec (fun z : ℕ =>
      Dovetail.halfPow (uMinLen (z.unpair.1 - 1) (Encodable.encode
        (prefixSentenceEnum z.unpair.2)))) :=
    Dovetail.halfPow_prim.comp
      (uMinLen_prim.comp (Primrec.nat_sub.comp hj (Primrec.const 1)) hy)
  refine (Primrec.encode.comp
    (Primrec.ite (Primrec.eq.comp hj (Primrec.const 0)) (Primrec.const (0 : ℚ)) hm)).of_eq
    (fun z => ?_)
  rw [uEmit, uTab]
  by_cases h : z.unpair.1 = 0
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, uApprox_eq_halfPow]

theorem exists_uCode : ∃ c : Nat.Partrec.Code, ∀ z, c.eval z = Part.some (uEmit z) := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp
    (Nat.Partrec.of_primrec (Primrec.nat_iff.mp uEmit_prim))
  exact ⟨c, fun z => by rw [hc]; rfl⟩

/-- **The exact stage table has a program.**  Discharged, not assumed: the table is the
bounded search `uMinLen`, primitive recursive by the section above.  Note that this carries
*no* complexity claim — the polynomial clock below is constructed on top of this code.
Paper node: `thm:ob` -/
noncomputable def uCode : Nat.Partrec.Code := exists_uCode.choose

lemma uCode_eval (z : ℕ) : uCode.eval z = Part.some (uEmit z) := exists_uCode.choose_spec z

lemma uCode_evaln_eq {k x out : ℕ} (h : uCode.evaln k x = some out) : out = uEmit x := by
  have hmem : out ∈ uCode.eval x := Nat.Partrec.Code.evaln_sound h
  rw [uCode_eval] at hmem
  simpa using hmem

lemma uCode_evaln_exists (x : ℕ) :
    ∃ F₀, ∀ F, F₀ ≤ F → uCode.evaln F x = some (uEmit x) := by
  have hmem : uEmit x ∈ uCode.eval x := by rw [uCode_eval]; exact Part.mem_some _
  obtain ⟨F₀, hF₀⟩ := Nat.Partrec.Code.evaln_complete.mp hmem
  exact ⟨F₀, fun F hF => Nat.Partrec.Code.evaln_mono hF hF₀⟩

/-- One clocked reading of the exact table: stage `j`, sentence index `i`, clock `F`.
`0` means "the clock ran out". -/
noncomputable def uRead (F j i : ℕ) : ℕ :=
  codeEvalnNat uCode (Nat.pair F (Nat.pair j i))

lemma uRead_eq_of_ne_zero {F j i : ℕ} (h : uRead F j i ≠ 0) :
    uRead F j i = Encodable.encode (uTab j i) + 1 := by
  rw [uRead, codeEvalnNat] at h ⊢
  simp only [Nat.unpair_pair] at h ⊢
  cases hev : uCode.evaln F (Nat.pair j i) with
  | none => rw [hev] at h; simp at h
  | some out => rw [uCode_evaln_eq hev, uEmit, Nat.unpair_pair]

lemma uRead_le (F j i : ℕ) : uRead F j i ≤ codeEvalBound uCode F + 1 := by
  simpa [uRead] using codeEvalnNat_le uCode (Nat.pair F (Nat.pair j i))

lemma uRead_ne_zero (j i : ℕ) : ∃ F₀, ∀ F, F₀ ≤ F → uRead F j i ≠ 0 := by
  obtain ⟨F₀, hF₀⟩ := uCode_evaln_exists (Nat.pair j i)
  refine ⟨F₀, fun F hF => ?_⟩
  rw [uRead, codeEvalnNat]
  simp [Nat.unpair_pair, hF₀ F hF]

/-- The polynomial clock offered at query `z`. -/
def uFuel (z : ℕ) : ℕ := Nat.pair z z

lemma le_uFuel (z : ℕ) : z ≤ uFuel z := Nat.left_le_pair z z

/-- The stage that the last successful reading below `j` came from. -/
noncomputable def uStage (z : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => if uRead (uFuel z) j z.unpair.2 = 0 then uStage z j else j

/-- The carried encoded state of the scan. -/
noncomputable def uState (z : ℕ) : ℕ → ℕ
  | 0 => Encodable.encode (0 : ℚ) + 1
  | j + 1 =>
      ifzSelFn (Nat.pair (uState z j) (uRead (uFuel z) j z.unpair.2))
        (uRead (uFuel z) j z.unpair.2)

lemma uState_zero (z : ℕ) : uState z 0 = Encodable.encode (0 : ℚ) + 1 := rfl

lemma uState_eq (z : ℕ) : ∀ j,
    uState z j = Encodable.encode (uTab (uStage z j) z.unpair.2) + 1
  | 0 => by rw [uState, uStage, uTab_zero]
  | j + 1 => by
      rw [uState, uStage, ifzSelFn]
      by_cases h : uRead (uFuel z) j z.unpair.2 = 0
      · rw [if_pos h, if_pos h, Nat.unpair_pair]
        exact uState_eq z j
      · rw [if_neg h, if_neg h, Nat.unpair_pair]
        exact uRead_eq_of_ne_zero h

lemma uState_le (z : ℕ) : ∀ j,
    uState z j ≤ codeEvalBound uCode (uFuel z) + Encodable.encode (0 : ℚ) + 2
  | 0 => by rw [uState]; omega
  | j + 1 => by
      rw [uState, ifzSelFn]
      by_cases h : uRead (uFuel z) j z.unpair.2 = 0
      · rw [if_pos h, Nat.unpair_pair]; exact uState_le z j
      · rw [if_neg h, Nat.unpair_pair]
        have := uRead_le (uFuel z) j z.unpair.2
        omega

/-- A stage whose reading succeeds is never lost. -/
lemma le_uStage {z j N : ℕ} (hj : j < N) (h : uRead (uFuel z) j z.unpair.2 ≠ 0) :
    j ≤ uStage z N := by
  induction N with
  | zero => omega
  | succ N ih =>
      rw [uStage]
      by_cases hN : uRead (uFuel z) N z.unpair.2 = 0
      · rw [if_pos hN]
        rcases Nat.lt_or_ge j N with hlt | hge
        · exact ih hlt
        · have hjN : j = N := by omega
          subst hjN
          exact absurd hN h
      · rw [if_neg hN]; omega

/-- **The poly-fuel stage table.**  At query `z = ⟪n, i⟫` it is the exact table at whatever
stage `< n` the clock `⟪z,z⟫` last completed on sentence index `i`.
Paper node: `thm:ob` -/
noncomputable def uSel (z : ℕ) : ℚ := uTab (uStage z z.unpair.1) z.unpair.2

lemma uSel_nonneg (z : ℕ) : 0 ≤ uSel z := uTab_nonneg _ _

lemma uSel_le (z : ℕ) :
    ((uSel z : ℚ) : ℝ) ≤ prefixWeight kappaU (prefixSentenceEnum z.unpair.2) :=
  uTab_le _ _

lemma encode_uSel (z : ℕ) : Encodable.encode (uSel z) = uState z z.unpair.1 - 1 := by
  rw [uSel, uState_eq]
  omega

/-- Every fixed stage is eventually reached. -/
lemma uSel_eventually_ge (m i : ℕ) :
    ∀ᶠ n in atTop, uTab m i ≤ uSel (Nat.pair n i) := by
  obtain ⟨F₀, hF₀⟩ := uRead_ne_zero m i
  refine Filter.eventually_atTop.2 ⟨max (m + 1) F₀, fun n hn => ?_⟩
  have hni : n ≤ Nat.pair n i := Nat.left_le_pair n i
  have hfuel : F₀ ≤ uFuel (Nat.pair n i) :=
    le_trans (le_trans (le_max_right _ _) hn) (le_trans hni (le_uFuel _))
  have hsnd : (Nat.pair n i).unpair.2 = i := by simp
  have hne : uRead (uFuel (Nat.pair n i)) m (Nat.pair n i).unpair.2 ≠ 0 := by
    rw [hsnd]; exact hF₀ _ hfuel
  have hlt : m < (Nat.pair n i).unpair.1 := by
    have : m + 1 ≤ n := le_trans (le_max_left _ _) hn
    simpa using this
  have := le_uStage hlt hne
  rw [uSel, hsnd]
  exact uTab_mono this i

lemma uSel_tendsto (i : ℕ) :
    Tendsto (fun n => ((uSel (Nat.pair n i) : ℚ) : ℝ)) atTop
      (𝓝 (prefixWeight kappaU (prefixSentenceEnum i))) := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · obtain ⟨m, hm⟩ := ((uTab_tendsto i).eventually (eventually_gt_nhds ha)).exists
    filter_upwards [uSel_eventually_ge m i] with n hn
    exact lt_of_lt_of_le hm (by exact_mod_cast hn)
  · refine Filter.Eventually.of_forall fun n => lt_of_le_of_lt ?_ hb
    have h := uSel_le (Nat.pair n i)
    simpa using h

/-! ### The emission certificate

`PolyFueled.prec` over the packed input `w = ⟪z, ⟪j, prev⟫⟫`; the only nontrivial input is
the clocked reading, poly-fueled because the simulated code is *fixed*. -/

/-- The scan's step function on the packed `prec` input `w = ⟪z, ⟪j, prev⟫⟫`. -/
noncomputable def uStep (w : ℕ) : ℕ :=
  ifzSelFn
    (Nat.pair w.unpair.2.unpair.2
      (codeEvalnNat uCode
        (Nat.pair (Nat.pair w.unpair.1 w.unpair.1)
          (Nat.pair w.unpair.2.unpair.1 w.unpair.1.unpair.2))))
    (codeEvalnNat uCode
      (Nat.pair (Nat.pair w.unpair.1 w.unpair.1)
        (Nat.pair w.unpair.2.unpair.1 w.unpair.1.unpair.2)))

lemma uState_succ (z j : ℕ) :
    uState z (j + 1) = uStep (Nat.pair z (Nat.pair j (uState z j))) := by
  rw [uStep]
  simp only [Nat.unpair_pair]
  rfl

attribute [local irreducible] Nat.sqrt uApprox uTab kappaStage in
lemma uStep_polyFueled : ∃ c, PolyFueled c uStep := by
  obtain ⟨cR, hR⟩ := codeEvalnNat_polyFueled uCode
  have hz : PolyFueled _ (fun w : ℕ => w.unpair.1) := PolyFueled.left
  have hr : PolyFueled _ (fun w : ℕ => w.unpair.2) := PolyFueled.right
  have hj := PolyFueled.left.comp hr
  have hprev := PolyFueled.right.comp hr
  have hi := PolyFueled.right.comp hz
  have hv := hR.comp ((hz.pair hz).pair (hj.pair hi))
  exact ⟨_, (ifzSel_polyFueled.comp ((hprev.pair hv).pair hv)).of_eq
    (fun w => by simp only [Nat.unpair_pair, uStep])⟩

-- **The poly-fuel emission certificate of the universal machine's stage table.**  The
-- polynomial clock is *constructed* here; only the exact table's code is an input.
-- Paper node: `thm:ob`
attribute [local irreducible] Nat.sqrt uApprox uTab kappaStage uStep uState in
/-- The clocked selection table is polynomially emitted: the `evaln` self-clamp
lets the emitter select exact stage values under a polynomial clock.
Paper node: `thm:ob` -/
theorem uSel_polyRatCodes : PolyRatCodes uSel := by
  obtain ⟨cs, hs⟩ := uStep_polyFueled
  have hst : IsPolyBounded (fun m => uState m.unpair.1 m.unpair.2) := by
    refine IsPolyBounded.of_le
      (b' := fun m => codeEvalBound uCode (Nat.pair m.unpair.1 m.unpair.1)
        + Encodable.encode (0 : ℚ) + 2)
      ((IsPolyBounded.linear (Encodable.encode (0 : ℚ) + 2)).comp
        ((codeEvalBound_poly uCode).comp
          (isPolyBounded_fst.pair isPolyBounded_fst))) (fun m => ?_)
    have := uState_le m.unpair.1 m.unpair.2
    simpa [uFuel] using this
  have hprec := PolyFueled.prec (PolyFueled.const (Encodable.encode (0 : ℚ) + 1)) hs
    (st := uState) uState_zero uState_succ hst
  have hstate : ∃ c, PolyFueled c (fun z => uState z z.unpair.1) :=
    ⟨_, (hprec.comp (PolyFueled.id.pair PolyFueled.left)).of_eq
      (fun z => by simp only [Nat.unpair_pair])⟩
  obtain ⟨c, hc⟩ := hstate
  exact ⟨_, (predc_polyFueled.comp hc).of_eq (fun z => (encode_uSel z).symm)⟩

/-- **The universal prefix machine as an Occam presentation.**  Every *mathematical* field
is discharged here — the Kraft budget from the built-in prefix-freeness of `dom U`,
coverage from the reused sentence enumeration, and the from-below convergence of the
clocked stage table — including the exact table's own program (`uCode`).  There is no
residual input.
Paper node: `thm:ob` -/
noncomputable def universalPrefixPresentation :
    PrefixMachinePresentation kappaU where
  sentence := prefixSentenceEnum
  sentence_codes := prefixSentenceEnum_polySentenceCodes
  approximation := fun n i => uSel (Nat.pair n i)
  approximation_codes := by
    obtain ⟨c, hc⟩ := uSel_polyRatCodes
    exact ⟨c, hc.of_eq (fun z => by simp only [Nat.pair_unpair])⟩
  approximation_nonneg := fun n i => uSel_nonneg _
  approximation_le := fun n i => by
    have := uSel_le (Nat.pair n i)
    simpa using this
  approximation_tendsto := uSel_tendsto
  kraft := kappaU_kraft
  covers := prefixSentenceEnum_covers

/-! ## The gate token emission

Both `OccamThresholdEmission` streams are rational arithmetic on the emitted stage
rational, exactly as in `Dovetail.dusThresholdEmission`: with `q = N/D` in lowest terms and
rung scale `k = z.1 + 1`, the base is `N / (2·k⁴·D)`, the threshold sum is `N / (k⁴·D)` and
the inverse width is `2·k⁴·D / N` (all zero when `N = 0`, matching `ℚ`'s `x / 0 = 0`).  The
generic `gcd`-reduced emitter `Dovetail.encode_natDiv_polyFueled` covers both. -/

/-- The stage-table query behind gate input `z = ⟨j', ⟨n, i⟩⟩`. -/
def uQuery (z : ℕ) : ℕ := Nat.pair z.unpair.2.unpair.1 z.unpair.2.unpair.2

/-- Reduced numerator of the emitted stage rational at the gate query. -/
noncomputable def uNum (z : ℕ) : ℕ :=
  (Encodable.encode (uSel (uQuery z))).unpair.1 / 2

/-- Reduced denominator of the emitted stage rational at the gate query. -/
noncomputable def uDenom (z : ℕ) : ℕ :=
  (Encodable.encode (uSel (uQuery z))).unpair.2

lemma uNum_eq (z : ℕ) : uNum z = (uSel (uQuery z)).num.toNat := by
  rw [uNum, Dovetail.encode_rat_of_nonneg (uSel_nonneg _), Nat.unpair_pair]
  omega

lemma uDenom_eq (z : ℕ) : uDenom z = (uSel (uQuery z)).den := by
  rw [uDenom, Dovetail.encode_rat_of_nonneg (uSel_nonneg _), Nat.unpair_pair]

lemma uDenom_pos (z : ℕ) : 0 < uDenom z := by
  rw [uDenom_eq]; exact (uSel (uQuery z)).den_pos

lemma uSel_query_eq (z : ℕ) :
    uSel (uQuery z) = (uNum z : ℚ) / (uDenom z : ℚ) := by
  have hnn : 0 ≤ (uSel (uQuery z)).num := Rat.num_nonneg.mpr (uSel_nonneg _)
  have hcast : ((uSel (uQuery z)).num.toNat : ℚ) = ((uSel (uQuery z)).num : ℚ) := by
    exact_mod_cast congrArg (fun n : ℤ => (n : ℚ)) (Int.toNat_of_nonneg hnn)
  rw [uNum_eq, uDenom_eq, hcast]
  exact (Rat.num_div_den _).symm

section Emission

attribute [local irreducible] Nat.sqrt uSel uStage uState uApprox uTab kappaStage

lemma uNum_polyFueled : ∃ c, PolyFueled c uNum := by
  obtain ⟨c, hc⟩ := uSel_polyRatCodes
  obtain ⟨cdm, hdm⟩ := divmodc_polyFueled 2 (by norm_num)
  have hq : PolyFueled _ (fun z : ℕ => Nat.pair z.unpair.2.unpair.1 z.unpair.2.unpair.2) :=
    (PolyFueled.left.comp PolyFueled.right).pair (PolyFueled.right.comp PolyFueled.right)
  exact ⟨_, (PolyFueled.left.comp (hdm.comp (PolyFueled.left.comp (hc.comp hq)))).of_eq
    (fun z => by simp only [Nat.unpair_pair]; rfl)⟩

lemma uDenom_polyFueled : ∃ c, PolyFueled c uDenom := by
  obtain ⟨c, hc⟩ := uSel_polyRatCodes
  have hq : PolyFueled _ (fun z : ℕ => Nat.pair z.unpair.2.unpair.1 z.unpair.2.unpair.2) :=
    (PolyFueled.left.comp PolyFueled.right).pair (PolyFueled.right.comp PolyFueled.right)
  exact ⟨_, (PolyFueled.right.comp (hc.comp hq)).of_eq (fun z => rfl)⟩

/-- `z ↦ uDenom z * (w * (z.1 + 1)⁴)`, the gate denominators for `w = 1` and `w = 2`. -/
lemma uGateDen_polyFueled (w : ℕ) :
    ∃ c, PolyFueled c (fun z => uDenom z * (w * (z.unpair.1 + 1) ^ 4)) := by
  obtain ⟨cd, hd⟩ := uDenom_polyFueled
  obtain ⟨cm, hm⟩ := mul_polyFueled
  have hk1 := PolyFueled.left.succ_comp
  have hk2 := (hm.comp (hk1.pair hk1)).of_eq
    (f' := fun z : ℕ => (z.unpair.1 + 1) * (z.unpair.1 + 1))
    (fun z => by simp only [Nat.unpair_pair])
  have hk4 := (hm.comp (hk2.pair hk2)).of_eq
    (f' := fun z : ℕ => (z.unpair.1 + 1) ^ 4)
    (fun z => by simp only [Nat.unpair_pair]; ring)
  have hw := (hm.comp ((PolyFueled.const w).pair hk4)).of_eq
    (f' := fun z : ℕ => w * (z.unpair.1 + 1) ^ 4) (fun z => by simp only [Nat.unpair_pair])
  exact ⟨_, (hm.comp (hd.pair hw)).of_eq (fun z => by simp only [Nat.unpair_pair])⟩

attribute [local irreducible] uNum uDenom in
lemma uEmitBase_eq (z : ℕ) :
    obEmitBase universalPrefixPresentation z
      = (uNum z : ℚ) / ((uDenom z * (2 * (z.unpair.1 + 1) ^ 4) : ℕ) : ℚ) := by
  have hD : (0 : ℚ) < (uDenom z : ℚ) := by exact_mod_cast uDenom_pos z
  have hk : (0 : ℚ) < ((z.unpair.1 : ℚ) + 1) := by positivity
  show uSel (uQuery z) / (2 * ((z.unpair.1 + 1 : ℕ) : ℚ) ^ 4) = _
  rw [uSel_query_eq]
  push_cast
  field_simp

lemma uEmitSum_eq (z : ℕ) :
    obEmitBase universalPrefixPresentation z + obEmitBase universalPrefixPresentation z
      = (uNum z : ℚ) / ((uDenom z * (1 * (z.unpair.1 + 1) ^ 4) : ℕ) : ℚ) := by
  have hD : (0 : ℚ) < (uDenom z : ℚ) := by exact_mod_cast uDenom_pos z
  have hk : (0 : ℚ) < ((z.unpair.1 : ℚ) + 1) := by positivity
  rw [uEmitBase_eq]
  push_cast
  field_simp
  ring

lemma uEmitRecip_eq (z : ℕ) :
    1 / obEmitBase universalPrefixPresentation z
      = ((uDenom z * (2 * (z.unpair.1 + 1) ^ 4) : ℕ) : ℚ) / (uNum z : ℚ) := by
  rw [uEmitBase_eq, one_div_div]

/-- The gate token emission of the universal machine, derived from its stage-table
emission.
Paper node: `thm:ob` -/
theorem universalPrefixThresholdEmission :
    OccamThresholdEmission universalPrefixPresentation where
  threshold_sum_codes := by
    obtain ⟨cn, hn⟩ := uNum_polyFueled
    obtain ⟨cd, hd⟩ := uGateDen_polyFueled 1
    obtain ⟨c, hc⟩ := Dovetail.encode_natDiv_polyFueled hn hd
    exact ⟨c, hc.of_eq (fun z => by simp only [uEmitSum_eq])⟩
  inverse_width_codes := by
    obtain ⟨cn, hn⟩ := uGateDen_polyFueled 2
    obtain ⟨cd, hd⟩ := uNum_polyFueled
    obtain ⟨c, hc⟩ := Dovetail.encode_natDiv_polyFueled hn hd
    exact ⟨c, hc.of_eq (fun z => by simp only [uEmitRecip_eq])⟩

end Emission

/-! ## Paper-facing endpoints over the universal machine -/

/-- **Lower Occam bound at universal prefix complexity.**  Same statement as
`lic_occam_lower_ofPrefixMachine`, but `κ` is now the prefix complexity of a genuine
universal prefix machine (`kappaU_le_of_prefixMachine`), not of one fixed code.
Unconditional: the stage table's emission is fully constructed (`uSel_polyRatCodes`).
Paper node: `thm:ob` -/
theorem lic_occam_lower_ofUniversalPrefix (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ∃ K : ℝ, 0 < K ∧ ∀ φ,
      (∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ v.Holds φ) →
      K * prefixWeight kappaU φ ≤ limitingBelief P φ :=
  lic_occam_lower universalPrefixPresentation
    (universalPrefixThresholdEmission) P DP hworld

/-- **Occam Bounds at universal prefix complexity**, with the negation compiler discharged
by the machine's hard-wired negation instruction (overhead `2`).
Unconditional: the stage table's emission is fully constructed (`uSel_polyRatCodes`).
Paper node: `thm:ob` -/
theorem lic_occamBounds_ofUniversalPrefix (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ∃ K : ℝ, 0 < K ∧
      (∀ φ,
        (∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ v.Holds φ) →
        K * prefixWeight kappaU φ ≤ limitingBelief P φ) ∧
      (∀ φ,
        (∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ ¬ v.Holds φ) →
        limitingBelief P φ ≤ 1 - K * prefixWeight kappaU φ) :=
  lic_occamBounds universalPrefixPresentation
    (universalPrefixThresholdEmission) kappaUNegationCompiler P DP hworld

#print axioms UHalt_prefixFree
#print axioms UHalt_functional
#print axioms kappaU_kraft
#print axioms kappaUNegationCompiler
#print axioms kappaU_le_of_prefixMachine
#print axioms kappaStage_eventually_eq
#print axioms uMinLen_eq
#print axioms uEmit_prim
#print axioms exists_uCode
#print axioms universalPrefixPresentation
#print axioms lic_occam_lower_ofUniversalPrefix
#print axioms lic_occamBounds_ofUniversalPrefix

end UPrefix

end LogicalInduction
