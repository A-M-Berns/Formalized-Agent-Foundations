import LogicalInduction.Framework.Computable
import LogicalInduction.Framework.RpnSentence

/-!
# RPN splice streams: the 𝓔𝓒-sequence interface and its combinators

Sits upstream of the feature and LUV interfaces so their structures can carry the
`𝓔𝓒`-sequence hypothesis.

`RpnSentenceCodes φ` is a narrower, token-metered sufficient subclass of `def:ec`'s own
write-out sentence class `BigSentenceCodes` (`Framework/WriteOut.lean`): a `PolySegStream`
of self-delimiting sentence blocks parsing to `φ`, each block consumed exactly, which
bounds every emitted token's *value* on top of their number. The whole-value interface
`PolySentenceCodes` meters the single pair-code token, which excludes deep or skewed
sentence sequences whose codes are value-exponential in their symbol count;
`RpnSentenceCodes` meters symbols instead. `BigSentenceCodes.ofRpnSentenceCodes` is the
inclusion into the node's own class; no separation of the two is proved.

The paper's affine and self-trust theorems quantify over `BigSentenceCodes`, not over this
class. `RpnSentenceCodes` is the supply side: the class the compilers in `Construction/`
emit into, and the class the LUV threshold interfaces `LUV.RpnThresholdCodes(Seq)`
(`Framework/Expectations.lean`) are phrased in.

Constructors and combinators: `ofCanonical`, `ofPolySentenceCodes`, `const`, `of_eq`,
`comp`, `ifZero`, `modDispatch` (the fixed-`k` families of `thm:lex`), the fixed-arity
`and`/`or`/`imp`, and the variable-width `bigOr`/`bigAnd`, whose parse laws are
`parseRpn_disjChain`/`parseRpn_conjChain`.

`RpnSpliceStream ts` says some `PolySegStream` contracts (`UnRpnContractsTo`) to `ts`
position-wise. Slot-free runs embed by transparency; price and trade sentence slots draw
their blocks from an `RpnSentenceCodes` certificate; the class is closed under the same
combinators as `PolySegStream`, so a `serialize` emission assembly transfers combinator for
combinator. The realization capstones (digitize + `ec_of_rawSegStream`) live in
`Framework/RpnEmission.lean`.

Paper node: `def:ec` (token-metered sentence slots — a subclass rendering, not the node's
own class).
-/

namespace LogicalInduction

/-! ## A token-metered 𝓔𝓒 sentence-sequence subclass (`RpnSentenceCodes`) -/

/-- A `PolySegStream` of self-delimiting sentence blocks parsing to `φ`, each block
consumed exactly; a token-metered sufficient subclass of `BigSentenceCodes` (see the module
docstring).  Canonical Polish runs (`ofCanonical`) admit arbitrarily deep and skewed
sentences at poly symbol count; escaped pair codes (`ofPolySentenceCodes`) embed the
whole-value interface.
Paper node: `def:ec` -/
def RpnSentenceCodes (φ : ℕ → Sentence) : Prop :=
  ∃ s : ℕ → List ℕ, PolySegStream s ∧
    ∀ n, parseRpn (s n).length (s n) = some (φ n, [])

/-- A polynomially emittable canonical Polish stream instantiates the class (the paper's
𝓔𝓒 *metering* on the nose: poly stream length = poly symbol count; this is a statement
about the cost measure, not a claim that the fuel-metered class equals the paper's). -/
lemma RpnSentenceCodes.ofCanonical {φ : ℕ → Sentence}
    (h : PolySegStream fun n => rpn (φ n)) : RpnSentenceCodes φ :=
  ⟨_, h, fun n => by
    simpa using parseRpn_rpn (φ n) [] (le_refl (rpn (φ n)).length)⟩

/-- Every whole-value certificate embeds by two-token escape blocks. -/
lemma RpnSentenceCodes.ofPolySentenceCodes {φ : ℕ → Sentence}
    (h : PolySentenceCodes φ) : RpnSentenceCodes φ := by
  obtain ⟨c, hc⟩ := h
  refine ⟨fun n => [1, Encodable.encode (φ n)],
    PolySegStream.ofTokenStream
      ((PolyTokenStream.const 1).append (PolyTokenStream.polyTok hc)),
    fun n => parseRpn_escape (φ n) [] (by norm_num)⟩

/-- Reindexing along a poly-fueled index map (e.g. `z ↦ z.unpair.1` for the paired
family index of `PolySequence`). -/
lemma RpnSentenceCodes.comp {φ : ℕ → Sentence} (h : RpnSentenceCodes φ)
    {c : Nat.Partrec.Code} {f : ℕ → ℕ} (hf : PolyFueled c f) :
    RpnSentenceCodes (fun z => φ (f z)) := by
  obtain ⟨s, hs, hp⟩ := h
  exact ⟨fun z => s (f z), hs.comp hf, fun z => hp (f z)⟩

/-- Transport along a pointwise equality of sentence families. -/
lemma RpnSentenceCodes.of_eq {φ ψ : ℕ → Sentence} (h : RpnSentenceCodes φ)
    (hφψ : ∀ n, φ n = ψ n) : RpnSentenceCodes ψ := by
  obtain ⟨s, hs, hp⟩ := h
  exact ⟨s, hs, fun n => (hφψ n) ▸ hp n⟩

/-- A fixed sentence is a token-metered efficient sentence family.  This is the
consumer constructor for constant propositions; it keeps callers above the raw clocked
code layer. -/
lemma RpnSentenceCodes.const (φ : Sentence) : RpnSentenceCodes (fun _ => φ) :=
  RpnSentenceCodes.ofPolySentenceCodes
    ⟨_, PolyFueled.const (Encodable.encode φ)⟩

/-- Two-way dispatch of sentence-block streams along a poly-fueled test. -/
lemma RpnSentenceCodes.ifZero {φ ψ : ℕ → Sentence}
    (hφ : RpnSentenceCodes φ) (hψ : RpnSentenceCodes ψ)
    {c : Nat.Partrec.Code} {t : ℕ → ℕ} (ht : PolyFueled c t) :
    RpnSentenceCodes (fun z => if t z = 0 then φ z else ψ z) := by
  obtain ⟨a, ha, hpa⟩ := hφ
  obtain ⟨b, hb, hpb⟩ := hψ
  refine ⟨fun z => if t z = 0 then a z else b z,
    PolySegStream.ifZero ha hb ht, fun z => ?_⟩
  by_cases hz : t z = 0
  · simpa [hz] using hpa z
  · simpa [hz] using hpb z

/-- Conjunction of two sentence-block streams: the fixed `⋏` tag in front of the two
blocks, which the prefix parser consumes in order. -/
lemma RpnSentenceCodes.and {φ ψ : ℕ → Sentence}
    (hφ : RpnSentenceCodes φ) (hψ : RpnSentenceCodes ψ) :
    RpnSentenceCodes (fun z => φ z ⋏ ψ z) := by
  obtain ⟨a, ha, hpa⟩ := hφ
  obtain ⟨b, hb, hpb⟩ := hψ
  have h3 : PolySegStream (fun _ : ℕ => [3]) :=
    PolySegStream.ofTokenStream (PolyTokenStream.const 3)
  refine ⟨fun z => 3 :: (a z ++ b z), ((h3.append ha).append hb).of_eq (fun z => by simp),
    fun z => ?_⟩
  have hlen : (3 :: (a z ++ b z)).length = (a z).length + (b z).length + 1 := by
    simp
  rw [hlen, parseRpn_cons]
  rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]
  rw [parseRpn_block_head (hpa z) (b z) (by omega)]
  simp only [Option.bind_some]
  rw [parseRpn_mono (b z) (show (b z).length ≤ (a z).length + (b z).length by omega)
    (hpb z)]
  rfl

/-- Disjunction of two sentence-block streams: the fixed `⋎` tag in front of the two
blocks, which the prefix parser consumes in order. -/
lemma RpnSentenceCodes.or {φ ψ : ℕ → Sentence}
    (hφ : RpnSentenceCodes φ) (hψ : RpnSentenceCodes ψ) :
    RpnSentenceCodes (fun z => φ z ⋎ ψ z) := by
  obtain ⟨a, ha, hpa⟩ := hφ
  obtain ⟨b, hb, hpb⟩ := hψ
  have h4 : PolySegStream (fun _ : ℕ => [4]) :=
    PolySegStream.ofTokenStream (PolyTokenStream.const 4)
  refine ⟨fun z => 4 :: (a z ++ b z), ((h4.append ha).append hb).of_eq (fun z => by simp),
    fun z => ?_⟩
  have hlen : (4 :: (a z ++ b z)).length = (a z).length + (b z).length + 1 := by
    simp
  rw [hlen, parseRpn_cons]
  rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
    if_neg (by norm_num), if_pos rfl]
  rw [parseRpn_block_head (hpa z) (b z) (by omega)]
  simp only [Option.bind_some]
  rw [parseRpn_mono (b z) (show (b z).length ≤ (a z).length + (b z).length by omega)
    (hpb z)]
  rfl

/-- Implication of two sentence-block streams: the fixed implication tag in front of the
two blocks, which the prefix parser consumes in order. -/
lemma RpnSentenceCodes.imp {φ ψ : ℕ → Sentence}
    (hφ : RpnSentenceCodes φ) (hψ : RpnSentenceCodes ψ) :
    RpnSentenceCodes (fun z => LO.Propositional.Formula.imp (φ z) (ψ z)) := by
  obtain ⟨a, ha, hpa⟩ := hφ
  obtain ⟨b, hb, hpb⟩ := hψ
  have h2 : PolySegStream (fun _ : ℕ => [2]) :=
    PolySegStream.ofTokenStream (PolyTokenStream.const 2)
  refine ⟨fun z => 2 :: (a z ++ b z), ((h2.append ha).append hb).of_eq (fun z => by simp),
    fun z => ?_⟩
  have hlen : (2 :: (a z ++ b z)).length = (a z).length + (b z).length + 1 := by
    simp
  rw [hlen, parseRpn_cons]
  rw [if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]
  rw [parseRpn_block_head (hpa z) (b z) (by omega)]
  simp only [Option.bind_some]
  rw [parseRpn_mono (b z) (show (b z).length ≤ (a z).length + (b z).length by omega)
    (hpb z)]
  rfl

/-! ### Variable-width disjunction blocks

The mesh product of `thm:ccee` needs a disjunction whose *width* grows with the index, so
its block cannot be a fixed tuple of segments.  The emitted form is a `concatVar` of
`⋎`-tagged disjunct blocks closed by a single `⊥` token, which the prefix parser reads as
the right-associated `sentenceDisjunction` of the disjuncts. -/

/-- The prefix parser reads a `⋎`-tagged chain of complete blocks closed by `⊥` as the
right-associated disjunction of the blocks' sentences, leaving the tail untouched. -/
private lemma parseRpn_disjChain (blk : ℕ → List ℕ) (D : ℕ → Sentence)
    (hblk : ∀ b, parseRpn (blk b).length (blk b) = some (D b, [])) :
    ∀ (t a : ℕ) (rest : List ℕ) (fuel : ℕ),
      (((List.range t).flatMap fun j => 4 :: blk (a + j)) ++ 0 :: rest).length ≤ fuel →
      parseRpn fuel (((List.range t).flatMap fun j => 4 :: blk (a + j)) ++ 0 :: rest) =
        some (sentenceDisjunction ((List.range t).map fun j => D (a + j)), rest) := by
  intro t
  induction t with
  | zero =>
      intro a rest fuel hfuel
      simp only [List.range_zero, List.flatMap_nil, List.nil_append, List.map_nil]
      obtain ⟨fuel, rfl⟩ : ∃ g, fuel = g + 1 := by
        cases fuel with
        | zero => simp at hfuel
        | succ g => exact ⟨g, rfl⟩
      rw [parseRpn_cons, if_pos rfl]
      rfl
  | succ t ih =>
      intro a rest fuel hfuel
      have hsplit : ((List.range (t + 1)).flatMap fun j => 4 :: blk (a + j)) =
          (4 :: blk a) ++ ((List.range t).flatMap fun j => 4 :: blk (a + 1 + j)) := by
        rw [List.range_succ_eq_map]
        simp only [List.flatMap_cons, List.flatMap_map,
          Nat.add_zero]
        congr 1
        refine List.flatMap_congr (fun j _ => ?_)
        congr 2
        omega
      have hmapsplit : ((List.range (t + 1)).map fun j => D (a + j)) =
          D a :: ((List.range t).map fun j => D (a + 1 + j)) := by
        rw [List.range_succ_eq_map]
        simp only [List.map_cons, List.map_map, Function.comp_def, Nat.add_zero]
        congr 1
        refine List.map_congr_left (fun j _ => ?_)
        congr 1
        omega
      rw [hsplit] at hfuel
      rw [hsplit, hmapsplit]
      set F := (List.range t).flatMap fun j => 4 :: blk (a + 1 + j) with hF
      have hassoc : ((4 :: blk a) ++ F) ++ 0 :: rest =
          4 :: (blk a ++ (F ++ 0 :: rest)) := by simp
      rw [hassoc] at hfuel ⊢
      obtain ⟨fuel, rfl⟩ : ∃ g, fuel = g + 1 := by
        cases fuel with
        | zero => simp at hfuel
        | succ g => exact ⟨g, rfl⟩
      have hlen : (blk a).length + (F ++ 0 :: rest).length ≤ fuel := by
        simp only [List.length_cons, List.length_append] at hfuel ⊢
        omega
      rw [parseRpn_cons]
      rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
        if_neg (by norm_num), if_pos rfl]
      rw [parseRpn_block_head (hblk a) (F ++ 0 :: rest)
        (le_trans (Nat.le_add_right _ _) hlen)]
      simp only [Option.bind_some]
      rw [ih (a + 1) rest fuel (le_trans (Nat.le_add_left _ _) hlen)]
      rfl

/-! ### Variable-width conjunction blocks

The growing-conditioning strengthening of `thm:scon` needs a conjunction whose *width*
grows with the index — the prefix conjunction `ψ₀ ⋏ ⋯ ⋏ ψₙ`.  As with the disjunction
chain the block cannot be a fixed tuple of segments; the emitted form is a `concatVar` of
`⋏`-tagged conjunct blocks closed by the fixed three-token constant `[2, 0, 0]`, which the
prefix parser reads as `⊤ = ⊥ ➝ ⊥` (Foundation's `Formula.top_def`, definitional), the
conjunction identity.  This is the empty-fold terminator, mirroring the single `⊥` token
that closes the disjunction chain. -/

/-- The prefix parser reads a `⋏`-tagged chain of complete blocks closed by the constant
`[2, 0, 0]` (the block for `⊤ = ⊥ ➝ ⊥`) as the right-associated conjunction of the
blocks' sentences, leaving the tail untouched.  (Not `private`: the write-out mirror
`BigSentenceCodes.bigAnd` in `Framework/WriteOut.lean` reuses this parse fact verbatim.) -/
lemma parseRpn_conjChain (blk : ℕ → List ℕ) (D : ℕ → Sentence)
    (hblk : ∀ b, parseRpn (blk b).length (blk b) = some (D b, [])) :
    ∀ (t a : ℕ) (rest : List ℕ) (fuel : ℕ),
      (((List.range t).flatMap fun j => 3 :: blk (a + j)) ++ 2 :: 0 :: 0 :: rest).length ≤ fuel →
      parseRpn fuel (((List.range t).flatMap fun j => 3 :: blk (a + j)) ++ 2 :: 0 :: 0 :: rest) =
        some (sentenceConjunction ((List.range t).map fun j => D (a + j)), rest) := by
  intro t
  induction t with
  | zero =>
      intro a rest fuel hfuel
      simp only [List.range_zero, List.flatMap_nil, List.nil_append, List.map_nil]
      -- goal: parseRpn fuel (2 :: 0 :: 0 :: rest) = some (sentenceConjunction [], rest)
      obtain ⟨fuel, rfl⟩ : ∃ g, fuel = g + 1 := by
        cases fuel with
        | zero => simp at hfuel
        | succ g => exact ⟨g, rfl⟩
      rw [parseRpn_cons, if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]
      obtain ⟨fuel, rfl⟩ : ∃ g, fuel = g + 1 := by
        cases fuel with
        | zero => simp at hfuel
        | succ g => exact ⟨g, rfl⟩
      rw [parseRpn_cons, if_pos rfl]
      simp only [Option.bind_some]
      rw [parseRpn_cons, if_pos rfl]
      simp only [Option.bind_some]
      rfl
  | succ t ih =>
      intro a rest fuel hfuel
      have hsplit : ((List.range (t + 1)).flatMap fun j => 3 :: blk (a + j)) =
          (3 :: blk a) ++ ((List.range t).flatMap fun j => 3 :: blk (a + 1 + j)) := by
        rw [List.range_succ_eq_map]
        simp only [List.flatMap_cons, List.flatMap_map,
          Nat.add_zero]
        congr 1
        refine List.flatMap_congr (fun j _ => ?_)
        congr 2
        omega
      have hmapsplit : ((List.range (t + 1)).map fun j => D (a + j)) =
          D a :: ((List.range t).map fun j => D (a + 1 + j)) := by
        rw [List.range_succ_eq_map]
        simp only [List.map_cons, List.map_map, Function.comp_def, Nat.add_zero]
        congr 1
        refine List.map_congr_left (fun j _ => ?_)
        congr 1
        omega
      rw [hsplit] at hfuel
      rw [hsplit, hmapsplit]
      set F := (List.range t).flatMap fun j => 3 :: blk (a + 1 + j) with hF
      have hassoc : ((3 :: blk a) ++ F) ++ 2 :: 0 :: 0 :: rest =
          3 :: (blk a ++ (F ++ 2 :: 0 :: 0 :: rest)) := by simp
      rw [hassoc] at hfuel ⊢
      obtain ⟨fuel, rfl⟩ : ∃ g, fuel = g + 1 := by
        cases fuel with
        | zero => simp at hfuel
        | succ g => exact ⟨g, rfl⟩
      have hlen : (blk a).length + (F ++ 2 :: 0 :: 0 :: rest).length ≤ fuel := by
        simp only [List.length_cons, List.length_append] at hfuel ⊢
        omega
      rw [parseRpn_cons]
      rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]
      rw [parseRpn_block_head (hblk a) (F ++ 2 :: 0 :: 0 :: rest)
        (le_trans (Nat.le_add_right _ _) hlen)]
      simp only [Option.bind_some]
      rw [ih (a + 1) rest fuel (le_trans (Nat.le_add_left _ _) hlen)]
      rfl

/-- **Variable-width disjunction of sentence-block streams.**  `D z j` is the `j`-th
disjunct at index `z`, presented by a single block stream on the paired index, and `cnt z`
disjuncts are taken.  The emitted block is `cnt z` `⋎`-tagged disjunct blocks followed by
one `⊥` token — a `PolySegStream.concatVar`, so the whole family stays 𝓔𝓒.
Paper node: `def:ec` -/
lemma RpnSentenceCodes.bigOr {D : ℕ → ℕ → Sentence}
    (hD : RpnSentenceCodes fun m => D m.unpair.1 m.unpair.2)
    {ccnt : Nat.Partrec.Code} {cnt : ℕ → ℕ} (hcnt : PolyFueled ccnt cnt) :
    RpnSentenceCodes (fun z => sentenceDisjunction ((List.range (cnt z)).map (D z))) := by
  obtain ⟨b, hb, hpb⟩ := hD
  have h4 : PolySegStream (fun _ : ℕ => [4]) :=
    PolySegStream.ofTokenStream (PolyTokenStream.const 4)
  have h0 : PolySegStream (fun _ : ℕ => [0]) :=
    PolySegStream.ofTokenStream (PolyTokenStream.const 0)
  have hseg : PolySegStream (fun m => 4 :: b m) := (h4.append hb).of_eq (fun m => by simp)
  refine ⟨fun z => ((List.range (cnt z)).flatMap fun j => 4 :: b (Nat.pair z j)) ++ [0],
    ((PolySegStream.concatVar hseg hcnt).append h0).of_eq (fun z => rfl), fun z => ?_⟩
  have hblk : ∀ j, parseRpn (b (Nat.pair z j)).length (b (Nat.pair z j)) =
      some (D z j, []) := by
    intro j
    simpa using hpb (Nat.pair z j)
  have := parseRpn_disjChain (fun j => b (Nat.pair z j)) (fun j => D z j) hblk
    (cnt z) 0 []
    (((List.range (cnt z)).flatMap fun j => 4 :: b (Nat.pair z (0 + j))) ++ 0 :: []).length
    le_rfl
  simpa using this

/-- **Variable-width conjunction of sentence-block streams.**  `D z j` is the `j`-th
conjunct at index `z`, presented by a single block stream on the paired index, and `cnt z`
conjuncts are taken.  The emitted block is `cnt z` `⋏`-tagged conjunct blocks followed by
the three-token constant `[2, 0, 0]` (the block for `⊤`) — a `PolySegStream.concatVar`, so
the whole family stays 𝓔𝓒.  No positivity hypothesis on `cnt` is needed: the empty width
folds to `⊤`.
Paper node: `def:ec` -/
lemma RpnSentenceCodes.bigAnd {D : ℕ → ℕ → Sentence}
    (hD : RpnSentenceCodes fun m => D m.unpair.1 m.unpair.2)
    {ccnt : Nat.Partrec.Code} {cnt : ℕ → ℕ} (hcnt : PolyFueled ccnt cnt) :
    RpnSentenceCodes (fun z => sentenceConjunction ((List.range (cnt z)).map (D z))) := by
  obtain ⟨b, hb, hpb⟩ := hD
  have h3 : PolySegStream (fun _ : ℕ => [3]) :=
    PolySegStream.ofTokenStream (PolyTokenStream.const 3)
  have h200 : PolySegStream (fun _ : ℕ => [2, 0, 0]) :=
    PolySegStream.ofTokenStream ((PolyTokenStream.const 2).append
      ((PolyTokenStream.const 0).append (PolyTokenStream.const 0)))
  have hseg : PolySegStream (fun m => 3 :: b m) := (h3.append hb).of_eq (fun m => by simp)
  refine ⟨fun z => ((List.range (cnt z)).flatMap fun j => 3 :: b (Nat.pair z j)) ++ [2, 0, 0],
    ((PolySegStream.concatVar hseg hcnt).append h200).of_eq (fun z => rfl), fun z => ?_⟩
  have hblk : ∀ j, parseRpn (b (Nat.pair z j)).length (b (Nat.pair z j)) =
      some (D z j, []) := by
    intro j
    simpa using hpb (Nat.pair z j)
  have := parseRpn_conjChain (fun j => b (Nat.pair z j)) (fun j => D z j) hblk
    (cnt z) 0 []
    (((List.range (cnt z)).flatMap fun j => 3 :: b (Nat.pair z (0 + j)))
      ++ 2 :: 0 :: 0 :: []).length
    le_rfl
  simpa using this

section
-- `Nat.sqrt` is scoped irreducible: `PolyFueled` elaboration over paired inputs otherwise
-- loops in `whnf` (see `Construction/Witnesses/RpnFreeze.lean`).
attribute [local irreducible] Nat.sqrt

/-- Finite mod-`k` dispatch of sentence-block streams: the paper's fixed-`k` family
forms (`thm:lex`) quantify over `k` independent 𝓔𝓒 sequences read through
`z ↦ φ (z.unpair.2 % k) z.unpair.1`. -/
lemma RpnSentenceCodes.modDispatch {k : ℕ} (hk : 0 < k) {φ : ℕ → ℕ → Sentence}
    (hφ : ∀ j < k, RpnSentenceCodes (φ j)) :
    RpnSentenceCodes (fun z => φ (z.unpair.2 % k) z.unpair.1) := by
  obtain ⟨cdm, hdm⟩ := divmodc_polyFueled k hk
  obtain ⟨cadd, hadd⟩ := addc_polyFueled
  have hrem : PolyFueled _ (fun z : ℕ => z.unpair.2 % k) :=
    (PolyFueled.right.comp (hdm.comp PolyFueled.right)).of_eq (fun z => by
      simp)
  have hleft := PolyFueled.left
  have H : ∀ m, m ≤ k → RpnSentenceCodes (fun z =>
      if z.unpair.2 % k < m then φ (z.unpair.2 % k) z.unpair.1
      else φ 0 z.unpair.1) := by
    intro m
    induction m with
    | zero =>
        intro _
        exact ((hφ 0 hk).comp hleft).of_eq (fun z => by simp)
    | succ m ih =>
        intro hm
        have hmk : m < k := hm
        have htest : PolyFueled _ (fun z : ℕ =>
            (z.unpair.2 % k - m) + (m - z.unpair.2 % k)) :=
          (hadd.comp ((subc_polyFueled.comp (hrem.pair (PolyFueled.const m))).pair
            (subc_polyFueled.comp ((PolyFueled.const m).pair hrem)))).of_eq
            (fun z => by simp)
        refine (RpnSentenceCodes.ifZero ((hφ m hmk).comp hleft)
          (ih (le_of_lt hm)) htest).of_eq (fun z => ?_)
        by_cases heq : z.unpair.2 % k = m
        · rw [if_pos (by omega), if_pos (by omega), heq]
        · rw [if_neg (by omega)]
          by_cases hlt : z.unpair.2 % k < m + 1
          · rw [if_pos hlt, if_pos (by omega)]
          · rw [if_neg hlt, if_neg (by omega)]
  exact (H k le_rfl).of_eq (fun z => by
    rw [if_pos (Nat.mod_lt z.unpair.2 hk)])

end

/-- The spliced price-leaf segment over a sentence-block stream: the reusable segment for
buy-signal coefficients whose price leaf sits on the traded sentence, `[0, ⌜φ⌝, d]` with the
sentence token replaced by its block.  The sentence index and the day are read by
independent poly-fueled maps.  Its contraction is `UnRpnContractsTo.priceChunk`. -/
lemma priceSlotSeg {s : ℕ → List ℕ} (hs : PolySegStream s)
    {cs cd : Nat.Partrec.Code} {sf df : ℕ → ℕ}
    (hsf : PolyFueled cs sf) (hdf : PolyFueled cd df) :
    PolySegStream (fun m => 0 :: s (sf m) ++ [df m]) := by
  have h0 : PolySegStream (fun _ : ℕ => [0]) :=
    PolySegStream.ofTokenStream (PolyTokenStream.const 0)
  have hd : PolySegStream (fun m : ℕ => [df m]) :=
    PolySegStream.ofTokenStream (PolyTokenStream.polyTok hdf)
  exact ((h0.append (hs.comp hsf)).append hd).of_eq fun m => by
    simp

/-! ## `RpnSpliceStream` — polynomially emittable RPN expansions

A token-stream family is *RPN-spliceable* when some `PolySegStream` contracts
(`UnRpnContractsTo`) to it position-wise.  Slot-free streams embed by transparency;
price and trade sentence slots draw their blocks from an `RpnSentenceCodes`
certificate; and the class is closed under the same combinators as `PolySegStream`, so
a serialize emission assembly built from those combinators transfers combinator for
combinator. -/

/-- Some polynomially emittable stream contracts to `ts` position-wise. -/
def RpnSpliceStream (ts : ℕ → List ℕ) : Prop :=
  ∃ s : ℕ → List ℕ, PolySegStream s ∧ ∀ z, UnRpnContractsTo (s z) (ts z)

/-- A polynomially emittable stream with no sentence slots is spliceable by
transparency: contraction leaves it unchanged. -/
lemma RpnSpliceStream.ofTransparent {ts : ℕ → List ℕ} (h : PolySegStream ts)
    (ht : ∀ z, UnRpnTransparent (ts z)) : RpnSpliceStream ts :=
  ⟨ts, h, fun z => (ht z).contractsTo⟩

/-- Concatenation of spliceable streams, the workhorse for assembling an emission from
its segments. -/
lemma RpnSpliceStream.append {a b : ℕ → List ℕ}
    (ha : RpnSpliceStream a) (hb : RpnSpliceStream b) :
    RpnSpliceStream (fun z => a z ++ b z) := by
  obtain ⟨sa, hsa, hca⟩ := ha
  obtain ⟨sb, hsb, hcb⟩ := hb
  exact ⟨fun z => sa z ++ sb z, hsa.append hsb, fun z => (hca z).append (hcb z)⟩

/-- Reindexing along a poly-fueled index map. -/
lemma RpnSpliceStream.comp {ts : ℕ → List ℕ} (h : RpnSpliceStream ts)
    {c : Nat.Partrec.Code} {f : ℕ → ℕ} (hf : PolyFueled c f) :
    RpnSpliceStream (fun z => ts (f z)) := by
  obtain ⟨s, hs, hc⟩ := h
  exact ⟨fun z => s (f z), hs.comp hf, fun z => hc (f z)⟩

/-- Variable-width concatenation: `cnt n` copies of a segment read on the paired index.
This is what the mesh product of `thm:ccee` needs, its width growing with the index. -/
lemma RpnSpliceStream.concatVar {seg : ℕ → List ℕ} (hseg : RpnSpliceStream seg)
    {ccnt : Nat.Partrec.Code} {cnt : ℕ → ℕ} (hcnt : PolyFueled ccnt cnt) :
    RpnSpliceStream (fun n =>
      (List.range (cnt n)).flatMap fun j => seg (Nat.pair n j)) := by
  obtain ⟨s, hs, hc⟩ := hseg
  refine ⟨fun n => (List.range (cnt n)).flatMap fun j => s (Nat.pair n j),
    PolySegStream.concatVar hs hcnt, fun n => ?_⟩
  have key : ∀ m : ℕ, UnRpnContractsTo
      ((List.range m).flatMap fun j => s (Nat.pair n j))
      ((List.range m).flatMap fun j => seg (Nat.pair n j)) := by
    intro m
    induction m with
    | zero => intro rest; simp
    | succ m ih =>
        rw [List.range_succ, List.flatMap_append, List.flatMap_append]
        simpa using ih.append (hc (Nat.pair n m))
  exact key (cnt n)

/-- A spliced trade frame on a sentence sequence: target `[6, ⌜φ (f m)⌝]`. -/
lemma RpnSpliceStream.tradeSlot {φ : ℕ → Sentence} (hφ : RpnSentenceCodes φ)
    {c : Nat.Partrec.Code} {f : ℕ → ℕ} (hf : PolyFueled c f) :
    RpnSpliceStream (fun m => [6, Encodable.encode (φ (f m))]) := by
  obtain ⟨s, hs, hp⟩ := hφ
  have h6 : PolySegStream (fun _ : ℕ => [6]) :=
    PolySegStream.ofTokenStream (PolyTokenStream.const 6)
  exact ⟨fun m => 6 :: s (f m), (h6.append (hs.comp hf)).of_eq (fun m => by simp),
    fun m => UnRpnContractsTo.tradeChunk (hp (f m))⟩

/-- Two-way dispatch of spliceable streams along a poly-fueled test. -/
lemma RpnSpliceStream.ifZero {s₀ s₁ : ℕ → List ℕ}
    (h₀ : RpnSpliceStream s₀) (h₁ : RpnSpliceStream s₁)
    {ct : Nat.Partrec.Code} {t : ℕ → ℕ} (ht : PolyFueled ct t) :
    RpnSpliceStream (fun z => if t z = 0 then s₀ z else s₁ z) := by
  obtain ⟨a, ha, hca⟩ := h₀
  obtain ⟨b, hb, hcb⟩ := h₁
  refine ⟨fun z => if t z = 0 then a z else b z,
    PolySegStream.ifZero ha hb ht, fun z => ?_⟩
  by_cases hz : t z = 0
  · simpa [hz] using hca z
  · simpa [hz] using hcb z

/-- Transport along a pointwise equality of token streams. -/
lemma RpnSpliceStream.of_eq {a b : ℕ → List ℕ} (h : RpnSpliceStream a)
    (hab : ∀ z, a z = b z) : RpnSpliceStream b := by
  obtain ⟨s, hs, hc⟩ := h
  exact ⟨s, hs, fun z => (hab z) ▸ hc z⟩

/-! ### Serialization combinator mirrors

One-for-one mirrors of the `PolySegStream.serialize_*` closure suite: an emission
assembly written against that suite transfers by renaming combinators.  Operator tails
and payload frames are transparent; only sentence slots differ.

The suite is complete by construction — every `EF` constructor has a member here — and
completeness is the contract, so a member is kept even where nothing in the library
currently calls it. -/

/-- A bare operator/close token as a spliceable stream. -/
lemma RpnSpliceStream.tag (t : ℕ) (ht : t ≠ 0 ∧ t ≠ 1 ∧ t ≠ 6 ∧ t ≠ 7) :
    RpnSpliceStream (fun _ => [t]) :=
  .ofTransparent (PolySegStream.ofTokenStream (PolyTokenStream.const t))
    (fun _ => UnRpnTransparent.single t ht)

/-- A payload chunk (`1`/`7` tag with a poly-fueled payload) as a spliceable stream. -/
lemma RpnSpliceStream.payload (t : ℕ) (ht : t = 1 ∨ t = 7)
    {c : Nat.Partrec.Code} {f : ℕ → ℕ} (hf : PolyFueled c f) :
    RpnSpliceStream (fun z => [t, f z]) :=
  .ofTransparent (PolySegStream.ofTokenStream
      ((PolyTokenStream.const t).append (PolyTokenStream.polyTok hf)))
    (fun z => UnRpnTransparent.payload t (f z) ht)

lemma RpnSpliceStream.serialize_const (q : ℚ) :
    RpnSpliceStream (fun _ => (EF.const q).serialize) :=
  RpnSpliceStream.payload 1 (Or.inl rfl)
    (PolyFueled.const (Encodable.encode q))

lemma RpnSpliceStream.serialize_const_comp {q : ℕ → ℚ}
    (hq : ∃ c, PolyFueled c (fun z => Encodable.encode (q z))) :
    RpnSpliceStream (fun z => (EF.const (q z)).serialize) := by
  obtain ⟨c, hc⟩ := hq
  exact RpnSpliceStream.payload 1 (Or.inl rfl) hc

lemma RpnSpliceStream.serialize_add {A B : ℕ → EF}
    (hA : RpnSpliceStream (fun z => (A z).serialize))
    (hB : RpnSpliceStream (fun z => (B z).serialize)) :
    RpnSpliceStream (fun z => (EF.add (A z) (B z)).serialize) :=
  ((hA.append hB).append (RpnSpliceStream.tag 2 (by norm_num))).of_eq
    (fun z => by simp [EF.serialize])

lemma RpnSpliceStream.serialize_mul {A B : ℕ → EF}
    (hA : RpnSpliceStream (fun z => (A z).serialize))
    (hB : RpnSpliceStream (fun z => (B z).serialize)) :
    RpnSpliceStream (fun z => (EF.mul (A z) (B z)).serialize) :=
  ((hA.append hB).append (RpnSpliceStream.tag 3 (by norm_num))).of_eq
    (fun z => by simp [EF.serialize])

lemma RpnSpliceStream.serialize_max {A B : ℕ → EF}
    (hA : RpnSpliceStream (fun z => (A z).serialize))
    (hB : RpnSpliceStream (fun z => (B z).serialize)) :
    RpnSpliceStream (fun z => (EF.max (A z) (B z)).serialize) :=
  ((hA.append hB).append (RpnSpliceStream.tag 4 (by norm_num))).of_eq
    (fun z => by simp [EF.serialize])

lemma RpnSpliceStream.serialize_safeRecip {A : ℕ → EF}
    (hA : RpnSpliceStream (fun z => (A z).serialize)) :
    RpnSpliceStream (fun z => (EF.safeRecip (A z)).serialize) :=
  (hA.append (RpnSpliceStream.tag 5 (by norm_num))).of_eq
    (fun z => by simp [EF.serialize])

lemma RpnSpliceStream.serialize_var {f : ℕ → ℕ} {cf : Nat.Partrec.Code}
    (hf : PolyFueled cf f) :
    RpnSpliceStream (fun z => (EF.var (f z)).serialize) :=
  RpnSpliceStream.payload 7 (Or.inr rfl) hf

lemma RpnSpliceStream.serialize_letE {X Body : ℕ → EF}
    (hX : RpnSpliceStream (fun z => (X z).serialize))
    (hBody : RpnSpliceStream (fun z => (Body z).serialize)) :
    RpnSpliceStream (fun z => (EF.letE (X z) (Body z)).serialize) :=
  ((hX.append hBody).append (RpnSpliceStream.tag 8 (by norm_num))).of_eq
    (fun z => by simp [EF.serialize])

/-- A replicated close/operator tag as a spliceable stream. -/
lemma RpnSpliceStream.repeatTag (t : ℕ) (ht : t ≠ 0 ∧ t ≠ 1 ∧ t ≠ 6 ∧ t ≠ 7)
    {ccnt : Nat.Partrec.Code} {cnt : ℕ → ℕ} (hcnt : PolyFueled ccnt cnt) :
    RpnSpliceStream (fun n => List.replicate (cnt n) t) := by
  have key : ∀ m : ℕ, UnRpnTransparent (List.replicate m t) := by
    intro m
    induction m with
    | zero => exact UnRpnTransparent.nil
    | succ m ih =>
        rw [List.replicate_succ,
          show t :: List.replicate m t = [t] ++ List.replicate m t from rfl]
        exact (UnRpnTransparent.single t ht).append ih
  exact .ofTransparent (PolySegStream.repeatTag t hcnt) (fun n => key (cnt n))

/-- A spliced varying price leaf: sentence slot from the block stream, day from a
poly-fueled index. -/
lemma RpnSpliceStream.serialize_price {φ : ℕ → Sentence} (hφ : RpnSentenceCodes φ)
    {cs cd : Nat.Partrec.Code} {sf df : ℕ → ℕ}
    (hs : PolyFueled cs sf) (hd : PolyFueled cd df) :
    RpnSpliceStream (fun z => (EF.price (φ (sf z)) (df z)).serialize) := by
  obtain ⟨s, hstream, hp⟩ := hφ
  refine ⟨fun z => 0 :: s (sf z) ++ [df z], ?_, fun z => ?_⟩
  · exact priceSlotSeg hstream hs hd
  · have := UnRpnContractsTo.priceChunk (hp (sf z)) (df z)
    exact fun rest => by
      have h1 := this rest
      simpa [EF.serialize] using h1

/-- A transparent whole-serialization for price-free features. -/
lemma RpnSpliceStream.ofPriceFree {A : ℕ → EF}
    (h : PolySegStream (fun z => (A z).serialize))
    (hfree : ∀ z, (A z).priceFree) :
    RpnSpliceStream (fun z => (A z).serialize) :=
  .ofTransparent h (fun z => EF.serialize_unRpnTransparent (A z) (hfree z))

end LogicalInduction
