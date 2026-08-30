/-
# Write-out emission: token streams whose token *values* may be exponential

The paper's efficiently computable sequences are polynomial-time **write-out** objects:
the machine prints a serialization whose *length* is polynomial in the day.  Nothing
bounds the numeric value of what is printed — `δ n = 2⁻ⁿ`, an `n`-bit source string, and
the Gödel code of a sentence naming an `n`-bit machine are all polynomial to write and
all exponential in value.

`PolySegStream` (`Framework/Computable.lean`) meters the wrong thing for that purpose: it
asks for a poly-fueled per-*token* emitter, so each token's numeric value is polynomial in
the day.  The criterion the traders are judged against is already write-out metered —
`EfficientlyComputableDigit` meters base-4 digits and `undigitize` reassembles tokens of
any size — so the restriction lives only in the certificate layer, not in the notion of
efficiency.

This file supplies the missing certificate layer.  `BigTokenStream t` says: some
`PolySegStream` of *digits* undigitizes to `t`, block by block.  A token of value `v`
costs `len4 v + 1` digits, so an exponential token is a polynomially long digit run, and
`BigDigits` (`Framework/DigitArith.lean`) is exactly the certificate that emits one.
Because `undigitize` distributes over concatenation at block boundaries
(`TokenFold.undigitize_append_of_complete`) and `digitize` is a `flatMap` homomorphism,
every `PolySegStream` combinator transports to `BigTokenStream` mechanically; the classes
built on top — `BigSentenceCodes` and `BigSpliceStream` — are then combinator-for-
combinator mirrors of `RpnSentenceCodes` and `RpnSpliceStream`, and the capstone
`BigSpliceStream.ec` lands in the same `EfficientlyComputable`.

The value-bounded classes are *not* wrong where they are used as fuel certificates: the
fuel model is unit-cost arithmetic, so a poly-fuel run genuinely does produce a
poly-*value* output, and dropping `IsPolyBounded` from `PolyFueled` would certify
repeated squaring.  The error is only in applying that certificate shape to write-out
data, and this layer is the repair.

Paper node: `def:ec`
-/
import LogicalInduction.Framework.RpnEmission
import LogicalInduction.Framework.Machine.TokenFold
import LogicalInduction.Framework.CodeSource

namespace LogicalInduction

open Nat.Partrec (Code)

-- Deep `PolyFueled` compositions over paired inputs loop `whnf` on `Nat.sqrt`; keep it
-- opaque throughout (the standard `dd:fuel` safeguard).
attribute [local irreducible] Nat.sqrt

/-! ## `BigTokenStream` — the write-out analogue of `PolySegStream` -/

/-- **A polynomially written-out token stream.**  Some `PolySegStream` of base-4 digits
undigitizes to `t n`, ending on a block boundary.  The digit stream is what the emitter
is metered on, so `t n` may carry tokens whose *values* are exponential in `n` while the
certificate stays polynomial.  Compare `PolySegStream`, which meters token values.
Paper node: `def:ec` -/
def BigTokenStream (t : ℕ → List ℕ) : Prop :=
  ∃ ds : ℕ → List ℕ, PolySegStream ds ∧ (∀ n, (blockSplit (ds n)).2 = []) ∧
    ∀ n, undigitize (ds n) = t n

namespace BigTokenStream

lemma of_eq {a b : ℕ → List ℕ} (h : BigTokenStream a) (he : ∀ n, a n = b n) :
    BigTokenStream b := by
  rwa [funext he] at h

/-- **The inclusion**: every value-metered stream is written out, by digitizing it.  This
is what makes the upgrade a class swap rather than a rewrite — every existing
`PolySegStream` construction lifts unchanged. -/
lemma ofPolySegStream {t : ℕ → List ℕ} (h : PolySegStream t) : BigTokenStream t :=
  ⟨fun n => digitize (t n), h.digitizeStream,
    fun n => TokenFold.blockSplit_digitize (t n), fun n => undigitize_digitize (t n)⟩

/-- **The write-out base case**: one token of arbitrary magnitude, given poly-fueled
digit access to it.  This is the step `PolySegStream` cannot take — `BigDigits.blockSeg`
emits the value's self-delimiting digit block in `len4 (x n) + 1` polynomial steps
without ever materializing `x n`. -/
lemma ofBigDigits {x : ℕ → ℕ} (h : BigDigits x) : BigTokenStream (fun n => [x n]) :=
  ⟨fun n => tokenBlock (x n), h.blockSeg,
    fun n => (TokenFold.undigitize_run_terminator (natDigits4 (x n))
      (natDigits4_lt (x n))).2,
    fun n => (TokenFold.undigitize_run_terminator (natDigits4 (x n))
      (natDigits4_lt (x n))).1.trans (by rw [TokenFold.digitVal_natDigits4])⟩

lemma append {a b : ℕ → List ℕ} (ha : BigTokenStream a) (hb : BigTokenStream b) :
    BigTokenStream (fun n => a n ++ b n) := by
  obtain ⟨da, hda, hca, hua⟩ := ha
  obtain ⟨db, hdb, hcb, hub⟩ := hb
  refine ⟨fun n => da n ++ db n, hda.append hdb, fun n => ?_, fun n => ?_⟩
  · rw [TokenFold.blockSplit_append_of_complete _ _ (hca n)]; exact hcb n
  · rw [TokenFold.undigitize_append_of_complete _ _ (hca n), hua n, hub n]

lemma comp {t : ℕ → List ℕ} (h : BigTokenStream t) {c : Code} {f : ℕ → ℕ}
    (hf : PolyFueled c f) : BigTokenStream (fun n => t (f n)) := by
  obtain ⟨ds, hds, hc, hu⟩ := h
  exact ⟨fun n => ds (f n), hds.comp hf, fun n => hc (f n), fun n => hu (f n)⟩

lemma ifZero {s₀ s₁ : ℕ → List ℕ} (h₀ : BigTokenStream s₀) (h₁ : BigTokenStream s₁)
    {ct : Code} {tf : ℕ → ℕ} (ht : PolyFueled ct tf) :
    BigTokenStream (fun z => if tf z = 0 then s₀ z else s₁ z) := by
  obtain ⟨a, ha, hca, hua⟩ := h₀
  obtain ⟨b, hb, hcb, hub⟩ := h₁
  refine ⟨fun z => if tf z = 0 then a z else b z, PolySegStream.ifZero ha hb ht,
    fun z => ?_, fun z => ?_⟩
  · by_cases hz : tf z = 0
    · simpa [hz] using hca z
    · simpa [hz] using hcb z
  · by_cases hz : tf z = 0
    · simpa [hz] using hua z
    · simpa [hz] using hub z

/-- Undigitizing a concatenation of complete digit runs is the concatenation of their
decodes — the `flatMap` form of `TokenFold.undigitize_append_of_complete`, which is what
lets variable-width concatenation transport. -/
private lemma undigitize_flatMap_complete {ι : Type} (f : ι → List ℕ) :
    ∀ l : List ι, (∀ j ∈ l, (blockSplit (f j)).2 = []) →
      undigitize (l.flatMap f) = l.flatMap (fun j => undigitize (f j)) ∧
        (blockSplit (l.flatMap f)).2 = []
  | [], _ => ⟨rfl, rfl⟩
  | j :: l, h => by
      have hj := h j (List.mem_cons_self)
      have ih := undigitize_flatMap_complete f l
        (fun k hk => h k (List.mem_cons_of_mem _ hk))
      rw [List.flatMap_cons, List.flatMap_cons]
      exact ⟨by rw [TokenFold.undigitize_append_of_complete _ _ hj, ih.1],
        by rw [TokenFold.blockSplit_append_of_complete _ _ hj]; exact ih.2⟩

/-- **Variable-width concatenation**: `cnt n` written-out segments, indexed by
`Nat.pair n j`.  The digit-level certificate is `PolySegStream.concatVar` verbatim; only
the decode step is new. -/
lemma concatVar {seg : ℕ → List ℕ} (hseg : BigTokenStream seg) {ccnt : Code}
    {cnt : ℕ → ℕ} (hcnt : PolyFueled ccnt cnt) :
    BigTokenStream (fun n => (List.range (cnt n)).flatMap fun j => seg (Nat.pair n j)) := by
  obtain ⟨ds, hds, hc, hu⟩ := hseg
  refine ⟨fun n => (List.range (cnt n)).flatMap fun j => ds (Nat.pair n j),
    hds.concatVar hcnt, fun n => ?_, fun n => ?_⟩
  · exact (undigitize_flatMap_complete (fun j => ds (Nat.pair n j)) _
      (fun j _ => hc (Nat.pair n j))).2
  · rw [(undigitize_flatMap_complete (fun j => ds (Nat.pair n j)) _
      (fun j _ => hc (Nat.pair n j))).1]
    exact List.flatMap_congr (fun j _ => by rw [hu (Nat.pair n j)])

end BigTokenStream

/-- **The write-out capstone**: a written-out token stream whose contracted decode is the
target trader realizes an `EfficientlyComputable` certificate.  The digit stream is
handed straight to `ec_of_rawSegStream`, so nothing about the emission pipeline changes —
only the metering of the stream that feeds it.
Paper node: `def:ec` -/
lemma ec_of_bigTokenStream (Tr : Trader) {t : ℕ → List ℕ} (h : BigTokenStream t)
    (hstrategy : ∀ n, strategyOfTokens n (unRpn (t n)) = Tr.strat n) :
    EfficientlyComputable Tr := by
  obtain ⟨ds, hds, -, hu⟩ := h
  exact ec_of_rawSegStream Tr hds (fun n => by rw [hu n]; exact hstrategy n)

/-! ## The write-out sentence class

`BigSentenceCodes` is `RpnSentenceCodes` with its inner `PolySegStream` replaced by
`BigTokenStream`.  The whole point is `ofBigDigits`: a sentence whose Gödel code is
exponential in the day — the halting claim about an `n`-bit machine, say — reaches the
stream as a two-token escape block whose payload is written out digit by digit. -/

/-- A written-out token stream is primitive recursive: its digit stream is
(`PolySegStream.primrec`) and `undigitize` is. -/
lemma BigTokenStream.primrec {t : ℕ → List ℕ} (h : BigTokenStream t) : Primrec t := by
  obtain ⟨ds, hds, _, heq⟩ := h
  exact (undigitize_prim.comp hds.primrec).of_eq heq

/-- **The paper's 𝓔𝓒 sentence-sequence class, write-out metered.**  A written-out stream
of self-delimiting sentence blocks parsing to the sequence, each block consumed exactly.
Contrast `RpnSentenceCodes`, which additionally bounds every emitted *token's* value by a
polynomial in the day.  That is **not** a bound on the sentences' Gödel codes:
`RpnSentenceCodes.ofCanonical` admits a family whose codes are exponential, provided each
sentence is spelled as a polynomially long run of small Polish symbols.  What the token
bound excludes is a family whose block needs a single *unbounded* token — the escape block
`[1, ⌜φ n⌝]` of `ofPolySentenceCodes` at an exponential `⌜φ n⌝`, which only
`ofDigitSentenceCodes` can emit.  No separation of the two sentence classes is proved here;
the proved separations are at `BigDigits`, `BigTokenStream` and `DigitRatCodes` (see
`## Strictness` below).
Paper node: `def:ec` -/
def BigSentenceCodes (φ : ℕ → Sentence) : Prop :=
  ∃ s : ℕ → List ℕ, BigTokenStream s ∧
    ∀ n, parseRpn (s n).length (s n) = some (φ n, [])

namespace BigSentenceCodes

/-- Every value-metered certificate is a write-out certificate. -/
lemma ofRpnSentenceCodes {φ : ℕ → Sentence} (h : RpnSentenceCodes φ) :
    BigSentenceCodes φ := by
  obtain ⟨s, hs, hp⟩ := h
  exact ⟨s, BigTokenStream.ofPolySegStream hs, hp⟩

/-- A written-out canonical Polish stream instantiates the class.  The write-out mirror of
`RpnSentenceCodes.ofCanonical`: the symbol count is polynomial, and now individual symbols
may carry exponential values. -/
lemma ofCanonical {φ : ℕ → Sentence}
    (h : BigTokenStream fun n => rpn (φ n)) : BigSentenceCodes φ :=
  ⟨_, h, fun n => by
    simpa using parseRpn_rpn (φ n) [] (le_refl (rpn (φ n)).length)⟩

/-- A value-bounded code sequence, in one step.  Composition of `ofRpnSentenceCodes` with
`RpnSentenceCodes.ofPolySentenceCodes`; kept so a consumer holding the old certificate need
not name both adapters. -/
lemma ofPolySentenceCodes {φ : ℕ → Sentence} (h : PolySentenceCodes φ) :
    BigSentenceCodes φ :=
  ofRpnSentenceCodes (RpnSentenceCodes.ofPolySentenceCodes h)

/-- **The point of the layer.**  Poly-fueled *digit* access to the sequence's Gödel codes
— `DigitSentenceCodes`, which places no bound on the codes themselves — certifies the
sentence sequence, by the two-token escape block.  `RpnSentenceCodes.ofPolySentenceCodes`
is the same construction under a polynomial bound on the code. -/
lemma ofDigitSentenceCodes {φ : ℕ → Sentence} (h : DigitSentenceCodes φ) :
    BigSentenceCodes φ := by
  refine ⟨fun n => [1, Encodable.encode (φ n)], ?_,
    fun n => parseRpn_escape (φ n) [] (by norm_num)⟩
  exact ((BigTokenStream.ofPolySegStream
    (PolySegStream.ofTokenStream (PolyTokenStream.const 1))).append
      (BigTokenStream.ofBigDigits h)).of_eq (fun _ => rfl)

lemma of_eq {φ ψ : ℕ → Sentence} (h : BigSentenceCodes φ) (hφψ : ∀ n, φ n = ψ n) :
    BigSentenceCodes ψ := by
  obtain ⟨s, hs, hp⟩ := h
  exact ⟨s, hs, fun n => (hφψ n) ▸ hp n⟩

lemma comp {φ : ℕ → Sentence} (h : BigSentenceCodes φ) {c : Code} {f : ℕ → ℕ}
    (hf : PolyFueled c f) : BigSentenceCodes (fun z => φ (f z)) := by
  obtain ⟨s, hs, hp⟩ := h
  exact ⟨fun z => s (f z), hs.comp hf, fun z => hp (f z)⟩

lemma const (φ : Sentence) : BigSentenceCodes (fun _ => φ) :=
  ofRpnSentenceCodes (RpnSentenceCodes.const φ)

/-- Two-way dispatch of sentence-block streams along a poly-fueled test. -/
lemma ifZero {φ ψ : ℕ → Sentence} (hφ : BigSentenceCodes φ) (hψ : BigSentenceCodes ψ)
    {c : Code} {t : ℕ → ℕ} (ht : PolyFueled c t) :
    BigSentenceCodes (fun z => if t z = 0 then φ z else ψ z) := by
  obtain ⟨a, ha, hpa⟩ := hφ
  obtain ⟨b, hb, hpb⟩ := hψ
  refine ⟨fun z => if t z = 0 then a z else b z, ha.ifZero hb ht, fun z => ?_⟩
  by_cases hz : t z = 0
  · simpa [hz] using hpa z
  · simpa [hz] using hpb z

/-- Conjunction of two written-out sentence streams: the fixed `⋏` tag in front of the
two blocks, which the prefix parser consumes in order.  The parse argument is
`RpnSentenceCodes.and`'s verbatim; only the stream certificate changes. -/
lemma and {φ ψ : ℕ → Sentence} (hφ : BigSentenceCodes φ) (hψ : BigSentenceCodes ψ) :
    BigSentenceCodes (fun z => φ z ⋏ ψ z) := by
  obtain ⟨a, ha, hpa⟩ := hφ
  obtain ⟨b, hb, hpb⟩ := hψ
  have h3 : BigTokenStream (fun _ : ℕ => [3]) :=
    BigTokenStream.ofPolySegStream (PolySegStream.ofTokenStream (PolyTokenStream.const 3))
  refine ⟨fun z => 3 :: (a z ++ b z),
    ((h3.append ha).append hb).of_eq (fun z => by simp), fun z => ?_⟩
  have hlen : (3 :: (a z ++ b z)).length = (a z).length + (b z).length + 1 := by
    simp
  rw [hlen, parseRpn_cons]
  rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]
  rw [parseRpn_block_head (hpa z) (b z) (by omega)]
  simp only [Option.bind_some]
  rw [parseRpn_mono (b z) (show (b z).length ≤ (a z).length + (b z).length by omega)
    (hpb z)]
  rfl

/-- Negation of a written-out sentence stream: the fixed `🡒` tag in front of the block and
a constant `⊥` block, which the prefix parser consumes in order.  Foundation spells `∼φ`
as `φ 🡒 ⊥` definitionally, and `rpn` tags an implication with `2`, so this is `and`'s
argument at tag `2` with `const ⊥` as the second stream. -/
lemma neg {φ : ℕ → Sentence} (hφ : BigSentenceCodes φ) :
    BigSentenceCodes (fun z => ∼(φ z)) := by
  obtain ⟨a, ha, hpa⟩ := hφ
  obtain ⟨b, hb, hpb⟩ := BigSentenceCodes.const (⊥ : Sentence)
  have h2 : BigTokenStream (fun _ : ℕ => [2]) :=
    BigTokenStream.ofPolySegStream (PolySegStream.ofTokenStream (PolyTokenStream.const 2))
  refine ⟨fun z => 2 :: (a z ++ b z),
    ((h2.append ha).append hb).of_eq (fun z => by simp), fun z => ?_⟩
  have hlen : (2 :: (a z ++ b z)).length = (a z).length + (b z).length + 1 := by simp
  rw [hlen, parseRpn_cons]
  rw [if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]
  rw [parseRpn_block_head (hpa z) (b z) (by omega)]
  simp only [Option.bind_some]
  rw [parseRpn_mono (b z) (show (b z).length ≤ (a z).length + (b z).length by omega)
    (hpb z)]
  rfl

end BigSentenceCodes

/-! ## The write-out splice class

`BigSpliceStream` is `RpnSpliceStream` with its inner `PolySegStream` replaced by
`BigTokenStream`; the combinator suite below is a one-for-one mirror, so an emission
assembly written against `RpnSpliceStream` transfers by renaming combinators.  The one
genuinely new constructor is `bigPayload`, which splices a payload token the emitter
knows only through its digits. -/

/-- Some written-out stream contracts to `ts` position-wise. -/
def BigSpliceStream (ts : ℕ → List ℕ) : Prop :=
  ∃ s : ℕ → List ℕ, BigTokenStream s ∧ ∀ z, UnRpnContractsTo (s z) (ts z)

namespace BigSpliceStream

lemma ofRpnSpliceStream {ts : ℕ → List ℕ} (h : RpnSpliceStream ts) :
    BigSpliceStream ts := by
  obtain ⟨s, hs, hc⟩ := h
  exact ⟨s, BigTokenStream.ofPolySegStream hs, hc⟩

lemma ofTransparent {ts : ℕ → List ℕ} (h : BigTokenStream ts)
    (ht : ∀ z, UnRpnTransparent (ts z)) : BigSpliceStream ts :=
  ⟨ts, h, fun z => (ht z).contractsTo⟩

lemma of_eq {a b : ℕ → List ℕ} (h : BigSpliceStream a) (hab : ∀ z, a z = b z) :
    BigSpliceStream b := by
  obtain ⟨s, hs, hc⟩ := h
  exact ⟨s, hs, fun z => (hab z) ▸ hc z⟩

lemma append {a b : ℕ → List ℕ} (ha : BigSpliceStream a) (hb : BigSpliceStream b) :
    BigSpliceStream (fun z => a z ++ b z) := by
  obtain ⟨sa, hsa, hca⟩ := ha
  obtain ⟨sb, hsb, hcb⟩ := hb
  exact ⟨fun z => sa z ++ sb z, hsa.append hsb, fun z => (hca z).append (hcb z)⟩

lemma comp {ts : ℕ → List ℕ} (h : BigSpliceStream ts) {c : Code} {f : ℕ → ℕ}
    (hf : PolyFueled c f) : BigSpliceStream (fun z => ts (f z)) := by
  obtain ⟨s, hs, hc⟩ := h
  exact ⟨fun z => s (f z), hs.comp hf, fun z => hc (f z)⟩

lemma ifZero {s₀ s₁ : ℕ → List ℕ} (h₀ : BigSpliceStream s₀) (h₁ : BigSpliceStream s₁)
    {ct : Code} {t : ℕ → ℕ} (ht : PolyFueled ct t) :
    BigSpliceStream (fun z => if t z = 0 then s₀ z else s₁ z) := by
  obtain ⟨a, ha, hca⟩ := h₀
  obtain ⟨b, hb, hcb⟩ := h₁
  refine ⟨fun z => if t z = 0 then a z else b z, ha.ifZero hb ht, fun z => ?_⟩
  by_cases hz : t z = 0
  · simpa [hz] using hca z
  · simpa [hz] using hcb z

lemma concatVar {seg : ℕ → List ℕ} (hseg : BigSpliceStream seg) {ccnt : Code}
    {cnt : ℕ → ℕ} (hcnt : PolyFueled ccnt cnt) :
    BigSpliceStream (fun n =>
      (List.range (cnt n)).flatMap fun j => seg (Nat.pair n j)) := by
  obtain ⟨s, hs, hc⟩ := hseg
  refine ⟨fun n => (List.range (cnt n)).flatMap fun j => s (Nat.pair n j),
    hs.concatVar hcnt, fun n => ?_⟩
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

/-- A bare operator/close token as a spliceable stream. -/
lemma tag (t : ℕ) (ht : t ≠ 0 ∧ t ≠ 1 ∧ t ≠ 6 ∧ t ≠ 7) :
    BigSpliceStream (fun _ => [t]) :=
  ofRpnSpliceStream (RpnSpliceStream.tag t ht)

/-- **A written-out payload chunk**: a `1`/`7` tag whose payload token is known only
through its digits, so its value may be exponential in the day.  This is the constructor
`RpnSpliceStream.payload` cannot offer. -/
lemma bigPayload (t : ℕ) (ht : t = 1 ∨ t = 7) {f : ℕ → ℕ} (hf : BigDigits f) :
    BigSpliceStream (fun z => [t, f z]) :=
  ofTransparent
    (((BigTokenStream.ofPolySegStream
        (PolySegStream.ofTokenStream (PolyTokenStream.const t))).append
      (BigTokenStream.ofBigDigits hf)).of_eq (fun _ => rfl))
    (fun z => UnRpnTransparent.payload t (f z) ht)

/-- **A written-out sentence slot**: the price leaf `[0, ⌜φ (f m)⌝, f m]` on a written-out
sentence sequence. -/
lemma priceSlot {φ : ℕ → Sentence} (hφ : BigSentenceCodes φ) {c : Code} {f : ℕ → ℕ}
    (hf : PolyFueled c f) :
    BigSpliceStream (fun m => [0, Encodable.encode (φ (f m)), f m]) := by
  obtain ⟨s, hs, hp⟩ := hφ
  refine ⟨fun m => 0 :: s (f m) ++ [f m], ?_,
    fun m => UnRpnContractsTo.priceChunk (hp (f m)) (f m)⟩
  have h0 : BigTokenStream (fun _ : ℕ => [0]) :=
    BigTokenStream.ofPolySegStream (PolySegStream.ofTokenStream (PolyTokenStream.const 0))
  have hday : BigTokenStream (fun m => [f m]) :=
    BigTokenStream.ofPolySegStream
      (PolySegStream.ofTokenStream (PolyTokenStream.polyTok hf))
  exact ((h0.append (hs.comp hf)).append hday).of_eq (fun m => by simp)

/-- **A written-out trade frame**: `[6, ⌜φ (f m)⌝]` on a written-out sentence sequence. -/
lemma tradeSlot {φ : ℕ → Sentence} (hφ : BigSentenceCodes φ) {c : Code} {f : ℕ → ℕ}
    (hf : PolyFueled c f) :
    BigSpliceStream (fun m => [6, Encodable.encode (φ (f m))]) := by
  obtain ⟨s, hs, hp⟩ := hφ
  have h6 : BigTokenStream (fun _ : ℕ => [6]) :=
    BigTokenStream.ofPolySegStream (PolySegStream.ofTokenStream (PolyTokenStream.const 6))
  exact ⟨fun m => 6 :: s (f m), (h6.append (hs.comp hf)).of_eq (fun m => by simp),
    fun m => UnRpnContractsTo.tradeChunk (hp (f m))⟩

/-! ### Serialization combinator mirrors -/

lemma serialize_add {A B : ℕ → EF}
    (hA : BigSpliceStream (fun z => (A z).serialize))
    (hB : BigSpliceStream (fun z => (B z).serialize)) :
    BigSpliceStream (fun z => (EF.add (A z) (B z)).serialize) :=
  ((hA.append hB).append (tag 2 (by norm_num))).of_eq (fun z => by simp [EF.serialize])

lemma serialize_mul {A B : ℕ → EF}
    (hA : BigSpliceStream (fun z => (A z).serialize))
    (hB : BigSpliceStream (fun z => (B z).serialize)) :
    BigSpliceStream (fun z => (EF.mul (A z) (B z)).serialize) :=
  ((hA.append hB).append (tag 3 (by norm_num))).of_eq (fun z => by simp [EF.serialize])

lemma serialize_max {A B : ℕ → EF}
    (hA : BigSpliceStream (fun z => (A z).serialize))
    (hB : BigSpliceStream (fun z => (B z).serialize)) :
    BigSpliceStream (fun z => (EF.max (A z) (B z)).serialize) :=
  ((hA.append hB).append (tag 4 (by norm_num))).of_eq (fun z => by simp [EF.serialize])

/-- A *fixed* rational constant, lifted from the value-bounded stream: a constant costs
the same to write on every day, so no write-out generality is needed to emit it. -/
lemma serialize_const (q : ℚ) :
    BigSpliceStream (fun _ : ℕ => (EF.const q).serialize) :=
  ofRpnSpliceStream (RpnSpliceStream.serialize_const q)

/-- A value-bounded payload leaf, lifted.  `bigPayload` is the counterpart that admits
an exponentially-named datum; this one is for leaves that really are polynomial. -/
lemma payload (t : ℕ) (ht : t = 1 ∨ t = 7)
    {c : Code} {f : ℕ → ℕ} (hf : PolyFueled c f) :
    BigSpliceStream (fun z => [t, f z]) :=
  ofRpnSpliceStream (RpnSpliceStream.payload t ht hf)

/-- A rational constant with a poly-fueled code — the value-bounded case, kept so that a
consumer still holding a `PolyRatCodes` certificate need not convert it. -/
lemma serialize_const_comp {q : ℕ → ℚ}
    (hq : ∃ c, PolyFueled c (fun z => Encodable.encode (q z))) :
    BigSpliceStream (fun z => (EF.const (q z)).serialize) :=
  ofRpnSpliceStream (RpnSpliceStream.serialize_const_comp hq)

/-- **A written-out rational constant.**  The emitter knows `⌜q z⌝` only through its
digits, so `q z` may need exponentially many bits to name — `2⁻ᶻ` is the motivating
case, and `DigitRatCodes.toBigDigits` is where the hypothesis comes from.
`serialize_const_comp` is the value-bounded counterpart. -/
lemma serialize_const_write {q : ℕ → ℚ}
    (hq : BigDigits (fun z => Encodable.encode (q z))) :
    BigSpliceStream (fun z => (EF.const (q z)).serialize) :=
  (bigPayload 1 (Or.inl rfl) hq).of_eq (fun z => by simp [EF.serialize])

lemma serialize_var {f : ℕ → ℕ} {cf : Code} (hf : PolyFueled cf f) :
    BigSpliceStream (fun z => (EF.var (f z)).serialize) :=
  ofRpnSpliceStream (RpnSpliceStream.serialize_var hf)

lemma serialize_safeRecip {A : ℕ → EF}
    (hA : BigSpliceStream (fun z => (A z).serialize)) :
    BigSpliceStream (fun z => (EF.safeRecip (A z)).serialize) :=
  (hA.append (tag 5 (by norm_num))).of_eq (fun z => by simp [EF.serialize])

lemma serialize_letE {X Body : ℕ → EF}
    (hX : BigSpliceStream (fun z => (X z).serialize))
    (hBody : BigSpliceStream (fun z => (Body z).serialize)) :
    BigSpliceStream (fun z => (EF.letE (X z) (Body z)).serialize) :=
  ((hX.append hBody).append (tag 8 (by norm_num))).of_eq
    (fun z => by simp [EF.serialize])

/-- A replicated close/operator tag as a spliceable stream. -/
lemma repeatTag (t : ℕ) (ht : t ≠ 0 ∧ t ≠ 1 ∧ t ≠ 6 ∧ t ≠ 7) {ccnt : Code}
    {cnt : ℕ → ℕ} (hcnt : PolyFueled ccnt cnt) :
    BigSpliceStream (fun n => List.replicate (cnt n) t) :=
  ofRpnSpliceStream (RpnSpliceStream.repeatTag t ht hcnt)

/-- **A written-out varying price leaf**: sentence slot from a written-out block stream,
day from a poly-fueled index. -/
lemma serialize_price {φ : ℕ → Sentence} (hφ : BigSentenceCodes φ) {cs cd : Code}
    {sf df : ℕ → ℕ} (hs : PolyFueled cs sf) (hd : PolyFueled cd df) :
    BigSpliceStream (fun z => (EF.price (φ (sf z)) (df z)).serialize) := by
  obtain ⟨s, hstream, hp⟩ := hφ
  refine ⟨fun z => 0 :: s (sf z) ++ [df z], ?_, fun z => ?_⟩
  · have h0 : BigTokenStream (fun _ : ℕ => [0]) :=
      BigTokenStream.ofPolySegStream (PolySegStream.ofTokenStream (PolyTokenStream.const 0))
    have hdSeg : BigTokenStream (fun z : ℕ => [df z]) :=
      BigTokenStream.ofPolySegStream
        (PolySegStream.ofTokenStream (PolyTokenStream.polyTok hd))
    exact ((h0.append (hstream.comp hs)).append hdSeg).of_eq fun z => by simp
  · have hcontract := UnRpnContractsTo.priceChunk (hp (sf z)) (df z)
    exact fun rest => by simpa [EF.serialize] using hcontract rest

/-- A transparent whole-serialization for price-free features. -/
lemma ofPriceFree {A : ℕ → EF} (h : BigTokenStream (fun z => (A z).serialize))
    (hfree : ∀ z, (A z).priceFree) :
    BigSpliceStream (fun z => (A z).serialize) :=
  ofTransparent h (fun z => EF.serialize_unRpnTransparent (A z) (hfree z))

end BigSpliceStream

/-- Write-out mirror of `RpnSentenceCodes.modDispatch`: a `k`-way dispatch on `z % k`
between finitely many written-out sentence families.  Same induction as the value-bounded
version, with `BigSentenceCodes.ifZero` doing the branching. -/
lemma BigSentenceCodes.modDispatch {k : ℕ} (hk : 0 < k) {φ : ℕ → ℕ → Sentence}
    (hφ : ∀ j < k, BigSentenceCodes (φ j)) :
    BigSentenceCodes (fun z => φ (z.unpair.2 % k) z.unpair.1) := by
  obtain ⟨cdm, hdm⟩ := divmodc_polyFueled k hk
  obtain ⟨cadd, hadd⟩ := addc_polyFueled
  have hrem : PolyFueled _ (fun z : ℕ => z.unpair.2 % k) :=
    (PolyFueled.right.comp (hdm.comp PolyFueled.right)).of_eq (fun z => by
      simp)
  have hleft := PolyFueled.left
  have H : ∀ m, m ≤ k → BigSentenceCodes (fun z =>
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
        refine (BigSentenceCodes.ifZero ((hφ m hmk).comp hleft)
          (ih (le_of_lt hm)) htest).of_eq (fun z => ?_)
        by_cases heq : z.unpair.2 % k = m
        · rw [if_pos (by omega), if_pos (by omega), heq]
        · rw [if_neg (by omega)]
          by_cases hlt : z.unpair.2 % k < m + 1
          · rw [if_pos hlt, if_pos (by omega)]
          · rw [if_neg hlt, if_neg (by omega)]
  exact (H k le_rfl).of_eq (fun z => by
    rw [if_pos (Nat.mod_lt z.unpair.2 hk)])

/-- **The write-out realization theorem**: a trader whose per-day trade serialization is
written-out spliceable is efficiently computable.  The mirror of `RpnSpliceStream.ec`,
with no polynomial bound on any emitted token's value.
Paper node: `def:ec` -/
lemma BigSpliceStream.ec (Tr : Trader)
    (h : BigSpliceStream (fun n => serializeTrades (Tr.strat n).trades)) :
    EfficientlyComputable Tr := by
  obtain ⟨s, hs, hc⟩ := h
  refine ec_of_bigTokenStream Tr hs (fun n => ?_)
  have hun : unRpn (s n) = serializeTrades (Tr.strat n).trades := by
    have h0 := (hc n).unRpn_eq
    rw [show unRpn ([] : List ℕ) = [] from rfl, List.append_nil] at h0
    exact h0
  rw [hun]
  have hdecode := deserializeTrades_serializeTrades (Tr.strat n).trades
  cases hS : Tr.strat n with
  | mk trades rank_le =>
      simp only [strategyOfTokens]
      rw [hS] at hdecode
      split
      · next hnone =>
          rw [hdecode] at hnone; exact absurd hnone (by simp)
      · next trades' hsome =>
          rw [hdecode] at hsome
          obtain rfl := Option.some.inj hsome
          rw [dif_pos rank_le]

/-- Write-out mirror of `EfficientlyComputable.ofSingleTradeBlocks`: a trader whose day-`n`
strategy is the single trade `(f n, φ n)`, with a price-free coefficient stream and a
*written-out* sentence family, is efficiently computable.  The value-bounded entry point
cannot take an exponentially-named sentence; this one can.
Paper node: `def:ec` -/
lemma EfficientlyComputable.ofSingleTradeBlocksBig (Tr : Trader) (f : ℕ → EF)
    (φ : ℕ → Sentence)
    (hf : PolySegStream fun n => (f n).serialize)
    (hfree : ∀ n, (f n).priceFree)
    (hφ : BigSentenceCodes φ)
    (hTr : ∀ n, (Tr.strat n).trades = [(f n, φ n)]) :
    EfficientlyComputable Tr := by
  have hfB : BigSpliceStream (fun n => (f n).serialize) :=
    BigSpliceStream.ofPriceFree (BigTokenStream.ofPolySegStream hf) hfree
  have hslot : BigSpliceStream (fun n => [6, Encodable.encode (φ n)]) :=
    (BigSpliceStream.tradeSlot hφ PolyFueled.id).of_eq (fun _ => rfl)
  refine BigSpliceStream.ec Tr ((hfB.append hslot).of_eq (fun n => ?_))
  rw [hTr n]
  simp [serializeTrades]


/-! ## The write-out sequence classes for values

The natural-number write-out class is `BigDigits` itself, and needs no new name.  Machine
codes and rationals do: the former because the class is about the *code* of a machine, the
latter because a flat `BigDigits` on `⌜q n⌝` would make the reciprocal a bignum `unpair`,
hence a bignum `Nat.sqrt`, which the digit calculus provably does not close under. -/

/-- **The write-out class for machine codes.**  Poly-fueled digit access to the machine's
*source* number — no polynomial bound on that number itself, so a machine whose description
grows linearly in the day (an `O(n)`-symbol source, the paper's own example at tex:1931-1933)
qualifies.

**Representation choice** (disclosed, in the same spirit as RPN for sentences).  Machines are
`Nat.Partrec.Code`, exactly as elsewhere in this development; what is chosen here is how a
machine is *named*.  The name is `Code.sourceNat` (`Framework/CodeSource.lean`): the postfix
tag stream of the syntax tree read base-16, whose symbol count is linear in the tree
(`len4_sourceNat_le`).  That is what tex:1931-1933 asks of `⟨m⟩` — the source must be
writable in time polynomial in the day.

Decoding is by the total primitive recursive `ofSource` (`ofSource_primrec`), which inverts
the naming map (`ofSource_sourceNat`).  Its cost is metered in peel steps, one per base-4
digit of the name — exactly `len4 n` of them (`ofSource_peelSteps`), hence at most `2 * size`
for a machine name (`sourceNat_peelSteps_le`): **linear in the source length**.  That is the
whole cost claim; no `PolyFueled` or `Complexity.FP` certificate is proved for `ofSource`.

Mathlib's `Encodable.encode` on `Nat.Partrec.Code` fails this and is deliberately **not** the
naming map.  `encodeCode` is `2 * (2 * Nat.pair (encode cf) (encode cg)) + 4` at every
`pair`/`comp`/`prec` node, so the code *value* squares per node.  For the family
`nest 0 = zero`, `nest (n+1) = pair (nest n) zero` — `2n + 1` syntax nodes — the encoded
**value** is therefore doubly exponential in the day, and its base-4 **digit count**, which
merely doubles per node, is `0, 2, 4, 8, 16, 33, 67, 134, …`: exponential in the day and in
the tree size, against the *linear* `sourceNat` source length (`len4_sourceNat_le`).  Under
`encode`-naming that paper-admissible family would be excluded from this class; under
`sourceNat` it is admitted (`Nat.Partrec.Code.bigDigits_sourceNat_nest`), and
`digitMachineCodes_nest_not_polyMachineCodes` is the witness that the admission is strict.
Paper node: `def:ec` -/
def DigitMachineCodes (m : ℕ → Nat.Partrec.Code) : Prop :=
  BigDigits (fun n => Nat.Partrec.Code.sourceNat (m n))

/-- **The write-out class for rationals**, carried as *separate digit runs* for the
numerator and the denominator rather than as one run for `⌜q n⌝`.

The split is forced by the reciprocal.  `encode_rat_inv_of_pos` shows that inverting a
positive rational swaps the two components of the pair code with no normalization; under
the split that swap is a literal exchange of fields, while under a flat `BigDigits` on
`⌜q n⌝` it would require unpairing an exponential value — a bignum `Nat.sqrt`, which is
one of the inverse operations the digit calculus is known not to close under.

Two runs are carried for the numerator: `numCode`, the `ℤ`-code that `encode_rat_eq`
pairs into `⌜q n⌝`, and `natAbsNum`, its magnitude.  Neither is derivable from the other
inside the calculus — recovering the magnitude from the code is a halving, recovering the
code from the magnitude a truncated subtraction, and `BigDigits` closes under neither.
The *sign* needs no field, being the code's parity (`DigitRatCodes.sign`).
Paper node: `def:ec` -/
structure DigitRatCodes (q : ℕ → ℚ) : Prop where
  /-- Digit access to the `ℤ`-code of the numerator, `⌜(q n).num⌝`. -/
  numCode : BigDigits (fun n => Encodable.encode (q n).num)
  /-- Digit access to the numerator's magnitude. -/
  natAbsNum : BigDigits (fun n => (q n).num.natAbs)
  /-- Digit access to the denominator. -/
  den : BigDigits (fun n => (q n).den)

/-- The code of a negative integer, in closed form: `-(n+1) ↦ 2n + 1`, the odd branch of
`Equiv.intEquivNat`'s sign fold.  The even branch is `encode_int_natCast`. -/
lemma encode_int_negSucc (n : ℕ) : Encodable.encode (Int.negSucc n) = 2 * n + 1 := rfl

/-- **The magnitude of an integer, from its code, without halving a negative branch**:
`(⌜i⌝ + 1) / 2 = |i|` uniformly, because the two branches of the sign fold are `2|i|` and
`2|i| - 1`. -/
lemma encode_int_add_one_div_two (i : ℤ) : (Encodable.encode i + 1) / 2 = i.natAbs := by
  cases i with
  | ofNat m =>
      rw [show (Int.ofNat m) = ((m : ℕ) : ℤ) from rfl, encode_int_natCast,
        Int.natAbs_natCast]
      omega
  | negSucc n =>
      rw [encode_int_negSucc, show (Int.negSucc n).natAbs = n + 1 from rfl]
      omega

/-- The parity of the numerator's code decides the sign, so `DigitRatCodes` needs no sign
field: `⌜i⌝` is even exactly when `i ≥ 0`. -/
lemma encode_int_mod_two (i : ℤ) : Encodable.encode i % 2 = if i < 0 then 1 else 0 := by
  cases i with
  | ofNat m =>
      rw [show (Int.ofNat m) = ((m : ℕ) : ℤ) from rfl, encode_int_natCast,
        if_neg (by simp)]
      omega
  | negSucc n => rw [encode_int_negSucc, if_pos (Int.negSucc_lt_zero n)]; omega

namespace DigitRatCodes

/-- The sign bit is poly-fueled from the numerator's digit certificate — it is the
parity of `⌜(q n).num⌝`, which is that value's lowest base-4 digit mod 2. -/
lemma sign {q : ℕ → ℚ} (h : DigitRatCodes q) :
    ∃ c, PolyFueled c (fun n => if (q n).num < 0 then 1 else 0) := by
  obtain ⟨c, hc⟩ := h.numCode.mod_two
  exact ⟨c, hc.of_eq (fun n => encode_int_mod_two (q n).num)⟩

/-- Assembling the pair code for emission: `⌜q n⌝ = ⟪⌜(q n).num⌝, (q n).den⟫`, which
`BigDigits.natPair` builds from the two runs.  This is the interface
`BigSpliceStream.serialize_const_write` consumes. -/
lemma toBigDigits {q : ℕ → ℚ} (h : DigitRatCodes q) :
    BigDigits (fun n => Encodable.encode (q n)) :=
  (h.numCode.natPair h.den).of_eq (fun n => (encode_rat_eq (q n)).symm)

/-- Every value-bounded certificate is a write-out certificate: unpair the polynomial
code and halve the numerator branch, all at polynomial values. -/
lemma ofPolyRatCodes {q : ℕ → ℚ} (h : PolyRatCodes q) : DigitRatCodes q := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨cd, hd⟩ := divmodc_polyFueled 2 (by norm_num)
  have hnum : PolyFueled _ (fun n => Encodable.encode (q n).num) :=
    (PolyFueled.left.comp hc).of_eq (fun n => by
      rw [encode_rat_eq]; simp only [Nat.unpair_pair])
  have hden : PolyFueled _ (fun n => (q n).den) :=
    (PolyFueled.right.comp hc).of_eq (fun n => by
      rw [encode_rat_eq]; simp only [Nat.unpair_pair])
  have habs : PolyFueled _ (fun n => (q n).num.natAbs) :=
    (PolyFueled.left.comp (hd.comp hnum.succ_comp)).of_eq (fun n => by
      simp only [Nat.unpair_pair]; exact encode_int_add_one_div_two (q n).num)
  exact ⟨.of_polyFueled hnum, .of_polyFueled habs, .of_polyFueled hden⟩

lemma const (r : ℚ) : DigitRatCodes (fun _ => r) :=
  ofPolyRatCodes ⟨_, PolyFueled.const (Encodable.encode r)⟩

lemma comp {q : ℕ → ℚ} (h : DigitRatCodes q) {c : Code} {f : ℕ → ℕ}
    (hf : PolyFueled c f) : DigitRatCodes (fun n => q (f n)) :=
  ⟨h.numCode.comp hf, h.natAbsNum.comp hf, h.den.comp hf⟩

lemma of_eq {q q' : ℕ → ℚ} (h : DigitRatCodes q) (he : ∀ n, q n = q' n) :
    DigitRatCodes q' := by
  rwa [funext he] at h

/-- A written-out natural is a written-out rational. -/
lemma natCast {v : ℕ → ℕ} (h : BigDigits v) : DigitRatCodes (fun n => (v n : ℚ)) where
  numCode := (h.add h).of_eq (fun n => by
    rw [Rat.num_natCast, encode_int_natCast]; omega)
  natAbsNum := h.of_eq (fun n => by rw [Rat.num_natCast]; simp)
  den := (BigDigits.const 1).of_eq (fun n => by rw [Rat.den_natCast])

/-- **The reciprocal, by representation rather than arithmetic.**  For a positive
rational the inverse exchanges numerator magnitude and denominator, so the two digit runs
simply swap; the numerator's `ℤ`-code is the doubled denominator, one `BigDigits.add`.
No digit-level division, unpairing, or normalization is involved — which is exactly why
the split representation was chosen. -/
lemma inv_of_pos {q : ℕ → ℚ} (h : DigitRatCodes q) (hpos : ∀ n, 0 < q n) :
    DigitRatCodes (fun n => 1 / q n) := by
  have hnum : ∀ n, (1 / q n).num = ((q n).den : ℤ) := fun n => by
    rw [one_div]
    simp [Rat.num_inv, Int.sign_eq_one_iff_pos.mpr (Rat.num_pos.mpr (hpos n))]
  have hden : ∀ n, (1 / q n).den = (q n).num.natAbs := fun n => by
    rw [one_div]; exact Rat.den_inv_of_ne_zero (ne_of_gt (hpos n))
  exact ⟨(h.den.add h.den).of_eq (fun n => by
      rw [hnum n, encode_int_natCast]; omega),
    h.den.of_eq (fun n => by rw [hnum n, Int.natAbs_natCast]),
    h.natAbsNum.of_eq (fun n => (hden n).symm)⟩

end DigitRatCodes

/-! ## Strictness

The write-out classes are not a relabeling.  Three separations are **proved** below, and
the separating families are the paper's own — an `n`-bit natural and the tolerance
sequence `δ n = 2⁻ⁿ`:

* `bigDigits_two_pow_not_polyFueled` — `BigDigits` over `∃ c, PolyFueled c v`;
* `bigTokenStream_not_polySegStream` — `BigTokenStream` over `PolySegStream`;
* `digitRatCodes_two_pow_inv_not_polyRatCodes` — `DigitRatCodes` over `PolyRatCodes`.

* `bigSpliceStream_two_pow_inv_not_rpnSpliceStream` — `BigSpliceStream` over
  `RpnSpliceStream`, at the constant feature for `δ n = 2⁻ⁿ`.

`not_polyFueled_two_pow` is the repo's size-based separation of `PolyFueled`, and all four
reduce to it.  The remaining pair — `BigSentenceCodes` over `RpnSentenceCodes` — is an
inclusion here (`BigSentenceCodes.ofRpnSentenceCodes`) with **no strictness proof**; do not
describe it as strict.  What is established for it is that its write-out constructor
`ofDigitSentenceCodes` has no value-bounded counterpart. -/

/-- The base-4 length of `2 ^ n` is `n / 2 + 1`. -/
lemma len4_two_pow (n : ℕ) : len4 (2 ^ n) = n / 2 + 1 := by
  have hle : len4 (2 ^ n) ≤ n / 2 + 1 := by
    rw [len4_le_iff]
    calc (2:ℕ) ^ n < 2 ^ (2 * (n / 2 + 1)) :=
          Nat.pow_lt_pow_right (by norm_num) (by omega)
      _ = 4 ^ (n / 2 + 1) := by rw [show (4:ℕ) = 2 ^ 2 from rfl, ← pow_mul]
  have hge : n / 2 < len4 (2 ^ n) := by
    rw [lt_len4_iff]
    calc (4:ℕ) ^ (n / 2) = 2 ^ (2 * (n / 2)) := by
          rw [show (4:ℕ) = 2 ^ 2 from rfl, ← pow_mul]
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- The base-4 digits of `2 ^ n`: a single `1` or `2` at column `n / 2`. -/
lemma dig4_two_pow (n j : ℕ) :
    dig4 (2 ^ n) j = if n = 2 * j then 1 else if n = 2 * j + 1 then 2 else 0 := by
  rw [dig4, show (4:ℕ) ^ j = 2 ^ (2 * j) from by
    rw [show (4:ℕ) = 2 ^ 2 from rfl, ← pow_mul]]
  rcases lt_or_ge n (2 * j) with h | h
  · rw [Nat.div_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) h)]
    rw [if_neg (by omega), if_neg (by omega)]
  · rw [Nat.pow_div h (by norm_num : 0 < 2)]
    rcases Nat.lt_or_ge (n - 2 * j) 2 with h2 | h2
    · rcases (by omega : n - 2 * j = 0 ∨ n - 2 * j = 1) with hh | hh
      · rw [hh, if_pos (by omega)]
      · rw [hh, if_neg (by omega), if_pos (by omega)]
    · rw [if_neg (by omega), if_neg (by omega)]
      obtain ⟨m, hm⟩ : ∃ m, n - 2 * j = m + 2 := ⟨n - 2 * j - 2, by omega⟩
      rw [hm, pow_add]
      simp [Nat.mul_mod_left]

/-- **The separating natural family**: `2 ^ n` is written out — an `n`-bit string, one
nonzero base-4 digit, both located by constant-width arithmetic on `n` — even though its
value is exponential. -/
lemma bigDigits_two_pow : BigDigits (fun n => 2 ^ n) := by
  obtain ⟨cdm, hdm⟩ := divmodc_polyFueled 2 (by norm_num)
  obtain ⟨cad, had⟩ := addc_polyFueled
  obtain ⟨cml, hml⟩ := mulc_polyFueled 2
  have hlen : PolyFueled _ (fun n : ℕ => len4 (2 ^ n)) :=
    ((PolyFueled.left.comp (hdm.comp PolyFueled.id)).succ_comp).of_eq (fun n => by
      rw [len4_two_pow]; simp)
  have hn : PolyFueled _ (fun z : ℕ => z.unpair.1) := PolyFueled.left
  have hj2 : PolyFueled _ (fun z : ℕ => 2 * z.unpair.2) :=
    (hml.comp PolyFueled.right).of_eq (fun z => by ring)
  have hj2s : PolyFueled _ (fun z : ℕ => 2 * z.unpair.2 + 1) := hj2.succ_comp
  have ht1 : PolyFueled _ (fun z : ℕ =>
      (z.unpair.1 - 2 * z.unpair.2) + (2 * z.unpair.2 - z.unpair.1)) :=
    had.comp ((subc_polyFueled.comp (hn.pair hj2)).pair
      (subc_polyFueled.comp (hj2.pair hn))) |>.of_eq (fun z => by simp)
  have ht2 : PolyFueled _ (fun z : ℕ =>
      (z.unpair.1 - (2 * z.unpair.2 + 1)) + ((2 * z.unpair.2 + 1) - z.unpair.1)) :=
    had.comp ((subc_polyFueled.comp (hn.pair hj2s)).pair
      (subc_polyFueled.comp (hj2s.pair hn))) |>.of_eq (fun z => by simp)
  have hinner : PolyFueled _ (fun z : ℕ =>
      if z.unpair.1 = 2 * z.unpair.2 + 1 then 2 else 0) :=
    (ifzSel_polyFueled.comp (((PolyFueled.const 2).pair (PolyFueled.const 0)).pair ht2)).of_eq
      (fun z => by
        simp only [Nat.unpair_pair, ifzSelFn]
        by_cases h : z.unpair.1 = 2 * z.unpair.2 + 1
        · rw [if_pos (by omega), if_pos h]
        · rw [if_neg (by omega), if_neg h])
  have hdig : PolyFueled _ (fun z : ℕ => dig4 (2 ^ z.unpair.1) z.unpair.2) :=
    (ifzSel_polyFueled.comp
      (((PolyFueled.const 1).pair hinner).pair ht1)).of_eq (fun z => by
        simp only [Nat.unpair_pair, ifzSelFn, dig4_two_pow]
        by_cases h : z.unpair.1 = 2 * z.unpair.2
        · rw [if_pos (by omega), if_pos h]
        · rw [if_neg (by omega), if_neg h])
  exact ⟨_, _, hlen, hdig⟩

/-- **The natural-number separation.**  `2 ^ n` — an `n`-bit string, and so a paper-legal
polynomial write-out — has poly-fueled digit access but no poly-fueled whole value.  Every
class of the form `∃ c, PolyFueled c v` therefore excludes a sequence the paper admits,
and `BigDigits` is a strict enlargement rather than a renaming. -/
lemma bigDigits_two_pow_not_polyFueled :
    BigDigits (fun n => 2 ^ n) ∧ ∀ c : Code, ¬ PolyFueled c (fun n => 2 ^ n) :=
  ⟨bigDigits_two_pow, not_polyFueled_two_pow⟩

/-- **The stream-level separation.**  A single-token stream carrying `2 ^ n` is written
out but is not a `PolySegStream`: the latter's per-token emitter would be a poly-fueled
program for `2 ^ n` itself.  This is the separation that matters for emission, since
`PolySegStream` is the certificate every consumer builds. -/
lemma bigTokenStream_not_polySegStream :
    BigTokenStream (fun n => [2 ^ n]) ∧ ¬ PolySegStream (fun n => [2 ^ n]) := by
  refine ⟨BigTokenStream.ofBigDigits bigDigits_two_pow, fun h => ?_⟩
  obtain ⟨ct, cl, tokenFn, lenFn, htok, hlen, hslen, hget⟩ := h
  refine not_polyFueled_two_pow _
    ((htok.comp (PolyFueled.id.pair (PolyFueled.const 0))).of_eq (fun n => ?_))
  have h1 : lenFn n = 1 := by simpa using (hslen n).symm
  simpa using hget n 0 (by omega)

/-- **The separating rational family**: the paper's tolerance sequence `δ n = 2⁻ⁿ`.  Its
numerator is `1` and its denominator is `2 ^ n`, so all three digit runs are immediate. -/
lemma digitRatCodes_two_pow_inv :
    DigitRatCodes (fun n => (((2 ^ n : ℕ) : ℚ))⁻¹) where
  numCode := (BigDigits.const 2).of_eq (fun n => by
    rw [Rat.inv_natCast_num_of_pos ((by positivity))]; rfl)
  natAbsNum := (BigDigits.const 1).of_eq (fun n => by
    rw [Rat.inv_natCast_num_of_pos ((by positivity))]; rfl)
  den := bigDigits_two_pow.of_eq (fun n => by
    rw [Rat.inv_natCast_den_of_pos ((by positivity))])

/-- **The rational separation.**  `δ n = 2⁻ⁿ` is the tolerance sequence the paper's
convergence statements quantify over, and it is a two-symbol write-out at every day; but
its code `⟪2, 2ⁿ⟫` is exponential, so `PolyRatCodes` excludes it.  A theorem whose
hypothesis is `PolyRatCodes δ` is therefore silent about the paper's own δ, and this is
the concrete content of the seven qualified rows. -/
lemma digitRatCodes_two_pow_inv_not_polyRatCodes :
    DigitRatCodes (fun n => (((2 ^ n : ℕ) : ℚ))⁻¹) ∧
      ¬ PolyRatCodes (fun n => (((2 ^ n : ℕ) : ℚ))⁻¹) := by
  refine ⟨digitRatCodes_two_pow_inv, fun h => ?_⟩
  obtain ⟨c, hc⟩ := h
  refine not_polyFueled_two_pow _ ((PolyFueled.right.comp hc).of_eq (fun n => ?_))
  rw [encode_rat_inv_natCast ((by positivity)), Nat.unpair_pair]

/-! ### The emission-surface separation

`serialize_const_write` has no value-bounded counterpart, and the reason is visible one
level down: a constant leaf serializes to the single payload chunk `[1, ⌜q n⌝]`, and
`unRpn` copies a tag-`1` payload token **verbatim**, so any `RpnSpliceStream` certificate
for that family has `⌜q n⌝` sitting in its emitted stream as one token — which a
`PolySegStream`'s per-token emitter would have to produce at polynomial value. -/

/-- **A run contracting to a bare payload chunk is one.**  `unRpn` rewrites a tag-`1`
frame to itself and consumes nothing around it, so a run whose whole contraction is
`[1, c]` carries `c` as its own second token. -/
private lemma unRpn_eq_payload_getD {ts : List ℕ} {c : ℕ} (h : unRpn ts = [1, c]) :
    2 ≤ ts.length ∧ ts.getD 1 0 = c := by
  match ts with
  | [] => simp [unRpn, unRpnTokens] at h
  | [t] =>
      simp only [unRpn, List.length_cons] at h
      rw [unRpnTokens] at h
      split_ifs at h with h0 h6 h1 h7
      · split at h
        · simp at h
        · split at h <;> simp at h
      · split at h <;> simp at h
      · simp at h
      · simp at h
      · simp only [List.cons.injEq] at h
        exact absurd h.1 h1
  | t :: c' :: r =>
      refine ⟨by simp, ?_⟩
      simp only [unRpn, List.length_cons] at h
      rw [unRpnTokens] at h
      split_ifs at h with h0 h6 h1 h7
      · split at h
        · simp at h
        · split at h <;> simp at h
      · split at h <;> simp at h
      · simp only [List.cons.injEq] at h
        simpa using h.2.1
      · simp only [List.cons.injEq] at h
        exact absurd h.1 (by omega)
      · simp only [List.cons.injEq] at h
        exact absurd h.1 h1

/-- **The emission-surface separation.**  The constant-feature stream for the paper's
`δ n = 2⁻ⁿ` is a `BigSpliceStream` (`serialize_const_write`) and is **not** an
`RpnSpliceStream`: `unRpn` copies the tag-`1` payload verbatim, so a value-metered
certificate would hand `PolySegStream`'s per-token emitter a poly-fueled program for
`⌜2⁻ⁿ⌝ = ⟪2, 2ⁿ⟫`, which `digitRatCodes_two_pow_inv_not_polyRatCodes` refutes.

This is what makes `GeneratedRatFeature.polyTok : BigSpliceStream` a genuine widening of
the `RpnSpliceStream` field it replaced, rather than a restatement.
Kind: `P` proved; provenance: (a) derived in-project. -/
lemma bigSpliceStream_two_pow_inv_not_rpnSpliceStream :
    BigSpliceStream (fun n => (EF.const ((((2 ^ n : ℕ) : ℚ))⁻¹)).serialize) ∧
      ¬ RpnSpliceStream (fun n => (EF.const ((((2 ^ n : ℕ) : ℚ))⁻¹)).serialize) := by
  refine ⟨BigSpliceStream.serialize_const_write
    digitRatCodes_two_pow_inv.toBigDigits, ?_⟩
  rintro ⟨s, ⟨ct, cl, tokenFn, lenFn, htok, hlen, hslen, hget⟩, hc⟩
  refine digitRatCodes_two_pow_inv_not_polyRatCodes.2
    ⟨_, (htok.comp (PolyFueled.id.pair (PolyFueled.const 1))).of_eq (fun z => ?_)⟩
  have hu : unRpn (s z) = [1, Encodable.encode ((((2 ^ z : ℕ) : ℚ))⁻¹)] := by
    simpa [EF.serialize, unRpn_nil] using (hc z).unRpn_eq
  obtain ⟨hlen2, hval⟩ := unRpn_eq_payload_getD hu
  have h1 : (1 : ℕ) < lenFn z := by rw [← hslen z]; omega
  exact (hget z 1 h1).trans hval

example : ¬ RpnSpliceStream (fun n => (EF.const ((((2 ^ n : ℕ) : ℚ))⁻¹)).serialize) :=
  bigSpliceStream_two_pow_inv_not_rpnSpliceStream.2

#print axioms BigTokenStream.ofBigDigits
#print axioms BigTokenStream.concatVar
#print axioms ec_of_bigTokenStream
#print axioms BigSentenceCodes.ofDigitSentenceCodes
#print axioms BigSpliceStream.bigPayload
#print axioms BigSpliceStream.ec
#print axioms DigitRatCodes.toBigDigits
#print axioms DigitRatCodes.inv_of_pos
#print axioms bigDigits_two_pow_not_polyFueled
#print axioms bigTokenStream_not_polySegStream
#print axioms digitRatCodes_two_pow_inv_not_polyRatCodes
#print axioms bigSpliceStream_two_pow_inv_not_rpnSpliceStream

end LogicalInduction

