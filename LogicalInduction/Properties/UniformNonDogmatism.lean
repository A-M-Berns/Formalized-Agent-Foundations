import LogicalInduction.Properties.NonDogmatism
import LogicalInduction.Properties.AffinePersistence
import LogicalInduction.Framework.Emission.WriteOut

/-!
# Uniform Non-Dogmatism

Renders §4.6 *Non-Dogmatism*, `thm:obu` (Uniform Non-Dogmatism).

`RepeatsEveryMember` is the paper's triangular repetition preprocessing, stated
independently of any market.

The varying-sentence scale ladder is the `Properties/Support/Exploitation.lean` ladder at
the trigger family `obuBuySig`: rung `j` buys from the currently enumerated sentence
whenever its price falls below `1/j³`, spends at most `1/j²` over its lifetime, and
permanently disarms after one full trigger (`armChain`). `obuTrader` is that ladder and
`obuTrader_exploits` supplies its trigger guarantee to `ladderTrader_exploits`: a world
satisfying the whole enumerated theory values every purchased share at one, so the ladder is
bounded below by `−2` (via `sum_inv_sq_le_two`) while a single rung firing already yields
profit `j − 1`.

The token-emission half — `obuArmBlock`, `serialize_armChain_obuBuy`, `serialize_obuCoef`,
`serialize_obuLadderEF`, `obuChunkSeg_spliceStream` — proves
`obuTrader_ec : EfficientlyComputable (obuTrader φ)` from a `MachineSentenceCodes` enumeration
certificate. Arm blocks are variable-length once sentence slots carry blocks, so the
combinator is `concatVar` rather than the fixed-width `blocks`.
`exists_obu_fire_of_low_limit` is the analytic link from fixed-sentence convergence to the
varying ladder.

The endpoints are `lic_uniform_nonDogmatism_repeating`, for an enumeration that already
repeats, and the paper-facing `lic_uniform_nonDogmatism`, which takes the explicit
preprocessing witness `EfficientRepeatedEnumeration` — a Tier-2 `#assert_fields` structure
that is purely syntactic, containing neither prices nor a conclusion. Both are consumed by
`Properties/UniversalSemimeasure.lean` and
`Construction/NonDogmatism/RepeatedEnumeration.lean` and
`Construction/Conditioning/Compiler.lean`.
-/

namespace LogicalInduction

open Filter Topology

/-! ## The repeating enumeration -/

/-- Every member of an enumeration reappears arbitrarily late.  This is the paper's
triangular repetition preprocessing, stated independently of any market. -/
def RepeatsEveryMember (φ : ℕ → Sentence) : Prop :=
  ∀ i N, ∃ n, N ≤ n ∧ φ n = φ i

/-! ## The varying-sentence scale ladder -/

/-- Rung-`j`, day-`i` signal for the current member `φ i`. -/
def obuBuySig (φ : ℕ → Sentence) (j i : ℕ) : EF :=
  ndBuySig (φ i) j i

@[simp] lemma obuBuySig_rank (φ : ℕ → Sentence) (j i : ℕ) :
    (obuBuySig φ j i).rank = i := ndBuySig_rank (φ i) j i

lemma obuBuySig_denote_pad (φ : ℕ → Sentence) (P : History)
    {j i : ℕ} (h : i < j) :
    (obuBuySig φ j i).denote P = 0 :=
  ndBuySig_denote_pad (φ i) P h

lemma obuBuySig_mem (φ : ℕ → Sentence) (P : History) (j i : ℕ) :
    0 ≤ (obuBuySig φ j i).denote P ∧ (obuBuySig φ j i).denote P ≤ 1 :=
  ndBuySig_mem (φ i) P j i

lemma obuBuySig_pos_imp (φ : ℕ → Sentence) (P : History)
    {j i : ℕ} (hj : 1 ≤ j) (h : 0 < (obuBuySig φ j i).denote P) :
    P i (φ i) < 1 / (j : ℝ) ^ 3 :=
  ndBuySig_pos_imp (φ i) P hj h

lemma obuBuySig_eq_one (φ : ℕ → Sentence) (P : History)
    {j i : ℕ} (hj : 1 ≤ j) (hlive : j ≤ i)
    (h : P i (φ i) < ((ndThr j : ℚ) : ℝ)) :
    (obuBuySig φ j i).denote P = 1 :=
  ndBuySig_eq_one (φ i) P hj hlive h

/-- Day-`n` coefficient of varying-sentence rung `j`. -/
def obuCoef (φ : ℕ → Sentence) (j n : ℕ) : EF :=
  ladderCoef (fun j => (j : ℚ)) (obuBuySig φ) j n

/-- Sum of all live rungs on day `n`. -/
def obuLadderEF (φ : ℕ → Sentence) (n m : ℕ) : EF :=
  ladderEF (fun j => (j : ℚ)) (obuBuySig φ) n m

/-- The varying-sentence scale-ladder trader used by Uniform Non-Dogmatism: the scale ladder
of `Properties/Support/Exploitation.lean` at the trigger family that reads each day's own
enumerated member. -/
def obuTrader (φ : ℕ → Sentence) : Trader :=
  ladderTrader (fun j => (j : ℚ)) (obuBuySig φ) φ
    (fun j i => (obuBuySig_rank φ j i).le)

/-- The varying ladder exploits if every rung receives one full trigger and
every finite deductive stage has a world satisfying the whole enumerated theory.  The ladder
economics are `ladderTrader_exploits`; this lane supplies the trigger's guarantee — a share
of `φ n` is only bought below `1/j³`, where a world satisfying the whole enumeration pays
`1`. -/
lemma obuTrader_exploits
    (P : History) (DP : DeductiveProcess) (φ : ℕ → Sentence)
    (hjoint : ∀ n, ∃ v : PCWorld,
      v.ConsistentWith (DP.D n) ∧ ∀ i, v.Holds (φ i))
    (hfire : ∀ j, 1 ≤ j → ∃ n, j ≤ n ∧ P n (φ n) < ((ndThr j : ℚ) : ℝ)) :
    (obuTrader φ).Exploits P DP := by
  refine ladderTrader_exploits (pay := fun v n => v.payout (φ n) - P n (φ n))
    (Good := fun v => ∀ i, v.Holds (φ i)) _ (fun j i => obuBuySig_mem φ P j i)
    (fun j i hi => obuBuySig_denote_pad φ P hi)
    (fun v j n => by push_cast; ring) ?_ ?_ ?_
  · intro v j n hj hpos
    have hprice := obuBuySig_pos_imp φ P hj hpos
    have hpay : 0 ≤ v.payout (φ n) := by rw [PCWorld.payout]; split <;> norm_num
    linarith
  · intro v hv j n hj hpos
    have hprice := obuBuySig_pos_imp φ P hj hpos
    have hpay : v.payout (φ n) = 1 := by rw [PCWorld.payout, if_pos (hv n)]
    rw [hpay]
    linarith
  · intro j hj
    obtain ⟨n₀, hn₀, hdip⟩ := hfire j hj
    obtain ⟨v, hv, hvφ⟩ := hjoint n₀
    exact ⟨n₀, hn₀, obuBuySig_eq_one φ P hj hn₀ hdip, v, hv, hvφ⟩


/-! ## Uniform token emission -/

/-- Serialization block for one historical varying-sentence arm update. -/
def obuArmBlock (φ : ℕ → Sentence) (j i : ℕ) : List ℕ :=
  (oneMinus (obuBuySig φ j i)).serialize ++ [3]

lemma serialize_armChain_obuBuy (φ : ℕ → Sentence) (j : ℕ) : ∀ n,
    (armChain (obuBuySig φ j) n).serialize =
      [1, Encodable.encode ((1 : ℚ))] ++
        (List.range n).flatMap (fun i ↦ obuArmBlock φ j i)
  | 0 => by simp [armChain, EF.serialize]
  | (n + 1) => by
      rw [armChain]
      simp only [EF.serialize]
      rw [serialize_armChain_obuBuy φ j n, List.range_succ,
        List.flatMap_append, List.flatMap_singleton, obuArmBlock]
      simp [List.append_assoc]

lemma serialize_obuCoef (φ : ℕ → Sentence) (j n : ℕ) :
    (obuCoef φ j n).serialize =
      [1, Encodable.encode ((j : ℚ))] ++
        (armChain (obuBuySig φ j) n).serialize ++
        (obuBuySig φ j n).serialize ++ [3, 3] := by
  simp [obuCoef, ladderCoef, EF.serialize, List.append_assoc]

lemma serialize_obuLadderEF (φ : ℕ → Sentence) (n : ℕ) : ∀ m,
    (obuLadderEF φ n m).serialize =
      [1, Encodable.encode ((0 : ℚ))] ++
        (List.range m).flatMap
          (fun j' ↦ (obuCoef φ (j' + 1) n).serialize ++ [2])
  | 0 => by simp [obuLadderEF, ladderEF, EF.serialize]
  | (m + 1) => by
      rw [obuLadderEF, ladderEF]
      simp only [EF.serialize]
      rw [show ladderEF (fun j => (j : ℚ)) (obuBuySig φ) n m = obuLadderEF φ n m from rfl,
        show ladderCoef (fun j => (j : ℚ)) (obuBuySig φ) (m + 1) n
            = obuCoef φ (m + 1) n from rfl,
        serialize_obuLadderEF φ n m, List.range_succ,
        List.flatMap_append, List.flatMap_singleton]
      simp [List.append_assoc]

/-- Spliced varying-sentence buy-signal emitter: the sentence slot draws blocks from
a `MachineSentenceCodes` certificate, admitting deep enumerations, and the two rational
constants from `MachineDigits` writers.  Every premise is at the machine class the
conclusion is; a caller holding fuel certificates crosses by `BigDigits.of_polyFueled` and
`BigDigits.toMachine`. -/
lemma obuBuySig_spliceStream_comp
    {φ : ℕ → Sentence} (hφ : MachineSentenceCodes φ)
    {af δf : ℕ → ℚ} {jf : ℕ → ℕ}
    (hj : UnaryRuler jf)
    (ha : MachineDigits (fun m ↦ Encodable.encode (af m + δf m)))
    (hd : MachineDigits (fun m ↦ Encodable.encode (1 / δf m))) :
    MachineSpliceStream (fun m ↦
      (buyIndEF (φ (jf m)) (af m) (δf m) (jf m)).serialize) :=
  MachineSpliceStream.serialize_clip01 (MachineSpliceStream.serialize_mul
    (MachineSpliceStream.serialize_add
      (MachineSpliceStream.serialize_const_write ha)
      (MachineSpliceStream.serialize_mul (MachineSpliceStream.serialize_const (-1))
        (MachineSpliceStream.serialize_price hφ hj
          (MachineDigits.ofUnaryRuler hj))))
    (MachineSpliceStream.serialize_const_write hd))

/-- Spliced arm-update block. -/
lemma obuArmBlock_spliceStream (φ : ℕ → Sentence) (hφ : MachineSentenceCodes φ) :
    MachineSpliceStream
      (fun x ↦ obuArmBlock φ (x.unpair.1.unpair.2 + 1) x.unpair.2) := by
  obtain ⟨_, hsum⟩ := encode_thrSum_polyFueled
    (PolyFueled.right.comp PolyFueled.left) PolyFueled.right
  obtain ⟨_, hrecip⟩ := encode_thrRecip_polyFueled
    (PolyFueled.right.comp PolyFueled.left) PolyFueled.right
  have hbuy : MachineSpliceStream (fun x ↦
      (obuBuySig φ (x.unpair.1.unpair.2 + 1) x.unpair.2).serialize) := by
    simpa only [obuBuySig, ndBuySig] using
      obuBuySig_spliceStream_comp hφ
        (af := fun x ↦ ndThr (x.unpair.1.unpair.2 + 1))
        (δf := fun x ↦ ndPadThr (x.unpair.1.unpair.2 + 1) x.unpair.2)
        (UnaryRuler.of_polyFueled PolyFueled.right)
        (BigDigits.toMachine (BigDigits.of_polyFueled hsum))
        (BigDigits.toMachine (BigDigits.of_polyFueled hrecip))
  exact (MachineSpliceStream.serialize_oneMinus hbuy).append
    (MachineSpliceStream.tag 3 (by norm_num))

/-- Spliced coefficient chunk (`obuCoef` + the ladder `add` tag): the arm blocks are
variable-length once sentence slots carry blocks, so this uses `concatVar` rather than the
fixed-width `blocks` combinator. -/
lemma obuChunkSeg_spliceStream
    (φ : ℕ → Sentence) (hφ : MachineSentenceCodes φ) :
    MachineSpliceStream (fun m ↦
      (obuCoef φ (m.unpair.2 + 1) m.unpair.1).serialize ++ [2]) := by
  obtain ⟨cr, hcr⟩ := encode_ratCast_polyFueled PolyFueled.right
  have segA : MachineSpliceStream (fun m ↦
      (EF.const (((m.unpair.2 + 1 : ℕ) : ℚ))).serialize) :=
    MachineSpliceStream.serialize_const_write
      (BigDigits.toMachine (BigDigits.of_polyFueled hcr))
  have segB : MachineSpliceStream (fun _ : ℕ ↦ [1, Encodable.encode ((1 : ℚ))]) :=
    MachineSpliceStream.bigPayload 1 (Or.inl rfl)
      (MachineDigits.const (Encodable.encode ((1 : ℚ))))
  have segC := (obuArmBlock_spliceStream φ hφ).concatVar
    (UnaryRuler.unpairFst)
  obtain ⟨_, hsum⟩ := encode_thrSum_polyFueled PolyFueled.right PolyFueled.left
  obtain ⟨_, hrecip⟩ := encode_thrRecip_polyFueled PolyFueled.right PolyFueled.left
  have segD : MachineSpliceStream (fun m ↦
      (obuBuySig φ (m.unpair.2 + 1) m.unpair.1).serialize) := by
    simpa only [obuBuySig, ndBuySig] using
      obuBuySig_spliceStream_comp hφ
        (af := fun m ↦ ndThr (m.unpair.2 + 1))
        (δf := fun m ↦ ndPadThr (m.unpair.2 + 1) m.unpair.1)
        (UnaryRuler.of_polyFueled PolyFueled.left)
        (BigDigits.toMachine (BigDigits.of_polyFueled hsum))
        (BigDigits.toMachine (BigDigits.of_polyFueled hrecip))
  have segE : MachineSpliceStream (fun _ : ℕ ↦ [3, 3, 2]) :=
    ((MachineSpliceStream.tag 3 (by norm_num)).append
      (MachineSpliceStream.tag 3 (by norm_num))).append
        (MachineSpliceStream.tag 2 (by norm_num))
  refine MachineSpliceStream.of_eq
    ((((segA.append segB).append segC).append segD).append segE) (fun m ↦ ?_)
  rw [serialize_obuCoef, serialize_armChain_obuBuy]
  simp [EF.serialize, Nat.unpair_pair, List.append_assoc]

/-- The varying-sentence scale ladder is efficiently computable, from an 𝓔𝓒 enumeration
certificate at the machine class.
Paper node: `def:ec` -/
lemma obuTrader_ec (φ : ℕ → Sentence) (hφ : MachineSentenceCodes φ) :
    EfficientlyComputable (obuTrader φ) := by
  have segChunks := (obuChunkSeg_spliceStream φ hφ).concatVar UnaryRuler.id
  have seg1 : MachineSpliceStream (fun _ : ℕ ↦ [1, Encodable.encode ((0 : ℚ))]) :=
    MachineSpliceStream.bigPayload 1 (Or.inl rfl)
      (MachineDigits.const (Encodable.encode ((0 : ℚ))))
  have seg3 := MachineSpliceStream.tradeSlot hφ UnaryRuler.id
  refine MachineSpliceStream.ec _
    (MachineSpliceStream.of_eq ((seg1.append segChunks).append seg3) ?_)
  intro n
  show _ = serializeTrades ((obuTrader φ).strat n).trades
  rw [show ((obuTrader φ).strat n).trades = [(obuLadderEF φ n n, φ n)] from rfl,
    serializeTrades, serializeTrades, serialize_obuLadderEF]
  simp [Nat.unpair_pair]

/-! ## Uniform Non-Dogmatism (`thm:obu`) -/

/-- If one member of a repeating enumeration has limiting probability below rung `j`'s
threshold, then that rung eventually receives a full trigger on a day when the same member
is enumerated.  This is the analytic link between fixed-sentence convergence and the
varying-sentence ladder. -/
lemma exists_obu_fire_of_low_limit
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (φ : ℕ → Sentence) (hrepeat : RepeatsEveryMember φ)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    {j : ℕ}
    (hlow : ∃ i, limitingBelief P (φ i) < ((ndThr j : ℚ) : ℝ)) :
    ∃ n, j ≤ n ∧ P n (φ n) < ((ndThr j : ℚ) : ℝ) := by
  obtain ⟨i, hi⟩ := hlow
  have hconv := lic_limitingBelief_tendsto P DP hworld (φ i)
  have hevent : ∀ᶠ n in atTop, P n (φ i) < ((ndThr j : ℚ) : ℝ) :=
    (tendsto_order.1 hconv).2 _ hi
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hevent
  obtain ⟨n, hn, hφn⟩ := hrepeat i (max j N)
  refine ⟨n, le_trans (le_max_left j N) hn, ?_⟩
  rw [hφn]
  exact hN n (le_trans (le_max_right j N) hn)

/-- Uniform Non-Dogmatism for the efficiently padded, infinitely repeating enumeration
used in the paper's proof.  Joint consistency means that every finite deductive stage has
a propositional world satisfying the entire enumerated theory.
Paper node: `thm:obu` -/
theorem lic_uniform_nonDogmatism_repeating
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (φ : ℕ → Sentence) (hφ : MachineSentenceCodes φ)
    (hrepeat : RepeatsEveryMember φ)
    (hjoint : ∀ n, ∃ v : PCWorld,
      v.ConsistentWith (DP.D n) ∧ ∀ i, v.Holds (φ i)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, ε ≤ limitingBelief P (φ i) := by
  have hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n) := by
    intro n
    obtain ⟨v, hv, _⟩ := hjoint n
    exact ⟨v, hv⟩
  by_contra hbound
  have hlow : ∀ ε : ℝ, 0 < ε →
      ∃ i, limitingBelief P (φ i) < ε := by
    intro ε hε
    by_contra hnone
    apply hbound
    refine ⟨ε, hε, fun i ↦ ?_⟩
    exact le_of_not_gt (fun hi ↦ hnone ⟨i, hi⟩)
  have hfire : ∀ j, 1 ≤ j →
      ∃ n, j ≤ n ∧ P n (φ n) < ((ndThr j : ℚ) : ℝ) := by
    intro j hj
    exact exists_obu_fire_of_low_limit P DP φ hrepeat hworld
      (hlow _ (ndThr_pos hj))
  exact IsLogicalInductor.noExploit (P := P) (DP := DP)
    (obuTrader φ) (obuTrader_ec φ hφ)
    (obuTrader_exploits P DP φ hjoint hfire)

/-- A concrete witness for the paper's preprocessing of a c.e. sentence stream into an
efficiently emitted stream in which every member repeats infinitely often.  `sound` and
`covers` say that preprocessing changes only order and multiplicity.  This structure is
purely syntactic: it contains neither prices nor a non-dogmatism conclusion.
Paper node: `thm:obu` -/
structure EfficientRepeatedEnumeration (source : ℕ → Sentence) where
  sequence : ℕ → Sentence
  sequence_poly : MachineSentenceCodes sequence
  repeats : RepeatsEveryMember sequence
  sound : ∀ j, ∃ i, sequence j = source i
  covers : ∀ i, ∃ j, sequence j = source i

/-- Paper-facing Uniform Non-Dogmatism.  Given the explicit efficient-repetition witness
for the source c.e. stream, every member of a jointly consistent theory receives one
common positive limiting-probability lower bound.
Paper node: `thm:obu` -/
theorem lic_uniform_nonDogmatism
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (source : ℕ → Sentence) (rep : EfficientRepeatedEnumeration source)
    (hjoint : ∀ n, ∃ v : PCWorld,
      v.ConsistentWith (DP.D n) ∧ ∀ i, v.Holds (source i)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, ε ≤ limitingBelief P (source i) := by
  have hjointRep : ∀ n, ∃ v : PCWorld,
      v.ConsistentWith (DP.D n) ∧ ∀ j, v.Holds (rep.sequence j) := by
    intro n
    obtain ⟨v, hv, hvsource⟩ := hjoint n
    refine ⟨v, hv, fun j ↦ ?_⟩
    obtain ⟨i, hi⟩ := rep.sound j
    rw [hi]
    exact hvsource i
  obtain ⟨ε, hε, hrep⟩ := lic_uniform_nonDogmatism_repeating
    P DP rep.sequence rep.sequence_poly rep.repeats hjointRep
  refine ⟨ε, hε, fun i ↦ ?_⟩
  obtain ⟨j, hj⟩ := rep.covers i
  simpa only [hj] using hrep j

end LogicalInduction
