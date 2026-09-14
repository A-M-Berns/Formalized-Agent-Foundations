import LogicalInduction.Construction.Primcodable
import LogicalInduction.Framework.BooleanWorlds
import LogicalInduction.Framework.Emission.Emission
import LogicalInduction.Properties.Pseudorandomness

/-!
# The patient settlement clock

`Properties/Pseudorandomness.lean` states `PatientSettlementClock`: the interface the §4.3–4.4
traders — and the §4.5 affine and §4.8 expectation analogues that run on the same three
families — need in order to wait for a stage at which an affine combination has settled.  This
module inhabits it from computability data alone, and imports exactly the `Properties/` module
that declares the interface.

The deadline itself is not testable outright.  A `DeferralFunction` (`def:deferralfunc`)
decides its graph in time polynomial in `f n` and not in `n`, so a machine holding a budget
`n` can locate every `f k` below `n` and learn nothing about the ones beyond it.
`deadlineRun` (`Properties/SelfTrust.lean`) / `deadlinePassed` is that budgeted test: it is
monotone in the budget, never true early, and eventually true.  `polyFueled_dovetailFound`
(`Framework/Emission/Emission.lean`) discharges the paper's `DefinitelySettled` bullet
(tex:4872) over it.

## Objects

* `deadlineStep`, `deadlinePassed` — the budgeted deadline test over `deadlineRun`, with its
  soundness (`deadlinePassed_sound`), monotonicity, eventual-truth and machine-metering
  (`unaryRuler_deadlinePassed`) lemmas.
* `SettlementSemiDecider` — the general interface: a code semi-deciding settlement, from which
  `PatientSettlementClock.ofSemiDecider` derives every semantic field of the clock.
* `SettlementChecker` — its purely computational specialization, with
  `SettlementChecker.toSemiDecider` and `PatientSettlementClock.ofChecker`.
  `Statistics/SettlementCompiler.lean` builds a checker from a market program and a
  deductive-process program, leaving no computability hypothesis on the caller.

`Nat.sqrt` is locally irreducible in the section below: `PolyFueled` and `Primrec` elaboration
over nested `Primcodable` product types reaches `Nat.unpair`, and unfolding `Nat.sqrt`'s
well-founded definition sends `whnf` into a loop.  The loop is not domain mathematics, so the
fix is opacity rather than a heartbeat raise, and a declaration moved across that `section`
boundary must carry the attribute with it.
-/

namespace LogicalInduction

section
-- See the module header on `Nat.sqrt` opacity.
attribute [local irreducible] Nat.sqrt

/-! ### The deadline test

`PatientSettlementClock` must keep component `i` active through `deferralEnvelope f i`, and
may only go inactive once that deadline has passed.  `DeferralFunction.graph_fp` decides
`f k = m` in time polynomial in the unary pair `⟨k, m⟩`, so a machine holding a budget `n`
can scan `m < n` and learn `f k < n` exactly — but nothing about a `f k` beyond its budget,
which is the sense in which the deadline stays undecidable without one.

`deadlineStep` is the per-component failure flag of that scan and `deadlinePassed` its
`k ≤ i` conjunction; both are machine-metered (`unaryRuler_deadlinePassed`), and the test is
sound (`deadlinePassed_sound`), monotone in the budget, and eventually true.

`deadlineRun` is stated beside `DeferralFunction` itself, in `Properties/SelfTrust.lean`;
the schedule built on it is shared with `Construction/Quotation/`, and this module builds
the clock out of it. -/

/-- A prefix sum of counts vanishes exactly when every summand does. -/
private lemma segPrefix_eq_zero_iff (lenFn : ℕ → ℕ) (n : ℕ) : ∀ r : ℕ,
    segPrefix lenFn n r = 0 ↔ ∀ j < r, lenFn (Nat.pair n j) = 0
  | 0 => by simp
  | r + 1 => by
      rw [segPrefix_succ, Nat.add_eq_zero_iff, segPrefix_eq_zero_iff lenFn n r]
      constructor
      · rintro ⟨h1, h2⟩ j hj
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · exact h1 j hj
        · exact h2
      · intro h
        exact ⟨fun j hj => h j (by omega), h r (Nat.lt_succ_self r)⟩

/-- The per-component failure flag of the deadline check, at the paired index `⟨n, k⟩`:
`1` unless component `k`'s deferral has been located strictly below the budget `n`. -/
def deadlineStep (f : DeferralFunction) (w : ℕ) : ℕ :=
  if deadlineRun f (w.unpair.1 - 1) w.unpair.2 = 0 then 1 else 0

/-- The failure flag says exactly that the deferral has not been located below the budget. -/
lemma deadlineStep_eq (f : DeferralFunction) (n k : ℕ) :
    deadlineStep f (Nat.pair n k) = if f.f k < n then 0 else 1 := by
  have hpos : 0 < f.f k := Nat.lt_of_le_of_lt (Nat.zero_le _) (f.lt _)
  simp only [deadlineStep, deadlineRun, Nat.unpair_pair]
  split_ifs <;> omega

/-- The failure flag is machine-metered: it is the day-`(n-1)` lookup tested against zero. -/
lemma unaryRuler_deadlineStep (f : DeferralFunction) : UnaryRuler (deadlineStep f) :=
  (((unaryRuler_deadlineRun f).comp
      ((UnaryRuler.unpairFst.sub (UnaryRuler.const 1)).pair UnaryRuler.unpairSnd)).ifZero
    (UnaryRuler.const 1) (UnaryRuler.const 0)).of_eq (fun w => by simp [deadlineStep])

/-- Every `k ≤ i` has been located strictly below the budget `n`. -/
def deadlinePassed (f : DeferralFunction) (i n : ℕ) : Bool :=
  decide (segPrefix (deadlineStep f) n (i + 1) = 0)

lemma deadlinePassed_eq_true_iff (f : DeferralFunction) (i n : ℕ) :
    deadlinePassed f i n = true ↔ ∀ k ≤ i, f.f k < n := by
  rw [deadlinePassed, decide_eq_true_iff, segPrefix_eq_zero_iff]
  constructor
  · intro h k hk
    have hk' := h k (Nat.lt_succ_of_le hk)
    rw [deadlineStep_eq] at hk'
    by_contra hcon
    rw [if_neg hcon] at hk'
    exact one_ne_zero hk'
  · intro h k hk
    rw [deadlineStep_eq, if_pos (h k (Nat.lt_succ_iff.1 hk))]

lemma deferralEnvelope_lt_of_forall (f : DeferralFunction) (i n : ℕ)
    (h : ∀ k ≤ i, f.f k < n) : deferralEnvelope f i < n := by
  induction i with
  | zero => simpa [deferralEnvelope] using h 0 le_rfl
  | succ i ih =>
      simp only [deferralEnvelope, max_lt_iff]
      exact ⟨ih (fun k hk => h k (by omega)), h (i + 1) le_rfl⟩

/-- **Soundness**: certification implies the deadline really has passed. -/
lemma deadlinePassed_sound (f : DeferralFunction) {i n : ℕ}
    (h : deadlinePassed f i n = true) : deferralEnvelope f i < n :=
  deferralEnvelope_lt_of_forall f i n ((deadlinePassed_eq_true_iff f i n).1 h)

/-- **Monotone**: a larger budget preserves certification. -/
lemma deadlinePassed_mono (f : DeferralFunction) {i n : ℕ}
    (h : deadlinePassed f i n = true) : deadlinePassed f i (n + 1) = true := by
  rw [deadlinePassed_eq_true_iff] at h ⊢
  exact fun k hk => Nat.lt_succ_of_lt (h k hk)

/-- **Eventual completion**: every component's deadline is eventually certified. -/
lemma deadlinePassed_eventually (f : DeferralFunction) (i : ℕ) :
    ∃ N, ∀ n, N ≤ n → deadlinePassed f i n = true := by
  refine ⟨deferralEnvelope f i + 1, fun n hn => ?_⟩
  rw [deadlinePassed_eq_true_iff]
  exact fun k hk => lt_of_le_of_lt (deferral_le_envelope_of_le f hk) (by omega)

/-- The deadline test is machine-metered: the scan is a prefix sum of a ruler-metered
per-component flag, and the conjunction is that sum tested against zero. -/
lemma unaryRuler_deadlinePassed (f : DeferralFunction) :
    UnaryRuler (fun z => if deadlinePassed f z.unpair.1 z.unpair.2 then 1 else 0) := by
  have hscan : UnaryRuler (fun z =>
      segPrefix (deadlineStep f) z.unpair.2 (z.unpair.1 + 1)) :=
    ((UnaryRuler.segPrefix (unaryRuler_deadlineStep f)).comp
      (UnaryRuler.unpairSnd.pair UnaryRuler.unpairFst.succ)).of_eq (fun z => by simp)
  exact (hscan.ifZero (UnaryRuler.const 1) (UnaryRuler.const 0)).of_eq (fun z => by
    simp [deadlinePassed])

/-! ### Assembling the clock

The clock's one remaining ingredient is a *code* semi-deciding settlement.  It is isolated
as `SettlementSemiDecider` — a pure computability obligation with no market, economic or
limit content — and the clock is constructed from it, so building a patient clock reduces
entirely to inhabiting that structure (done below from `SettlementChecker`). -/

/-- A code semi-deciding **tolerance agreement**, stated semantically.

Prefer `SettlementChecker` and `PatientSettlementClock.ofChecker` below.  This structure's
`sound` field *states* the agreement bound, so a clock built from it has that bound
transported from an assumption rather than derived — a conclusion-in-hypothesis shape.  It
is kept because it is the honest general interface (any semi-decider will do, however
obtained), and because `ofChecker` factors through it; but the concrete route derives both
fields as theorems.  See `settlementTest_iff_agree`.

Neither field mentions `truth`: a checker cannot compute a limit over the completed
theory, and does not need to. -/
structure SettlementSemiDecider (As : ℕ → AffineCombination) (P : History)
    (DP : DeductiveProcess) (tol : ℕ → ℚ) where
  code : Nat.Partrec.Code
  sound : ∀ i j F, acceptsWithin code F (Nat.pair i j) = true →
    ∀ v w : PCWorld, v.ConsistentWith (DP.D j) → w.ConsistentWith (DP.D j) →
      |(As i).value P v.payout - (As i).value P w.payout| ≤ ((tol i : ℚ) : ℝ)
  complete : ∀ i j, (∀ v w : PCWorld, v.ConsistentWith (DP.D j) →
      w.ConsistentWith (DP.D j) →
      |(As i).value P v.payout - (As i).value P w.payout| ≤ ((tol i : ℚ) : ℝ)) →
    ∃ F, acceptsWithin code F (Nat.pair i j) = true

private lemma orNot_eq_false_iff (a b : Bool) :
    ((!a) || (!b)) = false ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp

/-- **The patient settlement clock, constructed.**  Given a semi-decider for agreement
within `tol` and approximate completed-theory determination with error `e`, the clock
exists: activity is the deadline under-approximation OR'd with the dovetail's failure to
certify agreement.  The clock's residual error is `tol + e` — the checker's tolerance plus
the determination error — reported through any upper bound `err`.  `hreach` is what makes
the dovetail *fire*: some finite stage must already confine the plausible worlds' values to
within `tol i`.  It holds at `tol = 0` under exact determination
(`exists_settled_stage`), and at any `tol i > 2 * e i` under approximate determination
(`exists_agree_stage`). -/
noncomputable def PatientSettlementClock.ofSemiDecider
    {As : ℕ → AffineCombination} {P : History} {DP : DeductiveProcess}
    {truth e err : ℕ → ℝ} {tol : ℕ → ℚ}
    (d : SettlementSemiDecider As P DP tol)
    (hdet : AffineCombination.ApproxDeterminedViaTheory As P DP truth e)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hreach : ∀ i, ∃ m, ∀ v w : PCWorld, v.ConsistentWith (DP.D m) →
      w.ConsistentWith (DP.D m) →
      |(As i).value P v.payout - (As i).value P w.payout| ≤ ((tol i : ℚ) : ℝ))
    (herr : ∀ i, ((tol i : ℚ) : ℝ) + e i ≤ err i)
    (f : DeferralFunction) :
    PatientSettlementClock As P DP truth err f where
  active i n := (!(deadlinePassed f i n)) || (!(dovetailFound d.code i n))
  active_codes := by
    obtain ⟨cdf, hdf⟩ := polyFueled_dovetailFound d.code
    have hflag : UnaryRuler (fun z ↦
        (if deadlinePassed f z.unpair.2 z.unpair.1 then 1 else 0) *
        (if dovetailFound d.code z.unpair.2 z.unpair.1 then 1 else 0)) :=
      (((unaryRuler_deadlinePassed f).comp
          (UnaryRuler.unpairSnd.pair UnaryRuler.unpairFst)).mul
        ((UnaryRuler.of_polyFueled hdf).comp
          (UnaryRuler.unpairSnd.pair UnaryRuler.unpairFst))).of_eq (fun z ↦ by simp)
    have hsel : PolyRatCodes (fun i : ℕ ↦ if i = 0 then (1 : ℚ) else 0) := by
      obtain ⟨c, hc⟩ := polyFueled_selectConst PolyFueled.id
        (Encodable.encode (1 : ℚ)) (Encodable.encode (0 : ℚ))
      exact ⟨c, hc.of_eq (fun i ↦ by split_ifs with h <;> simp [h])⟩
    refine ((DigitRatCodes.toMachine (DigitRatCodes.ofPolyRatCodes hsel)).comp hflag).of_eq
      (fun z ↦ ?_)
    by_cases h1 : deadlinePassed f z.unpair.2 z.unpair.1 = true <;>
      by_cases h2 : dovetailFound d.code z.unpair.2 z.unpair.1 = true <;>
      simp [h1, h2]
  antitone := by
    intro i n hactive
    by_contra hcon
    rw [Bool.not_eq_true] at hcon
    obtain ⟨hdp, hdf⟩ := (orNot_eq_false_iff _ _).1 hcon
    rw [(orNot_eq_false_iff _ _).2 ⟨deadlinePassed_mono f hdp,
      dovetailFound_mono d.code hdf⟩] at hactive
    exact Bool.false_ne_true hactive
  active_through_envelope := by
    intro i n hn
    by_contra hcon
    rw [Bool.not_eq_true] at hcon
    obtain ⟨hdp, -⟩ := (orNot_eq_false_iff _ _).1 hcon
    exact absurd hn (not_le.mpr (deadlinePassed_sound f hdp))
  eventually_inactive := by
    intro i
    obtain ⟨N1, hN1⟩ := deadlinePassed_eventually f i
    obtain ⟨m, hm⟩ := hreach i
    obtain ⟨F, hF⟩ := d.complete i m hm
    refine ⟨max N1 (max F m), fun n hn => ?_⟩
    refine (orNot_eq_false_iff _ _).2 ⟨hN1 n (le_trans (le_max_left _ _) hn), ?_⟩
    rw [dovetailFound_eq_true_iff]
    exact ⟨m, le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn,
      acceptsWithin_mono d.code
        (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn) hF⟩
  settled_of_inactive := by
    intro i n hinactive
    obtain ⟨hdp, hdf⟩ := (orNot_eq_false_iff _ _).1 hinactive
    refine ⟨deadlinePassed_sound f hdp, fun v hv => ?_⟩
    obtain ⟨j, hj, ha⟩ := (dovetailFound_eq_true_iff d.code i n).1 hdf
    exact le_trans (hdet.close_of_agree hworld i j ((tol i : ℚ) : ℝ) (d.sound i j n ha) v
      (fun φ hφ => hv φ (DP.mono_le hj hφ))) (herr i)

/-! ### The purely computational checker

`SettlementSemiDecider` above assumes a *semantic* property of a code.  `SettlementChecker`
instead assumes only that a code recognizes a **named decidable function** —
`SettlementTest`, which mentions no market, no `truth`, no worlds beyond the finite
enumeration — and *derives* soundness and completeness from `settlementTest_iff_agree`.
The residual assumption is then pure plumbing: "this program recognizes this decidable
predicate", carrying no semantics at all. -/

/-- A code recognizing the concrete decidable settlement test at tolerance `tol i`.

**Purely computational**: the spec relates a program to a `Bool`-valued function of
`⟨i,j⟩` and nothing else — no history, no `truth`, no market conclusion.
`SettlementTestBool` is exponential (it enumerates every bit list of length `B`), which is
exactly what the dovetail absorbs, so no efficiency is asked of `code`.

The **Bool** presentation is deliberate and load-bearing.  The equivalent `SettlementTest`
quantifies over `FiniteWorld B = Fin B → Bool` with `B` computed from the input — a
dependent family that `Computable` cannot decompose, so no code could be shown to
recognize it in that form.  `SettlementTestBool` ranges over `List Bool`, one
non-dependent `Primcodable` type; `settlementTestBool_iff` bridges them.

**No paper node.**  This carries no `Paper node` line, deliberately: it asks for a
recognizer and no runtime bound at all, so it renders neither `def:ec` nor any other node —
it is a repo-side computability interface, like its siblings `SettlementSemiDecider` and
`FamilyMaturitySemidecider`.  It stays inventoried and field-frozen because it is a data
premise of `SettlementChecker.ofComputations`, and the exemption is recorded in
`scripts/check-paper-nodes.sh`. -/
structure SettlementChecker (As : ℕ → AffineCombination) (Q : ℕ → Sentence → ℚ)
    (DP : DeductiveProcess) (tol : ℕ → ℚ) where
  code : Nat.Partrec.Code
  spec : ∀ i j, (∃ F, acceptsWithin code F (Nat.pair i j) = true) ↔
    (As i).SettlementTestBool Q (DP.D j) (tol i) = true

/-- A concrete checker yields a semi-decider: soundness and completeness are **derived**
from `settlementTest_iff_agree`, not assumed. -/
def SettlementChecker.toSemiDecider
    {As : ℕ → AffineCombination} {P : History} {DP : DeductiveProcess}
    {Q : ℕ → Sentence → ℚ} {tol : ℕ → ℚ} (chk : SettlementChecker As Q DP tol)
    (hQ : ∀ d φ, P d φ = (Q d φ : ℝ)) :
    SettlementSemiDecider As P DP tol where
  code := chk.code
  sound i j F ha :=
    ((As i).settlementTest_iff_agree P Q hQ (DP.D j) (tol i)).1
      (((As i).settlementTestBool_iff Q (DP.D j) (tol i)).1 ((chk.spec i j).1 ⟨F, ha⟩))
  complete i j hagree :=
    (chk.spec i j).2 (((As i).settlementTestBool_iff Q (DP.D j) (tol i)).2
      (((As i).settlementTest_iff_agree P Q hQ (DP.D j) (tol i)).2 hagree))

/-- **The patient settlement clock from a concrete checker.**  The only assumption is that
one program recognizes one decidable predicate; every semantic field of the clock —
including `settled_of_inactive` — is proved.  This is what makes the appendix's waiting
argument a construction rather than a hypothesis.
Kind `C` (composition); provenance (a) derived in-project.
Paper node: `app:prandaff` -/
noncomputable def PatientSettlementClock.ofChecker
    {As : ℕ → AffineCombination} {P : History} {DP : DeductiveProcess}
    {truth e err : ℕ → ℝ}
    {Q : ℕ → Sentence → ℚ} {tol : ℕ → ℚ} (chk : SettlementChecker As Q DP tol)
    (hdet : AffineCombination.ApproxDeterminedViaTheory As P DP truth e)
    (hQ : ∀ d φ, P d φ = (Q d φ : ℝ))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hreach : ∀ i, ∃ m, ∀ v w : PCWorld, v.ConsistentWith (DP.D m) →
      w.ConsistentWith (DP.D m) →
      |(As i).value P v.payout - (As i).value P w.payout| ≤ ((tol i : ℚ) : ℝ))
    (herr : ∀ i, ((tol i : ℚ) : ℝ) + e i ≤ err i)
    (f : DeferralFunction) :
    PatientSettlementClock As P DP truth err f :=
  PatientSettlementClock.ofSemiDecider (chk.toSemiDecider hQ) hdet hworld hreach herr f

end

end LogicalInduction
