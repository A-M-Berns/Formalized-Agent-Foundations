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

The deadline itself is undecidable.  A `DeferralFunction` (`def:deferralfunc`) guarantees fuel
polynomial in `f n` and not in `n`, so no machine can test "the deferral deadline has passed".
`deadlineRun` (`Properties/SelfTrust.lean`) / `deadlinePassed` is the sound
under-approximation that *can* be tested: it is monotone in the fuel, never true early, and
eventually true.  `polyFueled_dovetailFound`
(`Framework/Emission/Emission.lean`) discharges the paper's `DefinitelySettled` bullet
(tex:4872) over it.

## Objects

* `deadlineStep`, `deadlinePassed` — the under-approximated deadline over `deadlineRun`, with
  its soundness (`deadlinePassed_sound`), monotonicity and eventual-truth lemmas.
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

/-! ### The deadline under-approximation

`PatientSettlementClock` must keep component `i` active through `deferralEnvelope f i`, and
may only go inactive once that deadline has *provably* passed.  But `DeferralFunction`
guarantees only fuel polynomial in `f n` — **not** in `n` (the paper's "time polynomial in
`f(n)`", deliberately weaker since `f` may grow fast).  So `deferralEnvelope f i` is not
polynomial-time computable and the clock cannot decide the deadline exactly.

It does not need to.  `active_through_envelope` only requires activity to be *true* before
the deadline, so a **sound under-approximation** suffices: run `f`'s code on each `k ≤ i`
with budget `n` and certify only when every one halts with `f k < n`.  That is sound
(a halting run returns the true `f k`), monotone in `n` (`evaln_mono`), and eventually
fires (each `f k`, `k ≤ i`, is a fixed finite number).

`deadlineRun` and its soundness and monotonicity lemmas are stated beside `DeferralFunction`
itself, in `Properties/SelfTrust.lean`; the schedule built on them is shared with
`Construction/Quotation/`, and this module builds the clock out of them. -/

/-- The per-`k` failure test of the deadline check, indexed as `⟨⟨i,n⟩,k⟩`. -/
def deadlineStep (f : DeferralFunction) (z k : ℕ) : Bool :=
  decide ((1 - deadlineRun f z.unpair.2 k)
    + (deadlineRun f z.unpair.2 k - z.unpair.2) ≠ 0)

/-- Every `k ≤ i` has been certified `f k < n` within budget `n`. -/
def deadlinePassed (f : DeferralFunction) (i n : ℕ) : Bool :=
  boundedNone (deadlineStep f) (Nat.pair i n) i

lemma deadlinePassed_eq_true_iff (f : DeferralFunction) (i n : ℕ) :
    deadlinePassed f i n = true ↔
      ∀ k ≤ i, 0 < deadlineRun f n k ∧ deadlineRun f n k ≤ n := by
  rw [deadlinePassed, boundedNone_eq_true_iff]
  simp only [deadlineStep, Nat.unpair_pair, decide_eq_false_iff_not, not_not]
  constructor
  · intro h k hk; have := h k hk; omega
  · intro h k hk; have := h k hk; omega

lemma deferralEnvelope_lt_of_forall (f : DeferralFunction) (i n : ℕ)
    (h : ∀ k ≤ i, f.f k < n) : deferralEnvelope f i < n := by
  induction i with
  | zero => simpa [deferralEnvelope] using h 0 le_rfl
  | succ i ih =>
      simp only [deferralEnvelope, max_lt_iff]
      exact ⟨ih (fun k hk => h k (by omega)), h (i + 1) le_rfl⟩

/-- **Soundness**: certification implies the deadline really has passed. -/
lemma deadlinePassed_sound (f : DeferralFunction) {i n : ℕ}
    (h : deadlinePassed f i n = true) : deferralEnvelope f i < n := by
  refine deferralEnvelope_lt_of_forall f i n (fun k hk => ?_)
  obtain ⟨hpos, hle⟩ := (deadlinePassed_eq_true_iff f i n).1 h k hk
  rw [deadlineRun_eq f hpos] at hle
  omega

/-- **Monotone**: a larger budget preserves certification. -/
lemma deadlinePassed_mono (f : DeferralFunction) {i n : ℕ}
    (h : deadlinePassed f i n = true) : deadlinePassed f i (n + 1) = true := by
  rw [deadlinePassed_eq_true_iff] at h ⊢
  intro k hk
  obtain ⟨hpos, hle⟩ := h k hk
  rw [deadlineRun_mono f (Nat.le_succ n) hpos]
  exact ⟨hpos, by omega⟩

/-- **Eventual completion**: every component's deadline is eventually certified. -/
lemma deadlinePassed_eventually (f : DeferralFunction) (i : ℕ) :
    ∃ N, ∀ n, N ≤ n → deadlinePassed f i n = true := by
  obtain ⟨a, kk, hspec⟩ := f.fueled
  refine ⟨(Finset.range (i + 1)).sup
    (fun k => max (a * (f.f k + 1) ^ kk + a) (f.f k + 1)), fun n hn => ?_⟩
  rw [deadlinePassed_eq_true_iff]
  intro k hk
  have hmem : k ∈ Finset.range (i + 1) := Finset.mem_range.mpr (by omega)
  have hsup := Finset.le_sup (f := fun k => max (a * (f.f k + 1) ^ kk + a) (f.f k + 1)) hmem
  have hmono : Nat.Partrec.Code.evaln n f.code k = some (f.f k) :=
    Nat.Partrec.Code.evaln_mono (le_trans (le_trans (le_max_left _ _) hsup) hn) (hspec k)
  have hrun : deadlineRun f n k = f.f k + 1 := by
    simp [deadlineRun, codeEvalnNat, hmono]
  rw [hrun]
  have : f.f k + 1 ≤ n := le_trans (le_trans (le_max_right _ _) hsup) hn
  omega

/-- The deadline under-approximation is a polynomial Boolean table. -/
lemma polyFueled_deadlinePassed (f : DeferralFunction) :
    ∃ prog, PolyFueled prog
      (fun z => if deadlinePassed f z.unpair.1 z.unpair.2 then 1 else 0) := by
  obtain ⟨sim, hsim⟩ := codeEvalnNat_polyFueled f.code
  obtain ⟨cad, had⟩ := addc_polyFueled
  -- Inner step at `w = ⟨⟨i,n⟩,k⟩`: run `f` on `k` with budget `n`, then test `1 ≤ r ≤ n`.
  have hstep : ∃ p, PolyFueled p (fun w =>
      if deadlineStep f w.unpair.1 w.unpair.2 then 1 else 0) := by
    obtain ⟨cr, hr⟩ : ∃ p, PolyFueled p (fun w =>
        deadlineRun f w.unpair.1.unpair.2 w.unpair.2) :=
      ⟨_, (hsim.comp ((PolyFueled.right.comp PolyFueled.left).pair
        PolyFueled.right)).of_eq (fun w => by simp [deadlineRun])⟩
    obtain ⟨c1, h1⟩ : ∃ p, PolyFueled p (fun w =>
        1 - deadlineRun f w.unpair.1.unpair.2 w.unpair.2) :=
      ⟨_, (subc_polyFueled.comp ((PolyFueled.const 1).pair hr)).of_eq (fun w => by simp)⟩
    obtain ⟨c2, h2⟩ : ∃ p, PolyFueled p (fun w =>
        deadlineRun f w.unpair.1.unpair.2 w.unpair.2 - w.unpair.1.unpair.2) :=
      ⟨_, (subc_polyFueled.comp
        (hr.pair (PolyFueled.right.comp PolyFueled.left))).of_eq (fun w => by simp)⟩
    obtain ⟨cgap, hgap⟩ : ∃ p, PolyFueled p (fun w =>
        (1 - deadlineRun f w.unpair.1.unpair.2 w.unpair.2)
          + (deadlineRun f w.unpair.1.unpair.2 w.unpair.2 - w.unpair.1.unpair.2)) :=
      ⟨_, (had.comp (h1.pair h2)).of_eq (fun w => by simp)⟩
    obtain ⟨p, hp⟩ := polyFueled_selectConst hgap 0 1
    refine ⟨p, hp.of_eq (fun w => ?_)⟩
    by_cases hz : (1 - deadlineRun f w.unpair.1.unpair.2 w.unpair.2)
        + (deadlineRun f w.unpair.1.unpair.2 w.unpair.2 - w.unpair.1.unpair.2) = 0
    · have hf : deadlineStep f w.unpair.1 w.unpair.2 = false :=
        decide_eq_false (not_not_intro hz)
      rw [hf, if_pos hz]
      simp
    · have ht : deadlineStep f w.unpair.1 w.unpair.2 = true := decide_eq_true hz
      rw [ht, if_neg hz]
      simp
  obtain ⟨cn, hn⟩ := polyFueled_boundedNone (deadlineStep f) hstep
  refine ⟨_, (hn.comp (PolyFueled.id.pair PolyFueled.left)).of_eq (fun z => ?_)⟩
  simp [deadlinePassed, Nat.unpair_pair]

/-! ### Assembling the clock

The clock's one remaining ingredient is a *code* semi-deciding settlement.  It is isolated
as `SettlementSemiDecider` — a pure computability obligation with no market, economic or
limit content — and the clock is constructed from it, so building a patient clock reduces
entirely to inhabiting that structure (done below from `SettlementChecker`). -/

lemma acceptsWithin_mono (c : Nat.Partrec.Code) {F F' x : ℕ} (h : F ≤ F')
    (ha : acceptsWithin c F x = true) : acceptsWithin c F' x = true := by
  cases hev : Nat.Partrec.Code.evaln F c x with
  | none => simp [acceptsWithin, codeEvalnNat, hev] at ha
  | some out =>
      have hm : Nat.Partrec.Code.evaln F' c x = some out :=
        Nat.Partrec.Code.evaln_mono h hev
      simp only [acceptsWithin, codeEvalnNat, Nat.unpair_pair, hev, decide_eq_true_iff] at ha
      simp [acceptsWithin, codeEvalnNat, hm, ha]

lemma dovetailFound_mono (c : Nat.Partrec.Code) {i n : ℕ}
    (h : dovetailFound c i n = true) : dovetailFound c i (n + 1) = true := by
  rw [dovetailFound_eq_true_iff] at h ⊢
  obtain ⟨j, hj, ha⟩ := h
  exact ⟨j, by omega, acceptsWithin_mono c (Nat.le_succ n) ha⟩

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
    obtain ⟨cdp, hdp⟩ := polyFueled_deadlinePassed f
    obtain ⟨cdf, hdf⟩ := polyFueled_dovetailFound d.code
    obtain ⟨cml, hml⟩ := mul_polyFueled
    obtain ⟨cprod, hprod⟩ : ∃ c, PolyFueled c (fun w =>
        (if deadlinePassed f w.unpair.1 w.unpair.2 then 1 else 0) *
        (if dovetailFound d.code w.unpair.1 w.unpair.2 then 1 else 0)) :=
      ⟨_, (hml.comp (hdp.pair hdf)).of_eq (fun w => by simp)⟩
    obtain ⟨cswap, hswap⟩ : ∃ c, PolyFueled c (fun z =>
        (if deadlinePassed f z.unpair.2 z.unpair.1 then 1 else 0) *
        (if dovetailFound d.code z.unpair.2 z.unpair.1 then 1 else 0)) :=
      ⟨_, (hprod.comp (PolyFueled.right.pair PolyFueled.left)).of_eq (fun z => by simp)⟩
    obtain ⟨c, hc⟩ := polyFueled_selectConst hswap
      (Encodable.encode (1 : ℚ)) (Encodable.encode (0 : ℚ))
    refine ⟨c, hc.of_eq (fun z => ?_)⟩
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
Paper node: `def:ec` -/
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
