/-
# The symbol-metered decode is primitive recursive (`Tok₃`, part 4)

The trading firm's compiler runs the symbol-metered decode (`unRpn`); with the
concrete `Primcodable Sentence` instance in scope the strong-recursion steps
assemble from standard combinators (`parseRpnC_prim`, `unRpn_prim`).

Paper node: `def:ec` (symbol-metered sentence slots).
-/
import LogicalInduction.Construction.Witnesses.DigitConditioning
import LogicalInduction.Framework.RpnEmission
import LogicalInduction.Framework.RpnComputation

namespace LogicalInduction

open Nat.Partrec (Code)
open Nat.Partrec.Code

attribute [local irreducible] Nat.sqrt


/-! ## Primitive recursion of the decode

The trading firm's compiler runs the symbol-metered decode; with the concrete
`Primcodable Sentence` instance in scope the strong-recursion steps assemble from
standard combinators. -/

private abbrev PCtx :=
  (List (Option (ℕ × List ℕ)) × ℕ) × (ℕ × List ℕ)

private lemma parseG_prim : Primrec parseG := by
  have hfuel : Primrec fun prev : List (Option (ℕ × List ℕ)) =>
      prev.length.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.list_length)
  have hts0 : Primrec fun p : List (Option (ℕ × List ℕ)) × ℕ =>
      Denumerable.ofNat (List ℕ) p.1.length.unpair.2 :=
    (Primrec.ofNat (List ℕ)).comp
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.list_length.comp Primrec.fst)))
  have hprev : Primrec fun x : PCtx => x.1.1 := Primrec.fst.comp Primrec.fst
  have hfuel' : Primrec fun x : PCtx => x.1.2 := Primrec.snd.comp Primrec.fst
  have ht : Primrec fun x : PCtx => x.2.1 := Primrec.fst.comp Primrec.snd
  have hrest : Primrec fun x : PCtx => x.2.2 := Primrec.snd.comp Primrec.snd
  have hbr0 : Primrec fun x : PCtx =>
      (some (Nat.pair 0 0 + 1, x.2.2) : Option (ℕ × List ℕ)) :=
    Primrec.option_some.comp ((Primrec.const (Nat.pair 0 0 + 1)).pair hrest)
  have hesc : Primrec fun x : PCtx =>
      x.2.2.head?.bind fun c =>
        if Encodable.encode (Encodable.decode (α := Sentence) c) = 0 then none
        else some (Encodable.encode (Encodable.decode (α := Sentence) c) - 1,
          x.2.2.tail) := by
    refine Primrec.option_bind (Primrec.list_head?.comp hrest) ?_
    have he : Primrec fun y : PCtx × ℕ =>
        Encodable.encode (Encodable.decode (α := Sentence) y.2) :=
      (Primrec.encdec.comp Primrec.snd).of_eq fun y => rfl
    exact (Primrec.ite (PrimrecRel.comp Primrec.eq he (Primrec.const 0))
      (Primrec.const none)
      (Primrec.option_some.comp ((Primrec.pred.comp he).pair
        (Primrec.list_tail.comp (hrest.comp Primrec.fst))))).to₂
  have hlook1 : Primrec fun x : PCtx =>
      ((x.1.1[Nat.pair x.1.2 (Encodable.encode x.2.2)]?).getD none) :=
    Primrec.option_getD.comp
      (Primrec.list_getElem?.comp hprev
        (Primrec₂.natPair.comp hfuel' (Primrec.encode.comp hrest)))
      (Primrec.const none)
  have hlook2 : Primrec fun y : PCtx × (ℕ × List ℕ) =>
      ((y.1.1.1[Nat.pair y.1.1.2 (Encodable.encode y.2.2)]?).getD none) :=
    Primrec.option_getD.comp
      (Primrec.list_getElem?.comp (hprev.comp Primrec.fst)
        (Primrec₂.natPair.comp (hfuel'.comp Primrec.fst)
          (Primrec.encode.comp (Primrec.snd.comp Primrec.snd))))
      (Primrec.const none)
  have hout : Primrec fun z : (PCtx × (ℕ × List ℕ)) × (ℕ × List ℕ) =>
      (some (Nat.pair z.1.1.2.1 (Nat.pair z.1.2.1 z.2.1) + 1, z.2.2) :
        Option (ℕ × List ℕ)) :=
    Primrec.option_some.comp
      ((Primrec.succ.comp (Primrec₂.natPair.comp
          (ht.comp (Primrec.fst.comp Primrec.fst))
          (Primrec₂.natPair.comp
            (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
            (Primrec.fst.comp Primrec.snd)))).pair
        (Primrec.snd.comp Primrec.snd))
  have hbin : Primrec fun x : PCtx =>
      ((x.1.1[Nat.pair x.1.2 (Encodable.encode x.2.2)]?).getD none).bind fun p =>
        ((x.1.1[Nat.pair x.1.2 (Encodable.encode p.2)]?).getD none).bind fun q =>
          some (Nat.pair x.2.1 (Nat.pair p.1 q.1) + 1, q.2) :=
    Primrec.option_bind hlook1 (Primrec.option_bind hlook2 hout.to₂).to₂
  have hatom : Primrec fun x : PCtx =>
      (some (Nat.pair 1 (x.2.1 - 5) + 1, x.2.2) : Option (ℕ × List ℕ)) :=
    Primrec.option_some.comp
      ((Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 1)
        (Primrec.nat_sub.comp ht (Primrec.const 5)))).pair hrest)
  have heqt : ∀ k : ℕ, PrimrecPred fun x : PCtx => x.2.1 = k := fun k =>
    PrimrecRel.comp Primrec.eq ht (Primrec.const k)
  have hbody : Primrec fun x : PCtx =>
      if x.2.1 = 0 then some (Nat.pair 0 0 + 1, x.2.2)
      else if x.2.1 = 1 then
        x.2.2.head?.bind fun c =>
          if Encodable.encode (Encodable.decode (α := Sentence) c) = 0 then none
          else some (Encodable.encode (Encodable.decode (α := Sentence) c) - 1,
            x.2.2.tail)
      else if x.2.1 = 2 ∨ x.2.1 = 3 ∨ x.2.1 = 4 then
        ((x.1.1[Nat.pair x.1.2 (Encodable.encode x.2.2)]?).getD none).bind fun p =>
          ((x.1.1[Nat.pair x.1.2 (Encodable.encode p.2)]?).getD none).bind fun q =>
            some (Nat.pair x.2.1 (Nat.pair p.1 q.1) + 1, q.2)
      else some (Nat.pair 1 (x.2.1 - 5) + 1, x.2.2) := by
    refine Primrec.ite (heqt 0) hbr0 ?_
    refine Primrec.ite (heqt 1) hesc ?_
    exact Primrec.ite ((heqt 2).or ((heqt 3).or (heqt 4))) hbin hatom
  have hinner : Primrec fun p : List (Option (ℕ × List ℕ)) × ℕ =>
      match Denumerable.ofNat (List ℕ) p.1.length.unpair.2 with
      | [] => (none : Option (ℕ × List ℕ))
      | t :: rest =>
          if t = 0 then some (Nat.pair 0 0 + 1, rest)
          else if t = 1 then
            rest.head?.bind fun c =>
              if Encodable.encode (Encodable.decode (α := Sentence) c) = 0 then
                none
              else some
                (Encodable.encode (Encodable.decode (α := Sentence) c) - 1,
                  rest.tail)
          else if t = 2 ∨ t = 3 ∨ t = 4 then
            ((p.1[Nat.pair p.2 (Encodable.encode rest)]?).getD none).bind
              fun q1 =>
                ((p.1[Nat.pair p.2 (Encodable.encode q1.2)]?).getD none).bind
                  fun q2 =>
                    some (Nat.pair t (Nat.pair q1.1 q2.1) + 1, q2.2)
          else some (Nat.pair 1 (t - 5) + 1, rest) :=
    (Primrec.list_casesOn hts0 (Primrec.const none) hbody.to₂).of_eq fun p => by
      rcases Denumerable.ofNat (List ℕ) p.1.length.unpair.2 with _ | ⟨t, rest⟩ <;>
        rfl
  refine (Primrec.option_some.comp
    (Primrec.nat_casesOn hfuel (Primrec.const none) hinner.to₂)).of_eq
    fun prev => ?_
  rw [parseG, parseGCore]
  cases hf : prev.length.unpair.1 with
  | zero => rfl
  | succ fuel' =>
      cases hts : Denumerable.ofNat (List ℕ) prev.length.unpair.2 with
      | nil => simp [hts]
      | cons t rest => simp [hts]

/-- The symbol-block parser is primitive recursive. -/
lemma parseRpnC_prim : Primrec₂ parseRpnC := by
  have hF : Primrec₂ (fun (_ : Unit) => parseF) :=
    Primrec.nat_strong_rec _ (parseG_prim.comp Primrec.snd).to₂
      fun _ n => parseG_spec n
  have hF1 : Primrec parseF := hF.comp (Primrec.const ()) Primrec.id
  have h2 : Primrec fun p : ℕ × List ℕ =>
      parseF (Nat.pair p.1 (Encodable.encode p.2)) :=
    hF1.comp (Primrec₂.natPair.comp Primrec.fst (Primrec.encode.comp Primrec.snd))
  exact h2.to₂.of_eq fun fuel ts => by
    rw [parseF, Nat.unpair_pair, Denumerable.ofNat_encode]

private abbrev UCtx := (List (List ℕ) × ℕ) × (ℕ × List ℕ)

private lemma unG_prim : Primrec unG := by
  have hfuel : Primrec fun prev : List (List ℕ) => prev.length.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.list_length)
  have hts0 : Primrec fun p : List (List ℕ) × ℕ =>
      Denumerable.ofNat (List ℕ) p.1.length.unpair.2 :=
    (Primrec.ofNat (List ℕ)).comp
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.list_length.comp Primrec.fst)))
  have hprev : Primrec fun x : UCtx => x.1.1 := Primrec.fst.comp Primrec.fst
  have hfuel' : Primrec fun x : UCtx => x.1.2 := Primrec.snd.comp Primrec.fst
  have ht : Primrec fun x : UCtx => x.2.1 := Primrec.fst.comp Primrec.snd
  have hrest : Primrec fun x : UCtx => x.2.2 := Primrec.snd.comp Primrec.snd
  have hlook : ∀ {γ : Type} [Primcodable γ]
      {fp : γ → List (List ℕ)} {ff : γ → ℕ} {fr : γ → List ℕ},
      Primrec fp → Primrec ff → Primrec fr →
      Primrec fun y : γ => ((fp y)[Nat.pair (ff y) (Encodable.encode (fr y))]?).getD
        ([] : List ℕ) := by
    intro γ _ fp ff fr hp hf hr
    exact Primrec.option_getD.comp
      (Primrec.list_getElem?.comp hp
        (Primrec₂.natPair.comp hf (Primrec.encode.comp hr)))
      (Primrec.const [])
  have hparse : Primrec fun x : UCtx => parseRpnC x.2.2.length x.2.2 :=
    parseRpnC_prim.comp (Primrec.list_length.comp hrest) hrest
  -- price branch
  have hbr0inner : Primrec fun y : UCtx × (ℕ × List ℕ) =>
      match y.2.2 with
      | [] => [0, y.2.1]
      | d :: r2 =>
          0 :: y.2.1 :: d ::
            ((y.1.1.1[Nat.pair y.1.1.2 (Encodable.encode r2)]?).getD []) := by
    have hnil : Primrec fun y : UCtx × (ℕ × List ℕ) => [0, y.2.1] :=
      Primrec.list_cons.comp (Primrec.const 0)
        (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
          (Primrec.const []))
    have hcons : Primrec fun z : (UCtx × (ℕ × List ℕ)) × (ℕ × List ℕ) =>
        0 :: z.1.2.1 :: z.2.1 ::
          ((z.1.1.1.1[Nat.pair z.1.1.1.2 (Encodable.encode z.2.2)]?).getD []) :=
      Primrec.list_cons.comp (Primrec.const 0)
        (Primrec.list_cons.comp
          (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
            (hlook (Primrec.fst.comp (Primrec.fst.comp
                (Primrec.fst.comp Primrec.fst)))
              (Primrec.snd.comp (Primrec.fst.comp
                (Primrec.fst.comp Primrec.fst)))
              (Primrec.snd.comp Primrec.snd))))
    exact (Primrec.list_casesOn (Primrec.snd.comp Primrec.snd) hnil
      hcons.to₂).of_eq fun y => by rcases y.2.2 with _ | ⟨d, r2⟩ <;> rfl
  have hbr0 : Primrec fun x : UCtx =>
      match parseRpnC x.2.2.length x.2.2 with
      | none => [0, 0]
      | some (e, r1) =>
          match r1 with
          | [] => [0, e]
          | d :: r2 =>
              0 :: e :: d ::
                ((x.1.1[Nat.pair x.1.2 (Encodable.encode r2)]?).getD []) :=
    (Primrec.option_casesOn hparse (Primrec.const [0, 0]) hbr0inner.to₂).of_eq
      fun x => by
        rcases parseRpnC x.2.2.length x.2.2 with _ | ⟨e, r1⟩
        · rfl
        rcases r1 with _ | ⟨d, r2⟩ <;> rfl
  -- trade branch
  have hbr6inner : Primrec fun y : UCtx × (ℕ × List ℕ) =>
      6 :: y.2.1 ::
        ((y.1.1.1[Nat.pair y.1.1.2 (Encodable.encode y.2.2)]?).getD []) :=
    Primrec.list_cons.comp (Primrec.const 6)
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
        (hlook (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.snd.comp Primrec.snd)))
  have hbr6 : Primrec fun x : UCtx =>
      match parseRpnC x.2.2.length x.2.2 with
      | none => [6, 0]
      | some (e, r1) =>
          6 :: e :: ((x.1.1[Nat.pair x.1.2 (Encodable.encode r1)]?).getD []) :=
    (Primrec.option_casesOn hparse (Primrec.const [6, 0]) hbr6inner.to₂).of_eq
      fun x => by rcases parseRpnC x.2.2.length x.2.2 with _ | ⟨e, r1⟩ <;> rfl
  -- opaque payload branches
  have hpayinner : ∀ tag : ℕ, Primrec fun z : UCtx × (ℕ × List ℕ) =>
      tag :: z.2.1 ::
        ((z.1.1.1[Nat.pair z.1.1.2 (Encodable.encode z.2.2)]?).getD []) := by
    intro tag
    exact Primrec.list_cons.comp (Primrec.const tag)
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
        (hlook (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.snd.comp Primrec.snd)))
  have hpay : ∀ tag : ℕ, Primrec fun x : UCtx =>
      match x.2.2 with
      | [] => [tag]
      | c :: r =>
          tag :: c :: ((x.1.1[Nat.pair x.1.2 (Encodable.encode r)]?).getD []) := by
    intro tag
    exact (Primrec.list_casesOn hrest (Primrec.const [tag])
      (hpayinner tag).to₂).of_eq fun x => by
        rcases x.2.2 with _ | ⟨c, r⟩ <;> rfl
  -- copy branch
  have hcopy : Primrec fun x : UCtx =>
      x.2.1 :: ((x.1.1[Nat.pair x.1.2 (Encodable.encode x.2.2)]?).getD []) :=
    Primrec.list_cons.comp ht (hlook hprev hfuel' hrest)
  have heqt : ∀ k : ℕ, PrimrecPred fun x : UCtx => x.2.1 = k := fun k =>
    PrimrecRel.comp Primrec.eq ht (Primrec.const k)
  have hbody : Primrec fun x : UCtx =>
      if x.2.1 = 0 then
        match parseRpnC x.2.2.length x.2.2 with
        | none => [0, 0]
        | some (e, r1) =>
            match r1 with
            | [] => [0, e]
            | d :: r2 =>
                0 :: e :: d ::
                  ((x.1.1[Nat.pair x.1.2 (Encodable.encode r2)]?).getD [])
      else if x.2.1 = 6 then
        match parseRpnC x.2.2.length x.2.2 with
        | none => [6, 0]
        | some (e, r1) =>
            6 :: e :: ((x.1.1[Nat.pair x.1.2 (Encodable.encode r1)]?).getD [])
      else if x.2.1 = 1 then
        match x.2.2 with
        | [] => [1]
        | c :: r =>
            1 :: c :: ((x.1.1[Nat.pair x.1.2 (Encodable.encode r)]?).getD [])
      else if x.2.1 = 7 then
        match x.2.2 with
        | [] => [7]
        | c :: r =>
            7 :: c :: ((x.1.1[Nat.pair x.1.2 (Encodable.encode r)]?).getD [])
      else x.2.1 :: ((x.1.1[Nat.pair x.1.2 (Encodable.encode x.2.2)]?).getD []) := by
    refine Primrec.ite (heqt 0) hbr0 ?_
    refine Primrec.ite (heqt 6) hbr6 ?_
    refine Primrec.ite (heqt 1) (hpay 1) ?_
    exact Primrec.ite (heqt 7) (hpay 7) hcopy
  have hinner : Primrec fun p : List (List ℕ) × ℕ =>
      match Denumerable.ofNat (List ℕ) p.1.length.unpair.2 with
      | [] => ([] : List ℕ)
      | t :: rest =>
          if t = 0 then
            match parseRpnC rest.length rest with
            | none => [0, 0]
            | some (e, r1) =>
                match r1 with
                | [] => [0, e]
                | d :: r2 =>
                    0 :: e :: d ::
                      ((p.1[Nat.pair p.2 (Encodable.encode r2)]?).getD [])
          else if t = 6 then
            match parseRpnC rest.length rest with
            | none => [6, 0]
            | some (e, r1) =>
                6 :: e :: ((p.1[Nat.pair p.2 (Encodable.encode r1)]?).getD [])
          else if t = 1 then
            match rest with
            | [] => [1]
            | c :: r =>
                1 :: c :: ((p.1[Nat.pair p.2 (Encodable.encode r)]?).getD [])
          else if t = 7 then
            match rest with
            | [] => [7]
            | c :: r =>
                7 :: c :: ((p.1[Nat.pair p.2 (Encodable.encode r)]?).getD [])
          else t :: ((p.1[Nat.pair p.2 (Encodable.encode rest)]?).getD []) :=
    (Primrec.list_casesOn hts0 (Primrec.const []) hbody.to₂).of_eq fun p => by
      rcases Denumerable.ofNat (List ℕ) p.1.length.unpair.2 with _ | ⟨t, rest⟩ <;>
        rfl
  refine (Primrec.option_some.comp
    (Primrec.nat_casesOn hfuel
      ((Primrec.list_casesOn
        ((Primrec.ofNat (List ℕ)).comp
          (Primrec.snd.comp (Primrec.unpair.comp Primrec.list_length)))
        (Primrec.const []) (Primrec.const []).to₂).of_eq fun prev => by
          rcases Denumerable.ofNat (List ℕ) prev.length.unpair.2 with
            _ | ⟨t, rest⟩ <;> rfl)
      hinner.to₂)).of_eq fun prev => ?_
  rw [unG, unGCore]
  cases hf : prev.length.unpair.1 with
  | zero =>
      cases hts : Denumerable.ofNat (List ℕ) prev.length.unpair.2 with
      | nil => simp [hts]
      | cons t rest => simp [hts]
  | succ fuel' =>
      cases hts : Denumerable.ofNat (List ℕ) prev.length.unpair.2 with
      | nil => simp [hts]
      | cons t rest =>
          simp only [hts]
          rfl

/-- The stream contraction is primitive recursive. -/
lemma unRpn_prim : Primrec unRpn := by
  have hF : Primrec₂ (fun (_ : Unit) => unF) :=
    Primrec.nat_strong_rec _ (unG_prim.comp Primrec.snd).to₂
      fun _ n => unG_spec n
  have hF1 : Primrec unF := hF.comp (Primrec.const ()) Primrec.id
  have h2 : Primrec fun ts : List ℕ =>
      unF (Nat.pair ts.length (Encodable.encode ts)) :=
    hF1.comp (Primrec₂.natPair.comp Primrec.list_length Primrec.encode)
  exact h2.of_eq fun ts => by
    rw [unF, Nat.unpair_pair, Denumerable.ofNat_encode, ← unRpn_eq_unRpnTokensC]

#print axioms parseRpnC_prim
#print axioms unRpn_prim

end LogicalInduction
