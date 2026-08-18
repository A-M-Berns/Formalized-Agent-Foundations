import FactoredSpaces.ConditionalHistory

/-!
# Active trails and the `Z`-closure criterion

The graph-theoretic half of the direct proof of Proposition 5.5, the **`Z`-closure
criterion**: for vertices `s, t`,
`S_Z(s) ∩ S_Z(t) ≠ ∅` iff there is an active trail between `s` and `t` given `Z`.  The
easy direction decomposes an active trail at its colliders into forks; the hard direction
builds an active *walk* from a witness of the intersection and shortens it to a trail.

## The oriented-walk representation (`dd:owalk`)

`Digraph.Walk` and `Digraph.Trail` carry a bare `List V` and read collider status off
triples of consecutive indices, which is the right *statement* of d-separation but a poor
shape to build walks in.  All the work here happens instead in `Digraph.OWalk`, an
inductive walk that records each edge's orientation (`consF`: the edge points forwards,
away from the current vertex; `consB`: it points backwards, into the current vertex).
Activity is then a structural recursion carrying one `Bool` — whether the *preceding*
edge points into the current vertex, i.e. whether the vertex can be a collider:

* `OWalk.ActiveOpen Z b` — active, ignoring the condition at the terminal vertex;
* `OWalk.ActiveBi Z b c = ActiveOpen Z b ∧ vertCond Z (c && endDir b) t` — active with `b`
  the incoming flag at the initial vertex and `c` the outgoing flag at the terminal one.

In this shape `append` and `reverse` have clean activity lemmas
(`OWalk.activeBi_append`, `OWalk.activeBi_reverse`), which is what makes the gluing in
the hard direction and the shortcut in `exists_active_trail_of_active_walk` short.
`activeFrom_iff_activeBi` is the bridge back to `Walk.Active`; it needs acyclicity,
because only then is the orientation of a skeleton edge determined.

`OWalk` and the list helpers `ColliderFrom`/`ActiveFrom` (over the private index helper
`prevOf`) sit in the root
`Digraph` namespace but deliberately in this file rather than in `DSeparation.lean`
(`dd:owalk`): they are proof machinery for the `Z`-closure criterion, with no role in the
*statement* of d-separation, and `DSeparation.lean` is kept to the small readable surface
that Proposition 5.5 and the trust-surface read-through are checked against.
-/

universe u

namespace Digraph

variable {V : Type u} {G : Digraph V}

/-! ## Collider conditions -/

/-- The activity condition at a vertex of a walk, as a function of its collider status. -/
def vertCond (G : Digraph V) (Z : Finset V) : Bool → V → Prop
  | true, v => G.ColliderOK Z v
  | false, v => v ∉ Z

@[simp] lemma vertCond_true (Z : Finset V) (v : V) :
    G.vertCond Z true v ↔ G.ColliderOK Z v := Iff.rfl

@[simp] lemma vertCond_false (Z : Finset V) (v : V) :
    G.vertCond Z false v ↔ v ∉ Z := Iff.rfl

/-! ## Oriented walks -/

/-- An *oriented walk* from `s` to `t`: a walk in the skeleton that records, for each
step, whether the edge points forwards (`consF`) or backwards (`consB`). -/
inductive OWalk (G : Digraph V) : V → V → Type u
  | nil (v : V) : OWalk G v v
  | consF {u v w : V} : G.Adj u v → OWalk G v w → OWalk G u w
  | consB {u v w : V} : G.Adj v u → OWalk G v w → OWalk G u w

namespace OWalk

/-- The vertex list of an oriented walk. -/
def verts : {s t : V} → G.OWalk s t → List V
  | _, _, .nil v => [v]
  | s, _, .consF _ p => s :: p.verts
  | s, _, .consB _ p => s :: p.verts

/-- The number of edges. -/
def length : {s t : V} → G.OWalk s t → ℕ
  | _, _, .nil _ => 0
  | _, _, .consF _ p => p.length + 1
  | _, _, .consB _ p => p.length + 1

/-- Concatenation. -/
def append : {s m t : V} → G.OWalk s m → G.OWalk m t → G.OWalk s t
  | _, _, _, .nil _, q => q
  | _, _, _, .consF h p, q => .consF h (p.append q)
  | _, _, _, .consB h p, q => .consB h (p.append q)

/-- Reversal. -/
def reverse : {s t : V} → G.OWalk s t → G.OWalk t s
  | _, _, .nil v => .nil v
  | s, _, .consF h p => p.reverse.append (.consB h (.nil s))
  | s, _, .consB h p => p.reverse.append (.consF h (.nil s))

/-- `p.endDir b` is `true` iff the last edge of `p` points into its terminal vertex;
`b` is returned for the zero-edge walk. -/
def endDir : {s t : V} → G.OWalk s t → Bool → Bool
  | _, _, .nil _, b => b
  | _, _, .consF _ p, _ => p.endDir true
  | _, _, .consB _ p, _ => p.endDir false

/-- `p.headDir c` is `true` iff the first edge of `p` points into its initial vertex;
`c` is returned for the zero-edge walk. -/
def headDir : {s t : V} → G.OWalk s t → Bool → Bool
  | _, _, .nil _, c => c
  | _, _, .consF _ _, _ => false
  | _, _, .consB _ _, _ => true

/-- `p` is active given `Z`, *excluding* the condition at its terminal vertex; `b` is the
collider flag of the initial vertex (whether the preceding edge points into it). -/
def ActiveOpen : {s t : V} → G.OWalk s t → Finset V → Bool → Prop
  | _, _, .nil _, _, _ => True
  | s, _, .consF _ p, Z, _ => s ∉ Z ∧ p.ActiveOpen Z true
  | s, _, .consB _ p, Z, b => G.vertCond Z b s ∧ p.ActiveOpen Z false

/-- `p` is active given `Z`, with `b` the incoming-edge flag at the initial vertex and `c`
the outgoing-edge flag at the terminal vertex. -/
def ActiveBi {s t : V} (p : G.OWalk s t) (Z : Finset V) (b c : Bool) : Prop :=
  p.ActiveOpen Z b ∧ G.vertCond Z (c && p.endDir b) t

/-! ### Simp equations -/

@[simp] lemma verts_nil (v : V) : (OWalk.nil (G := G) v).verts = [v] := rfl
@[simp] lemma verts_consF {u v w : V} (h : G.Adj u v) (p : G.OWalk v w) :
    (OWalk.consF h p).verts = u :: p.verts := rfl
@[simp] lemma verts_consB {u v w : V} (h : G.Adj v u) (p : G.OWalk v w) :
    (OWalk.consB h p).verts = u :: p.verts := rfl

@[simp] lemma length_nil (v : V) : (OWalk.nil (G := G) v).length = 0 := rfl
@[simp] lemma length_consF {u v w : V} (h : G.Adj u v) (p : G.OWalk v w) :
    (OWalk.consF h p).length = p.length + 1 := rfl
@[simp] lemma length_consB {u v w : V} (h : G.Adj v u) (p : G.OWalk v w) :
    (OWalk.consB h p).length = p.length + 1 := rfl

@[simp] lemma nil_append {v t : V} (q : G.OWalk v t) : (OWalk.nil v).append q = q := rfl
@[simp] lemma consF_append {u v m t : V} (h : G.Adj u v) (p : G.OWalk v m) (q : G.OWalk m t) :
    (OWalk.consF h p).append q = .consF h (p.append q) := rfl
@[simp] lemma consB_append {u v m t : V} (h : G.Adj v u) (p : G.OWalk v m) (q : G.OWalk m t) :
    (OWalk.consB h p).append q = .consB h (p.append q) := rfl

@[simp] lemma endDir_nil (v : V) (b : Bool) : (OWalk.nil (G := G) v).endDir b = b := rfl
@[simp] lemma endDir_consF {u v w : V} (h : G.Adj u v) (p : G.OWalk v w) (b : Bool) :
    (OWalk.consF h p).endDir b = p.endDir true := rfl
@[simp] lemma endDir_consB {u v w : V} (h : G.Adj v u) (p : G.OWalk v w) (b : Bool) :
    (OWalk.consB h p).endDir b = p.endDir false := rfl

@[simp] lemma headDir_nil (v : V) (c : Bool) : (OWalk.nil (G := G) v).headDir c = c := rfl
@[simp] lemma headDir_consF {u v w : V} (h : G.Adj u v) (p : G.OWalk v w) (c : Bool) :
    (OWalk.consF h p).headDir c = false := rfl
@[simp] lemma headDir_consB {u v w : V} (h : G.Adj v u) (p : G.OWalk v w) (c : Bool) :
    (OWalk.consB h p).headDir c = true := rfl

@[simp] lemma activeOpen_nil (v : V) (Z : Finset V) (b : Bool) :
    (OWalk.nil (G := G) v).ActiveOpen Z b ↔ True := Iff.rfl
@[simp] lemma activeOpen_consF {u v w : V} (h : G.Adj u v) (p : G.OWalk v w)
    (Z : Finset V) (b : Bool) :
    (OWalk.consF h p).ActiveOpen Z b ↔ u ∉ Z ∧ p.ActiveOpen Z true := Iff.rfl
@[simp] lemma activeOpen_consB {u v w : V} (h : G.Adj v u) (p : G.OWalk v w)
    (Z : Finset V) (b : Bool) :
    (OWalk.consB h p).ActiveOpen Z b ↔ G.vertCond Z b u ∧ p.ActiveOpen Z false := Iff.rfl

lemma activeBi_nil (v : V) (Z : Finset V) (b c : Bool) :
    (OWalk.nil (G := G) v).ActiveBi Z b c ↔ G.vertCond Z (b && c) v := by
  simp [ActiveBi, Bool.and_comm]

lemma activeBi_consF {u v w : V} (h : G.Adj u v) (p : G.OWalk v w) (Z : Finset V) (b c : Bool) :
    (OWalk.consF h p).ActiveBi Z b c ↔ u ∉ Z ∧ p.ActiveBi Z true c := by
  simp [ActiveBi, and_assoc]

lemma activeBi_consB {u v w : V} (h : G.Adj v u) (p : G.OWalk v w) (Z : Finset V) (b c : Bool) :
    (OWalk.consB h p).ActiveBi Z b c ↔ G.vertCond Z b u ∧ p.ActiveBi Z false c := by
  simp [ActiveBi, and_assoc]

@[simp] lemma reverse_nil (v : V) : (OWalk.nil (G := G) v).reverse = .nil v := rfl
@[simp] lemma reverse_consF {u v w : V} (h : G.Adj u v) (p : G.OWalk v w) :
    (OWalk.consF h p).reverse = p.reverse.append (.consB h (.nil u)) := rfl
@[simp] lemma reverse_consB {u v w : V} (h : G.Adj v u) (p : G.OWalk v w) :
    (OWalk.consB h p).reverse = p.reverse.append (.consF h (.nil u)) := rfl

/-! ### Structural lemmas -/

lemma length_append : ∀ {s m : V} (p : G.OWalk s m) {t : V} (q : G.OWalk m t),
    (p.append q).length = p.length + q.length := by
  intro s m p
  induction p with
  | nil v => intro t q; simp
  | consF h p ih => intro t q; simp [ih]; omega
  | consB h p ih => intro t q; simp [ih]; omega

lemma verts_ne_nil : ∀ {s t : V} (p : G.OWalk s t), p.verts ≠ [] := by
  rintro s t (v | ⟨h, p⟩ | ⟨h, p⟩) <;> simp

lemma endDir_append : ∀ {s m : V} (p : G.OWalk s m) {t : V} (q : G.OWalk m t) (b : Bool),
    (p.append q).endDir b = q.endDir (p.endDir b) := by
  intro s m p
  induction p with
  | nil v => intro t q b; simp
  | consF h p ih => intro t q b; simp [ih]
  | consB h p ih => intro t q b; simp [ih]

lemma headDir_append : ∀ {s m : V} (p : G.OWalk s m) {t : V} (q : G.OWalk m t) (c : Bool),
    (p.append q).headDir c = p.headDir (q.headDir c) := by
  intro s m p
  induction p with
  | nil v => intro t q c; simp
  | consF h p _ => intro t q c; simp
  | consB h p _ => intro t q c; simp

lemma activeOpen_append : ∀ {s m : V} (p : G.OWalk s m) {t : V} (q : G.OWalk m t)
    (Z : Finset V) (b : Bool),
    (p.append q).ActiveOpen Z b ↔ p.ActiveOpen Z b ∧ q.ActiveOpen Z (p.endDir b) := by
  intro s m p
  induction p with
  | nil v => intro t q Z b; simp
  | consF h p ih => intro t q Z b; simp [ih]; tauto
  | consB h p ih => intro t q Z b; simp [ih]; tauto

lemma activeBi_append {s m t : V} (p : G.OWalk s m) (q : G.OWalk m t)
    (Z : Finset V) (b c : Bool) :
    (p.append q).ActiveBi Z b c ↔ p.ActiveOpen Z b ∧ q.ActiveBi Z (p.endDir b) c := by
  simp only [ActiveBi, activeOpen_append, endDir_append, and_assoc]

/-- The condition at the initial vertex of an active walk. -/
lemma vertCond_head_of_activeBi : ∀ {s t : V} {p : G.OWalk s t} {Z : Finset V} {b c : Bool},
    p.ActiveBi Z b c → G.vertCond Z (b && p.headDir c) s := by
  rintro s t (v | ⟨h, p⟩ | ⟨h, p⟩) Z b c hp
  · simpa [activeBi_nil] using hp
  · simp only [headDir_consF, Bool.and_false, vertCond_false]
    exact ((activeBi_consF _ _ _ _ _).1 hp).1
  · simpa using ((activeBi_consB _ _ _ _ _).1 hp).1

/-- Only the condition at the initial vertex depends on the incoming flag `b`. -/
lemma activeBi_of_vertCond_head : ∀ {s t : V} {p : G.OWalk s t} {Z : Finset V} {b b' c : Bool},
    p.ActiveBi Z b c → G.vertCond Z (b' && p.headDir c) s → p.ActiveBi Z b' c := by
  rintro s t (v | ⟨h, p⟩ | ⟨h, p⟩) Z b b' c hp hb
  · simpa [activeBi_nil] using hb
  · rw [activeBi_consF] at hp ⊢; exact hp
  · rw [activeBi_consB] at hp ⊢
    exact ⟨by simpa using hb, hp.2⟩

lemma endDir_reverse : ∀ {s t : V} (p : G.OWalk s t) (b : Bool),
    p.reverse.endDir b = p.headDir b := by
  rintro s t (v | ⟨h, p⟩ | ⟨h, p⟩) b <;> simp [endDir_append]

lemma activeBi_reverse : ∀ {s t : V} (p : G.OWalk s t) (Z : Finset V) (b c : Bool),
    p.reverse.ActiveBi Z b c ↔ p.ActiveBi Z c b := by
  intro s t p
  induction p with
  | nil v => intro Z b c; simp [activeBi_nil, Bool.and_comm]
  | consF h p ih =>
      intro Z b c
      have key := ih Z b true
      rw [ActiveBi, endDir_reverse, Bool.true_and] at key
      rw [reverse_consF, activeBi_append, activeBi_consB, activeBi_nil, endDir_reverse,
        activeBi_consF, ← key]
      simp only [Bool.false_and, vertCond_false]
      tauto
  | consB h p ih =>
      intro Z b c
      have key := ih Z b false
      rw [ActiveBi, endDir_reverse, Bool.false_and, vertCond_false] at key
      rw [reverse_consB, activeBi_append, activeBi_consF, activeBi_nil,
        activeBi_consB, ← key]
      simp only [Bool.true_and]
      tauto

/-- A walk that is active with its initial vertex flagged as a collider and whose final
edge points *away* from its terminal vertex contains a collider reachable from its
initial vertex by a directed path; hence its initial vertex is in `Z` or has a
descendant in `Z`. -/
lemma colliderOK_of_activeOpen : ∀ {s t : V} (p : G.OWalk s t) (Z : Finset V),
    p.ActiveOpen Z true → p.endDir true = false → G.ColliderOK Z s := by
  intro s t p
  induction p with
  | nil v => intro Z _ h; simp at h
  | consF h p ih =>
      intro Z hp hd
      simp only [endDir_consF] at hd
      rcases ih Z hp.2 hd with hv | ⟨z, hz, hanc⟩
      · exact Or.inr ⟨_, hv, Relation.TransGen.single h⟩
      · exact Or.inr ⟨z, hz, Relation.TransGen.head h hanc⟩
  | consB h p _ => intro Z hp _; exact hp.1

/-! ### The bridge to `Digraph.Walk` -/

lemma verts_head? : ∀ {s t : V} (p : G.OWalk s t), p.verts.head? = some s := by
  rintro s t (v | ⟨h, p⟩ | ⟨h, p⟩) <;> simp

lemma verts_getElem_zero : ∀ {s t : V} (p : G.OWalk s t), p.verts[0]? = some s := by
  rintro s t (v | ⟨h, p⟩ | ⟨h, p⟩) <;> simp

lemma verts_getLast? : ∀ {s t : V} (p : G.OWalk s t), p.verts.getLast? = some t := by
  intro s t p
  induction p with
  | nil v => simp
  | consF h p ih => rw [verts_consF, List.getLast?_cons_of_ne_nil (verts_ne_nil p)]; exact ih
  | consB h p ih => rw [verts_consB, List.getLast?_cons_of_ne_nil (verts_ne_nil p)]; exact ih

lemma isChain_verts : ∀ {s t : V} (p : G.OWalk s t), p.verts.IsChain G.Skel := by
  intro s t p
  induction p with
  | nil v => exact List.isChain_singleton v
  | consF h p ih =>
      rw [verts_consF, List.isChain_cons]
      refine ⟨fun y hy => ?_, ih⟩
      simp only [verts_head?, Option.mem_def, Option.some.injEq] at hy
      subst hy; exact Or.inl h
  | consB h p ih =>
      rw [verts_consB, List.isChain_cons]
      refine ⟨fun y hy => ?_, ih⟩
      simp only [verts_head?, Option.mem_def, Option.some.injEq] at hy
      subst hy; exact Or.inr h

/-- An oriented walk without repeated vertices is a trail. -/
def toTrail {s t : V} (p : G.OWalk s t) (h : p.verts.Nodup) : G.Trail s t :=
  ⟨p.verts, p.isChain_verts, p.verts_head?, p.verts_getLast?, h⟩

end OWalk

/-- Every walk carries an orientation. -/
lemma exists_owalk_of_chain : ∀ (l : List V) (s t : V), l.IsChain G.Skel → l.head? = some s →
    l.getLast? = some t → ∃ p : G.OWalk s t, p.verts = l := by
  intro l
  induction l with
  | nil => intro s t _ h _; simp at h
  | cons v l ih =>
      intro s t hc hh hl
      simp only [List.head?_cons, Option.some.injEq] at hh
      subst hh
      cases l with
      | nil =>
          simp only [List.getLast?_singleton, Option.some.injEq] at hl
          subst hl; exact ⟨.nil v, rfl⟩
      | cons w l' =>
          rw [List.isChain_cons] at hc
          have hsw : G.Skel v w := hc.1 w rfl
          rw [List.getLast?_cons_of_ne_nil (by simp)] at hl
          obtain ⟨q, hq⟩ := ih w t hc.2 rfl hl
          rcases hsw with h | h
          · exact ⟨.consF h q, by rw [OWalk.verts_consF, hq]⟩
          · exact ⟨.consB h q, by rw [OWalk.verts_consB, hq]⟩

lemma exists_owalk {s t : V} (w : G.Walk s t) : ∃ p : G.OWalk s t, p.verts = w.verts :=
  exists_owalk_of_chain w.verts s t w.chain w.head w.last

/-! ### Activity, read off the vertex list -/

/-- The vertex preceding index `k` of `l`, with `a?` standing for the (virtual) vertex
before the list. -/
private def prevOf (a? : Option V) (l : List V) : ℕ → Option V
  | 0 => a?
  | k + 1 => l[k]?

/-- Index `k` of `l` is a collider, with `a?` the vertex preceding the list. -/
def ColliderFrom (G : Digraph V) (a? : Option V) (l : List V) (k : ℕ) : Prop :=
  ∃ x y z, prevOf a? l k = some x ∧ l[k]? = some y ∧ l[k + 1]? = some z ∧ G.Adj x y ∧ G.Adj z y

/-- `l` is active given `Z`, with `a?` the vertex preceding the list. -/
def ActiveFrom (G : Digraph V) (Z : Finset V) (a? : Option V) (l : List V) : Prop :=
  ∀ k v, l[k]? = some v →
    (G.ColliderFrom a? l k → G.ColliderOK Z v) ∧ (¬ G.ColliderFrom a? l k → v ∉ Z)

private lemma prevOf_cons (a? : Option V) (v : V) (l : List V) (k : ℕ) :
    prevOf (some v) l k = prevOf a? (v :: l) (k + 1) := by
  cases k <;> simp [prevOf]

lemma colliderFrom_cons (a? : Option V) (v : V) (l : List V) (k : ℕ) :
    G.ColliderFrom (some v) l k ↔ G.ColliderFrom a? (v :: l) (k + 1) := by
  simp [ColliderFrom, ← prevOf_cons a? v l k]

lemma activeFrom_cons (Z : Finset V) (a? : Option V) (v : V) (l : List V) :
    G.ActiveFrom Z a? (v :: l) ↔
      ((G.ColliderFrom a? (v :: l) 0 → G.ColliderOK Z v) ∧
        (¬ G.ColliderFrom a? (v :: l) 0 → v ∉ Z)) ∧ G.ActiveFrom Z (some v) l := by
  constructor
  · intro h
    refine ⟨h 0 v (by simp), fun k w hw => ?_⟩
    rw [colliderFrom_cons a?]
    exact h (k + 1) w (by simpa using hw)
  · rintro ⟨h0, h⟩ k w hw
    cases k with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hw; subst hw; exact h0
    | succ k => rw [← colliderFrom_cons a?]; exact h k w (by simpa using hw)

lemma activeFrom_iff_activeBi (hG : G.IsAcyclic) (Z : Finset V) :
    ∀ {s t : V} (p : G.OWalk s t) (a? : Option V) (b : Bool),
      (∀ x, a? = some x → (b = true ↔ G.Adj x s)) → (a? = none → b = false) →
      (G.ActiveFrom Z a? p.verts ↔ p.ActiveBi Z b false) := by
  intro s t p
  induction p with
  | nil v =>
      intro a? b hb hn
      rw [OWalk.verts_nil, activeFrom_cons, OWalk.activeBi_nil, Bool.and_false, vertCond_false]
      have hcol : ¬ G.ColliderFrom a? [v] 0 := by
        rintro ⟨x, y, z, -, -, hz, -⟩; simp at hz
      simp only [hcol, false_implies, not_false_eq_true, true_implies, true_and]
      constructor
      · rintro ⟨h1, -⟩; exact h1
      · intro h; exact ⟨h, fun k w hw => by simp at hw⟩
  | @consF u v w h p ih =>
      intro a? b hb hn
      rw [OWalk.verts_consF, activeFrom_cons, OWalk.activeBi_consF]
      have hcol : ¬ G.ColliderFrom a? (u :: p.verts) 0 := by
        rintro ⟨x, y, z, -, hy, hz, -, hzy⟩
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hy
        simp only [zero_add, List.getElem?_cons_succ, p.verts_getElem_zero,
          Option.some.injEq] at hz
        subst hy; subst hz
        exact hG.not_adj_symm h hzy
      rw [ih (some u) true (by
        intro x hx
        simp only [Option.some.injEq] at hx
        subst hx
        simpa using h) (by simp)]
      simp only [hcol, false_implies, not_false_eq_true, true_implies, true_and]
  | @consB u v w h p ih =>
      intro a? b hb hn
      rw [OWalk.verts_consB, activeFrom_cons, OWalk.activeBi_consB]
      have hcol : G.ColliderFrom a? (u :: p.verts) 0 ↔ b = true := by
        constructor
        · rintro ⟨x, y, z, hx, hy, hz, hxy, -⟩
          simp only [prevOf] at hx
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hy
          subst hy
          exact (hb x hx).2 hxy
        · intro hbt
          rcases ha : a? with _ | x
          · exact absurd (hn ha) (by simp [hbt])
          · refine ⟨x, u, v, rfl, rfl, ?_, (hb x ha).1 hbt, h⟩
            simp only [zero_add, List.getElem?_cons_succ, p.verts_getElem_zero]
      rw [ih (some u) false (by
        intro x hx
        simp only [Option.some.injEq] at hx
        subst hx
        simp [hG.not_adj_symm h]) (by simp)]
      refine and_congr ?_ Iff.rfl
      cases b with
      | true => simp only [hcol, vertCond_true]; simp
      | false => simp only [hcol, vertCond_false]; simp

/-! ### Shortening an active walk to an active trail -/

namespace OWalk

lemma exists_split : ∀ {s t : V} (p : G.OWalk s t) {x : V}, x ∈ p.verts →
    ∃ (q₁ : G.OWalk s x) (q₂ : G.OWalk x t), p = q₁.append q₂ := by
  intro s t p
  induction p with
  | nil v =>
      intro x hx
      simp only [verts_nil, List.mem_singleton] at hx
      subst hx
      exact ⟨.nil _, .nil _, rfl⟩
  | @consF u v w h p ih =>
      intro x hx
      simp only [verts_consF, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨.nil _, .consF h p, rfl⟩
      · obtain ⟨r₁, r₂, hr⟩ := ih hx
        exact ⟨.consF h r₁, r₂, by rw [consF_append, ← hr]⟩
  | @consB u v w h p ih =>
      intro x hx
      simp only [verts_consB, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨.nil _, .consB h p, rfl⟩
      · obtain ⟨r₁, r₂, hr⟩ := ih hx
        exact ⟨.consB h r₁, r₂, by rw [consB_append, ← hr]⟩

lemma exists_repeat_split : ∀ {s t : V} (p : G.OWalk s t), ¬ p.verts.Nodup →
    ∃ (x : V) (q₁ : G.OWalk s x) (q₂ : G.OWalk x x) (q₃ : G.OWalk x t),
      p = q₁.append (q₂.append q₃) ∧ 0 < q₂.length := by
  intro s t p
  induction p with
  | nil v => intro hnd; exact absurd (List.nodup_singleton v) hnd
  | @consF u v w h p ih =>
      intro hnd
      simp only [verts_consF, List.nodup_cons, not_and_or, not_not] at hnd
      rcases hnd with hmem | hnd
      · obtain ⟨r₁, r₂, hr⟩ := exists_split p hmem
        exact ⟨u, .nil u, .consF h r₁, r₂, by rw [nil_append, consF_append, ← hr], by simp⟩
      · obtain ⟨x, r₁, r₂, r₃, hr, hlen⟩ := ih hnd
        exact ⟨x, .consF h r₁, r₂, r₃, by rw [consF_append, ← hr], hlen⟩
  | @consB u v w h p ih =>
      intro hnd
      simp only [verts_consB, List.nodup_cons, not_and_or, not_not] at hnd
      rcases hnd with hmem | hnd
      · obtain ⟨r₁, r₂, hr⟩ := exists_split p hmem
        exact ⟨u, .nil u, .consB h r₁, r₂, by rw [nil_append, consB_append, ← hr], by simp⟩
      · obtain ⟨x, r₁, r₂, r₃, hr, hlen⟩ := ih hnd
        exact ⟨x, .consB h r₁, r₂, r₃, by rw [consB_append, ← hr], hlen⟩

/-- The one dangerous case of the shortcut argument: cutting a closed sub-walk out of an
active walk can only turn its base point into a collider if the removed sub-walk leaves
that point forwards and returns to it forwards, in which case the point has a descendant
in `Z`. -/
lemma vertCond_shortcut {x : V} {Z : Finset V} {q : G.OWalk x x} {e₁ h₃ hq : Bool}
    (hopen : q.ActiveOpen Z e₁) (hA : G.vertCond Z (e₁ && hq) x)
    (hB : G.vertCond Z (q.endDir e₁ && h₃) x) : G.vertCond Z (e₁ && h₃) x := by
  cases e₁ with
  | false => simpa using hA
  | true =>
      cases h₃ with
      | false => simpa using hB
      | true =>
          show G.ColliderOK Z x
          cases he : q.endDir true with
          | true => rw [he, Bool.and_true] at hB; exact hB
          | false => exact colliderOK_of_activeOpen q Z hopen he

lemma exists_nodup (Z : Finset V) : ∀ (n : ℕ) {s t : V} (p : G.OWalk s t), p.length = n →
    p.ActiveBi Z false false →
    ∃ q : G.OWalk s t, q.ActiveBi Z false false ∧ q.verts.Nodup := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s t p hn hp
    by_cases hnd : p.verts.Nodup
    · exact ⟨p, hp, hnd⟩
    obtain ⟨x, q₁, q₂, q₃, hq, hpos⟩ := exists_repeat_split p hnd
    subst hq
    rw [activeBi_append] at hp
    obtain ⟨h1, hp23⟩ := hp
    have hA := vertCond_head_of_activeBi hp23
    rw [headDir_append] at hA
    rw [activeBi_append] at hp23
    obtain ⟨h2, h3⟩ := hp23
    have hB := vertCond_head_of_activeBi h3
    have key : G.vertCond Z (q₁.endDir false && q₃.headDir false) x :=
      vertCond_shortcut h2 hA hB
    have hnew : (q₁.append q₃).ActiveBi Z false false :=
      (activeBi_append q₁ q₃ Z false false).2 ⟨h1, activeBi_of_vertCond_head h3 key⟩
    refine ih ((q₁.append q₃).length) ?_ (q₁.append q₃) rfl hnew
    rw [← hn, length_append, length_append, length_append]
    omega

end OWalk

lemma isColliderAt_iff {s t : V} (w : G.Walk s t) (k : ℕ) :
    w.IsColliderAt k ↔ G.ColliderFrom none w.verts k := by
  cases k with
  | zero =>
      constructor
      · rintro ⟨a, b, c, h1, h2, h3, hk, h5, h6⟩; exact absurd hk (by simp)
      · rintro ⟨x, y, z, hx, hy, hz, h1, h2⟩; simp [prevOf] at hx
  | succ k =>
      simp only [Walk.IsColliderAt, ColliderFrom, prevOf, Nat.add_sub_cancel]
      constructor
      · rintro ⟨a, b, c, ha, hb, hc, -, h1, h2⟩; exact ⟨a, b, c, ha, hb, hc, h1, h2⟩
      · rintro ⟨a, b, c, ha, hb, hc, h1, h2⟩
        exact ⟨a, b, c, ha, hb, hc, Nat.succ_pos k, h1, h2⟩

lemma walk_active_iff {s t : V} (w : G.Walk s t) (Z : Finset V) :
    w.Active Z ↔ G.ActiveFrom Z none w.verts := by
  constructor
  · intro h k v hv
    exact ⟨fun hc => (h k v hv).1 ((isColliderAt_iff w k).2 hc),
      fun hc => (h k v hv).2 fun hc' => hc ((isColliderAt_iff w k).1 hc')⟩
  · intro h k v hv
    exact ⟨fun hc => (h k v hv).1 ((isColliderAt_iff w k).1 hc),
      fun hc => (h k v hv).2 fun hc' => hc ((isColliderAt_iff w k).2 hc')⟩

lemma exists_trail_of_owalk (hG : G.IsAcyclic) {s t : V} {Z : Finset V} (p : G.OWalk s t)
    (hp : p.ActiveBi Z false false) : ∃ q : G.Trail s t, q.Active Z := by
  obtain ⟨r, hr, hnd⟩ := OWalk.exists_nodup Z p.length p rfl hp
  refine ⟨r.toTrail hnd, ?_⟩
  rw [Trail.Active, walk_active_iff]
  exact (activeFrom_iff_activeBi hG Z r none false (by simp) fun _ => rfl).2 hr

/-! ## Directed pieces of a walk -/

lemma exists_ascWalk {Z : Finset V} : ∀ {m w : V}, m ∈ G.unblockedAnc Z w →
    ∃ p : G.OWalk m w, (∀ b : Bool, p.ActiveOpen Z b) ∧ p.endDir true = true ∧
      (m ≠ w → ∀ b : Bool, p.endDir b = true) := by
  intro m w h
  refine Relation.ReflTransGen.head_induction_on
    (motive := fun a (_ : Relation.ReflTransGen (fun a b => G.Adj a b ∧ a ∉ Z) a w) =>
      ∃ p : G.OWalk a w, (∀ b : Bool, p.ActiveOpen Z b) ∧ p.endDir true = true ∧
        (a ≠ w → ∀ b : Bool, p.endDir b = true)) h ?_ ?_
  · exact ⟨.nil w, fun _ => trivial, rfl, fun hne => absurd rfl hne⟩
  · intro a c hr _ ih
    obtain ⟨p, hopen, hend, -⟩ := ih
    exact ⟨.consF hr.1 p, fun _ => ⟨hr.2, hopen true⟩, hend, fun _ _ => hend⟩

lemma exists_descWalk {Z : Finset V} : ∀ {w u : V}, u ∈ G.unblockedAnc Z w →
    ∃ p : G.OWalk w u, (∀ b : Bool, G.vertCond Z b w → p.ActiveOpen Z b) ∧
      p.endDir false = false ∧ (u ≠ w → ∀ b : Bool, p.endDir b = false) := by
  intro w u h
  replace h : Relation.ReflTransGen (fun a b => G.Adj a b ∧ a ∉ Z) u w := h
  induction h with
  | refl => exact ⟨.nil u, fun _ _ => trivial, rfl, fun hne => absurd rfl hne⟩
  | tail _ hr ih =>
      obtain ⟨p, hopen, hend, -⟩ := ih
      exact ⟨.consB hr.1 p, fun b hb => ⟨hb, hopen false hr.2⟩, hend, fun _ _ => hend⟩

/-! ## Active trail ⟹ the closures meet -/

/-- The invariant carried along an active walk: at a vertex whose incoming edge points
away from it, all of `A_Z` is inside `S`; at a vertex whose incoming edge points into it,
`A_Z` merely meets `S`. -/
def reachCond (G : Digraph V) (Z : Finset V) (S : Set V) : Bool → V → Prop
  | true, u => (G.unblockedAnc Z u ∩ S).Nonempty
  | false, u => G.unblockedAnc Z u ⊆ S

lemma reach_of_activeBi {Z : Finset V} {S : Set V} (hS : G.IsZClosed Z S) :
    ∀ {s t : V} (p : G.OWalk s t) (b : Bool), p.ActiveBi Z b false →
      G.reachCond Z S b s → (G.unblockedAnc Z t ∩ S).Nonempty := by
  intro s t p
  induction p with
  | nil v =>
      intro b _ hr
      cases b with
      | true => exact hr
      | false => exact ⟨v, mem_unblockedAnc_self Z v, hr (mem_unblockedAnc_self Z v)⟩
  | @consF u v w h p ih =>
      intro b hp hr
      rw [OWalk.activeBi_consF] at hp
      refine ih true hp.2 ?_
      cases b with
      | false => exact ⟨u, mem_unblockedAnc_of_adj hp.1 h, hr (mem_unblockedAnc_self Z u)⟩
      | true =>
          obtain ⟨m, hm1, hm2⟩ := hr
          exact ⟨m, unblockedAnc_subset_of_adj hp.1 h hm1, hm2⟩
  | @consB u v w h p ih =>
      intro b hp hr
      rw [OWalk.activeBi_consB] at hp
      have hvZ : v ∉ Z := by simpa using OWalk.vertCond_head_of_activeBi hp.2
      have hAu : G.unblockedAnc Z u ⊆ S := by
        cases b with
        | false => exact hr
        | true => exact unblockedAnc_subset_of_colliderOK hS hp.1 hr
      exact ih false hp.2 ((unblockedAnc_subset_of_adj hvZ h).trans hAu)

/-! ## The closures meet ⟹ an active trail exists -/

section
variable [DecidableEq V]

/-- Every vertex of `S_Z(s)` carries an active walk from `s` to it whose terminal condition
is the one the vertex gets when the walk is continued *into* it. -/
lemma exists_cert {Z : Finset V} {s : V} (hs : s ∉ Z) :
    ∀ u ∈ G.zClosure Z s, ∃ p : G.OWalk s u, p.ActiveBi Z false true := by
  refine zClosure_induction ?_ ?_
  · intro u hu
    obtain ⟨p, hopen, hend, -⟩ := exists_descWalk hu
    have huZ : u ∉ Z := by
      by_cases h : u = s
      · exact h ▸ hs
      · exact not_mem_of_mem_unblockedAnc hu h
    refine ⟨p, hopen false hs, ?_⟩
    rw [hend]
    exact huZ
  · rintro w hw u hu ⟨m, hm, pm, hpm⟩
    have hPw : ∃ q : G.OWalk s w, q.ActiveBi Z false true ∧ q.endDir false = true := by
      by_cases hmw : m = w
      · subst hmw
        refine ⟨pm, hpm, ?_⟩
        by_contra hd
        simp only [Bool.not_eq_true] at hd
        have h2 := hpm.2
        rw [hd] at h2
        exact h2 hw
      · obtain ⟨asc, haopen, -, haend⟩ := exists_ascWalk hm
        refine ⟨pm.append asc, ?_, ?_⟩
        · rw [OWalk.activeBi_append]
          refine ⟨hpm.1, haopen _, ?_⟩
          rw [haend hmw]
          exact Or.inl hw
        · rw [OWalk.endDir_append, haend hmw]
    obtain ⟨q, hq, hqend⟩ := hPw
    by_cases huw : u = w
    · exact ⟨huw ▸ q, huw ▸ hq⟩
    · obtain ⟨desc, hdopen, -, hdend⟩ := exists_descWalk hu
      have huZ : u ∉ Z := not_mem_of_mem_unblockedAnc hu huw
      refine ⟨q.append desc, ?_⟩
      rw [OWalk.activeBi_append, hqend]
      refine ⟨hq.1, hdopen true (Or.inl hw), ?_⟩
      rw [hdend huw]
      exact huZ

/-! ## The interface consumed by `Separation.lean` -/

section Interface

omit [DecidableEq V] in
/-- An active walk between `s` and `t` shortens to an active trail: d-separation may
equivalently be defined through walks. -/
lemma exists_active_trail_of_active_walk (hG : G.IsAcyclic) {s t : V} {Z : Finset V}
    (p : G.Walk s t) (hp : p.Active Z) : ∃ q : G.Trail s t, q.Active Z := by
  obtain ⟨r, hr⟩ := exists_owalk p
  refine exists_trail_of_owalk hG r ?_
  rw [walk_active_iff, ← hr] at hp
  exact (activeFrom_iff_activeBi hG Z r none false (by simp) fun _ => rfl).1 hp

/-- **Active trail ⟹ the closures meet.**  If some trail from `s` to `t` is active given
`Z`, then `S_Z(s) ∩ S_Z(t) ≠ ∅`.  (The easy direction of the `Z`-closure criterion: orient
the trail and read the meeting point off its decomposition at the colliders.) -/
lemma zClosure_inter_nonempty_of_active_trail (hG : G.IsAcyclic) {s t : V} {Z : Finset V}
    (p : G.Trail s t) (hp : p.Active Z) : (G.zClosure Z s ∩ G.zClosure Z t).Nonempty := by
  obtain ⟨r, hr⟩ := exists_owalk p.toWalk
  have hract : r.ActiveBi Z false false := by
    rw [Trail.Active, walk_active_iff, ← hr] at hp
    exact (activeFrom_iff_activeBi hG Z r none false (by simp) fun _ => rfl).1 hp
  have hs : s ∉ Z := by simpa using OWalk.vertCond_head_of_activeBi hract
  have ht : t ∉ Z := by simpa using hract.2
  obtain ⟨m, hm1, hm2⟩ :=
    reach_of_activeBi (isZClosed_zClosure Z s) r false hract (unblockedAnc_subset_zClosure hs)
  exact ⟨m, hm2, unblockedAnc_subset_zClosure ht hm1⟩

/-- **The closures meet ⟹ an active trail exists.**  If `S_Z(s) ∩ S_Z(t) ≠ ∅`, then some
trail from `s` to `t` is active given `Z`.  (The hard direction of the `Z`-closure
criterion: glue the two certificates at the meeting point into an active oriented walk and
shorten it to a trail.) -/
lemma exists_active_trail_of_zClosure_inter_nonempty (hG : G.IsAcyclic) {s t : V}
    {Z : Finset V} (h : (G.zClosure Z s ∩ G.zClosure Z t).Nonempty) :
    ∃ p : G.Trail s t, p.Active Z := by
  obtain ⟨u, hus, hut⟩ := h
  have hs : s ∉ Z := fun hsZ => by rw [zClosure_eq_empty hsZ] at hus; exact hus
  have ht : t ∉ Z := fun htZ => by rw [zClosure_eq_empty htZ] at hut; exact hut
  obtain ⟨p, hp⟩ := exists_cert hs u hus
  obtain ⟨p', hp'⟩ := exists_cert ht u hut
  have hd : G.vertCond Z (p.endDir false) u := by rw [← Bool.true_and (p.endDir false)]; exact hp.2
  have hd' : G.vertCond Z (p'.endDir false) u := by
    rw [← Bool.true_and (p'.endDir false)]; exact hp'.2
  have hcomb : G.vertCond Z (p.endDir false && p'.endDir false) u := by
    cases he : p.endDir false with
    | false => rw [he] at hd; exact hd
    | true =>
        cases he' : p'.endDir false with
        | false => rw [he'] at hd'; exact hd'
        | true => rw [he] at hd; exact hd
  refine exists_trail_of_owalk hG (p.append p'.reverse) ?_
  rw [OWalk.activeBi_append, OWalk.activeBi_reverse]
  exact ⟨hp.1, hp'.1, hcomb⟩

/-- **`Z`-closure criterion for d-separation**: `V₁` and `V₂` are d-separated given `V₃`
iff `S_{V₃}(V₁) ∩ S_{V₃}(V₂) = ∅`.  This is the set form of the two lemmas above, and the
form Proposition 5.5 is assembled from. -/
lemma dSeparated_iff_disjoint_zClosureSet (hG : G.IsAcyclic) (V₁ V₂ V₃ : Finset V) :
    G.DSeparated V₁ V₂ V₃ ↔ Disjoint (G.zClosureSet V₃ V₁) (G.zClosureSet V₃ V₂) := by
  rw [Set.disjoint_left]
  constructor
  · intro h x hx1 hx2
    simp only [zClosureSet, Set.mem_iUnion, exists_prop] at hx1 hx2
    obtain ⟨s, hs, hxs⟩ := hx1
    obtain ⟨t, ht, hxt⟩ := hx2
    obtain ⟨q, hq⟩ := exists_active_trail_of_zClosure_inter_nonempty hG ⟨x, hxs, hxt⟩
    exact h s hs t ht q hq
  · intro h s hs t ht q hq
    obtain ⟨x, hx1, hx2⟩ := zClosure_inter_nonempty_of_active_trail hG q hq
    have m1 : x ∈ G.zClosureSet V₃ V₁ := by
      simp only [zClosureSet, Set.mem_iUnion, exists_prop]; exact ⟨s, hs, hx1⟩
    have m2 : x ∈ G.zClosureSet V₃ V₂ := by
      simp only [zClosureSet, Set.mem_iUnion, exists_prop]; exact ⟨t, ht, hx2⟩
    exact h m1 m2

/-! ## The local Markov property (graph side)

The d-separation the "I-map implies factorization" theorem of `PerfectMap.lean` consumes.
It is proved from the `Z`-closure criterion above rather than from trails, which is the
standing preference for new d-separation facts. -/

/-- **Local Markov property (graph side).**  A node `v` is d-separated, given its parents,
from every set `N` of nodes that are neither `v` nor descendants of `v`.  (Nodes of `N` may
be parents of `v`; those are blocked by the conditioning set itself.) -/
lemma dSeparated_singleton_parents [Fintype V] [DecidableRel G.Adj] (hG : G.IsAcyclic)
    (v : V) (N : Finset V) (hN : ∀ u ∈ N, u ≠ v ∧ ¬ G.IsAncestor v u) :
    G.DSeparated {v} N (G.parents v) := by
  rw [dSeparated_iff_disjoint_zClosureSet hG]
  have hclosed : G.IsZClosed (G.parents v) ({v} : Set V) := by
    rintro w hw ⟨m, hm1, hm2⟩
    rw [Set.mem_singleton_iff] at hm2
    subst hm2
    exact absurd hm1 (notMem_unblockedAnc_of_mem_parents hG hw)
  have hsub : G.zClosure (G.parents v) v ⊆ {v} :=
    zClosure_subset hclosed (unblockedAnc_parents_self (G := G) v).subset
  have hne : ∀ u ∈ N, v ∉ G.zClosure (G.parents v) u := by
    intro u hu hv
    obtain ⟨hune, hnanc⟩ := hN u hu
    refine zClosure_induction (P := fun m => m ≠ v) ?_ ?_ v hv rfl
    · rintro m hm rfl
      rcases Relation.reflTransGen_iff_eq_or_transGen.mp
        (Relation.ReflTransGen.mono (fun _ _ hab => hab.1) hm) with h | h
      · exact hune h
      · exact hnanc h
    · rintro w hw m hm _ rfl
      exact notMem_unblockedAnc_of_mem_parents hG hw hm
  rw [Set.disjoint_left]
  intro a ha hb
  obtain ⟨s, hs, has⟩ := Set.mem_iUnion₂.mp ha
  obtain ⟨t, ht, hat⟩ := Set.mem_iUnion₂.mp hb
  rw [Finset.mem_singleton] at hs
  subst hs
  rw [Set.mem_singleton_iff.mp (hsub has)] at hat
  exact hne t ht hat

end Interface

end

end Digraph
