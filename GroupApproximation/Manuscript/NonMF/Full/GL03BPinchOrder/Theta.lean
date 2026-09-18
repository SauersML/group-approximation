import Mathlib.SetTheory.Cardinal.NatCard
import GroupApproximation.GGT.VanKampen.CombMapDual
import GroupApproximation.GGT.VanKampen.CombMapRestrictionPlanarity
import GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
import GroupApproximation.GGT.VanKampen.SurgeryReclosedConnected
import GroupApproximation.Meta.AxiomGuard

/-!
# The theta obstruction for two cyclic orders on one face

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Infrastructure for `thm:hull`
(non_mf_groups_exist.tex 2134, Hull's small cancellation theorem, through Osin's Lemma 9.7).

In a planar map, take three pairwise distinct darts `a, b, c`.  Let `S` be the set of the six
darts `a, b, c, α a, α b, α c`.  Suppose that, going around faces, the first dart of `S` after
`a` is `b` and after `b` is `c`, and also the first dart of `S` after `α a` is
`α b`, after `α b` is `α c`, after `α c` is `α a`.  Then the two triangles `a b c` and
`α a α b α c` are read in the same cyclic order, which is impossible on a sphere
(`false_of_theta`).

Proof: restrict the dual map to the three edges.  The restricted map has two vertices (the two
triangles), one face (`a ↦ α b ↦ c ↦ α a ↦ b ↦ α c ↦ a`) and at least two edges, so its Euler
characteristic is at most one.  It is connected, so it is planar as a restriction of the planar
dual (`CombMap.IsRestriction.planar`), which is a contradiction.

* `predRestr_sigma_val_of_firstHit`, `predRestr_facePerm_val_of_keep`: the rotation and the face
  permutation of a restriction to a dart predicate, at a dart whose first return is known.
* `faceCount_le_one_of`, `vertexCount_le_two_of`: counting orbits.
* `false_of_sixDarts`: the counting contradiction for six darts in two triangles.
* `false_of_theta`: the theta obstruction.
-/

namespace GroupApproximation.Full.GL03BPinchOrder

universe u

open Equiv
open GroupApproximation.GGT.VanKampen GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides

/-- Membership in a three-element list. -/
theorem eq_or_of_mem_three {α : Type*} {z a b c : α} (h : z ∈ [a, b, c]) :
    z = a ∨ z = b ∨ z = c := by
  rcases List.mem_cons.mp h with h | h
  · exact Or.inl h
  rcases List.mem_cons.mp h with h | h
  · exact Or.inr (Or.inl h)
  rcases List.mem_cons.mp h with h | h
  · exact Or.inr (Or.inr h)
  exact absurd h List.not_mem_nil

/-- One more step of a permutation stays in the same cycle. -/
theorem sameCycle_step {α : Type*} {f : Perm α} {x y z : α} (h : f.SameCycle x y)
    (e : f y = z) : f.SameCycle x z := by
  subst e
  exact Equiv.Perm.sameCycle_apply_right.mpr h

/-- **Rotation of a predicate restriction at a known first return.**  If the first dart of the
rotation orbit of `x` after `x` that satisfies `keep` is `y`, reached after `m` steps, then the
restricted rotation sends `x` to `y`.  (Osin, proof of Lemma 9.7(b); `thm:hull`.) -/
theorem predRestr_sigma_val_of_firstHit (M : CombMap.{u}) (keep : M.Dart → Prop)
    (hkeep : ∀ d, keep (M.alpha d) ↔ keep d) (x : {d // keep d}) {y : M.Dart} (hy : keep y)
    {m : ℕ} (hm : 0 < m) (hxy : (M.sigma ^ m) x.1 = y)
    (hskip : ∀ j, 0 < j → j < m → ¬ keep ((M.sigma ^ j) x.1)) :
    ((CombMap.PredicateRestriction.toCombMap M keep hkeep).sigma x).1 = y := by
  obtain ⟨m', hm', heq, hskip'⟩ :=
    (CombMap.PredicateRestriction.isRestriction M keep hkeep).sigma_firstReturn x
  have heq' : (M.sigma ^ m') x.1 =
      ((CombMap.PredicateRestriction.toCombMap M keep hkeep).sigma x).1 := heq
  rcases lt_trichotomy m m' with h | h | h
  · exact (hskip' m hm h ⟨⟨y, hy⟩, hxy.symm⟩).elim
  · subst h
    exact heq'.symm.trans hxy
  · have hk : keep ((M.sigma ^ m') x.1) := by
      rw [heq']
      exact ((CombMap.PredicateRestriction.toCombMap M keep hkeep).sigma x).2
    exact absurd hk (hskip m' hm' h)

/-- **Face permutation of a predicate restriction at a kept successor.**  If the ambient face
successor of a kept dart is kept, it is also the restricted face successor.  (Osin, proof of
Lemma 9.7(b); `thm:hull`.) -/
theorem predRestr_facePerm_val_of_keep (M : CombMap.{u}) (keep : M.Dart → Prop)
    (hkeep : ∀ d, keep (M.alpha d) ↔ keep d) (x : {d // keep d})
    (h : keep (M.facePerm x.1)) :
    ((CombMap.PredicateRestriction.toCombMap M keep hkeep).facePerm x).1 = M.facePerm x.1 :=
  predRestr_sigma_val_of_firstHit M keep hkeep
    ((CombMap.PredicateRestriction.toCombMap M keep hkeep).alpha x) h Nat.one_pos
    (congrArg (fun p : Perm M.Dart => p (M.alpha x.1)) (pow_one M.sigma))
    (fun j hj hjm => absurd hjm (by omega))

/-- A map all of whose darts lie in one face cycle has at most one face. -/
theorem faceCount_le_one_of (R : CombMap.{u}) (p : R.Dart)
    (h : ∀ d, R.facePerm.SameCycle p d) : R.faceCount ≤ 1 := by
  have hsub : Subsingleton R.Face := by
    refine ⟨fun f g => ?_⟩
    obtain ⟨d, rfl⟩ := Quotient.exists_rep f
    obtain ⟨e, rfl⟩ := Quotient.exists_rep g
    exact ((R.faceOf_eq_iff p d).mpr (h d)).symm.trans ((R.faceOf_eq_iff p e).mpr (h e))
  have h1 : Nat.card R.Face ≤ 1 := Finite.card_le_one_iff_subsingleton.mpr hsub
  exact h1

/-- A map all of whose darts lie in one of two rotation cycles has at most two vertices. -/
theorem vertexCount_le_two_of (R : CombMap.{u}) (p q : R.Dart)
    (h : ∀ d, R.sigma.SameCycle p d ∨ R.sigma.SameCycle q d) : R.vertexCount ≤ 2 := by
  have hsurj : Function.Surjective
      (fun t : Bool => cond t (R.vertexOf p) (R.vertexOf q)) := by
    intro v
    obtain ⟨d, rfl⟩ := Quotient.exists_rep v
    rcases h d with hd | hd
    · exact ⟨true, (R.vertexOf_eq_iff p d).mpr hd⟩
    · exact ⟨false, (R.vertexOf_eq_iff q d).mpr hd⟩
  have hle : Nat.card R.Vertex ≤ Nat.card Bool := Nat.card_le_card_of_surjective _ hsurj
  have hb : Nat.card Bool = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_bool]
  exact hle.trans hb.le

/-- **Two triangles read in the same order contradict planarity.**  A map on at most six darts
`A₀ B₀ C₀ A₁ B₁ C₁`, with `α A₀ = A₁`, `α B₀ = B₁`, `α C₀ = C₁`, rotation steps
`A₀ ↦ B₀ ↦ C₀` and `A₁ ↦ B₁ ↦ C₁ ↦ A₁`, and `A₀ B₀ C₀` pairwise distinct, has one face, at
most two vertices and at least two edges, so it is not planar; if every connected such map is
planar, this is a contradiction.  (Osin, proof of Lemma 9.7(b); `thm:hull`.) -/
theorem false_of_sixDarts (R : CombMap.{u}) (hplanar : R.IsConnected → R.IsPlanar)
    (A0 B0 C0 A1 B1 C1 : R.Dart)
    (hall : ∀ d, d = A0 ∨ d = B0 ∨ d = C0 ∨ d = A1 ∨ d = B1 ∨ d = C1)
    (hab : A0 ≠ B0) (hbc : B0 ≠ C0) (hac : A0 ≠ C0)
    (hαA : R.alpha A0 = A1) (hαB : R.alpha B0 = B1) (hαC : R.alpha C0 = C1)
    (hA0 : R.sigma A0 = B0) (hB0 : R.sigma B0 = C0)
    (hA1 : R.sigma A1 = B1) (hB1 : R.sigma B1 = C1) (hC1 : R.sigma C1 = A1) : False := by
  have e1 : R.facePerm A0 = B1 := by
    change R.sigma (R.alpha A0) = B1
    rw [hαA, hA1]
  have e2 : R.facePerm B1 = C0 := by
    change R.sigma (R.alpha B1) = C0
    rw [← hαB, R.alpha_involutive B0, hB0]
  have e3 : R.facePerm C0 = A1 := by
    change R.sigma (R.alpha C0) = A1
    rw [hαC, hC1]
  have e4 : R.facePerm A1 = B0 := by
    change R.sigma (R.alpha A1) = B0
    rw [← hαA, R.alpha_involutive A0, hA0]
  have e5 : R.facePerm B0 = C1 := by
    change R.sigma (R.alpha B0) = C1
    rw [hαB, hB1]
  have f1 : R.facePerm.SameCycle A0 B1 := sameCycle_step Equiv.Perm.SameCycle.rfl e1
  have f2 : R.facePerm.SameCycle A0 C0 := sameCycle_step f1 e2
  have f3 : R.facePerm.SameCycle A0 A1 := sameCycle_step f2 e3
  have f4 : R.facePerm.SameCycle A0 B0 := sameCycle_step f3 e4
  have f5 : R.facePerm.SameCycle A0 C1 := sameCycle_step f4 e5
  have hface : ∀ d, R.facePerm.SameCycle A0 d := by
    intro d
    rcases hall d with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [Equiv.Perm.SameCycle.rfl, f4, f2, f3, f1, f5]
  have v1 : R.sigma.SameCycle A0 B0 := sameCycle_step Equiv.Perm.SameCycle.rfl hA0
  have v2 : R.sigma.SameCycle A0 C0 := sameCycle_step v1 hB0
  have v3 : R.sigma.SameCycle A1 B1 := sameCycle_step Equiv.Perm.SameCycle.rfl hA1
  have v4 : R.sigma.SameCycle A1 C1 := sameCycle_step v3 hB1
  have hvert : ∀ d, R.sigma.SameCycle A0 d ∨ R.sigma.SameCycle A1 d := by
    intro d
    rcases hall d with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [Or.inl Equiv.Perm.SameCycle.rfl, Or.inl v1, Or.inl v2,
      Or.inr Equiv.Perm.SameCycle.rfl, Or.inr v3, Or.inr v4]
  have hconn : R.IsConnected := fun d e =>
    R.eqvGen_of_sameCycle_facePerm ((hface d).symm.trans (hface e))
  have hE := R.euler_eq_two (hplanar hconn)
  have hF := faceCount_le_one_of R A0 hface
  have hV := vertexCount_le_two_of R A0 A1 hvert
  have hDE := R.dartCount_eq_two_mul_edgeCount
  have hnd : [A0, B0, C0].Nodup := by
    refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, List.nodup_singleton C0⟩⟩
    · intro h
      rcases List.mem_cons.mp h with h | h
      · exact hab h
      rcases List.mem_cons.mp h with h | h
      · exact hac h
      exact List.not_mem_nil h
    · intro h
      rcases List.mem_cons.mp h with h | h
      · exact hbc h
      exact List.not_mem_nil h
  have h3 : [A0, B0, C0].length ≤ Nat.card R.Dart := hnd.length_le_natCard
  have hlen : [A0, B0, C0].length = 3 := rfl
  have hdc : R.dartCount = Nat.card R.Dart := rfl
  omega

/-- The first dart of `S` strictly after `x` in the `p`-orbit of `x` is `y`. -/
abbrev FirstHit {α : Type*} (p : Perm α) (S : α → Prop) (x y : α) : Prop :=
  ∃ m, 0 < m ∧ (p ^ m) x = y ∧ ∀ j, 0 < j → j < m → ¬ S ((p ^ j) x)

/-- The six darts of the three edges of `a`, `b`, `c`. -/
abbrev SixDart (M : CombMap.{u}) (a b c z : M.Dart) : Prop :=
  z = a ∨ z = b ∨ z = c ∨ z = M.alpha a ∨ z = M.alpha b ∨ z = M.alpha c

/-- The darts kept by the restriction of the dual to the edges of `[a, b, c]` are the six darts.
-/
theorem sixDart_of_walkKeep_dual (M : CombMap.{u}) {a b c z : M.Dart}
    (hz : walkKeep M.dual [a, b, c] z) : SixDart M a b c z := by
  change z ∈ [a, b, c] ∨ M.alpha z ∈ [a, b, c] at hz
  rcases hz with hz | hz
  · rcases eq_or_of_mem_three hz with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  · have hz' : z = M.alpha (M.alpha z) := (M.alpha_involutive z).symm
    rcases eq_or_of_mem_three hz with h | h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inl (hz'.trans (congrArg M.alpha h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hz'.trans (congrArg M.alpha h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hz'.trans (congrArg M.alpha h))))))

/-- The six darts are kept by the restriction of the dual to the edges of `[a, b, c]`. -/
theorem walkKeep_dual_of_sixDart (M : CombMap.{u}) {a b c z : M.Dart}
    (hz : SixDart M a b c z) : walkKeep M.dual [a, b, c] z := by
  change z ∈ [a, b, c] ∨ M.alpha z ∈ [a, b, c]
  rcases hz with h | h | h | h | h | h
  · left
    rw [h]
    simp
  · left
    rw [h]
    simp
  · left
    rw [h]
    simp
  · right
    rw [h, M.alpha_involutive a]
    simp
  · right
    rw [h, M.alpha_involutive b]
    simp
  · right
    rw [h, M.alpha_involutive c]
    simp

/-- **The theta obstruction.**  In a planar map, three pairwise distinct darts `a, b, c` and their
reversals cannot be met by the face permutation, among these six darts, in the orders
`a → b → c` and `α a → α b → α c → α a` at the same time.  (Osin, proof of Lemma 9.7(b);
`thm:hull`, non_mf_groups_exist.tex 2134.) -/
theorem false_of_theta (M : CombMap.{u}) (hM : M.IsPlanar) {a b c : M.Dart}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (h1 : FirstHit M.facePerm (SixDart M a b c) a b)
    (h2 : FirstHit M.facePerm (SixDart M a b c) b c)
    (h4 : FirstHit M.facePerm (SixDart M a b c) (M.alpha a) (M.alpha b))
    (h5 : FirstHit M.facePerm (SixDart M a b c) (M.alpha b) (M.alpha c))
    (h6 : FirstHit M.facePerm (SixDart M a b c) (M.alpha c) (M.alpha a)) : False := by
  have hσ : ∀ (x y : M.Dart) (hx : walkKeep M.dual [a, b, c] x)
      (hy : walkKeep M.dual [a, b, c] y), FirstHit M.facePerm (SixDart M a b c) x y →
      (walkMap M.dual [a, b, c]).sigma ⟨x, hx⟩ = ⟨y, hy⟩ := by
    rintro x y hx hy ⟨m, hm, hxy, hskip⟩
    apply Subtype.ext
    exact predRestr_sigma_val_of_firstHit M.dual (walkKeep M.dual [a, b, c])
      (walkKeep_alpha M.dual [a, b, c]) ⟨x, hx⟩ hy hm hxy
      (fun j hj hjm hj' => hskip j hj hjm (sixDart_of_walkKeep_dual M hj'))
  have ka : walkKeep M.dual [a, b, c] a := walkKeep_dual_of_sixDart M (Or.inl rfl)
  have kb : walkKeep M.dual [a, b, c] b := walkKeep_dual_of_sixDart M (Or.inr (Or.inl rfl))
  have kc : walkKeep M.dual [a, b, c] c :=
    walkKeep_dual_of_sixDart M (Or.inr (Or.inr (Or.inl rfl)))
  have ka' : walkKeep M.dual [a, b, c] (M.alpha a) :=
    walkKeep_dual_of_sixDart M (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have kb' : walkKeep M.dual [a, b, c] (M.alpha b) :=
    walkKeep_dual_of_sixDart M (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have kc' : walkKeep M.dual [a, b, c] (M.alpha c) :=
    walkKeep_dual_of_sixDart M (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  have hall : ∀ d : (walkMap M.dual [a, b, c]).Dart,
      d = ⟨a, ka⟩ ∨ d = ⟨b, kb⟩ ∨ d = ⟨c, kc⟩ ∨ d = ⟨M.alpha a, ka'⟩ ∨
        d = ⟨M.alpha b, kb'⟩ ∨ d = ⟨M.alpha c, kc'⟩ := by
    rintro ⟨d, hd⟩
    rcases sixDart_of_walkKeep_dual M hd with h | h | h | h | h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr (Or.inl (Subtype.ext h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Subtype.ext h)))))
  exact false_of_sixDarts (walkMap M.dual [a, b, c])
    (fun hconn => (walkMap_isRestriction M.dual [a, b, c]).planar (M.dual_planar hM) hconn
      ⟨a, ka⟩)
    ⟨a, ka⟩ ⟨b, kb⟩ ⟨c, kc⟩ ⟨M.alpha a, ka'⟩ ⟨M.alpha b, kb'⟩ ⟨M.alpha c, kc'⟩ hall
    (fun h => hab (congrArg Subtype.val h)) (fun h => hbc (congrArg Subtype.val h))
    (fun h => hac (congrArg Subtype.val h)) rfl rfl rfl
    (hσ a b ka kb h1) (hσ b c kb kc h2)
    (hσ _ _ ka' kb' h4) (hσ _ _ kb' kc' h5) (hσ _ _ kc' ka' h6)

end GroupApproximation.Full.GL03BPinchOrder

#audit_axioms GroupApproximation.Full.GL03BPinchOrder.eq_or_of_mem_three
#audit_axioms GroupApproximation.Full.GL03BPinchOrder.sameCycle_step
#audit_axioms GroupApproximation.Full.GL03BPinchOrder.predRestr_sigma_val_of_firstHit
#audit_axioms GroupApproximation.Full.GL03BPinchOrder.predRestr_facePerm_val_of_keep
#audit_axioms GroupApproximation.Full.GL03BPinchOrder.faceCount_le_one_of
#audit_axioms GroupApproximation.Full.GL03BPinchOrder.vertexCount_le_two_of
#audit_axioms GroupApproximation.Full.GL03BPinchOrder.false_of_sixDarts
#audit_axioms GroupApproximation.Full.GL03BPinchOrder.sixDart_of_walkKeep_dual
#audit_axioms GroupApproximation.Full.GL03BPinchOrder.walkKeep_dual_of_sixDart
#audit_axioms GroupApproximation.Full.GL03BPinchOrder.false_of_theta
