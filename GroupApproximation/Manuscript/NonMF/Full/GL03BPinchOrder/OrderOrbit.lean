import GroupApproximation.Manuscript.NonMF.Full.GL03BPinchOrder.OrderRing
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFillWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# Face orbits of the ring map

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Infrastructure for `thm:hull`
(non_mf_groups_exist.tex 2134, Hull's small cancellation theorem, through Osin's Lemma 9.7).

In the ring map `ordRing hw hM` of a noncrossing closed walk `w`:
* the walk darts form one face orbit, read in the order of `w` (`ordRing_facePerm_pow_wd`,
  `wd_last`);
* the face orbit of a dart whose reversal is on `w` never meets a walk dart, and it follows
  the face orbit of the walk map (`lake_orbit`);
* the ring map is planar when the inner reclosing is (`ordRing_planar`).
-/

namespace GroupApproximation.Full.GL03BPinchOrder

universe u

open Equiv
open GroupApproximation.GGT.VanKampen GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
open GroupApproximation.GGT.VanKampen.Surgery.MapCollapse

/-- Equal indices give equal entries. -/
theorem getElem_idx_congr {α : Type*} (l : List α) {i j : ℕ} (h : i = j) (hi : i < l.length)
    (hj : j < l.length) : l[i] = l[j] := by
  subst h
  rfl

variable {M : CombMap.{u}} {w : List M.Dart}

/-- The face successor of `w[i]` in the ring map is `w[i + 1]`. -/
theorem wd_succ (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar) (i : ℕ)
    (hi : i < w.length) (hi1 : i + 1 < w.length) :
    (ordRing hw hM).facePerm (wd hw hM i hi) = wd hw hM (i + 1) hi1 :=
  ordRing_ext hw hM ((ordRing_facePerm_val_of_getElem hw hM _ i hi rfl).trans
    (getElem_idx_congr w (Nat.mod_eq_of_lt hi1) (Nat.mod_lt _ (by omega)) hi1))

/-- The face successor of the last walk dart in the ring map is the first walk dart. -/
theorem wd_last (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (hn : w.length - 1 < w.length) (h0 : 0 < w.length) :
    (ordRing hw hM).facePerm (wd hw hM (w.length - 1) hn) = wd hw hM 0 h0 :=
  ordRing_ext hw hM ((ordRing_facePerm_val_of_getElem hw hM _ _ hn rfl).trans
    (getElem_idx_congr w (by rw [Nat.sub_add_cancel (by omega : 1 ≤ w.length), Nat.mod_self])
      (Nat.mod_lt _ (by omega)) h0))

/-- Walking `s` steps along the walk darts in the ring map. -/
theorem ordRing_facePerm_pow_wd (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (t s : ℕ) (ht : t < w.length) (h : t + s < w.length) :
    ((ordRing hw hM).facePerm ^ s) (wd hw hM t ht) = wd hw hM (t + s) h := by
  induction s with
  | zero =>
    have e : ((ordRing hw hM).facePerm ^ 0) (wd hw hM t ht) = wd hw hM t ht := by
      rw [pow_zero, Perm.one_apply]
    exact e.trans (ordRing_ext hw hM (getElem_idx_congr w (Nat.add_zero t).symm ht h))
  | succ s ih =>
    have ih' := ih (by omega)
    rw [pow_succ', Perm.mul_apply, ih']
    exact (wd_succ hw hM (t + s) (by omega) (by omega)).trans
      (ordRing_ext hw hM (getElem_idx_congr w (Nat.add_assoc t s 1) (by omega) h))

/-- Every walk dart of the ring map has a walk dart before it. -/
theorem exists_wd_facePerm_eq (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar) (i : ℕ)
    (hi : i < w.length) :
    ∃ j, ∃ hj : j < w.length, (ordRing hw hM).facePerm (wd hw hM j hj) = wd hw hM i hi := by
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · exact ⟨w.length - 1, by omega, wd_last hw hM (by omega) hi⟩
  · refine ⟨i - 1, by omega, ?_⟩
    exact (wd_succ hw hM (i - 1) (by omega) (by omega)).trans
      (ordRing_ext hw hM (getElem_idx_congr w (Nat.sub_add_cancel hi0) (by omega) hi))

/-- **Lake darts stay lake darts.**  If the reversal of a ring-map dart is a walk dart, so is the
reversal of its face successor.  (Osin, proof of Lemma 9.7(b); `thm:hull`.) -/
theorem alpha_mem_facePerm (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (X : (ordRing hw hM).Dart) (hX : M.alpha X.1.1 ∈ w) :
    M.alpha ((ordRing hw hM).facePerm X).1.1 ∈ w := by
  have hk : ((ordRing hw hM).facePerm X).1.1 ∈ w ∨
      M.alpha ((ordRing hw hM).facePerm X).1.1 ∈ w := ((ordRing hw hM).facePerm X).2
  rcases hk with h | h
  · exfalso
    obtain ⟨i, hi, hieq⟩ := List.getElem_of_mem h
    obtain ⟨j, hj, hjeq⟩ := exists_wd_facePerm_eq hw hM i hi
    have hY : (ordRing hw hM).facePerm X = wd hw hM i hi := ordRing_ext hw hM hieq.symm
    have hXj : X = wd hw hM j hj := (ordRing hw hM).facePerm.injective (hY.trans hjeq.symm)
    have hmem : X.1.1 ∈ w := by
      rw [hXj]
      exact List.getElem_mem hj
    exact hw.alpha_not_mem _ hmem hX
  · exact h

/-- The start of a lake orbit, as a ring-map dart. -/
noncomputable def lakeStart (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (x₀ : (walkMap M w).Dart) : (ordRing hw hM).Dart :=
  ⟨⟨x₀.1, not_internal_of_walkKeep hw hM x₀.2⟩, x₀.2⟩

theorem lakeStart_val (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (x₀ : (walkMap M w).Dart) : (lakeStart hw hM x₀).1.1 = x₀.1 :=
  rfl

/-- **The lake orbit in the ring map.**  Starting at a dart whose reversal is on `w`, the face
orbit in the ring map has the same darts as the face orbit in the walk map, and all of them
have reversal on `w`.  (Osin, proof of Lemma 9.7(b); `thm:hull`.) -/
theorem lake_orbit (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (x₀ : (walkMap M w).Dart) (hx₀ : M.alpha x₀.1 ∈ w) (i : ℕ) :
    (((ordRing hw hM).facePerm ^ i) (lakeStart hw hM x₀)).1.1 =
        (((walkMap M w).facePerm ^ i) x₀).1 ∧
      M.alpha (((walkMap M w).facePerm ^ i) x₀).1 ∈ w := by
  induction i with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp only [pow_zero, Perm.one_apply] <;> rfl
    · simp only [pow_zero, Perm.one_apply] <;> exact hx₀
  | succ i ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hXa : M.alpha (((ordRing hw hM).facePerm ^ i) (lakeStart hw hM x₀)).1.1 ∈ w := by
      rw [ih1]
      exact ih2
    have hstep := ordRing_facePerm_val_of_alpha_mem hw hM _ hXa
    have hy : (⟨(((ordRing hw hM).facePerm ^ i) (lakeStart hw hM x₀)).1.1, Or.inr hXa⟩ :
        (walkMap M w).Dart) = ((walkMap M w).facePerm ^ i) x₀ := Subtype.ext ih1
    have h1 : (((ordRing hw hM).facePerm ^ (i + 1)) (lakeStart hw hM x₀)).1.1 =
        (((walkMap M w).facePerm ^ (i + 1)) x₀).1 := by
      rw [pow_succ', Perm.mul_apply, pow_succ', Perm.mul_apply]
      exact hstep.trans (congrArg Subtype.val (congrArg (fun z => (walkMap M w).facePerm z) hy))
    refine ⟨h1, ?_⟩
    rw [← h1, pow_succ', Perm.mul_apply]
    exact alpha_mem_facePerm hw hM _ hXa

/-- The inner reclosing is planar when it keeps the Euler characteristic. -/
theorem ordInner_planar (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (hinner : (reclosedMap M (sideFaces M w) (hw.innerCycle hM)).eulerCharacteristic =
      M.eulerCharacteristic) :
    (ordInner hw hM).IsPlanar :=
  ⟨reclosedMap_connected M _ _ hM.1, hinner.trans hM.2⟩

/-- Every walk dart of the ring map is joined to the first one. -/
theorem eqvGen_wd (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar) (h0 : 0 < w.length)
    (t : ℕ) (ht : t < w.length) :
    Relation.EqvGen (ordRing hw hM).Adjacent (wd hw hM 0 h0) (wd hw hM t ht) := by
  have hp : ((ordRing hw hM).facePerm ^ t) (wd hw hM 0 h0) = wd hw hM t ht :=
    (ordRing_facePerm_pow_wd hw hM 0 t h0 (by omega)).trans
      (ordRing_ext hw hM (getElem_idx_congr w (Nat.zero_add t) (by omega) ht))
  have hs : (ordRing hw hM).facePerm.SameCycle (wd hw hM 0 h0)
      (((ordRing hw hM).facePerm ^ t) (wd hw hM 0 h0)) :=
    Perm.sameCycle_pow_right.mpr (Perm.SameCycle.refl _ _)
  rw [hp] at hs
  exact CombMap.eqvGen_of_sameCycle_facePerm _ hs

/-- The ring map is connected. -/
theorem ordRing_connected (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar) :
    (ordRing hw hM).IsConnected := by
  have h0 : 0 < w.length := List.length_pos_iff.mpr hw.ne_nil
  have hW : ∀ d : (ordRing hw hM).Dart, d.1.1 ∈ w →
      Relation.EqvGen (ordRing hw hM).Adjacent (wd hw hM 0 h0) d := by
    intro d hd
    obtain ⟨t, ht, hteq⟩ := List.getElem_of_mem hd
    have hdt : wd hw hM t ht = d := ordRing_ext hw hM hteq
    subst hdt
    exact eqvGen_wd hw hM h0 t ht
  have hall : ∀ d : (ordRing hw hM).Dart,
      Relation.EqvGen (ordRing hw hM).Adjacent (wd hw hM 0 h0) d := by
    intro d
    have hk : d.1.1 ∈ w ∨ M.alpha d.1.1 ∈ w := d.2
    rcases hk with hd | hd
    · exact hW d hd
    · have hA := hW ((ordRing hw hM).alpha d) hd
      have hadj : (ordRing hw hM).Adjacent ((ordRing hw hM).alpha d) d :=
        Or.inl ((ordRing hw hM).alpha_involutive d)
      exact Relation.EqvGen.trans _ _ _ hA (Relation.EqvGen.rel _ _ hadj)
  exact fun d e => Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (hall d)) (hall e)

/-- **The ring map is planar** when the inner reclosing keeps the Euler characteristic.
(Osin, proof of Lemma 9.7(b); `thm:hull`.) -/
theorem ordRing_planar (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (hinner : (reclosedMap M (sideFaces M w) (hw.innerCycle hM)).eulerCharacteristic =
      M.eulerCharacteristic) :
    (ordRing hw hM).IsPlanar :=
  (CombMap.PredicateRestriction.isRestriction (ordInner hw hM) (fun d => walkKeep M w d.1)
    (ordInner_keep_alpha hw hM)).planar (ordInner_planar hw hM hinner)
    (ordRing_connected hw hM) (wd hw hM 0 (List.length_pos_iff.mpr hw.ne_nil))

end GroupApproximation.Full.GL03BPinchOrder

#audit_axioms GroupApproximation.Full.GL03BPinchOrder.getElem_idx_congr
#audit_axioms GroupApproximation.Full.GL03BPinchOrder.wd_succ
#audit_axioms GroupApproximation.Full.GL03BPinchOrder.wd_last
#audit_axioms GroupApproximation.Full.GL03BPinchOrder.ordRing_facePerm_pow_wd
#audit_axioms GroupApproximation.Full.GL03BPinchOrder.exists_wd_facePerm_eq
#audit_axioms GroupApproximation.Full.GL03BPinchOrder.alpha_mem_facePerm
#audit_axioms GroupApproximation.Full.GL03BPinchOrder.lakeStart
#audit_axioms GroupApproximation.Full.GL03BPinchOrder.lakeStart_val
#audit_axioms GroupApproximation.Full.GL03BPinchOrder.lake_orbit
#audit_axioms GroupApproximation.Full.GL03BPinchOrder.ordInner_planar
#audit_axioms GroupApproximation.Full.GL03BPinchOrder.eqvGen_wd
#audit_axioms GroupApproximation.Full.GL03BPinchOrder.ordRing_connected
#audit_axioms GroupApproximation.Full.GL03BPinchOrder.ordRing_planar
