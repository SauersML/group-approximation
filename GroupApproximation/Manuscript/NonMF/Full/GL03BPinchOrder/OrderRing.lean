import GroupApproximation.Manuscript.NonMF.Full.GL03BPinchOrder.Theta
import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkEuler
import GroupApproximation.Meta.AxiomGuard

/-!
# The ring map of a noncrossing closed walk

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Infrastructure for `thm:hull`
(non_mf_groups_exist.tex 2134, Hull's small cancellation theorem, through Osin's Lemma 9.7).

Let `w` be a noncrossing closed walk in a planar map `M`.  Reclose the inner side of `w`
(`ordInner`), then keep only the edges of `w` (`ordRing`).  In the result:
* a walk dart `w[i]` is followed on its face by `w[i + 1]` (`ordRing_facePerm_val_of_getElem`);
* a dart whose reversal is on `w` is followed on its face as in the walk map `walkMap M w`
  (`ordRing_facePerm_val_of_alpha_mem`).
-/

namespace GroupApproximation.Full.GL03BPinchOrder

universe u

open Equiv
open GroupApproximation.GGT.VanKampen GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
open GroupApproximation.GGT.VanKampen.Surgery.MapCollapse

variable {M : CombMap.{u}} {w : List M.Dart}

/-- The inner reclosing of a noncrossing closed walk. -/
noncomputable abbrev ordInner (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar) :
    CombMap.{u} :=
  reclosedMap M (sideFaces M w) (hw.innerCycle hM)

/-- Darts of the walk edges are not internal to the side faces. -/
theorem not_internal_of_walkKeep (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    {d : M.Dart} (hd : walkKeep M w d) : ¬ InternalDart M (sideFaces M w) d := by
  intro hint
  rcases (hd : d ∈ w ∨ M.alpha d ∈ w) with hd | hd
  · exact ((hw.isBoundaryDart_sideFaces_iff hM d).mpr hd).2 hint.2
  · have hb := ((hw.isBoundaryDart_sideFaces_iff hM (M.alpha d)).mpr hd).2
    rw [M.alpha_involutive d] at hb
    exact hb hint.1

/-- Keeping the walk edges in the inner reclosing is invariant under reversal. -/
theorem ordInner_keep_alpha (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (d : (ordInner hw hM).Dart) :
    walkKeep M w ((ordInner hw hM).alpha d).1 ↔ walkKeep M w d.1 :=
  walkKeep_alpha M w d.1

/-- The ring map: the walk edges inside the inner reclosing. -/
noncomputable abbrev ordRing (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar) :
    CombMap.{u} :=
  CombMap.PredicateRestriction.toCombMap (ordInner hw hM) (fun d => walkKeep M w d.1)
    (ordInner_keep_alpha hw hM)

/-- Darts of the ring map are determined by their underlying darts. -/
theorem ordRing_ext (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    {x y : (ordRing hw hM).Dart} (h : x.1.1 = y.1.1) : x = y :=
  Subtype.ext (Subtype.ext h)

/-- The walk dart `w[i]` as a dart of the ring map. -/
noncomputable def wd (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar) (i : ℕ)
    (hi : i < w.length) : (ordRing hw hM).Dart :=
  ⟨⟨w[i], not_internal_of_walkKeep hw hM (Or.inl (List.getElem_mem hi))⟩,
    Or.inl (List.getElem_mem hi)⟩

theorem wd_val (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar) (i : ℕ)
    (hi : i < w.length) : (wd hw hM i hi).1.1 = w[i] :=
  rfl

theorem ordRing_alpha_val (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (x : (ordRing hw hM).Dart) : ((ordRing hw hM).alpha x).1.1 = M.alpha x.1.1 :=
  rfl

/-- **Walk step.**  In the ring map, the face successor of the walk dart `w[i]` is `w[i + 1]`
(cyclically).  (Osin, proof of Lemma 9.7(b); `thm:hull`.) -/
theorem ordRing_facePerm_val_of_getElem (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (x : (ordRing hw hM).Dart) (i : ℕ) (hi : i < w.length) (hx : x.1.1 = w[i]) :
    ((ordRing hw hM).facePerm x).1.1 = w[(i + 1) % w.length]'(Nat.mod_lt _ (by omega)) := by
  classical
  have hmem : x.1.1 ∈ w := by
    rw [hx]
    exact List.getElem_mem hi
  have hbd : IsBoundaryDart M (sideFaces M w) x.1.1 :=
    (hw.isBoundaryDart_sideFaces_iff hM _).mpr hmem
  have hΓ : ((ordInner hw hM).facePerm x.1).1 = w.next x.1.1 hmem :=
    (reclosedMap_facePerm_val_of_mem M (sideFaces M w) (hw.innerCycle hM) x.1 hbd.1).trans
      (hw.innerCycle_boundaryPerm_val hM _)
  have hnext : ∀ (d : M.Dart) (hd : d ∈ w), d = w[i] →
      w.next d hd = w[(i + 1) % w.length]'(Nat.mod_lt _ (by omega)) := by
    intro d hd h
    subst h
    exact List.next_getElem w hw.nodup i hi
  have hkeep : walkKeep M w ((ordInner hw hM).facePerm x.1).1 := by
    refine Or.inl ?_
    rw [hΓ]
    exact List.next_mem _ _ hmem
  have h2 := predRestr_facePerm_val_of_keep (ordInner hw hM) (fun d => walkKeep M w d.1)
    (ordInner_keep_alpha hw hM) x hkeep
  exact (congrArg Subtype.val h2).trans (hΓ.trans (hnext _ hmem hx))

/-- **Lake step.**  In the ring map, a dart whose reversal is a walk dart has the same face
successor as in the walk map.  (Osin, proof of Lemma 9.7(b); `thm:hull`.) -/
theorem ordRing_facePerm_val_of_alpha_mem (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (X : (ordRing hw hM).Dart) (hX : M.alpha X.1.1 ∈ w) :
    ((ordRing hw hM).facePerm X).1.1 = ((walkMap M w).facePerm ⟨X.1.1, Or.inr hX⟩).1 := by
  obtain ⟨m, hm, hpm, havoid⟩ := (walkMap_isRestriction M w).sigma_firstReturn
    (⟨M.alpha X.1.1, Or.inl hX⟩ : (walkMap M w).Dart)
  have hpm' : (M.sigma ^ m) (M.alpha X.1.1) =
      ((walkMap M w).sigma ⟨M.alpha X.1.1, Or.inl hX⟩).1 := hpm
  have hskipM : ∀ k, 0 < k → k < m → ¬ walkKeep M w ((M.sigma ^ k) (M.alpha X.1.1)) :=
    fun k hk hkm hkeep =>
      havoid k hk hkm (Set.mem_range.mpr ⟨⟨(M.sigma ^ k) (M.alpha X.1.1), hkeep⟩, rfl⟩)
  have hmin : ∀ j < m, M.alpha ((M.sigma ^ j) (M.alpha X.1.1)) ∉ w := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [pow_zero, Perm.one_apply]
      exact hw.alpha_not_mem _ hX
    · exact fun h => hskipM j hj0 hj (Or.inr h)
  have hval : ∀ j, j ≤ m → (((ordInner hw hM).sigma ^ j) ((ordRing hw hM).alpha X).1).1 =
      (M.sigma ^ j) (M.alpha X.1.1) := fun j hj =>
    hw.innerSigma_pow_val hM ((ordRing hw hM).alpha X).1 j (fun t ht => hmin t (by omega))
  have hyk : walkKeep M w (((ordInner hw hM).sigma ^ m) ((ordRing hw hM).alpha X).1).1 := by
    rw [hval m le_rfl, hpm']
    exact ((walkMap M w).sigma ⟨M.alpha X.1.1, Or.inl hX⟩).2
  have hstep := predRestr_sigma_val_of_firstHit (ordInner hw hM) (fun d => walkKeep M w d.1)
    (ordInner_keep_alpha hw hM) ((ordRing hw hM).alpha X)
    (y := ((ordInner hw hM).sigma ^ m) ((ordRing hw hM).alpha X).1) hyk hm rfl
    (fun j hj hjm hk => hskipM j hj hjm (by rw [← hval j hjm.le]; exact hk))
  exact ((congrArg Subtype.val hstep).trans (hval m le_rfl)).trans hpm'

end GroupApproximation.Full.GL03BPinchOrder

#audit_axioms GroupApproximation.Full.GL03BPinchOrder.ordInner
#audit_axioms GroupApproximation.Full.GL03BPinchOrder.not_internal_of_walkKeep
#audit_axioms GroupApproximation.Full.GL03BPinchOrder.ordInner_keep_alpha
#audit_axioms GroupApproximation.Full.GL03BPinchOrder.ordRing
#audit_axioms GroupApproximation.Full.GL03BPinchOrder.ordRing_ext
#audit_axioms GroupApproximation.Full.GL03BPinchOrder.wd
#audit_axioms GroupApproximation.Full.GL03BPinchOrder.wd_val
#audit_axioms GroupApproximation.Full.GL03BPinchOrder.ordRing_alpha_val
#audit_axioms GroupApproximation.Full.GL03BPinchOrder.ordRing_facePerm_val_of_getElem
#audit_axioms GroupApproximation.Full.GL03BPinchOrder.ordRing_facePerm_val_of_alpha_mem
