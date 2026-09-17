import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerPhiMapTransportClasses
import GroupApproximation.Meta.AxiomGuard

/-!
# The new rotation at `none` when the next corner may be deleted

Osin, arXiv:math/0411039v3, Appendix, the assumption before Lemma 9.3: "inside every 2-gon of
`Φ′_M`, there is a vertex of `Φ_M`".

Setting: an edge insertion `M' := EdgeInsertion.toCombMap M a b` at the corners `a` and
`b = σ (α a)`, a retained set `keep` of old darts closed under `alpha`, containing `a`, and a retained
set `keep'` of new darts with `keep' (embed z) ↔ keep z`, containing both new darts `none` and
`some none`.  The Insert module (`PhiMapTransport.sigma_val_none`) computes the new rotation at
`none` only when `b` itself is retained.  Here `b` may be deleted: in a region-pair thickening,
`b` is internal to the holding region exactly when the face across `b` belongs to it.

Mathematical proof.

(A) `sigma_val_none_gen`.  Let `m > 0` be the first return of the old rotation from `α a` to
  `keep`; since `σ (α a) = b`, write `m = m' + 1`, so the old retained successor of `α a` is
  `σ^m' b`.
  * If `m' = 0`, then `b` is retained and `σ' none = embed b` is the new retained successor; and
    `b ≠ a`.
  * If `m' > 0`, then `b` is not retained (it is `σ^1 (α a)`, strictly before the return), so
    `b ≠ σ⁻¹ b = α a`.  The old run from `b` to `σ^m' b` avoids `keep`, and
    `EnclosedBridgeDoubling.firstKept_lift` lifts it to a new run from `embed b` of some length
    `k' > 0` reaching `some none` if `σ^m' b = a` and `embed (σ^m' b)` otherwise, avoiding
    `keep'` in between.  Prepending the step `σ' none = embed b` (not retained, since `b` is not)
    gives a run of length `k' + 1` from `none`, which is the new rotation by
    `restriction_sigma_val_of_run`.
  Hence the new rotation at `none` is `some none` if the old retained successor of `α a` is `a`,
  and its embedding otherwise.

(B) `eqvGen_backDart_none`.  `backDart none = α a`.  By (A), the rotation step from `none` goes to
  `some none`, named `a`, which is the rotation of `α a`, or to `embed x`, named `x`, the rotation
  of `α a`.  Either way it names a rotation step.

(C) `eqvGen_backDart'`.  As `PhiMapTransport.eqvGen_backDart_of_retained`, without assuming
  `keep b`: the rotation steps from `some none` and from old darts only use `keep (σ⁻¹ b)`, which is
  `keep (α a)`, and the step from `none` is (B).  Reversal steps are named by `backDart_alpha`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair

open Equiv EdgeInsertion PhiMapTransport

universe u

variable {M : CombMap.{u}} {a b : M.Dart} {keep : M.Dart → Prop}
  (hkeep : ∀ d, keep (M.alpha d) ↔ keep d) {keep' : (toCombMap M a b).Dart → Prop}
  (hkeep' : ∀ d, keep' ((toCombMap M a b).alpha d) ↔ keep' d)
  (hembed : ∀ z, keep' (embed M z) ↔ keep z)

include hembed in
/-- The new run from `none` through a deleted `b`. -/
theorem run_none_of_lift (hb : ¬ keep b) {y : (toCombMap M a b).Dart} (hy : keep' y)
    (hn : keep' none) {k' : ℕ} (hlift : ((toCombMap M a b).sigma ^ k') (embed M b) = y)
    (hskip' : ∀ t', 0 < t' → t' < k' →
      ¬ keep' (((toCombMap M a b).sigma ^ t') (embed M b))) :
    ((CombMap.PredicateRestriction.toCombMap (toCombMap M a b) keep' hkeep').sigma
        ⟨none, hn⟩).1 = y := by
  refine restriction_sigma_val_of_run hkeep' hn hy (m := k' + 1) (by omega) ?_ ?_
  · rw [pow_succ, Perm.mul_apply, EdgeInsertion.sigma_none_apply]
    exact hlift
  · intro t ht htk
    obtain ⟨r, rfl⟩ : ∃ r, t = r + 1 := ⟨t - 1, by omega⟩
    rw [pow_succ, Perm.mul_apply, EdgeInsertion.sigma_none_apply]
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · rw [pow_zero, Perm.one_apply]
      exact fun hk => hb ((hembed b).mp hk)
    · exact hskip' r hr (by omega)

include hembed in
open scoped Classical in
/-- **The new rotation at `none`**, when `b` may be deleted. -/
theorem sigma_val_none_gen (hab : a ≠ b) (ha : keep a) (hba : M.sigma (M.alpha a) = b)
    (hsn : keep' (some none)) (hn : keep' none) :
    ((CombMap.PredicateRestriction.toCombMap (toCombMap M a b) keep' hkeep').sigma
        ⟨none, hn⟩).1 =
      if ((CombMap.PredicateRestriction.toCombMap M keep hkeep).sigma
          ⟨M.alpha a, (hkeep a).mpr ha⟩).1 = a then some none
      else embed M ((CombMap.PredicateRestriction.toCombMap M keep hkeep).sigma
          ⟨M.alpha a, (hkeep a).mpr ha⟩).1 := by
  obtain ⟨m, hm, hrun, hskip⟩ :=
    CombMap.PredicateRestriction.sigma_firstReturn M keep ⟨M.alpha a, (hkeep a).mpr ha⟩
  have hrun' : (M.sigma ^ m) (M.alpha a) =
      ((CombMap.PredicateRestriction.toCombMap M keep hkeep).sigma
        ⟨M.alpha a, (hkeep a).mpr ha⟩).1 := hrun
  have hkr : keep ((M.sigma ^ m) (M.alpha a)) := by
    rw [hrun']
    exact ((CombMap.PredicateRestriction.toCombMap M keep hkeep).sigma
      ⟨M.alpha a, (hkeep a).mpr ha⟩).2
  rw [← hrun']
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hstep : (M.sigma ^ (m' + 1)) (M.alpha a) = (M.sigma ^ m') b := by
    rw [pow_succ, Perm.mul_apply, hba]
  rw [hstep] at hkr ⊢
  rcases Nat.eq_zero_or_pos m' with rfl | hm'
  · rw [pow_zero, Perm.one_apply] at hkr ⊢
    rw [if_neg (Ne.symm hab)]
    exact sigma_val_none hkeep' hembed hkr hn
  · have hb : ¬ keep b := fun hkb => hskip 1 Nat.one_pos (by omega)
      ⟨⟨b, hkb⟩, by
        show b = (M.sigma ^ 1) (M.alpha a)
        rw [pow_one]
        exact hba.symm⟩
    have hαb : M.sigma.symm b = M.alpha a := (Equiv.symm_apply_eq M.sigma).mpr hba.symm
    have hb' : keep (M.sigma.symm b) := by rw [hαb]; exact (hkeep a).mpr ha
    have hbx : b ≠ M.sigma.symm b := fun h => hb (by rw [h, hαb]; exact (hkeep a).mpr ha)
    obtain ⟨k', -, hlift, hskip'⟩ :=
      EnclosedBridgeDoubling.firstKept_lift hab hembed ha hb' hbx hm'
        (fun t ht htm hkt => hskip (t + 1) (by omega) (by omega)
          ⟨⟨(M.sigma ^ t) b, hkt⟩, by
            show (M.sigma ^ t) b = (M.sigma ^ (t + 1)) (M.alpha a)
            rw [pow_succ, Perm.mul_apply, hba]⟩)
    by_cases h : (M.sigma ^ m') b = a
    · rw [if_pos h] at hlift ⊢
      exact run_none_of_lift hkeep' hembed hb hsn hn hlift hskip'
    · rw [if_neg h] at hlift ⊢
      exact run_none_of_lift hkeep' hembed hb ((hembed _).mpr hkr) hn hlift hskip'

include hembed in
open scoped Classical in
/-- **The new face rotation at `some none`**, when `b` may be deleted. -/
theorem facePerm_val_some_none_gen (hab : a ≠ b) (ha : keep a) (hba : M.sigma (M.alpha a) = b)
    (hsn : keep' (some none)) (hn : keep' none) :
    ((CombMap.PredicateRestriction.toCombMap (toCombMap M a b) keep' hkeep').sigma
        ⟨none, hn⟩).1 =
      if ((CombMap.PredicateRestriction.toCombMap M keep hkeep).facePerm ⟨a, ha⟩).1 = a then
        some none
      else embed M ((CombMap.PredicateRestriction.toCombMap M keep hkeep).facePerm ⟨a, ha⟩).1 :=
  sigma_val_none_gen hkeep hkeep' hembed hab ha hba hsn hn

/-- **The rotation step from `none` names a rotation step.** -/
theorem eqvGen_backDart_none (hab : a ≠ b) (ha : keep a) (hba : M.sigma (M.alpha a) = b)
    (hsn : keep' (some none)) (hn : keep' none)
    {kp : (CombMap.PredicateRestriction.toCombMap M keep hkeep).Dart → Prop}
    {y' : (CombMap.PredicateRestriction.toCombMap (toCombMap M a b) keep' hkeep').Dart}
    (hrot : y' = (CombMap.PredicateRestriction.toCombMap (toCombMap M a b) keep' hkeep').sigma
      ⟨none, hn⟩) :
    Relation.EqvGen (CombMap.FaceClassStep
        (CombMap.PredicateRestriction.toCombMap M keep hkeep).dual kp)
      (backDart hkeep hkeep' hembed ha ⟨none, hn⟩) (backDart hkeep hkeep' hembed ha y') := by
  have hlift := sigma_val_none_gen hkeep hkeep' hembed hab ha hba hsn hn
  by_cases hA : ((CombMap.PredicateRestriction.toCombMap M keep hkeep).sigma
      ⟨M.alpha a, (hkeep a).mpr ha⟩).1 = a
  · have hy : y' = ⟨some none, hsn⟩ := hrot.trans (Subtype.ext (hlift.trans (if_pos hA)))
    subst hy
    refine Relation.EqvGen.rel _ _ (Or.inl ?_)
    rw [CombMap.dual_facePerm]
    exact Subtype.ext hA.symm
  · have hy : y' = ⟨embed M ((CombMap.PredicateRestriction.toCombMap M keep hkeep).sigma
          ⟨M.alpha a, (hkeep a).mpr ha⟩).1,
        (hembed _).mpr ((CombMap.PredicateRestriction.toCombMap M keep hkeep).sigma
          ⟨M.alpha a, (hkeep a).mpr ha⟩).2⟩ :=
      hrot.trans (Subtype.ext (hlift.trans (if_neg hA)))
    subst hy
    refine Relation.EqvGen.rel _ _ (Or.inl ?_)
    rw [CombMap.dual_facePerm]
    rfl

/-- The rotation step from an old dart names a rotation step or no step. -/
theorem eqvGen_backDart_embed (hab : a ≠ b) (ha : keep a) (hba : M.sigma (M.alpha a) = b)
    (hsn : keep' (some none)) (hn : keep' none)
    {kp : (CombMap.PredicateRestriction.toCombMap M keep hkeep).Dart → Prop} {z : M.Dart}
    (hd : keep' (some (some z)))
    {y' : (CombMap.PredicateRestriction.toCombMap (toCombMap M a b) keep' hkeep').Dart}
    (hrot : y' = (CombMap.PredicateRestriction.toCombMap (toCombMap M a b) keep' hkeep').sigma
      ⟨some (some z), hd⟩) :
    Relation.EqvGen (CombMap.FaceClassStep
        (CombMap.PredicateRestriction.toCombMap M keep hkeep).dual kp)
      (backDart hkeep hkeep' hembed ha ⟨some (some z), hd⟩)
      (backDart hkeep hkeep' hembed ha y') := by
  have hαb : M.sigma.symm b = M.alpha a := (Equiv.symm_apply_eq M.sigma).mpr hba.symm
  have hb : keep (M.sigma.symm b) := by rw [hαb]; exact (hkeep a).mpr ha
  have hz : keep z := (hembed z).mp hd
  by_cases hzb : z = M.sigma.symm b
  · subst hzb
    have hy : y' = ⟨none, hn⟩ :=
      hrot.trans (Subtype.ext (sigma_val_symm_of_retained hkeep' hembed hab hb hn))
    subst hy
    have hback : backDart hkeep hkeep' hembed ha ⟨some (some (M.sigma.symm b)), hd⟩ =
        backDart hkeep hkeep' hembed ha ⟨none, hn⟩ := Subtype.ext hαb
    rw [hback]
    exact Relation.EqvGen.refl _
  · have hlift := sigma_val_of_retained hkeep hkeep' hembed hab ha hb hsn hz hzb
    by_cases hA : ((CombMap.PredicateRestriction.toCombMap M keep hkeep).sigma ⟨z, hz⟩).1 = a
    · have hy : y' = ⟨some none, hsn⟩ := hrot.trans (Subtype.ext (hlift.trans (if_pos hA)))
      subst hy
      refine Relation.EqvGen.rel _ _ (Or.inl ?_)
      rw [CombMap.dual_facePerm]
      exact Subtype.ext hA.symm
    · have hy : y' = ⟨embed M
          ((CombMap.PredicateRestriction.toCombMap M keep hkeep).sigma ⟨z, hz⟩).1,
          (hembed _).mpr
            ((CombMap.PredicateRestriction.toCombMap M keep hkeep).sigma ⟨z, hz⟩).2⟩ :=
        hrot.trans (Subtype.ext (hlift.trans (if_neg hA)))
      subst hy
      refine Relation.EqvGen.rel _ _ (Or.inl ?_)
      rw [CombMap.dual_facePerm]
      rfl

/-- **A face-class path after the insertion names a path before it**, when the new darts are in the
collapsed map and the next corner `b` may be deleted. -/
theorem eqvGen_backDart' (hab : a ≠ b) (ha : keep a) (hba : M.sigma (M.alpha a) = b)
    (hsn : keep' (some none)) (hn : keep' none)
    {kp : (CombMap.PredicateRestriction.toCombMap M keep hkeep).Dart → Prop}
    {kp' : (CombMap.PredicateRestriction.toCombMap (toCombMap M a b) keep' hkeep').Dart → Prop}
    (hcorr : ∀ z (hz : keep z), kp' ⟨embed M z, (hembed z).mpr hz⟩ ↔ kp ⟨z, hz⟩)
    (hka : ¬ kp ⟨a, ha⟩) (hkaa : ¬ kp ⟨M.alpha a, (hkeep a).mpr ha⟩)
    {x' y' : (CombMap.PredicateRestriction.toCombMap (toCombMap M a b) keep' hkeep').Dart}
    (h : Relation.EqvGen (CombMap.FaceClassStep
      (CombMap.PredicateRestriction.toCombMap (toCombMap M a b) keep' hkeep').dual kp') x' y') :
    Relation.EqvGen (CombMap.FaceClassStep
        (CombMap.PredicateRestriction.toCombMap M keep hkeep).dual kp)
      (backDart hkeep hkeep' hembed ha x') (backDart hkeep hkeep' hembed ha y') := by
  induction h with
  | rel x' y' hstep =>
    obtain ⟨d, hd⟩ := x'
    rcases hstep with hrot | ⟨hnk, halpha⟩
    · rw [CombMap.dual_facePerm] at hrot
      rcases d with _ | _ | z
      · exact eqvGen_backDart_none hkeep hkeep' hembed hab ha hba hsn hd hrot
      · have hy : y' = ⟨embed M a, (hembed a).mpr ha⟩ :=
          hrot.trans (Subtype.ext (sigma_val_some_none hkeep' hembed hab ha hd))
        subst hy
        exact Relation.EqvGen.refl _
      · exact eqvGen_backDart_embed hkeep hkeep' hembed hab ha hba hsn hn hd hrot
    · subst halpha
      refine Relation.EqvGen.rel _ _ (Or.inr ⟨?_, backDart_alpha hkeep hkeep' hembed ha _⟩)
      rcases d with _ | _ | z
      · exact hkaa
      · exact hka
      · exact fun hk => hnk ((hcorr z ((hembed z).mp hd)).mpr hk)
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair.sigma_val_none_gen
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair.eqvGen_backDart'
