import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerPhiMapTransportInsert
import GroupApproximation.GGT.VanKampen.CombMapRestrictionFaceClasses
import GroupApproximation.GGT.VanKampen.CombMapDual
import GroupApproximation.Meta.AxiomGuard

/-!
# Face classes of a restriction after inserting an edge

Osin, arXiv:math/0411039v3, Appendix, the assumption before Lemma 9.3: "inside every 2-gon of
`Φ′_M`, there is a vertex of `Φ_M`".

`RegionCandidate.HoldsCellO` asks for a path from a retained dart of a face of `Φ'_M` to a dart of
a relator cell, advancing by the rotation of the collapsed map and crossing edges that are not
retained.  After an edge insertion `EdgeInsertion.toCombMap M a b` at `b = σ (α a)`, name each
retained dart by an old one: an old dart by itself, `some none` by `a`, and `none` by `α a`.  Every
step of a path after the insertion names a path before it, as long as neither `a` nor `α a` is
retained in `Φ'_M`.

* `PhiMapTransport.backDart`.
* `PhiMapTransport.eqvGen_backDart_of_retained`: when the new darts are in the collapsed map.
* `PhiMapTransport.eqvGen_backDart_of_deleted`: when they are not.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`), through Osin's Lemma 9.7(a);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.PhiMapTransport

open Equiv EdgeInsertion

universe u

variable {M : CombMap.{u}} {a b : M.Dart} {keep : M.Dart → Prop}
  (hkeep : ∀ d, keep (M.alpha d) ↔ keep d) {keep' : (toCombMap M a b).Dart → Prop}
  (hkeep' : ∀ d, keep' ((toCombMap M a b).alpha d) ↔ keep' d)
  (hembed : ∀ z, keep' (embed M z) ↔ keep z)

/-- **The old dart named by a retained dart of the insertion**: an old dart names itself,
`some none` names `a`, and `none` names `α a`. -/
def backDart (ha : keep a) :
    (CombMap.PredicateRestriction.toCombMap (toCombMap M a b) keep' hkeep').Dart →
      (CombMap.PredicateRestriction.toCombMap M keep hkeep).Dart
  | ⟨some (some z), h⟩ => ⟨z, (hembed z).mp h⟩
  | ⟨some none, _⟩ => ⟨a, ha⟩
  | ⟨none, _⟩ => ⟨M.alpha a, (hkeep a).mpr ha⟩

/-- **A reversal step after the insertion is a reversal step before it.** -/
theorem backDart_alpha (ha : keep a)
    (x' : (CombMap.PredicateRestriction.toCombMap (toCombMap M a b) keep' hkeep').Dart) :
    backDart hkeep hkeep' hembed ha
        ((CombMap.PredicateRestriction.toCombMap (toCombMap M a b) keep' hkeep').dual.alpha x') =
      (CombMap.PredicateRestriction.toCombMap M keep hkeep).dual.alpha
        (backDart hkeep hkeep' hembed ha x') := by
  obtain ⟨d, hd⟩ := x'
  rcases d with _ | _ | z
  · exact Subtype.ext (M.alpha_involutive a).symm
  · rfl
  · rfl

/-- **A face-class path after the insertion names a path before it**, when the new darts are in the
collapsed map. -/
theorem eqvGen_backDart_of_retained (hab : a ≠ b) (ha : keep a) (hba : M.sigma (M.alpha a) = b)
    (hbk : keep b) (hsn : keep' (some none)) (hn : keep' none)
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
  have hαb : M.sigma.symm b = M.alpha a := (Equiv.symm_apply_eq M.sigma).mpr hba.symm
  have hb : keep (M.sigma.symm b) := by rw [hαb]; exact (hkeep a).mpr ha
  induction h with
  | rel x' y' hstep =>
    obtain ⟨d, hd⟩ := x'
    rcases hstep with hrot | ⟨hnk, halpha⟩
    · rw [CombMap.dual_facePerm] at hrot
      rcases d with _ | _ | z
      · have hy : y' = ⟨embed M b, (hembed b).mpr hbk⟩ :=
          hrot.trans (Subtype.ext (sigma_val_none hkeep' hembed hbk hd))
        subst hy
        refine Relation.EqvGen.rel _ _ (Or.inl ?_)
        rw [CombMap.dual_facePerm]
        exact Subtype.ext (restriction_sigma_val_of_run hkeep ((hkeep a).mpr ha) hbk Nat.one_pos
          (by rw [pow_one]; exact hba) fun k hk hk1 => absurd hk1 (by omega)).symm
      · have hy : y' = ⟨embed M a, (hembed a).mpr ha⟩ :=
          hrot.trans (Subtype.ext (sigma_val_some_none hkeep' hembed hab ha hd))
        subst hy
        exact Relation.EqvGen.refl _
      · have hz : keep z := (hembed z).mp hd
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
    · subst halpha
      refine Relation.EqvGen.rel _ _ (Or.inr ⟨?_, backDart_alpha hkeep hkeep' hembed ha _⟩)
      rcases d with _ | _ | z
      · exact hkaa
      · exact hka
      · exact fun hk => hnk ((hcorr z ((hembed z).mp hd)).mpr hk)
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

/-- **A face-class path after the insertion names a path before it**, when the new darts are not in
the collapsed map. -/
theorem eqvGen_backDart_of_deleted (hab : a ≠ b) (ha : keep a) (hba : M.sigma (M.alpha a) = b)
    (hbk : keep b) (hsn : ¬ keep' (some none)) (hn : ¬ keep' none)
    {kp : (CombMap.PredicateRestriction.toCombMap M keep hkeep).Dart → Prop}
    {kp' : (CombMap.PredicateRestriction.toCombMap (toCombMap M a b) keep' hkeep').Dart → Prop}
    (hcorr : ∀ z (hz : keep z), kp' ⟨embed M z, (hembed z).mpr hz⟩ ↔ kp ⟨z, hz⟩)
    {x' y' : (CombMap.PredicateRestriction.toCombMap (toCombMap M a b) keep' hkeep').Dart}
    (h : Relation.EqvGen (CombMap.FaceClassStep
      (CombMap.PredicateRestriction.toCombMap (toCombMap M a b) keep' hkeep').dual kp') x' y') :
    Relation.EqvGen (CombMap.FaceClassStep
        (CombMap.PredicateRestriction.toCombMap M keep hkeep).dual kp)
      (backDart hkeep hkeep' hembed ha x') (backDart hkeep hkeep' hembed ha y') := by
  have hαb : M.sigma.symm b = M.alpha a := (Equiv.symm_apply_eq M.sigma).mpr hba.symm
  have hb : keep (M.sigma.symm b) := by rw [hαb]; exact (hkeep a).mpr ha
  induction h with
  | rel x' y' hstep =>
    obtain ⟨d, hd⟩ := x'
    rcases d with _ | _ | z
    · exact absurd hd hn
    · exact absurd hd hsn
    · have hz : keep z := (hembed z).mp hd
      rcases hstep with hrot | ⟨hnk, halpha⟩
      · rw [CombMap.dual_facePerm] at hrot
        have hy : y' = ⟨embed M
            ((CombMap.PredicateRestriction.toCombMap M keep hkeep).sigma ⟨z, hz⟩).1,
            (hembed _).mpr
              ((CombMap.PredicateRestriction.toCombMap M keep hkeep).sigma ⟨z, hz⟩).2⟩ :=
          hrot.trans
            (Subtype.ext (sigma_val_of_deleted hkeep hkeep' hembed hab ha hb hbk hsn hn hz))
        subst hy
        refine Relation.EqvGen.rel _ _ (Or.inl ?_)
        rw [CombMap.dual_facePerm]
        rfl
      · subst halpha
        exact Relation.EqvGen.rel _ _ (Or.inr ⟨fun hk => hnk ((hcorr z hz).mpr hk),
          backDart_alpha hkeep hkeep' hembed ha _⟩)
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

end GroupApproximation.GGT.VanKampen.PhiMapTransport

#audit_axioms GroupApproximation.GGT.VanKampen.PhiMapTransport.backDart_alpha
#audit_axioms GroupApproximation.GGT.VanKampen.PhiMapTransport.eqvGen_backDart_of_retained
#audit_axioms GroupApproximation.GGT.VanKampen.PhiMapTransport.eqvGen_backDart_of_deleted
