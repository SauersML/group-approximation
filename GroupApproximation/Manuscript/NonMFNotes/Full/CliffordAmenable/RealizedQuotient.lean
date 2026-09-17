import GroupApproximation.Sofic.CliffordBSAmenableMF
import GroupApproximation.Sofic.CliffordBSPrintedRoute
import GroupApproximation.Monsters.LiteralDyadicCalibration
import GroupApproximation.Meta.AxiomGuard

/-!
# Sharpness of the Kazhdan hypothesis: the realized Clifford quotient is amenable

`non_mf_group_notes.tex`, `\section{Necessity}`, the paragraph after *Sharpness of the Kazhdan
hypothesis* (grep `The realized Clifford quotient is amenable`, tex ≈ 1163–1170):

> The realized Clifford quotient is amenable: it is a subgroup of the semidirect product of the
> locally finite Clifford group on the coset space by the solvable affine group
> `BS(1,2) ≅ ℤ[1/2] ⋊ ℤ`.  So it is MF: … [Schafhauser, Theorem B].  The models above give
> `Θ(w_BS) ≠ 1` for an MF image `Θ(E_BS)`.

The paragraph is badged `\leanverified{Sofic/CliffordBSAmenableMF}{manuscriptSharpnessOfKazhdanHypothesis}`.
This file packages the printed sentence clause by clause.  It cites the library and duplicates
nothing.

## What is proved here (unconditionally)

* `realizedCliffordQuotient_isAmenable`: both realized Clifford quotients are amenable.  One sits
  over `ℚ ⋊ ℤ` (`LiteralCyclicCalibration.RealizedQuotient`); the other is the literal one over
  `ℤ[1/2] ⋊ ℤ` (`LiteralDyadicCalibration.DyadicRealizedQuotient`).
* `realizedCliffordQuotient_amenabilityReasons`: the printed *reasons*.  The Clifford lamp groups on
  the coset spaces are locally finite, both bases are solvable, `BS(1,2) ≃* ℤ[1/2] ⋊ ℤ`, and both
  semidirect products carry invariant means.
* `mfImage_*`: facts about the explicit MF image `Θ = coronaRep` of `E_BS` in which `w_BS`
  survives.  It is countable, the mark stays central, and it is neither LEF nor residually finite.
  So no exact finite model detects `w_BS` there.
* `notesRealizedCliffordQuotient`: the whole paragraph as one closed conjunction.

## What is *not* proved here

* The clause "So it is MF", i.e. `IsOperatorMF RealizedQuotient`, is not proved.  The
  realized quotient is not LEF (`CyclicBaseLEFObstruction.realizedQuotient_not_isLEF`), so every
  exact-model criterion of the library fails.  The printed route goes through
  Tikuisis–White–Winter / Schafhauser quasidiagonality, which is not formalized.  The paragraph's
  *conclusion* (`w_BS` survives in an MF image) does not need it.  The image is exhibited
  explicitly as `CliffordBSAmenableMF.coronaRep.range`.
* Amenability of that MF image `coronaRep.range` is not proved.  The manuscript does not claim it
  either: `coronaRep` does not factor through the realized quotient.
-/

namespace GroupApproximation.Full.NN10

/-- **tex ≈ 1163, "The realized Clifford quotient is amenable".**  This covers both the realized
quotient over the overgroup `ℚ ⋊ ℤ` used by the corona model and the literal one over
`BS(1,2) ≅ ℤ[1/2] ⋊ ℤ`. -/
theorem realizedCliffordQuotient_isAmenable :
    Amenability.IsAmenable LiteralCyclicCalibration.RealizedQuotient ∧
      Amenability.IsAmenable LiteralDyadicCalibration.DyadicRealizedQuotient :=
  ⟨CliffordBSAmenableMF.realizedQuotient_isAmenable,
    LiteralDyadicCalibration.isAmenable_dyadicRealizedQuotient⟩

/-- **tex ≈ 1163–1165, the printed reasons.**  The realized quotient lies in "the semidirect
product of the locally finite Clifford group on the coset space by the solvable affine group
`BS(1,2) ≅ ℤ[1/2] ⋊ ℤ`".  Each named ingredient is formalized:

* the Clifford lamp groups on both coset spaces are locally finite;
* both bases are solvable;
* `BS(1,2) ≃* ℤ[1/2] ⋊ ℤ`;
* both semidirect products have invariant means.

The realized quotients are the ranges of `realization` and `dyadicRealization`, so they are
subgroups of these semidirect products by definition. -/
theorem realizedCliffordQuotient_amenabilityReasons :
    IsLocallyFiniteGroup (CliffordAlgebraLamp.lampGroup CyclicBaseCalibration.Sites) ∧
      IsLocallyFiniteGroup (CliffordAlgebraLamp.lampGroup LiteralDyadicCalibration.Sites) ∧
      IsSolvable CyclicBaseCalibration.BSLike ∧
      IsSolvable DyadicRationals.Affine ∧
      Nonempty (DyadicRationals.BS ≃* DyadicRationals.Affine) ∧
      Amenability.HasInvariantMean CyclicBaseCalibration.CliffordBS ∧
      Amenability.HasInvariantMean LiteralDyadicCalibration.CliffordDyadic :=
  ⟨CliffordAlgebraLamp.isLocallyFiniteGroup_lampGroup _,
    CliffordAlgebraLamp.isLocallyFiniteGroup_lampGroup _,
    CliffordBSPrintedRoute.isSolvable_BSLike,
    LiteralDyadicCalibration.affine_isSolvable,
    ⟨DyadicRationals.bsEquivAffine⟩,
    CyclicBaseCalibration.hasInvariantMean_CliffordBS,
    LiteralDyadicCalibration.hasInvariantMean_cliffordDyadic⟩

/-- The MF image `Θ(E_BS) = coronaRep.range` of tex ≈ 1169 is countable, being a quotient of the
finitely presented group `E_BS`. -/
theorem mfImage_countable : Countable CliffordBSAmenableMF.coronaRep.range :=
  Function.Surjective.countable CliffordBSAmenableMF.coronaRep.rangeRestrict_surjective

/-- The MF image `Θ(E_BS)` detecting `w_BS` is not LEF.  Every quotient in which the mark
survives fails LEF, so exact finite models cannot produce this image. -/
theorem mfImage_not_isLEF : ¬ IsLEF CliffordBSAmenableMF.coronaRep.range :=
  CliffordBSAmenableMF.not_isLEF_of_mark_survives _
    CliffordBSAmenableMF.rangeRestrict_mark_ne_one

/-- The MF image `Θ(E_BS)` detecting `w_BS` is not residually finite. -/
theorem mfImage_not_residuallyFinite :
    ¬ Group.ResiduallyFinite CliffordBSAmenableMF.coronaRep.range :=
  fun h ↦ mfImage_not_isLEF (@isLEF_of_residuallyFinite _ _ h)

/-- In the MF image the surviving mark `Θ(w_BS)` is still central.  This is the image of the
central relation of `E_BS`. -/
theorem mfImage_mark_central (g : CliffordBSAmenableMF.coronaRep.range) :
    Commute (CliffordBSAmenableMF.coronaRep.rangeRestrict LiteralCyclicCalibration.mark) g := by
  obtain ⟨x, rfl⟩ := CliffordBSAmenableMF.coronaRep.rangeRestrict_surjective g
  exact (LiteralCyclicCalibration.mark_central x).map
    CliffordBSAmenableMF.coronaRep.rangeRestrict

/-- **The sharpness paragraph, tex ≈ 1163–1170, as one closed statement.**

1. Both realized Clifford quotients are amenable, and the mark survives in the realized quotient.
2. That quotient is not LEF, so the "So it is MF" step cannot come from exact models.  It is left
   to the unformalized Schafhauser/TWW citation and is **not** asserted here.
3. The conclusion `Θ(w_BS) ≠ 1` for an MF image `Θ(E_BS)` holds, with `Θ` the explicit corona
   representation over a sequence of nonempty finite models.
4. `w_BS` lies outside the corona MF radical of `E_BS`. -/
theorem notesRealizedCliffordQuotient :
    Amenability.IsAmenable LiteralCyclicCalibration.RealizedQuotient ∧
      Amenability.IsAmenable LiteralDyadicCalibration.DyadicRealizedQuotient ∧
      LiteralCyclicCalibration.quotientMap LiteralCyclicCalibration.mark ≠ 1 ∧
      ¬ IsLEF LiteralCyclicCalibration.RealizedQuotient ∧
      IsOperatorMF CliffordBSAmenableMF.coronaRep.range ∧
      CliffordBSAmenableMF.coronaRep.rangeRestrict LiteralCyclicCalibration.mark ≠ 1 ∧
      ¬ IsLEF CliffordBSAmenableMF.coronaRep.range ∧
      (∃ X : ℕ → FiniteModel, (∀ n, 0 < Fintype.card (X n)) ∧
        ∃ rho : LiteralCyclicCalibration.LiteralGroup →* NormMatrixCoronaUnitary X,
          rho LiteralCyclicCalibration.mark ≠ 1) ∧
      (LiteralCyclicCalibration.mark : LiteralCyclicCalibration.LiteralGroup) ∉
        coronaMFResidual LiteralCyclicCalibration.LiteralGroup :=
  ⟨realizedCliffordQuotient_isAmenable.1,
    realizedCliffordQuotient_isAmenable.2,
    LiteralCyclicCalibration.quotientMap_mark_ne_one,
    CyclicBaseLEFObstruction.realizedQuotient_not_isLEF,
    CliffordBSAmenableMF.coronaRep_range_isOperatorMF,
    CliffordBSAmenableMF.rangeRestrict_mark_ne_one,
    mfImage_not_isLEF,
    ⟨CliffordBSAmenableMF.site, CliffordBSAmenableMF.card_site_pos,
      CliffordBSAmenableMF.coronaRep, CliffordBSAmenableMF.coronaRep_mark_ne_one⟩,
    CliffordBSAmenableMF.mark_notMem_coronaMFResidual⟩

end GroupApproximation.Full.NN10

#audit_closed_axioms GroupApproximation.Full.NN10.realizedCliffordQuotient_isAmenable
#audit_closed_axioms GroupApproximation.Full.NN10.realizedCliffordQuotient_amenabilityReasons
#audit_closed_axioms GroupApproximation.Full.NN10.mfImage_countable
#audit_closed_axioms GroupApproximation.Full.NN10.mfImage_not_isLEF
#audit_closed_axioms GroupApproximation.Full.NN10.mfImage_not_residuallyFinite
#audit_axioms GroupApproximation.Full.NN10.mfImage_mark_central
#audit_closed_axioms GroupApproximation.Full.NN10.notesRealizedCliffordQuotient
