import GroupApproximation.PropertyT.IntegralGeneratorShearSelector

/-!
# Turning the region placements into mass inequalities

`IntegralGeneratorShearDescent` places the `A/B/C/D` regions of the integral
column-plane spectrum under the four shears, and
`IntegralGeneratorShearSelector` cuts the source region into disjoint
measurable letter pieces.  This file converts the unit-shear placements into
the two square-root mass inequalities

```
sqrt (mu A) ≤ sqrt (mu B) + delta,     sqrt (mu C) ≤ sqrt (mu B) + delta
```

for the column-plane spectral measure of an almost invariant unit vector.
They are the integral analogues of `FreeRootPlaneMassBase.sum_planeMass_A_le_sum_B`
and `sum_planeMass_C_le_sum_B`, and they are what the endgame arithmetic uses
to bound the two off-diagonal regions by the diagonal one.

The transport itself is Kassabov's Lemma 2.4, already in the tree as
`KassabovBorelMeasureInequalities.abs_sqrt_measureReal_image_sub_le`.  It asks
for quadratic quasi-invariance in *both* directions, so the file first
identifies the inverse of a shear's dual action with the dual action of the
opposite shear, and records quasi-invariance for the opposite shear of every
control coefficient.  The opposite shear of a control element is the inverse
of that control element, so it displaces the vector by exactly as much.
-/

namespace GroupApproximation
namespace IntegralGeneratorShearMass

open Set MeasureTheory WeakDual
open IntegralCharacterMass
open IntegralColumnPlaneSpectralMeasure
open IntegralColumnPlaneSpectralShear
open IntegralColumnPlaneSpectralTorus
open IntegralColumnPlaneSpectralMassBound
open IntegralGeneratorShearDescent
open IntegralGeneratorShearSelector
open RepresentedRootPlaneSpectralQuasiInvariant
open FreeAlgebraDegree

noncomputable section

universe u v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]
variable {X : Type u} [Fintype X]
variable (rho : elementaryGroup (Fin 3) (FreeAlgebra ℤ X) →* (E ≃ₗᵢ[ℝ] E))

noncomputable local instance columnPlaneCharacterMeasurableSpace' :
    MeasurableSpace (characterSpace ℂ (representedColumnPlane rho).algebra) :=
  borel _

local instance columnPlaneCharacterBorelSpace' :
    BorelSpace (characterSpace ℂ (representedColumnPlane rho).algebra) :=
  ⟨rfl⟩

noncomputable local instance columnPlaneSpectralMeasureIsFinite'
    (z : E) (hz : ‖z‖ = 1) :
    IsFiniteMeasure (columnPlaneSpectralMeasure rho z hz) := by
  unfold columnPlaneSpectralMeasure
  infer_instance

/-! ### The inverse of a shear action is the action of the opposite shear -/

omit [Fintype X] in
theorem lowerCharacterMeasurableEquiv_symm_apply (r : FreeAlgebra ℤ X)
    (chi : characterSpace ℂ (representedColumnPlane rho).algebra) :
    (lowerCharacterMeasurableEquiv rho r).symm chi =
      lowerCharacterAction rho (-r) chi := by
  have hstar : star ((representedColumnPlane rho).rho (lowerShear r)) =
      (representedColumnPlane rho).rho (lowerShear (-r)) := by
    rw [Unitary.star_eq_inv, ← map_inv, lowerShear_inv]
  apply CharacterSpace.ext
  intro y
  show chi ((CommutativeCStarCovariance.restrictConjStarAlgEquiv
      (representedColumnPlane rho).algebra
      ((representedColumnPlane rho).rho (lowerShear r))
      (lowerShear_forward rho r) (lowerShear_backward rho r)).symm y) =
    chi (CommutativeCStarCovariance.restrictConjStarAlgEquiv
      (representedColumnPlane rho).algebra
      ((representedColumnPlane rho).rho (lowerShear (-r)))
      (lowerShear_forward rho (-r)) (lowerShear_backward rho (-r)) y)
  refine congrArg (fun t : (representedColumnPlane rho).algebra ↦ chi t) ?_
  apply Subtype.ext
  rw [CommutativeCStarCovariance.restrictConjStarAlgEquiv_symm_coe,
    CommutativeCStarCovariance.restrictConjStarAlgEquiv_coe,
    Unitary.conjStarAlgAut_symm, hstar]

omit [Fintype X] in
theorem upperCharacterMeasurableEquiv_symm_apply (r : FreeAlgebra ℤ X)
    (chi : characterSpace ℂ (representedColumnPlane rho).algebra) :
    (upperCharacterMeasurableEquiv rho r).symm chi =
      upperCharacterAction rho (-r) chi := by
  have hstar : star ((representedColumnPlane rho).rho (upperShear r)) =
      (representedColumnPlane rho).rho (upperShear (-r)) := by
    rw [Unitary.star_eq_inv, ← map_inv, upperShear_inv]
  apply CharacterSpace.ext
  intro y
  show chi ((CommutativeCStarCovariance.restrictConjStarAlgEquiv
      (representedColumnPlane rho).algebra
      ((representedColumnPlane rho).rho (upperShear r))
      (upperShear_forward rho r) (upperShear_backward rho r)).symm y) =
    chi (CommutativeCStarCovariance.restrictConjStarAlgEquiv
      (representedColumnPlane rho).algebra
      ((representedColumnPlane rho).rho (upperShear (-r)))
      (upperShear_forward rho (-r)) (upperShear_backward rho (-r)) y)
  refine congrArg (fun t : (representedColumnPlane rho).algebra ↦ chi t) ?_
  apply Subtype.ext
  rw [CommutativeCStarCovariance.restrictConjStarAlgEquiv_symm_coe,
    CommutativeCStarCovariance.restrictConjStarAlgEquiv_coe,
    Unitary.conjStarAlgAut_symm, hstar]

/-! ### Quasi-invariance under the opposite of every control shear -/

/-- The opposite of a control shear is the inverse of a control element, so it
displaces the vector by the same amount and the spectral measure obeys the
same quadratic estimate. -/
theorem lowerShear_neg_control_measurableQuasiInvariantAtScale
    (z : E) (hz : ‖z‖ = 1) (delta : ℝ) (hdelta : 0 < delta)
    (hnear : ∀ s ∈ integralControlSet X, ‖rho s z - z‖ < delta)
    (q : Option X) :
    KassabovBorelMeasureInequalities.MeasurableQuasiInvariantAtScale
      (columnPlaneSpectralMeasure rho z hz) delta
      (lowerCharacterMeasurableEquiv rho
        (-(integralControlCoefficient X q))) := by
  apply measurableQuasiInvariantAtScale_characterHomeomorph
    (representedColumnPlane rho) (Complexification.mk z 0)
    (norm_mk_zero_eq_one hz)
    ((representedColumnPlane rho).rho
      (lowerShear (-(integralControlCoefficient X q))))
    (lowerShear_forward rho _) (lowerShear_backward rho _) hdelta.le
  change ‖RealToComplexUnitaryRepresentation.complexifiedOperatorRepresentation
      rho (lowerShear (-(integralControlCoefficient X q)))
        (Complexification.mk z 0) - Complexification.mk z 0‖ ≤ delta
  rw [RealToComplexUnitaryRepresentation.norm_complexified_displacement_mk_zero]
  rw [← lowerShear_inv (integralControlCoefficient X q),
    IntegralCharacterMass.norm_inv_displacement]
  have hmem : lowerShear (integralControlCoefficient X q) ∈
      integralControlSet X := by
    let a : A2Root := ⟨((1 : Fin 3), (0 : Fin 3)), by decide⟩
    simpa [lowerShear, integralControlElement, a] using
      integralControlElement_mem X (a, q)
  exact (hnear _ hmem).le

/-- The mirror statement for the upper shears. -/
theorem upperShear_neg_control_measurableQuasiInvariantAtScale
    (z : E) (hz : ‖z‖ = 1) (delta : ℝ) (hdelta : 0 < delta)
    (hnear : ∀ s ∈ integralControlSet X, ‖rho s z - z‖ < delta)
    (q : Option X) :
    KassabovBorelMeasureInequalities.MeasurableQuasiInvariantAtScale
      (columnPlaneSpectralMeasure rho z hz) delta
      (upperCharacterMeasurableEquiv rho
        (-(integralControlCoefficient X q))) := by
  apply measurableQuasiInvariantAtScale_characterHomeomorph
    (representedColumnPlane rho) (Complexification.mk z 0)
    (norm_mk_zero_eq_one hz)
    ((representedColumnPlane rho).rho
      (upperShear (-(integralControlCoefficient X q))))
    (upperShear_forward rho _) (upperShear_backward rho _) hdelta.le
  change ‖RealToComplexUnitaryRepresentation.complexifiedOperatorRepresentation
      rho (upperShear (-(integralControlCoefficient X q)))
        (Complexification.mk z 0) - Complexification.mk z 0‖ ≤ delta
  rw [RealToComplexUnitaryRepresentation.norm_complexified_displacement_mk_zero]
  rw [← upperShear_inv (integralControlCoefficient X q),
    IntegralCharacterMass.norm_inv_displacement]
  have hmem : upperShear (integralControlCoefficient X q) ∈
      integralControlSet X := by
    let a : A2Root := ⟨((0 : Fin 3), (1 : Fin 3)), by decide⟩
    simpa [upperShear, integralControlElement, a] using
      integralControlElement_mem X (a, q)
  exact (hnear _ hmem).le

/-- Quasi-invariance under the control shear itself, stated for the bundled
measurable equivalence and the named spectral measure. -/
theorem lowerShear_control_measurableQuasiInvariantAtScale
    (z : E) (hz : ‖z‖ = 1) (delta : ℝ) (hdelta : 0 < delta)
    (hnear : ∀ s ∈ integralControlSet X, ‖rho s z - z‖ < delta)
    (q : Option X) :
    KassabovBorelMeasureInequalities.MeasurableQuasiInvariantAtScale
      (columnPlaneSpectralMeasure rho z hz) delta
      (lowerCharacterMeasurableEquiv rho (integralControlCoefficient X q)) :=
  lowerShear_measurableQuasiInvariantAtScale X rho z hz delta hdelta hnear q

theorem upperShear_control_measurableQuasiInvariantAtScale
    (z : E) (hz : ‖z‖ = 1) (delta : ℝ) (hdelta : 0 < delta)
    (hnear : ∀ s ∈ integralControlSet X, ‖rho s z - z‖ < delta)
    (q : Option X) :
    KassabovBorelMeasureInequalities.MeasurableQuasiInvariantAtScale
      (columnPlaneSpectralMeasure rho z hz) delta
      (upperCharacterMeasurableEquiv rho (integralControlCoefficient X q)) :=
  upperShear_measurableQuasiInvariantAtScale X rho z hz delta hdelta hnear q

/-! ### The two unit-shear mass inequalities -/

omit [Fintype X] in
/-- Transport of one measurable set by a shear whose two directions both obey
the quadratic estimate. -/
theorem sqrt_measureReal_le_of_mapsTo
    (z : E) (hz : ‖z‖ = 1) (delta : ℝ) (hdelta : 0 < delta)
    (g : Equiv.Perm (characterSpace ℂ (representedColumnPlane rho).algebra))
    (hg : KassabovBorelMeasureInequalities.MeasurableQuasiInvariantAtScale
      (columnPlaneSpectralMeasure rho z hz) delta g)
    (hginv : KassabovBorelMeasureInequalities.MeasurableQuasiInvariantAtScale
      (columnPlaneSpectralMeasure rho z hz) delta g.symm)
    {S T : Set (characterSpace ℂ (representedColumnPlane rho).algebra)}
    (hS : MeasurableSet S) (himage : MeasurableSet (g '' S))
    (hmaps : Set.MapsTo g S T) :
    Real.sqrt ((columnPlaneSpectralMeasure rho z hz).real S) ≤
      Real.sqrt ((columnPlaneSpectralMeasure rho z hz).real T) + delta := by
  have hkey := KassabovBorelMeasureInequalities.abs_sqrt_measureReal_image_sub_le
    (columnPlaneSpectralMeasure rho z hz) hdelta.le g hg hginv S hS himage
  have hsubset : g '' S ⊆ T := by
    rintro y ⟨x, hx, rfl⟩
    exact hmaps hx
  have hmono : (columnPlaneSpectralMeasure rho z hz).real (g '' S) ≤
      (columnPlaneSpectralMeasure rho z hz).real T :=
    measureReal_mono hsubset
  have hsqrt := Real.sqrt_le_sqrt hmono
  have hlower := neg_le_of_abs_le hkey
  linarith

/-- **Region `A` is dominated by region `B`.**  The lower unit shear folds `A`
into `B` and moves the vector by less than `delta`. -/
theorem sqrt_measureReal_regionA_le_regionB
    (z : E) (hz : ‖z‖ = 1) (n : ℕ) (delta : ℝ) (hdelta : 0 < delta)
    (hnear : ∀ s ∈ integralControlSet X, ‖rho s z - z‖ < delta) :
    Real.sqrt ((columnPlaneSpectralMeasure rho z hz).real
        (wordPairRegionSet rho n .A)) ≤
      Real.sqrt ((columnPlaneSpectralMeasure rho z hz).real
        (wordPairRegionSet rho n .B)) + delta := by
  have hg := lowerShear_control_measurableQuasiInvariantAtScale rho z hz delta
    hdelta hnear none
  have hginv := lowerShear_neg_control_measurableQuasiInvariantAtScale rho z hz
    delta hdelta hnear none
  refine sqrt_measureReal_le_of_mapsTo rho z hz delta hdelta
    (lowerCharacterMeasurableEquiv rho 1).toEquiv ?_ ?_
    (measurableSet_wordPairRegionSet rho n .A) ?_ ?_
  · exact hg
  · intro A hA himage
    have hfun : ∀ chi, ((lowerCharacterMeasurableEquiv rho
        (1 : FreeAlgebra ℤ X)).toEquiv).symm chi =
        lowerCharacterMeasurableEquiv rho (-(1 : FreeAlgebra ℤ X)) chi := by
      intro chi
      exact lowerCharacterMeasurableEquiv_symm_apply rho 1 chi
    have hset : ((lowerCharacterMeasurableEquiv rho
        (1 : FreeAlgebra ℤ X)).toEquiv).symm '' A =
        (lowerCharacterMeasurableEquiv rho (-(1 : FreeAlgebra ℤ X))) '' A :=
      Set.image_congr' hfun
    rw [hset]
    rw [hset] at himage
    exact hginv A hA himage
  · exact (MeasurableEquiv.measurableSet_image
      (lowerCharacterMeasurableEquiv rho 1)).mpr
      (measurableSet_wordPairRegionSet rho n .A)
  · intro chi hchi
    exact wordPairRegion_lowerUnit_eq_B_of_eq_A rho n chi hchi

/-- **Region `C` is dominated by region `B`**, by the upper unit shear. -/
theorem sqrt_measureReal_regionC_le_regionB
    (z : E) (hz : ‖z‖ = 1) (n : ℕ) (delta : ℝ) (hdelta : 0 < delta)
    (hnear : ∀ s ∈ integralControlSet X, ‖rho s z - z‖ < delta) :
    Real.sqrt ((columnPlaneSpectralMeasure rho z hz).real
        (wordPairRegionSet rho n .C)) ≤
      Real.sqrt ((columnPlaneSpectralMeasure rho z hz).real
        (wordPairRegionSet rho n .B)) + delta := by
  have hg := upperShear_control_measurableQuasiInvariantAtScale rho z hz delta
    hdelta hnear none
  have hginv := upperShear_neg_control_measurableQuasiInvariantAtScale rho z hz
    delta hdelta hnear none
  refine sqrt_measureReal_le_of_mapsTo rho z hz delta hdelta
    (upperCharacterMeasurableEquiv rho 1).toEquiv ?_ ?_
    (measurableSet_wordPairRegionSet rho n .C) ?_ ?_
  · exact hg
  · intro A hA himage
    have hfun : ∀ chi, ((upperCharacterMeasurableEquiv rho
        (1 : FreeAlgebra ℤ X)).toEquiv).symm chi =
        upperCharacterMeasurableEquiv rho (-(1 : FreeAlgebra ℤ X)) chi := by
      intro chi
      exact upperCharacterMeasurableEquiv_symm_apply rho 1 chi
    have hset : ((upperCharacterMeasurableEquiv rho
        (1 : FreeAlgebra ℤ X)).toEquiv).symm '' A =
        (upperCharacterMeasurableEquiv rho (-(1 : FreeAlgebra ℤ X))) '' A :=
      Set.image_congr' hfun
    rw [hset]
    rw [hset] at himage
    exact hginv A hA himage
  · exact (MeasurableEquiv.measurableSet_image
      (upperCharacterMeasurableEquiv rho 1)).mpr
      (measurableSet_wordPairRegionSet rho n .C)
  · intro chi hchi
    exact wordPairRegion_upperUnit_eq_B_of_eq_C rho n chi hchi

end

end IntegralGeneratorShearMass
end GroupApproximation
