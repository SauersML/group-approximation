import GroupApproximation.PropertyT.IntegralColumnPlaneSpectralCoreBound
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Scalar spectral mass bound for the integral column plane

The unit-root displacement identities control the two outer strips of the
scalar torus.  Combining those bounds with the four-shear theorem gives the
exact mass estimate away from the trivial scalar character.
-/

namespace GroupApproximation
namespace IntegralColumnPlaneSpectralMassBound

open MeasureTheory Set WeakDual
open IntegralCharacterMass IntegralColumnPlaneSpectralMeasure
open IntegralColumnPlaneSpectralTorus IntegralColumnPlaneSpectralCoreBound
open KassabovRankZeroTorusGeometry
open RepresentedRootPlaneSpectralMeasure

noncomputable section

universe u v

/-- A point at least one quarter of the way around the additive circle has
squared chordal displacement from `1` at least `2`. -/
theorem two_le_norm_toCircle_sub_one_sq_of_one_fourth_le_abs_centered
    (x : AddCircle (1 : ℝ))
    (hx : (1 / 4 : ℝ) ≤ |centeredRepresentative x|) :
    2 ≤ ‖(x.toCircle : ℂ) - 1‖ ^ 2 := by
  let r := centeredRepresentative x
  have hrange :=
    (AddCircle.measurableEquivIoc (1 : ℝ) (-(1 / 2 : ℝ)) x).property
  change -(1 / 2 : ℝ) < r ∧ r ≤ -(1 / 2 : ℝ) + 1 at hrange
  have habsle : |r| ≤ (1 / 2 : ℝ) := by
    rw [abs_le]
    constructor <;> linarith
  have hangleLower : Real.pi / 2 ≤ |2 * Real.pi * r| := by
    have htwoPi : 0 ≤ 2 * Real.pi :=
      mul_nonneg (by norm_num) Real.pi_pos.le
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_pos Real.pi_pos]
    have hx' : (1 / 4 : ℝ) ≤ |r| := hx
    have hmul := mul_le_mul_of_nonneg_left hx' htwoPi
    nlinarith
  have hangleUpper :
      |2 * Real.pi * r| ≤ Real.pi + Real.pi / 2 := by
    have htwoPi : 0 ≤ 2 * Real.pi :=
      mul_nonneg (by norm_num) Real.pi_pos.le
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_pos Real.pi_pos]
    have hmul := mul_le_mul_of_nonneg_left habsle htwoPi
    nlinarith [Real.pi_pos]
  have hcos : Real.cos (2 * Real.pi * r) ≤ 0 := by
    rw [← Real.cos_abs]
    exact Real.cos_nonpos_of_pi_div_two_le_of_le hangleLower hangleUpper
  have hre : ((x.toCircle : Circle) : ℂ).re =
      Real.cos (2 * Real.pi * r) := by
    rw [← coe_centeredRepresentative x]
    change ((AddCircle.toCircle (r : AddCircle (1 : ℝ)) : Circle) : ℂ).re = _
    rw [AddCircle.toCircle_apply_mk, div_one, Circle.coe_exp]
    exact Complex.exp_ofReal_mul_I_re _
  rw [Complex.norm_sub_one_sq_eq_of_norm_eq_one (by
    exact x.toCircle.norm_coe), hre]
  linarith

private def firstChordSq (p : Torus) : ℝ :=
  ‖(p.1.toCircle : ℂ) - 1‖ ^ 2

private def secondChordSq (p : Torus) : ℝ :=
  ‖(p.2.toCircle : ℂ) - 1‖ ^ 2

private theorem continuous_firstChordSq : Continuous firstChordSq := by
  unfold firstChordSq
  fun_prop

private theorem continuous_secondChordSq : Continuous secondChordSq := by
  unfold secondChordSq
  fun_prop

private theorem two_mul_measureReal_verticalOuter_le_integral_firstChordSq
    (mu : Measure Torus) [IsFiniteMeasure mu] :
    2 * mu.real verticalOuter ≤ ∫ p, firstChordSq p ∂mu := by
  have hconst : Integrable (fun _ : Torus ↦ (2 : ℝ)) mu := integrable_const 2
  have hleft := hconst.indicator measurableSet_verticalOuter
  have hright : Integrable firstChordSq mu :=
    continuous_firstChordSq.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace firstChordSq)
  have hmono :
      ∫ p, verticalOuter.indicator (fun _ ↦ (2 : ℝ)) p ∂mu ≤
        ∫ p, firstChordSq p ∂mu := by
    apply integral_mono hleft hright
    intro p
    by_cases hp : p ∈ verticalOuter
    · rw [indicator_of_mem hp]
      exact two_le_norm_toCircle_sub_one_sq_of_one_fourth_le_abs_centered
        p.1 hp
    · rw [Set.indicator_of_notMem hp]
      exact sq_nonneg _
  rw [integral_indicator_const (2 : ℝ) measurableSet_verticalOuter] at hmono
  simpa [smul_eq_mul, mul_comm] using hmono

private theorem two_mul_measureReal_horizontalOuter_le_integral_secondChordSq
    (mu : Measure Torus) [IsFiniteMeasure mu] :
    2 * mu.real horizontalOuter ≤ ∫ p, secondChordSq p ∂mu := by
  have hconst : Integrable (fun _ : Torus ↦ (2 : ℝ)) mu := integrable_const 2
  have hleft := hconst.indicator measurableSet_horizontalOuter
  have hright : Integrable secondChordSq mu :=
    continuous_secondChordSq.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace secondChordSq)
  have hmono :
      ∫ p, horizontalOuter.indicator (fun _ ↦ (2 : ℝ)) p ∂mu ≤
        ∫ p, secondChordSq p ∂mu := by
    apply integral_mono hleft hright
    intro p
    by_cases hp : p ∈ horizontalOuter
    · rw [indicator_of_mem hp]
      exact two_le_norm_toCircle_sub_one_sq_of_one_fourth_le_abs_centered
        p.2 hp
    · rw [Set.indicator_of_notMem hp]
      exact sq_nonneg _
  rw [integral_indicator_const (2 : ℝ) measurableSet_horizontalOuter] at hmono
  simpa [smul_eq_mul, mul_comm] using hmono

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]
variable {X : Type u} [Fintype X]

private abbrev R := FreeAlgebra ℤ X
private abbrev P
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E)) :=
  representedColumnPlane rho

private abbrev Spectrum
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E)) :=
  characterSpace ℂ (P rho).algebra

noncomputable local instance representedColumnPlaneSpectrumMeasurableSpace
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E)) :
    MeasurableSpace (Spectrum rho) :=
  borel _

local instance representedColumnPlaneSpectrumBorelSpace
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E)) :
    BorelSpace (Spectrum rho) :=
  ⟨rfl⟩

noncomputable local instance scalarTorusMeasureIsFinite
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (hz : ‖z‖ = 1) :
    IsFiniteMeasure (scalarTorusMeasure rho z hz) := by
  unfold scalarTorusMeasure
  exact Measure.isFiniteMeasure_map _ _

/-! ### The scalar zero fiber versus the full plane support -/

omit [Fintype X] in
/-- A scalar torus coordinate is zero exactly when the character is trivial
on the two unit-coefficient column roots. -/
theorem scalarTorusCoordinate_eq_zero_iff
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (chi : Spectrum rho) :
    scalarTorusCoordinate rho chi = (0, 0) ↔
      chi ((P rho).coordinate (0, 1)) = 1 ∧
        chi ((P rho).coordinate (1, 1)) = 1 := by
  constructor
  · intro hzero
    have hzero0 := congrArg Prod.fst hzero
    have hzero1 := congrArg Prod.snd hzero
    change coordinateAngle rho (0, 1) chi = 0 at hzero0
    change coordinateAngle rho (1, 1) chi = 0 at hzero1
    have hcircle0 := congrArg
      (fun a : AddCircle (1 : ℝ) ↦ (a.toCircle : ℂ)) hzero0
    have hcircle1 := congrArg
      (fun a : AddCircle (1 : ℝ) ↦ (a.toCircle : ℂ)) hzero1
    rw [coordinateAngle_toCircle, coordinateCircle_coe,
      AddCircle.toCircle_zero] at hcircle0 hcircle1
    exact ⟨hcircle0, hcircle1⟩
  · rintro ⟨hzero0, hzero1⟩
    apply Prod.ext
    · change coordinateAngle rho (0, 1) chi = 0
      apply AddCircle.injective_toCircle (by norm_num)
      rw [coordinateAngle_toCircle, AddCircle.toCircle_zero]
      apply Circle.ext
      exact hzero0
    · change coordinateAngle rho (1, 1) chi = 0
      apply AddCircle.injective_toCircle (by norm_num)
      rw [coordinateAngle_toCircle, AddCircle.toCircle_zero]
      apply Circle.ext
      exact hzero1

/-- Characters detected as nontrivial by the two unit-coefficient column
roots. -/
def unitRootNontrivialSet
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E)) :
    Set (Spectrum rho) :=
  {chi | chi ((P rho).coordinate (0, 1)) ≠ 1 ∨
    chi ((P rho).coordinate (1, 1)) ≠ 1}

/-- Characters nontrivial on at least one coefficient in the full represented
column plane. -/
def fullPlaneNontrivialSet
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E)) :
    Set (Spectrum rho) :=
  {chi | ∃ q : Fin 2 × R (X := X), chi ((P rho).coordinate q) ≠ 1}

/-- One arbitrary coefficient coordinate is zero precisely when the
corresponding character evaluation is trivial. -/
theorem coordinateAngle_eq_zero_iff
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (q : Fin 2 × R (X := X)) (chi : Spectrum rho) :
    coordinateAngle rho q chi = 0 ↔
      chi ((P rho).coordinate q) = 1 := by
  constructor
  · intro hzero
    have hcircle := congrArg
      (fun a : AddCircle (1 : ℝ) ↦ (a.toCircle : ℂ)) hzero
    rw [coordinateAngle_toCircle, coordinateCircle_coe,
      AddCircle.toCircle_zero] at hcircle
    exact hcircle
  · intro hzero
    apply AddCircle.injective_toCircle (by norm_num)
    rw [coordinateAngle_toCircle, AddCircle.toCircle_zero]
    apply Circle.ext
    exact hzero

/-- The part of the character spectrum detected by a finite family of
coefficient coordinates. -/
def finitePlaneNontrivialSet
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (s : Finset (Fin 2 × R (X := X))) : Set (Spectrum rho) :=
  {chi | ∃ q ∈ s, chi ((P rho).coordinate q) ≠ 1}

omit [Fintype X] in
theorem finitePlaneNontrivialSet_mono
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    {s t : Finset (Fin 2 × R (X := X))} (hst : s ⊆ t) :
    finitePlaneNontrivialSet rho s ⊆ finitePlaneNontrivialSet rho t := by
  rintro chi ⟨q, hqs, hq⟩
  exact ⟨q, hst hqs, hq⟩

omit [Fintype X] in
theorem measurableSet_finitePlaneNontrivialSet
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (s : Finset (Fin 2 × R (X := X))) :
    MeasurableSet (finitePlaneNontrivialSet rho s) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa [finitePlaneNontrivialSet] using
        (MeasurableSet.empty : MeasurableSet (∅ : Set (Spectrum rho)))
  | @insert q s hqs ih =>
      have hsingle : MeasurableSet
          {chi : Spectrum rho | chi ((P rho).coordinate q) ≠ 1} := by
        have hset :
            {chi : Spectrum rho | chi ((P rho).coordinate q) ≠ 1} =
              coordinateAngle rho q ⁻¹' ({0}ᶜ : Set (AddCircle (1 : ℝ))) := by
          ext chi
          exact not_congr (coordinateAngle_eq_zero_iff rho q chi)
        rw [hset]
        exact (measurableSet_singleton (0 : AddCircle (1 : ℝ))).compl.preimage
          (continuous_coordinateAngle rho q).measurable
      have hunion : finitePlaneNontrivialSet rho (insert q s) =
          {chi : Spectrum rho | chi ((P rho).coordinate q) ≠ 1} ∪
            finitePlaneNontrivialSet rho s := by
        ext chi
        simp [finitePlaneNontrivialSet]
      rw [hunion]
      exact hsingle.union ih

omit [Fintype X] in
theorem iUnion_finitePlaneNontrivialSet
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E)) :
    (⋃ s : Finset (Fin 2 × R (X := X)), finitePlaneNontrivialSet rho s) =
      fullPlaneNontrivialSet rho := by
  classical
  ext chi
  constructor
  · rintro ⟨s, q, _, hq⟩
    exact ⟨q, hq⟩
  · rintro ⟨q, hq⟩
    exact ⟨{q}, q, Finset.mem_singleton_self q, hq⟩

/-- For a finite generator type, the full nontrivial support is measurable:
it is the countable union of its finite-coordinate pieces. -/
theorem measurableSet_fullPlaneNontrivialSet
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E)) :
    MeasurableSet (fullPlaneNontrivialSet rho) := by
  rw [← iUnion_finitePlaneNontrivialSet rho]
  exact MeasurableSet.iUnion fun s ↦
    measurableSet_finitePlaneNontrivialSet rho s

/-- Evaluation on a finite coefficient family gives an honest
finite-dimensional additive torus. -/
noncomputable def finitePlaneCoordinate
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (s : Finset (Fin 2 × R (X := X))) (chi : Spectrum rho) :
    s → AddCircle (1 : ℝ) :=
  fun q ↦ coordinateAngle rho q.1 chi

omit [Fintype X] in
theorem measurable_finitePlaneCoordinate
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (s : Finset (Fin 2 × R (X := X))) :
    Measurable (finitePlaneCoordinate rho s) := by
  apply measurable_pi_lambda
  intro q
  exact (continuous_coordinateAngle rho q.1).measurable

omit [Fintype X] in
theorem finitePlaneCoordinate_preimage_punctured
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (s : Finset (Fin 2 × R (X := X))) :
    finitePlaneCoordinate rho s ⁻¹'
        (Set.univ \ {(0 : s → AddCircle (1 : ℝ))}) =
      finitePlaneNontrivialSet rho s := by
  classical
  ext chi
  constructor
  · intro hchi
    have hne : finitePlaneCoordinate rho s chi ≠ 0 := hchi.2
    by_contra hnot
    apply hne
    funext q
    apply (coordinateAngle_eq_zero_iff rho q.1 chi).mpr
    by_contra hq
    apply hnot
    exact ⟨q.1, q.2, hq⟩
  · rintro ⟨q, hqs, hq⟩
    refine ⟨Set.mem_univ _, ?_⟩
    intro hzero
    have hcoordinate := congrFun (Set.mem_singleton_iff.mp hzero) ⟨q, hqs⟩
    change coordinateAngle rho q chi = 0 at hcoordinate
    exact hq ((coordinateAngle_eq_zero_iff rho q chi).mp hcoordinate)

/-- The finite-torus pushforward of the full column-plane spectral measure. -/
noncomputable def finitePlaneMeasure
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (hz : ‖z‖ = 1)
    (s : Finset (Fin 2 × R (X := X))) :
    Measure (s → AddCircle (1 : ℝ)) :=
  Measure.map (finitePlaneCoordinate rho s)
    (CommutativeStateSpectralMeasure.stateSpectralMeasure
      ((P rho).vectorState (Complexification.mk z 0)
        (norm_mk_zero_eq_one hz)))

omit [Fintype X] in
theorem finitePlaneMeasure_punctured_eq
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (hz : ‖z‖ = 1)
    (s : Finset (Fin 2 × R (X := X))) :
    (finitePlaneMeasure rho z hz s).real
        (Set.univ \ {(0 : s → AddCircle (1 : ℝ))}) =
      (CommutativeStateSpectralMeasure.stateSpectralMeasure
        ((P rho).vectorState (Complexification.mk z 0)
          (norm_mk_zero_eq_one hz))).real
        (finitePlaneNontrivialSet rho s) := by
  have hpunctured : MeasurableSet
      (Set.univ \ ({(0 : s → AddCircle (1 : ℝ))} :
        Set (s → AddCircle (1 : ℝ)))) :=
    MeasurableSet.univ.diff (measurableSet_singleton 0)
  unfold finitePlaneMeasure
  rw [map_measureReal_apply (measurable_finitePlaneCoordinate rho s) hpunctured]
  rw [finitePlaneCoordinate_preimage_punctured]

omit [Fintype X] in
theorem scalarTorusCoordinate_preimage_punctured
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E)) :
    scalarTorusCoordinate rho ⁻¹' (Set.univ \ {(0, 0)}) =
      unitRootNontrivialSet rho := by
  classical
  ext chi
  constructor
  · intro hchi
    have hne : scalarTorusCoordinate rho chi ≠ (0, 0) := hchi.2
    have hnotBoth : ¬
        (chi ((P rho).coordinate (0, 1)) = 1 ∧
          chi ((P rho).coordinate (1, 1)) = 1) :=
      (not_congr (scalarTorusCoordinate_eq_zero_iff rho chi)).mp hne
    exact not_and_or.mp hnotBoth
  · intro hchi
    refine ⟨Set.mem_univ _, ?_⟩
    intro hzero
    have hboth := (scalarTorusCoordinate_eq_zero_iff rho chi).mp
      (Set.mem_singleton_iff.mp hzero)
    rcases hchi with hzero0 | hzero1
    · exact hzero0 hboth.1
    · exact hzero1 hboth.2

omit [Fintype X] in
theorem unitRootNontrivialSet_subset_fullPlaneNontrivialSet
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E)) :
    unitRootNontrivialSet rho ⊆ fullPlaneNontrivialSet rho := by
  intro chi hchi
  rcases hchi with hzero | hone
  · exact ⟨(0, 1), hzero⟩
  · exact ⟨(1, 1), hone⟩

omit [Fintype X] in
/-- The pushed mass away from the scalar origin is exactly the original
spectral mass detected by the two unit roots. -/
theorem scalarTorusMeasure_punctured_eq_unitRootNontrivialSet
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (hz : ‖z‖ = 1) :
    (scalarTorusMeasure rho z hz).real (Set.univ \ {(0, 0)}) =
      (CommutativeStateSpectralMeasure.stateSpectralMeasure
        ((P rho).vectorState (Complexification.mk z 0)
          (norm_mk_zero_eq_one hz))).real (unitRootNontrivialSet rho) := by
  have hpunctured : MeasurableSet
      (Set.univ \ ({(0, 0)} : Set Torus)) :=
    MeasurableSet.univ.diff (measurableSet_singleton (0, 0))
  unfold scalarTorusMeasure
  rw [map_measureReal_apply (continuous_scalarTorusCoordinate rho).measurable
    hpunctured]
  rw [scalarTorusCoordinate_preimage_punctured]

omit [Fintype X] in
/-- Consequently, the scalar punctured mass is bounded above by the spectral
mass nontrivial on the full column plane.  This is the direction opposite to
the one needed to deduce a full-plane moving-projection bound from the scalar
torus estimate. -/
theorem scalarTorusMeasure_punctured_le_fullPlaneNontrivialSet
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (hz : ‖z‖ = 1) :
    (scalarTorusMeasure rho z hz).real (Set.univ \ {(0, 0)}) ≤
      (CommutativeStateSpectralMeasure.stateSpectralMeasure
        ((P rho).vectorState (Complexification.mk z 0)
          (norm_mk_zero_eq_one hz))).real (fullPlaneNontrivialSet rho) := by
  rw [scalarTorusMeasure_punctured_eq_unitRootNontrivialSet]
  exact measureReal_mono
    (unitRootNontrivialSet_subset_fullPlaneNontrivialSet rho)

omit [Fintype X] in
theorem integral_firstChordSq_scalarTorusMeasure
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (hz : ‖z‖ = 1) :
    ∫ p, firstChordSq p ∂scalarTorusMeasure rho z hz =
      ‖rho (columnRoot (0, 1)) z - z‖ ^ 2 := by
  unfold scalarTorusMeasure
  rw [integral_map_of_stronglyMeasurable
    (continuous_scalarTorusCoordinate rho).measurable
    continuous_firstChordSq.stronglyMeasurable]
  calc
    ∫ chi, firstChordSq (scalarTorusCoordinate rho chi)
        ∂CommutativeStateSpectralMeasure.stateSpectralMeasure
          ((P rho).vectorState (Complexification.mk z 0)
            (norm_mk_zero_eq_one hz)) =
      ∫ chi, ‖chi ((P rho).coordinate (0, 1)) - 1‖ ^ 2
        ∂CommutativeStateSpectralMeasure.stateSpectralMeasure
          ((P rho).vectorState (Complexification.mk z 0)
            (norm_mk_zero_eq_one hz)) := by
      apply integral_congr_ae
      filter_upwards [] with chi
      unfold firstChordSq scalarTorusCoordinate
      rw [coordinateAngle_toCircle, coordinateCircle_coe]
    _ = ‖rho (columnRoot (0, 1)) z - z‖ ^ 2 :=
      integral_columnRoot_displacement_sq rho z hz (0, 1)

omit [Fintype X] in
theorem integral_secondChordSq_scalarTorusMeasure
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (hz : ‖z‖ = 1) :
    ∫ p, secondChordSq p ∂scalarTorusMeasure rho z hz =
      ‖rho (columnRoot (1, 1)) z - z‖ ^ 2 := by
  unfold scalarTorusMeasure
  rw [integral_map_of_stronglyMeasurable
    (continuous_scalarTorusCoordinate rho).measurable
    continuous_secondChordSq.stronglyMeasurable]
  calc
    ∫ chi, secondChordSq (scalarTorusCoordinate rho chi)
        ∂CommutativeStateSpectralMeasure.stateSpectralMeasure
          ((P rho).vectorState (Complexification.mk z 0)
            (norm_mk_zero_eq_one hz)) =
      ∫ chi, ‖chi ((P rho).coordinate (1, 1)) - 1‖ ^ 2
        ∂CommutativeStateSpectralMeasure.stateSpectralMeasure
          ((P rho).vectorState (Complexification.mk z 0)
            (norm_mk_zero_eq_one hz)) := by
      apply integral_congr_ae
      filter_upwards [] with chi
      unfold secondChordSq scalarTorusCoordinate
      rw [coordinateAngle_toCircle, coordinateCircle_coe]
    _ = ‖rho (columnRoot (1, 1)) z - z‖ ^ 2 :=
      integral_columnRoot_displacement_sq rho z hz (1, 1)

private theorem columnRoot_zero_one_mem_integralControlSet :
    columnRoot ((0 : Fin 2), (1 : R (X := X))) ∈ integralControlSet X := by
  let a : A2Root := ⟨((0 : Fin 3), (2 : Fin 3)), by decide⟩
  have hm := integralControlElement_mem X (a, none)
  simpa [a, integralControlElement, integralControlCoefficient, columnRoot,
    columnSource] using hm

private theorem columnRoot_one_one_mem_integralControlSet :
    columnRoot ((1 : Fin 2), (1 : R (X := X))) ∈ integralControlSet X := by
  let a : A2Root := ⟨((1 : Fin 3), (2 : Fin 3)), by decide⟩
  have hm := integralControlElement_mem X (a, none)
  simpa [a, integralControlElement, integralControlCoefficient, columnRoot,
    columnSource] using hm

theorem scalarTorusMeasure_verticalOuter_le
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (hz : ‖z‖ = 1) (delta : ℝ)
    (hdelta : 0 < delta)
    (hnear : ∀ s ∈ integralControlSet X, ‖rho s z - z‖ < delta) :
    (scalarTorusMeasure rho z hz).real verticalOuter ≤ delta ^ 2 / 2 := by
  have hroot := hnear _ columnRoot_zero_one_mem_integralControlSet
  have hintegral := two_mul_measureReal_verticalOuter_le_integral_firstChordSq
    (scalarTorusMeasure rho z hz)
  rw [integral_firstChordSq_scalarTorusMeasure rho z hz] at hintegral
  have hsq : ‖rho (columnRoot (0, 1)) z - z‖ ^ 2 < delta ^ 2 :=
    (sq_lt_sq₀ (norm_nonneg _) hdelta.le).mpr hroot
  linarith

theorem scalarTorusMeasure_horizontalOuter_le
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (hz : ‖z‖ = 1) (delta : ℝ)
    (hdelta : 0 < delta)
    (hnear : ∀ s ∈ integralControlSet X, ‖rho s z - z‖ < delta) :
    (scalarTorusMeasure rho z hz).real horizontalOuter ≤ delta ^ 2 / 2 := by
  have hroot := hnear _ columnRoot_one_one_mem_integralControlSet
  have hintegral :=
    two_mul_measureReal_horizontalOuter_le_integral_secondChordSq
      (scalarTorusMeasure rho z hz)
  rw [integral_secondChordSq_scalarTorusMeasure rho z hz] at hintegral
  have hsq : ‖rho (columnRoot (1, 1)) z - z‖ ^ 2 < delta ^ 2 :=
    (sq_lt_sq₀ (norm_nonneg _) hdelta.le).mpr hroot
  linarith

/-- The scalar torus spectral measure has uniformly small mass away from its
trivial character. -/
theorem scalarTorusMeasure_punctured_mass_le
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (hz : ‖z‖ = 1) (delta : ℝ)
    (hdelta : 0 < delta)
    (hnear : ∀ s ∈ integralControlSet X, ‖rho s z - z‖ < delta) :
    (scalarTorusMeasure rho z hz).real (Set.univ \ {(0, 0)}) ≤
      (2 + Real.sqrt 10) ^ 2 * delta ^ 2 := by
  apply total_mass_le_of_four_shear_quasiInvariant
    (scalarTorusMeasure rho z hz) hdelta.le
    (scalarTorusMeasure_verticalOuter_le rho z hz delta hdelta hnear)
    (scalarTorusMeasure_horizontalOuter_le rho z hz delta hdelta hnear)
  · exact scalarTorusMeasure_measurableQuasiInvariantAtScale_g12Plus
      X rho z hz delta hdelta hnear
  · exact scalarTorusMeasure_measurableQuasiInvariantAtScale_g12Minus
      X rho z hz delta hdelta hnear
  · exact scalarTorusMeasure_measurableQuasiInvariantAtScale_g21Plus
      X rho z hz delta hdelta hnear
  · exact scalarTorusMeasure_measurableQuasiInvariantAtScale_g21Minus
      X rho z hz delta hdelta hnear

end
end IntegralColumnPlaneSpectralMassBound
end GroupApproximation

open GroupApproximation.IntegralColumnPlaneSpectralMassBound

#audit_axioms scalarTorusMeasure_verticalOuter_le
#audit_axioms scalarTorusMeasure_horizontalOuter_le
#audit_axioms scalarTorusMeasure_punctured_mass_le
