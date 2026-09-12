import GroupApproximation.PropertyT.IntegralColumnPlaneSpectralTorus

/-!
# The four-shear quadratic core estimate

This file combines the exact eight-sector geometry with the four measurable
quasi-invariance inequalities.  The result is the quadratic estimate required
by the rank-zero torus bound.  All additivity steps use measurable disjoint
unions of the explicitly constructed sectors.
-/

namespace GroupApproximation
namespace IntegralColumnPlaneSpectralCoreBound

open MeasureTheory Set
open KassabovRankZeroTorusGeometry

private theorem sum_four_sqrt_le_two_sqrt_sum
    {b1 b2 b3 b4 : ℝ}
    (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2) (hb3 : 0 ≤ b3) (hb4 : 0 ≤ b4) :
    Real.sqrt b1 + Real.sqrt b2 + Real.sqrt b3 + Real.sqrt b4 ≤
      2 * Real.sqrt (b1 + b2 + b3 + b4) := by
  have hs1 := Real.sq_sqrt hb1
  have hs2 := Real.sq_sqrt hb2
  have hs3 := Real.sq_sqrt hb3
  have hs4 := Real.sq_sqrt hb4
  have hsum : 0 ≤ b1 + b2 + b3 + b4 := by positivity
  have hsqrtSum : 0 ≤ Real.sqrt (b1 + b2 + b3 + b4) :=
    Real.sqrt_nonneg _
  have hleft :
      0 ≤ Real.sqrt b1 + Real.sqrt b2 + Real.sqrt b3 + Real.sqrt b4 := by
    positivity
  apply (sq_le_sq₀ hleft (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt hsum]
  norm_num
  nlinarith [sq_nonneg (Real.sqrt b1 - Real.sqrt b2),
    sq_nonneg (Real.sqrt b1 - Real.sqrt b3),
    sq_nonneg (Real.sqrt b1 - Real.sqrt b4),
    sq_nonneg (Real.sqrt b2 - Real.sqrt b3),
    sq_nonneg (Real.sqrt b2 - Real.sqrt b4),
    sq_nonneg (Real.sqrt b3 - Real.sqrt b4)]

/-- The four exact shear transports imply the quadratic core estimate.  The
two outer-strip assumptions are used only to bound the total mass of the four
overflow sectors by `epsilon²`. -/
theorem core_quadratic_of_four_shear_quasiInvariant
    (mu : Measure Torus) [IsFiniteMeasure mu] {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hvertical : mu.real verticalOuter ≤ epsilon ^ 2 / 2)
    (hhorizontal : mu.real horizontalOuter ≤ epsilon ^ 2 / 2)
    (h12Plus :
      KassabovBorelMeasureInequalities.MeasurableQuasiInvariantAtScale
        mu epsilon g12Plus)
    (h12Minus :
      KassabovBorelMeasureInequalities.MeasurableQuasiInvariantAtScale
        mu epsilon g12Minus)
    (h21Plus :
      KassabovBorelMeasureInequalities.MeasurableQuasiInvariantAtScale
        mu epsilon g21Plus)
    (h21Minus :
      KassabovBorelMeasureInequalities.MeasurableQuasiInvariantAtScale
        mu epsilon g21Minus) :
    mu.real puncturedCentralSquare ≤ 5 * epsilon ^ 2 +
      4 * epsilon *
        Real.sqrt (mu.real puncturedCentralSquare + epsilon ^ 2) := by
  have h34 :
      mu.real (sector3 ∪ sector4) =
        mu.real sector3 + mu.real sector4 :=
    measureReal_union disjoint_sector3_sector4 measurableSet_sector4
  have h12 :
      mu.real (sector1 ∪ sector2) =
        mu.real sector1 + mu.real sector2 :=
    measureReal_union disjoint_sector1_sector2 measurableSet_sector2
  have h3p4 :
      mu.real (sector3 ∪ sectorPrime4) =
        mu.real sector3 + mu.real sectorPrime4 :=
    measureReal_union disjoint_sector3_sectorPrime4 measurableSet_sectorPrime4
  have hp3_4 :
      mu.real (sectorPrime3 ∪ sector4) =
        mu.real sectorPrime3 + mu.real sector4 :=
    measureReal_union disjoint_sectorPrime3_sector4 measurableSet_sector4
  have hp1_2 :
      mu.real (sectorPrime1 ∪ sector2) =
        mu.real sectorPrime1 + mu.real sector2 :=
    measureReal_union disjoint_sectorPrime1_sector2 measurableSet_sector2
  have h1p2 :
      mu.real (sector1 ∪ sectorPrime2) =
        mu.real sector1 + mu.real sectorPrime2 :=
    measureReal_union disjoint_sector1_sectorPrime2 measurableSet_sectorPrime2
  have hA4 :
      mu.real sector4 ≤ mu.real sectorPrime4 +
        2 * epsilon *
          Real.sqrt (mu.real sector3 + mu.real sectorPrime4) + epsilon ^ 2 := by
    have hq := h12Plus (sector3 ∪ sectorPrime4)
      (measurableSet_sector3.union measurableSet_sectorPrime4)
      (by
        rw [g12Plus_image_sector3_union_sectorPrime4_eq_sector3_union_sector4]
        exact measurableSet_sector3.union measurableSet_sector4)
    rw [g12Plus_image_sector3_union_sectorPrime4_eq_sector3_union_sector4,
      h34, h3p4] at hq
    linarith [le_abs_self
      ((mu.real sector3 + mu.real sector4) -
        (mu.real sector3 + mu.real sectorPrime4))]
  have hA3 :
      mu.real sector3 ≤ mu.real sectorPrime3 +
        2 * epsilon *
          Real.sqrt (mu.real sectorPrime3 + mu.real sector4) + epsilon ^ 2 := by
    have hq := h21Plus (sectorPrime3 ∪ sector4)
      (measurableSet_sectorPrime3.union measurableSet_sector4)
      (by
        rw [g21Plus_image_sectorPrime3_union_sector4_eq_sector3_union_sector4]
        exact measurableSet_sector3.union measurableSet_sector4)
    rw [g21Plus_image_sectorPrime3_union_sector4_eq_sector3_union_sector4,
      h34, hp3_4] at hq
    linarith [le_abs_self
      ((mu.real sector3 + mu.real sector4) -
        (mu.real sectorPrime3 + mu.real sector4))]
  have hA1 :
      mu.real sector1 ≤ mu.real sectorPrime1 +
        2 * epsilon *
          Real.sqrt (mu.real sectorPrime1 + mu.real sector2) + epsilon ^ 2 := by
    have hq := h12Minus (sectorPrime1 ∪ sector2)
      (measurableSet_sectorPrime1.union measurableSet_sector2)
      (by
        rw [g12Minus_image_sectorPrime1_union_sector2_eq_sector1_union_sector2]
        exact measurableSet_sector1.union measurableSet_sector2)
    rw [g12Minus_image_sectorPrime1_union_sector2_eq_sector1_union_sector2,
      h12, hp1_2] at hq
    linarith [le_abs_self
      ((mu.real sector1 + mu.real sector2) -
        (mu.real sectorPrime1 + mu.real sector2))]
  have hA2 :
      mu.real sector2 ≤ mu.real sectorPrime2 +
        2 * epsilon *
          Real.sqrt (mu.real sector1 + mu.real sectorPrime2) + epsilon ^ 2 := by
    have hq := h21Minus (sector1 ∪ sectorPrime2)
      (measurableSet_sector1.union measurableSet_sectorPrime2)
      (by
        rw [g21Minus_image_sector1_union_sectorPrime2_eq_sector1_union_sector2]
        exact measurableSet_sector1.union measurableSet_sector2)
    rw [g21Minus_image_sector1_union_sectorPrime2_eq_sector1_union_sector2,
      h12, h1p2] at hq
    linarith [le_abs_self
      ((mu.real sector1 + mu.real sector2) -
        (mu.real sector1 + mu.real sectorPrime2))]
  have hp14 :
      mu.real sectorPrime1 + mu.real sectorPrime4 ≤
        mu.real verticalOuter := by
    rw [← measureReal_union disjoint_sectorPrime1_sectorPrime4
      measurableSet_sectorPrime4]
    exact measureReal_mono
      sectorPrime1_union_sectorPrime4_subset_verticalOuter
  have hp23 :
      mu.real sectorPrime2 + mu.real sectorPrime3 ≤
        mu.real horizontalOuter := by
    rw [← measureReal_union disjoint_sectorPrime2_sectorPrime3
      measurableSet_sectorPrime3]
    exact measureReal_mono
      sectorPrime2_union_sectorPrime3_subset_horizontalOuter
  have hp :
      mu.real sectorPrime1 + mu.real sectorPrime2 +
          mu.real sectorPrime3 + mu.real sectorPrime4 ≤ epsilon ^ 2 := by
    nlinarith
  have hcentralDisjoint :
      Disjoint (sector1 ∪ sector2) (sector3 ∪ sector4) := by
    rw [sector1_union_sector2, sector3_union_sector4]
    exact disjoint_sameSignCentral_oppositeSignCentral
  have hcore :
      mu.real puncturedCentralSquare =
        mu.real sector1 + mu.real sector2 +
          mu.real sector3 + mu.real sector4 := by
    rw [← fourCentralSectors_union,
      measureReal_union hcentralDisjoint
        (measurableSet_sector3.union measurableSet_sector4), h12, h34]
    ring
  have hroot := sum_four_sqrt_le_two_sqrt_sum
    (add_nonneg measureReal_nonneg measureReal_nonneg)
    (add_nonneg measureReal_nonneg measureReal_nonneg)
    (add_nonneg measureReal_nonneg measureReal_nonneg)
    (add_nonneg measureReal_nonneg measureReal_nonneg)
    (b1 := mu.real sectorPrime1 + mu.real sector2)
    (b2 := mu.real sector1 + mu.real sectorPrime2)
    (b3 := mu.real sectorPrime3 + mu.real sector4)
    (b4 := mu.real sector3 + mu.real sectorPrime4)
  have hrootSum :
      Real.sqrt (mu.real sectorPrime1 + mu.real sector2) +
          Real.sqrt (mu.real sector1 + mu.real sectorPrime2) +
          Real.sqrt (mu.real sectorPrime3 + mu.real sector4) +
          Real.sqrt (mu.real sector3 + mu.real sectorPrime4) ≤
        2 * Real.sqrt (mu.real puncturedCentralSquare + epsilon ^ 2) := by
    have hsum :
        (mu.real sectorPrime1 + mu.real sector2) +
            (mu.real sector1 + mu.real sectorPrime2) +
            (mu.real sectorPrime3 + mu.real sector4) +
            (mu.real sector3 + mu.real sectorPrime4) ≤
          mu.real puncturedCentralSquare + epsilon ^ 2 := by
      rw [hcore]
      linarith [hp]
    exact hroot.trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsum) (by norm_num))
  have htwoeps : 0 ≤ 2 * epsilon :=
    mul_nonneg (by norm_num) hepsilon
  have hcross := mul_le_mul_of_nonneg_left hrootSum htwoeps
  have hsumA :
      mu.real sector1 + mu.real sector2 +
          mu.real sector3 + mu.real sector4 ≤
        mu.real sectorPrime1 + mu.real sectorPrime2 +
            mu.real sectorPrime3 + mu.real sectorPrime4 +
          2 * epsilon *
            (Real.sqrt (mu.real sectorPrime1 + mu.real sector2) +
              Real.sqrt (mu.real sector1 + mu.real sectorPrime2) +
              Real.sqrt (mu.real sectorPrime3 + mu.real sector4) +
              Real.sqrt (mu.real sector3 + mu.real sectorPrime4)) +
          4 * epsilon ^ 2 := by
    linarith [hA1, hA2, hA3, hA4]
  rw [hcore] at hcross ⊢
  nlinarith [hp, hsumA, hcross]

/-- The quadratic core estimate and the torus cover give the exact terminal
mass bound. -/
theorem total_mass_le_of_four_shear_quasiInvariant
    (mu : Measure Torus) [IsFiniteMeasure mu] {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hvertical : mu.real verticalOuter ≤ epsilon ^ 2 / 2)
    (hhorizontal : mu.real horizontalOuter ≤ epsilon ^ 2 / 2)
    (h12Plus :
      KassabovBorelMeasureInequalities.MeasurableQuasiInvariantAtScale
        mu epsilon g12Plus)
    (h12Minus :
      KassabovBorelMeasureInequalities.MeasurableQuasiInvariantAtScale
        mu epsilon g12Minus)
    (h21Plus :
      KassabovBorelMeasureInequalities.MeasurableQuasiInvariantAtScale
        mu epsilon g21Plus)
    (h21Minus :
      KassabovBorelMeasureInequalities.MeasurableQuasiInvariantAtScale
        mu epsilon g21Minus) :
    mu.real (Set.univ \ {(0, 0)}) ≤
      (2 + Real.sqrt 10) ^ 2 * epsilon ^ 2 := by
  exact total_mass_le_of_core_quadratic mu hepsilon hvertical hhorizontal
    (core_quadratic_of_four_shear_quasiInvariant mu hepsilon
      hvertical hhorizontal h12Plus h12Minus h21Plus h21Minus)

end IntegralColumnPlaneSpectralCoreBound
end GroupApproximation

open GroupApproximation.IntegralColumnPlaneSpectralCoreBound

#audit_axioms core_quadratic_of_four_shear_quasiInvariant
#audit_axioms total_mass_le_of_four_shear_quasiInvariant
