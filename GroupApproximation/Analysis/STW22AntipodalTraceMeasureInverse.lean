import GroupApproximation.Analysis.STW22AntipodalBoundaryMeasureTrace
import GroupApproximation.Analysis.STW22AntipodalBlockTraceAffineEquiv

/-!
# The trace--boundary-measure round trip

The probability measure assembled from an actual trace of the antipodal
scalar-tail algebra recovers that trace when integrated against the literal
boundary family.  The proof first recovers each coordinate corner, then uses
the canonical scalar-tail truncations and contractivity of tracial states.
-/

namespace GroupApproximation
namespace STW22AntipodalTraceMeasureInverse

open Filter MeasureTheory
open STW22
open STW22ActualTraceSpaces
open STW22BaseAlgebraUnitization
open STW22BaseAlgebraNuclear
open STW22BaseUniformTracialGauge
open STW22AntipodalTraceBoundary
open STW22AntipodalBaseCoordinateMeasures
open STW22AntipodalBaseBoundaryMeasure
open STW22AntipodalBoundaryTraceFunction
open STW22AntipodalBoundaryMeasureTrace
open STW22AntipodalBlockTraceMeasure
open STW22AntipodalBlockMeasureTrace
open STW22AntipodalBlockTraceAffineEquiv
open UniformTracialGNSTwoGauge
open PolarLiftingGeneralCStar
open CStarC0DirectSum

noncomputable section

open scoped ComplexOrder ENNReal OnePoint

/-- The coordinate-corner inclusion specialized to the concrete antipodal
block family. -/
def antipodalBaseSummandInclusion (n : Nat) :
    AntipodalCounterexampleBlock n →⋆ₙₐ[Complex]
      BaseAlgebra AntipodalCounterexampleBlock :=
  baseSummandInclusion (D := AntipodalCounterexampleBlock) n

/-- The central projection supporting one concrete antipodal block. -/
def antipodalBaseCoordinateProjection (n : Nat) :
    BaseAlgebra AntipodalCounterexampleBlock :=
  antipodalBaseSummandInclusion n 1

@[simp] theorem antipodalBaseSummandInclusion_eq (n : Nat) :
    antipodalBaseSummandInclusion n =
      baseSummandInclusion (D := AntipodalCounterexampleBlock) n := rfl

@[simp] theorem antipodalBaseCoordinateProjection_eq (n : Nat) :
    antipodalBaseCoordinateProjection n =
      baseCoordinateProjection (D := AntipodalCounterexampleBlock) n := rfl

@[simp] theorem antipodalBaseSummandInclusion_apply_self (n : Nat)
    (a : AntipodalCounterexampleBlock n) :
    ((antipodalBaseSummandInclusion n a :
        BaseAlgebra AntipodalCounterexampleBlock) :
      BoundedCStarSequence AntipodalCounterexampleBlock) n = a := by
  change (((summandInclusion AntipodalCounterexampleBlock n a :
      C0DirectSum AntipodalCounterexampleBlock) :
    BoundedCStarSequence AntipodalCounterexampleBlock) n) = a
  exact summandInclusion_apply_self AntipodalCounterexampleBlock n a

@[simp] theorem antipodalBaseSummandInclusion_apply_ne {n m : Nat}
    (h : m ≠ n) (a : AntipodalCounterexampleBlock n) :
    ((antipodalBaseSummandInclusion n a :
        BaseAlgebra AntipodalCounterexampleBlock) :
      BoundedCStarSequence AntipodalCounterexampleBlock) m = 0 := by
  change (((summandInclusion AntipodalCounterexampleBlock n a :
      C0DirectSum AntipodalCounterexampleBlock) :
    BoundedCStarSequence AntipodalCounterexampleBlock) m) = 0
  exact summandInclusion_apply_ne AntipodalCounterexampleBlock h a

@[simp] theorem antipodalBaseCoordinateProjection_mul_summand
    (n : Nat) (a : AntipodalCounterexampleBlock n) :
    antipodalBaseCoordinateProjection n * antipodalBaseSummandInclusion n a =
      antipodalBaseSummandInclusion n a := by
  change antipodalBaseSummandInclusion n 1 *
      antipodalBaseSummandInclusion n a = antipodalBaseSummandInclusion n a
  rw [← map_mul]
  simp

@[simp] theorem star_antipodalBaseCoordinateProjection (n : Nat) :
    star (antipodalBaseCoordinateProjection n) =
      antipodalBaseCoordinateProjection n := by
  change star (antipodalBaseSummandInclusion n 1) =
    antipodalBaseSummandInclusion n 1
  calc
    star (antipodalBaseSummandInclusion n 1) =
        antipodalBaseSummandInclusion n (star 1) :=
      (map_star (antipodalBaseSummandInclusion n) 1).symm
    _ = antipodalBaseSummandInclusion n 1 := by rw [star_one]

@[simp] theorem antipodalBaseCoordinateProjection_sq (n : Nat) :
    antipodalBaseCoordinateProjection n * antipodalBaseCoordinateProjection n =
      antipodalBaseCoordinateProjection n := by
  exact antipodalBaseCoordinateProjection_mul_summand n 1

private theorem tracialState_ext {A : Type*} [Ring A] [StarRing A]
    [Algebra Complex A] {tau sigma : TracialState A}
    (h : ∀ a, tau a = sigma a) : tau = sigma := by
  cases tau with
  | mk f hf1 hfp hft =>
    cases sigma with
    | mk g hg1 hgp hgt =>
      have hfg : f = g := LinearMap.ext h
      subst g
      rfl

@[simp] theorem baseScalarStarAlgHom_antipodalBaseSummandInclusion
    (n : Nat) (a : AntipodalCounterexampleBlock n) :
    baseScalarStarAlgHom AntipodalCounterexampleBlock
      (antipodalBaseSummandInclusion n a) = 0 := by
  have hincl : antipodalBaseSummandInclusion n a =
      STW22BaseAlgebraUnitization.c0ToBase AntipodalCounterexampleBlock
        (summandInclusion AntipodalCounterexampleBlock n a) := rfl
  rw [hincl, baseScalarStarAlgHom_c0ToBase]

/-- A zero coordinate weight forces the trace to vanish on the whole
coordinate corner. -/
theorem apply_baseSummandInclusion_eq_zero_of_weight_eq_zero
    (sigma : TracialState (BaseAlgebra AntipodalCounterexampleBlock))
    (n : Nat) (hweight : antipodalBaseCoordinateWeight sigma n = 0)
    (a : AntipodalCounterexampleBlock n) :
    sigma (antipodalBaseSummandInclusion n a) = 0 := by
  let p := antipodalBaseCoordinateProjection n
  let y := antipodalBaseSummandInclusion n a
  have hpTwo : tracialTwoNorm sigma p = 0 := by
    rw [tracialTwoNorm_def]
    change Real.sqrt
      ((sigma (star (antipodalBaseCoordinateProjection n) *
          antipodalBaseCoordinateProjection n)).re) = 0
    rw [star_antipodalBaseCoordinateProjection,
      antipodalBaseCoordinateProjection_sq]
    rw [antipodalBaseCoordinateProjection_eq]
    change Real.sqrt ((antipodalBaseCoordinateWeight sigma n).re) = 0
    rw [hweight]
    exact Real.sqrt_zero
  have hpy : star p * y = y := by
    change star (antipodalBaseCoordinateProjection n) *
        antipodalBaseSummandInclusion n a = antipodalBaseSummandInclusion n a
    rw [star_antipodalBaseCoordinateProjection,
      antipodalBaseCoordinateProjection_mul_summand]
  have hnorm := norm_apply_star_mul_le sigma p y
  rw [hpy, hpTwo, zero_mul] at hnorm
  exact norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _))

/-- The unnormalized coordinate RMK measure integrates normalized fibre
traces to the original (unnormalized) coordinate restriction. -/
theorem integral_baseCoordinateTraceMeasure_projectiveBlockTraceFunction
    (sigma : TracialState (BaseAlgebra AntipodalCounterexampleBlock))
    (n : Nat) (a : AntipodalCounterexampleBlock n) :
    (∫ x, projectiveBlockTraceFunction a x
      ∂(baseCoordinateTraceMeasure sigma n)) =
      sigma (antipodalBaseSummandInclusion n a) := by
  by_cases hweight : antipodalBaseCoordinateWeight sigma n = 0
  · rw [show baseCoordinateTraceMeasure sigma n = 0 by
      simp [baseCoordinateTraceMeasure, hweight]]
    rw [integral_zero_measure]
    exact (apply_baseSummandInclusion_eq_zero_of_weight_eq_zero
      sigma n hweight a).symm
  · rw [show baseCoordinateTraceMeasure sigma n =
        (baseCoordinateWeightNNReal sigma n) •
          blockTraceMeasure
            (antipodalNormalizedCoordinateTracialState sigma n hweight) by
      simp [baseCoordinateTraceMeasure, hweight]]
    rw [integral_smul_nnreal_measure]
    have hround :=
      probabilityMeasureBlockTrace_blockTraceProbabilityMeasure_apply
        (antipodalNormalizedCoordinateTracialState sigma n hweight) a
    rw [probabilityMeasureBlockTrace_apply] at hround
    change (∫ x, projectiveBlockTraceFunction a x
      ∂(blockTraceMeasure
        (antipodalNormalizedCoordinateTracialState sigma n hweight))) = _
      at hround
    rw [hround]
    rw [antipodalBaseSummandInclusion_eq]
    change (((baseCoordinateWeightNNReal sigma n : Real) : Complex) *
        ((antipodalBaseCoordinateWeight sigma n)⁻¹ *
          sigma (baseSummandInclusion
            (D := AntipodalCounterexampleBlock) n a))) = _
    rw [baseCoordinateWeightNNReal_coe]
    have him : (antipodalBaseCoordinateWeight sigma n).im = 0 :=
      (Complex.nonneg_iff.mp
        (antipodalBaseCoordinateWeight_nonneg sigma n)).2.symm
    have hreal :
        (((antipodalBaseCoordinateWeight sigma n).re : Real) : Complex) =
          antipodalBaseCoordinateWeight sigma n := by
      apply Complex.ext <;> simp [him]
    rw [hreal, ← mul_assoc, mul_inv_cancel₀ hweight, one_mul]

/-- Boundary evaluation of a coordinate-corner element vanishes off that
coordinate and is the normalized fibre trace on that coordinate. -/
theorem boundaryTraceFunction_baseSummandInclusion
    (n m : Nat) (a : AntipodalCounterexampleBlock n)
    (x : GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RP
      (antipodalBlockDimension m)) :
    boundaryTraceFunction
        (antipodalBaseSummandInclusion n a)
        (((⟨m, x⟩ : Σ k : Nat,
          GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RP
            (antipodalBlockDimension k))) : AntipodalTraceBoundary) =
      if h : m = n then projectiveBlockTraceFunction a (h ▸ x) else 0 := by
  by_cases hmn : m = n
  · subst m
    rw [dif_pos rfl, boundaryTraceFunction_coe,
      finiteBoundaryBaseTracialState_apply,
      antipodalBaseSummandInclusion_apply_self]
    change projectiveFibreTracialState (antipodalBlockDimension n)
      (antipodalBlockSize n) x a = projectiveBlockTraceFunction a x
    exact (projectiveBlockTraceFunction_eq_projectiveFibre a x).symm
  · rw [dif_neg hmn, boundaryTraceFunction_coe,
      finiteBoundaryBaseTracialState_apply,
      antipodalBaseSummandInclusion_apply_ne hmn]
    exact TracialState.map_zero _

/-- The boundary measure assembled from `sigma` integrates a coordinate
corner exactly as `sigma` does. -/
theorem integral_baseTraceBoundaryMeasure_baseSummandInclusion
    (sigma : TracialState (BaseAlgebra AntipodalCounterexampleBlock))
    (n : Nat) (a : AntipodalCounterexampleBlock n) :
    (∫ z, boundaryTraceFunction
        (antipodalBaseSummandInclusion n a) z
      ∂(baseTraceBoundaryMeasure sigma)) =
      sigma (antipodalBaseSummandInclusion n a) := by
  let f := boundaryTraceFunction
    (antipodalBaseSummandInclusion n a)
  have hf : Integrable f (baseTraceBoundaryMeasure sigma) :=
    f.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact isCompact_univ
        (Set.subset_univ _))
  have hfinite : Integrable f (finiteBoundaryTraceMeasure sigma) :=
    hf.mono_measure (Measure.le_add_right (le_refl _))
  have hinfty : Integrable f
      ((baseInfinityWeightNNReal sigma) •
        Measure.dirac (∞ : AntipodalTraceBoundary)) :=
    hf.mono_measure (Measure.le_add_left (le_refl _))
  have hfinftyValue : f (∞ : AntipodalTraceBoundary) = 0 := by
    change infinityBaseTracialState
      (antipodalBaseSummandInclusion n a) = 0
    rw [infinityBaseTracialState_apply,
      baseScalarStarAlgHom_antipodalBaseSummandInclusion]
  have hinftyZero : (∫ z, f z
      ∂((baseInfinityWeightNNReal sigma) •
        Measure.dirac (∞ : AntipodalTraceBoundary))) = 0 := by
    rw [integral_smul_nnreal_measure, integral_dirac, hfinftyValue, smul_zero]
  rw [baseTraceBoundaryMeasure, integral_add_measure hfinite hinfty,
    finiteBoundaryTraceMeasure, integral_sum_measure hfinite, hinftyZero,
    add_zero]
  ·
    have hcoord : ∀ m : Nat,
        (∫ z, f z ∂(pushedCoordinateTraceMeasure sigma m)) =
          if m = n then
            sigma (antipodalBaseSummandInclusion n a) else 0 := by
      intro m
      rw [pushedCoordinateTraceMeasure,
        integral_map_of_stronglyMeasurable
          (measurable_boundaryCoordinateEmbedding m)
          f.continuous.stronglyMeasurable]
      by_cases hmn : m = n
      · subst m
        rw [if_pos rfl]
        simpa only [f, boundaryCoordinateEmbedding,
          boundaryTraceFunction_baseSummandInclusion, dif_pos] using
          integral_baseCoordinateTraceMeasure_projectiveBlockTraceFunction
            sigma n a
      · rw [if_neg hmn]
        apply integral_eq_zero_of_ae
        filter_upwards [] with x
        simp only [f, boundaryCoordinateEmbedding,
          boundaryTraceFunction_baseSummandInclusion, dif_neg hmn]
        change (0 : Complex) = 0
        rfl
    simp_rw [hcoord]
    rw [tsum_eq_single n]
    · simp
    · intro m hmn
      rw [if_neg hmn]

/-- Evaluating a finite sum of concrete coordinate-corner inclusions picks
out exactly the matching coordinate. -/
theorem finiteSum_antipodalBaseSummandInclusion_apply
    (a : ∀ n : Nat, AntipodalCounterexampleBlock n) (N m : Nat) :
    ((((∑ n ∈ Finset.range (N + 1), antipodalBaseSummandInclusion n (a n)) :
        BaseAlgebra AntipodalCounterexampleBlock) :
      BoundedCStarSequence AntipodalCounterexampleBlock) m) =
      if m ≤ N then a m else 0 := by
  classical
  let ev : BaseAlgebra AntipodalCounterexampleBlock →+
      AntipodalCounterexampleBlock m :=
    { toFun z := z.1 m
      map_zero' := rfl
      map_add' _ _ := rfl }
  change ev (∑ n ∈ Finset.range (N + 1),
    antipodalBaseSummandInclusion n (a n)) = if m ≤ N then a m else 0
  rw [map_sum]
  by_cases hm : m ≤ N
  · rw [if_pos hm]
    have hmmem : m ∈ Finset.range (N + 1) := by
      simpa only [Finset.mem_range, Nat.lt_succ_iff] using hm
    rw [Finset.sum_eq_single m]
    · exact antipodalBaseSummandInclusion_apply_self m (a m)
    · intro n hn hnm
      exact antipodalBaseSummandInclusion_apply_ne
        (fun hmn ↦ hnm hmn.symm) (a n)
    · exact fun h ↦ (h hmmem).elim
  · rw [if_neg hm, Finset.sum_eq_zero]
    intro n hn
    exact antipodalBaseSummandInclusion_apply_ne (by
      intro hmn
      subst n
      exact hm (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))) (a n)

/-- A canonical scalar-tail truncation is the scalar unit plus the finite
sum of its deviations from that scalar. -/
theorem canonicalBaseTruncation_eq_scalar_add_sum
    (x : BaseAlgebra AntipodalCounterexampleBlock) (N : Nat) :
    canonicalBaseTruncation AntipodalCounterexampleBlock x N =
      (baseScalarStarAlgHom AntipodalCounterexampleBlock x) • 1 +
        ∑ n ∈ Finset.range (N + 1),
          antipodalBaseSummandInclusion n
            (x.1 n - algebraMap Complex
              (AntipodalCounterexampleBlock n)
              (baseScalarStarAlgHom AntipodalCounterexampleBlock x)) := by
  classical
  apply Subtype.ext
  apply lp.ext
  funext m
  rw [canonicalBaseTruncation_apply]
  change (if m ≤ N then x.1 m else algebraMap Complex
      (AntipodalCounterexampleBlock m)
      (baseScalarStarAlgHom AntipodalCounterexampleBlock x)) =
    (((baseScalarStarAlgHom AntipodalCounterexampleBlock x) • 1 +
        ∑ n ∈ Finset.range (N + 1),
          antipodalBaseSummandInclusion n
            (x.1 n - algebraMap Complex (AntipodalCounterexampleBlock n)
              (baseScalarStarAlgHom AntipodalCounterexampleBlock x)) :
          BaseAlgebra AntipodalCounterexampleBlock) :
        BoundedCStarSequence AntipodalCounterexampleBlock) m
  change (if m ≤ N then x.1 m else algebraMap Complex
      (AntipodalCounterexampleBlock m)
      (baseScalarStarAlgHom AntipodalCounterexampleBlock x)) =
    ((((baseScalarStarAlgHom AntipodalCounterexampleBlock x) •
          (1 : BaseAlgebra AntipodalCounterexampleBlock) :
        BaseAlgebra AntipodalCounterexampleBlock) :
      BoundedCStarSequence AntipodalCounterexampleBlock) m) +
    ((((∑ n ∈ Finset.range (N + 1),
          antipodalBaseSummandInclusion n
            (x.1 n - algebraMap Complex (AntipodalCounterexampleBlock n)
              (baseScalarStarAlgHom AntipodalCounterexampleBlock x))) :
        BaseAlgebra AntipodalCounterexampleBlock) :
      BoundedCStarSequence AntipodalCounterexampleBlock) m)
  rw [show ((((baseScalarStarAlgHom AntipodalCounterexampleBlock x) •
      (1 : BaseAlgebra AntipodalCounterexampleBlock) :
        BaseAlgebra AntipodalCounterexampleBlock) :
      BoundedCStarSequence AntipodalCounterexampleBlock) m) =
      (baseScalarStarAlgHom AntipodalCounterexampleBlock x) •
        (1 : AntipodalCounterexampleBlock m) by rfl]
  rw [finiteSum_antipodalBaseSummandInclusion_apply]
  by_cases hm : m ≤ N
  · rw [if_pos hm, if_pos hm, ← Algebra.algebraMap_eq_smul_one]
    abel
  · rw [if_neg hm, if_neg hm, add_zero,
      ← Algebra.algebraMap_eq_smul_one]

/-- Integrating the boundary measure canonically assembled from a base trace
recovers that trace on every base element. -/
theorem boundaryProbabilityMeasureTracialState_baseTraceBoundaryProbabilityMeasure
    (sigma : TracialState (BaseAlgebra AntipodalCounterexampleBlock)) :
    boundaryProbabilityMeasureTracialState
        (baseTraceBoundaryProbabilityMeasure sigma) = sigma := by
  let rho := boundaryProbabilityMeasureTracialState
    (baseTraceBoundaryProbabilityMeasure sigma)
  have hsummand : ∀ (n : Nat) (a : AntipodalCounterexampleBlock n),
      rho (antipodalBaseSummandInclusion n a) =
        sigma (antipodalBaseSummandInclusion n a) := by
    intro n a
    change (∫ z, boundaryTraceFunction
        (antipodalBaseSummandInclusion n a) z
      ∂(baseTraceBoundaryMeasure sigma)) = _
    exact integral_baseTraceBoundaryMeasure_baseSummandInclusion sigma n a
  have htrunc : ∀ (x : BaseAlgebra AntipodalCounterexampleBlock) (N : Nat),
      rho (canonicalBaseTruncation AntipodalCounterexampleBlock x N) =
        sigma (canonicalBaseTruncation AntipodalCounterexampleBlock x N) := by
    intro x N
    rw [canonicalBaseTruncation_eq_scalar_add_sum,
      rho.map_add, sigma.map_add, rho.map_smul, sigma.map_smul,
      rho.apply_one, sigma.apply_one]
    congr 1
    rw [map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro n hn
    exact hsummand n _
  have hpoint : ∀ x : BaseAlgebra AntipodalCounterexampleBlock, rho x = sigma x := by
    intro x
    have ht := tendsto_canonicalBaseTruncation
      AntipodalCounterexampleBlock x
    have hrho : Tendsto
        (fun N ↦ rho (canonicalBaseTruncation
          AntipodalCounterexampleBlock x N)) atTop (nhds (rho x)) :=
      ((HNNTrace.tracialStateCLM rho).continuous.tendsto x).comp ht
    have hsigma : Tendsto
        (fun N ↦ sigma (canonicalBaseTruncation
          AntipodalCounterexampleBlock x N)) atTop (nhds (sigma x)) :=
      ((HNNTrace.tracialStateCLM sigma).continuous.tendsto x).comp ht
    exact tendsto_nhds_unique
      (hrho.congr' (Eventually.of_forall fun N ↦ htrunc x N)) hsigma
  exact tracialState_ext hpoint

end

end STW22AntipodalTraceMeasureInverse
end GroupApproximation
