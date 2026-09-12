import GroupApproximation.Analysis.STW22ActualTraceSpaces
import GroupApproximation.Analysis.CoronaCoordinateStateCompactness
import GroupApproximation.Analysis.CStarC0DirectSum
import GroupApproximation.Analysis.CuntzPedersenJordanTracial
import GroupApproximation.Analysis.UniformTracialGNSTwoGauge

/-!
# The genuine trace gauge on the STW base algebra

This file compares the supremum over the actual bundled tracial states of the
unitized `c₀` base algebra with the coordinate gauge used in the sequence
model.  The coordinate-to-global inequality is completely formal: every trace
on a block pulls back along coordinate evaluation to a trace on the base
algebra.  In particular the sequence-model gauge is not merely an externally
chosen seminorm; it is bounded above by the literal uniform tracial two-size
of the base algebra.
-/

namespace GroupApproximation
namespace STW22BaseUniformTracialGauge

open Filter PolarLiftingGeneralCStar
open UniformTracialSequenceCompletion UniformTracialTwoNullIdeal
open UniformTracialGNSTwoGauge STW22Assembly
open STW22ActualTraceSpaces CoronaCoordinateStateCompactness
open CStarC0DirectSum

noncomputable section

set_option linter.unusedSectionVars false

open scoped ComplexOrder

universe u

variable {D : ℕ → Type u} [∀ n, CStarAlgebra (D n)]
  [∀ n, Nontrivial (D n)] [∀ n, Nonempty (TracialState (D n))]

/-- Evaluation of the concrete unitized `c₀` base algebra at one block. -/
def baseCoordinateStarAlgHom (n : ℕ) :
    BaseAlgebra D →⋆ₐ[ℂ] D n :=
  (coordinateStarAlgHom (D := D) n).comp (BaseAlgebra D).subtype

@[simp] theorem baseCoordinateStarAlgHom_apply (n : ℕ)
    (x : BaseAlgebra D) :
    baseCoordinateStarAlgHom (D := D) n x = x.1 n := rfl

/-- A coordinate tracial state, regarded as an actual tracial state of the
unitized `c₀` base algebra. -/
def baseCoordinateTracialState (n : ℕ) (τ : TracialState (D n)) :
    TracialState (BaseAlgebra D) :=
  τ.compStarAlgHom (baseCoordinateStarAlgHom (D := D) n)

@[simp] theorem baseCoordinateTracialState_apply (n : ℕ)
    (τ : TracialState (D n)) (x : BaseAlgebra D) :
    baseCoordinateTracialState (D := D) n τ x = τ (x.1 n) := rfl

/-- The base algebra has a tracial state, obtained from any coordinate. -/
instance nonemptyTracialState_baseAlgebra :
    Nonempty (TracialState (BaseAlgebra D)) :=
  ⟨baseCoordinateTracialState (D := D) 0 (Classical.choice inferInstance)⟩

/-- The literal uniform tracial two-size on the actual base algebra. -/
def baseTracialTwoSize (x : BaseAlgebra D) : ℝ :=
  sSup (Set.range fun τ : TracialState (BaseAlgebra D) ↦ tracialTwoNorm τ x)

theorem bddAbove_range_baseTracialTwoNorm (x : BaseAlgebra D) :
    BddAbove (Set.range fun τ : TracialState (BaseAlgebra D) ↦
      tracialTwoNorm τ x) :=
  bddAbove_range_tracialTwoNorm x

/-- Every actual base trace two-norm is below the literal supremum. -/
theorem tracialTwoNorm_le_baseTracialTwoSize
    (τ : TracialState (BaseAlgebra D)) (x : BaseAlgebra D) :
    tracialTwoNorm τ x ≤ baseTracialTwoSize x := by
  exact le_csSup (bddAbove_range_baseTracialTwoNorm x) (Set.mem_range_self τ)

/-- Pulling a coordinate trace back to the base algebra preserves its
two-norm exactly. -/
theorem tracialTwoNorm_baseCoordinateTracialState
    (n : ℕ) (τ : TracialState (D n)) (x : BaseAlgebra D) :
    tracialTwoNorm (baseCoordinateTracialState (D := D) n τ) x =
      tracialTwoNorm τ (x.1 n) := by
  rw [tracialTwoNorm_def, tracialTwoNorm_def]
  change Real.sqrt ((τ (star (x.1 n) * x.1 n)).re) =
    Real.sqrt ((τ (star (x.1 n) * x.1 n)).re)
  rfl

/-- The all-block-traces gauge at one coordinate is bounded by the genuine
uniform tracial two-size on the actual base algebra. -/
theorem tracialTwoSize_coordinate_le_baseTracialTwoSize
    (n : ℕ) (x : BaseAlgebra D) :
    tracialTwoSize n (x.1 n) ≤ baseTracialTwoSize x := by
  rw [tracialTwoSize_eq_sSup]
  refine csSup_le (Set.range_nonempty _) ?_
  rintro _ ⟨τ, rfl⟩
  calc
    tracialTwoNorm τ (x.1 n) =
        tracialTwoNorm (baseCoordinateTracialState (D := D) n τ) x :=
      (tracialTwoNorm_baseCoordinateTracialState n τ x).symm
    _ ≤ baseTracialTwoSize x := tracialTwoNorm_le_baseTracialTwoSize _ _

/-- The sequence-model uniform gauge is bounded by the literal supremum over
all tracial states of the actual base algebra. -/
theorem uniformTwoNorm_allTraces_le_baseTracialTwoSize
    (x : BaseAlgebra D) :
    uniformTwoNorm (allTracesTracialTwoGauge D) x.1 ≤
      baseTracialTwoSize x := by
  apply uniformTwoNorm_le
  intro n
  rw [allTracesTracialTwoGauge_q]
  exact tracialTwoSize_coordinate_le_baseTracialTwoSize n x

/-! ## Restricting an arbitrary base trace to a coordinate corner -/

/-- The nonunital inclusion of a block as the corresponding coordinate corner
of the concrete base algebra. -/
def c0ToBase : C0DirectSum D →⋆ₙₐ[ℂ] BaseAlgebra D where
  toFun b := ⟨b.1, (mem_baseAlgebra_iff b.1).2 ⟨0, by
    have hb := b.2
    change IsNullCStarSequence D atTop b.1 at hb
    rw [IsNullCStarSequence] at hb
    simpa only [map_zero, sub_zero] using hb⟩⟩
  map_zero' := by apply Subtype.ext; rfl
  map_add' _ _ := by apply Subtype.ext; rfl
  map_mul' _ _ := by apply Subtype.ext; rfl
  map_smul' _ _ := by apply Subtype.ext; rfl
  map_star' _ := by apply Subtype.ext; rfl

def baseSummandInclusion (n : ℕ) : D n →⋆ₙₐ[ℂ] BaseAlgebra D :=
  (c0ToBase (D := D)).comp (summandInclusion D n)

/-- The linear map underlying a coordinate-corner inclusion. -/
def baseSummandLinearMap (n : ℕ) : D n →ₗ[ℂ] BaseAlgebra D where
  toFun := baseSummandInclusion (D := D) n
  map_add' := map_add _
  map_smul' := map_smul _

@[simp] theorem baseSummandInclusion_apply_self (n : ℕ) (a : D n) :
    ((baseSummandInclusion (D := D) n a : BaseAlgebra D) :
      BoundedCStarSequence D) n = a := by
  exact summandInclusion_apply_self D n a

@[simp] theorem baseSummandInclusion_apply_ne {n m : ℕ} (h : m ≠ n)
    (a : D n) :
    ((baseSummandInclusion (D := D) n a : BaseAlgebra D) :
      BoundedCStarSequence D) m = 0 := by
  exact summandInclusion_apply_ne D h a

/-- The central support projection of the `n`-th coordinate corner. -/
def baseCoordinateProjection (n : ℕ) : BaseAlgebra D :=
  baseSummandInclusion (D := D) n 1

@[simp] theorem baseCoordinateProjection_mul_summand (n : ℕ) (a : D n) :
    baseCoordinateProjection (D := D) n * baseSummandInclusion n a =
      baseSummandInclusion n a := by
  apply Subtype.ext
  apply lp.ext
  funext m
  by_cases hmn : m = n
  · subst m
    simp [baseCoordinateProjection]
  · simp [baseCoordinateProjection, baseSummandInclusion_apply_ne, hmn]

@[simp] theorem star_baseCoordinateProjection (n : ℕ) :
    star (baseCoordinateProjection (D := D) n) = baseCoordinateProjection n := by
  simpa [baseCoordinateProjection] using
    (map_star (baseSummandInclusion (D := D) n) (1 : D n)).symm

@[simp] theorem baseCoordinateProjection_sq (n : ℕ) :
    baseCoordinateProjection (D := D) n * baseCoordinateProjection n =
      baseCoordinateProjection n := by
  exact baseCoordinateProjection_mul_summand n 1

/-- The (complex) weight assigned by a base trace to one coordinate corner. -/
def baseCoordinateWeight (σ : TracialState (BaseAlgebra D)) (n : ℕ) : ℂ :=
  σ (baseCoordinateProjection (D := D) n)

theorem baseCoordinateWeight_nonneg
    (σ : TracialState (BaseAlgebra D)) (n : ℕ) :
    0 ≤ baseCoordinateWeight σ n := by
  simpa [baseCoordinateWeight] using
    σ.map_star_mul_self_nonneg (baseCoordinateProjection (D := D) n)

/-- If a base trace gives positive weight to a coordinate corner, normalize
its restriction to obtain a genuine tracial state of that block. -/
def normalizedCoordinateTracialState
    (σ : TracialState (BaseAlgebra D)) (n : ℕ)
    (hweight : baseCoordinateWeight σ n ≠ 0) : TracialState (D n) where
  toLinearMap := (baseCoordinateWeight σ n)⁻¹ •
    σ.toLinearMap.comp (baseSummandLinearMap (D := D) n)
  map_one := by
    change (baseCoordinateWeight σ n)⁻¹ * baseCoordinateWeight σ n = 1
    exact inv_mul_cancel₀ hweight
  map_star_mul_self_nonneg a := by
    change 0 ≤ (baseCoordinateWeight σ n)⁻¹ *
      σ (baseSummandInclusion (D := D) n (star a * a))
    exact CuntzPedersenJordanTracial.mul_nonneg_complex
      (CuntzPedersenJordanTracial.inv_nonneg_complex
        (baseCoordinateWeight_nonneg σ n))
      (by
        rw [map_mul, map_star]
        exact σ.map_star_mul_self_nonneg (baseSummandInclusion n a))
  map_mul_comm a b := by
    change (baseCoordinateWeight σ n)⁻¹ *
        σ (baseSummandInclusion (D := D) n (a * b)) =
      (baseCoordinateWeight σ n)⁻¹ *
        σ (baseSummandInclusion (D := D) n (b * a))
    rw [map_mul (baseSummandInclusion (D := D) n) a b,
      map_mul (baseSummandInclusion (D := D) n) b a,
      σ.map_mul_comm]

@[simp] theorem normalizedCoordinateTracialState_apply
    (σ : TracialState (BaseAlgebra D)) (n : ℕ)
    (hweight : baseCoordinateWeight σ n ≠ 0) (a : D n) :
    normalizedCoordinateTracialState σ n hweight a =
      (baseCoordinateWeight σ n)⁻¹ *
        σ (baseSummandInclusion (D := D) n a) := by
  rfl

/-- An arbitrary base trace, restricted to one corner, is bounded by its
corner weight times the square of the all-traces coordinate gauge.  This is
the key finite-coordinate estimate in the reverse global-gauge inequality. -/
theorem re_apply_summand_star_mul_self_le
    (σ : TracialState (BaseAlgebra D)) (n : ℕ) (a : D n) :
    (σ (baseSummandInclusion (D := D) n (star a * a))).re ≤
      (baseCoordinateWeight σ n).re * (tracialTwoSize n a) ^ 2 := by
  by_cases hw : baseCoordinateWeight σ n = 0
  · have heTwo : tracialTwoNorm σ (baseCoordinateProjection (D := D) n) = 0 := by
      rw [tracialTwoNorm_def, star_baseCoordinateProjection,
        baseCoordinateProjection_sq]
      change Real.sqrt ((baseCoordinateWeight σ n).re) = 0
      rw [hw,
        Complex.zero_re, Real.sqrt_zero]
    have hzero : σ (baseSummandInclusion (D := D) n (star a * a)) = 0 := by
      let y := baseSummandInclusion (D := D) n (star a * a)
      have hcs := norm_apply_star_mul_le σ
        (baseCoordinateProjection (D := D) n) y
      rw [star_baseCoordinateProjection,
        baseCoordinateProjection_mul_summand, heTwo, zero_mul] at hcs
      exact norm_eq_zero.mp (le_antisymm hcs (norm_nonneg _))
    rw [hzero, hw]
    simp
  · let τ := normalizedCoordinateTracialState σ n hw
    have hq : tracialTwoNorm τ a ≤ tracialTwoSize n a :=
      tracialTwoNorm_le_tracialTwoSize n τ a
    have hsq : (τ (star a * a)).re ≤ (tracialTwoSize n a) ^ 2 := by
      have := pow_le_pow_left₀ (tracialTwoNorm_nonneg τ a) hq 2
      rw [tracialTwoNorm_def,
        Real.sq_sqrt (re_apply_star_mul_self_nonneg τ a)] at this
      exact this
    have hrecover :
        σ (baseSummandInclusion (D := D) n (star a * a)) =
          baseCoordinateWeight σ n * τ (star a * a) := by
      rw [show τ (star a * a) =
          (baseCoordinateWeight σ n)⁻¹ *
            σ (baseSummandInclusion (D := D) n (star a * a)) from rfl]
      rw [← mul_assoc, mul_inv_cancel₀ hw, one_mul]
    rw [hrecover, Complex.mul_re]
    have hwIm : (baseCoordinateWeight σ n).im = 0 :=
      (Complex.nonneg_iff.mp (baseCoordinateWeight_nonneg σ n)).2.symm
    have hτIm : (τ (star a * a)).im = 0 :=
      (Complex.nonneg_iff.mp (τ.map_star_mul_self_nonneg a)).2.symm
    rw [hwIm, hτIm, mul_zero, sub_zero]
    exact mul_le_mul_of_nonneg_left hsq
      ((Complex.nonneg_iff.mp (baseCoordinateWeight_nonneg σ n)).1)

/-! ## Finite scalar truncations -/

/-- Scalar truncation, now bundled as an element of the actual base algebra. -/
def baseScalarTruncation (x : BaseAlgebra D) (c : ℂ) (N : ℕ) :
    BaseAlgebra D :=
  ⟨scalarTruncation x.1 c N,
    (mem_baseAlgebra_iff _).2 (scalarTruncation_mem_unitizedC0Sum x.1 c N)⟩

@[simp] theorem baseScalarTruncation_apply (x : BaseAlgebra D) (c : ℂ)
    (N n : ℕ) :
    (baseScalarTruncation x c N).1 n =
      if n ≤ N then x.1 n else algebraMap ℂ (D n) c :=
  scalarTruncation_apply x.1 c N n

private theorem base_sum_mem_apply {I : Type*}
    (S : Finset I) (f : I → BaseAlgebra D) (m : ℕ) :
    ((∑ i ∈ S, f i : BaseAlgebra D) : BoundedCStarSequence D) m =
      ∑ i ∈ S, ((f i : BaseAlgebra D) : BoundedCStarSequence D) m := by
  let ev : BaseAlgebra D →+ D m :=
    { toFun := fun z ↦ z.1 m
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  exact map_sum ev f S

/-- The square of a scalar truncation splits into its scalar tail and finitely
many coordinate-corner corrections.  This identity makes all cross terms
disappear before any trace is applied. -/
theorem star_mul_baseScalarTruncation_eq
    (x : BaseAlgebra D) (c : ℂ) (N : ℕ) :
    star (baseScalarTruncation x c N) * baseScalarTruncation x c N =
      algebraMap ℂ (BaseAlgebra D) (star c * c) +
        ∑ n ∈ Finset.range (N + 1),
          baseSummandInclusion (D := D) n
            (star (x.1 n) * x.1 n - algebraMap ℂ (D n) (star c * c)) := by
  classical
  apply Subtype.ext
  apply lp.ext
  funext m
  change star ((baseScalarTruncation x c N).1 m) *
      (baseScalarTruncation x c N).1 m =
    algebraMap ℂ (D m) (star c * c) +
      ((∑ n ∈ Finset.range (N + 1),
          baseSummandInclusion (D := D) n
            (star (x.1 n) * x.1 n -
              algebraMap ℂ (D n) (star c * c)) : BaseAlgebra D) :
        BoundedCStarSequence D) m
  by_cases hm : m ≤ N
  · have hmmem : m ∈ Finset.range (N + 1) := by simpa using hm
    rw [base_sum_mem_apply]
    simp only [baseScalarTruncation_apply, if_pos hm]
    rw [Finset.sum_eq_single m]
    · simp
    · intro n hn hnm
      exact baseSummandInclusion_apply_ne (D := D) (Ne.symm hnm) _
    · intro hnot
      exact (hnot hmmem).elim
  · have hm' : m ∉ Finset.range (N + 1) := by simpa using hm
    rw [base_sum_mem_apply]
    simp only [baseScalarTruncation_apply, if_neg hm]
    rw [Finset.sum_eq_zero]
    · simp only [Algebra.algebraMap_eq_smul_one, star_smul, star_one,
        add_zero]
      rw [smul_mul_smul_comm, one_mul]
    · intro n hn
      have hmn : m ≠ n := by
        intro h
        subst n
        exact hm' hn
      exact baseSummandInclusion_apply_ne (D := D) hmn _

/-- The sum of the first `N+1` coordinate support projections. -/
def baseFiniteCoordinateProjection (N : ℕ) : BaseAlgebra D :=
  ∑ n ∈ Finset.range (N + 1), baseCoordinateProjection (D := D) n

@[simp] theorem baseFiniteCoordinateProjection_apply
    (N m : ℕ) :
    (baseFiniteCoordinateProjection (D := D) N).1 m =
      if m ≤ N then 1 else 0 := by
  classical
  rw [baseFiniteCoordinateProjection, base_sum_mem_apply]
  by_cases hm : m ≤ N
  · rw [if_pos hm]
    have hmmem : m ∈ Finset.range (N + 1) := by simpa using hm
    rw [Finset.sum_eq_single m]
    · simp [baseCoordinateProjection]
    · intro n hn hnm
      exact baseSummandInclusion_apply_ne (D := D) (Ne.symm hnm) _
    · intro hnot
      exact (hnot hmmem).elim
  · rw [if_neg hm, Finset.sum_eq_zero]
    intro n hn
    have hmn : m ≠ n := by
      intro h
      subst n
      exact hm (by simpa using hn)
    exact baseSummandInclusion_apply_ne (D := D) hmn _

@[simp] theorem star_baseFiniteCoordinateProjection (N : ℕ) :
    star (baseFiniteCoordinateProjection (D := D) N) =
      baseFiniteCoordinateProjection N := by
  apply Subtype.ext
  apply lp.ext
  funext m
  change star ((baseFiniteCoordinateProjection (D := D) N).1 m) =
    (baseFiniteCoordinateProjection (D := D) N).1 m
  rw [baseFiniteCoordinateProjection_apply]
  by_cases hm : m ≤ N <;> simp [hm]

@[simp] theorem baseFiniteCoordinateProjection_sq (N : ℕ) :
    baseFiniteCoordinateProjection (D := D) N *
        baseFiniteCoordinateProjection N =
      baseFiniteCoordinateProjection N := by
  apply Subtype.ext
  apply lp.ext
  funext m
  change (baseFiniteCoordinateProjection (D := D) N).1 m *
      (baseFiniteCoordinateProjection (D := D) N).1 m =
    (baseFiniteCoordinateProjection (D := D) N).1 m
  rw [baseFiniteCoordinateProjection_apply]
  by_cases hm : m ≤ N <;> simp [hm]

/-- Coordinate weights of any tracial state are subprobability weights on
every finite initial segment. -/
theorem sum_baseCoordinateWeight_re_le_one
    (σ : TracialState (BaseAlgebra D)) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), (baseCoordinateWeight σ n).re ≤ 1 := by
  let p := baseFiniteCoordinateProjection (D := D) N
  have hpos : 0 ≤ σ (star (1 - p) * (1 - p)) :=
    σ.map_star_mul_self_nonneg (1 - p)
  have hproj : star (1 - p) * (1 - p) = 1 - p := by
    apply Subtype.ext
    apply lp.ext
    funext m
    change star (1 - (baseFiniteCoordinateProjection (D := D) N).1 m) *
        (1 - (baseFiniteCoordinateProjection (D := D) N).1 m) =
      1 - (baseFiniteCoordinateProjection (D := D) N).1 m
    rw [baseFiniteCoordinateProjection_apply]
    by_cases hm : m ≤ N <;> simp [hm]
  rw [hproj, TracialState.map_sub, TracialState.apply_one] at hpos
  have hre := (Complex.nonneg_iff.mp hpos).1
  simp only [Complex.sub_re, Complex.one_re] at hre
  have hsum :
      (σ (baseFiniteCoordinateProjection (D := D) N)).re =
        ∑ n ∈ Finset.range (N + 1), (baseCoordinateWeight σ n).re := by
    simp [baseFiniteCoordinateProjection, baseCoordinateWeight]
  rwa [hsum, sub_nonneg] at hre

@[simp] theorem tracialState_algebraMap
    (σ : TracialState (BaseAlgebra D)) (z : ℂ) :
    σ (algebraMap ℂ (BaseAlgebra D) z) = z := by
  rw [Algebra.algebraMap_eq_smul_one, TracialState.map_smul,
    TracialState.apply_one, smul_eq_mul, mul_one]

@[simp] theorem tracialState_baseSummand_algebraMap
    (σ : TracialState (BaseAlgebra D)) (n : ℕ) (z : ℂ) :
    σ (baseSummandInclusion (D := D) n (algebraMap ℂ (D n) z)) =
      z * baseCoordinateWeight σ n := by
  rw [Algebra.algebraMap_eq_smul_one,
    map_smul (baseSummandInclusion (D := D) n), TracialState.map_smul]
  rfl

/-- Trace evaluation of the finite square decomposition, in real form. -/
theorem re_apply_star_mul_baseScalarTruncation_eq
    (σ : TracialState (BaseAlgebra D)) (x : BaseAlgebra D)
    (c : ℂ) (N : ℕ) :
    (σ (star (baseScalarTruncation x c N) *
        baseScalarTruncation x c N)).re =
      ‖c‖ ^ 2 *
          (1 - ∑ n ∈ Finset.range (N + 1),
            (baseCoordinateWeight σ n).re) +
        ∑ n ∈ Finset.range (N + 1),
          (σ (baseSummandInclusion (D := D) n
            (star (x.1 n) * x.1 n))).re := by
  rw [star_mul_baseScalarTruncation_eq]
  simp only [TracialState.map_add, tracialState_algebraMap, map_sum,
    Complex.add_re]
  simp_rw [map_sub]
  simp_rw [tracialState_baseSummand_algebraMap]
  have hnorm : (star c * c).re = ‖c‖ ^ 2 := by
    change ((starRingEnd ℂ c) * c).re = ‖c‖ ^ 2
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    rfl
  have hscalar : star c * c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    calc
      star c * c = ((((star c * c).re : ℝ) : ℂ)) :=
        CuntzPedersenJordanTracial.eq_ofReal_re_of_nonneg
          (star_mul_self_nonneg c)
      _ = ((‖c‖ ^ 2 : ℝ) : ℂ) := by rw [hnorm]
  rw [hscalar]
  have hterm : ∀ n,
      ( σ (baseSummandInclusion (D := D) n
          (star (x.1 n) * x.1 n)) -
        ((‖c‖ ^ 2 : ℝ) : ℂ) * baseCoordinateWeight σ n).re =
      (σ (baseSummandInclusion (D := D) n
          (star (x.1 n) * x.1 n))).re -
        ‖c‖ ^ 2 * (baseCoordinateWeight σ n).re := by
    intro n
    rw [Complex.sub_re, Complex.mul_re]
    change (σ (baseSummandInclusion (D := D) n
          (star (x.1 n) * x.1 n))).re -
        (‖c‖ ^ 2 * (baseCoordinateWeight σ n).re -
          0 * (baseCoordinateWeight σ n).im) =
      (σ (baseSummandInclusion (D := D) n
          (star (x.1 n) * x.1 n))).re -
        ‖c‖ ^ 2 * (baseCoordinateWeight σ n).re
    ring
  have hsum :
      (∑ n ∈ Finset.range (N + 1),
          (σ (baseSummandInclusion (D := D) n
              (star (x.1 n) * x.1 n)) -
            ((‖c‖ ^ 2 : ℝ) : ℂ) * baseCoordinateWeight σ n)).re =
        ∑ n ∈ Finset.range (N + 1),
          ((σ (baseSummandInclusion (D := D) n
              (star (x.1 n) * x.1 n))).re -
            ‖c‖ ^ 2 * (baseCoordinateWeight σ n).re) := by
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl fun n _ ↦ hterm n
  calc
    (((‖c‖ ^ 2 : ℝ) : ℂ)).re +
          (∑ n ∈ Finset.range (N + 1),
            (σ (baseSummandInclusion (D := D) n
                (star (x.1 n) * x.1 n)) -
              ((‖c‖ ^ 2 : ℝ) : ℂ) * baseCoordinateWeight σ n)).re =
        ‖c‖ ^ 2 +
          ∑ n ∈ Finset.range (N + 1),
            ((σ (baseSummandInclusion (D := D) n
                (star (x.1 n) * x.1 n))).re -
              ‖c‖ ^ 2 * (baseCoordinateWeight σ n).re) := by
      have h := congrArg (fun t : ℝ ↦ ‖c‖ ^ 2 + t) hsum
      simpa only [Complex.ofReal_re] using h
    _ = ‖c‖ ^ 2 *
          (1 - ∑ n ∈ Finset.range (N + 1),
            (baseCoordinateWeight σ n).re) +
        ∑ n ∈ Finset.range (N + 1),
          (σ (baseSummandInclusion (D := D) n
            (star (x.1 n) * x.1 n))).re := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      ring

/-- Every actual base trace is controlled by the coordinate uniform gauge on
a finite scalar truncation. -/
theorem tracialTwoNorm_baseScalarTruncation_le_uniformTwoNorm
    (σ : TracialState (BaseAlgebra D)) (x : BaseAlgebra D)
    (c : ℂ) (N : ℕ) :
    tracialTwoNorm σ (baseScalarTruncation x c N) ≤
      uniformTwoNorm (allTracesTracialTwoGauge D)
        (baseScalarTruncation x c N).1 := by
  let y := baseScalarTruncation x c N
  let R := uniformTwoNorm (allTracesTracialTwoGauge D) y.1
  let W := ∑ n ∈ Finset.range (N + 1),
    (baseCoordinateWeight σ n).re
  have hR : 0 ≤ R := uniformTwoNorm_nonneg _ _
  have hW0 : 0 ≤ W := by
    dsimp only [W]
    exact Finset.sum_nonneg fun n _ ↦
      (Complex.nonneg_iff.mp (baseCoordinateWeight_nonneg σ n)).1
  have hW1 : W ≤ 1 := sum_baseCoordinateWeight_re_le_one σ N
  have hc : ‖c‖ ≤ R := by
    have hcoord := q_le_uniformTwoNorm (allTracesTracialTwoGauge D) y.1 (N + 1)
    have hnot : ¬N + 1 ≤ N := by omega
    simpa only [R, y, baseScalarTruncation_apply, if_neg hnot,
      (allTracesTracialTwoGauge D).q_algebraMap] using hcoord
  have hfinite :
      ∑ n ∈ Finset.range (N + 1),
          (σ (baseSummandInclusion (D := D) n
            (star (x.1 n) * x.1 n))).re ≤ W * R ^ 2 := by
    calc
      ∑ n ∈ Finset.range (N + 1),
          (σ (baseSummandInclusion (D := D) n
            (star (x.1 n) * x.1 n))).re
          ≤ ∑ n ∈ Finset.range (N + 1),
              (baseCoordinateWeight σ n).re *
                (tracialTwoSize n (x.1 n)) ^ 2 := by
            gcongr with n hn
            exact re_apply_summand_star_mul_self_le σ n (x.1 n)
      _ ≤ ∑ n ∈ Finset.range (N + 1),
              (baseCoordinateWeight σ n).re * R ^ 2 := by
            apply Finset.sum_le_sum
            intro n hn
            have hnN : n ≤ N := by simpa using hn
            have hq := q_le_uniformTwoNorm
              (allTracesTracialTwoGauge D) y.1 n
            have hq' : tracialTwoSize n (x.1 n) ≤ R := by
              simpa [R, y, allTracesTracialTwoGauge_q,
                baseScalarTruncation_apply, hnN] using hq
            exact mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (tracialTwoSize_nonneg n _) hq' 2)
              ((Complex.nonneg_iff.mp (baseCoordinateWeight_nonneg σ n)).1)
      _ = W * R ^ 2 := by
            simp [W, Finset.sum_mul]
  have hsquare :
      (σ (star y * y)).re ≤ R ^ 2 := by
    rw [show (σ (star y * y)).re = ‖c‖ ^ 2 * (1 - W) +
        ∑ n ∈ Finset.range (N + 1),
          (σ (baseSummandInclusion (D := D) n
            (star (x.1 n) * x.1 n))).re by
      simpa [y, W] using
        re_apply_star_mul_baseScalarTruncation_eq σ x c N]
    calc
      ‖c‖ ^ 2 * (1 - W) +
          ∑ n ∈ Finset.range (N + 1),
            (σ (baseSummandInclusion (D := D) n
              (star (x.1 n) * x.1 n))).re
          ≤ R ^ 2 * (1 - W) + W * R ^ 2 := by
            exact add_le_add
              (mul_le_mul_of_nonneg_right
                (pow_le_pow_left₀ (norm_nonneg c) hc 2)
                (sub_nonneg.mpr hW1)) hfinite
      _ = R ^ 2 := by ring
  rw [tracialTwoNorm_def]
  exact (Real.sqrt_le_iff).2 ⟨hR, by
    simpa [Real.sq_sqrt (re_apply_star_mul_self_nonneg σ y)] using hsquare⟩

/-- Scalar truncations converge in operator norm to a base element whenever
`c` is its scalar tail. -/
theorem tendsto_baseScalarTruncation
    (x : BaseAlgebra D) (c : ℂ)
    (hc : Tendsto (fun n ↦ ‖x.1 n - algebraMap ℂ (D n) c‖)
      Filter.atTop (nhds 0)) :
    Tendsto (fun N ↦ baseScalarTruncation x c N)
      Filter.atTop (nhds x) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  rw [Metric.tendsto_atTop] at hc
  obtain ⟨N₀, hN₀⟩ := hc (ε / 2) hhalf
  refine ⟨N₀, fun N hNN₀ ↦ ?_⟩
  rw [dist_eq_norm]
  change ‖(scalarTruncation x.1 c N - x.1 : BoundedCStarSequence D)‖ < ε
  rw [lp.norm_eq_ciSup]
  apply lt_of_le_of_lt (ciSup_le fun n ↦ ?_) (half_lt_self hε)
  by_cases hn : n ≤ N
  · rw [show (scalarTruncation x.1 c N - x.1) n = 0 by
      simp [scalarTruncation_apply, hn]]
    simpa using hhalf.le
  · have hNn : N ≤ n := Nat.le_of_lt (Nat.lt_of_not_ge hn)
    have hN₀n : N₀ ≤ n := hNN₀.trans hNn
    have htail := hN₀ n hN₀n
    rw [Real.dist_eq, sub_zero, abs_norm] at htail
    rw [show (scalarTruncation x.1 c N - x.1) n =
        -(x.1 n - algebraMap ℂ (D n) c) by
      simp [scalarTruncation_apply, hn]]
    rw [norm_neg]
    exact htail.le

/-- Subadditivity of the coordinate supremum. -/
theorem uniformTwoNorm_add_le
    (u v : BoundedCStarSequence D) :
    uniformTwoNorm (allTracesTracialTwoGauge D) (u + v) ≤
      uniformTwoNorm (allTracesTracialTwoGauge D) u +
        uniformTwoNorm (allTracesTracialTwoGauge D) v := by
  apply uniformTwoNorm_le
  intro n
  exact ((allTracesTracialTwoGauge D).add_le n (u n) (v n)).trans
    (add_le_add
      (q_le_uniformTwoNorm (allTracesTracialTwoGauge D) u n)
      (q_le_uniformTwoNorm (allTracesTracialTwoGauge D) v n))

/-- The coordinate supremum of a difference is bounded by its operator norm. -/
theorem uniformTwoNorm_sub_le_norm
    (u v : BoundedCStarSequence D) :
    uniformTwoNorm (allTracesTracialTwoGauge D) (u - v) ≤ ‖u - v‖ :=
  uniformTwoNorm_le_norm _ _

/-- Every actual tracial state of the unitized `c₀` base is controlled by
the coordinate all-traces uniform two-gauge. -/
theorem tracialTwoNorm_le_uniformTwoNorm_allTraces
    (σ : TracialState (BaseAlgebra D)) (x : BaseAlgebra D) :
    tracialTwoNorm σ x ≤
      uniformTwoNorm (allTracesTracialTwoGauge D) x.1 := by
  obtain ⟨c, hc⟩ := (mem_baseAlgebra_iff x.1).1 x.2
  refine _root_.le_of_forall_pos_le_add fun ε hε ↦ ?_
  have hhalf : 0 < ε / 2 := half_pos hε
  have ht := tendsto_baseScalarTruncation x c hc
  rw [Metric.tendsto_atTop] at ht
  obtain ⟨N₀, hN₀⟩ := ht (ε / 2) hhalf
  let y := baseScalarTruncation x c N₀
  have hyx : ‖y.1 - x.1‖ < ε / 2 := by
    have hdist := hN₀ N₀ le_rfl
    rw [dist_eq_norm] at hdist
    exact hdist
  have hxy : ‖x - y‖ < ε / 2 := by
    rw [norm_sub_rev]
    exact hyx
  have hτy : tracialTwoNorm σ y ≤
      uniformTwoNorm (allTracesTracialTwoGauge D) y.1 :=
    tracialTwoNorm_baseScalarTruncation_le_uniformTwoNorm σ x c N₀
  have hUy : uniformTwoNorm (allTracesTracialTwoGauge D) y.1 ≤
      uniformTwoNorm (allTracesTracialTwoGauge D) x.1 + ‖y.1 - x.1‖ := by
    calc
      uniformTwoNorm (allTracesTracialTwoGauge D) y.1 =
          uniformTwoNorm (allTracesTracialTwoGauge D)
            (x.1 + (y.1 - x.1)) := by
              congr 1
              abel
      _ ≤ uniformTwoNorm (allTracesTracialTwoGauge D) x.1 +
          uniformTwoNorm (allTracesTracialTwoGauge D) (y.1 - x.1) :=
        uniformTwoNorm_add_le _ _
      _ ≤ uniformTwoNorm (allTracesTracialTwoGauge D) x.1 +
          ‖y.1 - x.1‖ := add_le_add le_rfl
            (uniformTwoNorm_sub_le_norm y.1 x.1)
  calc
    tracialTwoNorm σ x = tracialTwoNorm σ ((x - y) + y) := by
      rw [sub_add_cancel]
    _ ≤ tracialTwoNorm σ (x - y) + tracialTwoNorm σ y :=
      tracialTwoNorm_add_le σ _ _
    _ ≤ ‖x - y‖ + uniformTwoNorm (allTracesTracialTwoGauge D) y.1 :=
      add_le_add (tracialTwoNorm_le_norm σ _) hτy
    _ ≤ ‖x - y‖ +
        (uniformTwoNorm (allTracesTracialTwoGauge D) x.1 + ‖y.1 - x.1‖) :=
      add_le_add_right hUy _
    _ ≤ uniformTwoNorm (allTracesTracialTwoGauge D) x.1 + ε := by
      exact (by linarith :
        ‖x - y‖ +
            (uniformTwoNorm (allTracesTracialTwoGauge D) x.1 +
              ‖y.1 - x.1‖) <
          uniformTwoNorm (allTracesTracialTwoGauge D) x.1 + ε).le

/-- The literal uniform tracial two-size on the actual base algebra equals the
coordinate supremum used to construct its bounded uniform-two completion. -/
theorem baseTracialTwoSize_eq_uniformTwoNorm_allTraces
    (x : BaseAlgebra D) :
    baseTracialTwoSize x =
      uniformTwoNorm (allTracesTracialTwoGauge D) x.1 := by
  apply le_antisymm
  · rw [baseTracialTwoSize]
    refine csSup_le (Set.range_nonempty _) ?_
    rintro _ ⟨σ, rfl⟩
    exact tracialTwoNorm_le_uniformTwoNorm_allTraces σ x
  · exact uniformTwoNorm_allTraces_le_baseTracialTwoSize x

end

end STW22BaseUniformTracialGauge
end GroupApproximation
