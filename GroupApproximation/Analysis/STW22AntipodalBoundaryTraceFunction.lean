import GroupApproximation.Analysis.STW22AntipodalBlockMeasureTrace
import GroupApproximation.Analysis.STW22BaseAlgebraNuclear
import GroupApproximation.Analysis.TracialStateWeakStarTopology

/-!
# Continuous boundary evaluations for the antipodal base algebra

Every point of the one-point compactification gives an actual tracial state
of the scalar-tail base algebra.  Evaluation of a fixed base element against
these traces is continuous: on a finite projective component this is the
continuous normalized fibre trace, while convergence at infinity is exactly
the defining operator-norm convergence to the scalar tail.
-/

namespace GroupApproximation
namespace STW22AntipodalBoundaryTraceFunction

open Filter MeasureTheory Topology
open STW22
open STW22ActualTraceSpaces
open STW22BaseUniformTracialGauge
open STW22BaseAlgebraNuclear
open STW22AntipodalTraceBoundary
open STW22AntipodalBlockMeasureTrace
open UniformTracialGNSTwoGauge
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

open scoped OnePoint

/-- The quotient trace at the point at infinity. -/
def infinityBaseTracialState :
    TracialState (BaseAlgebra AntipodalCounterexampleBlock) :=
  (UniformTracialGNSTwoGauge.complexTracialState).compStarAlgHom
    (baseScalarStarAlgHom AntipodalCounterexampleBlock)

@[simp] theorem infinityBaseTracialState_apply
    (a : BaseAlgebra AntipodalCounterexampleBlock) :
    infinityBaseTracialState a =
      baseScalarStarAlgHom AntipodalCounterexampleBlock a := by
  change UniformTracialGNSTwoGauge.complexTracialState
    (baseScalarStarAlgHom AntipodalCounterexampleBlock a) = _
  exact tracialState_complex_eq _ _

/-- A finite projective boundary point, pulled back along coordinate
evaluation, gives a trace of the whole base algebra. -/
def finiteBoundaryBaseTracialState
    (z : Σ n : ℕ, RP (antipodalBlockDimension n)) :
    TracialState (BaseAlgebra AntipodalCounterexampleBlock) :=
  (finiteBoundaryBlockTrace z).compStarAlgHom
    (baseCoordinateStarAlgHom (D := AntipodalCounterexampleBlock) z.1)

@[simp] theorem finiteBoundaryBaseTracialState_apply
    (z : Σ n : ℕ, RP (antipodalBlockDimension n))
    (a : BaseAlgebra AntipodalCounterexampleBlock) :
    finiteBoundaryBaseTracialState z a =
      finiteBoundaryBlockTrace z (a.1 z.1) := by
  rfl

/-- The actual boundary-indexed family of base tracial states. -/
def boundaryBaseTracialState : AntipodalTraceBoundary →
    TracialState (BaseAlgebra AntipodalCounterexampleBlock) :=
  fun z ↦ z.elim infinityBaseTracialState finiteBoundaryBaseTracialState

@[simp] theorem boundaryBaseTracialState_infty :
    boundaryBaseTracialState (∞ : AntipodalTraceBoundary) =
      infinityBaseTracialState := rfl

@[simp] theorem boundaryBaseTracialState_coe
    (z : Σ n : ℕ, RP (antipodalBlockDimension n)) :
    boundaryBaseTracialState (z : AntipodalTraceBoundary) =
      finiteBoundaryBaseTracialState z := rfl

/-- Evaluation on the finite disjoint union is continuous componentwise. -/
def finiteBoundaryTraceFunction
    (a : BaseAlgebra AntipodalCounterexampleBlock) :
    C(Σ n : ℕ, RP (antipodalBlockDimension n), ℂ) where
  toFun z := finiteBoundaryBaseTracialState z a
  continuous_toFun := by
    apply continuous_sigma
    intro n
    change Continuous (fun x ↦
      projectiveFibreTracialState (antipodalBlockDimension n)
        (antipodalBlockSize n) x (a.1 n))
    simpa only [← projectiveBlockTraceFunction_eq_projectiveFibre] using
      (projectiveBlockTraceFunction (a.1 n)).continuous

@[simp] theorem finiteBoundaryTraceFunction_apply
    (a : BaseAlgebra AntipodalCounterexampleBlock)
    (z : Σ n : ℕ, RP (antipodalBlockDimension n)) :
    finiteBoundaryTraceFunction a z = finiteBoundaryBaseTracialState z a := rfl

/-- The finite-boundary trace values converge to the quotient trace along the
coclosed-compact filter. -/
theorem tendsto_finiteBoundaryTraceFunction
    (a : BaseAlgebra AntipodalCounterexampleBlock) :
    Tendsto (finiteBoundaryTraceFunction a)
      (coclosedCompact (Σ n : ℕ, RP (antipodalBlockDimension n)))
      (nhds (infinityBaseTracialState a)) := by
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  have htail := tendsto_norm_sub_baseScalar AntipodalCounterexampleBlock a
  rw [Metric.tendsto_atTop] at htail
  obtain ⟨N, hN⟩ := htail epsilon hepsilon
  let K : Set (Σ n : ℕ, RP (antipodalBlockDimension n)) :=
    ⋃ i : Fin N, Set.range (@Sigma.mk ℕ
      (fun n ↦ RP (antipodalBlockDimension n)) i.1)
  have hKcompact : IsCompact K := by
    exact isCompact_iUnion fun i ↦ isCompact_range continuous_sigmaMk
  refine hasBasis_coclosedCompact.mem_iff.mpr
    ⟨K, ⟨hKcompact.isClosed, hKcompact⟩, ?_⟩
  intro z hz
  have hn : N ≤ z.1 := by
    by_contra hn
    have hlt : z.1 < N := Nat.lt_of_not_ge hn
    apply hz
    exact Set.mem_iUnion_of_mem ⟨z.1, hlt⟩ ⟨z.2, rfl⟩
  let tau := finiteBoundaryBlockTrace z
  have hscalar : tau
      (algebraMap ℂ (AntipodalCounterexampleBlock z.1)
        (baseScalarStarAlgHom AntipodalCounterexampleBlock a)) =
      baseScalarStarAlgHom AntipodalCounterexampleBlock a := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, tau.apply_one, smul_eq_mul,
      mul_one]
  have heval : finiteBoundaryTraceFunction a z - infinityBaseTracialState a =
      tau (a.1 z.1 - algebraMap ℂ (AntipodalCounterexampleBlock z.1)
        (baseScalarStarAlgHom AntipodalCounterexampleBlock a)) := by
    rw [map_sub, hscalar]
    rfl
  change dist (finiteBoundaryTraceFunction a z)
    (infinityBaseTracialState a) < epsilon
  rw [dist_eq_norm, heval]
  refine lt_of_le_of_lt
    (Manuscript.MFRecognition.TensorSynchronization.norm_tracialState_le tau _) ?_
  have hnorm : 0 ≤ ‖a.1 z.1 -
      algebraMap ℂ (AntipodalCounterexampleBlock z.1)
        (baseScalarStarAlgHom AntipodalCounterexampleBlock a)‖ := norm_nonneg _
  calc
    ‖a.1 z.1 - algebraMap ℂ (AntipodalCounterexampleBlock z.1)
        (baseScalarStarAlgHom AntipodalCounterexampleBlock a)‖ =
        dist ‖a.1 z.1 - algebraMap ℂ (AntipodalCounterexampleBlock z.1)
          (baseScalarStarAlgHom AntipodalCounterexampleBlock a)‖ 0 := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hnorm]
    _ < epsilon := hN z.1 hn

/-- The normalized fibre trace of every base element extends continuously to
the point at infinity. -/
def boundaryTraceFunction
    (a : BaseAlgebra AntipodalCounterexampleBlock) :
    C(AntipodalTraceBoundary, ℂ) :=
  OnePoint.continuousMapMk (finiteBoundaryTraceFunction a)
    (infinityBaseTracialState a) (tendsto_finiteBoundaryTraceFunction a)

@[simp] theorem boundaryTraceFunction_infty
    (a : BaseAlgebra AntipodalCounterexampleBlock) :
    boundaryTraceFunction a (∞ : AntipodalTraceBoundary) =
      infinityBaseTracialState a := rfl

@[simp] theorem boundaryTraceFunction_coe
    (a : BaseAlgebra AntipodalCounterexampleBlock)
    (z : Σ n : ℕ, RP (antipodalBlockDimension n)) :
    boundaryTraceFunction a (z : AntipodalTraceBoundary) =
      finiteBoundaryBaseTracialState z a := rfl

theorem boundaryTraceFunction_eq_boundaryBaseTracialState
    (a : BaseAlgebra AntipodalCounterexampleBlock)
    (z : AntipodalTraceBoundary) :
    boundaryTraceFunction a z = boundaryBaseTracialState z a := by
  induction z using OnePoint.rec <;> rfl

end

end STW22AntipodalBoundaryTraceFunction
end GroupApproximation
