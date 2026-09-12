import GroupApproximation.Analysis.STW22CounterexampleAssembly

/-!
# Actual trace spaces in the STW XXII completion endpoint

This file removes an avoidable abstraction from the trace-space endpoint.  The
base algebra is the actual closed star subalgebra obtained by specializing
`ℂ1 + J` to the operator norm gauge.  Its underlying set is exactly the
unitized `c₀`-sum.  The target is the actual bounded uniform-two Cauchy
quotient, already proved star-algebra equivalent to `ℂ1 + J`.

Consequently all traces below are bundled `TracialState`s on C-star algebras;
no arbitrary functional stands in for `T(A)`.  A completion trace restricts
along the explicit star-algebra homomorphism to a base trace.  If the completion
trace is a continuous extension of any base trace, it is in particular
uniform-two continuous.  Thus the discontinuous trace produced by the
compactness route gives the literal failure of the universal extension
statement for these two actual trace spaces.

This bridge is independent of the antipodal/common-zero theorem.  That geometry
is needed only to construct `CoordinateStateBlockData` for the intended block
family.
-/

namespace GroupApproximation
namespace STW22ActualTraceSpaces

open Filter PolarLiftingGeneralCStar
open UniformTracialSequenceCompletion UniformTracialTwoNullIdeal
open UniformTracialCompletionIdentification
open UniformTracialBoundedCauchyQuotient STW22Assembly
open CStarState

noncomputable section

set_option linter.unusedSectionVars false

universe u

variable {D : ℕ → Type u} [∀ n, CStarAlgebra (D n)]
  [∀ n, Nontrivial (D n)]

/-! ## The actual base C-star algebra -/

/-- The unitization of the `c₀`-sum as an actual C-star algebra.  We use the
closed star-subalgebra model `ℂ1 + J` for the operator-norm gauge; the theorem
`mem_baseAlgebra_iff` below proves that its carrier is literally
`unitizedC0Sum D`. -/
abbrev BaseAlgebra (D : ℕ → Type u) [∀ n, CStarAlgebra (D n)]
    [∀ n, Nontrivial (D n)] :=
  scalarPlusJSubalgebra (normTracialTwoGauge D)

/-- The chosen base C-star algebra has exactly the intended unitized `c₀`-sum
as its underlying set. -/
theorem mem_baseAlgebra_iff (x : BoundedCStarSequence D) :
    x ∈ BaseAlgebra D ↔ x ∈ unitizedC0Sum D := by
  change x ∈ scalarPlusJ (normTracialTwoGauge D) ↔ x ∈ unitizedC0Sum D
  rw [mem_scalarPlusJ_iff_sub]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, hc⟩

/-- The unitized `c₀`-sum is contained in every coordinate-gauge completion. -/
theorem baseAlgebra_le_scalarPlusJSubalgebra (G : TracialTwoGauge D) :
    BaseAlgebra D ≤ scalarPlusJSubalgebra G := by
  intro x hx
  exact unitizedC0Sum_subset_scalarPlusJ G ((mem_baseAlgebra_iff x).1 hx)

/-- The concrete inclusion of the actual base algebra into `ℂ1 + J`. -/
def baseToScalarPlusJ (G : TracialTwoGauge D) :
    BaseAlgebra D →⋆ₐ[ℂ] scalarPlusJSubalgebra G :=
  StarSubalgebra.inclusion (baseAlgebra_le_scalarPlusJSubalgebra G)

@[simp] theorem baseToScalarPlusJ_apply (G : TracialTwoGauge D)
    (x : BaseAlgebra D) :
    ((baseToScalarPlusJ G x : scalarPlusJSubalgebra G) :
      BoundedCStarSequence D) = x := rfl

/-! ## Inclusion into the actual Cauchy quotient and trace restriction -/

/-- The base algebra maps into the actual bounded uniform-two Cauchy quotient:
first include it in `ℂ1 + J`, then use the inverse of the proved realization
equivalence. -/
noncomputable def baseToCompletion (G : TracialTwoGauge D) {r : ℕ → ℝ}
    (hr : IsCoordinateNormComparison G r) :
    BaseAlgebra D →⋆ₐ[ℂ] BoundedUniformTwoCompletion G r hr :=
  (realizationStarAlgEquiv G hr).symm.toStarAlgHom.comp (baseToScalarPlusJ G)

@[simp] theorem realize_baseToCompletion (G : TracialTwoGauge D)
    {r : ℕ → ℝ} (hr : IsCoordinateNormComparison G r)
    (x : BaseAlgebra D) :
    realize G hr (baseToCompletion G hr x) = baseToScalarPlusJ G x := by
  exact (realizationStarAlgEquiv G hr).apply_symm_apply _

/-- Restriction of an actual completion tracial state to the actual base
C-star algebra. -/
def restrictToBase (G : TracialTwoGauge D) {r : ℕ → ℝ}
    (hr : IsCoordinateNormComparison G r)
    (σ : TracialState (BoundedUniformTwoCompletion G r hr)) :
    TracialState (BaseAlgebra D) :=
  σ.compStarAlgHom (baseToCompletion G hr)

@[simp] theorem restrictToBase_apply (G : TracialTwoGauge D)
    {r : ℕ → ℝ} (hr : IsCoordinateNormComparison G r)
    (σ : TracialState (BoundedUniformTwoCompletion G r hr))
    (x : BaseAlgebra D) :
    restrictToBase G hr σ x = σ (baseToCompletion G hr x) := rfl

/-! ## The literal trace-space endpoint -/

/-- Sequential continuity at zero for an actual tracial state on the actual
bounded uniform-two Cauchy quotient, measured through its concrete
realization. -/
def IsCompletionUniformTwoContinuous (G : TracialTwoGauge D) {r : ℕ → ℝ}
    (hr : IsCoordinateNormComparison G r)
    (σ : TracialState (BoundedUniformTwoCompletion G r hr)) : Prop :=
  ∀ x : ℕ → BoundedUniformTwoCompletion G r hr,
    Tendsto (fun N ↦ uniformTwoNorm G
      ((realize G hr (x N) : BoundedCStarSequence D))) atTop (nhds 0) →
    Tendsto (fun N ↦ σ (x N)) atTop (nhds 0)

/-- An actual completion trace is a continuous extension of an actual base
trace.  Both sides are bundled trace spaces of C-star algebras. -/
def IsContinuousExtension (G : TracialTwoGauge D) {r : ℕ → ℝ}
    (hr : IsCoordinateNormComparison G r)
    (σ : TracialState (BoundedUniformTwoCompletion G r hr))
    (τ : TracialState (BaseAlgebra D)) : Prop :=
  IsCompletionUniformTwoContinuous G hr σ ∧
    ∀ x : BaseAlgebra D, σ (baseToCompletion G hr x) = τ x

/-- A trace on the completion is a continuous extension of some actual base
trace exactly when it is uniformly two-continuous.  In the reverse direction
the base trace is its explicit restriction. -/
theorem exists_continuousExtension_iff (G : TracialTwoGauge D)
    {r : ℕ → ℝ} (hr : IsCoordinateNormComparison G r)
    (σ : TracialState (BoundedUniformTwoCompletion G r hr)) :
    (∃ τ : TracialState (BaseAlgebra D), IsContinuousExtension G hr σ τ) ↔
      IsCompletionUniformTwoContinuous G hr σ := by
  constructor
  · rintro ⟨τ, hcont, _⟩
    exact hcont
  · intro hcont
    refine ⟨restrictToBase G hr σ, hcont, ?_⟩
    intro x
    rfl

/-- The literal universal trace-space statement: every bundled tracial state
of the actual completion is a continuous extension of a bundled tracial state
of the actual base algebra. -/
def EveryCompletionTraceIsContinuousExtension (G : TracialTwoGauge D)
    {r : ℕ → ℝ} (hr : IsCoordinateNormComparison G r) : Prop :=
  ∀ σ : TracialState (BoundedUniformTwoCompletion G r hr),
    ∃ τ : TracialState (BaseAlgebra D), IsContinuousExtension G hr σ τ

/-- Any discontinuous tracial state on `ℂ1 + J` refutes the literal universal
statement for the two actual trace spaces after transport to the actual
Cauchy quotient. -/
theorem not_everyCompletionTraceIsContinuousExtension_of_discontinuous
    (G : TracialTwoGauge D) {r : ℕ → ℝ}
    (hr : IsCoordinateNormComparison G r)
    (hM : HasUniformTwoDiscontinuousTracialState G) :
    ¬ EveryCompletionTraceIsContinuousExtension G hr := by
  obtain ⟨σ, x, hxnull, hxnot⟩ :=
    exists_discontinuous_tracialState_completion G hr hM
  intro hall
  obtain ⟨τ, hτ⟩ := hall σ
  exact hxnot (hτ.1 x hxnull)

/-- The compactness-route block data refute the universal extension statement
on the actual base and completion trace spaces.  The only remaining geometric
work is to construct this data for the concrete antipodal family. -/
theorem not_everyCompletionTraceIsContinuousExtension_of_blockData
    (G : TracialTwoGauge D) {r : ℕ → ℝ}
    (hr : IsCoordinateNormComparison G r)
    (B : CoordinateStateBlockData D G) :
    ¬ EveryCompletionTraceIsContinuousExtension G hr :=
  not_everyCompletionTraceIsContinuousExtension_of_discontinuous G hr
    (hasUniformTwoDiscontinuousTracialState_of_blockData G B)

end

end STW22ActualTraceSpaces
end GroupApproximation
