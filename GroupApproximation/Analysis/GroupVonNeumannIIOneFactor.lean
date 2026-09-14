import GroupApproximation.Analysis.GroupStandardFormInstance
import Mathlib.Analysis.Complex.Order
import Mathlib.LinearAlgebra.Dimension.Finite
import GroupApproximation.Meta.AxiomGuard

/-!
# II₁ factors, and the group von Neumann algebra of an infinite ICC group

`simple_kazhdan_sofic_group.tex` at origin/main e80dcf20a, "Finite models", tex 170 (first
clause of census row `07ce3ce2146f`):

> So `L(G)` is a `II₁` factor, ...

This module supplies the predicate and proves the group case.  Nothing is assumed: the factor
property is `GroupVonNeumann.isFactor` (`Analysis/GroupStandardFormInstance.lean`), and the trace
facts are those of `Analysis/GroupVonNeumannTrace.lean`.

* `IsNormalFunctional M τ`: on `M`, `τ` is a trace-class vector functional
  `T ↦ ∑ₙ ⟪ξₙ, T ηₙ⟫` with `∑ₙ ‖ξₙ‖ ‖ηₙ‖ < ∞`, i.e. a σ-weakly continuous (normal) functional.
* `IsFaithfulNormalTracialState M τ`: normal, `τ 1 = 1`, positive, tracial and faithful on `M`.
* `IsIIOneFactor M`: a factor that is infinite-dimensional and has a faithful normal tracial
  state.
* `groupTrace`: the identity coefficient `τ(T) = ⟪δ₁, T δ₁⟫`, a faithful normal tracial state
  on `L(G)`.
* `linearIndependent_leftRegularOperator`: the left translations are linearly independent in
  `L(G)`, because they send `δ₁` to the orthonormal point masses; so `L(G)` is
  infinite-dimensional when `G` is infinite.
* `isIIOneFactor_groupVonNeumannAlgebra`: over an infinite ICC group, `L(G)` is a II₁ factor.
-/

namespace GroupApproximation
namespace IIOneFactor

open scoped InnerProductSpace ComplexOrder

noncomputable section

universe u

section Predicates

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A **normal** functional on a von Neumann algebra `M`: on `M` it is a trace-class vector
functional `T ↦ ∑ₙ ⟪ξₙ, T ηₙ⟫` with `∑ₙ ‖ξₙ‖ ‖ηₙ‖ < ∞` (a σ-weakly continuous functional). -/
def IsNormalFunctional (M : VonNeumannAlgebra H) (τ : (H →L[ℂ] H) → ℂ) : Prop :=
  ∃ ξ η : ℕ → H, Summable (fun n ↦ ‖ξ n‖ * ‖η n‖) ∧
    ∀ T ∈ M, τ T = ∑' n, ⟪ξ n, T (η n)⟫_ℂ

/-- A **faithful normal tracial state** on a von Neumann algebra `M`. -/
structure IsFaithfulNormalTracialState (M : VonNeumannAlgebra H) (τ : (H →L[ℂ] H) → ℂ) :
    Prop where
  /-- `τ` is normal on `M`. -/
  normal : IsNormalFunctional M τ
  /-- `τ` is unital. -/
  map_one : τ 1 = 1
  /-- `τ` is positive on `M`. -/
  nonneg : ∀ T ∈ M, 0 ≤ τ (star T * T)
  /-- `τ` is a trace on `M`. -/
  tracial : ∀ T ∈ M, ∀ S ∈ M, τ (T * S) = τ (S * T)
  /-- `τ` is faithful on `M`. -/
  faithful : ∀ T ∈ M, τ (star T * T) = 0 → T = 0

/-- A **II₁ factor**: an infinite-dimensional factor with a faithful normal tracial state. -/
structure IsIIOneFactor (M : VonNeumannAlgebra H) : Prop where
  /-- The centre of `M` is the scalars. -/
  isFactor : TracialStandardForm.IsFactor M
  /-- `M` is infinite-dimensional. -/
  infinite_dimensional : ¬ Module.Finite ℂ ↥M.toStarSubalgebra
  /-- `M` has a faithful normal tracial state. -/
  exists_trace : ∃ τ : (H →L[ℂ] H) → ℂ, IsFaithfulNormalTracialState M τ

end Predicates

section Group

open ReducedGroupCStarTrace TwoSidedRegularCommutant GroupVonNeumann

variable (G : Type u) [Group G]

local instance : DecidableEq G := Classical.decEq G

/-- The identity coefficient `τ(T) = ⟪δ₁, T δ₁⟫` on the bounded operators of `ℓ²(G)`. -/
def groupTrace (T : GroupHilbert G →L[ℂ] GroupHilbert G) : ℂ :=
  ⟪deltaOne G, T (deltaOne G)⟫_ℂ

theorem groupTrace_eq_coefficient (T : GroupHilbert G →L[ℂ] GroupHilbert G) :
    groupTrace G T = (T (deltaOne G)) 1 :=
  inner_deltaOne_left G _

/-- The identity coefficient is a vector functional, hence normal. -/
theorem groupTrace_isNormalFunctional :
    IsNormalFunctional (groupVonNeumannAlgebra G) (groupTrace G) := by
  refine ⟨fun n ↦ if n = 0 then deltaOne G else 0,
    fun n ↦ if n = 0 then deltaOne G else 0, ?_, ?_⟩
  · apply summable_of_ne_finset_zero (s := {0})
    intro n hn
    have hn0 : n ≠ 0 := by simpa using hn
    simp [hn0]
  · intro T _hT
    rw [tsum_eq_single 0]
    · simp [groupTrace]
    · intro n hn
      simp [hn]

/-- `τ(T⋆T) ≥ 0`. -/
theorem groupTrace_star_mul_self_nonneg (T : GroupHilbert G →L[ℂ] GroupHilbert G) :
    0 ≤ groupTrace G (star T * T) := by
  rw [groupTrace_eq_coefficient, coefficient_star_mul_self]
  have h : (‖T (deltaOne G)‖ : ℂ) ^ 2 = ((‖T (deltaOne G)‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_pow]
  rw [h]
  exact Complex.zero_le_real.mpr (sq_nonneg _)

/-- **The identity coefficient is a faithful normal tracial state on `L(G)`.** -/
theorem groupTrace_isFaithfulNormalTracialState :
    IsFaithfulNormalTracialState (groupVonNeumannAlgebra G) (groupTrace G) where
  normal := groupTrace_isNormalFunctional G
  map_one := by
    rw [groupTrace_eq_coefficient]
    exact coefficient_one G
  nonneg := fun T _ ↦ groupTrace_star_mul_self_nonneg G T
  tracial := fun T hT S hS ↦ by
    rw [groupTrace_eq_coefficient, groupTrace_eq_coefficient]
    exact coefficient_mul_comm G hT hS
  faithful := fun T hT h ↦ by
    rw [groupTrace_eq_coefficient] at h
    exact eq_zero_of_mem_of_coefficient_star_mul_self_eq_zero G hT h

omit [Group G] in
/-- The point masses of `ℓ²(G)` are orthonormal. -/
theorem orthonormal_groupHilbert_single :
    Orthonormal ℂ (fun g : G ↦ (lp.single 2 g (1 : ℂ) : GroupHilbert G)) := by
  rw [orthonormal_iff_ite]
  intro g h
  rw [lp.inner_single_left, lp.single_apply]
  by_cases hgh : g = h
  · subst hgh
    simp
  · simp [hgh]

/-- **The left translations are linearly independent in `L(G)`.** -/
theorem linearIndependent_leftRegularOperator :
    LinearIndependent ℂ
      (fun g : G ↦ (⟨leftRegularOperator G g, leftRegularOperator_mem G g⟩ :
        ↥(groupVonNeumannAlgebra G).toStarSubalgebra)) := by
  let ev : ↥(groupVonNeumannAlgebra G).toStarSubalgebra →ₗ[ℂ] GroupHilbert G :=
    { toFun := fun T ↦ (T : GroupHilbert G →L[ℂ] GroupHilbert G) (deltaOne G)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  apply LinearIndependent.of_comp ev
  have hcomp : ev ∘ (fun g : G ↦ (⟨leftRegularOperator G g, leftRegularOperator_mem G g⟩ :
        ↥(groupVonNeumannAlgebra G).toStarSubalgebra)) =
      fun g : G ↦ (lp.single 2 g (1 : ℂ) : GroupHilbert G) := by
    funext g
    exact leftRegularOperator_deltaOne G g
  rw [hcomp]
  exact (orthonormal_groupHilbert_single G).linearIndependent

/-- Over an infinite group, `L(G)` is infinite-dimensional. -/
theorem not_finite_groupVonNeumannAlgebra [Infinite G] :
    ¬ Module.Finite ℂ ↥(groupVonNeumannAlgebra G).toStarSubalgebra := by
  intro hfin
  exact Module.Finite.not_linearIndependent_of_infinite _
    (linearIndependent_leftRegularOperator G)

/-- **Over an infinite ICC group, `L(G)` is a II₁ factor.** -/
theorem isIIOneFactor_groupVonNeumannAlgebra [Infinite G] (hG : IsICC G) :
    IsIIOneFactor (groupVonNeumannAlgebra G) where
  isFactor := GroupVonNeumann.isFactor G hG
  infinite_dimensional := not_finite_groupVonNeumannAlgebra G
  exists_trace := ⟨groupTrace G, groupTrace_isFaithfulNormalTracialState G⟩

end Group

end

end IIOneFactor
end GroupApproximation

#audit_axioms GroupApproximation.IIOneFactor.isIIOneFactor_groupVonNeumannAlgebra
