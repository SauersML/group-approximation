import GroupApproximation.Analysis.GroupStandardFormInstance
import GroupApproximation.Analysis.PermutationICC
import GroupApproximation.Analysis.ShiftIsometry
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# `p:limits-trace`: the standard-form sentence, assembled

Proof-ledger row `LI.06d`.  The printed sentence:

> for faithfully traced unital C\*-coordinates `A` the left and right actions
> on `L²(A,τ)` generate a von Neumann algebra that need not be finite: for an
> infinite-dimensional II₁ factor in standard form it is all of `B(L²(A,τ))`.

This module assembles the witness from the lane's pieces.  The coordinate
algebra is the group von Neumann algebra `A = L(G)` of `G = Perm ℕ`, its
faithful trace is the `δ₁`-coefficient, and `L²(A,τ)` is its standard form
`ℓ²(G)`:

* **`A` is faithfully traced in standard form** —
  `GroupVonNeumann.isTracialStandardForm`: `δ₁` is a unit cyclic separating
  tracial vector.
* **`A` is a II₁ factor** — a factor (`GroupVonNeumann.isFactor`, from the
  ICC commutant computation), infinite-dimensional
  (`not_moduleFinite_groupVonNeumannAlgebra`: the left translations are an
  infinite linearly independent family), and finite
  (`GroupVonNeumann.mul_star_eq_one_of_star_mul_eq_one`: isometries are
  unitaries, by the faithful trace).
* **The two actions generate all of `B(L²)`** —
  `TracialStandardForm.centralizer_centralizer_union_commutant` at the factor
  property, the right action being the `J`-conjugate of the left action for
  `GroupVonNeumann.groupTracialConjugation` by the commutation theorem; and,
  independently and concretely,
  `GroupVonNeumann.doubleCentralizer_union_eq_univ` for the two regular
  representations.
* **`B(L²)` is not finite** — `ShiftIsometry.exists_isometry_not_unitary`: a
  non-unitary isometry.  This is the sentence's "need not be finite", in
  contrast with the finiteness of `L(G)` itself.

`manuscriptLimitsTraceStandardForm` is the conjunction, stated on the named
witness.
-/

namespace GroupApproximation
namespace LimitsTraceStandardForm

open ReducedGroupCStarTrace TwoSidedRegularCommutant GroupVonNeumann
open TracialStandardForm PermutationICC ShiftIsometry

noncomputable section

universe u

variable (G : Type u) [Group G]

local instance : DecidableEq G := Classical.decEq G

/-! ## Infinite-dimensionality of `L(G)` -/

/-- **The left translations are linearly independent**: a vanishing
combination, applied to `δ₁` and read at a point mass, has vanishing
coefficients. -/
theorem linearIndependent_leftRegularOperator :
    LinearIndependent ℂ (fun g : G ↦ leftRegularOperator G g) := by
  rw [linearIndependent_iff']
  intro s coef hsum g₀ hg₀
  have h1 : (∑ g ∈ s, coef g • leftRegularOperator G g) (deltaOne G)
      = ∑ g ∈ s, coef g • (lp.single 2 g 1 : GroupHilbert G) := by
    refine (map_sum (ContinuousLinearMap.apply ℂ (GroupHilbert G)
      (deltaOne G)) _ s).trans ?_
    refine Finset.sum_congr rfl fun g _ ↦ ?_
    exact (map_smul (ContinuousLinearMap.apply ℂ (GroupHilbert G)
        (deltaOne G)) (coef g) (leftRegularOperator G g)).trans
      (congrArg (fun z ↦ coef g • z) (leftRegularOperator_deltaOne G g))
  rw [hsum] at h1
  have h2 : (0 : GroupHilbert G)
      = ∑ g ∈ s, coef g • (lp.single 2 g 1 : GroupHilbert G) := h1
  have h3 : ((0 : GroupHilbert G) : G → ℂ) g₀
      = (∑ g ∈ s, coef g • (lp.single 2 g 1 : GroupHilbert G)) g₀ := by
    rw [← h2]
  have h4 : (∑ g ∈ s, coef g • (lp.single 2 g 1 : GroupHilbert G)) g₀
      = ∑ g ∈ s, coef g * (if g₀ = g then 1 else 0) := by
    refine (map_sum (lp.evalCLM ℂ (fun _ : G ↦ ℂ) 2 g₀) _ s).trans ?_
    refine Finset.sum_congr rfl fun g _ ↦ ?_
    refine (map_smul (lp.evalCLM ℂ (fun _ : G ↦ ℂ) 2 g₀) (coef g)
      (lp.single 2 g 1 : GroupHilbert G)).trans ?_
    show coef g • ((lp.single 2 g 1 : GroupHilbert G) g₀)
        = coef g * (if g₀ = g then 1 else 0)
    rw [lp.single_apply, Pi.single_apply, smul_eq_mul]
  have h5 : ∑ g ∈ s, coef g * (if g₀ = g then 1 else 0) = coef g₀ := by
    rw [show (fun g ↦ coef g * (if g₀ = g then 1 else 0))
          = fun g ↦ if g₀ = g then coef g else 0 from funext fun g ↦ by
        by_cases hgg : g₀ = g
        · rw [if_pos hgg, if_pos hgg, mul_one]
        · rw [if_neg hgg, if_neg hgg, mul_zero]]
    rw [Finset.sum_ite_eq s g₀ coef, if_pos hg₀]
  rw [h4, h5] at h3
  have h6 : ((0 : GroupHilbert G) : G → ℂ) g₀ = 0 := by
    rw [lp.coeFn_zero]
    rfl
  rw [h6] at h3
  exact h3.symm

/-- **`L(G)` is infinite-dimensional** over an infinite group. -/
theorem not_moduleFinite_groupVonNeumannAlgebra [Infinite G] :
    ¬ Module.Finite ℂ
      ((groupVonNeumannAlgebra G).toStarSubalgebra.toSubalgebra) := by
  intro hfin
  haveI := hfin
  have hindep : LinearIndependent ℂ
      (fun g : G ↦
        (⟨leftRegularOperator G g, leftRegularOperator_mem G g⟩ :
          ((groupVonNeumannAlgebra G).toStarSubalgebra.toSubalgebra))) := by
    apply LinearIndependent.of_comp
      ((groupVonNeumannAlgebra G).toStarSubalgebra.toSubalgebra.val.toLinearMap)
    exact linearIndependent_leftRegularOperator G
  exact Module.Finite.not_linearIndependent_of_infinite _ hindep

/-! ## The sentence, on the named witness -/

/-- **`p:limits-trace`, the standard-form sentence.**  For the II₁ factor
`L(Perm ℕ)` in its tracial standard form: the vector state at `δ₁` is a unit
cyclic separating trace; the algebra is a factor, infinite-dimensional, and
finite; the two standard-form actions generate all of `B(L²)`; and `B(L²)` is
not finite, witnessed by a non-unitary isometry. -/
theorem manuscriptLimitsTraceStandardForm :
    IsTracialStandardForm (groupVonNeumannAlgebra (Equiv.Perm ℕ))
        (deltaOne (Equiv.Perm ℕ))
    ∧ IsFactor (groupVonNeumannAlgebra (Equiv.Perm ℕ))
    ∧ ¬ Module.Finite ℂ
        ((groupVonNeumannAlgebra (Equiv.Perm ℕ)).toStarSubalgebra.toSubalgebra)
    ∧ (∀ v ∈ groupVonNeumannAlgebra (Equiv.Perm ℕ),
        star v * v = 1 → v * star v = 1)
    ∧ Set.centralizer (Set.centralizer
        ((groupVonNeumannAlgebra (Equiv.Perm ℕ) :
            Set (GroupHilbert (Equiv.Perm ℕ) →L[ℂ]
              GroupHilbert (Equiv.Perm ℕ)))
          ∪ ((groupVonNeumannAlgebra (Equiv.Perm ℕ)).commutant :
            Set (GroupHilbert (Equiv.Perm ℕ) →L[ℂ]
              GroupHilbert (Equiv.Perm ℕ)))))
        = Set.univ
    ∧ ∃ V : GroupHilbert (Equiv.Perm ℕ) →L[ℂ] GroupHilbert (Equiv.Perm ℕ),
        star V * V = 1 ∧ V * star V ≠ 1 := by
  haveI : Infinite (Equiv.Perm ℕ) := infinite_perm
  exact ⟨isTracialStandardForm (Equiv.Perm ℕ),
    isFactor (Equiv.Perm ℕ) isICC_perm,
    not_moduleFinite_groupVonNeumannAlgebra (Equiv.Perm ℕ),
    fun _v hv h ↦ mul_star_eq_one_of_star_mul_eq_one (Equiv.Perm ℕ) hv h,
    centralizer_centralizer_union_commutant
      (isFactor (Equiv.Perm ℕ) isICC_perm),
    exists_isometry_not_unitary (Equiv.Perm ℕ)⟩

end

end LimitsTraceStandardForm
end GroupApproximation
