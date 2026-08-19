import GroupApproximation.Analysis.CStarFormCompletelyPositive

/-!
# From approximation on a spanning set to approximation everywhere

`NuclearReducedCPAP` says the composite `up ∘ down` nearly fixes a finite set of
*translations*; `CStarExactness.IsNuclearMap` asks that it nearly fix a finite
set of *algebra elements*.  `ReducedGroupCStarTrace.exists_translationSum_approx`
bridges the two sets --- every element of the reduced algebra is within `η` of a
finite combination of translations --- and this file is the estimate that turns
that bridge into the bound.

It is the three-`ε` argument, and nothing about it is specific to group
C⋆-algebras, so it is stated for arbitrary contractive linear maps:

```text
    β(α a) − a  =  β(α(a − s))  +  (β(α s) − s)  +  (s − a),
```

with `s` the combination.  The outer two terms are `‖a − s‖` and no more,
because `α` and `β` are contractions; the middle one distributes over the
combination, so it costs the sum of the moduli of the coefficients times the
defect on each spanning vector.

Contractivity is exactly what the Lance approximation could not supply on its
own, and `CStarExactness.norm_le_of_form_unital` now supplies it for `down`
while `norm_apply_le_of_unital` covers `up`.

## The finite-dimensional target

`IsNuclearMap` quantifies over `FinDimCStarAlgebra`, and **nothing in this
corpus had ever built one** --- the definition existed with no inhabitant, so no
map had ever been shown nuclear for want of a target to factor through.
`finDimMatrixBlock` and `finDimOperatorBlock` are the first two: square matrices
at the L2 operator norm, and the operators on `ℂᵏ` that the CPAP actually
factors through.  Each C⋆-structure is six field assignments, every one of them
an instance already.  It
is kept a `def` rather than an `instance` for the reason
`Analysis/PolarLiftingMatrixBlocks` keeps its copy `local`: the norm is scoped,
and registering the bundle globally would put it in competition with the
Hilbert--Schmidt structure the corona lane uses on the same type.

`NeZero k` is not bookkeeping.  The identity matrix must have norm one, which
fails over an empty index set; the CPAP produces its `k` from a Følner set,
which is nonempty for that reason.
-/

namespace GroupApproximation
namespace CStarExactness

open scoped Matrix.Norms.L2Operator

noncomputable section

/-! ## A finite-dimensional target to factor through -/

/-- The bundled C⋆-algebra structure on a square matrix block at the L2
operator norm.  Six field assignments, every one of them an instance already.

A `def` and not an `instance`: the L2 operator norm is scoped, and the same type
carries a Hilbert--Schmidt structure elsewhere in this development. -/
def matrixBlockCStarAlgebra (k : ℕ) [NeZero k] :
    CStarAlgebra (Matrix (Fin k) (Fin k) ℂ) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

/-- **The first inhabitant of `FinDimCStarAlgebra`.**  Until this, the class of
finite-dimensional targets `IsNuclearMap` factors through was empty in this
corpus, so no map could be shown nuclear whatever its approximations. -/
def finDimMatrixBlock (k : ℕ) [NeZero k] : FinDimCStarAlgebra where
  carrier := Matrix (Fin k) (Fin k) ℂ
  algebra := matrixBlockCStarAlgebra k
  findim := inferInstance

@[simp] theorem finDimMatrixBlock_carrier (k : ℕ) [NeZero k] :
    (finDimMatrixBlock k).carrier = Matrix (Fin k) (Fin k) ℂ := rfl

/-- The same bundle at the *operator* block.  This is the one the Lance
approximation needs: `NuclearReducedCPAP` factors through
`EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k)`, not through matrices,
and the two are isometrically `⋆`-isomorphic but not the same type.

`NeZero k` again buys `‖1‖ = 1`, which is what separates a C⋆-algebra from a
C⋆-ring here. -/
def operatorBlockCStarAlgebra (k : ℕ) [NeZero k] :
    CStarAlgebra (EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k)) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

/-- **The finite-dimensional target the Lance approximation factors through.**
-/
def finDimOperatorBlock (k : ℕ) [NeZero k] : FinDimCStarAlgebra where
  carrier := EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k)
  algebra := operatorBlockCStarAlgebra k
  findim := inferInstance

@[simp] theorem finDimOperatorBlock_carrier (k : ℕ) [NeZero k] :
    (finDimOperatorBlock k).carrier
      = (EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k)) := rfl

/-! ## Three epsilons -/

/-- **Three epsilons.**  A composite of contractions that nearly fixes each
vector of a combination nearly fixes anything the combination approximates.

The bound is `2η + (∑ ‖cᵢ‖) δ`: one `η` for pushing `a` to the combination
through the contractions, one for coming back, and the coefficient sum for the
defect the composite has on the spanning vectors themselves. -/
theorem norm_comp_sub_le_of_span_approx
    {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup D] [NormedSpace ℂ D]
    (α : E →ₗ[ℂ] D) (β : D →ₗ[ℂ] E)
    (hα : ∀ x, ‖α x‖ ≤ ‖x‖) (hβ : ∀ y, ‖β y‖ ≤ ‖y‖)
    {n : ℕ} (c : Fin n → ℂ) (u : Fin n → E) (a : E) {η δ : ℝ}
    (hspan : ‖a - ∑ i : Fin n, c i • u i‖ ≤ η)
    (hfix : ∀ i : Fin n, ‖β (α (u i)) - u i‖ ≤ δ) :
    ‖β (α a) - a‖ ≤ 2 * η + (∑ i : Fin n, ‖c i‖) * δ := by
  classical
  set s : E := ∑ i : Fin n, c i • u i with hs
  have hsplit : β (α a) - a
      = β (α (a - s)) + (β (α s) - s) + (s - a) := by
    rw [map_sub, map_sub]
    abel
  have h1 : ‖β (α (a - s))‖ ≤ η :=
    (hβ _).trans ((hα _).trans hspan)
  have h2 : ‖β (α s) - s‖ ≤ (∑ i : Fin n, ‖c i‖) * δ := by
    have hαs : α s = ∑ i : Fin n, c i • α (u i) := by
      rw [hs, map_sum]
      exact Finset.sum_congr rfl fun i _ ↦ map_smul _ _ _
    have hβs : β (α s) = ∑ i : Fin n, c i • β (α (u i)) := by
      rw [hαs, map_sum]
      exact Finset.sum_congr rfl fun i _ ↦ map_smul _ _ _
    have hexp : β (α s) - s = ∑ i : Fin n, c i • (β (α (u i)) - u i) := by
      rw [hβs, hs, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ (smul_sub _ _ _).symm
    rw [hexp, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hfix i) (norm_nonneg _)
  have h3 : ‖s - a‖ ≤ η := by
    rw [← norm_neg, neg_sub]
    exact hspan
  calc ‖β (α a) - a‖
      = ‖β (α (a - s)) + (β (α s) - s) + (s - a)‖ := by rw [hsplit]
    _ ≤ ‖β (α (a - s)) + (β (α s) - s)‖ + ‖s - a‖ := norm_add_le _ _
    _ ≤ ‖β (α (a - s))‖ + ‖β (α s) - s‖ + ‖s - a‖ := by
        gcongr
        exact norm_add_le _ _
    _ ≤ η + (∑ i : Fin n, ‖c i‖) * δ + η := by gcongr
    _ = 2 * η + (∑ i : Fin n, ‖c i‖) * δ := by ring

end

end CStarExactness
end GroupApproximation
