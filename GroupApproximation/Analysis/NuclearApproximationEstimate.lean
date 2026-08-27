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
`finDimOperatorBlock` is the first: the operators on `ℂᵏ`, which is what the
completely positive approximation of the Lance lane actually factors through.
It is not the matrix algebra: `Mₖ(ℂ)` and `B(ℂᵏ)` are isometrically
⋆-isomorphic but are not the same type, and at the pinned Mathlib revision only
the second carries a `CStarAlgebra` instance at all.

Nothing about the bundle is assembled by hand, and that is the point rather
than an economy.  `CStarAlgebra (E →L[ℂ] E)` is a Mathlib instance for every
complex Hilbert space `E`, and `ContinuousLinearMap.instModuleFinite` supplies
finite-dimensionality; letting instance search fill both fields is what makes
the bundle's `Module ℂ` *the same* `Module ℂ` that every map in the lane was
built at.  A hand-assembled `CStarAlgebra` structure --- even one whose every
field is `inferInstance` --- is a different term, and every `α : A →ₗ[ℂ] B(ℂᵏ)`
would then have to be transported into it.

There is also no positivity clause on `k` anywhere on this row.  An earlier
reading of the gap recorded one, on the ground that `‖1‖ = 1` fails over an
empty index set; that is a fact about the *matrix* bundle at the L2 operator
norm, and Mathlib's C⋆-structure on `E →L[ℂ] E` asks for no nontriviality, so
`k = 0` is a legitimate (useless) target and the interface never has to
remember that a Følner set is nonempty.

## What stands between the CPAP and `IsNuclearCStarAlgebra`

Nothing, as of `Analysis/LanceNuclearAmenable`.  The two gaps this file used to
record are closed: the target is `finDimOperatorBlock` above, and complete
positivity of the corestricted map is
`CStarCorestrictCP.exists_factor_entries_mem_of_isCompletelyPositive`, proved
from the positivity permanence of `Analysis/LanceMatrixSubalgebra` --- the
square root of a positive matrix over a closed ⋆-subalgebra stays inside it.
-/

namespace GroupApproximation
namespace CStarExactness

universe u

noncomputable section

/-! ## A finite-dimensional target to factor through -/

/-- **The first inhabitant of `FinDimCStarAlgebra`.**  Until this, the class of
finite-dimensional targets `IsNuclearMap` factors through was empty in this
corpus, so no map could be shown nuclear whatever its approximations.

Both instance fields are filled by search rather than by hand; see the module
docstring for why that is not a matter of brevity. -/
def finDimOperatorBlock (k : ℕ) : FinDimCStarAlgebra :=
  { carrier := EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k) }

@[simp] theorem finDimOperatorBlock_carrier (k : ℕ) :
    (finDimOperatorBlock k).carrier
      = (EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k)) := rfl

/-! ## Bundling the approximation -/

/-- **The bundling step.**  Every map the Lance approximation produces is built
at the bare operator algebra on `ℂᵏ`; `IsNuclearMap` asks for a factorization
through a bundled `FinDimCStarAlgebra`.  This is the only place in the
development where the two are identified.

`k` is quantified *inside* the approximation rather than fixed in advance,
because the `k` a Følner set produces depends on both the finite set and the
tolerance. -/
theorem isNuclearMap_of_operatorBlock {A : Type u} [NonUnitalCStarAlgebra A]
    {φ : A →ₗ[ℂ] A}
    (h : ∀ (F : Finset A) (ε : ℝ), 0 < ε →
      ∃ (k : ℕ)
        (α : A →ₗ[ℂ] (EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k)))
        (β : (EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k)) →ₗ[ℂ] A),
        IsCompletelyPositive α ∧ IsCompletelyPositive β ∧
          (∀ a : A, ‖α a‖ ≤ ‖a‖) ∧
          (∀ d : EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k),
            ‖β d‖ ≤ ‖d‖) ∧
          ∀ a ∈ F, ‖β (α a) - φ a‖ ≤ ε) :
    IsNuclearMap φ := by
  intro F ε hε
  obtain ⟨k, α, β, hα, hβ, hαc, hβc, happ⟩ := h F ε hε
  exact ⟨finDimOperatorBlock k, α, β, hα, hβ, hαc, hβc, happ⟩

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
