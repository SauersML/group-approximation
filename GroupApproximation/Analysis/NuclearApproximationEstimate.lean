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
-/

namespace GroupApproximation
namespace CStarExactness

noncomputable section

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
