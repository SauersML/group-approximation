import GroupApproximation.Analysis.LanceCPContractiveUnitalization
import GroupApproximation.Meta.AxiomGuard

/-!
# Related work (Blackadar--Kirchberg): unital nuclear approximations and defect estimates

Census row `14ee41b7f3cc`, `non_mf_groups_exist.tex` L310 (Related work):

> Their 1997 paper developed these notions and proved that a separable
> $C^*$-algebra is NF if and only if it is nuclear and MF~\cite{BK}.

This module holds two unconditional ingredients of the converse
"nuclear and MF implies NF". The overall route is in
`RelatedBK/LocalizationStatement`.

* `exists_ucp_cpc_finiteDimensional_approximation`. Start from a nuclear
  approximation `β ∘ α₀ ≈ id` within `δ < 1` on `S ∪ {1}`. The target `D` is
  nontrivial: otherwise `α₀ 1 = 0`, and the unit estimate would read
  `1 ≤ δ`. The additive unitalization `α = α₀ + ω(·) (1 - α₀ 1)` is UCP. We
  have `β α a - a = (β α₀ a - a) + ω(a) β(1 - α₀ 1)`, and the incoming defect
  `‖β(1 - α₀ 1)‖` is at most `δ`. Hence `‖β α a - a‖ ≤ δ (1 + ‖a‖)` on `S`.
* `norm_mul_defect_le_of_approx`. This is the elementary estimate for the
  multiplicative defect: `w - u v = (w - ab) - (u - a) b - u (v - b)`, together
  with `‖u‖ ≤ 1 + 2C`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace RelatedBK

open GroupApproximation.CStarExactness

universe u

noncomputable section

/-- **Unital nuclear approximations.** A nontrivial unital nuclear C-star algebra
has UCP maps `α` into a nontrivial finite-dimensional C-star algebra and
completely positive contractions `β` back, with `‖β (α a) - a‖ ≤ δ (1 + ‖a‖)`
on a prescribed finite set. -/
theorem exists_ucp_cpc_finiteDimensional_approximation
    {A : Type u} [CStarAlgebra A] [Nontrivial A]
    (hnuc : IsNuclearCStarAlgebra A) (S : Finset A) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ (D : FinDimCStarAlgebra) (_hD : Nontrivial D)
      (α : A →ₗ[ℂ] D) (β : D →ₗ[ℂ] A),
      IsCompletelyPositive α ∧ α 1 = 1 ∧
        IsCompletelyPositive β ∧ (∀ d : D, ‖β d‖ ≤ ‖d‖) ∧
          ∀ a ∈ S, ‖β (α a) - a‖ ≤ δ * (1 + ‖a‖) := by
  classical
  obtain ⟨D, α₀, β, hα₀CP, hβCP, hα₀Contract, hβContract, hrec⟩ :=
    hnuc (insert 1 S) δ hδ
  have hunit : ‖β (α₀ 1) - 1‖ ≤ δ := hrec 1 (Finset.mem_insert_self 1 S)
  have hD : Nontrivial D := by
    by_contra hnt
    have : Subsingleton D := not_nontrivial_iff_subsingleton.mp hnt
    have hzero : α₀ (1 : A) = 0 := Subsingleton.elim _ _
    have h1 : ‖β (α₀ 1) - 1‖ ≤ δ := hunit
    rw [hzero, map_zero, zero_sub, norm_neg, norm_one] at h1
    linarith
  let ω : CStarState.State A :=
    (CStarState.State.exists_star_mul_self (1 : A)).choose
  have hU : IsCompletelyPositive (additiveUnitalization α₀ ω) ∧
      additiveUnitalization α₀ ω 1 = 1 :=
    additiveUnitalization_completelyPositive_unital α₀ ω hα₀CP hα₀Contract
  have hincoming : ‖β ((1 : D) - α₀ 1)‖ ≤ δ :=
    norm_second_incoming_unit_defect_le_of_cp_contractions
      α₀ β hα₀CP hβCP hα₀Contract hβContract hunit
  refine ⟨D, hD, additiveUnitalization α₀ ω, β, hU.1, hU.2, hβCP,
    hβContract, ?_⟩
  intro a ha
  have happrox : ‖β (α₀ a) - a‖ ≤ δ :=
    hrec a (Finset.mem_insert_of_mem ha)
  have hω : ‖ω.toCLM a‖ ≤ ‖a‖ := by
    calc
      ‖ω.toCLM a‖ ≤ ‖ω.toCLM‖ * ‖a‖ := ω.toCLM.le_opNorm a
      _ ≤ 1 * ‖a‖ := mul_le_mul_of_nonneg_right ω.norm_le (norm_nonneg a)
      _ = ‖a‖ := one_mul _
  have hexpand : β (additiveUnitalization α₀ ω a) - a =
      (β (α₀ a) - a) + ω.toCLM a • β ((1 : D) - α₀ 1) := by
    rw [additiveUnitalization_apply, map_add, map_smul]
    abel
  rw [hexpand]
  calc
    ‖(β (α₀ a) - a) + ω.toCLM a • β ((1 : D) - α₀ 1)‖ ≤
        ‖β (α₀ a) - a‖ + ‖ω.toCLM a • β ((1 : D) - α₀ 1)‖ :=
      norm_add_le _ _
    _ = ‖β (α₀ a) - a‖ + ‖ω.toCLM a‖ * ‖β ((1 : D) - α₀ 1)‖ := by
      rw [norm_smul]
    _ ≤ δ + ‖a‖ * δ :=
      add_le_add happrox
        (mul_le_mul hω hincoming (norm_nonneg _) (norm_nonneg a))
    _ = δ * (1 + ‖a‖) := by ring

/-- **Multiplicative defect of approximants.** Suppose `u, v, w` approximate
`a, b, ab` within `δ (1 + C)`, `δ (1 + C)` and `δ (1 + C²)`, where
`‖a‖, ‖b‖ ≤ C` and `δ ≤ 1`. Then `‖w - u v‖ ≤ 4 (1 + C)² δ`. -/
theorem norm_mul_defect_le_of_approx {A : Type u} [NormedRing A]
    (a b u v w : A) {δ C : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hC : 0 ≤ C)
    (ha : ‖a‖ ≤ C) (hb : ‖b‖ ≤ C)
    (hu : ‖u - a‖ ≤ δ * (1 + C)) (hv : ‖v - b‖ ≤ δ * (1 + C))
    (hw : ‖w - a * b‖ ≤ δ * (1 + C * C)) :
    ‖w - u * v‖ ≤ 4 * (1 + C) ^ 2 * δ := by
  have hsplit : w - u * v = (w - a * b) - (u - a) * b - u * (v - b) := by
    simp only [mul_sub, sub_mul]
    abel
  have hδC : δ * (1 + C) ≤ 1 + C := mul_le_of_le_one_left (by linarith) hδ1
  have hunorm : ‖u‖ ≤ 1 + 2 * C := by
    have h := norm_sub_norm_le u a
    linarith
  have h1 : ‖(u - a) * b‖ ≤ δ * (1 + C) * C :=
    (norm_mul_le _ _).trans
      (mul_le_mul hu hb (norm_nonneg _) (mul_nonneg hδ (by linarith)))
  have h2 : ‖u * (v - b)‖ ≤ (1 + 2 * C) * (δ * (1 + C)) :=
    (norm_mul_le _ _).trans
      (mul_le_mul hunorm hv (norm_nonneg _) (by linarith))
  have h3 := norm_sub_le ((w - a * b) - (u - a) * b) (u * (v - b))
  have h4 := norm_sub_le (w - a * b) ((u - a) * b)
  rw [hsplit]
  nlinarith [mul_nonneg hδ hC, mul_nonneg (mul_nonneg hδ hC) hC]

end

end RelatedBK
end NonMF
end Manuscript
end GroupApproximation

open GroupApproximation.Manuscript.NonMF.RelatedBK

#audit_axioms exists_ucp_cpc_finiteDimensional_approximation
#audit_axioms norm_mul_defect_le_of_approx
