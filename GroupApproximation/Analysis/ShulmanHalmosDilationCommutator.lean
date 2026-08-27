import GroupApproximation.Analysis.ShulmanHalmosDilationUnitary

/-! Block commutator formulas and estimates for the Halmos dilation. -/

namespace GroupApproximation
namespace ShulmanHalmosDilation

open scoped CStarAlgebra

noncomputable section

universe u

variable {A : Type u} [CStarAlgebra A]

noncomputable local instance : PartialOrder A := CStarAlgebra.spectralOrder A
noncomputable local instance : StarOrderedRing A :=
  CStarAlgebra.spectralOrderedRing A

noncomputable local instance [Nontrivial A] :
    ContinuousFunctionalCalculus ℂ (Mat₂ A) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus

noncomputable local instance [Nontrivial A] :
    ContinuousFunctionalCalculus ℝ (Mat₂ A) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

noncomputable local instance [Nontrivial A] :
    PartialOrder (Mat₂ A) := CStarAlgebra.spectralOrder (Mat₂ A)

noncomputable local instance [Nontrivial A] :
    StarOrderedRing (Mat₂ A) := CStarAlgebra.spectralOrderedRing (Mat₂ A)

noncomputable local instance [Nontrivial A] :
    NonnegSpectrumClass ℝ (Mat₂ A) :=
  CStarAlgebra.instNonnegSpectrumClass

/-- The commutator of the Halmos dilation with a repeated diagonal block,
entry by entry. -/
theorem halmos_commutator_diag₂ (x a : A) :
    halmos x * diag₂ a a - diag₂ a a * halmos x =
      CStarMatrix.ofMatrix
        !![x * a - a * x,
           leftDefect x * a - a * leftDefect x;
           rightDefect x * a - a * rightDefect x,
           (-star x) * a - a * (-star x)] := by
  apply CStarMatrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [halmos, diag₂, CStarMatrix.mul_apply, Fin.sum_univ_two]

/-- A two-by-two C-star matrix is bounded by the sum of the norms of its four
entries.  This intentionally crude bound is sufficient for the asymptotic
commutator argument and avoids any quantitative square-root theorem. -/
theorem norm_mat₂_le_sum_entries (M : Mat₂ A) :
    ‖M‖ ≤ ∑ j : Fin 2, ∑ i : Fin 2, ‖M i j‖ := by
  rw [CStarMatrix.norm_def]
  refine (CStarMatrix.toCLM M).opNorm_le_bound (by positivity) fun v ↦ ?_
  simp only [CStarMatrix.toCLM_apply_eq_sum, Finset.sum_mul]
  apply WithCStarModule.pi_norm_le_sum_norm _ |>.trans
  gcongr with i _
  change ‖∑ j, v j * M j i‖ ≤ _
  apply norm_sum_le _ _ |>.trans
  gcongr with j _
  apply norm_mul_le _ _ |>.trans
  rw [mul_comm]
  gcongr
  exact WithCStarModule.norm_apply_le_norm v j

/-- The block commutator is controlled by the four coordinate commutators. -/
theorem norm_halmos_commutator_diag₂_le (x a : A) :
    ‖halmos x * diag₂ a a - diag₂ a a * halmos x‖ ≤
      ‖x * a - a * x‖ +
      ‖leftDefect x * a - a * leftDefect x‖ +
      ‖rightDefect x * a - a * rightDefect x‖ +
      ‖(-star x) * a - a * (-star x)‖ := by
  rw [halmos_commutator_diag₂]
  let M : Mat₂ A :=
    CStarMatrix.ofMatrix
      !![x * a - a * x,
         leftDefect x * a - a * leftDefect x;
         rightDefect x * a - a * rightDefect x,
         (-star x) * a - a * (-star x)]
  change ‖M‖ ≤ _
  refine (norm_mat₂_le_sum_entries M).trans_eq ?_
  simp only [Fin.sum_univ_two]
  change
    ‖x * a - a * x‖ + ‖rightDefect x * a - a * rightDefect x‖ +
        (‖leftDefect x * a - a * leftDefect x‖ +
          ‖(-star x) * a - a * (-star x)‖) = _
  abel

/-- If each of the four coordinate commutators is at most one quarter of the
target tolerance, then the block commutator has the requested tolerance. -/
theorem norm_halmos_commutator_diag₂_le_of_quarter
    {x a : A} {epsilon : ℝ}
    (h₀₀ : ‖x * a - a * x‖ ≤ epsilon / 4)
    (h₀₁ : ‖leftDefect x * a - a * leftDefect x‖ ≤ epsilon / 4)
    (h₁₀ : ‖rightDefect x * a - a * rightDefect x‖ ≤ epsilon / 4)
    (h₁₁ : ‖(-star x) * a - a * (-star x)‖ ≤ epsilon / 4) :
    ‖halmos x * diag₂ a a - diag₂ a a * halmos x‖ ≤ epsilon := by
  refine (norm_halmos_commutator_diag₂_le x a).trans ?_
  linarith

end

end ShulmanHalmosDilation
end GroupApproximation
