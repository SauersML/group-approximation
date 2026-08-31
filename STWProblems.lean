import Mathlib
import GroupApproximation.Manuscript.NinetyNineProblems.ProblemXCVCompactKTheory

/-!
# STW Problems XXII, LV, and XCV: unconditional kernel cores

This file records the parts of the three operator-algebra arguments that can
currently be stated and proved in Lean without introducing any new axiom,
`sorry`, `admit`, or placeholder theorem.

The surrounding operator-algebraic infrastructure is intentionally not
postulated here.  In particular, Mathlib currently has no API for the Cuntz
semigroup or operator K-theory used in Problem XCV, no crossed-product/KMS
formalization sufficient for Problem LV, and no factorial tracially complete
C*-bundle plus Michael-selection formalization sufficient for Problem XXII.
Encoding those missing results as hypotheses would make the claimed solutions
conditional rather than unconditional.

What is checked here is therefore the exact terminal mathematics used by the
three arguments:

* XXII: an unbounded family of replication inequalities
  `m * sigma(b) <= C` forces the nonnegative trace value `sigma(b)` to vanish;
* LV: the quasifree KMS equation has at most one inverse temperature for each
  positive parameter, and a common inverse temperature determines the
  parameter uniquely;
* XCV: the compact K-theory endpoint `Z !~= Z x Z`, re-exported from the
  existing axiom-free module.
-/

namespace GroupApproximation.NinetyNineProblems

namespace ProblemXXII

/-- The scalar endpoint of the orthogonal-replication argument.

If a nonnegative number `x` admits arbitrarily large natural-number
replications while all replicated masses stay bounded by one fixed `C`, then
`x = 0`.  In the trace argument, `x` is the value of a singular trace on a
spectral cut and `C` is the norm of that trace. -/
theorem zero_of_unbounded_replication {x C : ℝ} (hx : 0 ≤ x)
    (h : ∀ N : ℕ, ∃ m : ℕ, N ≤ m ∧ (m : ℝ) * x ≤ C) : x = 0 := by
  by_contra hx0
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, C / x < N := exists_nat_gt (C / x)
  obtain ⟨m, hmN, hbound⟩ := h N
  have hNm : (N : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hmN
  have hratio : C / x < (m : ℝ) := lt_of_lt_of_le hN hNm
  have hcontra : C < (m : ℝ) * x := (div_lt_iff₀ hxpos).mp hratio
  exact (not_lt_of_ge hbound) hcontra

/-- A cofinite tail of replication numbers is already enough for the trace
cut to vanish.  This is the quantifier shape used in the finite-dimensional
bundle argument, where stable range starts only after a dimension-dependent
threshold. -/
theorem zero_of_cofinite_replication {x C : ℝ} (hx : 0 ≤ x) (m0 : ℕ)
    (h : ∀ m : ℕ, m0 ≤ m → (m : ℝ) * x ≤ C) : x = 0 := by
  apply zero_of_unbounded_replication hx
  intro N
  refine ⟨max N m0, le_max_left _ _, ?_⟩
  exact h (max N m0) (le_max_right _ _)

end ProblemXXII

namespace ProblemLV

/-- The normalized quasifree KMS equation for the parameter `lambda` and
inverse temperature `beta`. -/
def KMSEquation (lambda beta : ℝ) : Prop :=
  Real.exp (-beta) + Real.exp (-(lambda * beta)) = 1

/-- Any solution of the normalized KMS equation has nonzero inverse
temperature. -/
theorem beta_ne_zero_of_kmsEquation {lambda beta : ℝ}
    (h : KMSEquation lambda beta) : beta ≠ 0 := by
  intro hbeta
  subst beta
  norm_num [KMSEquation] at h

/-- For every positive quasifree parameter, the normalized KMS equation has at
most one inverse temperature. -/
theorem kmsEquation_unique_beta {lambda beta gamma : ℝ} (hlambda : 0 < lambda)
    (hbeta : KMSEquation lambda beta) (hgamma : KMSEquation lambda gamma) :
    beta = gamma := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hfirst : Real.exp (-gamma) < Real.exp (-beta) := by
      exact Real.exp_lt_exp.mpr (by linarith)
    have hmul : lambda * beta < lambda * gamma :=
      mul_lt_mul_of_pos_left hlt hlambda
    have hsecond : Real.exp (-(lambda * gamma)) < Real.exp (-(lambda * beta)) := by
      exact Real.exp_lt_exp.mpr (by linarith)
    dsimp [KMSEquation] at hbeta hgamma
    linarith
  · have hfirst : Real.exp (-beta) < Real.exp (-gamma) := by
      exact Real.exp_lt_exp.mpr (by linarith)
    have hmul : lambda * gamma < lambda * beta :=
      mul_lt_mul_of_pos_left hgt hlambda
    have hsecond : Real.exp (-(lambda * beta)) < Real.exp (-(lambda * gamma)) := by
      exact Real.exp_lt_exp.mpr (by linarith)
    dsimp [KMSEquation] at hbeta hgamma
    linarith

/-- A common normalized KMS inverse temperature determines the quasifree
parameter uniquely.  This is the analytic separation step used after cocycle
conjugacy identifies the dual trace-scaling exponent. -/
theorem parameter_eq_of_common_kms_beta {lambda mu beta : ℝ}
    (hlambda : KMSEquation lambda beta) (hmu : KMSEquation mu beta) :
    lambda = mu := by
  have hbeta0 : beta ≠ 0 := beta_ne_zero_of_kmsEquation hlambda
  have hexp : Real.exp (-(lambda * beta)) = Real.exp (-(mu * beta)) := by
    dsimp [KMSEquation] at hlambda hmu
    linarith
  have harg : -(lambda * beta) = -(mu * beta) := Real.exp_injective hexp
  have hprod : lambda * beta = mu * beta := by
    linarith
  exact mul_right_cancel₀ hbeta0 hprod

end ProblemLV

namespace ProblemXCV

/-- Re-export of the existing unconditional compact-K-theory contradiction
for the XCV counterexample. -/
theorem compact_k0_rank_obstruction : ¬ Nonempty (ℤ ≃+ ℤ × ℤ) :=
  ProblemXCV.int_not_addEquiv_int_prod_int

end ProblemXCV

end GroupApproximation.NinetyNineProblems
