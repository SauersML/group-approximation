import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Tactic
import GroupApproximation.Meta.AxiomGuard

/-!
# The Halmos dilation used in Shulman's commutant-unitary correction

This file isolates the algebraic and continuous-functional-calculus part of
Shulman's Lemma 9.  A contraction `x` determines the Halmos matrix

`[[x, sqrt (1 - x x* )], [sqrt (1 - x* x), -x*]]`.

We prove that this matrix is unitary and compute its commutator with a scalar
two-by-two block.  No quotient, approximate-unit, or quantitative square-root
commutator theorem is assumed here.
-/

namespace GroupApproximation
namespace ShulmanHalmosDilation

open scoped CStarAlgebra

noncomputable section

universe u

variable {A : Type u} [CStarAlgebra A]

noncomputable local instance : PartialOrder A := CStarAlgebra.spectralOrder A
noncomputable local instance : StarOrderedRing A :=
  CStarAlgebra.spectralOrderedRing A

abbrev Mat₂ (A : Type u) := CStarMatrix (Fin 2) (Fin 2) A

noncomputable local instance matComplexCFC [Nontrivial A] :
    ContinuousFunctionalCalculus ℂ (Mat₂ A) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus

noncomputable local instance matRealCFC [Nontrivial A] :
    ContinuousFunctionalCalculus ℝ (Mat₂ A) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

noncomputable local instance matPartialOrder [Nontrivial A] :
    PartialOrder (Mat₂ A) := CStarAlgebra.spectralOrder (Mat₂ A)

noncomputable local instance matStarOrderedRing [Nontrivial A] :
    StarOrderedRing (Mat₂ A) := CStarAlgebra.spectralOrderedRing (Mat₂ A)

noncomputable local instance matNonnegSpectrum [Nontrivial A] :
    NonnegSpectrumClass ℝ (Mat₂ A) :=
  CStarAlgebra.instNonnegSpectrumClass

/-- A two-by-two diagonal matrix over a C-star algebra. -/
def diag₂ (a b : A) : Mat₂ A :=
  CStarMatrix.ofMatrix !![a, 0; 0, b]

/-- A selfadjoint off-diagonal matrix associated to an element. -/
def selfAdjointOffDiag (x : A) : Mat₂ A :=
  CStarMatrix.ofMatrix !![0, x; star x, 0]

/-- The left defect of a contraction. -/
def leftDefect (x : A) : A := CFC.sqrt (1 - x * star x)

/-- The right defect of a contraction. -/
def rightDefect (x : A) : A := CFC.sqrt (1 - star x * x)

/-- The Halmos two-by-two dilation of a contraction. -/
def halmos (x : A) : Mat₂ A :=
  CStarMatrix.ofMatrix !![x, leftDefect x; rightDefect x, -star x]

theorem mul_star_self_nonneg (x : A) : 0 ≤ x * star x := by
  simpa only [star_star] using star_mul_self_nonneg (star x)

theorem left_defect_argument_nonneg {x : A} (hx : ‖x‖ ≤ 1) :
    0 ≤ 1 - x * star x := by
  rw [sub_nonneg]
  apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ (mul_star_self_nonneg x)).mp
  calc
    ‖x * star x‖ = ‖star x‖ * ‖star x‖ := by
      simpa only [star_star] using CStarRing.norm_star_mul_self (x := star x)
    _ = ‖x‖ * ‖x‖ := by rw [norm_star]
    _ ≤ 1 * 1 := mul_le_mul hx hx (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem right_defect_argument_nonneg {x : A} (hx : ‖x‖ ≤ 1) :
    0 ≤ 1 - star x * x := by
  rw [sub_nonneg]
  apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ (star_mul_self_nonneg x)).mp
  calc
    ‖star x * x‖ = ‖x‖ * ‖x‖ := CStarRing.norm_star_mul_self
    _ ≤ 1 * 1 := mul_le_mul hx hx (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem diag₂_nonneg {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ diag₂ a b := by
  let R : Mat₂ A := diag₂ (CFC.sqrt a) (CFC.sqrt b)
  have hfactor : diag₂ a b = star R * R := by
    apply CStarMatrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [R, diag₂, CStarMatrix.star_eq_conjTranspose,
        CStarMatrix.mul_apply, Fin.sum_univ_two,
        (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg a)).star_eq,
        (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg b)).star_eq,
        CFC.sqrt_mul_sqrt_self a ha, CFC.sqrt_mul_sqrt_self b hb]
  rw [hfactor]
  exact star_mul_self_nonneg R

/-- The square of the selfadjoint off-diagonal matrix is the diagonal of the
two Gram elements. -/
theorem selfAdjointOffDiag_sq (x : A) :
    selfAdjointOffDiag x * selfAdjointOffDiag x =
      diag₂ (x * star x) (star x * x) := by
  apply CStarMatrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [selfAdjointOffDiag, diag₂, CStarMatrix.mul_apply,
      Fin.sum_univ_two]

theorem selfAdjointOffDiag_isSelfAdjoint (x : A) :
    IsSelfAdjoint (selfAdjointOffDiag x) := by
  rw [IsSelfAdjoint]
  apply CStarMatrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [selfAdjointOffDiag, CStarMatrix.star_eq_conjTranspose]

/-- The diagonal defect matrix is the positive square root of
`1 - selfAdjointOffDiag(x)^2`.  This matrix-level CFC argument supplies the
otherwise nontrivial pull-through identity between the two defect roots. -/
theorem sqrt_one_sub_selfAdjointOffDiag_sq [Nontrivial A] {x : A} (hx : ‖x‖ ≤ 1) :
    CFC.sqrt
        (1 - selfAdjointOffDiag x * selfAdjointOffDiag x) =
      diag₂ (leftDefect x) (rightDefect x) := by
  let T : Mat₂ A := selfAdjointOffDiag x
  let p : Mat₂ A := 1 - T * T
  let D : Mat₂ A := diag₂ (leftDefect x) (rightDefect x)
  have hpShape : p = diag₂ (1 - x * star x) (1 - star x * x) := by
    dsimp [p, T]
    rw [selfAdjointOffDiag_sq]
    apply CStarMatrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [diag₂]
  have hp : 0 ≤ p := by
    rw [hpShape]
    exact diag₂_nonneg (left_defect_argument_nonneg hx)
      (right_defect_argument_nonneg hx)
  have hD : 0 ≤ D := by
    exact diag₂_nonneg (CFC.sqrt_nonneg _) (CFC.sqrt_nonneg _)
  have hDsquare : D * D = p := by
    rw [hpShape]
    apply CStarMatrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [D, diag₂, leftDefect, rightDefect, CStarMatrix.mul_apply,
        Fin.sum_univ_two, CFC.sqrt_mul_sqrt_self,
        left_defect_argument_nonneg hx, right_defect_argument_nonneg hx]
  change CFC.sqrt p = D
  exact (CFC.sqrt_eq_iff p D hp hD).2 hDsquare

/-- The two defect square roots satisfy the Halmos pull-through identity. -/
theorem leftDefect_mul_eq_mul_rightDefect [Nontrivial A] {x : A} (hx : ‖x‖ ≤ 1) :
    leftDefect x * x = x * rightDefect x := by
  let T : Mat₂ A := selfAdjointOffDiag x
  let p : Mat₂ A := 1 - T * T
  let D : Mat₂ A := diag₂ (leftDefect x) (rightDefect x)
  have hpcomm : Commute p T := by
    rw [commute_iff_eq]
    dsimp [p]
    noncomm_ring
  have hsqrtcomm : Commute (CFC.sqrt p) T := by
    exact hpcomm.cfcₙ_nnreal NNReal.sqrt
  have hsqrt : CFC.sqrt p = D := by
    exact sqrt_one_sub_selfAdjointOffDiag_sq hx
  rw [hsqrt] at hsqrtcomm
  have hentry := congrArg (fun M : Mat₂ A => M 0 1) hsqrtcomm.eq
  simpa [D, T, diag₂, selfAdjointOffDiag, CStarMatrix.mul_apply,
    Fin.sum_univ_two] using hentry

/-- The adjoint pull-through identity. -/
theorem star_mul_leftDefect_eq_rightDefect_mul_star [Nontrivial A]
    {x : A} (hx : ‖x‖ ≤ 1) :
    star x * leftDefect x = rightDefect x * star x := by
  have h := congrArg star (leftDefect_mul_eq_mul_rightDefect hx)
  have hleftStar : star (leftDefect x) = leftDefect x :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)).star_eq
  have hrightStar : star (rightDefect x) = rightDefect x :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)).star_eq
  rw [star_mul, star_mul, hleftStar, hrightStar] at h
  exact h

theorem leftDefect_mul_self {x : A} (hx : ‖x‖ ≤ 1) :
    leftDefect x * leftDefect x = 1 - x * star x := by
  exact CFC.sqrt_mul_sqrt_self _ (left_defect_argument_nonneg hx)

theorem rightDefect_mul_self {x : A} (hx : ‖x‖ ≤ 1) :
    rightDefect x * rightDefect x = 1 - star x * x := by
  exact CFC.sqrt_mul_sqrt_self _ (right_defect_argument_nonneg hx)

theorem star_leftDefect {x : A} : star (leftDefect x) = leftDefect x :=
  (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)).star_eq

theorem star_rightDefect {x : A} : star (rightDefect x) = rightDefect x :=
  (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)).star_eq

/-- Multiplying the Halmos matrix by its adjoint gives the identity. -/
theorem halmos_mul_star [Nontrivial A] {x : A} (hx : ‖x‖ ≤ 1) :
    halmos x * star (halmos x) = 1 := by
  have hpull := leftDefect_mul_eq_mul_rightDefect hx
  have hpullStar := star_mul_leftDefect_eq_rightDefect_mul_star hx
  have hleftSq := leftDefect_mul_self hx
  have hrightSq := rightDefect_mul_self hx
  apply CStarMatrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [halmos, CStarMatrix.star_eq_conjTranspose,
      CStarMatrix.mul_apply, Fin.sum_univ_two, star_leftDefect,
      star_rightDefect, hleftSq, hrightSq, hpull, hpullStar]

/-- Multiplying the adjoint of the Halmos matrix by the matrix also gives the
identity. -/
theorem star_halmos_mul [Nontrivial A] {x : A} (hx : ‖x‖ ≤ 1) :
    star (halmos x) * halmos x = 1 := by
  have hpull := leftDefect_mul_eq_mul_rightDefect hx
  have hpullStar := star_mul_leftDefect_eq_rightDefect_mul_star hx
  have hleftSq := leftDefect_mul_self hx
  have hrightSq := rightDefect_mul_self hx
  apply CStarMatrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [halmos, CStarMatrix.star_eq_conjTranspose,
      CStarMatrix.mul_apply, Fin.sum_univ_two, star_leftDefect,
      star_rightDefect, hleftSq, hrightSq, hpull, hpullStar]

/-- The Halmos dilation of a contraction is a genuine unitary. -/
theorem halmos_mem_unitary [Nontrivial A] {x : A} (hx : ‖x‖ ≤ 1) :
    halmos x ∈ unitary (Mat₂ A) :=
  Unitary.mem_iff.2 ⟨star_halmos_mul hx, halmos_mul_star hx⟩

/-- The bundled Halmos unitary of a contraction. -/
def halmosUnitary [Nontrivial A] (x : A) (hx : ‖x‖ ≤ 1) : unitary (Mat₂ A) :=
  ⟨halmos x, halmos_mem_unitary hx⟩

@[simp] theorem coe_halmosUnitary [Nontrivial A] (x : A) (hx : ‖x‖ ≤ 1) :
    ((halmosUnitary x hx : unitary (Mat₂ A)) : Mat₂ A) = halmos x :=
  rfl

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

/-- Closed endpoint: the Halmos matrix of every contraction is unitary, and
its repeated-block commutator is controlled by the four displayed coordinate
commutators. -/
def HalmosDilationAndBlockCommutatorControl : Prop :=
  ∀ (A : Type u) [CStarAlgebra A] [Nontrivial A] (x a : A),
    ‖x‖ ≤ 1 →
    halmos x ∈ unitary (Mat₂ A) ∧
    ‖halmos x * diag₂ a a - diag₂ a a * halmos x‖ ≤
      ‖x * a - a * x‖ +
      ‖leftDefect x * a - a * leftDefect x‖ +
      ‖rightDefect x * a - a * rightDefect x‖ +
      ‖(-star x) * a - a * (-star x)‖

theorem halmosDilationAndBlockCommutatorControl :
    HalmosDilationAndBlockCommutatorControl := by
  intro A _ _ x a hx
  exact ⟨halmos_mem_unitary hx, norm_halmos_commutator_diag₂_le x a⟩

end

end ShulmanHalmosDilation
end GroupApproximation

#audit_closed_axioms GroupApproximation.ShulmanHalmosDilation.halmosDilationAndBlockCommutatorControl
