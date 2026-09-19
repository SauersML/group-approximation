import GroupApproximation.Analysis.LanceCPApprox
import GroupApproximation.Analysis.CStarTakesakiDense
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# Unit-defect control for completely positive contractions

The completely positive approximation property in `CStarExactness` supplies
contractive maps, whereas the Lance route consumes unital maps.  The standard
unitalization starts from the positive defects

```text
  1 - alpha(1),       1 - beta(1).
```

This file proves that positivity and the quantitative estimate which makes the
repair usable.  If `beta (alpha 1)` is within `delta` of `1`, then both the
outgoing defect `1 - beta 1` and the image `beta (1 - alpha 1)` of the incoming
defect have norm at most `delta`.

No finite-dimensional structure is used here.  The remaining step is to add
state-valued rank-one completely positive corrections and then transport the
finite-dimensional algebra through its Wedderburn decomposition.
-/

namespace GroupApproximation
namespace CStarExactness

universe u v w

noncomputable section

open scoped ComplexOrder InnerProductSpace

/-! ## State-valued positive rank-one maps -/

/-- A state, multiplied by a fixed target element. -/
def stateSmulLinearMap
    {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]
    (omega : CStarState.State A) (b : B) : A →ₗ[ℂ] B where
  toFun a := omega.toCLM a • b
  map_add' a c := by rw [map_add, add_smul]
  map_smul' z a := by
    simp only [map_smul, smul_smul, RingHom.id_apply, smul_eq_mul]

@[simp] theorem stateSmulLinearMap_apply
    {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]
    (omega : CStarState.State A) (b : B) (a : A) :
    stateSmulLinearMap omega b a = omega.toCLM a • b := rfl

open scoped MatrixOrder Matrix.Norms.L2Operator in
/-- A finite Gram matrix has a square factor in the ordinary complex matrix
algebra.  Keeping the matrix-order scope inside this declaration prevents it
from competing with the `CStarMatrix` instances in complete-positivity proofs. -/
theorem exists_matrix_star_mul_self_eq_gram
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {n : ℕ} (v : Fin n → H) :
  ∃ Q : Matrix (Fin n) (Fin n) ℂ, Matrix.gram ℂ v = star Q * Q := by
  have hnonneg : 0 ≤ Matrix.gram ℂ v := (Matrix.posSemidef_gram ℂ v).nonneg
  exact CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hnonneg

/-- A positive element multiplied by a state gives a completely positive map. -/
theorem isCompletelyPositive_stateSmulLinearMap
    {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]
    [Nontrivial A]
    (omega : CStarState.State A) {b : B}
    (hb : ∃ c : B, b = star c * c) :
    IsCompletelyPositive (stateSmulLinearMap omega b) := by
  intro n M hM
  obtain ⟨N, rfl⟩ := hM
  obtain ⟨c, rfl⟩ := hb
  let v : Fin n → PiLp 2 (fun _ : Fin n ↦ omega.GNSSpace) := fun i ↦
    WithLp.toLp 2 (fun r ↦ (omega.gnsRep).hom (N r i) omega.gnsVector)
  let S : Matrix (Fin n) (Fin n) ℂ := Matrix.gram ℂ v
  have hSentry : ∀ i j : Fin n,
      S i j = ∑ r : Fin n, omega.toCLM (star (N r i) * N r j) := by
    intro i j
    rw [show S i j = ⟪v i, v j⟫_ℂ from rfl, PiLp.inner_apply]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    change ⟪(omega.gnsRep).hom (N r i) omega.gnsVector,
        (omega.gnsRep).hom (N r j) omega.gnsVector⟫_ℂ = _
    calc
      ⟪(omega.gnsRep).hom (N r i) omega.gnsVector,
          (omega.gnsRep).hom (N r j) omega.gnsVector⟫_ℂ =
          ⟪omega.gnsVector,
            (omega.gnsRep).hom (star (N r i))
              ((omega.gnsRep).hom (N r j) omega.gnsVector)⟫_ℂ := by
            exact (omega.gnsRep).isAdjoint_star (N r i) _ _
      _ = ⟪omega.gnsVector,
            (omega.gnsRep).hom (star (N r i) * N r j)
              omega.gnsVector⟫_ℂ := by
            rw [map_mul]
            rfl
      _ = omega.toCLM (star (N r i) * N r j) :=
        CStarTensor.inner_gnsVector_gnsRep omega _
  obtain ⟨Q, hQ⟩ := exists_matrix_star_mul_self_eq_gram v
  let P : CStarMatrix (Fin n) (Fin n) B := fun i j ↦ Q i j • c
  refine ⟨P, ?_⟩
  ext i j
  have hNentry : (star N * N) i j =
      ∑ r : Fin n, star (N r i) * N r j := by
    rw [cstarMatrix_mul_apply]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    rw [cstarMatrix_star_apply]
  have hQentry : S i j = ∑ r : Fin n, star (Q r i) * Q r j := by
    change Matrix.gram ℂ v i j = _
    rw [hQ, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    rfl
  calc
    ((star N * N).map ⇑(stateSmulLinearMap omega (star c * c))) i j =
        omega.toCLM ((star N * N) i j) • (star c * c) := rfl
    _ = (∑ r : Fin n, omega.toCLM (star (N r i) * N r j)) •
        (star c * c) := by rw [hNentry, map_sum]
    _ = S i j • (star c * c) := by rw [hSentry]
    _ = (∑ r : Fin n, star (Q r i) * Q r j) • (star c * c) := by
      rw [← hQentry]
    _ = ∑ r : Fin n,
        (star (Q r i) * Q r j) • (star c * c) := Finset.sum_smul
    _ = ∑ r : Fin n, star (P r i) * P r j := by
      refine Finset.sum_congr rfl fun r _ ↦ ?_
      change (star (Q r i) * Q r j) • (star c * c) =
        (star (Q r i • c)) * (Q r j • c)
      rw [star_smul, smul_mul_smul]
    _ = (star P * P) i j := by
      rw [cstarMatrix_mul_apply]
      exact (Finset.sum_congr rfl fun r _ ↦ by rw [cstarMatrix_star_apply]).symm

/-- The unit defect of a completely positive contraction is positive. -/
theorem one_sub_map_one_nonneg_of_completelyPositive_contractive
    {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]
    [PartialOrder A] [StarOrderedRing A]
    [PartialOrder B] [StarOrderedRing B]
    (phi : A →ₗ[ℂ] B) (hphi : IsCompletelyPositive phi)
    (hcontract : ∀ a : A, ‖phi a‖ ≤ ‖a‖) :
    0 ≤ (1 : B) - phi 1 := by
  have hpos : 0 ≤ phi (1 : A) :=
    map_nonneg_of_completelyPositive hphi (show 0 ≤ (1 : A) from zero_le_one)
  have hnorm : ‖phi (1 : A)‖ ≤ 1 := by
    have honeSq : ‖(1 : A)‖ = ‖(1 : A)‖ ^ 2 := by
      have honeCstar : ‖star (1 : A) * (1 : A)‖ =
          ‖(1 : A)‖ * ‖(1 : A)‖ := CStarRing.norm_star_mul_self
      simpa [sq] using honeCstar
    have honeLe : ‖(1 : A)‖ ≤ 1 := by
      nlinarith [norm_nonneg (1 : A)]
    calc
      ‖phi (1 : A)‖ ≤ ‖(1 : A)‖ := hcontract (1 : A)
      _ ≤ 1 := honeLe
  exact sub_nonneg.mpr
    ((CStarAlgebra.norm_le_one_iff_of_nonneg (phi (1 : A)) hpos).mp hnorm)

/-- Approximation at the unit controls the outgoing unit defect. -/
theorem norm_one_sub_second_one_le_of_cp_contractions
    {A : Type u} {D : Type v} {B : Type w}
    [CStarAlgebra A] [CStarAlgebra D] [CStarAlgebra B]
    (alpha : A →ₗ[ℂ] D) (beta : D →ₗ[ℂ] B)
    (halpha : IsCompletelyPositive alpha)
    (hbeta : IsCompletelyPositive beta)
    (halphaContract : ∀ a : A, ‖alpha a‖ ≤ ‖a‖)
    (hbetaContract : ∀ d : D, ‖beta d‖ ≤ ‖d‖)
    {delta : ℝ} (hunit : ‖beta (alpha 1) - 1‖ ≤ delta) :
    ‖1 - beta 1‖ ≤ delta := by
  letI : PartialOrder A := CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  letI : PartialOrder D := CStarAlgebra.spectralOrder D
  letI : StarOrderedRing D := CStarAlgebra.spectralOrderedRing D
  letI : PartialOrder B := CStarAlgebra.spectralOrder B
  letI : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  have hAlphaDefect : 0 ≤ (1 : D) - alpha 1 :=
    one_sub_map_one_nonneg_of_completelyPositive_contractive
      alpha halpha halphaContract
  have hBetaDefect : 0 ≤ (1 : B) - beta 1 :=
    one_sub_map_one_nonneg_of_completelyPositive_contractive
      beta hbeta hbetaContract
  have hImageDefect : 0 ≤ beta ((1 : D) - alpha 1) :=
    map_nonneg_of_completelyPositive hbeta hAlphaDefect
  have hsplit : beta ((1 : D) - alpha 1) = beta 1 - beta (alpha 1) := by
    rw [map_sub]
  have hle : (1 : B) - beta 1 ≤ 1 - beta (alpha 1) := by
    rw [sub_le_sub_iff_left]
    rw [← sub_nonneg, ← hsplit]
    exact hImageDefect
  have hnorm := CStarAlgebra.norm_le_norm_of_nonneg_of_le hBetaDefect hle
  calc
    ‖1 - beta 1‖ ≤ ‖1 - beta (alpha 1)‖ := hnorm
    _ = ‖beta (alpha 1) - 1‖ := by rw [← norm_neg, neg_sub]
    _ ≤ delta := hunit

/-- Approximation at the unit controls the image of the incoming unit defect. -/
theorem norm_second_incoming_unit_defect_le_of_cp_contractions
    {A : Type u} {D : Type v} {B : Type w}
    [CStarAlgebra A] [CStarAlgebra D] [CStarAlgebra B]
    (alpha : A →ₗ[ℂ] D) (beta : D →ₗ[ℂ] B)
    (halpha : IsCompletelyPositive alpha)
    (hbeta : IsCompletelyPositive beta)
    (halphaContract : ∀ a : A, ‖alpha a‖ ≤ ‖a‖)
    (hbetaContract : ∀ d : D, ‖beta d‖ ≤ ‖d‖)
    {delta : ℝ} (hunit : ‖beta (alpha 1) - 1‖ ≤ delta) :
    ‖beta ((1 : D) - alpha 1)‖ ≤ delta := by
  letI : PartialOrder A := CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  letI : PartialOrder D := CStarAlgebra.spectralOrder D
  letI : StarOrderedRing D := CStarAlgebra.spectralOrderedRing D
  letI : PartialOrder B := CStarAlgebra.spectralOrder B
  letI : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  have hAlphaDefect : 0 ≤ (1 : D) - alpha 1 :=
    one_sub_map_one_nonneg_of_completelyPositive_contractive
      alpha halpha halphaContract
  have hImageDefect : 0 ≤ beta ((1 : D) - alpha 1) :=
    map_nonneg_of_completelyPositive hbeta hAlphaDefect
  have hBetaDefect : 0 ≤ (1 : B) - beta 1 :=
    one_sub_map_one_nonneg_of_completelyPositive_contractive
      beta hbeta hbetaContract
  have hsplit : beta ((1 : D) - alpha 1) = beta 1 - beta (alpha 1) := by
    rw [map_sub]
  have hle : beta ((1 : D) - alpha 1) ≤ 1 - beta (alpha 1) := by
    rw [hsplit]
    exact sub_le_sub_right (sub_nonneg.mp hBetaDefect) _
  have hnorm := CStarAlgebra.norm_le_norm_of_nonneg_of_le hImageDefect hle
  calc
    ‖beta ((1 : D) - alpha 1)‖ ≤ ‖1 - beta (alpha 1)‖ := hnorm
    _ = ‖beta (alpha 1) - 1‖ := by rw [← norm_neg, neg_sub]
    _ ≤ delta := hunit

end

end CStarExactness
end GroupApproximation

open GroupApproximation.CStarExactness

#audit_axioms one_sub_map_one_nonneg_of_completelyPositive_contractive
#audit_axioms norm_one_sub_second_one_le_of_cp_contractions
#audit_axioms norm_second_incoming_unit_defect_le_of_cp_contractions
#audit_axioms exists_matrix_star_mul_self_eq_gram
#audit_axioms isCompletelyPositive_stateSmulLinearMap
