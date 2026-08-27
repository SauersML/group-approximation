import GroupApproximation.Analysis.LanceCPApprox
import GroupApproximation.Analysis.CStarTakesakiDense
import GroupApproximation.Analysis.BlackadarKirchbergFiniteDirectSumLift
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

No finite-dimensional structure is used here.  We add state-valued rank-one
completely positive corrections and show that repairing both legs changes a
unit-ball approximation bound from `delta` to at most `4 * delta`.  Transport
of an arbitrary finite-dimensional algebra to the operator-algebra target used
by the Lance route remains a separate Wedderburn/injectivity step.
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

/-! ## Additive unitalization -/

/-- Add the state-valued unit defect to a linear map. -/
def additiveUnitalization
    {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]
    (phi : A →ₗ[ℂ] B) (omega : CStarState.State A) : A →ₗ[ℂ] B :=
  phi + stateSmulLinearMap omega (1 - phi 1)

@[simp] theorem additiveUnitalization_apply
    {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]
    (phi : A →ₗ[ℂ] B) (omega : CStarState.State A) (a : A) :
    additiveUnitalization phi omega a =
      phi a + omega.toCLM a • (1 - phi 1) := rfl

/-- **Additive UCP repair.**  A completely positive contraction becomes a
unital completely positive map after adding its unit defect, weighted by any
state of the source. -/
theorem additiveUnitalization_completelyPositive_unital
    {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]
    [Nontrivial A]
    (phi : A →ₗ[ℂ] B) (omega : CStarState.State A)
    (hphi : IsCompletelyPositive phi)
    (hcontract : ∀ a : A, ‖phi a‖ ≤ ‖a‖) :
    IsCompletelyPositive (additiveUnitalization phi omega) ∧
      additiveUnitalization phi omega 1 = 1 := by
  letI : PartialOrder A := CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  letI : PartialOrder B := CStarAlgebra.spectralOrder B
  letI : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  have hdefect : 0 ≤ (1 : B) - phi 1 :=
    one_sub_map_one_nonneg_of_completelyPositive_contractive
      phi hphi hcontract
  have hfactor : ∃ c : B, (1 : B) - phi 1 = star c * c :=
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hdefect
  refine ⟨BlackadarKirchberg.CStarExactness.IsCompletelyPositive.add hphi
      (isCompletelyPositive_stateSmulLinearMap omega hfactor), ?_⟩
  rw [additiveUnitalization_apply, omega.map_one, one_smul]
  abel

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

/-! ## Quantitative two-sided repair -/

/-- **Quantitative additive UCP repair.**  Suppose two completely positive
contractions nearly fix both the unit and a unit-ball element after
composition.  Additively unitalizing both maps with arbitrary source states
then still nearly fixes that element, with loss by a factor of at most four.

The three error terms are the original error, the image of the incoming unit
defect, and the outgoing unit defect.  The first two cost `delta`; the last
costs `2 * delta` because the repaired incoming map has norm at most two on the
unit ball. -/
theorem norm_additiveUnitalization_comp_sub_le_four_mul
    {A : Type u} {D : Type v}
    [CStarAlgebra A] [CStarAlgebra D]
    [Nontrivial A] [Nontrivial D]
    (alpha : A →ₗ[ℂ] D) (beta : D →ₗ[ℂ] A)
    (omegaA : CStarState.State A) (omegaD : CStarState.State D)
    (halpha : IsCompletelyPositive alpha)
    (hbeta : IsCompletelyPositive beta)
    (halphaContract : ∀ a : A, ‖alpha a‖ ≤ ‖a‖)
    (hbetaContract : ∀ d : D, ‖beta d‖ ≤ ‖d‖)
    {delta : ℝ} (hunit : ‖beta (alpha 1) - 1‖ ≤ delta)
    (a : A) (ha : ‖a‖ ≤ 1)
    (happrox : ‖beta (alpha a) - a‖ ≤ delta) :
    ‖additiveUnitalization beta omegaD
        (additiveUnitalization alpha omegaA a) - a‖ ≤ 4 * delta := by
  letI : PartialOrder A := CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  letI : PartialOrder D := CStarAlgebra.spectralOrder D
  letI : StarOrderedRing D := CStarAlgebra.spectralOrderedRing D
  have hAlphaDefectPos : 0 ≤ (1 : D) - alpha 1 :=
    one_sub_map_one_nonneg_of_completelyPositive_contractive
      alpha halpha halphaContract
  have hAlphaOnePos : 0 ≤ alpha (1 : A) :=
    map_nonneg_of_completelyPositive halpha zero_le_one
  have hAlphaDefectNorm : ‖(1 : D) - alpha 1‖ ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg
      ((1 : D) - alpha 1) hAlphaDefectPos).2
        (sub_le_self (1 : D) hAlphaOnePos)
  have hOmegaA : ‖omegaA.toCLM a‖ ≤ ‖a‖ := by
    calc
      ‖omegaA.toCLM a‖ ≤ ‖omegaA.toCLM‖ * ‖a‖ :=
        omegaA.toCLM.le_opNorm a
      _ ≤ 1 * ‖a‖ :=
        mul_le_mul_of_nonneg_right omegaA.norm_le (norm_nonneg a)
      _ = ‖a‖ := one_mul _
  have hAlphaRepairNorm :
      ‖additiveUnitalization alpha omegaA a‖ ≤ 2 := by
    calc
      ‖additiveUnitalization alpha omegaA a‖ =
          ‖alpha a + omegaA.toCLM a • ((1 : D) - alpha 1)‖ := rfl
      _ ≤ ‖alpha a‖ + ‖omegaA.toCLM a • ((1 : D) - alpha 1)‖ :=
        norm_add_le _ _
      _ = ‖alpha a‖ + ‖omegaA.toCLM a‖ * ‖(1 : D) - alpha 1‖ := by
        rw [norm_smul]
      _ ≤ ‖a‖ + ‖omegaA.toCLM a‖ * ‖(1 : D) - alpha 1‖ :=
        add_le_add (halphaContract a) le_rfl
      _ ≤ ‖a‖ + ‖a‖ * ‖(1 : D) - alpha 1‖ :=
        add_le_add le_rfl
          (mul_le_mul_of_nonneg_right hOmegaA (norm_nonneg _))
      _ ≤ ‖a‖ + ‖a‖ * 1 :=
        add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hAlphaDefectNorm (norm_nonneg a))
      _ ≤ 2 := by nlinarith [norm_nonneg a]
  have hOmegaD :
      ‖omegaD.toCLM (additiveUnitalization alpha omegaA a)‖ ≤ 2 := by
    calc
      ‖omegaD.toCLM (additiveUnitalization alpha omegaA a)‖ ≤
          ‖omegaD.toCLM‖ * ‖additiveUnitalization alpha omegaA a‖ :=
        omegaD.toCLM.le_opNorm _
      _ ≤ 1 * ‖additiveUnitalization alpha omegaA a‖ :=
        mul_le_mul_of_nonneg_right omegaD.norm_le (norm_nonneg _)
      _ ≤ 2 := by simpa using hAlphaRepairNorm
  have hIncoming : ‖beta ((1 : D) - alpha 1)‖ ≤ delta :=
    norm_second_incoming_unit_defect_le_of_cp_contractions
      alpha beta halpha hbeta halphaContract hbetaContract hunit
  have hOutgoing : ‖(1 : A) - beta 1‖ ≤ delta :=
    norm_one_sub_second_one_le_of_cp_contractions
      alpha beta halpha hbeta halphaContract hbetaContract hunit
  have hTermIncoming :
      ‖omegaA.toCLM a • beta ((1 : D) - alpha 1)‖ ≤ delta := by
    rw [norm_smul]
    calc
      ‖omegaA.toCLM a‖ * ‖beta ((1 : D) - alpha 1)‖ ≤
          1 * ‖beta ((1 : D) - alpha 1)‖ :=
        mul_le_mul_of_nonneg_right (hOmegaA.trans ha) (norm_nonneg _)
      _ ≤ 1 * delta :=
        mul_le_mul_of_nonneg_left hIncoming zero_le_one
      _ = delta := one_mul _
  have hTermOutgoing :
      ‖omegaD.toCLM (additiveUnitalization alpha omegaA a) •
          ((1 : A) - beta 1)‖ ≤ 2 * delta := by
    rw [norm_smul]
    calc
      ‖omegaD.toCLM (additiveUnitalization alpha omegaA a)‖ *
          ‖(1 : A) - beta 1‖ ≤ 2 * ‖(1 : A) - beta 1‖ :=
        mul_le_mul_of_nonneg_right hOmegaD (norm_nonneg _)
      _ ≤ 2 * delta := mul_le_mul_of_nonneg_left hOutgoing (by positivity)
  have hexpand :
      additiveUnitalization beta omegaD
          (additiveUnitalization alpha omegaA a) - a =
        (beta (alpha a) - a) +
          omegaA.toCLM a • beta ((1 : D) - alpha 1) +
          omegaD.toCLM (additiveUnitalization alpha omegaA a) •
            ((1 : A) - beta 1) := by
    have hbetaRepair :
        beta (additiveUnitalization alpha omegaA a) =
          beta (alpha a) +
            omegaA.toCLM a • beta ((1 : D) - alpha 1) := by
      rw [additiveUnitalization_apply, map_add, map_smul]
    change
      (beta (additiveUnitalization alpha omegaA a) +
          omegaD.toCLM (additiveUnitalization alpha omegaA a) •
            ((1 : A) - beta 1)) - a = _
    rw [hbetaRepair]
    abel
  rw [hexpand]
  calc
    ‖(beta (alpha a) - a) +
        omegaA.toCLM a • beta ((1 : D) - alpha 1) +
        omegaD.toCLM (additiveUnitalization alpha omegaA a) •
          ((1 : A) - beta 1)‖ ≤
        ‖beta (alpha a) - a‖ +
          ‖omegaA.toCLM a • beta ((1 : D) - alpha 1)‖ +
          ‖omegaD.toCLM (additiveUnitalization alpha omegaA a) •
            ((1 : A) - beta 1)‖ := by
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ delta + delta + 2 * delta := by gcongr
    _ = 4 * delta := by ring

end

end CStarExactness
end GroupApproximation

open GroupApproximation.CStarExactness

#audit_axioms one_sub_map_one_nonneg_of_completelyPositive_contractive
#audit_axioms norm_one_sub_second_one_le_of_cp_contractions
#audit_axioms norm_second_incoming_unit_defect_le_of_cp_contractions
#audit_axioms exists_matrix_star_mul_self_eq_gram
#audit_axioms isCompletelyPositive_stateSmulLinearMap
#audit_axioms additiveUnitalization_completelyPositive_unital
#audit_axioms norm_additiveUnitalization_comp_sub_le_four_mul
