import GroupApproximation.Kazhdan.KazhdanDisplacementCriterion
import GroupApproximation.Kazhdan.PositiveOperatorGap
import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# Exact finite Hodge certificates for Kazhdan pairs

This file is the trust boundary between a finite rational group-ring
certificate and Kazhdan's property `(T)`.  Certificate data consist only of
finite matrices over `ℚ[G]`, exact coefficient identities, and rational
row-`ℓ1` inequalities.  In particular, no positivity statement about a
represented operator and no Kazhdan conclusion is stored in the certificate.

The analytic argument has two independent layers.

* A Gram decomposition with row-and-column `ℓ1` control on its residual gives a
  uniform lower bound for the represented degree-one Hodge form.
* Testing that bound on the exact coboundaries of a finite generating tuple
  gives a quadratic gap for the ordinary generator Laplacian.  The
  Richardson-iteration theorem in `PositiveOperatorGap` then gives uniform
  displacement in every representation without invariant vectors.

All sums below are finite.  The coefficient ring is literally `ℚ`; casting
to `ℝ` occurs only in the representation evaluator.
-/

namespace GroupApproximation
namespace ExactHodgeCertificate

open scoped BigOperators MonoidAlgebra

universe u v

variable {G : Type u} [Group G]

/-- The rational group ring used by the certificate. -/
abbrev RatGroupRing (G : Type u) [Group G] := MonoidAlgebra ℚ G

/-- The coefficient involution `(∑ a_g g)⁺ = ∑ a_g g⁻¹`. -/
noncomputable def adjoint (a : RatGroupRing G) : RatGroupRing G :=
  MonoidAlgebra.ofCoeff <|
    a.coeff.equivMapDomain (Equiv.inv G)

@[simp] theorem adjoint_zero : adjoint (0 : RatGroupRing G) = 0 := by
  ext g
  simp [adjoint]

@[simp] theorem adjoint_add (a b : RatGroupRing G) :
    adjoint (a + b) = adjoint a + adjoint b := by
  ext g
  simp [adjoint]

theorem adjoint_sum {I : Type*} [Fintype I]
    (a : I → RatGroupRing G) :
    adjoint (∑ i, a i) = ∑ i, adjoint (a i) := by
  classical
  induction (Finset.univ : Finset I) using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, adjoint_add, ih]

/-- The coefficient involution reverses multiplication. -/
@[simp] theorem adjoint_mul (a b : RatGroupRing G) :
    adjoint (a * b) = adjoint b * adjoint a := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [add_mul, ha, hb, mul_add]
  | single g q =>
      induction b using MonoidAlgebra.induction_linear with
      | zero => simp
      | add a b ha hb => simp [mul_add, ha, hb, add_mul]
      | single h r =>
          simp [adjoint, MonoidAlgebra.single_mul_single, mul_comm]

@[simp] theorem adjoint_neg (a : RatGroupRing G) :
    adjoint (-a) = -adjoint a := by
  ext g
  simp [adjoint]

@[simp] theorem adjoint_sub (a b : RatGroupRing G) :
    adjoint (a - b) = adjoint a - adjoint b := by
  rw [sub_eq_add_neg, adjoint_add, adjoint_neg, sub_eq_add_neg]

@[simp] theorem adjoint_single (g : G) (q : ℚ) :
    adjoint (MonoidAlgebra.single g q) = MonoidAlgebra.single g⁻¹ q := by
  ext h
  simp [adjoint]

@[simp] theorem adjoint_one : adjoint (1 : RatGroupRing G) = 1 := by
  simp [MonoidAlgebra.one_def]

/-- Exact coefficient `ℓ1` norm.  This is rational, so a concrete
certificate can discharge its bounds by normalization of rational
arithmetic after its finite supports have been exposed. -/
noncomputable def l1 (a : RatGroupRing G) : ℚ :=
  a.coeff.sum fun _ q ↦ |q|

@[simp] theorem l1_single (g : G) (q : ℚ) :
    l1 (MonoidAlgebra.single g q) = |q| := by
  classical
  simp [l1]

/-- Triangle inequality for the exact coefficient `ℓ1` norm. -/
theorem l1_add_le (a b : RatGroupRing G) :
    l1 (a + b) ≤ l1 a + l1 b := by
  classical
  let s := a.coeff.support ∪ b.coeff.support
  unfold l1
  rw [Finsupp.sum_of_support_subset (a + b).coeff (by
        simpa [s] using Finsupp.support_add
          (g₁ := a.coeff) (g₂ := b.coeff))
      (fun _ q ↦ |q|) (by simp),
    Finsupp.sum_of_support_subset a.coeff (Finset.subset_union_left)
      (fun _ q ↦ |q|) (by simp),
    Finsupp.sum_of_support_subset b.coeff (Finset.subset_union_right)
      (fun _ q ↦ |q|) (by simp)]
  simp only [MonoidAlgebra.coeff_add]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun g _ ↦ abs_add_le (a.coeff g) (b.coeff g)

/-- A finite sum has `ℓ1` norm at most the sum of the individual norms. -/
theorem l1_sum_le {I : Type*} [Fintype I]
    (a : I → RatGroupRing G) :
    l1 (∑ i, a i) ≤ ∑ i, l1 (a i) := by
  classical
  exact Finset.le_sum_of_subadditive l1 (by simp [l1]) l1_add_le
    Finset.univ a

/-- A real orthogonal representation, read as a monoid homomorphism into
linear endomorphisms. -/
noncomputable def linearRepresentation
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) : G →* Module.End ℝ E where
  toFun g := (rho g).toLinearEquiv.toLinearMap
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp [map_mul]

/-- Evaluation of `ℚ[G]` in a real orthogonal representation.  We first
cast coefficients into `ℝ[G]`; this avoids inventing a spurious
`ℚ`-algebra structure on real-linear endomorphisms. -/
noncomputable def evaluate
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (a : RatGroupRing G) : Module.End ℝ E :=
  MonoidAlgebra.lift ℝ (Module.End ℝ E) G (linearRepresentation rho) <|
    MonoidAlgebra.mapRingHom (M := G) (Rat.castHom ℝ) a

@[simp] theorem evaluate_single_apply
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (g : G) (q : ℚ) (x : E) :
    evaluate rho (MonoidAlgebra.single g q) x = (q : ℝ) • rho g x := by
  simp [evaluate, linearRepresentation]

@[simp] theorem evaluate_one_apply
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    evaluate rho 1 x = x := by simp [evaluate]

@[simp] theorem evaluate_zero_apply
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    evaluate rho 0 x = 0 := by simp [evaluate]

@[simp] theorem evaluate_add_apply
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (a b : RatGroupRing G) (x : E) :
    evaluate rho (a + b) x = evaluate rho a x + evaluate rho b x := by
  simp [evaluate]

@[simp] theorem evaluate_mul_apply
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (a b : RatGroupRing G) (x : E) :
    evaluate rho (a * b) x = evaluate rho a (evaluate rho b x) := by
  simp [evaluate, map_mul]

theorem evaluate_sum_apply
    {I : Type*} [Fintype I]
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (a : I → RatGroupRing G) (x : E) :
    evaluate rho (∑ i, a i) x = ∑ i, evaluate rho (a i) x := by
  simp [evaluate]

theorem evaluate_apply_eq_sum
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (a : RatGroupRing G) (x : E) :
    evaluate rho a x = a.coeff.sum (fun g q ↦ (q : ℝ) • rho g x) := by
  simp [evaluate, MonoidAlgebra.lift_apply, linearRepresentation,
    MonoidAlgebra.mapRingHom, Finsupp.sum_mapRange_index]

/-- Evaluation of the coefficient involution is the Hilbert adjoint. -/
theorem inner_evaluate_adjoint
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (a : RatGroupRing G) (x y : E) :
    inner ℝ (evaluate rho (adjoint a) x) y =
      inner ℝ x (evaluate rho a y) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb =>
      simp [ha, hb, inner_add_left, inner_add_right]
  | single g q =>
      simp only [adjoint_single]
      rw [evaluate_single_apply, evaluate_single_apply]
      simp only [inner_smul_left, inner_smul_right]
      have hiso := (rho g).inner_map_map (rho g⁻¹ x) y
      have hadj : inner ℝ (rho g⁻¹ x) y = inner ℝ x (rho g y) := by
        calc
          inner ℝ (rho g⁻¹ x) y =
              inner ℝ (rho g (rho g⁻¹ x)) (rho g y) := hiso.symm
          _ = inner ℝ x (rho g y) := by simp
      simpa [map_inv] using congrArg (fun t : ℝ ↦ (q : ℝ) * t) hadj

/-- Right-slot form of `inner_evaluate_adjoint`. -/
theorem inner_evaluate_adjoint_right
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (a : RatGroupRing G) (x y : E) :
    inner ℝ x (evaluate rho (adjoint a) y) =
      inner ℝ (evaluate rho a x) y := by
  rw [real_inner_comm, inner_evaluate_adjoint, real_inner_comm]

/-- Evaluation is bounded by the exact coefficient `ℓ1` norm. -/
theorem norm_evaluate_le_l1_mul
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (a : RatGroupRing G) (x : E) :
    ‖evaluate rho a x‖ ≤ (l1 a : ℝ) * ‖x‖ := by
  rw [evaluate_apply_eq_sum]
  calc
    ‖a.coeff.sum (fun g q ↦ (q : ℝ) • rho g x)‖ ≤
        a.coeff.sum (fun g q ↦ ‖(q : ℝ) • rho g x‖) := by
      simpa [Finsupp.sum] using
        (norm_sum_le a.coeff.support
          (fun g ↦ (a.coeff g : ℝ) • rho g x))
    _ = a.coeff.sum (fun _ q ↦ (|q| : ℝ) * ‖x‖) := by
      apply Finsupp.sum_congr
      intro g hg
      rw [norm_smul, (rho g).norm_map, Real.norm_eq_abs]
    _ = (l1 a : ℝ) * ‖x‖ := by
      simp [l1, Finsupp.sum, Finset.sum_mul, Rat.cast_sum]

@[simp] theorem adjoint_adjoint (a : RatGroupRing G) :
    adjoint (adjoint a) = a := by
  ext g
  simp [adjoint]

/-- Matrix quadratic form obtained by evaluating group-ring entries. -/
noncomputable def matrixEnergy
    {I : Type*} [Fintype I]
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (A : I → I → RatGroupRing G) (z : I → E) : ℝ :=
  ∑ i, ∑ j, inner ℝ (z i) (evaluate rho (A i j) (z j))

theorem matrixEnergy_add
    {I : Type*} [Fintype I]
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (A B : I → I → RatGroupRing G) (z : I → E) :
    matrixEnergy rho (fun i j ↦ A i j + B i j) z =
      matrixEnergy rho A z + matrixEnergy rho B z := by
  unfold matrixEnergy
  simp only [evaluate_add_apply, inner_add_right, Finset.sum_add_distrib]

/-- Squared `ℓ²` norm of a finite Hilbert-space family. -/
def familyNormSq {I : Type*} [Fintype I]
    {E : Type v} [NormedAddCommGroup E] (z : I → E) : ℝ :=
  ∑ i, ‖z i‖ ^ 2

/-- Exact represented quadratic-form identity for a group-ring Gram
matrix. -/
theorem matrixEnergy_gram_eq
    {I K : Type*} [Fintype I] [Fintype K]
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (q : K → I → RatGroupRing G) (z : I → E) :
    matrixEnergy rho (fun i j ↦ ∑ k, adjoint (q k i) * q k j) z =
      ∑ k, ‖∑ i, evaluate rho (q k i) (z i)‖ ^ 2 := by
  unfold matrixEnergy
  calc
    ∑ i, ∑ j, inner ℝ (z i)
        (evaluate rho (∑ k, adjoint (q k i) * q k j) (z j)) =
        ∑ i, ∑ j, ∑ k, inner ℝ
          (evaluate rho (q k i) (z i))
          (evaluate rho (q k j) (z j)) := by
      simp_rw [evaluate_sum_apply, inner_sum, evaluate_mul_apply,
        inner_evaluate_adjoint_right]
    _ = ∑ i, ∑ k, ∑ j, inner ℝ
          (evaluate rho (q k i) (z i))
          (evaluate rho (q k j) (z j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ k, ∑ i, ∑ j, inner ℝ
          (evaluate rho (q k i) (z i))
          (evaluate rho (q k j) (z j)) := by
      rw [Finset.sum_comm]
    _ = ∑ k, ‖∑ i, evaluate rho (q k i) (z i)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [← real_inner_self_eq_norm_sq, sum_inner]
      apply Finset.sum_congr rfl
      intro i hi
      rw [inner_sum]

/-- The represented Gram matrix of finitely many group-ring rows has
nonnegative quadratic form. -/
theorem matrixEnergy_gram_nonneg
    {I K : Type*} [Fintype I] [Fintype K]
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (q : K → I → RatGroupRing G) (z : I → E) :
    0 ≤ matrixEnergy rho
      (fun i j ↦ ∑ k, adjoint (q k i) * q k j) z := by
  rw [matrixEnergy_gram_eq]
  exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-- A residual whose row and column `ℓ1` norms are at most `r` has
quadratic form bounded below by `-r`. -/
theorem neg_rowL1_mul_familyNormSq_le_matrixEnergy
    {I : Type*} [Fintype I]
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (R : I → I → RatGroupRing G) (z : I → E) (r : ℚ)
    (hrow : ∀ i, ∑ j, l1 (R i j) ≤ r)
    (hcol : ∀ j, ∑ i, l1 (R i j) ≤ r) :
    -(r : ℝ) * familyNormSq z ≤ matrixEnergy rho R z := by
  have hterm (i j : I) :
      |inner ℝ (z i) (evaluate rho (R i j) (z j))| ≤
        (l1 (R i j) : ℝ) * ‖z i‖ * ‖z j‖ := by
    calc
      |inner ℝ (z i) (evaluate rho (R i j) (z j))| ≤
          ‖z i‖ * ‖evaluate rho (R i j) (z j)‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ ‖z i‖ * ((l1 (R i j) : ℝ) * ‖z j‖) :=
        mul_le_mul_of_nonneg_left
          (norm_evaluate_le_l1_mul rho (R i j) (z j)) (norm_nonneg _)
      _ = (l1 (R i j) : ℝ) * ‖z i‖ * ‖z j‖ := by ring
  have hl1nonneg (i j : I) : (0 : ℝ) ≤ (l1 (R i j) : ℝ) := by
    exact_mod_cast Finsupp.sum_nonneg fun _ _ ↦ abs_nonneg _
  have hweighted :
      ∑ i, ∑ j, (l1 (R i j) : ℝ) * ‖z i‖ * ‖z j‖ ≤
        (r : ℝ) * familyNormSq z := by
    have hrowTerm :
        ∑ i, ∑ j, (l1 (R i j) : ℝ) * ‖z i‖ ^ 2 ≤
          (r : ℝ) * familyNormSq z := by
      calc
        ∑ i, ∑ j, (l1 (R i j) : ℝ) * ‖z i‖ ^ 2 =
            ∑ i, (∑ j, (l1 (R i j) : ℝ)) * ‖z i‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_mul]
        _ ≤ ∑ i, (r : ℝ) * ‖z i‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro i hi
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hrow i) (sq_nonneg _)
        _ = (r : ℝ) * familyNormSq z := by
          simp [familyNormSq, Finset.mul_sum]
    have hcolTerm :
        ∑ i, ∑ j, (l1 (R i j) : ℝ) * ‖z j‖ ^ 2 ≤
          (r : ℝ) * familyNormSq z := by
      rw [Finset.sum_comm]
      calc
        ∑ j, ∑ i, (l1 (R i j) : ℝ) * ‖z j‖ ^ 2 =
            ∑ j, (∑ i, (l1 (R i j) : ℝ)) * ‖z j‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.sum_mul]
        _ ≤ ∑ j, (r : ℝ) * ‖z j‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro j hj
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcol j) (sq_nonneg _)
        _ = (r : ℝ) * familyNormSq z := by
          simp [familyNormSq, Finset.mul_sum]
    calc
      ∑ i, ∑ j, (l1 (R i j) : ℝ) * ‖z i‖ * ‖z j‖ ≤
          ∑ i, ∑ j, (l1 (R i j) : ℝ) *
            ((‖z i‖ ^ 2 + ‖z j‖ ^ 2) / 2) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        have huv : ‖z i‖ * ‖z j‖ ≤
            (‖z i‖ ^ 2 + ‖z j‖ ^ 2) / 2 := by
          nlinarith [sq_nonneg (‖z i‖ - ‖z j‖)]
        nlinarith [hl1nonneg i j]
      _ = ((∑ i, ∑ j, (l1 (R i j) : ℝ) * ‖z i‖ ^ 2) +
          (∑ i, ∑ j, (l1 (R i j) : ℝ) * ‖z j‖ ^ 2)) / 2 := by
        calc
          ∑ i, ∑ j, (l1 (R i j) : ℝ) *
                ((‖z i‖ ^ 2 + ‖z j‖ ^ 2) / 2) =
              ∑ i, ∑ j,
              ((l1 (R i j) : ℝ) * ‖z i‖ ^ 2 * (1 / 2) +
                (l1 (R i j) : ℝ) * ‖z j‖ ^ 2 * (1 / 2)) := by
              apply Finset.sum_congr rfl
              intro i hi
              apply Finset.sum_congr rfl
              intro j hj
              ring
          _ =
              ∑ i, ((∑ j, (l1 (R i j) : ℝ) * ‖z i‖ ^ 2) * (1 / 2) +
                (∑ j, (l1 (R i j) : ℝ) * ‖z j‖ ^ 2) * (1 / 2)) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul]
          _ = (∑ i, ∑ j, (l1 (R i j) : ℝ) * ‖z i‖ ^ 2) * (1 / 2) +
              (∑ i, ∑ j, (l1 (R i j) : ℝ) * ‖z j‖ ^ 2) * (1 / 2) := by
            rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul]
          _ = ((∑ i, ∑ j, (l1 (R i j) : ℝ) * ‖z i‖ ^ 2) +
              (∑ i, ∑ j, (l1 (R i j) : ℝ) * ‖z j‖ ^ 2)) / 2 := by
            ring
      _ ≤ ((r : ℝ) * familyNormSq z +
          (r : ℝ) * familyNormSq z) / 2 := by gcongr
      _ = (r : ℝ) * familyNormSq z := by ring
  have habs : |matrixEnergy rho R z| ≤
      ∑ i, ∑ j, (l1 (R i j) : ℝ) * ‖z i‖ * ‖z j‖ := by
    unfold matrixEnergy
    calc
      |∑ i, ∑ j, inner ℝ (z i) (evaluate rho (R i j) (z j))| ≤
          ∑ i, |∑ j, inner ℝ (z i) (evaluate rho (R i j) (z j))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |inner ℝ (z i)
          (evaluate rho (R i j) (z j))| := by
        apply Finset.sum_le_sum
        intro i hi
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j,
          (l1 (R i j) : ℝ) * ‖z i‖ * ‖z j‖ := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact hterm i j
  have hnegative : -((r : ℝ) * familyNormSq z) ≤ matrixEnergy rho R z := by
    calc
      -((r : ℝ) * familyNormSq z) ≤
          -|∑ i, ∑ j, inner ℝ (z i)
            (evaluate rho (R i j) (z j))| := by
        exact neg_le_neg (habs.trans hweighted)
      _ ≤ ∑ i, ∑ j, inner ℝ (z i)
          (evaluate rho (R i j) (z j)) := neg_abs_le _
  simpa [matrixEnergy] using hnegative

/-- The degree-one Hodge matrix `B⁺B + DD⁺`. -/
noncomputable def hodgeMatrix
    {I J : Type*} [Fintype I] [Fintype J]
    (D : I → RatGroupRing G) (B : J → I → RatGroupRing G) :
    I → I → RatGroupRing G :=
  fun i k ↦
    (∑ j, adjoint (B j i) * B j k) + D i * adjoint (D k)

/-- The scalar degree-zero Laplacian `D⁺D`. -/
noncomputable def laplacianRing
    {I : Type*} [Fintype I] (D : I → RatGroupRing G) : RatGroupRing G :=
  ∑ i, adjoint (D i) * D i

/-- Exact chain identity turns the degree-one Hodge form on a coboundary
into the squared norm of the degree-zero Laplacian. -/
theorem matrixEnergy_hodge_coboundary_eq
    {I J : Type*} [Fintype I] [Fintype J]
    (D : I → RatGroupRing G) (B : J → I → RatGroupRing G)
    (hchain : ∀ j, ∑ i, B j i * D i = 0)
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    matrixEnergy rho (hodgeMatrix D B)
        (fun i ↦ evaluate rho (D i) x) =
      ‖evaluate rho (laplacianRing D) x‖ ^ 2 := by
  let qD : Unit → I → RatGroupRing G := fun _ i ↦ adjoint (D i)
  have hhodge : hodgeMatrix D B = fun i k ↦
      (∑ j, adjoint (B j i) * B j k) +
        (∑ a : Unit, adjoint (qD a i) * qD a k) := by
    funext i k
    simp [hodgeMatrix, qD]
  rw [hhodge, matrixEnergy_add, matrixEnergy_gram_eq,
    matrixEnergy_gram_eq]
  have hB (j : J) :
      ∑ i, evaluate rho (B j i)
          (evaluate rho (D i) x) = 0 := by
    calc
      ∑ i, evaluate rho (B j i) (evaluate rho (D i) x) =
          evaluate rho (∑ i, B j i * D i) x := by
        symm
        rw [evaluate_sum_apply]
        simp_rw [evaluate_mul_apply]
      _ = 0 := by rw [hchain j]; simp
  have hD :
      ∑ i, evaluate rho (adjoint (D i))
          (evaluate rho (D i) x) =
        evaluate rho (laplacianRing D) x := by
    symm
    rw [laplacianRing, evaluate_sum_apply]
    simp_rw [evaluate_mul_apply]
  simp_rw [hB]
  simp [qD, hD]

/-- The scalar identity matrix over the rational group ring. -/
noncomputable def scalarMatrix
    {I : Type*} [Fintype I] [DecidableEq I]
    (c : ℚ) : I → I → RatGroupRing G :=
  fun i k ↦ if i = k then MonoidAlgebra.single 1 c else 0

/-- Exact finite certificate for a positive Hodge gap.  Every proof field is
an identity or inequality in finite rational data. -/
structure Certificate
    {I J K : Type*} [Fintype I] [DecidableEq I] [Fintype J] [Fintype K]
    (D : I → RatGroupRing G) (B : J → I → RatGroupRing G)
    (q : K → I → RatGroupRing G)
    (R : I → I → RatGroupRing G) (c r : ℚ) : Prop where
  gap_pos : r < c
  chain : ∀ j, ∑ i, B j i * D i = 0
  decomposition : ∀ i k,
    hodgeMatrix D B i k =
      scalarMatrix c i k +
        (∑ a, adjoint (q a i) * q a k) + R i k
  residual_row_l1 : ∀ i, ∑ k, l1 (R i k) ≤ r
  residual_column_l1 : ∀ k, ∑ i, l1 (R i k) ≤ r

theorem matrixEnergy_scalarMatrix
    {I : Type*} [Fintype I] [DecidableEq I]
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (c : ℚ) (z : I → E) :
    matrixEnergy rho (scalarMatrix c) z = (c : ℝ) * familyNormSq z := by
  classical
  unfold matrixEnergy scalarMatrix familyNormSq
  calc
    ∑ i, ∑ j, inner ℝ (z i)
        (evaluate rho (if i = j then MonoidAlgebra.single 1 c else 0) (z j)) =
        ∑ i, inner ℝ (z i)
          (evaluate rho (MonoidAlgebra.single 1 c) (z i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_eq_single i]
      · simp
      · intro j hj hji
        simp [hji.symm]
      · simp
    _ = ∑ i, (c : ℝ) * ‖z i‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [evaluate_single_apply]
      simp [inner_smul_right]
    _ = (c : ℝ) * ∑ i, ‖z i‖ ^ 2 := by
      rw [Finset.mul_sum]

/-- A concrete exact certificate yields the represented Hodge lower bound
`c-r`, uniformly over all real orthogonal representations. -/
theorem Certificate.hodge_gap
    {I J K : Type*} [Fintype I] [DecidableEq I] [Fintype J] [Fintype K]
    {D : I → RatGroupRing G} {B : J → I → RatGroupRing G}
    {q : K → I → RatGroupRing G}
    {R : I → I → RatGroupRing G} {c r : ℚ}
    (C : Certificate D B q R c r)
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (z : I → E) :
    ((c - r : ℚ) : ℝ) * familyNormSq z ≤
      matrixEnergy rho (hodgeMatrix D B) z := by
  let Gram : I → I → RatGroupRing G :=
    fun i k ↦ ∑ a, adjoint (q a i) * q a k
  have hdecomp : hodgeMatrix D B =
      fun i k ↦ scalarMatrix c i k + Gram i k + R i k := by
    funext i k
    simpa [Gram, add_assoc] using C.decomposition i k
  have hgram : 0 ≤ matrixEnergy rho Gram z := by
    exact matrixEnergy_gram_nonneg rho q z
  have hres : -(r : ℝ) * familyNormSq z ≤
      matrixEnergy rho R z :=
    neg_rowL1_mul_familyNormSq_le_matrixEnergy rho R z r
      C.residual_row_l1 C.residual_column_l1
  rw [hdecomp, matrixEnergy_add, matrixEnergy_add,
    matrixEnergy_scalarMatrix]
  push_cast
  linarith

/-- The group-ring coboundary attached to a finite generator tuple. -/
noncomputable def generatorCoboundary
    {I : Type*} (s : I → G) (i : I) : RatGroupRing G :=
  MonoidAlgebra.single (s i) 1 - 1

@[simp] theorem evaluate_generatorCoboundary
    {I : Type*} (s : I → G) (i : I)
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    evaluate rho (generatorCoboundary s i) x = rho (s i) x - x := by
  simp [generatorCoboundary, evaluate, linearRepresentation]

@[simp] theorem evaluate_adjoint_generatorCoboundary
    {I : Type*} (s : I → G) (i : I)
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    evaluate rho (adjoint (generatorCoboundary s i)) x =
      rho (s i)⁻¹ x - x := by
  simp [generatorCoboundary, evaluate, linearRepresentation]

/-- The ordinary unnormalized Laplacian of a finite generator tuple. -/
noncomputable def generatorLaplacianOperator
    {I : Type*} [Fintype I] (s : I → G)
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) : E →L[ℝ] E :=
  ∑ i,
    ((rho (s i)⁻¹).toContinuousLinearEquiv.toContinuousLinearMap -
      ContinuousLinearMap.id ℝ E).comp
    ((rho (s i)).toContinuousLinearEquiv.toContinuousLinearMap -
      ContinuousLinearMap.id ℝ E)

@[simp] theorem generatorLaplacianOperator_apply
    {I : Type*} [Fintype I] (s : I → G)
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    generatorLaplacianOperator s rho x =
      ∑ i, (rho (s i)⁻¹ (rho (s i) x - x) - (rho (s i) x - x)) := by
  rw [generatorLaplacianOperator, sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rfl

theorem generatorLaplacianOperator_apply_eq_evaluate
    {I : Type*} [Fintype I] (s : I → G)
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    generatorLaplacianOperator s rho x =
      evaluate rho (laplacianRing (generatorCoboundary s)) x := by
  rw [generatorLaplacianOperator_apply, laplacianRing, evaluate_sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [evaluate_mul_apply, evaluate_generatorCoboundary,
    evaluate_adjoint_generatorCoboundary]

/-- The Laplacian quadratic form is the sum of squared generator
displacements. -/
theorem generatorLaplacian_energy
    {I : Type*} [Fintype I] (s : I → G)
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    PositiveOperatorGap.energy (generatorLaplacianOperator s rho) x =
      ∑ i, ‖rho (s i) x - x‖ ^ 2 := by
  rw [PositiveOperatorGap.energy,
    generatorLaplacianOperator_apply_eq_evaluate]
  rw [laplacianRing, evaluate_sum_apply, inner_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [evaluate_mul_apply, inner_evaluate_adjoint_right,
    evaluate_generatorCoboundary, real_inner_self_eq_norm_sq]

/-- Symmetry of the generator Laplacian. -/
theorem generatorLaplacian_symmetric
    {I : Type*} [Fintype I] (s : I → G)
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (x y : E) :
    inner ℝ (generatorLaplacianOperator s rho x) y =
      inner ℝ x (generatorLaplacianOperator s rho y) := by
  rw [generatorLaplacianOperator_apply_eq_evaluate,
    generatorLaplacianOperator_apply_eq_evaluate]
  rw [laplacianRing, evaluate_sum_apply, evaluate_sum_apply,
    inner_sum, sum_inner]
  apply Finset.sum_congr rfl
  intro i hi
  rw [evaluate_mul_apply, evaluate_mul_apply,
    inner_evaluate_adjoint, inner_evaluate_adjoint_right]

/-- Every generator displacement has norm at most twice the vector norm. -/
theorem norm_generator_displacement_le_two
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (g : G) (x : E) :
    ‖rho g x - x‖ ≤ 2 * ‖x‖ := by
  calc
    ‖rho g x - x‖ ≤ ‖rho g x‖ + ‖x‖ := norm_sub_le _ _
    _ = 2 * ‖x‖ := by rw [(rho g).norm_map]; ring

/-- Universal upper bound on the Laplacian quadratic form. -/
theorem generatorLaplacian_energy_le
    {I : Type*} [Fintype I] (s : I → G)
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    PositiveOperatorGap.energy (generatorLaplacianOperator s rho) x ≤
      (4 * Fintype.card I : ℝ) * ‖x‖ ^ 2 := by
  rw [generatorLaplacian_energy]
  calc
    ∑ i, ‖rho (s i) x - x‖ ^ 2 ≤
        ∑ _i : I, (2 * ‖x‖) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num)
        (norm_nonneg _))).2 (norm_generator_displacement_le_two rho (s i) x)
    _ = (4 * Fintype.card I : ℝ) * ‖x‖ ^ 2 := by
      simp
      ring

/-- Each Laplacian summand has norm at most twice the corresponding
generator displacement. -/
theorem norm_generatorLaplacian_summand_le
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (g : G) (x : E) :
    ‖rho g⁻¹ (rho g x - x) - (rho g x - x)‖ ≤
      2 * ‖rho g x - x‖ := by
  calc
    ‖rho g⁻¹ (rho g x - x) - (rho g x - x)‖ ≤
        ‖rho g⁻¹ (rho g x - x)‖ + ‖rho g x - x‖ := norm_sub_le _ _
    _ = 2 * ‖rho g x - x‖ := by rw [(rho g⁻¹).norm_map]; ring

/-- Universal upper estimate `‖Δx‖² ≤ 4|I|⟨Δx,x⟩`. -/
theorem generatorLaplacian_norm_sq_le
    {I : Type*} [Fintype I] (s : I → G)
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    ‖generatorLaplacianOperator s rho x‖ ^ 2 ≤
      (4 * Fintype.card I : ℝ) *
        PositiveOperatorGap.energy (generatorLaplacianOperator s rho) x := by
  rw [generatorLaplacianOperator_apply, generatorLaplacian_energy]
  have htriangle :
      ‖∑ i, (rho (s i)⁻¹ (rho (s i) x - x) -
          (rho (s i) x - x))‖ ≤
        ∑ i, 2 * ‖rho (s i) x - x‖ := by
    calc
      ‖∑ i, (rho (s i)⁻¹ (rho (s i) x - x) -
          (rho (s i) x - x))‖ ≤
          ∑ i, ‖rho (s i)⁻¹ (rho (s i) x - x) -
            (rho (s i) x - x)‖ := norm_sum_le _ _
      _ ≤ ∑ i, 2 * ‖rho (s i) x - x‖ := by
        apply Finset.sum_le_sum
        intro i hi
        exact norm_generatorLaplacian_summand_le rho (s i) x
  have hright : 0 ≤ ∑ i, 2 * ‖rho (s i) x - x‖ :=
    Finset.sum_nonneg fun _ _ ↦ mul_nonneg (by norm_num) (norm_nonneg _)
  have hsq := (sq_le_sq₀ (norm_nonneg _) hright).2 htriangle
  have hcauchy :
      (∑ i, 2 * ‖rho (s i) x - x‖) ^ 2 ≤
        (Fintype.card I : ℝ) *
          ∑ i, (2 * ‖rho (s i) x - x‖) ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq
      (s := (Finset.univ : Finset I))
      (f := fun _ ↦ (1 : ℝ))
      (g := fun i ↦ 2 * ‖rho (s i) x - x‖)
  calc
    ‖∑ i, (rho (s i)⁻¹ (rho (s i) x - x) -
        (rho (s i) x - x))‖ ^ 2 ≤
        (∑ i, 2 * ‖rho (s i) x - x‖) ^ 2 := hsq
    _ ≤ (Fintype.card I : ℝ) *
        ∑ i, (2 * ‖rho (s i) x - x‖) ^ 2 := hcauchy
    _ = (4 * Fintype.card I : ℝ) *
        ∑ i, ‖rho (s i) x - x‖ ^ 2 := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- Vanishing of the generator Laplacian forces invariance when the tuple
generates the group. -/
theorem invariant_of_generatorLaplacian_eq_zero
    {I : Type*} [Fintype I] (s : I → G)
    (hgen : Subgroup.closure (Set.range s) = ⊤)
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (x : E)
    (hzero : generatorLaplacianOperator s rho x = 0) :
    ∀ g : G, rho g x = x := by
  have henergy : ∑ i, ‖rho (s i) x - x‖ ^ 2 = 0 := by
    rw [← generatorLaplacian_energy s rho x,
      PositiveOperatorGap.energy, hzero]
    simp
  have hfix (i : I) : rho (s i) x = x := by
    have hi : ‖rho (s i) x - x‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ sq_nonneg _).mp
        henergy i (Finset.mem_univ i)
    have hnorm : ‖rho (s i) x - x‖ = 0 := sq_eq_zero_iff.mp hi
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  let H : Subgroup G :=
    { carrier := {g | rho g x = x}
      one_mem' := by simp
      mul_mem' := by
        intro g h hg hh
        change rho g x = x at hg
        change rho h x = x at hh
        change rho (g * h) x = x
        rw [map_mul]
        change rho g (rho h x) = x
        rw [hh, hg]
      inv_mem' := by
        intro g hg
        change rho g x = x at hg
        change rho g⁻¹ x = x
        have happly := congrArg (fun y ↦ rho g⁻¹ y) hg
        simpa using happly.symm }
  have hrange : Set.range s ⊆ (H : Set G) := by
    rintro _ ⟨i, rfl⟩
    exact hfix i
  have hclosure : Subgroup.closure (Set.range s) ≤ H :=
    (Subgroup.closure_le H).2 hrange
  have htop : H = ⊤ := by
    rw [hgen] at hclosure
    exact top_unique hclosure
  intro g
  have : g ∈ H := by rw [htop]; trivial
  exact this

/-- Testing the certified Hodge gap on exact coboundaries gives the
quadratic gap required by `PositiveOperatorGap`. -/
theorem Certificate.generatorLaplacian_quadratic_gap
    {I J K : Type*} [Fintype I] [DecidableEq I] [Fintype J] [Fintype K]
    (s : I → G) {B : J → I → RatGroupRing G}
    {q : K → I → RatGroupRing G}
    {R : I → I → RatGroupRing G} {c r : ℚ}
    (C : Certificate (generatorCoboundary s) B q R c r)
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    ((c - r : ℚ) : ℝ) *
        PositiveOperatorGap.energy (generatorLaplacianOperator s rho) x ≤
      ‖generatorLaplacianOperator s rho x‖ ^ 2 := by
  have hgap := C.hodge_gap rho
    (fun i ↦ evaluate rho (generatorCoboundary s i) x)
  rw [matrixEnergy_hodge_coboundary_eq
      (generatorCoboundary s) B C.chain rho x,
    ← generatorLaplacianOperator_apply_eq_evaluate] at hgap
  simpa only [familyNormSq, evaluate_generatorCoboundary,
    generatorLaplacian_energy] using hgap

/-- Norm of the generator Laplacian is bounded by twice the sum of the
generator displacements. -/
theorem norm_generatorLaplacian_le_two_sum
    {I : Type*} [Fintype I] (s : I → G)
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    ‖generatorLaplacianOperator s rho x‖ ≤
      2 * ∑ i, ‖rho (s i) x - x‖ := by
  rw [generatorLaplacianOperator_apply]
  calc
    ‖∑ i, (rho (s i)⁻¹ (rho (s i) x - x) -
        (rho (s i) x - x))‖ ≤
        ∑ i, ‖rho (s i)⁻¹ (rho (s i) x - x) -
          (rho (s i) x - x)‖ := norm_sum_le _ _
    _ ≤ ∑ i, 2 * ‖rho (s i) x - x‖ := by
      apply Finset.sum_le_sum
      intro i hi
      exact norm_generatorLaplacian_summand_le rho (s i) x
    _ = 2 * ∑ i, ‖rho (s i) x - x‖ := by
      rw [Finset.mul_sum]

/-! ## The certified Kazhdan pair -/

/-- Explicit Kazhdan tolerance extracted from an exact certificate.

The maximum in the denominator makes the construction unconditional: no
separate comparison between the certified gap and the universal Laplacian
upper bound is required. -/
noncomputable def certifiedKazhdanTolerance
    {I : Type*} [Fintype I] (c r : ℚ) : ℝ :=
  let gamma : ℝ := ((c - r : ℚ) : ℝ)
  let upper : ℝ := max gamma (4 * (Fintype.card I : ℝ))
  gamma * (1 - Real.sqrt (1 - gamma / upper)) /
    (2 * (Fintype.card I : ℝ))

/-- The finite control set underlying a finite generator tuple. -/
noncomputable def generatorFinset
    {I : Type*} [Fintype I] (s : I → G) : Finset G := by
  classical
  exact Finset.univ.image s

/-- An exact rational Hodge certificate for a finite generating tuple gives
an explicit Kazhdan pair.  The certificate contains only finite group-ring
identities and rational coefficient-`ℓ1` bounds; all Hilbert-space
positivity and displacement estimates are proved here. -/
theorem Certificate.isKazhdanPair
    {I J K : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [Fintype K] (hI : Nonempty I)
    (s : I → G) (hgen : Subgroup.closure (Set.range s) = ⊤)
    {B : J → I → RatGroupRing G}
    {q : K → I → RatGroupRing G}
    {R : I → I → RatGroupRing G} {c r : ℚ}
    (C : Certificate (generatorCoboundary s) B q R c r) :
    IsKazhdanPair.{u, v} G (generatorFinset s)
      (certifiedKazhdanTolerance (I := I) c r) := by
  classical
  letI : Nonempty I := hI
  let gamma : ℝ := ((c - r : ℚ) : ℝ)
  let generatorUpper : ℝ := 4 * (Fintype.card I : ℝ)
  let upper : ℝ := max gamma generatorUpper
  let spectralLower : ℝ :=
    gamma * (1 - Real.sqrt (1 - gamma / upper))
  let epsilon : ℝ := spectralLower / (2 * (Fintype.card I : ℝ))
  have hgapRat : 0 < c - r := sub_pos.mpr C.gap_pos
  have hgamma : 0 < gamma := by
    dsimp [gamma]
    exact_mod_cast hgapRat
  have hcardNat : 0 < Fintype.card I := Fintype.card_pos
  have hcard : (0 : ℝ) < Fintype.card I := by exact_mod_cast hcardNat
  have hgeneratorUpper : 0 < generatorUpper := by
    dsimp [generatorUpper]
    positivity
  have hgammaUpper : gamma ≤ upper := by
    exact le_max_left _ _
  have hgeneratorUpper_le : generatorUpper ≤ upper := by
    exact le_max_right _ _
  have hupper : 0 < upper :=
    hgeneratorUpper.trans_le hgeneratorUpper_le
  have hratio0 : 0 ≤ 1 - gamma / upper := by
    rw [sub_nonneg, div_le_one hupper]
    exact hgammaUpper
  have hratio1 : 1 - gamma / upper < 1 := by
    exact sub_lt_self _ (div_pos hgamma hupper)
  have hsqrt0 : 0 ≤ Real.sqrt (1 - gamma / upper) := Real.sqrt_nonneg _
  have hsqrtSq : Real.sqrt (1 - gamma / upper) ^ 2 =
      1 - gamma / upper := Real.sq_sqrt hratio0
  have hsqrt1 : Real.sqrt (1 - gamma / upper) < 1 := by
    nlinarith [sq_nonneg (Real.sqrt (1 - gamma / upper) - 1)]
  have hspectralLower : 0 < spectralLower := by
    dsimp [spectralLower]
    exact mul_pos hgamma (sub_pos.mpr hsqrt1)
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    exact div_pos hspectralLower (mul_pos (by norm_num) hcard)
  change IsKazhdanPair.{u, v} G (generatorFinset s) epsilon
  apply IsKazhdanPair.of_noInvariant_displacement_mul_norm hepsilon
  intro E _ _ _ rho hno x hx
  let A : E →L[ℝ] E := generatorLaplacianOperator s rho
  have henergy (y : E) : 0 ≤ PositiveOperatorGap.energy A y := by
    dsimp [A]
    rw [generatorLaplacian_energy]
    exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hformUpper (y : E) :
      PositiveOperatorGap.energy A y ≤ upper * ‖y‖ ^ 2 := by
    calc
      PositiveOperatorGap.energy A y ≤ generatorUpper * ‖y‖ ^ 2 := by
        simpa [A, generatorUpper] using generatorLaplacian_energy_le s rho y
      _ ≤ upper * ‖y‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hgeneratorUpper_le (sq_nonneg _)
  have hnormUpper (y : E) :
      ‖A y‖ ^ 2 ≤ upper * PositiveOperatorGap.energy A y := by
    calc
      ‖A y‖ ^ 2 ≤
          generatorUpper * PositiveOperatorGap.energy A y := by
        simpa [A, generatorUpper] using
          generatorLaplacian_norm_sq_le s rho y
      _ ≤ upper * PositiveOperatorGap.energy A y :=
        mul_le_mul_of_nonneg_right hgeneratorUpper_le (henergy y)
  have hlower (y : E) :
      gamma * PositiveOperatorGap.energy A y ≤ ‖A y‖ ^ 2 := by
    simpa [A, gamma] using C.generatorLaplacian_quadratic_gap s rho y
  have hsymm (y z : E) : inner ℝ (A y) z = inner ℝ y (A z) := by
    exact generatorLaplacian_symmetric s rho y z
  have hker (y : E) (hy : A y = 0) : y = 0 := by
    apply hno y
    exact invariant_of_generatorLaplacian_eq_zero s hgen rho y hy
  have hnorm := PositiveOperatorGap.norm_le_of_quadratic_gap
    A hgamma hupper hgammaUpper hsymm henergy hlower hformUpper
      hnormUpper hker x
  have hspectralNorm : spectralLower * ‖x‖ ≤ ‖A x‖ := by
    calc
      spectralLower * ‖x‖ ≤
          spectralLower * (spectralLower⁻¹ * ‖A x‖) :=
        mul_le_mul_of_nonneg_left (by simpa [spectralLower] using hnorm)
          hspectralLower.le
      _ = ‖A x‖ := by field_simp [ne_of_gt hspectralLower]
  have htotal : spectralLower * ‖x‖ ≤
      2 * ∑ i, ‖rho (s i) x - x‖ := by
    exact hspectralNorm.trans (norm_generatorLaplacian_le_two_sum s rho x)
  have hexists : ∃ i : I,
      epsilon * ‖x‖ ≤ ‖rho (s i) x - x‖ := by
    by_contra h
    have hall (i : I) :
        ‖rho (s i) x - x‖ < epsilon * ‖x‖ :=
      lt_of_not_ge fun hi ↦ h ⟨i, hi⟩
    have hsum :
        (∑ i, ‖rho (s i) x - x‖) <
          ∑ _i : I, epsilon * ‖x‖ :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
        (fun i _ ↦ hall i)
    have hstrict :
        2 * ∑ i, ‖rho (s i) x - x‖ < spectralLower * ‖x‖ := by
      calc
        2 * ∑ i, ‖rho (s i) x - x‖ <
            2 * ∑ _i : I, epsilon * ‖x‖ :=
          mul_lt_mul_of_pos_left hsum (by norm_num)
        _ = spectralLower * ‖x‖ := by
          rw [Finset.sum_const, nsmul_eq_mul]
          dsimp [epsilon]
          field_simp [ne_of_gt hcard]
    exact (not_lt_of_ge htotal) hstrict
  obtain ⟨i, hi⟩ := hexists
  exact ⟨s i, by simp [generatorFinset], hi⟩

/-- An exact rational Hodge certificate for a finite generating tuple proves
Kazhdan's property `(T)`, with no mathematical premise beyond the displayed
finite identities, rational error bounds, and generation. -/
theorem Certificate.hasKazhdanPropertyT
    {I J K : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [Fintype K] (hI : Nonempty I)
    (s : I → G) (hgen : Subgroup.closure (Set.range s) = ⊤)
    {B : J → I → RatGroupRing G}
    {q : K → I → RatGroupRing G}
    {R : I → I → RatGroupRing G} {c r : ℚ}
    (C : Certificate (generatorCoboundary s) B q R c r) :
    HasKazhdanPropertyT.{u, v} G :=
  ⟨generatorFinset s, certifiedKazhdanTolerance (I := I) c r,
    C.isKazhdanPair hI s hgen⟩

end ExactHodgeCertificate
end GroupApproximation
