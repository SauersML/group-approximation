import GroupApproximation.Sofic.InvolutionRankMass

/-!
# Flattening and rigidity tools for involution microstates

Two pieces of glue between the matrix side and the Hilbert-geometry side
of the compression-collapse argument.

* The **flattening isometry** `flatE` realizes a complex matrix as a
  Euclidean vector whose squared norm is the unnormalized Frobenius mass
  `matMass`.  All circumcenter geometry runs in the flattened picture,
  where the genuine norm triangle inequality is available (the matrix-side
  kit only has the crude `matMass_add_le`).

* The **rigidity of commuting exact involutions**: two commuting exact
  involutions at operator distance below `2` are equal.  Their difference
  `T` satisfies `T * T = 4 • halfSqProjection`, so a nonzero difference
  moves some vector by a factor `4` under `T * T`, forcing `2 ≤ ‖T‖`.
  This converts corona-level identities into eventual exact equalities of
  corrected microstates, with no spectral theory.
-/

namespace GroupApproximation
namespace InvolutionMicrostateTools

open Matrix InvolutionRankMass KazhdanCornerMatrices
open scoped Matrix.Norms.L2Operator

/-! ## The flattening isometry -/

/-- A matrix as a Euclidean vector in row-major coordinates. -/
noncomputable def flatE {Y : Type*} [Fintype Y] (X : Matrix Y Y ℂ) :
    EuclideanSpace ℂ (Y × Y) :=
  (EuclideanSpace.equiv (Y × Y) ℂ).symm (fun p ↦ X p.1 p.2)

theorem flatE_sub {Y : Type*} [Fintype Y] (X Z : Matrix Y Y ℂ) :
    flatE (X - Z) = flatE X - flatE Z := by
  unfold flatE
  rw [show (fun p : Y × Y ↦ (X - Z) p.1 p.2) =
    (fun p : Y × Y ↦ X p.1 p.2) - (fun p : Y × Y ↦ Z p.1 p.2) from rfl,
    map_sub]

theorem flatE_zero {Y : Type*} [Fintype Y] :
    flatE (0 : Matrix Y Y ℂ) = 0 := by
  unfold flatE
  rw [show (fun p : Y × Y ↦ (0 : Matrix Y Y ℂ) p.1 p.2) =
    (0 : (Y × Y) → ℂ) from rfl, map_zero]

theorem flatE_add {Y : Type*} [Fintype Y] (X Z : Matrix Y Y ℂ) :
    flatE (X + Z) = flatE X + flatE Z := by
  unfold flatE
  rw [show (fun p : Y × Y ↦ (X + Z) p.1 p.2) =
    (fun p : Y × Y ↦ X p.1 p.2) + (fun p : Y × Y ↦ Z p.1 p.2) from rfl,
    map_add]

theorem flatE_sum {Y : Type*} [Fintype Y] {ι : Type*} (F : Finset ι)
    (X : ι → Matrix Y Y ℂ) :
    flatE (∑ i ∈ F, X i) = ∑ i ∈ F, flatE (X i) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty, flatE_zero]
  | @insert i F hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, flatE_add, ih]

theorem flatE_smul {Y : Type*} [Fintype Y] (c : ℂ) (X : Matrix Y Y ℂ) :
    flatE (c • X) = c • flatE X := by
  unfold flatE
  rw [show (fun p : Y × Y ↦ (c • X) p.1 p.2) =
    c • (fun p : Y × Y ↦ X p.1 p.2) from rfl, map_smul]

/-- The squared Euclidean norm of a flattened matrix is its Frobenius
mass. -/
theorem norm_flatE_sq {Y : Type*} [Fintype Y] (X : Matrix Y Y ℂ) :
    ‖flatE X‖ ^ 2 = ScaledKazhdanTransport.matMass X := by
  unfold flatE
  rw [euclidean_norm_sq_general]
  show (∑ p : Y × Y, Complex.normSq (X p.1 p.2)) =
    ∑ i : Y, ∑ j : Y, Complex.normSq (X i j)
  rw [Fintype.sum_prod_type]

/-- Distances between flattened matrices measure the Frobenius mass of the
difference. -/
theorem dist_flatE_sq {Y : Type*} [Fintype Y] (X Z : Matrix Y Y ℂ) :
    dist (flatE X) (flatE Z) ^ 2 =
      ScaledKazhdanTransport.matMass (X - Z) := by
  rw [dist_eq_norm, ← flatE_sub, norm_flatE_sq]

/-! ## Rigidity of commuting exact involutions -/

/-- A nonzero matrix moves some vector: the conjugated row witnesses it. -/
theorem exists_mulVec_ne_zero {Y : Type*} [Fintype Y]
    {M : Matrix Y Y ℂ} (hM : M ≠ 0) :
    ∃ v : Y → ℂ, M *ᵥ v ≠ 0 := by
  obtain ⟨i, j, hij⟩ : ∃ i j : Y, M i j ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hM
    ext i j
    simpa using hall i j
  refine ⟨fun k ↦ (starRingEnd ℂ) (M i k), ?_⟩
  intro h0
  have hsum : (M *ᵥ fun k ↦ (starRingEnd ℂ) (M i k)) i =
      ((∑ k : Y, Complex.normSq (M i k) : ℝ) : ℂ) := by
    simp only [Matrix.mulVec, dotProduct]
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun k _ ↦ Complex.mul_conj (M i k)
  have hzero : ((∑ k : Y, Complex.normSq (M i k) : ℝ) : ℂ) = 0 := by
    rw [← hsum, h0]
    rfl
  have hpos : 0 < ∑ k : Y, Complex.normSq (M i k) := by
    have hle : Complex.normSq (M i j) ≤ ∑ k : Y, Complex.normSq (M i k) :=
      Finset.single_le_sum
        (fun k _ ↦ Complex.normSq_nonneg (M i k)) (Finset.mem_univ j)
    have hjpos : 0 < Complex.normSq (M i j) := by
      rw [Complex.normSq_pos]
      exact hij
    linarith
  rw [Complex.ofReal_eq_zero] at hzero
  linarith

/-- Positivity of the coordinate mass of a nonzero vector. -/
theorem sum_normSq_pos_of_ne_zero {Y : Type*} [Fintype Y]
    {v : Y → ℂ} (hv : v ≠ 0) :
    0 < ∑ i : Y, Complex.normSq (v i) := by
  obtain ⟨i, hi⟩ : ∃ i : Y, v i ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hv (funext hall)
  have hpos : 0 < Complex.normSq (v i) := by
    rw [Complex.normSq_pos]
    exact hi
  refine lt_of_lt_of_le hpos ?_
  exact Finset.single_le_sum
    (fun j _ ↦ Complex.normSq_nonneg (v j)) (Finset.mem_univ i)

/-- **Rigidity.**  Distinct commuting exact involutions are at operator
distance at least `2`. -/
theorem two_le_norm_sub_of_ne {Y : Type*} [Fintype Y] [DecidableEq Y]
    {u w : Matrix Y Y ℂ} (hu : IsExactInvolution u)
    (hw : IsExactInvolution w) (hcomm : u * w = w * u) (hne : u ≠ w) :
    2 ≤ ‖u - w‖ := by
  have hT : u - w ≠ 0 := sub_ne_zero.mpr hne
  have hTP : (u - w) * halfSqProjection u w = u - w :=
    sub_mul_halfSqProjection hu hw hcomm
  have hPne : halfSqProjection u w ≠ 0 := by
    intro hP0
    apply hT
    rw [← hTP, hP0, Matrix.mul_zero]
  obtain ⟨x, hx⟩ := exists_mulVec_ne_zero hPne
  set v : Y → ℂ := halfSqProjection u w *ᵥ x with hv
  have hPidem : halfSqProjection u w * halfSqProjection u w =
      halfSqProjection u w :=
    (halfSqProjection_isOrthogonalProjection hu hw hcomm).2
  have hPv : halfSqProjection u w *ᵥ v = v := by
    rw [hv, Matrix.mulVec_mulVec, hPidem]
  have hTsq : (u - w) * (u - w) = (4 : ℂ) • halfSqProjection u w := by
    show _ = (4 : ℂ) • ((4 : ℂ)⁻¹ • ((u - w) * (u - w)))
    rw [smul_smul]
    norm_num
  have hTTv : (u - w) *ᵥ ((u - w) *ᵥ v) = (4 : ℂ) • v := by
    rw [Matrix.mulVec_mulVec, hTsq, Matrix.smul_mulVec, hPv]
  have hmass4 : ∑ i : Y, Complex.normSq (((4 : ℂ) • v) i) =
      16 * ∑ i : Y, Complex.normSq (v i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    show Complex.normSq ((4 : ℂ) * v i) = _
    rw [Complex.normSq_mul]
    norm_num
  have hstep1 : ∑ i : Y, Complex.normSq (((u - w) *ᵥ ((u - w) *ᵥ v)) i) ≤
      ‖u - w‖ ^ 2 * (‖u - w‖ ^ 2 * ∑ i : Y, Complex.normSq (v i)) := by
    calc
      ∑ i : Y, Complex.normSq (((u - w) *ᵥ ((u - w) *ᵥ v)) i) ≤
          ‖u - w‖ ^ 2 * ∑ i : Y, Complex.normSq (((u - w) *ᵥ v) i) :=
        sum_normSq_mulVec_le_general _ _
      _ ≤ ‖u - w‖ ^ 2 * (‖u - w‖ ^ 2 * ∑ i : Y, Complex.normSq (v i)) :=
        mul_le_mul_of_nonneg_left
          (sum_normSq_mulVec_le_general (u - w) v) (sq_nonneg _)
  have hvpos : 0 < ∑ i : Y, Complex.normSq (v i) :=
    sum_normSq_pos_of_ne_zero hx
  have h16 : 16 * ∑ i : Y, Complex.normSq (v i) ≤
      ‖u - w‖ ^ 2 * (‖u - w‖ ^ 2 * ∑ i : Y, Complex.normSq (v i)) := by
    rw [← hmass4, ← hTTv]
    exact hstep1
  have hquad : 16 ≤ ‖u - w‖ ^ 2 * ‖u - w‖ ^ 2 := by
    nlinarith [hvpos, h16]
  have hnorm4 : 4 ≤ ‖u - w‖ ^ 2 := by
    nlinarith [sq_nonneg ‖u - w‖, hquad]
  nlinarith [norm_nonneg (u - w), hnorm4]

/-- **Eventual exactness.**  Commuting exact involutions at operator
distance below `2` are equal.  Operator-norm-vanishing differences of
corrected microstates are therefore eventually exact equalities. -/
theorem eq_of_norm_sub_lt_two {Y : Type*} [Fintype Y] [DecidableEq Y]
    {u w : Matrix Y Y ℂ} (hu : IsExactInvolution u)
    (hw : IsExactInvolution w) (hcomm : u * w = w * u)
    (hlt : ‖u - w‖ < 2) : u = w := by
  by_contra hne
  exact absurd hlt (not_lt.mpr (two_le_norm_sub_of_ne hu hw hcomm hne))

end InvolutionMicrostateTools
end GroupApproximation
