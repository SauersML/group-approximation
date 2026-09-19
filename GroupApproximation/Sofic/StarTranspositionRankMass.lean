import GroupApproximation.Sofic.InvolutionRankMass

/-!
# The rank--mass identity for two star transpositions

Two distinct transpositions sharing one endpoint satisfy the braid relation.
In every unitary representation their images are self-adjoint involutions
`u,w` with `u w u = w u w`.  This file proves algebraically that every
nonzero singular value of `u-w` is `sqrt 3`, in the rank--mass form needed by
finite-packet self-normalization:

`matMass (u-w) = 3 * rank (u-w)`.

No character theory or classification of irreducible representations is
used, so the result applies in every matrix dimension at once.
-/

namespace GroupApproximation
namespace StarTranspositionRankMass

open Matrix InvolutionRankMass
open KazhdanCornerMatrices
open ScaledKazhdanTransport
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- The support projection of the displacement of a braided involution pair. -/
def thirdSqProjection (u w : Matrix Y Y ℂ) : Matrix Y Y ℂ :=
  (3 : ℂ)⁻¹ • ((u - w) * (u - w))

/-- The displacement of braided involutions satisfies `D³ = 3D`. -/
theorem sub_cube_eq_three_smul
    {u w : Matrix Y Y ℂ} (hu : IsExactInvolution u)
    (hw : IsExactInvolution w) (hbraid : u * w * u = w * u * w) :
    (u - w) * (u - w) * (u - w) = (3 : ℂ) • (u - w) := by
  have hexp : (u - w) * (u - w) * (u - w) =
      u * u * u - u * u * w - u * w * u + u * w * w -
        w * u * u + w * u * w + w * w * u - w * w * w := by
    noncomm_ring
  have hbraid' : u * (w * u) = w * (u * w) := by
    simpa only [Matrix.mul_assoc] using hbraid
  rw [hexp]
  simp only [Matrix.mul_assoc, hu.2, hw.2, one_mul, mul_one, hbraid']
  module

/-- The normalized square displacement is self-adjoint. -/
theorem thirdSqProjection_conjTranspose
    {u w : Matrix Y Y ℂ} (hu : IsExactInvolution u)
    (hw : IsExactInvolution w) :
    (thirdSqProjection u w)ᴴ = thirdSqProjection u w := by
  unfold thirdSqProjection
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_sub, hu.1, hw.1]
  norm_num

/-- The normalized square displacement is idempotent. -/
theorem thirdSqProjection_mul_self
    {u w : Matrix Y Y ℂ} (hu : IsExactInvolution u)
    (hw : IsExactInvolution w) (hbraid : u * w * u = w * u * w) :
    thirdSqProjection u w * thirdSqProjection u w =
      thirdSqProjection u w := by
  let D : Matrix Y Y ℂ := u - w
  have hcube : D * D * D = (3 : ℂ) • D :=
    sub_cube_eq_three_smul hu hw hbraid
  have hfour : (D * D) * (D * D) = (3 : ℂ) • (D * D) := by
    calc
      (D * D) * (D * D) = (D * D * D) * D := by noncomm_ring
      _ = ((3 : ℂ) • D) * D := by rw [hcube]
      _ = (3 : ℂ) • (D * D) := by rw [smul_mul_assoc]
  change ((3 : ℂ)⁻¹ • (D * D)) * ((3 : ℂ)⁻¹ • (D * D)) =
    (3 : ℂ)⁻¹ • (D * D)
  calc
    ((3 : ℂ)⁻¹ • (D * D)) * ((3 : ℂ)⁻¹ • (D * D)) =
        ((3 : ℂ)⁻¹ * (3 : ℂ)⁻¹) • ((D * D) * (D * D)) := by
          rw [smul_mul_assoc, mul_smul_comm, smul_smul]
    _ = ((3 : ℂ)⁻¹ * (3 : ℂ)⁻¹) • ((3 : ℂ) • (D * D)) := by
      rw [hfour]
    _ = (3 : ℂ)⁻¹ • (D * D) := by
      rw [smul_smul]
      norm_num

/-- The normalized square displacement is an orthogonal projection. -/
theorem thirdSqProjection_isOrthogonalProjection
    {u w : Matrix Y Y ℂ} (hu : IsExactInvolution u)
    (hw : IsExactInvolution w) (hbraid : u * w * u = w * u * w) :
    IsOrthogonalProjectionMatrix (thirdSqProjection u w) :=
  ⟨thirdSqProjection_conjTranspose hu hw,
    thirdSqProjection_mul_self hu hw hbraid⟩

/-- The support projection acts as the identity on the displacement. -/
theorem sub_mul_thirdSqProjection
    {u w : Matrix Y Y ℂ} (hu : IsExactInvolution u)
    (hw : IsExactInvolution w) (hbraid : u * w * u = w * u * w) :
    (u - w) * thirdSqProjection u w = u - w := by
  have hcube := sub_cube_eq_three_smul hu hw hbraid
  unfold thirdSqProjection
  rw [Matrix.mul_smul]
  calc
    (3 : ℂ)⁻¹ • ((u - w) * ((u - w) * (u - w))) =
        (3 : ℂ)⁻¹ • (((u - w) * (u - w)) * (u - w)) := by
          congr 1
          noncomm_ring
    _ = (3 : ℂ)⁻¹ • ((3 : ℂ) • (u - w)) := by rw [hcube]
    _ = u - w := by rw [smul_smul]; norm_num

/-- The support projection and the displacement have equal rank. -/
theorem rank_thirdSqProjection
    {u w : Matrix Y Y ℂ} (hu : IsExactInvolution u)
    (hw : IsExactInvolution w) (hbraid : u * w * u = w * u * w) :
    (thirdSqProjection u w).rank = (u - w).rank := by
  apply le_antisymm
  · have hfac : thirdSqProjection u w =
        (u - w) * ((3 : ℂ)⁻¹ • (u - w)) := by
      unfold thirdSqProjection
      rw [Matrix.mul_smul]
    rw [hfac]
    exact Matrix.rank_mul_le_left _ _
  · calc
      (u - w).rank = ((u - w) * thirdSqProjection u w).rank := by
        rw [sub_mul_thirdSqProjection hu hw hbraid]
      _ ≤ (thirdSqProjection u w).rank := Matrix.rank_mul_le_right _ _

/-- **The explicit `sqrt 3` spectral floor, in squared-mass form.** -/
theorem matMass_sub_eq_three_mul_rank
    {u w : Matrix Y Y ℂ} (hu : IsExactInvolution u)
    (hw : IsExactInvolution w) (hbraid : u * w * u = w * u * w) :
    matMass (u - w) = 3 * ((u - w).rank : ℝ) := by
  have hDstar : (u - w)ᴴ = u - w := by
    rw [Matrix.conjTranspose_sub, hu.1, hw.1]
  have hsq : (u - w) * (u - w) =
      (3 : ℂ) • thirdSqProjection u w := by
    unfold thirdSqProjection
    rw [smul_smul]
    norm_num
  calc
    matMass (u - w) = (((u - w)ᴴ * (u - w)).trace).re :=
      matMass_eq_re_trace_conjTranspose_mul _
    _ = (((3 : ℂ) • thirdSqProjection u w).trace).re := by
      rw [hDstar, hsq]
    _ = ((3 : ℂ) * (thirdSqProjection u w).trace).re := by
      rw [Matrix.trace_smul, smul_eq_mul]
    _ = 3 * ((thirdSqProjection u w).trace).re := by
      rw [Complex.mul_re]
      norm_num
    _ = 3 * ((thirdSqProjection u w).rank : ℝ) :=
      congrArg (fun x : ℝ ↦ 3 * x)
        (re_trace_eq_rank_of_isOrthogonalProjection
          (thirdSqProjection_isOrthogonalProjection hu hw hbraid))
    _ = 3 * ((u - w).rank : ℝ) := by
      rw [rank_thirdSqProjection hu hw hbraid]

end

end StarTranspositionRankMass
end GroupApproximation
