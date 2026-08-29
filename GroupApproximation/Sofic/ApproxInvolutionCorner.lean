import GroupApproximation.Sofic.KazhdanCornerMatrices

/-!
# Spectral rounding of an approximate matrix involution

The marked-compression obstruction cuts an operator-norm approximation by the
negative spectral sector of a central involution.  This file supplies the
exact finite-dimensional objects used in that cut.  Quantitative proximity to
the original approximate involution is proved in the subsequent analytic
layer; here the spectral projections and rounded sign are exact.

The local maneuver has substantial prior art.  Slofstra--Vidick,
arXiv:1711.10676, Proposition 2.7, repair an approximate central involution and
compress to its negative eigenspace in normalized Hilbert--Schmidt models.
Bachner--Dogon--Lubotzky, arXiv:2508.17392, Lemmas 2.2--2.3 and
Proposition 2.4, carry out the operator-norm rounding, corner restriction, and
polar-correction pipeline while allowing the matrix dimension to change.  The
proofs below were written directly against mathlib; no external Lean code is
copied.
-/

namespace GroupApproximation
namespace ApproxInvolutionCorner

open Matrix
open scoped Matrix.Norms.L2Operator

variable {Y : Type*}

/-- Hermitian part of a square complex matrix. -/
noncomputable def hermitianPart (U : Matrix Y Y ℂ) : Matrix Y Y ℂ :=
  ((2 : ℂ)⁻¹) • (U + Uᴴ)

/-- The Hermitian part is exactly self-adjoint. -/
theorem hermitianPart_conjTranspose (U : Matrix Y Y ℂ) :
    (hermitianPart U)ᴴ = hermitianPart U := by
  rw [hermitianPart, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
    Matrix.conjTranspose_conjTranspose]
  have hstar : star ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by norm_num
  rw [hstar, add_comm]

/-- The Hermitian part, in Mathlib's predicate form. -/
theorem hermitianPart_isHermitian (U : Matrix Y Y ℂ) :
    (hermitianPart U).IsHermitian :=
  hermitianPart_conjTranspose U

variable [Fintype Y] [DecidableEq Y]

/-- For a unitary matrix, failure to be self-adjoint is exactly its
involution defect.  Right multiplication by `Uᴴ` is isometric. -/
theorem norm_sub_conjTranspose_eq_norm_sq_sub_one
    (U : Matrix Y Y ℂ) (hU : U ∈ Matrix.unitaryGroup Y ℂ) :
    ‖U - Uᴴ‖ = ‖U * U - 1‖ := by
  have hUUstar : U * Uᴴ = 1 :=
    Unitary.mul_star_self_of_mem hU
  have hUstar : Uᴴ ∈ Matrix.unitaryGroup Y ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact Unitary.star_mul_self_of_mem hU
  have hfactor : U - Uᴴ = (U * U - 1) * Uᴴ := by
    calc
      U - Uᴴ = U * (U * Uᴴ) - Uᴴ := by rw [hUUstar, Matrix.mul_one]
      _ = (U * U - 1) * Uᴴ := by noncomm_ring
  rw [hfactor, CStarRing.norm_mul_mem_unitary _ hUstar]

/-- Hermitian symmetrization costs exactly half the operator-norm
involution defect of a unitary. -/
theorem norm_hermitianPart_sub_eq_half_sq_defect
    (U : Matrix Y Y ℂ) (hU : U ∈ Matrix.unitaryGroup Y ℂ) :
    ‖hermitianPart U - U‖ =
      (1 / 2 : ℝ) * ‖U * U - 1‖ := by
  have hrewrite : hermitianPart U - U =
      ((2 : ℂ)⁻¹) • (Uᴴ - U) := by
    rw [hermitianPart]
    module
  rw [hrewrite, norm_smul]
  have hscalar : ‖((2 : ℂ)⁻¹)‖ = (1 / 2 : ℝ) := by norm_num
  rw [hscalar, show Uᴴ - U = -(U - Uᴴ) by abel, norm_neg,
    norm_sub_conjTranspose_eq_norm_sq_sub_one U hU]

/-- The Hermitian part of a unitary is a contraction. -/
theorem norm_hermitianPart_le_one
    (U : Matrix Y Y ℂ) (hU : U ∈ Matrix.unitaryGroup Y ℂ)
    (hY : 0 < Fintype.card Y) :
    ‖hermitianPart U‖ ≤ 1 := by
  letI : Nonempty Y := Fintype.card_pos_iff.mp hY
  rw [hermitianPart, norm_smul]
  have hscalar : ‖((2 : ℂ)⁻¹)‖ = (1 / 2 : ℝ) := by norm_num
  rw [hscalar]
  have hUnorm : ‖U‖ = 1 := CStarRing.norm_of_mem_unitary hU
  have hUstarNorm : ‖Uᴴ‖ = 1 := by
    rw [← Matrix.star_eq_conjTranspose, norm_star, hUnorm]
  calc
    (1 / 2 : ℝ) * ‖U + Uᴴ‖ ≤
        (1 / 2 : ℝ) * (‖U‖ + ‖Uᴴ‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ = 1 := by rw [hUnorm, hUstarNorm]; norm_num

/-- Scalar sign rounding is controlled by the involution defect on the
closed unit interval.  The zero eigenvalue is assigned to the negative
sector, matching `positiveProjection`'s strict threshold. -/
theorem abs_signed_sub_le_abs_sq_sub_one {lambda : ℝ}
    (hlambda : |lambda| ≤ 1) :
    |(if 0 < lambda then 1 else -1) - lambda| ≤
      |lambda ^ 2 - 1| := by
  have hlower : -1 ≤ lambda := (abs_le.mp hlambda).1
  have hupper : lambda ≤ 1 := (abs_le.mp hlambda).2
  have hsq : lambda ^ 2 ≤ 1 := by
    nlinarith only [mul_nonneg
      (show 0 ≤ lambda + 1 by linarith only [hlower])
      (sub_nonneg.mpr hupper)]
  rw [abs_of_nonpos (sub_nonpos.mpr hsq)]
  by_cases hpos : 0 < lambda
  · rw [if_pos hpos, abs_of_nonneg (sub_nonneg.mpr hupper)]
    nlinarith only [hupper, hpos]
  · rw [if_neg hpos, abs_of_nonpos (by linarith only [hlower])]
    nlinarith only [hlower, hpos]

/-- Squaring the Hermitian part averages the involution defect with its
adjoint. -/
theorem hermitianPart_sq_sub_one
    (U : Matrix Y Y ℂ) (hU : U ∈ Matrix.unitaryGroup Y ℂ) :
    hermitianPart U * hermitianPart U - 1 =
      ((4 : ℂ)⁻¹) • ((U * U - 1) + (U * U - 1)ᴴ) := by
  have hUUstar : U * Uᴴ = 1 := Unitary.mul_star_self_of_mem hU
  have hUstarU : Uᴴ * U = 1 := Unitary.star_mul_self_of_mem hU
  have htwo : ((2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by norm_num
  have hfour : ((4 : ℂ)⁻¹) = (1 / 4 : ℂ) := by norm_num
  rw [hermitianPart, htwo, hfour, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_one]
  calc
    ((1 / 2 : ℂ) • (U + Uᴴ)) * ((1 / 2 : ℂ) • (U + Uᴴ)) - 1 =
        (1 / 4 : ℂ) •
          (U * U + U * Uᴴ + Uᴴ * U + Uᴴ * Uᴴ) - 1 := by
            rw [smul_mul_smul_comm]
            norm_num
            rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
            module
    _ = (1 / 4 : ℂ) •
          ((U * U - 1) + (Uᴴ * Uᴴ - 1)) := by
            rw [hUUstar, hUstarU]
            module

/-- The Hermitian square defect is at most half the unitary involution
defect. -/
theorem norm_hermitianPart_sq_sub_one_le_half
    (U : Matrix Y Y ℂ) (hU : U ∈ Matrix.unitaryGroup Y ℂ) :
    ‖hermitianPart U * hermitianPart U - 1‖ ≤
      (1 / 2 : ℝ) * ‖U * U - 1‖ := by
  rw [hermitianPart_sq_sub_one U hU, norm_smul]
  have hscalar : ‖((4 : ℂ)⁻¹)‖ = (1 / 4 : ℝ) := by norm_num
  rw [hscalar]
  calc
    (1 / 4 : ℝ) * ‖(U * U - 1) + (U * U - 1)ᴴ‖ ≤
        (1 / 4 : ℝ) *
          (‖U * U - 1‖ + ‖(U * U - 1)ᴴ‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ = (1 / 2 : ℝ) * ‖U * U - 1‖ := by
      rw [← Matrix.star_eq_conjTranspose, norm_star]
      ring

/-- Squaring an eigenvalue of a Hermitian matrix cannot produce a larger
defect from `1` than the operator norm of the squared matrix defect. -/
theorem abs_hermitianEigenvalue_sq_sub_one_le
    (H : Matrix Y Y ℂ) (hH : H.IsHermitian) (i : Y) :
    |(hH.eigenvalues i) ^ 2 - 1| ≤ ‖H * H - 1‖ := by
  let x : EuclideanSpace ℂ Y := hH.eigenvectorBasis i
  have hx : ‖x‖ = 1 := hH.eigenvectorBasis.orthonormal.1 i
  have hi : H *ᵥ (x : Y → ℂ) =
      ((hH.eigenvalues i : ℝ) : ℂ) • (x : Y → ℂ) :=
    hH.mulVec_eigenvectorBasis i
  have heigen :
      (Matrix.toEuclideanCLM (n := Y) (𝕜 := ℂ)) (H * H - 1) x =
        (((hH.eigenvalues i) ^ 2 - 1 : ℝ) : ℂ) • x := by
    apply PiLp.ext
    intro j
    change ((H * H - 1) *ᵥ (x : Y → ℂ)) j =
      (((((hH.eigenvalues i) ^ 2 - 1 : ℝ) : ℂ) •
        (x : Y → ℂ)) j)
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hi,
      mulVec_smul, hi]
    simp
    ring
  have happly := ContinuousLinearMap.le_opNorm
    ((Matrix.toEuclideanCLM (n := Y) (𝕜 := ℂ)) (H * H - 1)) x
  rw [heigen, norm_smul, hx, mul_one,
    Matrix.l2_opNorm_toEuclideanCLM] at happly
  calc
    |(hH.eigenvalues i) ^ 2 - 1| =
        ‖((((hH.eigenvalues i) ^ 2 - 1 : ℝ) : ℂ))‖ := by
          rw [Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ‖H * H - 1‖ := by simpa only [mul_one] using happly

/-- Every Hermitian eigenvalue is bounded by the matrix operator norm. -/
theorem abs_hermitianEigenvalue_le_norm
    (H : Matrix Y Y ℂ) (hH : H.IsHermitian) (i : Y) :
    |hH.eigenvalues i| ≤ ‖H‖ := by
  let x : EuclideanSpace ℂ Y := hH.eigenvectorBasis i
  have hx : ‖x‖ = 1 := hH.eigenvectorBasis.orthonormal.1 i
  have heigen :
      (Matrix.toEuclideanCLM (n := Y) (𝕜 := ℂ)) H x =
        ((hH.eigenvalues i : ℝ) : ℂ) • x :=
    PiLp.ext fun j ↦ congrFun (hH.mulVec_eigenvectorBasis i) j
  have happly := ContinuousLinearMap.le_opNorm
    ((Matrix.toEuclideanCLM (n := Y) (𝕜 := ℂ)) H) x
  rw [heigen, norm_smul, hx, mul_one,
    Matrix.l2_opNorm_toEuclideanCLM] at happly
  calc
    |hH.eigenvalues i| = ‖((hH.eigenvalues i : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ‖H‖ := by simpa only [mul_one] using happly

/-- Positive spectral projection of the Hermitian part, with threshold zero. -/
noncomputable def positiveProjection (U : Matrix Y Y ℂ) : Matrix Y Y ℂ :=
  KazhdanCornerMatrices.spectralAbove (hermitianPart U)
    (hermitianPart_isHermitian U) 0

/-- Negative spectral projection, complementary to `positiveProjection`. -/
noncomputable def negativeProjection (U : Matrix Y Y ℂ) : Matrix Y Y ℂ :=
  1 - positiveProjection U

/-- Exact sign of the Hermitian part: `+1` on the positive sector and `-1`
on its complement. -/
noncomputable def roundedInvolution (U : Matrix Y Y ℂ) : Matrix Y Y ℂ :=
  (2 : ℂ) • positiveProjection U - 1

/-- The rounded sign differs from the Hermitian part by no more than the
Hermitian square defect. -/
theorem norm_roundedInvolution_sub_hermitianPart_le
    (U : Matrix Y Y ℂ) (hU : U ∈ Matrix.unitaryGroup Y ℂ)
    (hY : 0 < Fintype.card Y) :
    ‖roundedInvolution U - hermitianPart U‖ ≤
      ‖hermitianPart U * hermitianPart U - 1‖ := by
  let H : Matrix Y Y ℂ := hermitianPart U
  let hH : H.IsHermitian := hermitianPart_isHermitian U
  let V : Matrix Y Y ℂ := hH.eigenvectorUnitary
  let P : Matrix Y Y ℂ :=
    Matrix.diagonal (fun i ↦ if 0 < hH.eigenvalues i then 1 else 0)
  let L : Matrix Y Y ℂ :=
    Matrix.diagonal (fun i ↦ (hH.eigenvalues i : ℂ))
  let R : Matrix Y Y ℂ :=
    Matrix.diagonal (fun i ↦
      (((if 0 < hH.eigenvalues i then 1 else -1) -
        hH.eigenvalues i : ℝ) : ℂ))
  have hVstarV : Vᴴ * V = 1 :=
    Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
  have hVVstar : V * Vᴴ = 1 :=
    Unitary.mul_star_self_of_mem hH.eigenvectorUnitary.2
  have hHdiag : H = V * L * Vᴴ := by
    calc
      H = Unitary.conjStarAlgAut ℂ _ hH.eigenvectorUnitary
          (Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues)) :=
        hH.spectral_theorem
      _ = V * L * Vᴴ := by rfl
  have hPdef : positiveProjection U = V * P * Vᴴ := by
    rfl
  have hcore : (2 : ℂ) • P - 1 - L = R := by
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases hi : 0 < hH.eigenvalues i
      · simp [P, L, R, hi]
        norm_num
      · simp [P, L, R, hi]
    · simp [P, L, R, hij]
  have hrewrite : roundedInvolution U - hermitianPart U = V * R * Vᴴ := by
    rw [roundedInvolution, hPdef]
    change (2 : ℂ) • (V * P * Vᴴ) - 1 - H = V * R * Vᴴ
    rw [hHdiag, show (1 : Matrix Y Y ℂ) = V * Vᴴ by exact hVVstar.symm]
    calc
      (2 : ℂ) • (V * P * Vᴴ) - V * Vᴴ - V * L * Vᴴ =
          V * ((2 : ℂ) • P - 1 - L) * Vᴴ := by
            have hsmul : (2 : ℂ) • (V * P * Vᴴ) =
                V * ((2 : ℂ) • P) * Vᴴ := by
              rw [Matrix.mul_smul, Matrix.smul_mul]
            rw [hsmul]
            noncomm_ring
      _ = V * R * Vᴴ := by rw [hcore]
  have hVstar : Vᴴ ∈ Matrix.unitaryGroup Y ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact hVstarV
  rw [hrewrite, CStarRing.norm_mul_mem_unitary _ hVstar,
    CStarRing.norm_mem_unitary_mul _ hH.eigenvectorUnitary.2]
  change ‖R‖ ≤ ‖H * H - 1‖
  change ‖Matrix.diagonal (fun i ↦
    (((if 0 < hH.eigenvalues i then 1 else -1) -
      hH.eigenvalues i : ℝ) : ℂ))‖ ≤ ‖H * H - 1‖
  rw [Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i ↦ ?_
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact (abs_signed_sub_le_abs_sq_sub_one
      ((abs_hermitianEigenvalue_le_norm H hH i).trans
        (norm_hermitianPart_le_one U hU hY))).trans
    (abs_hermitianEigenvalue_sq_sub_one_le H hH i)

/-- **Dimension-free involution rounding.**  For a unitary matrix, the exact
rounded symmetry is within the original operator-norm involution defect. -/
theorem norm_roundedInvolution_sub_le_sq_defect
    (U : Matrix Y Y ℂ) (hU : U ∈ Matrix.unitaryGroup Y ℂ)
    (hY : 0 < Fintype.card Y) :
    ‖roundedInvolution U - U‖ ≤ ‖U * U - 1‖ := by
  have hsplit : roundedInvolution U - U =
      (roundedInvolution U - hermitianPart U) +
        (hermitianPart U - U) := by abel
  rw [hsplit]
  calc
    ‖(roundedInvolution U - hermitianPart U) +
        (hermitianPart U - U)‖ ≤
        ‖roundedInvolution U - hermitianPart U‖ +
          ‖hermitianPart U - U‖ := norm_add_le _ _
    _ ≤ ‖hermitianPart U * hermitianPart U - 1‖ +
          (1 / 2 : ℝ) * ‖U * U - 1‖ :=
      add_le_add (norm_roundedInvolution_sub_hermitianPart_le U hU hY)
        (le_of_eq (norm_hermitianPart_sub_eq_half_sq_defect U hU))
    _ ≤ (1 / 2 : ℝ) * ‖U * U - 1‖ +
          (1 / 2 : ℝ) * ‖U * U - 1‖ :=
      add_le_add (norm_hermitianPart_sq_sub_one_le_half U hU) le_rfl
    _ = ‖U * U - 1‖ := by ring

/-- The negative projection is `(1-Z)/2` for the rounded involution `Z`. -/
theorem negativeProjection_eq_one_sub_rounded (U : Matrix Y Y ℂ) :
    negativeProjection U =
      ((2 : ℂ)⁻¹) • (1 - roundedInvolution U) := by
  simp [negativeProjection, roundedInvolution]
  module

/-- A vanishing negative sector forces the rounded involution to be the
identity. -/
theorem roundedInvolution_eq_one_of_negativeProjection_eq_zero
    (U : Matrix Y Y ℂ) (hneg : negativeProjection U = 0) :
    roundedInvolution U = 1 := by
  have h := negativeProjection_eq_one_sub_rounded U
  rw [hneg] at h
  have hscalar : ((2 : ℂ)⁻¹) ≠ 0 := by norm_num
  have hone : 1 - roundedInvolution U = 0 :=
    (smul_eq_zero.mp h.symm).resolve_left hscalar
  exact (sub_eq_zero.mp hone).symm

section AlmostRepresentation

variable {G : Type*} [Group G]

/-- Rounding the image of a group involution changes an operator-norm almost
representation by a vanishing amount. -/
theorem roundedInvolution_sub_map_vanishing
    (A : OpAlmostRepresentation G) {z : G} (hz : z * z = 1) :
    KazhdanCornerMatrices.OpNormVanishing A (fun n ↦
      roundedInvolution
          (A.map n z : Matrix (A.model n) (A.model n) ℂ) -
        (A.map n z : Matrix (A.model n) (A.model n) ℂ)) := by
  have hmul := KazhdanCornerMatrices.multiplicativeDefect_vanishing A z z
  have hone := KazhdanCornerMatrices.map_one_vanishing A
  have hsq : KazhdanCornerMatrices.OpNormVanishing A (fun n ↦
      (A.map n z : Matrix (A.model n) (A.model n) ℂ) * A.map n z - 1) := by
    apply hmul.neg.add hone |>.congr
    intro n
    rw [hz]
    noncomm_ring
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := hsq epsilon hepsilon
  refine ⟨N, fun n hn ↦ ?_⟩
  exact (norm_roundedInvolution_sub_le_sq_defect
    (A.map n z : Matrix (A.model n) (A.model n) ℂ)
    (A.map n z).2 (A.modelNonempty n)).trans (hN n hn)

/-- Separation of a nontrivial central involution forces its rounded
negative spectral sector to be nonzero eventually. -/
theorem negativeProjection_eventually_ne_zero_of_separated
    (A : OpAlmostRepresentation G) {z : G} (hz : z * z = 1)
    {delta : ℝ} (hdelta : 0 < delta)
    (hsep : ∃ N, ∀ n ≥ N,
      delta ≤ ‖(A.map n z : Matrix (A.model n) (A.model n) ℂ) - A.map n 1‖) :
    ∃ N, ∀ n ≥ N,
      negativeProjection
        (A.map n z : Matrix (A.model n) (A.model n) ℂ) ≠ 0 := by
  have hround := roundedInvolution_sub_map_vanishing A hz
  have hone := KazhdanCornerMatrices.map_one_vanishing A
  obtain ⟨Nr, hNr⟩ := hround (delta / 4) (by positivity)
  obtain ⟨N1, hN1⟩ := hone (delta / 4) (by positivity)
  obtain ⟨Ns, hNs⟩ := hsep
  refine ⟨max (max Nr N1) Ns, fun n hn hzero ↦ ?_⟩
  have hnNr : Nr ≤ n := (le_max_left Nr N1).trans
    ((le_max_left (max Nr N1) Ns).trans hn)
  have hnN1 : N1 ≤ n := (le_max_right Nr N1).trans
    ((le_max_left (max Nr N1) Ns).trans hn)
  have hnNs : Ns ≤ n := (le_max_right (max Nr N1) Ns).trans hn
  have hZ : roundedInvolution
      (A.map n z : Matrix (A.model n) (A.model n) ℂ) = 1 :=
    roundedInvolution_eq_one_of_negativeProjection_eq_zero _ hzero
  have hsplit :
      (A.map n z : Matrix (A.model n) (A.model n) ℂ) -
          (A.map n 1 : Matrix (A.model n) (A.model n) ℂ) =
        ((A.map n z : Matrix (A.model n) (A.model n) ℂ) -
          roundedInvolution
            (A.map n z : Matrix (A.model n) (A.model n) ℂ)) +
        (1 - (A.map n 1 : Matrix (A.model n) (A.model n) ℂ)) := by
    rw [hZ]
    noncomm_ring
  have hstrict :
      ‖(A.map n z : Matrix (A.model n) (A.model n) ℂ) - A.map n 1‖ <
        delta := by
    rw [hsplit]
    calc
      ‖((A.map n z : Matrix (A.model n) (A.model n) ℂ) -
          roundedInvolution
            (A.map n z : Matrix (A.model n) (A.model n) ℂ)) +
          (1 - (A.map n 1 : Matrix (A.model n) (A.model n) ℂ))‖ ≤
          ‖(A.map n z : Matrix (A.model n) (A.model n) ℂ) -
            roundedInvolution
              (A.map n z : Matrix (A.model n) (A.model n) ℂ)‖ +
          ‖1 - (A.map n 1 : Matrix (A.model n) (A.model n) ℂ)‖ :=
        norm_add_le _ _
      _ ≤ delta / 4 + delta / 4 := by
        apply add_le_add
        · rw [show (A.map n z : Matrix (A.model n) (A.model n) ℂ) -
              roundedInvolution
                (A.map n z : Matrix (A.model n) (A.model n) ℂ) =
            -(roundedInvolution
                (A.map n z : Matrix (A.model n) (A.model n) ℂ) -
              (A.map n z : Matrix (A.model n) (A.model n) ℂ)) by abel,
            norm_neg]
          exact hNr n hnNr
        · rw [show 1 - (A.map n 1 : Matrix (A.model n) (A.model n) ℂ) =
            -((A.map n 1 : Matrix (A.model n) (A.model n) ℂ) - 1) by abel,
            norm_neg]
          exact hN1 n hnN1
      _ < delta := by linarith only [hdelta]
  exact (not_lt_of_ge (hNs n hnNs)) hstrict

/-- An exact commutation relation in the group becomes operator-norm
commutation of the corresponding almost-representation matrices. -/
theorem map_commute_vanishing
    (A : OpAlmostRepresentation G) {z g : G} (hcomm : z * g = g * z) :
    KazhdanCornerMatrices.OpNormVanishing A (fun n ↦
      (A.map n z : Matrix (A.model n) (A.model n) ℂ) *
          (A.map n g : Matrix (A.model n) (A.model n) ℂ) -
        (A.map n g : Matrix (A.model n) (A.model n) ℂ) *
          (A.map n z : Matrix (A.model n) (A.model n) ℂ)) := by
  have hzg :=
    (KazhdanCornerMatrices.multiplicativeDefect_vanishing A z g).neg
  have hgz := KazhdanCornerMatrices.multiplicativeDefect_vanishing A g z
  apply hzg.add hgz |>.congr
  intro n
  rw [hcomm]
  noncomm_ring

/-- Rounding a central involution preserves asymptotic commutation with each
fixed group element. -/
theorem roundedInvolution_commute_map_vanishing
    (A : OpAlmostRepresentation G) {z g : G} (hz : z * z = 1)
    (hcomm : z * g = g * z) :
    KazhdanCornerMatrices.OpNormVanishing A (fun n ↦
      roundedInvolution
          (A.map n z : Matrix (A.model n) (A.model n) ℂ) *
            (A.map n g : Matrix (A.model n) (A.model n) ℂ) -
        (A.map n g : Matrix (A.model n) (A.model n) ℂ) *
          roundedInvolution
            (A.map n z : Matrix (A.model n) (A.model n) ℂ)) := by
  let U : ∀ n, Matrix (A.model n) (A.model n) ℂ := fun n ↦ A.map n z
  let V : ∀ n, Matrix (A.model n) (A.model n) ℂ := fun n ↦ A.map n g
  let Z : ∀ n, Matrix (A.model n) (A.model n) ℂ := fun n ↦
    roundedInvolution (A.map n z)
  have hround : KazhdanCornerMatrices.OpNormVanishing A (fun n ↦ Z n - U n) :=
    roundedInvolution_sub_map_vanishing A hz
  have hleft := hround.mul_right_of_norm_le_one V (fun n ↦ by
    letI : Nonempty (A.model n) := Fintype.card_pos_iff.mp (A.modelNonempty n)
    exact le_of_eq (CStarRing.norm_of_mem_unitary (A.map n g).2))
  have hmiddle : KazhdanCornerMatrices.OpNormVanishing A (fun n ↦
      U n * V n - V n * U n) := map_commute_vanishing A hcomm
  have hright := hround.neg.mul_left_of_norm_le_one V (fun n ↦ by
    letI : Nonempty (A.model n) := Fintype.card_pos_iff.mp (A.modelNonempty n)
    exact le_of_eq (CStarRing.norm_of_mem_unitary (A.map n g).2))
  apply (hleft.add hmiddle |>.add hright).congr
  intro n
  dsimp [U, V, Z]
  noncomm_ring

end AlmostRepresentation

end ApproxInvolutionCorner
end GroupApproximation
