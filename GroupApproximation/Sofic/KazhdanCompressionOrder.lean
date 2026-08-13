import GroupApproximation.Sofic.AdjointMatrix
import GroupApproximation.Sofic.SpectralCapture

/-!
# Kazhdan compression order in finite adjoint models

This file isolates the finite-dimensional stable-finiteness step in the
compressor obstruction.  Let `B` be the adjoint almost-representation of a
Kazhdan subgroup and let `P_n` be its top Kazhdan spectral projection.  If a
unitary `T_n` transports the subgroup action into itself, then

`C_n = T_nᴴ P_n`

is asymptotically fixed by the subgroup average.  Spectral capture makes
`(1-P_n) C_n` vanish.  Equivalently, `P_n` is asymptotically contained in
`T_n P_n T_nᴴ`.  The two projections have exactly equal finite rank, so the
equal-rank projection flip upgrades this to operator-norm convergence of the
projections themselves.

The group-word calculation which supplies the transport hypothesis is kept
separate.  This theorem is the reusable analytic order endpoint.
-/

namespace GroupApproximation
namespace KazhdanCornerMatrices

open Matrix
open scoped Matrix.Norms.L2Operator

variable {G : Type*} [Group G]

/-- The top spectral projection associated with a finite symmetric Kazhdan
generating set. -/
noncomputable def kazhdanTopProjection (A : OpAlmostRepresentation G)
    (S : Finset G) (threshold : ℝ) (n : ℕ) :
    Matrix (A.model n) (A.model n) ℂ :=
  spectralAbove (hermitianAverage A S n)
    (hermitianAverage_conjTranspose A S n) threshold

theorem kazhdanTopProjection_isOrthogonalProjection
    (A : OpAlmostRepresentation G) (S : Finset G) (threshold : ℝ) (n : ℕ) :
    IsOrthogonalProjectionMatrix (kazhdanTopProjection A S threshold n) :=
  spectralAbove_isOrthogonalProjection _ _ _

theorem norm_kazhdanTopProjection_le_one
    (A : OpAlmostRepresentation G) (S : Finset G) (threshold : ℝ) (n : ℕ) :
    ‖kazhdanTopProjection A S threshold n‖ ≤ 1 :=
  norm_spectralAbove_le_one _ _ _

/-- Equal-rank finite projections turn asymptotic one-sided containment into
operator-norm equality. -/
theorem projection_conjugate_vanishing_of_one_sided
    (A : OpAlmostRepresentation G)
    (p : ∀ n, Matrix (A.model n) (A.model n) ℂ)
    (u : ∀ n, Matrix.unitaryGroup (A.model n) ℂ)
    (hp : ∀ n, IsOrthogonalProjectionMatrix (p n))
    (hone : OpNormVanishing A (fun n ↦
      (1 - ((u n : Matrix (A.model n) (A.model n) ℂ) * p n *
        (u n : Matrix (A.model n) (A.model n) ℂ)ᴴ)) * p n)) :
    OpNormVanishing A (fun n ↦
      (u n : Matrix (A.model n) (A.model n) ℂ) * p n *
        (u n : Matrix (A.model n) (A.model n) ℂ)ᴴ - p n) := by
  intro eta heta
  let epsilon : ℝ := min (1 / 2) (eta / 4)
  have hepsilon_pos : 0 < epsilon := lt_min (by norm_num) (div_pos heta (by norm_num))
  have hepsilon_nonneg : 0 ≤ epsilon := hepsilon_pos.le
  have hepsilon_half : epsilon ≤ 1 / 2 := min_le_left _ _
  have hepsilon_one : epsilon < 1 := lt_of_le_of_lt hepsilon_half (by norm_num)
  have hepsilon_eta : 4 * epsilon ≤ eta := by
    have := min_le_right (1 / 2) (eta / 4)
    linarith
  obtain ⟨N, hN⟩ := hone epsilon hepsilon_pos
  refine ⟨N, fun n hn ↦ ?_⟩
  let q : Matrix (A.model n) (A.model n) ℂ :=
    (u n : Matrix (A.model n) (A.model n) ℂ) * p n *
      (u n : Matrix (A.model n) (A.model n) ℂ)ᴴ
  have hq : IsOrthogonalProjectionMatrix q :=
    unitary_conjugate_isOrthogonalProjection (u n).2 (hp n)
  have hrank : (p n).rank = q.rank := by
    rw [rank_unitary_conj (u n).2]
  have hflip := norm_one_sub_mul_flip (hp n) hq hrank
    hepsilon_nonneg hepsilon_one (hN n hn)
  have hsqrt : (1 / 2 : ℝ) ≤ Real.sqrt (1 - epsilon ^ 2) := by
    rw [le_sqrt (by norm_num)]
    constructor
    · nlinarith
    · nlinarith
  have hquot : epsilon / Real.sqrt (1 - epsilon ^ 2) ≤ 2 * epsilon := by
    rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num) hsqrt)]
    nlinarith
  have hreverse : ‖(1 - p n) * q‖ ≤ 2 * epsilon := hflip.trans hquot
  have hdist := norm_proj_sub_le (hp n) hq
  have hqp : ‖q - p n‖ ≤ 3 * epsilon := by
    rw [show q - p n = -(p n - q) by abel, norm_neg]
    exact hdist.trans (by linarith [hN n hn, hreverse])
  exact hqp.trans (by linarith)

/-- **Finite Kazhdan compressor order.**

Let `A` be an almost representation of an ambient group and `iota : G → E`
the Kazhdan subgroup.  On the adjoint matrix models, suppose `compressor`
asymptotically transports every `g` to `alpha g`.  Then conjugation by the
compressor asymptotically preserves the top Kazhdan spectral projection.

The conclusion is in operator norm and is independent of the matrix
dimension. -/
theorem adjoint_compressor_preserves_kazhdanTopProjection
    {E : Type*} [Group E] (A : OpAlmostRepresentation E)
    (iota : G →* E) (alpha : G →* G) (compressor : E)
    {Q : Finset G} {kappa : ℝ}
    (hQ : IsKazhdanPair.{0, 0} G Q kappa)
    (S : Finset G) (hQS : Q ⊆ S) (honeS : 1 ∈ S)
    (hkappaOne : kappa ≤ 1) (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    {threshold : ℝ}
    (hthresholdLower : 1 - kappa ^ 2 / (4 * S.card) < threshold)
    (hthresholdUpper : threshold < 1)
    (htransport : ∀ g : G,
      OpNormVanishing ((A.adjoint).comap iota) (fun n ↦
        (((A.adjoint).comap iota).map n g :
            Matrix (((A.adjoint).comap iota).model n)
              (((A.adjoint).comap iota).model n) ℂ) *
          ((A.adjoint.map n compressor :
            Matrix (A.adjoint.model n) (A.adjoint.model n) ℂ))ᴴ -
          ((A.adjoint.map n compressor :
            Matrix (A.adjoint.model n) (A.adjoint.model n) ℂ))ᴴ *
          (((A.adjoint).comap iota).map n (alpha g) :
            Matrix (((A.adjoint).comap iota).model n)
              (((A.adjoint).comap iota).model n) ℂ))) :
    OpNormVanishing ((A.adjoint).comap iota) (fun n ↦
      let B := (A.adjoint).comap iota
      let P := kazhdanTopProjection B S threshold n
      let U : Matrix (B.model n) (B.model n) ℂ := A.adjoint.map n compressor
      U * P * Uᴴ - P) := by
  classical
  let B : OpAlmostRepresentation G := (A.adjoint).comap iota
  let P : ∀ n, Matrix (B.model n) (B.model n) ℂ := fun n ↦
    kazhdanTopProjection B S threshold n
  let U : ∀ n, Matrix.unitaryGroup (B.model n) ℂ := fun n ↦
    A.adjoint.map n compressor
  let C : ∀ n, Matrix (B.model n) (B.model n) ℂ := fun n ↦
    (U n : Matrix (B.model n) (B.model n) ℂ)ᴴ * P n
  have hPproj : ∀ n, IsOrthogonalProjectionMatrix (P n) := fun n ↦
    kazhdanTopProjection_isOrthogonalProjection B S threshold n
  have hPnorm : ∀ n, ‖P n‖ ≤ 1 := fun n ↦
    norm_kazhdanTopProjection_le_one B S threshold n
  have hUnorm : ∀ n, ‖(U n : Matrix (B.model n) (B.model n) ℂ)‖ ≤ 1 :=
    fun n ↦ (CStarRing.norm_of_mem_unitary (U n).2).le
  have hUstarNorm : ∀ n,
      ‖(U n : Matrix (B.model n) (B.model n) ℂ)ᴴ‖ ≤ 1 := by
    intro n
    rw [← Matrix.star_eq_conjTranspose, norm_star]
    exact hUnorm n
  have hCnorm : ∀ n, ‖C n‖ ≤ 1 := by
    intro n
    calc
      ‖C n‖ ≤
          ‖(U n : Matrix (B.model n) (B.model n) ℂ)ᴴ‖ * ‖P n‖ :=
        Matrix.l2_opNorm_mul _ _
      _ ≤ 1 * 1 := mul_le_mul (hUstarNorm n) (hPnorm n)
        (norm_nonneg _) zero_le_one
      _ = 1 := one_mul _
  have hdisp (g : G) : OpNormVanishing B (fun n ↦
      ((B.map n g : Matrix (B.model n) (B.model n) ℂ) - 1) * P n) := by
    simpa only [topSpectralDisplacement, P, kazhdanTopProjection, B] using
      topSpectralDisplacement_vanishing_of_generates
        hQ S hQS honeS hkappaOne hsymm hgen B hthresholdLower g
  have hfixed (g : G) : OpNormVanishing B (fun n ↦
      ((B.map n g : Matrix (B.model n) (B.model n) ℂ) - 1) * C n) := by
    have ht := (htransport g).mul_right_of_norm_le_one P hPnorm
    have hd := (hdisp (alpha g)).mul_left_of_norm_le_one
      (fun n ↦ (U n : Matrix (B.model n) (B.model n) ℂ)ᴴ) hUstarNorm
    exact (ht.add hd).congr fun n ↦ by
      simp only [C, B, U]
      noncomm_ring
  have hsum : OpNormVanishing B (fun n ↦
      ∑ g ∈ S, ((B.map n g : Matrix (B.model n) (B.model n) ℂ) - 1) * C n) :=
    OpNormVanishing.finset_sum S
      (fun g n ↦ ((B.map n g : Matrix (B.model n) (B.model n) ℂ) - 1) * C n)
      (fun g _ ↦ hfixed g)
  have hmatrix : OpNormVanishing B (fun n ↦
      matrixAverage B S n * C n - C n) := by
    have hs := hsum.smul ((S.card : ℂ)⁻¹)
    exact hs.congr fun n ↦ by
      have hcard : (S.card : ℂ) ≠ 0 := by
        exact_mod_cast (Finset.card_ne_zero.mpr ⟨1, honeS⟩)
      rw [matrixAverage, Matrix.smul_mul, Finset.sum_mul,
        Finset.sum_sub_distrib]
      simp only [Matrix.sub_mul, Matrix.one_mul, Finset.sum_const,
        nsmul_eq_mul, smul_sub, smul_smul]
      have hcoef : (S.card : ℂ)⁻¹ * (S.card : ℂ) = 1 := inv_mul_cancel₀ hcard
      rw [hcoef, one_smul]
  have hhermitian : OpNormVanishing B (fun n ↦
      C n - hermitianAverage B S n * C n) := by
    have hMH := (matrixAverage_sub_hermitian_vanishing B S hsymm).mul_right_of_norm_le_one
      C hCnorm
    exact (hmatrix.neg.add hMH).congr fun n ↦ by
      noncomm_ring
  have hlow : OpNormVanishing B (fun n ↦ (1 - P n) * C n) := by
    intro eta heta
    have honeThreshold : 0 < 1 - threshold := sub_pos.mpr hthresholdUpper
    obtain ⟨N, hN⟩ := hhermitian
      ((1 - threshold) * eta ^ 2)
      (mul_pos honeThreshold (sq_pos_of_pos heta))
    refine ⟨N, fun n hn ↦ ?_⟩
    have hcapture := norm_spectralBelow_mul_sq_le
      (hermitianAverage_conjTranspose B S n)
      (t := threshold) (delta := 0) (by norm_num)
      (by simpa using norm_hermitianAverage_le_one B S n)
      hthresholdUpper (hCnorm n)
    have hbelow : spectralBelow (hermitianAverage B S n)
        (hermitianAverage_conjTranspose B S n) threshold = 1 - P n := rfl
    rw [hbelow] at hcapture
    have hres := hN n hn
    have hsq : ‖(1 - P n) * C n‖ ^ 2 ≤ eta ^ 2 := by
      nlinarith
    nlinarith [norm_nonneg ((1 - P n) * C n)]
  have honeSide : OpNormVanishing B (fun n ↦
      (1 - ((U n : Matrix (B.model n) (B.model n) ℂ) * P n *
        (U n : Matrix (B.model n) (B.model n) ℂ)ᴴ)) * P n) := by
    have hleft := hlow.mul_left_of_norm_le_one
      (fun n ↦ (U n : Matrix (B.model n) (B.model n) ℂ)) hUnorm
    exact hleft.congr fun n ↦ by
      have hUU : (U n : Matrix (B.model n) (B.model n) ℂ) *
          (U n : Matrix (B.model n) (B.model n) ℂ)ᴴ = 1 :=
        Unitary.mul_star_self_of_mem (U n).2
      simp only [C]
      rw [show (1 - (U n : Matrix (B.model n) (B.model n) ℂ) * P n *
          (U n : Matrix (B.model n) (B.model n) ℂ)ᴴ) * P n =
          (U n : Matrix (B.model n) (B.model n) ℂ) *
            ((1 - P n) * ((U n : Matrix (B.model n) (B.model n) ℂ)ᴴ * P n)) by
        noncomm_ring]
  simpa only [B, P, U, kazhdanTopProjection] using
    projection_conjugate_vanishing_of_one_sided B P U hPproj honeSide

end KazhdanCornerMatrices
end GroupApproximation
