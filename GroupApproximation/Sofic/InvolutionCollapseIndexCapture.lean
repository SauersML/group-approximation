import GroupApproximation.Sofic.InvolutionCollapseCenter

/-!
# Per-index spectral capture for the collapse finale

The transport finale of the collapse argument runs at a single large
stage, where limit-level smallness and cofinite corner estimates hold
simultaneously.  This file provides the two per-index estimates it needs:

* `sqrt_residual_mass_le`: the Frobenius mass of the Hermitian Kazhdan
  average residual of a matrix is controlled by the largest generator
  displacement mass — via the flattening triangle inequality, with the
  reverse displacements reduced to the forward ones by unitary
  invariance;
* `index_capture`: the mass of the corner-complement compression of a
  flattened matrix is controlled by its total mass and its residual mass,
  by the vector spectral capture inequality — a stage-fixed, fully
  quantitative form of spectral capture.
-/

namespace GroupApproximation
namespace InvolutionCollapseIndexCapture

open Matrix KazhdanCornerMatrices KazhdanCompressorCorner
open InvolutionMicrostateTools
open scoped Matrix.Norms.L2Operator

variable {Γ E : Type} [Group Γ] [Group E]

/-- The reverse displacement has the same Frobenius mass as the forward
displacement. -/
theorem matMass_reverse_displacement
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    {U : Matrix Y Y ℂ} (hU : U ∈ Matrix.unitaryGroup Y ℂ)
    (X : Matrix Y Y ℂ) :
    ScaledKazhdanTransport.matMass (X - Uᴴ * X * U) =
      ScaledKazhdanTransport.matMass (X - U * X * Uᴴ) := by
  have hUU : U * Uᴴ = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp hU
    rwa [Matrix.star_eq_conjTranspose] at h
  have hconj : U * (X - Uᴴ * X * U) * Uᴴ = U * X * Uᴴ - X := by
    have hleft : U * (Uᴴ * X * U) * Uᴴ = X := by
      calc
        U * (Uᴴ * X * U) * Uᴴ = (U * Uᴴ) * X * (U * Uᴴ) := by
          noncomm_ring
        _ = X := by rw [hUU, one_mul, mul_one]
    calc
      U * (X - Uᴴ * X * U) * Uᴴ =
          U * X * Uᴴ - U * (Uᴴ * X * U) * Uᴴ := by noncomm_ring
      _ = U * X * Uᴴ - X := by rw [hleft]
  calc
    ScaledKazhdanTransport.matMass (X - Uᴴ * X * U) =
        ScaledKazhdanTransport.matMass
          (U * (X - Uᴴ * X * U) * Uᴴ) :=
      (ScaledKazhdanTransport.matMass_unitary_conj hU _).symm
    _ = ScaledKazhdanTransport.matMass (U * X * Uᴴ - X) := by
      rw [hconj]
    _ = ScaledKazhdanTransport.matMass (X - U * X * Uᴴ) := by
      rw [show U * X * Uᴴ - X = -(X - U * X * Uᴴ) by abel,
        ScaledKazhdanTransport.matMass_neg]

/-- **Per-index residual bound.**  The Frobenius norm of the Hermitian
Kazhdan average residual is at most the largest forward displacement
norm. -/
theorem sqrt_residual_mass_le
    (B : OpAlmostRepresentation E) (C : KazhdanCompressionCore Γ E)
    (S : Finset Γ) (hone : 1 ∈ S) (n : ℕ)
    (X : Matrix (B.model n) (B.model n) ℂ) {η : ℝ} (_hη : 0 ≤ η)
    (hdisp : ∀ a ∈ S, Real.sqrt (ScaledKazhdanTransport.matMass
      (X - (B.map n (C.iota a) : Matrix (B.model n) (B.model n) ℂ) * X *
        (B.map n (C.iota a) :
          Matrix (B.model n) (B.model n) ℂ)ᴴ)) ≤ η) :
    Real.sqrt (ScaledKazhdanTransport.matMass
      ((2 : ℂ)⁻¹ • ((S.card : ℂ)⁻¹ • ∑ a ∈ S,
        ((X - (B.map n (C.iota a) :
            Matrix (B.model n) (B.model n) ℂ) * X *
            (B.map n (C.iota a) :
              Matrix (B.model n) (B.model n) ℂ)ᴴ) +
          (X - (B.map n (C.iota a) :
            Matrix (B.model n) (B.model n) ℂ)ᴴ * X *
            (B.map n (C.iota a) :
              Matrix (B.model n) (B.model n) ℂ)))))) ≤ η := by
  classical
  have hcardpos : (0 : ℝ) < S.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, hone⟩
  -- flatten and use the genuine triangle inequality
  set R : Matrix (B.model n) (B.model n) ℂ :=
    (2 : ℂ)⁻¹ • ((S.card : ℂ)⁻¹ • ∑ a ∈ S,
      ((X - (B.map n (C.iota a) :
          Matrix (B.model n) (B.model n) ℂ) * X *
          (B.map n (C.iota a) :
            Matrix (B.model n) (B.model n) ℂ)ᴴ) +
        (X - (B.map n (C.iota a) :
          Matrix (B.model n) (B.model n) ℂ)ᴴ * X *
          (B.map n (C.iota a) :
            Matrix (B.model n) (B.model n) ℂ)))) with hR
  have hflatnorm : ∀ Z : Matrix (B.model n) (B.model n) ℂ,
      ‖flatE Z‖ = Real.sqrt (ScaledKazhdanTransport.matMass Z) := by
    intro Z
    have h := norm_flatE_sq Z
    calc
      ‖flatE Z‖ = Real.sqrt (‖flatE Z‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt (ScaledKazhdanTransport.matMass Z) := by rw [h]
  rw [← hflatnorm]
  have hterm : ∀ a ∈ S, ‖flatE
      ((X - (B.map n (C.iota a) :
          Matrix (B.model n) (B.model n) ℂ) * X *
          (B.map n (C.iota a) :
            Matrix (B.model n) (B.model n) ℂ)ᴴ) +
        (X - (B.map n (C.iota a) :
          Matrix (B.model n) (B.model n) ℂ)ᴴ * X *
          (B.map n (C.iota a) :
            Matrix (B.model n) (B.model n) ℂ)))‖ ≤ 2 * η := by
    intro a haS
    have hfwd : ‖flatE (X - (B.map n (C.iota a) :
        Matrix (B.model n) (B.model n) ℂ) * X *
        (B.map n (C.iota a) :
          Matrix (B.model n) (B.model n) ℂ)ᴴ)‖ ≤ η := by
      rw [hflatnorm]
      exact hdisp a haS
    have hrev : ‖flatE (X - (B.map n (C.iota a) :
        Matrix (B.model n) (B.model n) ℂ)ᴴ * X *
        (B.map n (C.iota a) :
          Matrix (B.model n) (B.model n) ℂ))‖ ≤ η := by
      rw [hflatnorm, matMass_reverse_displacement (B.map n (C.iota a)).2]
      exact hdisp a haS
    calc
      ‖flatE (_ + _)‖ = ‖flatE _ + flatE _‖ := by rw [flatE_add]
      _ ≤ ‖flatE (X - (B.map n (C.iota a) :
            Matrix (B.model n) (B.model n) ℂ) * X *
            (B.map n (C.iota a) :
              Matrix (B.model n) (B.model n) ℂ)ᴴ)‖ +
          ‖flatE (X - (B.map n (C.iota a) :
            Matrix (B.model n) (B.model n) ℂ)ᴴ * X *
            (B.map n (C.iota a) :
              Matrix (B.model n) (B.model n) ℂ))‖ := norm_add_le _ _
      _ ≤ 2 * η := by linarith
  calc
    ‖flatE R‖ = ‖(2 : ℂ)⁻¹ • ((S.card : ℂ)⁻¹ •
        ∑ a ∈ S, flatE
          ((X - (B.map n (C.iota a) :
              Matrix (B.model n) (B.model n) ℂ) * X *
              (B.map n (C.iota a) :
                Matrix (B.model n) (B.model n) ℂ)ᴴ) +
            (X - (B.map n (C.iota a) :
              Matrix (B.model n) (B.model n) ℂ)ᴴ * X *
              (B.map n (C.iota a) :
                Matrix (B.model n) (B.model n) ℂ))))‖ := by
      rw [hR, flatE_smul, flatE_smul, flatE_sum]
    _ ≤ ‖(2 : ℂ)⁻¹‖ * (‖((S.card : ℂ))⁻¹‖ *
        ∑ a ∈ S, ‖flatE
          ((X - (B.map n (C.iota a) :
              Matrix (B.model n) (B.model n) ℂ) * X *
              (B.map n (C.iota a) :
                Matrix (B.model n) (B.model n) ℂ)ᴴ) +
            (X - (B.map n (C.iota a) :
              Matrix (B.model n) (B.model n) ℂ)ᴴ * X *
              (B.map n (C.iota a) :
                Matrix (B.model n) (B.model n) ℂ)))‖) := by
      rw [norm_smul, norm_smul]
      have hsum := norm_sum_le S (fun a ↦ flatE
        ((X - (B.map n (C.iota a) :
            Matrix (B.model n) (B.model n) ℂ) * X *
            (B.map n (C.iota a) :
              Matrix (B.model n) (B.model n) ℂ)ᴴ) +
          (X - (B.map n (C.iota a) :
            Matrix (B.model n) (B.model n) ℂ)ᴴ * X *
            (B.map n (C.iota a) :
              Matrix (B.model n) (B.model n) ℂ))))
      have h2 : (0 : ℝ) ≤ ‖(2 : ℂ)⁻¹‖ := norm_nonneg _
      have hc : (0 : ℝ) ≤ ‖((S.card : ℂ))⁻¹‖ := norm_nonneg _
      have := mul_le_mul_of_nonneg_left hsum hc
      nlinarith [this]
    _ ≤ η := by
      have hsumle : ∑ a ∈ S, ‖flatE
          ((X - (B.map n (C.iota a) :
              Matrix (B.model n) (B.model n) ℂ) * X *
              (B.map n (C.iota a) :
                Matrix (B.model n) (B.model n) ℂ)ᴴ) +
            (X - (B.map n (C.iota a) :
              Matrix (B.model n) (B.model n) ℂ)ᴴ * X *
              (B.map n (C.iota a) :
                Matrix (B.model n) (B.model n) ℂ)))‖ ≤
          S.card * (2 * η) := by
        have h := Finset.sum_le_card_nsmul S _ (2 * η) fun a ha ↦
          hterm a ha
        simpa [nsmul_eq_mul] using h
      have h2 : ‖(2 : ℂ)⁻¹‖ = 2⁻¹ := by
        rw [norm_inv]
        simp
      have hcnorm : ‖((S.card : ℂ))⁻¹‖ = ((S.card : ℝ))⁻¹ := by
        rw [norm_inv]
        simp
      rw [h2, hcnorm]
      have hccancel : ((S.card : ℝ))⁻¹ * ((S.card : ℝ) * (2 * η)) =
          2 * η := by
        field_simp
      calc
        (2 : ℝ)⁻¹ * (((S.card : ℝ))⁻¹ * ∑ a ∈ S, ‖flatE
            ((X - (B.map n (C.iota a) :
                Matrix (B.model n) (B.model n) ℂ) * X *
                (B.map n (C.iota a) :
                  Matrix (B.model n) (B.model n) ℂ)ᴴ) +
              (X - (B.map n (C.iota a) :
                Matrix (B.model n) (B.model n) ℂ)ᴴ * X *
                (B.map n (C.iota a) :
                  Matrix (B.model n) (B.model n) ℂ)))‖) ≤
            (2 : ℝ)⁻¹ * (((S.card : ℝ))⁻¹ * ((S.card : ℝ) * (2 * η))) := by
          have hinv1 : (0 : ℝ) ≤ (2 : ℝ)⁻¹ := by norm_num
          have hinv2 : (0 : ℝ) ≤ ((S.card : ℝ))⁻¹ := by positivity
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hsumle hinv2) hinv1
        _ = η := by
          rw [hccancel]
          ring

/-- **Per-index spectral capture.**  At a fixed stage, a matrix with mass
at most `Cw²` and residual norm at most `η` has corner-complement mass at
most `(Cw + 1) η / (1 − θ)`. -/
theorem index_capture
    (B : OpAlmostRepresentation E) (C : KazhdanCompressionCore Γ E)
    (S : Finset Γ) (hone : 1 ∈ S) {θ : ℝ} (hθ1 : θ < 1) (n : ℕ)
    (X : Matrix (B.model n) (B.model n) ℂ) {Cw η : ℝ}
    (hCw : 0 ≤ Cw) (hη : 0 < η)
    (hmass : Real.sqrt (ScaledKazhdanTransport.matMass X) ≤ Cw)
    (hres : Real.sqrt (ScaledKazhdanTransport.matMass
      ((2 : ℂ)⁻¹ • ((S.card : ℂ)⁻¹ • ∑ a ∈ S,
        ((X - (B.map n (C.iota a) :
            Matrix (B.model n) (B.model n) ℂ) * X *
            (B.map n (C.iota a) :
              Matrix (B.model n) (B.model n) ℂ)ᴴ) +
          (X - (B.map n (C.iota a) :
            Matrix (B.model n) (B.model n) ℂ)ᴴ * X *
            (B.map n (C.iota a) :
              Matrix (B.model n) (B.model n) ℂ)))))) ≤ η) :
    MarkedCompressionVectorChain.vecMass
      ((1 - cornerProjection B C S θ n) *ᵥ gammaRowVec B n X) ≤
        ((Cw + 1) * η) / (1 - θ) := by
  classical
  have hgap : 0 < 1 - θ := by linarith
  set ξ := gammaRowVec B n X with hξ
  set H := hermitianAverage (gammaAdjoint B C) S n with hHdef
  set R : Matrix (B.model n) (B.model n) ℂ :=
    (2 : ℂ)⁻¹ • ((S.card : ℂ)⁻¹ • ∑ a ∈ S,
      ((X - (B.map n (C.iota a) :
          Matrix (B.model n) (B.model n) ℂ) * X *
          (B.map n (C.iota a) :
            Matrix (B.model n) (B.model n) ℂ)ᴴ) +
        (X - (B.map n (C.iota a) :
          Matrix (B.model n) (B.model n) ℂ)ᴴ * X *
          (B.map n (C.iota a) :
            Matrix (B.model n) (B.model n) ℂ)))) with hRdef
  have hresidVec : ξ - H *ᵥ ξ = gammaRowVec B n R := by
    simpa [hξ, hHdef, hRdef] using
      matrix_laplacian_matVec B C S hone n X
  have hmassξ : ∑ i : (gammaAdjoint B C).model n,
      Complex.normSq (ξ i) ≤ Cw ^ 2 := by
    rw [hξ, sum_normSq_gammaRowVec]
    have hfold : (∑ i : B.model n, ∑ j : B.model n,
        Complex.normSq (X i j)) =
        ScaledKazhdanTransport.matMass X := rfl
    rw [hfold]
    have h := hmass
    have hnn : 0 ≤ ScaledKazhdanTransport.matMass X :=
      ScaledKazhdanTransport.matMass_nonneg X
    nlinarith [Real.sq_sqrt hnn, Real.sqrt_nonneg
      (ScaledKazhdanTransport.matMass X)]
  have hmassR : ∑ i : (gammaAdjoint B C).model n,
      Complex.normSq ((ξ - H *ᵥ ξ) i) ≤ η ^ 2 := by
    rw [hresidVec, sum_normSq_gammaRowVec]
    have hfold : (∑ i : B.model n, ∑ j : B.model n,
        Complex.normSq (R i j)) =
        ScaledKazhdanTransport.matMass R := rfl
    rw [hfold]
    have hnn : 0 ≤ ScaledKazhdanTransport.matMass R :=
      ScaledKazhdanTransport.matMass_nonneg R
    nlinarith [Real.sq_sqrt hnn, Real.sqrt_nonneg
      (ScaledKazhdanTransport.matMass R), hres]
  have hδpos : 0 < η / (Cw + 1) := by positivity
  have henergy : (star ξ ⬝ᵥ (ξ - H *ᵥ ξ)).re ≤ (Cw + 1) * η := by
    have hamgm := re_star_dotProduct_le hδpos ξ (ξ - H *ᵥ ξ)
    have hclean : (2 : ℝ)⁻¹ * ((η / (Cw + 1)) * (Cw ^ 2) +
        ((η / (Cw + 1))⁻¹ * (η ^ 2))) ≤ (Cw + 1) * η := by
      have hCw1 : (0 : ℝ) < Cw + 1 := by linarith
      rw [inv_div]
      have h1 : (η / (Cw + 1)) * Cw ^ 2 ≤ η * (Cw + 1) := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hCw1]
        nlinarith [hη.le, hCw]
      have h2 : ((Cw + 1) / η) * η ^ 2 = (Cw + 1) * η := by
        field_simp
      linarith
    calc
      (star ξ ⬝ᵥ (ξ - H *ᵥ ξ)).re ≤
          (2 : ℝ)⁻¹ * ((η / (Cw + 1)) *
            ∑ i, Complex.normSq (ξ i) +
            (η / (Cw + 1))⁻¹ *
              ∑ i, Complex.normSq ((ξ - H *ᵥ ξ) i)) := hamgm
      _ ≤ (2 : ℝ)⁻¹ * ((η / (Cw + 1)) * (Cw ^ 2) +
          ((η / (Cw + 1))⁻¹ * (η ^ 2))) := by
        have hd1 : (0 : ℝ) ≤ η / (Cw + 1) := hδpos.le
        have hd2 : (0 : ℝ) ≤ (η / (Cw + 1))⁻¹ := by positivity
        have hm1 := mul_le_mul_of_nonneg_left hmassξ hd1
        have hm2 := mul_le_mul_of_nonneg_left hmassR hd2
        nlinarith [hm1, hm2]
      _ ≤ (Cw + 1) * η := hclean
  have hcapture := capture_vec H
    (by simpa [hHdef, Matrix.IsHermitian,
      Matrix.star_eq_conjTranspose] using
      hermitianAverage_conjTranspose (gammaAdjoint B C) S n)
    θ 0 hθ1.le (by norm_num)
    (by simpa [hHdef] using
      norm_hermitianAverage_le_one (gammaAdjoint B C) S n) ξ
  have hbelow : spectralBelow H
      (hermitianAverage_conjTranspose (gammaAdjoint B C) S n) θ =
      1 - cornerProjection B C S θ n := rfl
  rw [hbelow, zero_mul, add_zero] at hcapture
  have hchain : (1 - θ) * MarkedCompressionVectorChain.vecMass
      ((1 - cornerProjection B C S θ n) *ᵥ ξ) ≤ (Cw + 1) * η :=
    hcapture.trans henergy
  rw [le_div_iff₀ hgap]
  calc
    MarkedCompressionVectorChain.vecMass
        ((1 - cornerProjection B C S θ n) *ᵥ ξ) * (1 - θ) =
        (1 - θ) * MarkedCompressionVectorChain.vecMass
          ((1 - cornerProjection B C S θ n) *ᵥ ξ) := by ring
    _ ≤ (Cw + 1) * η := hchain

end InvolutionCollapseIndexCapture
end GroupApproximation
