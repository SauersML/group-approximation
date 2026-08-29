import GroupApproximation.Sofic.WeakMFVectorGNS
import GroupApproximation.Sofic.KazhdanCornerPolar

/-!
# Moving spectral compression for the Kazhdan corner

This file connects the finite-stage spectral gap to an almost reducing
projection.  The first layer is dimension-free spectral-cutoff calculus; the
later layer applies it to weak-MF matrix averages and compresses the
microstates to the moving eigenspaces.

For provenance, compare the operator-norm almost-spectral-gap theorem due to
Uri Bader and recorded as Dogon--Vigdorovich, Theorem 7.10
(arXiv:2506.20843v2), whose proof uses Ozawa's sum-of-squares
characterization of property (T) and generalizes Manuilov--You.  The present
file proves the concrete matrix cutoff estimates required by this project;
it does not import or transcribe external Lean code.
-/

namespace GroupApproximation
namespace KazhdanCornerMatrices

open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {Y : FiniteModel}

/-- Unitary conjugation preserves the matrix `ℓ²` operator norm. -/
theorem norm_unitary_conjugate {U D : Matrix Y Y ℂ}
    (hU : U ∈ Matrix.unitaryGroup Y ℂ) :
    ‖U * D * Uᴴ‖ = ‖D‖ := by
  have hUstar : Uᴴ ∈ Matrix.unitaryGroup Y ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact Unitary.star_mul_self_of_mem hU
  rw [CStarRing.norm_mul_mem_unitary _ hUstar,
    CStarRing.norm_mem_unitary_mul _ hU]

/-- A Hermitian spectral cutoff is a contraction. -/
theorem norm_spectralAbove_le_one (H : Matrix Y Y ℂ) (hH : H.IsHermitian)
    (t : ℝ) : ‖spectralAbove H hH t‖ ≤ 1 := by
  let U : Matrix Y Y ℂ := hH.eigenvectorUnitary
  let D : Matrix Y Y ℂ :=
    Matrix.diagonal (fun i ↦ if t < hH.eigenvalues i then 1 else 0)
  change ‖U * D * Uᴴ‖ ≤ 1
  rw [norm_unitary_conjugate hH.eigenvectorUnitary.2,
    Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i ↦ ?_
  split <;> simp

/-- Eigenvalues of a Hermitian contraction lie in `[-1,1]`, over an
arbitrary finite coordinate type. -/
theorem abs_hermitianEigenvalue_le_norm {Z : Type*} [Fintype Z]
    [DecidableEq Z] (H : Matrix Z Z ℂ)
    (hH : H.IsHermitian) (i : Z) : |hH.eigenvalues i| ≤ ‖H‖ := by
  let x : EuclideanSpace ℂ Z := hH.eigenvectorBasis i
  have hx : ‖x‖ = 1 := hH.eigenvectorBasis.orthonormal.1 i
  have heigen :
      (Matrix.toEuclideanCLM (n := Z) (𝕜 := ℂ)) H x =
        ((hH.eigenvalues i : ℝ) : ℂ) • x :=
    PiLp.ext fun j ↦ congrFun (hH.mulVec_eigenvectorBasis i) j
  calc
    |hH.eigenvalues i| = ‖((hH.eigenvalues i : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ‖H‖ := by
      simpa only [heigen, norm_smul, hx, mul_one,
        Matrix.l2_opNorm_toEuclideanCLM] using
        ContinuousLinearMap.le_opNorm
          ((Matrix.toEuclideanCLM (n := Z) (𝕜 := ℂ)) H) x

/-- On a spectral cutoff whose retained eigenvalues lie within `delta` of
`1`, the Hermitian displacement from the identity has norm at most `delta`.
-/
theorem norm_sub_one_mul_spectralAbove_le
    (H : Matrix Y Y ℂ) (hH : H.IsHermitian) (t delta : ℝ)
    (hdelta : 0 ≤ delta) (hHnorm : ‖H‖ ≤ 1)
    (hnear : ∀ i, t < hH.eigenvalues i → 1 - delta ≤ hH.eigenvalues i) :
    ‖(H - 1) * spectralAbove H hH t‖ ≤ delta := by
  let U : Matrix Y Y ℂ := hH.eigenvectorUnitary
  let L : Matrix Y Y ℂ :=
    Matrix.diagonal (fun i ↦ (hH.eigenvalues i : ℂ))
  let D : Matrix Y Y ℂ :=
    Matrix.diagonal (fun i ↦ if t < hH.eigenvalues i then 1 else 0)
  let R : Matrix Y Y ℂ :=
    Matrix.diagonal (fun i ↦
      ((hH.eigenvalues i : ℂ) - 1) *
        (if t < hH.eigenvalues i then 1 else 0))
  have hUU : Uᴴ * U = 1 :=
    Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
  have hUUstar : U * Uᴴ = 1 :=
    Unitary.mul_star_self_of_mem hH.eigenvectorUnitary.2
  have hHdiag : H = U * L * Uᴴ := by
    calc
      H = Unitary.conjStarAlgAut ℂ _ hH.eigenvectorUnitary
          (Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues)) :=
        hH.spectral_theorem
      _ = U * L * Uᴴ := by rfl
  have hresidual : (H - 1) * spectralAbove H hH t = U * R * Uᴴ := by
    have hsub : H - 1 = U * (L - 1) * Uᴴ := by
      rw [hHdiag]
      calc
        U * L * Uᴴ - 1 = U * L * Uᴴ - U * Uᴴ := by rw [hUUstar]
        _ = U * (L - 1) * Uᴴ := by noncomm_ring
    rw [hsub]
    change (U * (L - 1) * Uᴴ) * (U * D * Uᴴ) = U * R * Uᴴ
    have hLD : (L - 1) * D = R := by
      simp only [L, D, R]
      have hsubdiag :
          Matrix.diagonal (fun i ↦ (hH.eigenvalues i : ℂ)) - 1 =
            Matrix.diagonal (fun i ↦ (hH.eigenvalues i : ℂ) - 1) := by
        ext i j
        by_cases hij : i = j
        · subst j
          simp
        · simp [hij]
      rw [hsubdiag, Matrix.diagonal_mul_diagonal]
    calc
      (U * (L - 1) * Uᴴ) * (U * D * Uᴴ) =
          U * (L - 1) * (Uᴴ * U) * D * Uᴴ := by noncomm_ring
      _ = U * ((L - 1) * D) * Uᴴ := by rw [hUU]; noncomm_ring
      _ = U * R * Uᴴ := by rw [hLD]
  rw [hresidual, norm_unitary_conjugate hH.eigenvectorUnitary.2]
  simp only [R]
  rw [Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg hdelta).2 fun i ↦ ?_
  by_cases hi : t < hH.eigenvalues i
  · simp only [hi, if_true, mul_one]
    rw [show (hH.eigenvalues i : ℂ) - 1 =
        ((hH.eigenvalues i - 1 : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs]
    have hupper : hH.eigenvalues i ≤ 1 := by
      have habs := (abs_hermitianEigenvalue_le_norm H hH i).trans hHnorm
      exact (le_abs_self _).trans habs
    rw [abs_of_nonpos (by linarith only [hupper])]
    linarith only [hnear i hi]
  · simp [hi, hdelta]

/-- The entrywise squared Euclidean norm is the real part of the Gram
quadratic form. -/
theorem sum_normSq_mulVec_eq_re_gram (X : Matrix Y Y ℂ) (x : Y → ℂ) :
    ∑ i : Y, Complex.normSq ((X *ᵥ x) i) =
      (star x ⬝ᵥ ((Xᴴ * X) *ᵥ x)).re := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_conjTranspose, star_star]
  change (∑ i : Y, Complex.normSq ((X *ᵥ x) i)) =
    (∑ i : Y, star ((X *ᵥ x) i) * (X *ᵥ x) i).re
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  let z := (X *ᵥ x) i
  calc
    Complex.normSq z = ((Complex.normSq z : ℝ) : ℂ).re := by simp
    _ = (star z * z).re :=
      congrArg Complex.re Complex.normSq_eq_conj_mul_self

/-- A dimension-free Gram domination estimate, proved directly from
quadratic forms rather than through the matrix star-order instance. -/
theorem norm_sq_le_norm_of_posSemidef_sub (X K : Matrix Y Y ℂ)
    (hdom : (K - Xᴴ * X).PosSemidef) : ‖X‖ ^ 2 ≤ ‖K‖ := by
  have hKnonneg : 0 ≤ ‖K‖ := norm_nonneg K
  have hroot : 0 ≤ Real.sqrt ‖K‖ := Real.sqrt_nonneg _
  have hX : ‖X‖ ≤ Real.sqrt ‖K‖ := by
    refine l2_opNorm_le_of_sum_normSq Y X hroot fun x ↦ ?_
    let xE : EuclideanSpace ℂ Y := (EuclideanSpace.equiv Y ℂ).symm x
    let KxE : EuclideanSpace ℂ Y :=
      (EuclideanSpace.equiv Y ℂ).symm (K *ᵥ x)
    have hquad := hdom.re_dotProduct_nonneg x
    have hgram :
        ∑ i : Y, Complex.normSq ((X *ᵥ x) i) ≤
          (star x ⬝ᵥ (K *ᵥ x)).re := by
      rw [sum_normSq_mulVec_eq_re_gram]
      simp only [Matrix.sub_mulVec, dotProduct_sub, map_sub] at hquad
      change 0 ≤ (star x ⬝ᵥ (K *ᵥ x)).re -
        (star x ⬝ᵥ ((Xᴴ * X) *ᵥ x)).re at hquad
      linarith only [hquad]
    have hinner : (star x ⬝ᵥ (K *ᵥ x)).re =
        RCLike.re (inner ℂ xE KxE) := by
      simp only [xE, KxE, EuclideanSpace.inner_eq_star_dotProduct]
      rw [dotProduct_comm]
      rfl
    calc
      ∑ i : Y, Complex.normSq ((X *ᵥ x) i)
          ≤ (star x ⬝ᵥ (K *ᵥ x)).re := hgram
      _ = RCLike.re (inner ℂ xE KxE) := hinner
      _ ≤ ‖xE‖ * ‖KxE‖ := re_inner_le_norm _ _
      _ ≤ ‖xE‖ * (‖K‖ * ‖xE‖) :=
        mul_le_mul_of_nonneg_left (Matrix.l2_opNorm_mulVec K xE) (norm_nonneg _)
      _ = ‖K‖ * (∑ i : Y, Complex.normSq (x i)) := by
        rw [← euclidean_norm_sq Y x]
        ring
      _ = (Real.sqrt ‖K‖) ^ 2 *
          ∑ i : Y, Complex.normSq (x i) := by
        rw [Real.sq_sqrt hKnonneg]
  calc
    ‖X‖ ^ 2 = ‖X‖ * ‖X‖ := pow_two _
    _ ≤ Real.sqrt ‖K‖ * Real.sqrt ‖K‖ :=
      mul_self_le_mul_self (norm_nonneg X) hX
    _ = ‖K‖ := Real.mul_self_sqrt hKnonneg

/-- Removing one positive Gram term from a finite positive sum leaves a
positive matrix. -/
theorem posSemidef_finset_sum_sub_of_mem {I : Type*} [DecidableEq I]
    (s : Finset I) (F : I → Matrix Y Y ℂ)
    (hF : ∀ i ∈ s, (F i).PosSemidef) {i : I} (hi : i ∈ s) :
    ((∑ j ∈ s, F j) - F i).PosSemidef := by
  have hsplit : (∑ j ∈ s, F j) - F i = ∑ j ∈ s.erase i, F j := by
    rw [← Finset.sum_erase_add _ _ hi]
    abel_nf
  rw [hsplit]
  exact Matrix.posSemidef_sum (s.erase i) fun j hj ↦
    hF j (Finset.mem_of_mem_erase hj)

section WeakMF

variable {G : Type} [Group G]

/-- Above any fixed threshold strictly larger than the Kazhdan moving
spectrum bound, the Hermitian average is eventually arbitrarily close to
`1` on its retained spectral subspace. -/
theorem hermitianAverage_eventually_top_spectral_residual
    {Q : Finset G} {epsilon : ℝ}
    (hQ : IsKazhdanPair.{0, 0} G Q epsilon)
    (S : Finset G) (hQS : Q ⊆ S) (hone : 1 ∈ S)
    (hepsilonOne : epsilon ≤ 1) (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (A : OpAlmostRepresentation G) {t delta : ℝ}
    (ht : 1 - epsilon ^ 2 / (4 * S.card) < t) (hdelta : 0 < delta) :
    ∃ N : ℕ, ∀ n ≥ N,
      ‖(hermitianAverage A S n - 1) *
          spectralAbove (hermitianAverage A S n)
            (hermitianAverage_conjTranspose A S n) t‖ ≤ delta := by
  obtain ⟨N, hN⟩ :=
    WeakMFVectorGNS.hermitianAverage_eventually_no_intermediate_eigenvalues
      hQ S hQS hone hepsilonOne hsymm A ht
        (by linarith only [hdelta] : 1 - delta < 1)
  refine ⟨N, fun n hn ↦ ?_⟩
  refine norm_sub_one_mul_spectralAbove_le (hermitianAverage A S n)
    (hermitianAverage_conjTranspose A S n) t delta hdelta.le
    (norm_hermitianAverage_le_one A S n) ?_
  intro i hi
  have hnot := hN n hn i
  by_contra hnear
  exact hnot ⟨hi.le, le_of_not_ge hnear⟩

/-- Displacement of the top spectral subspace by one weak-MF microstate. -/
noncomputable def topSpectralDisplacement (A : OpAlmostRepresentation G)
    (S : Finset G) (t : ℝ) (n : ℕ) (g : G) :
    Matrix (A.model n) (A.model n) ℂ :=
  ((A.map n g : Matrix (A.model n) (A.model n) ℂ) - 1) *
    spectralAbove (hermitianAverage A S n)
      (hermitianAverage_conjTranspose A S n) t

/-- The sum of the generator displacement squares is the Kazhdan Laplacian
compressed to the top spectral subspace. -/
theorem sum_topSpectralDisplacement_gram
    (A : OpAlmostRepresentation G) (S : Finset G) (hone : 1 ∈ S)
    (t : ℝ) (n : ℕ) :
    (∑ g ∈ S, (topSpectralDisplacement A S t n g)ᴴ *
        topSpectralDisplacement A S t n g) =
      ((2 * S.card : ℕ) : ℂ) •
        (spectralAbove (hermitianAverage A S n)
            (hermitianAverage_conjTranspose A S n) t *
          (1 - hermitianAverage A S n) *
          spectralAbove (hermitianAverage A S n)
            (hermitianAverage_conjTranspose A S n) t) := by
  classical
  let P := spectralAbove (hermitianAverage A S n)
    (hermitianAverage_conjTranspose A S n) t
  let T : Matrix (A.model n) (A.model n) ℂ :=
    ∑ g ∈ S, (A.map n g : Matrix (A.model n) (A.model n) ℂ)
  have hPstar : Pᴴ = P :=
    (spectralAbove_isOrthogonalProjection _ _ _).1
  have hterm (g : G) :
      (topSpectralDisplacement A S t n g)ᴴ *
          topSpectralDisplacement A S t n g =
        P * ((2 : ℂ) • (1 : Matrix (A.model n) (A.model n) ℂ) -
          (A.map n g : Matrix (A.model n) (A.model n) ℂ) -
          (A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ) * P := by
    let U : Matrix (A.model n) (A.model n) ℂ := A.map n g
    have hU : Uᴴ * U = 1 := by
      have hu := (A.map n g).2
      rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hu
      exact hu
    rw [topSpectralDisplacement, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPstar]
    change P * (Uᴴ - 1) * ((U - 1) * P) =
      P * ((2 : ℂ) • 1 - U - Uᴴ) * P
    rw [show P * (Uᴴ - 1) * ((U - 1) * P) =
        P * ((Uᴴ - 1) * (U - 1)) * P by noncomm_ring]
    rw [show (Uᴴ - 1) * (U - 1) = Uᴴ * U - Uᴴ - U + 1 by
      noncomm_ring, hU]
    simp only [two_smul]
    abel_nf
  simp_rw [hterm]
  have hinner :
      (∑ g ∈ S,
        ((2 : ℂ) • (1 : Matrix (A.model n) (A.model n) ℂ) -
          (A.map n g : Matrix (A.model n) (A.model n) ℂ) -
          (A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ)) =
        (((2 * S.card : ℕ) : ℂ) • 1 - T - Tᴴ) := by
    rw [Matrix.conjTranspose_sum]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [T, Matrix.natCast_apply]
    · simp [T, Matrix.natCast_apply, hij]
  have hsum :
      (∑ g ∈ S,
          P * ((2 : ℂ) • (1 : Matrix (A.model n) (A.model n) ℂ) -
            (A.map n g : Matrix (A.model n) (A.model n) ℂ) -
            (A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ) * P) =
        P * (((2 * S.card : ℕ) : ℂ) • 1 - T - Tᴴ) * P := by
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    rw [hinner]
  rw [hsum]
  have hcard : (S.card : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr ⟨1, hone⟩)
  have hmiddle :
      (((2 * S.card : ℕ) : ℂ) •
          (1 - hermitianAverage A S n)) =
        (((2 * S.card : ℕ) : ℂ) • 1 - T - Tᴴ) := by
    have hscale : (((2 * S.card : ℕ) : ℂ) •
        hermitianAverage A S n) = T + Tᴴ := by
      rw [hermitianAverage, matrixAverage]
      simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_sum]
      have hstarCard : star ((S.card : ℂ)⁻¹) = (S.card : ℂ)⁻¹ := by simp
      rw [hstarCard, ← smul_add, smul_smul, smul_smul]
      have hcoef :
          (((2 * S.card : ℕ) : ℂ) * (2 : ℂ)⁻¹ *
              (S.card : ℂ)⁻¹) = 1 := by
        push_cast
        field_simp
      rw [hcoef, one_smul]
      simp only [T, Matrix.conjTranspose_sum]
    rw [smul_sub, hscale]
    abel
  change P * (((2 * S.card : ℕ) : ℂ) • 1 - T - Tᴴ) * P =
    ((2 * S.card : ℕ) : ℂ) •
      (P * (1 - hermitianAverage A S n) * P)
  rw [← hmiddle]
  rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]

/-- The total positive Gram mass of the top-space generator displacement
vanishes in operator norm. -/
theorem sum_topSpectralDisplacement_gram_vanishing
    {Q : Finset G} {epsilon : ℝ}
    (hQ : IsKazhdanPair.{0, 0} G Q epsilon)
    (S : Finset G) (hQS : Q ⊆ S) (hone : 1 ∈ S)
    (hepsilonOne : epsilon ≤ 1) (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (A : OpAlmostRepresentation G) {t : ℝ}
    (ht : 1 - epsilon ^ 2 / (4 * S.card) < t) :
    OpNormVanishing A (fun n ↦
      ∑ g ∈ S, (topSpectralDisplacement A S t n g)ᴴ *
        topSpectralDisplacement A S t n g) := by
  let P : ∀ n, Matrix (A.model n) (A.model n) ℂ := fun n ↦
    spectralAbove (hermitianAverage A S n)
      (hermitianAverage_conjTranspose A S n) t
  have hresidual : OpNormVanishing A (fun n ↦
      (hermitianAverage A S n - 1) * P n) := by
    intro eta heta
    exact hermitianAverage_eventually_top_spectral_residual
      hQ S hQS hone hepsilonOne hsymm A ht heta
  have hP : ∀ n, ‖P n‖ ≤ 1 := fun n ↦ norm_spectralAbove_le_one _ _ _
  have hcore : OpNormVanishing A (fun n ↦
      P n * ((hermitianAverage A S n - 1) * P n)) :=
    hresidual.mul_left_of_norm_le_one P hP
  have hscaled := hcore.neg.smul (((2 * S.card : ℕ) : ℂ))
  have heq (n : ℕ) :
      (∑ g ∈ S, (topSpectralDisplacement A S t n g)ᴴ *
          topSpectralDisplacement A S t n g) =
        (((2 * S.card : ℕ) : ℂ)) •
          -(P n * ((hermitianAverage A S n - 1) * P n)) := by
    rw [sum_topSpectralDisplacement_gram A S hone t n]
    dsimp only [P]
    congr 1
    noncomm_ring
  intro eta heta
  obtain ⟨N, hN⟩ := hscaled eta heta
  refine ⟨N, fun n hn ↦ ?_⟩
  change ‖∑ g ∈ S, (topSpectralDisplacement A S t n g)ᴴ *
    topSpectralDisplacement A S t n g‖ ≤ eta
  rw [heq n]
  exact hN n hn

/-- Each generator moves the retained top spectral subspace by an
operator-norm amount tending to zero. -/
theorem topSpectralDisplacement_vanishing
    {Q : Finset G} {epsilon : ℝ}
    (hQ : IsKazhdanPair.{0, 0} G Q epsilon)
    (S : Finset G) (hQS : Q ⊆ S) (hone : 1 ∈ S)
    (hepsilonOne : epsilon ≤ 1) (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (A : OpAlmostRepresentation G) {t : ℝ}
    (ht : 1 - epsilon ^ 2 / (4 * S.card) < t)
    {g : G} (hg : g ∈ S) :
    OpNormVanishing A (fun n ↦ topSpectralDisplacement A S t n g) := by
  classical
  have htotal := sum_topSpectralDisplacement_gram_vanishing
    hQ S hQS hone hepsilonOne hsymm A ht
  intro eta heta
  obtain ⟨N, hN⟩ := htotal (eta ^ 2) (sq_pos_of_pos heta)
  refine ⟨N, fun n hn ↦ ?_⟩
  let X := topSpectralDisplacement A S t n g
  let K := ∑ h ∈ S, (topSpectralDisplacement A S t n h)ᴴ *
    topSpectralDisplacement A S t n h
  have hdom : (K - Xᴴ * X).PosSemidef :=
    posSemidef_finset_sum_sub_of_mem S _
      (fun h _ ↦ Matrix.posSemidef_conjTranspose_mul_self _) hg
  have hsq : ‖X‖ ^ 2 ≤ ‖K‖ :=
    norm_sq_le_norm_of_posSemidef_sub X K hdom
  have hK : ‖K‖ ≤ eta ^ 2 := hN n hn
  nlinarith only [hsq, hK, norm_nonneg X, heta]

/-- Generator control propagates to every group element when the symmetric
finite set generates the group. -/
theorem topSpectralDisplacement_vanishing_of_generates
    {Q : Finset G} {epsilon : ℝ}
    (hQ : IsKazhdanPair.{0, 0} G Q epsilon)
    (S : Finset G) (hQS : Q ⊆ S) (hone : 1 ∈ S)
    (hepsilonOne : epsilon ≤ 1) (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (A : OpAlmostRepresentation G) {t : ℝ}
    (ht : 1 - epsilon ^ 2 / (4 * S.card) < t) (g : G) :
    OpNormVanishing A (fun n ↦ topSpectralDisplacement A S t n g) := by
  classical
  let P : ∀ n, Matrix (A.model n) (A.model n) ℂ := fun n ↦
    spectralAbove (hermitianAverage A S n)
      (hermitianAverage_conjTranspose A S n) t
  have hP : ∀ n, ‖P n‖ ≤ 1 := fun n ↦ norm_spectralAbove_le_one _ _ _
  let good : G → Prop := fun k ↦
    OpNormVanishing A (fun n ↦ topSpectralDisplacement A S t n k)
  have hgoodS : ∀ k ∈ (S : Set G), good k := by
    intro k hk
    exact topSpectralDisplacement_vanishing
      hQ S hQS hone hepsilonOne hsymm A ht hk
  have hgoodOne : good 1 := by
    have h := (map_one_vanishing A).mul_right_of_norm_le_one P hP
    exact h.congr fun n ↦ by rfl
  have hgoodMul : ∀ a b, good a → good b → good (a * b) := by
    intro a b ha hb
    have hdef := (multiplicativeDefect_vanishing A a b).mul_right_of_norm_le_one P hP
    have hb' := hb.mul_left_of_norm_le_one
      (fun n ↦ (A.map n a : Matrix (A.model n) (A.model n) ℂ))
      (fun n ↦ by
        letI : Nonempty (A.model n) :=
          Fintype.card_pos_iff.mp (A.modelNonempty n)
        rw [CStarRing.norm_of_mem_unitary (A.map n a).2])
    exact (hdef.add (hb'.add ha)).congr fun n ↦ by
      simp only [topSpectralDisplacement, P]
      noncomm_ring
  have hSinv : (S : Set G)⁻¹ ⊆ (S : Set G) := by
    intro k hk
    rw [Set.mem_inv] at hk
    have hk' : k⁻¹ ∈ S := by simpa using hk
    simpa using hsymm k⁻¹ hk'
  have hunion : (S : Set G) ∪ (S : Set G)⁻¹ = (S : Set G) :=
    Set.union_eq_left.mpr hSinv
  have hmclosure : Submonoid.closure (S : Set G) = ⊤ := by
    rw [← hunion, ← Subgroup.closure_toSubmonoid, hgen]
    rfl
  exact Submonoid.dense_induction (S : Set G) hmclosure hgoodS hgoodOne
    hgoodMul g

end WeakMF

end KazhdanCornerMatrices
end GroupApproximation
