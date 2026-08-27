import GroupApproximation.Sofic.ApproxInvolutionCorner
import GroupApproximation.Sofic.ProjectionRankFlip

/-!
# Exact commuting involution lifts

A weak-MF microstate sends an involution of the group to a unitary matrix that
squares to the identity only approximately.  The analytic collapse argument
needs to replace such a matrix by an *exact* self-adjoint unitary, without
disturbing a finite commuting corner structure that has already been fixed at
that stage.  This file supplies the finite-dimensional correction, with
explicit operator-norm constants and no limits.

Three layers are proved.

* The **spectral sign** `signOfHermitian H hH` of a Hermitian matrix is an
  exact involution unconditionally, and it moves `H` by at most the involution
  defect `‖H * H - 1‖`.  The estimate is eigenvalue-wise: rounding a real
  number `x` to `±1` costs at most `|x ^ 2 - 1|`.
* For a unitary `u` the Hermitian part absorbs half the defect and the sign of
  the Hermitian part absorbs the other half, so the corrected involution
  satisfies `‖W - u‖ ≤ ‖u * u - 1‖` with no smallness hypothesis at all.
* Given a **corner partition** — a finite family of pairwise orthogonal
  projections summing to `1` — the block compression `∑ i, P i * u * P i`
  commutes exactly with every `P i`, and the spectral sign of a Hermitian
  matrix commutes with everything the matrix commutes with.  The corrected
  involution therefore commutes exactly with the corner structure.

The commutation statement is the delicate one: it is proved by transporting to
the eigenbasis, where commuting with a diagonal matrix forces the off-diagonal
entries joining distinct eigenvalues to vanish, and any function of the
eigenvalues is then commuted with as well.  No polynomial interpolation is
needed.
-/

namespace GroupApproximation
namespace ExactInvolutionLifts

open Matrix
open KazhdanCornerMatrices
open scoped Matrix.Norms.L2Operator

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-! ## Contractivity toolbox

The repository's contractivity lemmas are stated for `FiniteModel` or assume a
nonempty coordinate type through `CStarRing.norm_of_mem_unitary`.  Everything
below is needed over a bare `Fintype`, and the vector criterion supplies it
without any nonemptiness hypothesis. -/

/-- Unitary conjugation preserves the matrix `ℓ²` operator norm, over an
arbitrary finite coordinate type. -/
theorem norm_unitary_conj {U D : Matrix Y Y ℂ}
    (hU : U ∈ Matrix.unitaryGroup Y ℂ) : ‖U * D * Uᴴ‖ = ‖D‖ := by
  have hUstar : Uᴴ ∈ Matrix.unitaryGroup Y ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact Unitary.star_mul_self_of_mem hU
  rw [CStarRing.norm_mul_mem_unitary _ hUstar,
    CStarRing.norm_mem_unitary_mul _ hU]

/-- A matrix with orthonormal columns is a contraction.  Unlike
`CStarRing.norm_of_mem_unitary` this needs no nonemptiness of `Y`. -/
theorem norm_le_one_of_conjTranspose_mul_self {u : Matrix Y Y ℂ}
    (hu : uᴴ * u = 1) : ‖u‖ ≤ 1 := by
  refine l2_opNorm_le_of_sum_normSq_general u zero_le_one fun x ↦ ?_
  rw [one_pow, one_mul]
  exact (sum_normSq_mulVec_of_star_mul_self hu x).le

/-- Orthogonal projection matrices are contractions. -/
theorem norm_le_one_of_isOrthogonalProjection {p : Matrix Y Y ℂ}
    (hp : IsOrthogonalProjectionMatrix p) : ‖p‖ ≤ 1 := by
  refine l2_opNorm_le_of_sum_normSq_general p zero_le_one fun x ↦ ?_
  rw [one_pow, one_mul]
  exact sum_normSq_mulVec_proj_le hp x

/-! ## Exact involutions -/

/-- An *exact involution* is a self-adjoint unitary: a matrix equal to its own
adjoint whose square is the identity. -/
def IsExactInvolution (R : Matrix Y Y ℂ) : Prop := Rᴴ = R ∧ R * R = 1

/-! ## Diagonal functional calculus in the eigenbasis

Every spectral object used below is a diagonal matrix conjugated by the
eigenvector unitary of a fixed Hermitian matrix.  Naming that shape once turns
the spectral estimates into entrywise estimates on the diagonal. -/

/-- The diagonal matrix `Matrix.diagonal d`, conjugated by the eigenvector
unitary of the Hermitian matrix `H`. -/
noncomputable def eigenCalc (H : Matrix Y Y ℂ) (hH : H.IsHermitian) (d : Y → ℂ) :
    Matrix Y Y ℂ :=
  (hH.eigenvectorUnitary : Matrix Y Y ℂ) * Matrix.diagonal d *
    (hH.eigenvectorUnitary : Matrix Y Y ℂ)ᴴ

/-- The eigenbasis calculus depends on the diagonal data only pointwise. -/
theorem eigenCalc_congr (H : Matrix Y Y ℂ) (hH : H.IsHermitian) {d₁ d₂ : Y → ℂ}
    (h : ∀ i, d₁ i = d₂ i) : eigenCalc H hH d₁ = eigenCalc H hH d₂ := by
  rw [show d₁ = d₂ from funext h]

/-- Differences pass through the eigenbasis calculus. -/
theorem eigenCalc_sub (H : Matrix Y Y ℂ) (hH : H.IsHermitian) (d₁ d₂ : Y → ℂ) :
    eigenCalc H hH d₁ - eigenCalc H hH d₂ =
      eigenCalc H hH (fun i ↦ d₁ i - d₂ i) := by
  have hdiag : Matrix.diagonal (fun i ↦ d₁ i - d₂ i) =
      Matrix.diagonal d₁ - Matrix.diagonal d₂ := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Matrix.diagonal_apply_ne _ hij]
  rw [eigenCalc, eigenCalc, eigenCalc, hdiag]
  noncomm_ring

/-- Scalars pass through the eigenbasis calculus. -/
theorem smul_eigenCalc (H : Matrix Y Y ℂ) (hH : H.IsHermitian) (c : ℂ)
    (d : Y → ℂ) :
    c • eigenCalc H hH d = eigenCalc H hH (fun i ↦ c * d i) := by
  have hdiag : Matrix.diagonal (fun i ↦ c * d i) = c • Matrix.diagonal d := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Matrix.diagonal_apply_ne _ hij]
  rw [eigenCalc, eigenCalc, hdiag, Matrix.mul_smul, Matrix.smul_mul]

/-- The constant function `1` gives the identity matrix. -/
theorem eigenCalc_one (H : Matrix Y Y ℂ) (hH : H.IsHermitian) :
    eigenCalc H hH (fun _ ↦ (1 : ℂ)) = 1 := by
  rw [eigenCalc, Matrix.diagonal_one, Matrix.mul_one]
  exact Unitary.mul_star_self_of_mem hH.eigenvectorUnitary.2

/-- The eigenbasis calculus is isometric from the supremum norm on diagonal
data to the matrix `ℓ²` operator norm. -/
theorem norm_eigenCalc (H : Matrix Y Y ℂ) (hH : H.IsHermitian) (d : Y → ℂ) :
    ‖eigenCalc H hH d‖ = ‖d‖ := by
  rw [eigenCalc, norm_unitary_conj hH.eigenvectorUnitary.2,
    Matrix.l2_opNorm_diagonal]

/-- The spectral theorem, in eigenbasis-calculus form. -/
theorem eq_eigenCalc_eigenvalues (H : Matrix Y Y ℂ) (hH : H.IsHermitian) :
    H = eigenCalc H hH (fun i ↦ (hH.eigenvalues i : ℂ)) := by
  calc H = Unitary.conjStarAlgAut ℂ _ hH.eigenvectorUnitary
        (Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues)) := hH.spectral_theorem
    _ = eigenCalc H hH (fun i ↦ (hH.eigenvalues i : ℂ)) := rfl

/-- Subtracting the Hermitian matrix itself stays inside the calculus. -/
theorem eigenCalc_sub_self (H : Matrix Y Y ℂ) (hH : H.IsHermitian) (d : Y → ℂ) :
    eigenCalc H hH d - H =
      eigenCalc H hH (fun i ↦ d i - (hH.eigenvalues i : ℂ)) := by
  calc eigenCalc H hH d - H
      = eigenCalc H hH d - eigenCalc H hH (fun i ↦ (hH.eigenvalues i : ℂ)) := by
        rw [← eq_eigenCalc_eigenvalues H hH]
    _ = eigenCalc H hH (fun i ↦ d i - (hH.eigenvalues i : ℂ)) :=
      eigenCalc_sub H hH _ _

/-! ## The spectral sign -/

/-- The spectral sign of a Hermitian matrix: `+1` on the strictly positive
spectral sector and `-1` on the rest.  The zero eigenvalue is assigned to the
negative sector, matching the strict threshold of `spectralAbove`. -/
noncomputable def signOfHermitian (H : Matrix Y Y ℂ) (hH : H.IsHermitian) :
    Matrix Y Y ℂ :=
  (2 : ℂ) • spectralAbove H hH 0 - 1

/-- The spectral sign in eigenbasis-calculus form. -/
theorem signOfHermitian_eq_eigenCalc (H : Matrix Y Y ℂ) (hH : H.IsHermitian) :
    signOfHermitian H hH =
      eigenCalc H hH (fun i ↦ if 0 < hH.eigenvalues i then (1 : ℂ) else -1) := by
  have hpt : ∀ i : Y,
      (2 : ℂ) * (if 0 < hH.eigenvalues i then (1 : ℂ) else 0) - (1 : ℂ)
        = if 0 < hH.eigenvalues i then (1 : ℂ) else -1 := by
    intro i
    by_cases hpos : 0 < hH.eigenvalues i
    · rw [if_pos hpos, if_pos hpos]
      norm_num
    · rw [if_neg hpos, if_neg hpos]
      norm_num
  have hcut : spectralAbove H hH 0 =
      eigenCalc H hH
        (fun i ↦ if (0 : ℝ) < hH.eigenvalues i then (1 : ℂ) else 0) := rfl
  have hstep :
      (2 : ℂ) • eigenCalc H hH
          (fun i ↦ if (0 : ℝ) < hH.eigenvalues i then (1 : ℂ) else 0)
        - eigenCalc H hH (fun _ ↦ (1 : ℂ))
        = eigenCalc H hH
          (fun i ↦ if 0 < hH.eigenvalues i then (1 : ℂ) else -1) := by
    rw [smul_eigenCalc, eigenCalc_sub]
    exact eigenCalc_congr H hH hpt
  rw [signOfHermitian, hcut, ← eigenCalc_one H hH, hstep]

/-- The spectral sign is self-adjoint. -/
theorem signOfHermitian_conjTranspose (H : Matrix Y Y ℂ) (hH : H.IsHermitian) :
    (signOfHermitian H hH)ᴴ = signOfHermitian H hH := by
  have hstar : star (2 : ℂ) = (2 : ℂ) := by norm_num
  rw [signOfHermitian, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one,
    (spectralAbove_isOrthogonalProjection H hH 0).1, hstar]

/-- The spectral sign squares to the identity.  No spectral gap is needed:
the identity `(2 * p - 1) ^ 2 = 1` holds for every idempotent `p`. -/
theorem signOfHermitian_mul_self (H : Matrix Y Y ℂ) (hH : H.IsHermitian) :
    signOfHermitian H hH * signOfHermitian H hH = 1 := by
  have hP : spectralAbove H hH 0 * spectralAbove H hH 0 = spectralAbove H hH 0 :=
    (spectralAbove_isOrthogonalProjection H hH 0).2
  have hdouble : (2 : ℂ) • spectralAbove H hH 0 =
      spectralAbove H hH 0 + spectralAbove H hH 0 := by
    module
  rw [signOfHermitian, hdouble]
  calc (spectralAbove H hH 0 + spectralAbove H hH 0 - 1) *
        (spectralAbove H hH 0 + spectralAbove H hH 0 - 1)
      = spectralAbove H hH 0 * spectralAbove H hH 0 +
          spectralAbove H hH 0 * spectralAbove H hH 0 +
          spectralAbove H hH 0 * spectralAbove H hH 0 +
          spectralAbove H hH 0 * spectralAbove H hH 0 -
          (spectralAbove H hH 0 + spectralAbove H hH 0) -
          (spectralAbove H hH 0 + spectralAbove H hH 0) + 1 := by
        noncomm_ring
    _ = 1 := by rw [hP]; abel

/-- The spectral sign of a Hermitian matrix is an exact involution, with no
hypothesis on the spectrum. -/
theorem signOfHermitian_isExactInvolution (H : Matrix Y Y ℂ)
    (hH : H.IsHermitian) : IsExactInvolution (signOfHermitian H hH) :=
  ⟨signOfHermitian_conjTranspose H hH, signOfHermitian_mul_self H hH⟩

/-- Rounding a real number to `±1` costs at most its defect from being a square
root of `1`.  The bound is `|1 - |x|| * (1 + |x|) = |1 - x ^ 2|` together with
`1 + |x| ≥ 1`; no restriction on `x` is required. -/
theorem abs_sign_sub_le_abs_sq_sub_one (x : ℝ) :
    |(if 0 < x then (1 : ℝ) else -1) - x| ≤ |x ^ 2 - 1| := by
  rcases le_or_gt x 0 with hx | hx
  · rw [if_neg (not_lt.mpr hx)]
    rcases le_or_gt (-1) x with hlow | hlow
    · rw [abs_of_nonpos (by linarith : -1 - x ≤ 0),
        abs_of_nonpos (by nlinarith : x ^ 2 - 1 ≤ 0)]
      nlinarith
    · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ -1 - x),
        abs_of_nonneg (by nlinarith : (0 : ℝ) ≤ x ^ 2 - 1)]
      nlinarith
  · rw [if_pos hx]
    rcases le_or_gt x 1 with hhigh | hhigh
    · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - x),
        abs_of_nonpos (by nlinarith : x ^ 2 - 1 ≤ 0)]
      nlinarith
    · rw [abs_of_nonpos (by linarith : 1 - x ≤ 0),
        abs_of_nonneg (by nlinarith : (0 : ℝ) ≤ x ^ 2 - 1)]
      nlinarith

/-- **Spectral rounding estimate.**  The spectral sign of a Hermitian matrix
moves it by at most its involution defect.  Explicitly, `‖H * H - 1‖ ≤ ε`
gives `‖signOfHermitian H hH - H‖ ≤ ε`, so the rounding error vanishes
linearly with the defect. -/
theorem norm_signOfHermitian_sub_le (H : Matrix Y Y ℂ) (hH : H.IsHermitian) :
    ‖signOfHermitian H hH - H‖ ≤ ‖H * H - 1‖ := by
  rw [signOfHermitian_eq_eigenCalc, eigenCalc_sub_self, norm_eigenCalc]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i ↦ ?_
  show ‖(if 0 < hH.eigenvalues i then (1 : ℂ) else -1) -
    (hH.eigenvalues i : ℂ)‖ ≤ ‖H * H - 1‖
  have hentry :
      (if 0 < hH.eigenvalues i then (1 : ℂ) else -1) - (hH.eigenvalues i : ℂ)
        = ((((if 0 < hH.eigenvalues i then (1 : ℝ) else -1) -
            hH.eigenvalues i : ℝ)) : ℂ) := by
    by_cases hpos : 0 < hH.eigenvalues i
    · rw [if_pos hpos, if_pos hpos]
      push_cast
      ring
    · rw [if_neg hpos, if_neg hpos]
      push_cast
      ring
  rw [hentry, Complex.norm_real, Real.norm_eq_abs]
  calc |(if 0 < hH.eigenvalues i then (1 : ℝ) else -1) - hH.eigenvalues i|
      ≤ |hH.eigenvalues i ^ 2 - 1| := abs_sign_sub_le_abs_sq_sub_one _
    _ ≤ ‖H * H - 1‖ :=
      ApproxInvolutionCorner.abs_hermitianEigenvalue_sq_sub_one_le H hH i

/-! ## The spectral sign lies in the commutant

The eigenbasis transport turns commutation with `H` into commutation with a
diagonal matrix, where the argument is entrywise: an off-diagonal entry
joining two distinct eigenvalues must vanish, and an entry joining two equal
eigenvalues sees equal values of any function of the spectrum. -/

/-- If a matrix commutes with `Matrix.diagonal f` then it commutes with
`Matrix.diagonal g` for every `g` that is constant on the fibres of `f`. -/
theorem commute_diagonal_of_commute_diagonal {f g : Y → ℂ}
    (hfg : ∀ i j, f i = f j → g i = g j) {N : Matrix Y Y ℂ}
    (hN : N * Matrix.diagonal f = Matrix.diagonal f * N) :
    N * Matrix.diagonal g = Matrix.diagonal g * N := by
  ext i j
  have h : (N * Matrix.diagonal f) i j = (Matrix.diagonal f * N) i j := by
    rw [hN]
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hij : f i = f j
  · rw [hfg i j hij]
    ring
  · have hzero : N i j = 0 := by
      have hprod : N i j * (f j - f i) = 0 := by
        rw [mul_sub, h]
        ring
      rcases mul_eq_zero.mp hprod with h1 | h2
      · exact h1
      · exact absurd (sub_eq_zero.mp h2).symm hij
    rw [hzero]
    ring

/-- Commutation with a unitary conjugate of `Matrix.diagonal f` transfers to
`Matrix.diagonal g` for every `g` constant on the fibres of `f`. -/
theorem commute_conj_diagonal_of_commute {U A : Matrix Y Y ℂ} {f g : Y → ℂ}
    (hUU : Uᴴ * U = 1) (hUUstar : U * Uᴴ = 1)
    (hfg : ∀ i j, f i = f j → g i = g j)
    (hA : A * (U * Matrix.diagonal f * Uᴴ) =
      (U * Matrix.diagonal f * Uᴴ) * A) :
    A * (U * Matrix.diagonal g * Uᴴ) =
      (U * Matrix.diagonal g * Uᴴ) * A := by
  have hforward : Uᴴ * (A * (U * Matrix.diagonal f * Uᴴ)) * U =
      (Uᴴ * A * U) * Matrix.diagonal f := by
    calc Uᴴ * (A * (U * Matrix.diagonal f * Uᴴ)) * U
        = Uᴴ * A * U * Matrix.diagonal f * (Uᴴ * U) := by noncomm_ring
      _ = (Uᴴ * A * U) * Matrix.diagonal f := by rw [hUU]; noncomm_ring
  have hbackward : Uᴴ * ((U * Matrix.diagonal f * Uᴴ) * A) * U =
      Matrix.diagonal f * (Uᴴ * A * U) := by
    calc Uᴴ * ((U * Matrix.diagonal f * Uᴴ) * A) * U
        = (Uᴴ * U) * Matrix.diagonal f * (Uᴴ * A * U) := by noncomm_ring
      _ = Matrix.diagonal f * (Uᴴ * A * U) := by rw [hUU]; noncomm_ring
  have hN : (Uᴴ * A * U) * Matrix.diagonal f =
      Matrix.diagonal f * (Uᴴ * A * U) := by
    rw [← hforward, hA, hbackward]
  have hNg : (Uᴴ * A * U) * Matrix.diagonal g =
      Matrix.diagonal g * (Uᴴ * A * U) :=
    commute_diagonal_of_commute_diagonal hfg hN
  have hleft : ∀ D : Matrix Y Y ℂ,
      U * ((Uᴴ * A * U) * D) * Uᴴ = A * (U * D * Uᴴ) := by
    intro D
    calc U * ((Uᴴ * A * U) * D) * Uᴴ = (U * Uᴴ) * A * (U * D * Uᴴ) := by
          noncomm_ring
      _ = A * (U * D * Uᴴ) := by rw [hUUstar]; noncomm_ring
  have hright : ∀ D : Matrix Y Y ℂ,
      U * (D * (Uᴴ * A * U)) * Uᴴ = (U * D * Uᴴ) * A := by
    intro D
    calc U * (D * (Uᴴ * A * U)) * Uᴴ = (U * D * Uᴴ) * A * (U * Uᴴ) := by
          noncomm_ring
      _ = (U * D * Uᴴ) * A := by rw [hUUstar]; noncomm_ring
  rw [← hleft (Matrix.diagonal g), hNg, hright]

/-- **Spectral projections lie in the bicommutant.**  Anything commuting with a
Hermitian matrix commutes with each of its spectral cutoffs. -/
theorem commute_spectralAbove_of_commute (H : Matrix Y Y ℂ) (hH : H.IsHermitian)
    (t : ℝ) {M : Matrix Y Y ℂ} (hM : M * H = H * M) :
    M * spectralAbove H hH t = spectralAbove H hH t * M := by
  have hUU : (hH.eigenvectorUnitary : Matrix Y Y ℂ)ᴴ *
      (hH.eigenvectorUnitary : Matrix Y Y ℂ) = 1 :=
    Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
  have hUUstar : (hH.eigenvectorUnitary : Matrix Y Y ℂ) *
      (hH.eigenvectorUnitary : Matrix Y Y ℂ)ᴴ = 1 :=
    Unitary.mul_star_self_of_mem hH.eigenvectorUnitary.2
  have hfg : ∀ i j : Y, (hH.eigenvalues i : ℂ) = (hH.eigenvalues j : ℂ) →
      (if t < hH.eigenvalues i then (1 : ℂ) else 0) =
        (if t < hH.eigenvalues j then (1 : ℂ) else 0) := by
    intro i j hij
    have hreal : hH.eigenvalues i = hH.eigenvalues j := by exact_mod_cast hij
    rw [hreal]
  have hA : M * (eigenCalc H hH (fun i ↦ (hH.eigenvalues i : ℂ))) =
      (eigenCalc H hH (fun i ↦ (hH.eigenvalues i : ℂ))) * M := by
    rw [← eq_eigenCalc_eigenvalues H hH]
    exact hM
  exact commute_conj_diagonal_of_commute hUU hUUstar hfg hA

/-- The spectral sign lies in the commutant of its argument. -/
theorem commute_signOfHermitian_of_commute (H : Matrix Y Y ℂ)
    (hH : H.IsHermitian) {M : Matrix Y Y ℂ} (hM : M * H = H * M) :
    M * signOfHermitian H hH = signOfHermitian H hH * M := by
  have hP := commute_spectralAbove_of_commute H hH 0 hM
  rw [signOfHermitian, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, hP]

/-! ## Correcting a single almost-involution unitary -/

/-- The exact involution attached to a unitary that almost squares to the
identity: the spectral sign of its self-adjoint part. -/
noncomputable def exactInvolutionCorrection (u : Matrix Y Y ℂ) : Matrix Y Y ℂ :=
  signOfHermitian (ApproxInvolutionCorner.hermitianPart u)
    (ApproxInvolutionCorner.hermitianPart_isHermitian u)

/-- The correction is an exact involution, for every matrix `u`. -/
theorem exactInvolutionCorrection_isExactInvolution (u : Matrix Y Y ℂ) :
    IsExactInvolution (exactInvolutionCorrection u) :=
  signOfHermitian_isExactInvolution _ _

/-- **Almost-involution correction.**  A unitary with `‖u * u - 1‖ ≤ ε` lies
within `ε` of an exact self-adjoint unitary.  Half the budget is spent on the
Hermitian symmetrization and half on the spectral rounding; no smallness
hypothesis on `ε` is needed. -/
theorem norm_exactInvolutionCorrection_sub_le (u : Matrix Y Y ℂ)
    (hu : u ∈ Matrix.unitaryGroup Y ℂ) :
    ‖exactInvolutionCorrection u - u‖ ≤ ‖u * u - 1‖ := by
  have hround : ‖exactInvolutionCorrection u -
      ApproxInvolutionCorner.hermitianPart u‖ ≤ (1 / 2 : ℝ) * ‖u * u - 1‖ :=
    (norm_signOfHermitian_sub_le (ApproxInvolutionCorner.hermitianPart u)
      (ApproxInvolutionCorner.hermitianPart_isHermitian u)).trans
      (ApproxInvolutionCorner.norm_hermitianPart_sq_sub_one_le_half u hu)
  have hsym : ‖ApproxInvolutionCorner.hermitianPart u - u‖ =
      (1 / 2 : ℝ) * ‖u * u - 1‖ :=
    ApproxInvolutionCorner.norm_hermitianPart_sub_eq_half_sq_defect u hu
  have hsplit : exactInvolutionCorrection u - u =
      (exactInvolutionCorrection u - ApproxInvolutionCorner.hermitianPart u) +
        (ApproxInvolutionCorner.hermitianPart u - u) := by abel
  rw [hsplit]
  calc ‖(exactInvolutionCorrection u -
        ApproxInvolutionCorner.hermitianPart u) +
        (ApproxInvolutionCorner.hermitianPart u - u)‖
      ≤ ‖exactInvolutionCorrection u -
          ApproxInvolutionCorner.hermitianPart u‖ +
        ‖ApproxInvolutionCorner.hermitianPart u - u‖ := norm_add_le _ _
    _ ≤ ‖u * u - 1‖ := by rw [hsym]; linarith

/-! ## Corner-compatible corrections

A *corner partition* is a finite family of pairwise orthogonal projections
summing to the identity.  Block compression along such a family produces a
matrix commuting exactly with every member, at a cost linear in the number of
blocks. -/

variable {ι : Type*} [Fintype ι]

/-- Block compression of a matrix along a finite family of projections. -/
def cornerCompression (P : ι → Matrix Y Y ℂ) (u : Matrix Y Y ℂ) :
    Matrix Y Y ℂ :=
  ∑ i, P i * u * P i

/-- Left multiplication by a member of the partition kills every other block.
-/
theorem mul_cornerCompression (P : ι → Matrix Y Y ℂ)
    (hproj : ∀ i, IsOrthogonalProjectionMatrix (P i))
    (horth : ∀ i j, i ≠ j → P i * P j = 0) (u : Matrix Y Y ℂ) (j : ι) :
    P j * cornerCompression P u = P j * u * P j := by
  rw [cornerCompression, Finset.mul_sum]
  refine (Finset.sum_eq_single_of_mem j (Finset.mem_univ j) ?_).trans ?_
  · intro i _ hij
    calc P j * (P i * u * P i) = (P j * P i) * u * P i := by noncomm_ring
      _ = 0 := by rw [horth j i (Ne.symm hij)]; simp
  · calc P j * (P j * u * P j) = (P j * P j) * u * P j := by noncomm_ring
      _ = P j * u * P j := by rw [(hproj j).2]

/-- Right multiplication by a member of the partition kills every other block.
-/
theorem cornerCompression_mul (P : ι → Matrix Y Y ℂ)
    (hproj : ∀ i, IsOrthogonalProjectionMatrix (P i))
    (horth : ∀ i j, i ≠ j → P i * P j = 0) (u : Matrix Y Y ℂ) (j : ι) :
    cornerCompression P u * P j = P j * u * P j := by
  rw [cornerCompression, Finset.sum_mul]
  refine (Finset.sum_eq_single_of_mem j (Finset.mem_univ j) ?_).trans ?_
  · intro i _ hij
    calc (P i * u * P i) * P j = P i * u * (P i * P j) := by noncomm_ring
      _ = 0 := by rw [horth i j hij]; simp
  · calc (P j * u * P j) * P j = P j * u * (P j * P j) := by noncomm_ring
      _ = P j * u * P j := by rw [(hproj j).2]

/-- The block compression commutes exactly with every member of the corner
partition. -/
theorem cornerCompression_comm (P : ι → Matrix Y Y ℂ)
    (hproj : ∀ i, IsOrthogonalProjectionMatrix (P i))
    (horth : ∀ i j, i ≠ j → P i * P j = 0) (u : Matrix Y Y ℂ) (j : ι) :
    P j * cornerCompression P u = cornerCompression P u * P j := by
  rw [mul_cornerCompression P hproj horth u j,
    cornerCompression_mul P hproj horth u j]

/-- Block compression along a corner partition costs at most the number of
blocks times the worst commutation defect. -/
theorem norm_cornerCompression_sub_le (P : ι → Matrix Y Y ℂ)
    (hproj : ∀ i, IsOrthogonalProjectionMatrix (P i))
    (hsum : ∑ i, P i = 1) (u : Matrix Y Y ℂ) {ε : ℝ}
    (hcomm : ∀ i, ‖P i * u - u * P i‖ ≤ ε) :
    ‖cornerCompression P u - u‖ ≤ (Fintype.card ι : ℝ) * ε := by
  have hexp : (∑ i, P i * (u * P i - P i * u)) =
      ∑ i : ι, (P i * u * P i - P i * u) :=
    Finset.sum_congr rfl fun i _ ↦ by
      calc P i * (u * P i - P i * u) = P i * u * P i - (P i * P i) * u := by
            noncomm_ring
        _ = P i * u * P i - P i * u := by rw [(hproj i).2]
  have hrewrite : cornerCompression P u - u = ∑ i, P i * (u * P i - P i * u) := by
    rw [hexp, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, Matrix.one_mul,
      cornerCompression]
  have hterm : ∀ i : ι, ‖P i * (u * P i - P i * u)‖ ≤ ε := by
    intro i
    have hswap : ‖u * P i - P i * u‖ ≤ ε := by
      rw [show u * P i - P i * u = -(P i * u - u * P i) from by abel, norm_neg]
      exact hcomm i
    calc ‖P i * (u * P i - P i * u)‖ ≤ ‖P i‖ * ‖u * P i - P i * u‖ :=
          Matrix.l2_opNorm_mul _ _
      _ ≤ 1 * ε := mul_le_mul (norm_le_one_of_isOrthogonalProjection (hproj i))
          hswap (norm_nonneg _) zero_le_one
      _ = ε := one_mul ε
  rw [hrewrite]
  calc ‖∑ i, P i * (u * P i - P i * u)‖
      ≤ ∑ i : ι, ‖P i * (u * P i - P i * u)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, ε := Finset.sum_le_sum fun i _ ↦ hterm i
    _ = (Fintype.card ι : ℝ) * ε := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The self-adjoint part of the block compression: the Hermitian matrix whose
spectral sign is the corner-compatible correction. -/
noncomputable def cornerHermitianPart (P : ι → Matrix Y Y ℂ) (u : Matrix Y Y ℂ) :
    Matrix Y Y ℂ :=
  ApproxInvolutionCorner.hermitianPart (cornerCompression P u)

omit [DecidableEq Y] in
/-- The self-adjoint part of the block compression is Hermitian. -/
theorem cornerHermitianPart_isHermitian (P : ι → Matrix Y Y ℂ)
    (u : Matrix Y Y ℂ) : (cornerHermitianPart P u).IsHermitian :=
  ApproxInvolutionCorner.hermitianPart_isHermitian _

/-- The self-adjoint part of the block compression still commutes exactly with
every member of the corner partition. -/
theorem cornerHermitianPart_comm (P : ι → Matrix Y Y ℂ)
    (hproj : ∀ i, IsOrthogonalProjectionMatrix (P i))
    (horth : ∀ i j, i ≠ j → P i * P j = 0) (u : Matrix Y Y ℂ) (j : ι) :
    P j * cornerHermitianPart P u = cornerHermitianPart P u * P j := by
  have hC : P j * cornerCompression P u = cornerCompression P u * P j :=
    cornerCompression_comm P hproj horth u j
  have hCstar : P j * (cornerCompression P u)ᴴ =
      (cornerCompression P u)ᴴ * P j := by
    have h : (P j * cornerCompression P u)ᴴ =
        (cornerCompression P u * P j)ᴴ := by rw [hC]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, (hproj j).1] at h
    exact h.symm
  rw [cornerHermitianPart, ApproxInvolutionCorner.hermitianPart,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, hC,
    hCstar]

/-- **Corner-compatible exact involution correction.**  The spectral sign of
the self-adjoint part of the block compression. -/
noncomputable def cornerInvolutionCorrection (P : ι → Matrix Y Y ℂ)
    (u : Matrix Y Y ℂ) : Matrix Y Y ℂ :=
  signOfHermitian (cornerHermitianPart P u) (cornerHermitianPart_isHermitian P u)

/-- The corner-compatible correction is an exact involution, for every `u`. -/
theorem cornerInvolutionCorrection_isExactInvolution (P : ι → Matrix Y Y ℂ)
    (u : Matrix Y Y ℂ) : IsExactInvolution (cornerInvolutionCorrection P u) :=
  signOfHermitian_isExactInvolution _ _

/-- The corner-compatible correction commutes **exactly** with every member of
the corner partition, with no hypothesis on `u`. -/
theorem cornerInvolutionCorrection_comm (P : ι → Matrix Y Y ℂ)
    (hproj : ∀ i, IsOrthogonalProjectionMatrix (P i))
    (horth : ∀ i j, i ≠ j → P i * P j = 0) (u : Matrix Y Y ℂ) (j : ι) :
    cornerInvolutionCorrection P u * P j =
      P j * cornerInvolutionCorrection P u :=
  (commute_signOfHermitian_of_commute (cornerHermitianPart P u)
    (cornerHermitianPart_isHermitian P u)
    (cornerHermitianPart_comm P hproj horth u j)).symm

/-- **Corner-compatible correction estimate.**  Let `P` be a corner partition
of `Fintype.card ι` blocks, and let `u` be a unitary with involution defect at
most `ε` and commutation defect at most `ε` against every block.  If `ε ≤ 1`
and `Fintype.card ι * ε ≤ 1`, then the corner-compatible exact involution
`cornerInvolutionCorrection P u` lies within `(5 * Fintype.card ι + 4) * ε` of
`u`.  The bound is linear in `ε` for a fixed number of blocks, hence tends to
`0` with `ε`. -/
theorem norm_cornerInvolutionCorrection_sub_le (P : ι → Matrix Y Y ℂ)
    (hproj : ∀ i, IsOrthogonalProjectionMatrix (P i))
    (hsum : ∑ i, P i = 1) {u : Matrix Y Y ℂ}
    (hu : u ∈ Matrix.unitaryGroup Y ℂ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hblocks : (Fintype.card ι : ℝ) * ε ≤ 1)
    (hinv : ‖u * u - 1‖ ≤ ε)
    (hcomm : ∀ i, ‖P i * u - u * P i‖ ≤ ε) :
    ‖cornerInvolutionCorrection P u - u‖ ≤
      5 * ((Fintype.card ι : ℝ) * ε) + 4 * ε := by
  have hCu : ‖cornerCompression P u - u‖ ≤ (Fintype.card ι : ℝ) * ε :=
    norm_cornerCompression_sub_le P hproj hsum u hcomm
  have huH : ‖u - uᴴ‖ ≤ ε := by
    rw [ApproxInvolutionCorner.norm_sub_conjTranspose_eq_norm_sq_sub_one u hu]
    exact hinv
  have hCHu : ‖(cornerCompression P u)ᴴ - u‖ ≤ (Fintype.card ι : ℝ) * ε + ε := by
    have hct : (cornerCompression P u)ᴴ - u = (cornerCompression P u - uᴴ)ᴴ := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose]
    rw [hct, ← Matrix.star_eq_conjTranspose, norm_star]
    calc ‖cornerCompression P u - uᴴ‖
        = ‖(cornerCompression P u - u) + (u - uᴴ)‖ := by
          rw [show (cornerCompression P u - u) + (u - uᴴ) =
            cornerCompression P u - uᴴ from by abel]
      _ ≤ ‖cornerCompression P u - u‖ + ‖u - uᴴ‖ := norm_add_le _ _
      _ ≤ (Fintype.card ι : ℝ) * ε + ε := add_le_add hCu huH
  have hd : ‖cornerHermitianPart P u - u‖ ≤ (Fintype.card ι : ℝ) * ε + ε / 2 := by
    have hsplit : cornerHermitianPart P u - u =
        (2 : ℂ)⁻¹ • (cornerCompression P u - u) +
          (2 : ℂ)⁻¹ • ((cornerCompression P u)ᴴ - u) := by
      rw [cornerHermitianPart, ApproxInvolutionCorner.hermitianPart]
      module
    have hscalar : ‖((2 : ℂ)⁻¹)‖ = (1 / 2 : ℝ) := by norm_num
    rw [hsplit]
    calc ‖(2 : ℂ)⁻¹ • (cornerCompression P u - u) +
          (2 : ℂ)⁻¹ • ((cornerCompression P u)ᴴ - u)‖
        ≤ ‖(2 : ℂ)⁻¹ • (cornerCompression P u - u)‖ +
          ‖(2 : ℂ)⁻¹ • ((cornerCompression P u)ᴴ - u)‖ := norm_add_le _ _
      _ = (1 / 2 : ℝ) * ‖cornerCompression P u - u‖ +
          (1 / 2 : ℝ) * ‖(cornerCompression P u)ᴴ - u‖ := by
        rw [norm_smul, norm_smul, hscalar]
      _ ≤ (Fintype.card ι : ℝ) * ε + ε / 2 := by linarith
  have hnu : ‖u‖ ≤ 1 :=
    norm_le_one_of_conjTranspose_mul_self (Unitary.star_mul_self_of_mem hu)
  have hnh : ‖cornerHermitianPart P u‖ ≤
      ‖u‖ + ‖cornerHermitianPart P u - u‖ := by
    calc ‖cornerHermitianPart P u‖
        = ‖u + (cornerHermitianPart P u - u)‖ := by
          rw [show u + (cornerHermitianPart P u - u) = cornerHermitianPart P u
            from by abel]
      _ ≤ ‖u‖ + ‖cornerHermitianPart P u - u‖ := norm_add_le _ _
  have hsq : ‖cornerHermitianPart P u * cornerHermitianPart P u - 1‖ ≤
      ‖cornerHermitianPart P u‖ * ‖cornerHermitianPart P u - u‖ +
        ‖cornerHermitianPart P u - u‖ * ‖u‖ + ε := by
    have hdecomp : cornerHermitianPart P u * cornerHermitianPart P u - 1 =
        cornerHermitianPart P u * (cornerHermitianPart P u - u) +
          (cornerHermitianPart P u - u) * u + (u * u - 1) := by noncomm_ring
    rw [hdecomp]
    calc ‖cornerHermitianPart P u * (cornerHermitianPart P u - u) +
          (cornerHermitianPart P u - u) * u + (u * u - 1)‖
        ≤ ‖cornerHermitianPart P u * (cornerHermitianPart P u - u) +
            (cornerHermitianPart P u - u) * u‖ + ‖u * u - 1‖ := norm_add_le _ _
      _ ≤ (‖cornerHermitianPart P u * (cornerHermitianPart P u - u)‖ +
            ‖(cornerHermitianPart P u - u) * u‖) + ‖u * u - 1‖ :=
          add_le_add (norm_add_le _ _) (le_refl _)
      _ ≤ (‖cornerHermitianPart P u‖ * ‖cornerHermitianPart P u - u‖ +
            ‖cornerHermitianPart P u - u‖ * ‖u‖) + ε :=
          add_le_add (add_le_add (Matrix.l2_opNorm_mul _ _)
            (Matrix.l2_opNorm_mul _ _)) hinv
  have hW : ‖cornerInvolutionCorrection P u - cornerHermitianPart P u‖ ≤
      ‖cornerHermitianPart P u * cornerHermitianPart P u - 1‖ :=
    norm_signOfHermitian_sub_le (cornerHermitianPart P u)
      (cornerHermitianPart_isHermitian P u)
  have hfinal : ‖cornerInvolutionCorrection P u - u‖ ≤
      ‖cornerInvolutionCorrection P u - cornerHermitianPart P u‖ +
        ‖cornerHermitianPart P u - u‖ := by
    calc ‖cornerInvolutionCorrection P u - u‖
        = ‖(cornerInvolutionCorrection P u - cornerHermitianPart P u) +
            (cornerHermitianPart P u - u)‖ := by
          rw [show (cornerInvolutionCorrection P u - cornerHermitianPart P u) +
            (cornerHermitianPart P u - u) =
              cornerInvolutionCorrection P u - u from by abel]
      _ ≤ ‖cornerInvolutionCorrection P u - cornerHermitianPart P u‖ +
          ‖cornerHermitianPart P u - u‖ := norm_add_le _ _
  have hd0 : 0 ≤ ‖cornerHermitianPart P u - u‖ := norm_nonneg _
  have hdle : ‖cornerHermitianPart P u - u‖ ≤ 3 / 2 := by linarith
  have hhle : ‖cornerHermitianPart P u‖ ≤ 5 / 2 := by linarith
  have hp1 : ‖cornerHermitianPart P u‖ * ‖cornerHermitianPart P u - u‖ ≤
      (5 / 2) * ‖cornerHermitianPart P u - u‖ :=
    mul_le_mul_of_nonneg_right hhle hd0
  have hp2 : ‖cornerHermitianPart P u - u‖ * ‖u‖ ≤
      ‖cornerHermitianPart P u - u‖ * 1 :=
    mul_le_mul_of_nonneg_left hnu hd0
  have hblocks0 : 0 ≤ (Fintype.card ι : ℝ) * ε :=
    mul_nonneg (Nat.cast_nonneg _) hε0
  linarith

/-! ## The two-block corner partition of an exact involution

The corner partition supplied by a single exact involution has two blocks, its
positive and negative spectral sectors.  Correcting against that partition is
the elementary step of the iteration: it produces an exact involution
commuting with the given one, and — crucially — it never leaves the commutant,
so exact commutations already achieved are preserved. -/

/-- The positive affine cut `(1 + S) / 2`. -/
noncomputable def affineCut (S : Matrix Y Y ℂ) : Matrix Y Y ℂ :=
  (2 : ℂ)⁻¹ • (1 + S)

/-- The affine cut of a self-adjoint unitary is an orthogonal projection. -/
theorem affineCut_isOrthogonalProjection {S : Matrix Y Y ℂ} (hstar : Sᴴ = S)
    (hsq : S * S = 1) : IsOrthogonalProjectionMatrix (affineCut S) := by
  constructor
  · rw [affineCut, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
      Matrix.conjTranspose_one, hstar]
    norm_num
  · rw [affineCut, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    calc ((2 : ℂ)⁻¹ * 2⁻¹) • ((1 + S) * (1 + S))
        = ((2 : ℂ)⁻¹ * 2⁻¹) • ((2 : ℂ) • (1 + S)) := by
          congr 1
          calc (1 + S) * (1 + S) = 1 + S + S + S * S := by noncomm_ring
            _ = (2 : ℂ) • (1 + S) := by rw [hsq]; module
      _ = (2 : ℂ)⁻¹ • (1 + S) := by norm_num [smul_smul]

/-- The two affine cuts of a self-adjoint unitary are orthogonal. -/
theorem affineCut_mul_neg {S : Matrix Y Y ℂ} (hsq : S * S = 1) :
    affineCut S * affineCut (-S) = 0 := by
  rw [affineCut, affineCut, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    show (1 + S) * (1 + -S) = 1 - S * S from by noncomm_ring, hsq, sub_self,
    smul_zero]

omit [Fintype Y] in
/-- The two affine cuts sum to the identity. -/
theorem affineCut_add_neg (S : Matrix Y Y ℂ) :
    affineCut S + affineCut (-S) = 1 := by
  rw [affineCut, affineCut]
  module

omit [Fintype Y] in
/-- The two affine cuts recover the matrix as their difference. -/
theorem affineCut_sub_neg (S : Matrix Y Y ℂ) :
    affineCut S - affineCut (-S) = S := by
  rw [affineCut, affineCut]
  module

/-- The commutation defect of an affine cut is half the commutation defect of
its argument. -/
theorem affineCut_comm_sub (S v : Matrix Y Y ℂ) :
    affineCut S * v - v * affineCut S = (2 : ℂ)⁻¹ • (S * v - v * S) := by
  rw [affineCut, Matrix.smul_mul, Matrix.mul_smul, ← smul_sub]
  congr 1
  noncomm_ring

/-- Anything commuting with `S` commutes with its affine cut. -/
theorem commute_affineCut_of_commute {S M : Matrix Y Y ℂ} (hMS : M * S = S * M) :
    M * affineCut S = affineCut S * M := by
  rw [affineCut, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, hMS]

/-- The two spectral cuts of an exact involution, indexed by `Bool`:
`involutionCut R false = (1 + R) / 2` is the positive sector and
`involutionCut R true = (1 - R) / 2` the negative one. -/
noncomputable def involutionCut (R : Matrix Y Y ℂ) : Bool → Matrix Y Y ℂ
  | false => affineCut R
  | true => affineCut (-R)

/-- The negated exact involution is again an exact involution. -/
theorem IsExactInvolution.neg {R : Matrix Y Y ℂ} (hR : IsExactInvolution R) :
    IsExactInvolution (-R) := by
  constructor
  · rw [Matrix.conjTranspose_neg, hR.1]
  · rw [Matrix.neg_mul, Matrix.mul_neg, neg_neg]
    exact hR.2

/-- An exact involution is a unitary matrix. -/
theorem IsExactInvolution.mem_unitaryGroup {R : Matrix Y Y ℂ}
    (hR : IsExactInvolution R) : R ∈ Matrix.unitaryGroup Y ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, hR.1]
  exact hR.2

/-- An exact involution is a contraction. -/
theorem IsExactInvolution.norm_le_one {R : Matrix Y Y ℂ}
    (hR : IsExactInvolution R) : ‖R‖ ≤ 1 :=
  norm_le_one_of_conjTranspose_mul_self (by rw [hR.1]; exact hR.2)

/-- Both spectral cuts of an exact involution are orthogonal projections. -/
theorem involutionCut_isOrthogonalProjection {R : Matrix Y Y ℂ}
    (hR : IsExactInvolution R) (b : Bool) :
    IsOrthogonalProjectionMatrix (involutionCut R b) := by
  cases b
  · simp only [involutionCut]
    exact affineCut_isOrthogonalProjection hR.1 hR.2
  · simp only [involutionCut]
    exact affineCut_isOrthogonalProjection hR.neg.1 hR.neg.2

/-- The two spectral cuts of an exact involution are orthogonal. -/
theorem involutionCut_orthogonal {R : Matrix Y Y ℂ}
    (hR : IsExactInvolution R) (b b' : Bool) (hbb : b ≠ b') :
    involutionCut R b * involutionCut R b' = 0 := by
  cases b <;> cases b'
  · exact absurd rfl hbb
  · simp only [involutionCut]
    exact affineCut_mul_neg hR.2
  · simp only [involutionCut]
    have h : affineCut (-R) * affineCut (-(-R)) = 0 := affineCut_mul_neg hR.neg.2
    rwa [neg_neg] at h
  · exact absurd rfl hbb

omit [Fintype Y] in
/-- The two spectral cuts of an exact involution sum to the identity. -/
theorem involutionCut_sum (R : Matrix Y Y ℂ) : ∑ b, involutionCut R b = 1 := by
  rw [Fintype.sum_bool]
  simp only [involutionCut]
  rw [add_comm (affineCut (-R)) (affineCut R)]
  exact affineCut_add_neg R

omit [Fintype Y] in
/-- The exact involution is the difference of its two spectral cuts. -/
theorem involutionCut_sub (R : Matrix Y Y ℂ) :
    involutionCut R false - involutionCut R true = R := by
  simp only [involutionCut]
  exact affineCut_sub_neg R

/-- The commutation defect of a spectral cut is half the commutation defect of
the involution. -/
theorem norm_involutionCut_comm (R v : Matrix Y Y ℂ) (b : Bool) :
    ‖involutionCut R b * v - v * involutionCut R b‖ =
      (1 / 2 : ℝ) * ‖R * v - v * R‖ := by
  have hscalar : ‖((2 : ℂ)⁻¹)‖ = (1 / 2 : ℝ) := by norm_num
  cases b
  · simp only [involutionCut]
    rw [affineCut_comm_sub, norm_smul, hscalar]
  · simp only [involutionCut]
    rw [affineCut_comm_sub, norm_smul, hscalar]
    congr 1
    rw [show (-R) * v - v * (-R) = -(R * v - v * R) from by noncomm_ring,
      norm_neg]

/-- Anything commuting with an exact involution commutes with both of its
spectral cuts. -/
theorem commute_involutionCut_of_commute {R M : Matrix Y Y ℂ}
    (hMR : M * R = R * M) (b : Bool) :
    M * involutionCut R b = involutionCut R b * M := by
  cases b
  · simp only [involutionCut]
    exact commute_affineCut_of_commute hMR
  · simp only [involutionCut]
    refine commute_affineCut_of_commute ?_
    rw [Matrix.mul_neg, Matrix.neg_mul, hMR]

/-! ## One correction step against a single exact involution -/

/-- One correction step: the exact involution obtained from `v` by correcting
against the two-block corner partition of the exact involution `R`. -/
noncomputable def involutionStep (R v : Matrix Y Y ℂ) : Matrix Y Y ℂ :=
  cornerInvolutionCorrection (involutionCut R) v

/-- The corrected matrix is an exact involution, for every `R` and `v`. -/
theorem involutionStep_isExactInvolution (R v : Matrix Y Y ℂ) :
    IsExactInvolution (involutionStep R v) :=
  cornerInvolutionCorrection_isExactInvolution _ _

/-- The corrected matrix commutes **exactly** with the involution it was
corrected against, with no hypothesis on `v`. -/
theorem involutionStep_comm {R : Matrix Y Y ℂ} (hR : IsExactInvolution R)
    (v : Matrix Y Y ℂ) : involutionStep R v * R = R * involutionStep R v := by
  have hcut : ∀ b : Bool,
      cornerInvolutionCorrection (involutionCut R) v * involutionCut R b =
        involutionCut R b * cornerInvolutionCorrection (involutionCut R) v :=
    fun b ↦ cornerInvolutionCorrection_comm (involutionCut R)
      (involutionCut_isOrthogonalProjection hR) (involutionCut_orthogonal hR) v b
  rw [involutionStep]
  calc cornerInvolutionCorrection (involutionCut R) v * R
      = cornerInvolutionCorrection (involutionCut R) v *
          (involutionCut R false - involutionCut R true) := by
        rw [involutionCut_sub]
    _ = (involutionCut R false - involutionCut R true) *
          cornerInvolutionCorrection (involutionCut R) v := by
        rw [Matrix.mul_sub, Matrix.sub_mul, hcut false, hcut true]
    _ = R * cornerInvolutionCorrection (involutionCut R) v := by
        rw [involutionCut_sub]

/-- **The step never leaves the commutant.**  A self-adjoint matrix commuting
with both `v` and `R` still commutes with the corrected involution.  This is
what makes the correction iterable: commutations achieved at earlier steps are
preserved exactly. -/
theorem involutionStep_commutant {R v M : Matrix Y Y ℂ} (hM : Mᴴ = M)
    (hMv : M * v = v * M) (hMR : M * R = R * M) :
    M * involutionStep R v = involutionStep R v * M := by
  have hMcut : ∀ b : Bool,
      M * involutionCut R b = involutionCut R b * M :=
    commute_involutionCut_of_commute hMR
  have hC : M * cornerCompression (involutionCut R) v =
      cornerCompression (involutionCut R) v * M := by
    rw [cornerCompression, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    calc M * (involutionCut R b * v * involutionCut R b)
        = (M * involutionCut R b) * v * involutionCut R b := by noncomm_ring
      _ = involutionCut R b * (M * v) * involutionCut R b := by
          rw [hMcut b]; noncomm_ring
      _ = involutionCut R b * v * (M * involutionCut R b) := by
          rw [hMv]; noncomm_ring
      _ = involutionCut R b * v * involutionCut R b * M := by
          rw [hMcut b]; noncomm_ring
  have hCstar : M * (cornerCompression (involutionCut R) v)ᴴ =
      (cornerCompression (involutionCut R) v)ᴴ * M := by
    have h : (M * cornerCompression (involutionCut R) v)ᴴ =
        (cornerCompression (involutionCut R) v * M)ᴴ := by rw [hC]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hM] at h
    exact h.symm
  have hH : M * cornerHermitianPart (involutionCut R) v =
      cornerHermitianPart (involutionCut R) v * M := by
    rw [cornerHermitianPart, ApproxInvolutionCorner.hermitianPart,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, hC,
      hCstar]
  exact commute_signOfHermitian_of_commute _ _ hH

/-- **Step estimate.**  Correcting an exact involution `v` against another
exact involution `R` moves it by at most seven times their commutation
defect. -/
theorem norm_involutionStep_sub_le {R v : Matrix Y Y ℂ}
    (hR : IsExactInvolution R) (hv : IsExactInvolution v) {η : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hcomm : ‖R * v - v * R‖ ≤ η) :
    ‖involutionStep R v - v‖ ≤ 7 * η := by
  have hinv : ‖v * v - 1‖ ≤ η / 2 := by
    rw [hv.2, sub_self, norm_zero]
    linarith
  have hcuts : ∀ b : Bool,
      ‖involutionCut R b * v - v * involutionCut R b‖ ≤ η / 2 := by
    intro b
    rw [norm_involutionCut_comm]
    linarith
  have hcard : ((Fintype.card Bool : ℕ) : ℝ) = 2 := by
    rw [Fintype.card_bool]
    norm_num
  have hmain := norm_cornerInvolutionCorrection_sub_le (involutionCut R)
    (involutionCut_isOrthogonalProjection hR) (involutionCut_sum R)
    hv.mem_unitaryGroup (by linarith : (0 : ℝ) ≤ η / 2)
    (by linarith : η / 2 ≤ 1)
    (by rw [hcard]; linarith : ((Fintype.card Bool : ℕ) : ℝ) * (η / 2) ≤ 1)
    hinv hcuts
  rw [hcard] at hmain
  rw [involutionStep]
  linarith

/-- Commutation defects degrade by at most twice the distance moved. -/
theorem norm_comm_sub_le_of_norm_sub_le {S v W : Matrix Y Y ℂ}
    (hS : IsExactInvolution S) {η δ : ℝ} (hcomm : ‖S * v - v * S‖ ≤ η)
    (hd : ‖W - v‖ ≤ δ) : ‖S * W - W * S‖ ≤ η + 2 * δ := by
  have hsplit : S * W - W * S =
      S * (W - v) + (S * v - v * S) + (v - W) * S := by noncomm_ring
  have hleft : ‖S * (W - v)‖ ≤ δ := by
    calc ‖S * (W - v)‖ ≤ ‖S‖ * ‖W - v‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ 1 * δ := mul_le_mul hS.norm_le_one hd (norm_nonneg _) zero_le_one
      _ = δ := one_mul δ
  have hright : ‖(v - W) * S‖ ≤ δ := by
    have hswap : ‖v - W‖ ≤ δ := by
      rw [show v - W = -(W - v) from by abel, norm_neg]
      exact hd
    calc ‖(v - W) * S‖ ≤ ‖v - W‖ * ‖S‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ δ * 1 := mul_le_mul hswap hS.norm_le_one (norm_nonneg _)
        (le_trans (norm_nonneg _) hswap)
      _ = δ := mul_one δ
  rw [hsplit]
  calc ‖S * (W - v) + (S * v - v * S) + (v - W) * S‖
      ≤ ‖S * (W - v) + (S * v - v * S)‖ + ‖(v - W) * S‖ := norm_add_le _ _
    _ ≤ (‖S * (W - v)‖ + ‖S * v - v * S‖) + ‖(v - W) * S‖ :=
      add_le_add (norm_add_le _ _) (le_refl _)
    _ ≤ η + 2 * δ := by linarith

/-! ## Iterating over a finite family of commuting involutions -/

omit [Fintype ι] in
/-- **Simultaneous exact commutation.**  Let `R` be a family of pairwise
commuting exact involutions and let `v` be an exact involution whose
commutation defect against every `R i`, `i ∈ s`, is at most `η`.  If
`15 ^ s.card * η ≤ 1`, there is an exact involution commuting *exactly* with
every `R i` for `i ∈ s` and within `(15 ^ s.card - 1) * η` of `v`.

The correction is obtained one involution at a time; the constant `15` is the
product of the step constant `7` with the degradation `η ↦ η + 2 δ` of the
commutation defects, and each step preserves the exact commutations already
achieved because the construction stays inside the commutant. -/
theorem exists_isExactInvolution_comm_of_isExactInvolution
    (R : ι → Matrix Y Y ℂ) (hR : ∀ i, IsExactInvolution (R i))
    (hRcomm : ∀ i j, R i * R j = R j * R i) (s : Finset ι)
    {v : Matrix Y Y ℂ} (hv : IsExactInvolution v) {η : ℝ} (hη0 : 0 ≤ η) :
    (15 : ℝ) ^ s.card * η ≤ 1 →
    (∀ i ∈ s, ‖R i * v - v * R i‖ ≤ η) →
    ∃ W : Matrix Y Y ℂ, IsExactInvolution W ∧ (∀ i ∈ s, W * R i = R i * W) ∧
      ‖W - v‖ ≤ ((15 : ℝ) ^ s.card - 1) * η := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro _ _
      exact ⟨v, hv, by simp, by simp⟩
  | @insert a s ha ih =>
      intro hsmall hcomm
      have hcard : (insert a s).card = s.card + 1 :=
        Finset.card_insert_of_notMem ha
      rw [hcard, show (15 : ℝ) ^ (s.card + 1) = 15 * (15 : ℝ) ^ s.card from by
        ring] at hsmall
      have hp0 : (0 : ℝ) ≤ (15 : ℝ) ^ s.card := by positivity
      have hp1 : (1 : ℝ) ≤ (15 : ℝ) ^ s.card := one_le_pow₀ (by norm_num)
      have hpη0 : (0 : ℝ) ≤ (15 : ℝ) ^ s.card * η := mul_nonneg hp0 hη0
      have hpηη : η ≤ (15 : ℝ) ^ s.card * η := le_mul_of_one_le_left hη0 hp1
      obtain ⟨Ws, hWs, hWsComm, hWsd⟩ :=
        ih (by linarith) fun i hi ↦ hcomm i (Finset.mem_insert_of_mem hi)
      have hRa : ‖R a * Ws - Ws * R a‖ ≤
          η + 2 * (((15 : ℝ) ^ s.card - 1) * η) :=
        norm_comm_sub_le_of_norm_sub_le (hR a)
          (hcomm a (Finset.mem_insert_self a s)) hWsd
      have hηa0 : (0 : ℝ) ≤ η + 2 * (((15 : ℝ) ^ s.card - 1) * η) := by linarith
      have hηa1 : η + 2 * (((15 : ℝ) ^ s.card - 1) * η) ≤ 1 := by linarith
      have hstep : ‖involutionStep (R a) Ws - Ws‖ ≤
          7 * (η + 2 * (((15 : ℝ) ^ s.card - 1) * η)) :=
        norm_involutionStep_sub_le (hR a) hWs hηa0 hηa1 hRa
      refine ⟨involutionStep (R a) Ws, involutionStep_isExactInvolution _ _,
        ?_, ?_⟩
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi'
        · exact involutionStep_comm (hR i) Ws
        · exact (involutionStep_commutant (hR i).1 (hWsComm i hi').symm
            (hRcomm i a)).symm
      · rw [hcard, show (15 : ℝ) ^ (s.card + 1) = 15 * (15 : ℝ) ^ s.card from by
          ring]
        calc ‖involutionStep (R a) Ws - v‖
            = ‖(involutionStep (R a) Ws - Ws) + (Ws - v)‖ := by
              rw [show (involutionStep (R a) Ws - Ws) + (Ws - v) =
                involutionStep (R a) Ws - v from by abel]
          _ ≤ ‖involutionStep (R a) Ws - Ws‖ + ‖Ws - v‖ := norm_add_le _ _
          _ ≤ (15 * (15 : ℝ) ^ s.card - 1) * η := by nlinarith

omit [Fintype ι] in
/-- **Iterated correction of an almost-involution unitary.**  A unitary `u`
with involution defect at most `ε` and commutation defect at most `ε` against
each of finitely many pairwise commuting exact involutions is within
`3 * 15 ^ s.card * ε` of an exact involution commuting *exactly* with all of
them, provided `15 ^ s.card * (3 * ε) ≤ 1`. -/
theorem exists_isExactInvolution_comm_of_unitary
    (R : ι → Matrix Y Y ℂ) (hR : ∀ i, IsExactInvolution (R i))
    (hRcomm : ∀ i j, R i * R j = R j * R i) (s : Finset ι)
    {u : Matrix Y Y ℂ} (hu : u ∈ Matrix.unitaryGroup Y ℂ) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hsmall : (15 : ℝ) ^ s.card * (3 * ε) ≤ 1)
    (hinv : ‖u * u - 1‖ ≤ ε)
    (hcomm : ∀ i ∈ s, ‖R i * u - u * R i‖ ≤ ε) :
    ∃ W : Matrix Y Y ℂ, IsExactInvolution W ∧ (∀ i ∈ s, W * R i = R i * W) ∧
      ‖W - u‖ ≤ 3 * ((15 : ℝ) ^ s.card * ε) := by
  have hvd : ‖exactInvolutionCorrection u - u‖ ≤ ε :=
    (norm_exactInvolutionCorrection_sub_le u hu).trans hinv
  have hvcomm : ∀ i ∈ s,
      ‖R i * exactInvolutionCorrection u -
        exactInvolutionCorrection u * R i‖ ≤ 3 * ε := by
    intro i hi
    have h := norm_comm_sub_le_of_norm_sub_le (hR i) (hcomm i hi) hvd
    linarith
  obtain ⟨W, hW, hWcomm, hWd⟩ :=
    exists_isExactInvolution_comm_of_isExactInvolution R hR hRcomm s
      (exactInvolutionCorrection_isExactInvolution u) (by linarith : (0 : ℝ) ≤ 3 * ε)
      hsmall hvcomm
  refine ⟨W, hW, hWcomm, ?_⟩
  have hp0 : (0 : ℝ) ≤ (15 : ℝ) ^ s.card := by positivity
  have hp1 : (1 : ℝ) ≤ (15 : ℝ) ^ s.card := one_le_pow₀ (by norm_num)
  calc ‖W - u‖
      = ‖(W - exactInvolutionCorrection u) +
          (exactInvolutionCorrection u - u)‖ := by
        rw [show (W - exactInvolutionCorrection u) +
          (exactInvolutionCorrection u - u) = W - u from by abel]
    _ ≤ ‖W - exactInvolutionCorrection u‖ +
        ‖exactInvolutionCorrection u - u‖ := norm_add_le _ _
    _ ≤ 3 * ((15 : ℝ) ^ s.card * ε) := by nlinarith

end ExactInvolutionLifts
end GroupApproximation
