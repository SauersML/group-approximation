import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedRouteAnalyticFacts

/-!
# `Ad(V)` on the Hilbert--Schmidt space, as a matrix

`non_mf_groups_exist.tex`, the rewritten proof of Theorem `thm:transport`:

> For unitaries `A, B`, `‖Ad(A) − Ad(B)‖ ≤ 2‖A − B‖`, where the norm on the
> left is the operator norm on the Hilbert space `(M_{d_n}(ℂ), ‖·‖₂)`, so the
> maps `Ad(V_n(g))` are asymptotically multiplicative in operator norm and
> `σ̃(g) = [Ad(V_n(g))]_n ∈ U(𝓑)` … is a homomorphism, where
> `𝓑 = ∏_n B(M_{d_n}(ℂ)) / ⊕_n B(M_{d_n}(ℂ))`.  The algebra `𝓑` is a norm
> matrix corona with coordinate sizes `d_n²` after a choice of matrix units.

This module is that sentence's first half: the choice of matrix units, made
explicit.  `adMatrix V` is the matrix of `x ↦ V x V*` in the matrix-unit basis
of `M_Y(ℂ)`, an element of `M_{Y × Y}(ℂ)`, so `B(M_{d_n}(ℂ))` *is* a matrix
algebra of size `d_n²` and `𝓑` is a `NormMatrixCStarCorona` over the square
models.

What is proved here:

* `adMatrix` is a unital `⋆`-homomorphism of `M_Y(ℂ)` into `M_{Y×Y}(ℂ)` — the
  Kronecker product `V ⊗ V̄` — so it carries unitaries to unitaries;
* `adMatrix_mulVec` identifies its action on a vector with the printed
  `x ↦ V x V*`, under the vectorization `unvec`;
* `norm_adMatrix_sub_le` is the printed estimate `‖Ad(A) − Ad(B)‖ ≤ 2‖A − B‖`
  for contractions, in the `L2Operator` norm of `M_{Y×Y}(ℂ)`.

The normalization of the printed `‖·‖₂` costs nothing: `‖x‖₂` is
`(card Y)^{-1/2}` times the Euclidean norm of the vectorization, and a
positive scalar multiple of an inner product changes neither the unitary group
nor any operator norm.  `norm_sq_eq_card_mul_hsNormSq` is that bookkeeping,
and it is where the factor is discharged.

What is *not* here: the corona `𝓑` itself, the Kazhdan projection in it, and
the characterization of `𝒞₂(V,L)`.  See
`notes/nonmf-lane-reports/printed-route.md`.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace HilbertSchmidtAdMatrix

open Filter Matrix Topology
open scoped Matrix.Norms.L2Operator

noncomputable section

/-! ## The matrix of `Ad(V)` -/

variable (Y : FiniteModel)

/-- **The square model.**  `M_{Y×Y}(ℂ)` is the algebra of operators on the
Hilbert--Schmidt space of `M_Y(ℂ)`, which is the printed "coordinate sizes
`d_n²` after a choice of matrix units". -/
abbrev sqModel : FiniteModel := ⟨Y × Y, inferInstance, inferInstance⟩

/-- **The matrix of `Ad(V) : x ↦ V x V*`** in the matrix-unit basis, i.e. the
Kronecker product `V ⊗ V̄`. -/
def adMatrix (V : Matrix Y Y ℂ) : Matrix (Y × Y) (Y × Y) ℂ :=
  Matrix.of fun p r ↦ V p.1 r.1 * (starRingEnd ℂ) (V p.2 r.2)

@[simp] theorem adMatrix_apply (V : Matrix Y Y ℂ) (p r : Y × Y) :
    adMatrix Y V p r = V p.1 r.1 * (starRingEnd ℂ) (V p.2 r.2) := rfl

theorem adMatrix_one : adMatrix Y (1 : Matrix Y Y ℂ) = 1 := by
  ext p r
  by_cases h1 : p.1 = r.1 <;> by_cases h2 : p.2 = r.2 <;>
    simp [adMatrix_apply, Matrix.one_apply, h1, h2, Prod.ext_iff]

theorem adMatrix_mul (V W : Matrix Y Y ℂ) :
    adMatrix Y (V * W) = adMatrix Y V * adMatrix Y W := by
  ext p r
  simp only [adMatrix_apply, Matrix.mul_apply, map_sum, map_mul]
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ by ring

theorem adMatrix_conjTranspose (V : Matrix Y Y ℂ) :
    (adMatrix Y V)ᴴ = adMatrix Y Vᴴ := by
  ext p r
  simp only [Matrix.conjTranspose_apply, adMatrix_apply, map_mul,
    RingHomCompTriple.comp_apply, RingHom.id_apply, RCLike.star_def]

theorem adMatrix_mem_unitary {V : Matrix Y Y ℂ}
    (hV : V ∈ Matrix.unitaryGroup Y ℂ) :
    adMatrix Y V ∈ Matrix.unitaryGroup (Y × Y) ℂ := by
  have hstar : star V * V = 1 := Unitary.star_mul_self_of_mem hV
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    adMatrix_conjTranspose, ← adMatrix_mul,
    show Vᴴ * V = 1 by rw [← Matrix.star_eq_conjTranspose]; exact hstar]
  exact adMatrix_one Y

/-! ## The vectorization -/

/-- **The printed matrix units.**  A vector of the Hilbert--Schmidt space read
back as a matrix. -/
def unvec (x : EuclideanSpace ℂ (Y × Y)) : Matrix Y Y ℂ :=
  Matrix.of fun i j ↦ x (i, j)

@[simp] theorem unvec_apply (x : EuclideanSpace ℂ (Y × Y)) (i j : Y) :
    unvec Y x i j = x (i, j) := rfl

/-- **`Ad(V)` acts as the printed `x ↦ V x V*`.** -/
theorem unvec_adMatrix_mulVec (V : Matrix Y Y ℂ)
    (x : EuclideanSpace ℂ (Y × Y)) :
    Matrix.of (fun i j ↦ (adMatrix Y V *ᵥ (x : Y × Y → ℂ)) (i, j))
      = V * unvec Y x * Vᴴ := by
  ext i j
  simp only [Matrix.of_apply, Matrix.mulVec, dotProduct, adMatrix_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, unvec_apply, RCLike.star_def]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ ↦ by ring

/-- **The normalization bookkeeping.**  The Euclidean norm of a vector is
`(card Y)^{1/2}` times the printed normalized Hilbert--Schmidt norm of the
matrix it names. -/
theorem norm_sq_eq_card_mul_hsNormSq (hY : 0 < Fintype.card Y)
    (x : EuclideanSpace ℂ (Y × Y)) :
    ‖x‖ ^ 2 = (Fintype.card Y : ℝ) * hsNormSq Y (unvec Y x) := by
  have hcard : (Fintype.card Y : ℝ) ≠ 0 := by
    exact_mod_cast hY.ne'
  rw [EuclideanSpace.norm_sq_eq, hsNormSq, mul_div_cancel₀ _ hcard,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Complex.normSq_eq_norm_sq]
  rfl

/-! ## The printed estimate -/

/-- **`‖Ad(A) − Ad(B)‖₂ ≤ 2‖A − B‖` in the Hilbert--Schmidt norm.**  The
splitting `A x A* − B x B* = (A − B) x A* + B x (A* − B*)` and the two mixed
estimates of `Sofic/LeavittTraceFloor.lean`. -/
theorem hsNormSq_conj_sub_conj_le {A B : Matrix Y Y ℂ}
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (M : Matrix Y Y ℂ) :
    hsNormSq Y (A * M * Aᴴ - B * M * Bᴴ)
      ≤ 4 * ‖A - B‖ ^ 2 * hsNormSq Y M := by
  have hsplit : A * M * Aᴴ - B * M * Bᴴ
      = (A - B) * M * Aᴴ + B * M * (Aᴴ - Bᴴ) := by noncomm_ring
  have hAH : ‖Aᴴ‖ ≤ 1 := by rwa [Matrix.l2_opNorm_conjTranspose]
  have hABH : ‖Aᴴ - Bᴴ‖ = ‖A - B‖ := by
    rw [← Matrix.conjTranspose_sub, Matrix.l2_opNorm_conjTranspose]
  have hMnn := hsNormSq_nonneg Y M
  have hleft : hsNormSq Y ((A - B) * M * Aᴴ)
      ≤ ‖A - B‖ ^ 2 * hsNormSq Y M := by
    refine (hsNormSq_mul_le_sq_l2_opNorm_right Y ((A - B) * M) Aᴴ).trans ?_
    refine le_trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) hAH 2)
      (hsNormSq_nonneg Y ((A - B) * M))) ?_
    rw [one_pow, one_mul]
    exact hsNormSq_mul_le_sq_l2_opNorm_mul Y (A - B) M
  have hright : hsNormSq Y (B * M * (Aᴴ - Bᴴ))
      ≤ ‖A - B‖ ^ 2 * hsNormSq Y M := by
    refine (hsNormSq_mul_le_sq_l2_opNorm_right Y (B * M) (Aᴴ - Bᴴ)).trans ?_
    rw [hABH]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    refine (hsNormSq_mul_le_sq_l2_opNorm_mul Y B M).trans ?_
    refine le_trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) hB 2) hMnn) ?_
    rw [one_pow, one_mul]
  rw [hsplit]
  have hadd := hsNormSq_add_le Y ((A - B) * M * Aᴴ) (B * M * (Aᴴ - Bᴴ))
  nlinarith [hadd, hleft, hright]

/-- **The printed estimate, in the `L2Operator` norm of `M_{Y×Y}(ℂ)`.** -/
theorem norm_adMatrix_sub_le (hY : 0 < Fintype.card Y) {A B : Matrix Y Y ℂ}
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) :
    ‖adMatrix Y A - adMatrix Y B‖ ≤ 2 * ‖A - B‖ := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x ↦ ?_
  have hcard : (0 : ℝ) < (Fintype.card Y : ℝ) := by exact_mod_cast hY
  have hkey : unvec Y (Matrix.toEuclideanCLM (n := Y × Y) (𝕜 := ℂ)
        (adMatrix Y A - adMatrix Y B) x)
      = A * unvec Y x * Aᴴ - B * unvec Y x * Bᴴ := by
    have h1 := unvec_adMatrix_mulVec Y A x
    have h2 := unvec_adMatrix_mulVec Y B x
    ext i j
    have hcoord : (Matrix.toEuclideanCLM (n := Y × Y) (𝕜 := ℂ)
          (adMatrix Y A - adMatrix Y B) x) (i, j)
        = (adMatrix Y A *ᵥ (x : Y × Y → ℂ)) (i, j)
          - (adMatrix Y B *ᵥ (x : Y × Y → ℂ)) (i, j) := by
      rw [map_sub]
      show ((Matrix.toEuclideanCLM (n := Y × Y) (𝕜 := ℂ) (adMatrix Y A)) x
          - (Matrix.toEuclideanCLM (n := Y × Y) (𝕜 := ℂ) (adMatrix Y B)) x)
          (i, j) = _
      rfl
    rw [unvec_apply, hcoord, Matrix.sub_apply, ← Matrix.of_apply
      (fun i j ↦ (adMatrix Y A *ᵥ (x : Y × Y → ℂ)) (i, j)) i j,
      ← Matrix.of_apply
      (fun i j ↦ (adMatrix Y B *ᵥ (x : Y × Y → ℂ)) (i, j)) i j, h1, h2]
  have hsq : ‖(Matrix.toEuclideanCLM (n := Y × Y) (𝕜 := ℂ)
        (adMatrix Y A - adMatrix Y B)) x‖ ^ 2
      ≤ (2 * ‖A - B‖ * ‖x‖) ^ 2 := by
    rw [norm_sq_eq_card_mul_hsNormSq Y hY, hkey, mul_pow, mul_pow,
      norm_sq_eq_card_mul_hsNormSq Y hY]
    have h := hsNormSq_conj_sub_conj_le Y hA hB (unvec Y x)
    nlinarith [h, hsNormSq_nonneg Y (unvec Y x), hcard, sq_nonneg (‖A - B‖)]
  have hnn : (0 : ℝ) ≤ 2 * ‖A - B‖ * ‖x‖ := by positivity
  nlinarith [hsq, norm_nonneg ((Matrix.toEuclideanCLM (n := Y × Y) (𝕜 := ℂ)
    (adMatrix Y A - adMatrix Y B)) x), hnn]

end

end HilbertSchmidtAdMatrix
end OneSidedMFRadical
end Manuscript
end GroupApproximation
