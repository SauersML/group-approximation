import GroupApproximation.Analysis.HilbertSchmidtApproximateUnit
import GroupApproximation.Analysis.PreliminaryInequalitiesPrinted

/-!
# The absolute value of a finite matrix

`|x| = (x⋆x)^{1/2}`, for `x` a complex matrix over one of the repository's
`FiniteModel` index types, together with the four facts a polar decomposition
needs.

Mathlib in this checkout has no `Matrix.PosSemidef.sqrt` and no matrix polar
decomposition, so the square root is taken by hand.  It is not taken from
scratch either: `ExactInvolutionLifts.eigenCalc` is already the diagonal
functional calculus in the eigenbasis of a Hermitian matrix --- `eigenCalc H hH
d` is `U * diagonal d * U⋆` for `U` the eigenvector unitary of `H` --- and it
already carries `eigenCalc_congr`, `eigenCalc_sub`, `eigenCalc_one`,
`eq_eigenCalc_eigenvalues` (the spectral theorem) and, from
`HilbertSchmidtApproximateUnit`, `eigenCalc_mul`.  So

`abs Y x = eigenCalc (x⋆x) _ (fun i ↦ √λᵢ)`,

with `λ` the eigenvalue list of `x⋆x`, and every clause below is an entrywise
statement about that list.

## What is proved

* `abs_isHermitian`, `abs_posSemidef` --- `|x|` is Hermitian and positive
  semidefinite.  Positivity is not proved from the definition of `PosSemidef`
  but by exhibiting `|x|` as `B⋆B` for `B` the calculus at `λᵢ^{1/4}`, which is
  the same trick one would use for any nonnegative spectral function.
* `abs_mul_abs : |x| * |x| = x⋆x` --- the defining property, from
  multiplicativity of the calculus and `√λ · √λ = λ`, which needs
  `0 ≤ λᵢ` (`eigenvalues_conjTranspose_self_nonneg`).
* `hsNorm_one_sub_abs_le : ‖1 - |x|‖₂ ≤ ‖x⋆x - 1‖₂` --- the estimate that lets
  an approximate isometry be replaced by its polar factor at bounded
  Hilbert--Schmidt cost.  Both sides are diagonalized by the same unitary, so
  the normalized Hilbert--Schmidt norm (unitarily invariant by
  `PrelimNotation.hsNorm_unitary_mul_mul`) reduces to the diagonal, and the
  whole content is the scalar inequality `(1 - √t)² ≤ (t - 1)²` for `t ≥ 0`.
  That one is an identity plus two signs: `(t-1)² - (1-√t)² = (1-√t)²(t + 2√t)`.
* `norm_abs_mulVec : ∑ᵢ ‖(|x| v)ᵢ‖² = ∑ᵢ ‖(x v)ᵢ‖²` --- `|x|` and `x` move
  every vector the same distance, which is what makes `x = u|x|` solvable for
  an isometry `u` on the range of `|x|`.  It is `sum_normSq_mulVec_congr`, which
  says the squared mass of `M v` depends on `M` only through `M⋆M`, applied to
  `|x|⋆|x| = |x| * |x| = x⋆x`.

## The mass identity, and why it is proved by a column

`sum_normSq_mulVec_congr` could be proved by expanding both sides into a double
sum over the entries.  It is shorter to notice that the squared mass of `M v` is
one *diagonal entry of a Gram matrix*: filling a square matrix `V` with copies
of the column `v` makes every column of `M * V` equal to `M v`, so the mass is
`((M V)⋆(M V))ᵢᵢ = (V⋆(M⋆M)V)ᵢᵢ`, visibly a function of `M⋆M` alone.  The
column-mass identity itself is three lines and is repeated here as a private
lemma: the repository's copy, `column_mass_eq`, sits in
`Manuscript/MFRecognition/PrintedTarskiCertificateSyntax.lean`, and an
`Analysis` module must not import a `Manuscript` one.

The empty model is handled separately throughout --- there is no column to take
a mass on, and every sum is empty.

## What is not here

No polar decomposition.  Nothing below constructs the unitary `u` with
`x = u|x|`: that needs the isometry `range |x| → range x` this file's
`norm_abs_mulVec` supplies, extended to the whole space, and it belongs with the
consumer.  Nor is `|x|` related to the operator norm, or shown unique among
positive square roots.
-/

namespace GroupApproximation

namespace MatrixAbs

open Matrix ExactInvolutionLifts HilbertSchmidtApproximateUnit
open scoped ComplexOrder

noncomputable section

/-! ## Two additions to the eigenbasis calculus -/

section Calculus

variable {Z : Type*} [Fintype Z] [DecidableEq Z]

/-- The adjoint of a diagonal functional calculus is the calculus at the
conjugated diagonal.  The eigenvector unitary and its adjoint change places,
which is exactly what the conjugation `U * · * U⋆` is set up to survive. -/
theorem conjTranspose_eigenCalc (H : Matrix Z Z ℂ) (hH : H.IsHermitian)
    (d : Z → ℂ) : (eigenCalc H hH d)ᴴ = eigenCalc H hH (star d) := by
  rw [eigenCalc, eigenCalc, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.mul_assoc]

/-- A real diagonal gives a Hermitian matrix.  This is the only way any matrix
below is shown Hermitian. -/
theorem isHermitian_eigenCalc_ofReal (H : Matrix Z Z ℂ) (hH : H.IsHermitian)
    (r : Z → ℝ) : (eigenCalc H hH fun i ↦ (r i : ℂ)).IsHermitian :=
  (conjTranspose_eigenCalc H hH _).trans
    (eigenCalc_congr H hH fun i ↦ by simp)

end Calculus

/-! ## The absolute value -/

variable (Y : FiniteModel)

/-- **The absolute value of a matrix**, `|x| = (x⋆x)^{1/2}`: the diagonal
functional calculus of `x⋆x` at the pointwise square root of its eigenvalue
list.

The eigenvalues of `x⋆x` are nonnegative
(`eigenvalues_conjTranspose_self_nonneg`), so no square root is taken of a
negative number and `Real.sqrt`'s junk value is never reached. -/
def abs (x : Matrix Y Y ℂ) : Matrix Y Y ℂ :=
  eigenCalc (xᴴ * x) (isHermitian_conjTranspose_self Y x) fun i ↦
    (Real.sqrt ((isHermitian_conjTranspose_self Y x).eigenvalues i) : ℂ)

/-- `|x|` is Hermitian: its diagonal in the eigenbasis of `x⋆x` is real. -/
theorem abs_isHermitian (x : Matrix Y Y ℂ) : (abs Y x).IsHermitian :=
  isHermitian_eigenCalc_ofReal (xᴴ * x) (isHermitian_conjTranspose_self Y x)
    fun i ↦ Real.sqrt ((isHermitian_conjTranspose_self Y x).eigenvalues i)

/-- **The defining property**: `|x|² = x⋆x`.

Multiplicativity of the calculus turns the square into the pointwise square of
the diagonal, and `√λ · √λ = λ` holds because the eigenvalues of `x⋆x` are
nonnegative.  The last step is the spectral theorem, in the form
`eq_eigenCalc_eigenvalues`. -/
theorem abs_mul_abs (x : Matrix Y Y ℂ) : abs Y x * abs Y x = xᴴ * x := by
  have hH : (xᴴ * x).IsHermitian := isHermitian_conjTranspose_self Y x
  calc abs Y x * abs Y x
      = eigenCalc (xᴴ * x) hH (fun i ↦ (Real.sqrt (hH.eigenvalues i) : ℂ) *
          (Real.sqrt (hH.eigenvalues i) : ℂ)) := by
        rw [abs, eigenCalc_mul]
    _ = eigenCalc (xᴴ * x) hH (fun i ↦ ((hH.eigenvalues i : ℝ) : ℂ)) := by
        refine eigenCalc_congr (xᴴ * x) hH fun i ↦ ?_
        rw [← Complex.ofReal_mul,
          Real.mul_self_sqrt (eigenvalues_conjTranspose_self_nonneg Y x i)]
    _ = xᴴ * x := (eq_eigenCalc_eigenvalues (xᴴ * x) hH).symm

/-- The Gram matrix of `|x|` is the Gram matrix of `x`.  This is `abs_mul_abs`
with one factor turned round by `abs_isHermitian`, and it is the form the mass
identity consumes. -/
theorem abs_conjTranspose_mul_abs (x : Matrix Y Y ℂ) :
    (abs Y x)ᴴ * abs Y x = xᴴ * x := by
  rw [show (abs Y x)ᴴ = abs Y x from abs_isHermitian Y x, abs_mul_abs]

/-- `|x|` is positive semidefinite.

Rather than unfold `Matrix.PosSemidef`, the proof exhibits `|x|` as `B⋆B` for
`B` the calculus at the *fourth* root of the eigenvalue list, and quotes
`Matrix.posSemidef_conjTranspose_mul_self`.  `B` is Hermitian for the same
reason `|x|` is, so `B⋆B = B²`, and the fourth roots square to the square
roots. -/
theorem abs_posSemidef (x : Matrix Y Y ℂ) : (abs Y x).PosSemidef := by
  have hH : (xᴴ * x).IsHermitian := isHermitian_conjTranspose_self Y x
  set B : Matrix Y Y ℂ := eigenCalc (xᴴ * x) hH
    (fun i ↦ (Real.sqrt (Real.sqrt (hH.eigenvalues i)) : ℂ)) with hB
  have hBherm : Bᴴ = B :=
    isHermitian_eigenCalc_ofReal (xᴴ * x) hH
      fun i ↦ Real.sqrt (Real.sqrt (hH.eigenvalues i))
  have hBB : Bᴴ * B = abs Y x := by
    rw [hBherm, hB, eigenCalc_mul, abs]
    refine eigenCalc_congr (xᴴ * x) hH fun i ↦ ?_
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Real.sqrt_nonneg _)]
  rw [← hBB]
  exact Matrix.posSemidef_conjTranspose_mul_self B

/-! ## The Hilbert--Schmidt estimate -/

/-- The normalized Hilbert--Schmidt norm of a diagonal matrix sees only the
diagonal: every off-diagonal entry contributes nothing. -/
theorem hsNormSq_diagonal (d : Y → ℂ) :
    hsNormSq Y (Matrix.diagonal d)
      = (∑ i : Y, Complex.normSq (d i)) / Fintype.card Y := by
  have hnum : ∑ i : Y, ∑ j : Y, Complex.normSq (Matrix.diagonal d i j)
      = ∑ i : Y, Complex.normSq (d i) := by
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.sum_eq_single i]
    · rw [Matrix.diagonal_apply_eq]
    · intro j _ hj
      rw [Matrix.diagonal_apply_ne' d hj, Complex.normSq_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [hsNormSq, hnum]

/-- Diagonal matrices are compared entrywise in the normalized
Hilbert--Schmidt norm. -/
theorem hsNorm_diagonal_le (d₁ d₂ : Y → ℂ)
    (h : ∀ i, Complex.normSq (d₁ i) ≤ Complex.normSq (d₂ i)) :
    hsNorm Y (Matrix.diagonal d₁) ≤ hsNorm Y (Matrix.diagonal d₂) := by
  have hsum : ∑ i : Y, Complex.normSq (d₁ i) ≤ ∑ i : Y, Complex.normSq (d₂ i) :=
    Finset.sum_le_sum fun i _ ↦ h i
  have hcard : (0 : ℝ) ≤ (Fintype.card Y : ℝ) := Nat.cast_nonneg _
  unfold hsNorm
  refine Real.sqrt_le_sqrt ?_
  rw [hsNormSq_diagonal, hsNormSq_diagonal, div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hsum (inv_nonneg.mpr hcard)

/-- The eigenbasis calculus is a unitary conjugation, so it does not change the
normalized Hilbert--Schmidt norm of its diagonal.  This is the third printed
inequality of `PrelimNotation`, applied to `U` and `U⋆`. -/
theorem hsNorm_eigenCalc (H : Matrix Y Y ℂ) (hH : H.IsHermitian) (d : Y → ℂ) :
    hsNorm Y (eigenCalc H hH d) = hsNorm Y (Matrix.diagonal d) := by
  have hstar : (hH.eigenvectorUnitary : Matrix Y Y ℂ)ᴴ ∈
      Matrix.unitaryGroup Y ℂ := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.star_mem hH.eigenvectorUnitary.2
  rw [eigenCalc]
  exact PrelimNotation.hsNorm_unitary_mul_mul Y hH.eigenvectorUnitary.2 hstar
    (Matrix.diagonal d)

/-- **The scalar content of the estimate**: `(1 - √t)² ≤ (t - 1)²` for
`t ≥ 0`, in the form in which the diagonal entries meet it.

`|1 - √t| · (1 + √t) = |1 - t|` and `1 + √t ≥ 1`, so shrinking by the square
root can only move a number closer to `1`.  The Lean proof is the polynomial
identity `(t-1)² - (1-√t)² = (1-√t)²·t + 2(1-√t)²·√t` with `t = √t · √t`. -/
theorem one_sub_mul_self_le (s t : ℝ) (hs : 0 ≤ s) (hst : s * s = t) :
    (1 - s) * (1 - s) ≤ (t - 1) * (t - 1) := by
  subst hst
  have expand : (s * s - 1) * (s * s - 1) - (1 - s) * (1 - s)
      = (1 - s) * (1 - s) * (s * s) + 2 * ((1 - s) * (1 - s) * s) := by ring
  have h1 : 0 ≤ (1 - s) * (1 - s) * (s * s) :=
    mul_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
  have h2 : 0 ≤ (1 - s) * (1 - s) * s := mul_nonneg (mul_self_nonneg _) hs
  linarith

/-- **The estimate.**  `‖1 - |x|‖₂ ≤ ‖x⋆x - 1‖₂`.

Both matrices are the eigenbasis calculus of `x⋆x` at a real diagonal --- at
`1 - √λᵢ` and at `λᵢ - 1` --- so the unitary invariance of the normalized
Hilbert--Schmidt norm reduces the claim to the diagonal, where it is
`one_sub_mul_self_le` entry by entry.

Read the inequality as: replacing an approximate isometry by its polar factor
costs no more, in the normalized Hilbert--Schmidt norm, than the failure of
`x⋆x` to be the unit. -/
theorem hsNorm_one_sub_abs_le (x : Matrix Y Y ℂ) :
    hsNorm Y (1 - abs Y x) ≤ hsNorm Y (xᴴ * x - 1) := by
  have hH : (xᴴ * x).IsHermitian := isHermitian_conjTranspose_self Y x
  have hleft : (1 : Matrix Y Y ℂ) - abs Y x
      = eigenCalc (xᴴ * x) hH
        (fun i ↦ ((1 - Real.sqrt (hH.eigenvalues i) : ℝ) : ℂ)) := by
    rw [abs, ← eigenCalc_one (xᴴ * x) hH, eigenCalc_sub]
    refine eigenCalc_congr (xᴴ * x) hH fun i ↦ ?_
    rw [Complex.ofReal_sub, Complex.ofReal_one]
  have hright : xᴴ * x - 1
      = eigenCalc (xᴴ * x) hH
        (fun i ↦ ((hH.eigenvalues i - 1 : ℝ) : ℂ)) := by
    conv_lhs => rw [eq_eigenCalc_eigenvalues (xᴴ * x) hH]
    rw [← eigenCalc_one (xᴴ * x) hH, eigenCalc_sub]
    refine eigenCalc_congr (xᴴ * x) hH fun i ↦ ?_
    rw [Complex.ofReal_sub, Complex.ofReal_one]
  rw [hleft, hright, hsNorm_eigenCalc, hsNorm_eigenCalc]
  refine hsNorm_diagonal_le Y _ _ fun i ↦ ?_
  rw [Complex.normSq_ofReal, Complex.normSq_ofReal]
  exact one_sub_mul_self_le _ _ (Real.sqrt_nonneg _)
    (Real.mul_self_sqrt (eigenvalues_conjTranspose_self_nonneg Y x i))

/-! ## The mass identity -/

/-- The squared modulus as a complex product.  A private copy of
`MFRecognition.PrintedTarskiCertificateSyntax.ofReal_normSq`, which an
`Analysis` module cannot import. -/
private theorem ofReal_normSq_eq (z : ℂ) :
    ((Complex.normSq z : ℝ) : ℂ) = star z * z := by
  rw [Complex.star_def, mul_comm, Complex.mul_conj]

/-- The diagonal entry of `A⋆A` is the squared mass of the `i`-th column.  A
private copy of `MFRecognition.PrintedTarskiCertificateSyntax.column_mass_eq`,
for the same reason. -/
private theorem ofReal_column_mass (A : Matrix Y Y ℂ) (i : Y) :
    ((∑ y : Y, Complex.normSq (A y i) : ℝ) : ℂ) = (Aᴴ * A) i i := by
  rw [Complex.ofReal_sum, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [Matrix.conjTranspose_apply, ofReal_normSq_eq]

/-- **The squared mass of `M v` depends on `M` only through `M⋆M`.**

Filling a square matrix with copies of the column `v` makes every column of
`M * V` equal to `M *ᵥ v`, so the mass in question is the diagonal entry
`((M V)⋆(M V))ᵢᵢ = (V⋆(M⋆M)V)ᵢᵢ`, in which `M` occurs only inside `M⋆M`.

On an empty model there is no column to read, and both sides are empty
sums. -/
theorem sum_normSq_mulVec_congr {A B : Matrix Y Y ℂ} (h : Aᴴ * A = Bᴴ * B)
    (v : Y → ℂ) :
    ∑ i : Y, Complex.normSq ((A *ᵥ v) i)
      = ∑ i : Y, Complex.normSq ((B *ᵥ v) i) := by
  rcases Nat.eq_zero_or_pos (Fintype.card Y) with h0 | hpos
  · haveI : IsEmpty Y := Fintype.card_eq_zero_iff.mp h0
    simp
  · obtain ⟨i₀⟩ := Fintype.card_pos_iff.mp hpos
    have key : ∀ M : Matrix Y Y ℂ,
        ((∑ y : Y, Complex.normSq ((M *ᵥ v) y) : ℝ) : ℂ)
          = ((Matrix.of fun (j _ : Y) ↦ v j)ᴴ * (Mᴴ * M) *
              (Matrix.of fun (j _ : Y) ↦ v j)) i₀ i₀ := by
      intro M
      have hsum : ∑ y : Y, Complex.normSq ((M *ᵥ v) y)
          = ∑ y : Y, Complex.normSq
              ((M * Matrix.of fun (j _ : Y) ↦ v j) y i₀) :=
        Finset.sum_congr rfl fun y _ ↦ by
          simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
      have hgram : (M * Matrix.of fun (j _ : Y) ↦ v j)ᴴ *
            (M * Matrix.of fun (j _ : Y) ↦ v j)
          = (Matrix.of fun (j _ : Y) ↦ v j)ᴴ * (Mᴴ * M) *
              (Matrix.of fun (j _ : Y) ↦ v j) := by
        rw [Matrix.conjTranspose_mul]
        noncomm_ring
      rw [hsum, ofReal_column_mass, hgram]
    have hcast : ((∑ y : Y, Complex.normSq ((A *ᵥ v) y) : ℝ) : ℂ)
        = ((∑ y : Y, Complex.normSq ((B *ᵥ v) y) : ℝ) : ℂ) := by
      rw [key A, key B, h]
    exact_mod_cast hcast

/-- **`|x|` moves every vector exactly as far as `x` does.**

The squared Euclidean mass of `|x| v` equals that of `x v`, because both are
read off the same Gram matrix by `sum_normSq_mulVec_congr` and
`abs_conjTranspose_mul_abs` says the Gram matrices agree.

This is the clause a polar decomposition is built on: `x v ↦ |x| v` is a
well-defined linear isometry from the range of `x` onto the range of `|x|`, and
an isometry between subspaces of a finite-dimensional space extends to a
unitary. -/
theorem norm_abs_mulVec (x : Matrix Y Y ℂ) (v : Y → ℂ) :
    ∑ i : Y, Complex.normSq ((abs Y x *ᵥ v) i)
      = ∑ i : Y, Complex.normSq ((x *ᵥ v) i) :=
  sum_normSq_mulVec_congr Y (abs_conjTranspose_mul_abs Y x) v

end

end MatrixAbs

end GroupApproximation
