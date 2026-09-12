import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# The Frobenius mass of a matrix is at most its rank times its operator norm squared

`thm:projection-collapse` builds a rank-normalized Hilbertization of the ideal
`q 𝒬 q`, and the estimate that makes it well defined is printed as

> `‖Z‖_F² ≤ rank(Z) ‖Z‖²`

used together with "elements of the ideal have coordinate representatives of
rank at most `r·k_n`" to bound the Frobenius mass of a representative by
`r·k_n·‖Z‖²`, so that dividing by `k_n` leaves something bounded.  Proof-ledger
row `CO.20` records the whole step as missing; this file supplies the
inequality, which is its quantitative core and the only part of it that is a
statement about a single matrix rather than about the ultraproduct.

**Why rank and not dimension.**  The trivial bound is
`‖Z‖_F² ≤ card Y · ‖Z‖²`, one term per coordinate, and it is useless here: the
whole point of the rank normalization is that `k_n` may be `o(d_n)`, so a bound
by the ambient dimension says nothing about the corner.  Replacing `card Y` by
`rank Z` is exactly what makes the corner's own normalization survive.

**The proof.**  Write `A = Zᴴ Z`, which is Hermitian and positive
semidefinite.  Three facts about `A` do all the work, and Mathlib has each:

* `Matrix.trace_eq_sum_eigenvalues` — the trace is the sum of the eigenvalues,
  and `‖Z‖_F²` is the real part of that trace;
* `Matrix.IsHermitian.rank_eq_card_non_zero_eigs` — the rank counts the nonzero
  eigenvalues, so the sum has at most `rank A` nonzero terms;
* `Matrix.l2_opNorm_conjTranspose_mul_self` — `‖Zᴴ Z‖ = ‖Z‖²`, which bounds
  each eigenvalue, each being the norm of `A` applied to a unit eigenvector.

Then `rank A = rank Z` by `Matrix.rank_conjTranspose_mul_self`.  Nothing here is
special to the corona: it is a statement about one finite matrix, which is why
it lives in `Analysis/` and takes no compression datum.
-/

namespace GroupApproximation

open Matrix
open scoped Matrix.Norms.L2Operator
-- `Matrix.rank_conjTranspose_mul_self` asks for `StarOrderedRing ℂ`, and the
-- instance that supplies it, `RCLike.toStarOrderedRing`, is `scoped[ComplexOrder]`.
-- Without this line the rank step fails with a bare `⊢ StarOrderedRing ℂ`, which
-- reads like a missing import rather than a missing scope.
open scoped ComplexOrder

namespace RankFrobeniusBound

variable {Y : Type*} [Fintype Y]

/-! ## The trace of `Zᴴ Z` is the Frobenius mass -/

/-- The unnormalized squared Frobenius mass of `Z` is the trace of `Zᴴ Z`, read
as a real number.  The double sum is in the order `∑ i ∑ j ‖Z i j‖²`, which is
the order the manuscript writes it in; the trace produces the other order, so
this is where the two are exchanged. -/
theorem sum_normSq_eq_re_trace (Z : Matrix Y Y ℂ) :
    ∑ i : Y, ∑ j : Y, Complex.normSq (Z i j) = ((Zᴴ * Z).trace).re := by
  classical
  have hentry : ∀ i : Y, (Zᴴ * Z) i i = ∑ j : Y, (Complex.normSq (Z j i) : ℂ) := by
    intro i
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Matrix.conjTranspose_apply, RCLike.star_def]
    exact (Complex.normSq_eq_conj_mul_self (z := Z j i)).symm
  have htr : (Zᴴ * Z).trace = ∑ i : Y, ∑ j : Y, (Complex.normSq (Z j i) : ℂ) := by
    rw [Matrix.trace]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [Matrix.diag_apply, hentry i]
  rw [htr, Complex.re_sum]
  refine (Finset.sum_comm).trans ?_
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Complex.re_sum]
  exact Finset.sum_congr rfl fun j _ ↦ (Complex.ofReal_re _)

/-! ## Every eigenvalue of `Zᴴ Z` is at most `‖Z‖²` -/

/-- An eigenvalue of a Hermitian matrix is bounded by its operator norm: the
eigenvector is a unit vector, so the eigenvalue is the norm of the matrix
applied to it. -/
theorem abs_eigenvalues_le_l2_opNorm [DecidableEq Y] {A : Matrix Y Y ℂ}
    (hA : A.IsHermitian)
    (i : Y) : |hA.eigenvalues i| ≤ ‖A‖ := by
  classical
  have hunit : ‖hA.eigenvectorBasis i‖ = 1 := hA.eigenvectorBasis.orthonormal.1 i
  have hbound := A.l2_opNorm_mulVec (hA.eigenvectorBasis i)
  rw [hA.mulVec_eigenvectorBasis i] at hbound
  have hsmul : ((EuclideanSpace.equiv Y ℂ).symm
      ((hA.eigenvalues i) • (hA.eigenvectorBasis i : Y → ℂ)))
      = (hA.eigenvalues i) • (hA.eigenvectorBasis i) := by
    simp [EuclideanSpace.equiv]
  rw [hsmul, norm_smul, Real.norm_eq_abs, hunit, mul_one] at hbound
  simpa [hunit] using hbound

/-! ## The bound -/

/-- **`‖Z‖_F² ≤ rank(Z) · ‖Z‖²`.**  The printed estimate of
`thm:projection-collapse`'s rank-normalized Hilbertization, for a single square
matrix and with no hypothesis on `Z`. -/
theorem sum_normSq_le_rank_mul_opNorm_sq [DecidableEq Y] (Z : Matrix Y Y ℂ) :
    ∑ i : Y, ∑ j : Y, Complex.normSq (Z i j) ≤ (Z.rank : ℝ) * (‖Z‖ * ‖Z‖) := by
  classical
  have hherm : (Zᴴ * Z).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self Z
  have hpsd : (Zᴴ * Z).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self Z
  have hnorm : ‖Zᴴ * Z‖ = ‖Z‖ * ‖Z‖ := Matrix.l2_opNorm_conjTranspose_mul_self Z
  have hnn : ∀ i : Y, 0 ≤ hherm.eigenvalues i := fun i ↦ hpsd.eigenvalues_nonneg i
  have hle : ∀ i : Y, hherm.eigenvalues i ≤ ‖Z‖ * ‖Z‖ := by
    intro i
    have := abs_eigenvalues_le_l2_opNorm hherm i
    rw [hnorm] at this
    exact (le_abs_self _).trans this
  -- the trace is the sum of the eigenvalues, and only the nonzero ones count
  have htrace : ∑ i : Y, ∑ j : Y, Complex.normSq (Z i j)
      = ∑ i : Y, hherm.eigenvalues i := by
    rw [sum_normSq_eq_re_trace Z, hherm.trace_eq_sum_eigenvalues, Complex.re_sum]
    exact Finset.sum_congr rfl fun i _ ↦ Complex.ofReal_re _
  set S : Finset Y := Finset.univ.filter fun i ↦ hherm.eigenvalues i ≠ 0 with hS
  have hsupport : ∑ i : Y, hherm.eigenvalues i = ∑ i ∈ S, hherm.eigenvalues i := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro i _ hnot
    have : ¬ (hherm.eigenvalues i ≠ 0) := by
      simpa [hS, Finset.mem_filter] using hnot
    exact not_not.mp this
  have hcard : S.card = Z.rank := by
    have hrk : (Zᴴ * Z).rank = Fintype.card {i // hherm.eigenvalues i ≠ 0} :=
      hherm.rank_eq_card_non_zero_eigs
    rw [Matrix.rank_conjTranspose_mul_self] at hrk
    rw [hS, ← Fintype.card_subtype]
    exact hrk.symm
  calc ∑ i : Y, ∑ j : Y, Complex.normSq (Z i j)
      = ∑ i ∈ S, hherm.eigenvalues i := htrace.trans hsupport
    _ ≤ S.card • (‖Z‖ * ‖Z‖) :=
        Finset.sum_le_card_nsmul S _ _ fun i _ ↦ hle i
    _ = (Z.rank : ℝ) * (‖Z‖ * ‖Z‖) := by rw [hcard, nsmul_eq_mul]

end RankFrobeniusBound

end GroupApproximation
