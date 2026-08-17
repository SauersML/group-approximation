import GroupApproximation.Analysis.NaturalMatrixCoordinateEquiv
import GroupApproximation.Sofic.HyperlinearScalar

/-!
# Reindexing invariance of the normalized Hilbert--Schmidt norm

`Analysis/NaturalMatrixCoordinateEquiv` reindexes a finite matrix algebra along
a bijection of its coordinates and shows the reindexing is a star-algebra
isomorphism (`matrixReindexStarAlgEquiv`) preserving the operator norm
(`norm_matrixReindexStarAlgEquiv`).  That is what the corona constructions
need, because they are stated in operator norm.

The Kazhdan transport theorem is not.  Its hypothesis and its conclusion are
both written in the *normalized Hilbert--Schmidt* norm, and the corresponding
invariance was missing: nothing in the corpus said that `hsNormSq` is a
coordinate invariant.  It is, for the obvious reason — reindexing permutes the
entries, and the cardinality the normalization divides by is unchanged — and
this file says so.

`hsNormSq_congr_equiv` is the general form: any bijection of finite models
carrying one matrix to another entrywise preserves the normalized mass.  The
rest specializes it to the canonical reindexing of a model family onto the
literal natural bases `Fin (card (Y n))`, which is the change of basis that
carries a statement about arbitrary finite models onto the manuscript's own
coordinates `M_{d n}(ℂ)`.

Everything here is bookkeeping; the point is that it was not available, and
`Sofic/GeneralModelKazhdanTransport.lean` cannot move the literal Section-3
theorem off natural coordinates without it.
-/

namespace GroupApproximation
namespace MatrixReindexHS

-- The adjoint postfix `ᴴ` and the `L²` operator norm on matrices are both
-- scoped: `Analysis/NaturalMatrixCoordinateEquiv`, whose statements this file
-- continues, opens the same two.
open Matrix
open scoped Matrix.Norms.L2Operator

/-! ## The invariance -/

/-- **The normalized Hilbert--Schmidt norm is a coordinate invariant.**  If a
bijection of finite models carries `A` to `B` entrywise, the two have the same
normalized Hilbert--Schmidt mass. -/
theorem hsNormSq_congr_equiv (Y Z : FiniteModel) (e : Y ≃ Z)
    (A : Matrix Y Y ℂ) (B : Matrix Z Z ℂ)
    (hB : ∀ i j : Y, B (e i) (e j) = A i j) :
    hsNormSq Z B = hsNormSq Y A := by
  have hcard : Fintype.card Z = Fintype.card Y := (Fintype.card_congr e).symm
  have hsum : (∑ i : Z, ∑ j : Z, Complex.normSq (B i j))
      = ∑ i : Y, ∑ j : Y, Complex.normSq (A i j) := by
    refine (Fintype.sum_equiv e
      (fun i : Y ↦ ∑ j : Y, Complex.normSq (A i j))
      (fun i : Z ↦ ∑ j : Z, Complex.normSq (B i j)) ?_).symm
    intro i
    refine Fintype.sum_equiv e
      (fun j : Y ↦ Complex.normSq (A i j))
      (fun j : Z ↦ Complex.normSq (B (e i) j)) ?_
    intro j
    rw [hB]
  unfold hsNormSq
  rw [hsum, hcard]

/-! ## The canonical naturalizing reindexing -/

section Naturalize

variable (Y : ℕ → FiniteModel)

/-- The `n`-th matrix algebra, reindexed onto the literal natural basis of the
same cardinality. -/
noncomputable def naturalize (n : ℕ) :
    Matrix (Y n) (Y n) ℂ ≃⋆ₐ[ℂ]
      Matrix (naturalizedModel Y n) (naturalizedModel Y n) ℂ :=
  matrixReindexStarAlgEquiv (Fintype.equivFin (Y n))

theorem naturalize_apply (n : ℕ) (A : Matrix (Y n) (Y n) ℂ)
    (i j : naturalizedModel Y n) :
    naturalize Y n A i j =
      A ((Fintype.equivFin (Y n)).symm i) ((Fintype.equivFin (Y n)).symm j) :=
  rfl

/-- Reindexing preserves the operator norm. -/
theorem norm_naturalize (n : ℕ) (A : Matrix (Y n) (Y n) ℂ) :
    ‖naturalize Y n A‖ = ‖A‖ :=
  norm_matrixReindexStarAlgEquiv (Fintype.equivFin (Y n)) A

/-- **Reindexing preserves the normalized Hilbert--Schmidt mass.**  This is the
statement the transport theorem's change of basis turns on. -/
theorem hsNormSq_naturalize (n : ℕ) (A : Matrix (Y n) (Y n) ℂ) :
    hsNormSq (naturalizedModel Y n) (naturalize Y n A) = hsNormSq (Y n) A := by
  refine hsNormSq_congr_equiv (Y n) (naturalizedModel Y n)
    (Fintype.equivFin (Y n)) A (naturalize Y n A) ?_
  intro i j
  rw [naturalize_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- Reindexing commutes with the adjoint. -/
theorem naturalize_conjTranspose (n : ℕ) (A : Matrix (Y n) (Y n) ℂ) :
    naturalize Y n Aᴴ = (naturalize Y n A)ᴴ := by
  have h := map_star (naturalize Y n) A
  rwa [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose] at h

/-- The unitary-group reindexing agrees with the algebra reindexing on the
underlying matrices.  `opLength_unitaryReindexEquiv` already relies on this
identification definitionally; naming it lets `rw` use it. -/
theorem coe_unitaryReindexEquiv (n : ℕ) (u : Matrix.unitaryGroup (Y n) ℂ) :
    ((unitaryReindexEquiv (Fintype.equivFin (Y n)) u :
        Matrix.unitaryGroup (naturalizedModel Y n) ℂ) :
        Matrix (naturalizedModel Y n) (naturalizedModel Y n) ℂ)
      = naturalize Y n (u : Matrix (Y n) (Y n) ℂ) :=
  rfl

end Naturalize

end MatrixReindexHS
end GroupApproximation
