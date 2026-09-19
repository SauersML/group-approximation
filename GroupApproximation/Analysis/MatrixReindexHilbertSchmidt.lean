import GroupApproximation.Analysis.NaturalMatrixCoordinateEquiv
import GroupApproximation.Analysis.UltraproductRigidityRoute
import GroupApproximation.Sofic.HyperlinearScalar

/-!
# Reindexing invariance of the normalized Hilbert--Schmidt norm

`Analysis/NaturalMatrixCoordinateEquiv` reindexes a finite matrix algebra along
a bijection of its coordinates and shows the reindexing is a star-algebra
isomorphism (`matrixReindexStarAlgEquiv`) preserving the operator norm
(`norm_matrixReindexStarAlgEquiv`).  That is what the corona constructions
need, because they are stated in operator norm.

The Kazhdan transport theorem is not: its hypothesis and its conclusion are
both written in the *normalized Hilbert--Schmidt* norm, so moving it between
coordinate systems needs the invariance of `hsNormSq` instead.

**That invariance is not proved here.**  It is
`UltraproductRigidityRoute.hsNormSq_matrixReindex`, and everything below is a
thin specialization of it to the canonical reindexing of a model *family* onto
the literal natural bases `Fin (card (Y n))` — the change of basis that carries
a statement about arbitrary finite models onto the manuscript's own coordinates
`M_{d n}(ℂ)`, which is what `Sofic/GeneralModelKazhdanTransport.lean` consumes.

An earlier revision of this file proved the invariance again, from scratch,
under the heading that the corpus did not have it.  The corpus did have it, in
a green root-imported module, and the reason it was not found is worth keeping:
the search that would have turned it up was for what the lemma is *for* — the
transport rewiring and its ledger rows — not for the lemma itself.  The
duplicate proof has been deleted and `hsNormSq_naturalize` now instantiates the
canonical one.
-/

namespace GroupApproximation
namespace MatrixReindexHS

-- The adjoint postfix `ᴴ` and the `L²` operator norm on matrices are both
-- scoped: `Analysis/NaturalMatrixCoordinateEquiv`, whose statements this file
-- continues, opens the same two.
open Matrix
open scoped Matrix.Norms.L2Operator

/-! ## The canonical naturalizing reindexing -/

section Naturalize

variable (Y : ℕ → FiniteModel)

/-- The `n`-th matrix algebra, reindexed onto the literal natural basis of the
same cardinality. -/
noncomputable def naturalize (n : ℕ) :
    Matrix (Y n) (Y n) ℂ ≃⋆ₐ[ℂ]
      Matrix (naturalizedModel Y n) (naturalizedModel Y n) ℂ :=
  matrixReindexStarAlgEquiv (Fintype.equivFin (Y n))

@[simp] theorem naturalize_apply (n : ℕ) (A : Matrix (Y n) (Y n) ℂ)
    (i j : naturalizedModel Y n) :
    naturalize Y n A i j =
      A ((Fintype.equivFin (Y n)).symm i) ((Fintype.equivFin (Y n)).symm j) :=
  rfl

/-- Reindexing preserves the operator norm. -/
theorem norm_naturalize (n : ℕ) (A : Matrix (Y n) (Y n) ℂ) :
    ‖naturalize Y n A‖ = ‖A‖ :=
  norm_matrixReindexStarAlgEquiv (Fintype.equivFin (Y n)) A

/-- **Reindexing preserves the normalized Hilbert--Schmidt mass**, at the
canonical equivalence.  The invariance itself is
`UltraproductRigidityRoute.hsNormSq_matrixReindex`; this only instantiates it at
`Fintype.equivFin`, which is the equivalence `naturalize` is built from. -/
theorem hsNormSq_naturalize (n : ℕ) (A : Matrix (Y n) (Y n) ℂ) :
    hsNormSq (naturalizedModel Y n) (naturalize Y n A) = hsNormSq (Y n) A :=
  UltraproductRigidityRoute.hsNormSq_matrixReindex (Fintype.equivFin (Y n)) A

/-- Reindexing commutes with the adjoint. -/
theorem naturalize_conjTranspose (n : ℕ) (A : Matrix (Y n) (Y n) ℂ) :
    naturalize Y n Aᴴ = (naturalize Y n A)ᴴ := by
  have h := map_star (naturalize Y n) A
  rwa [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose] at h

/-- The unitary-group reindexing agrees with the algebra reindexing on the
underlying matrices.  `opLength_unitaryReindexEquiv` already relies on this
identification definitionally; naming it lets `rw` use it. -/
@[simp] theorem coe_unitaryReindexEquiv (n : ℕ) (u : Matrix.unitaryGroup (Y n) ℂ) :
    ((unitaryReindexEquiv (Fintype.equivFin (Y n)) u :
        Matrix.unitaryGroup (naturalizedModel Y n) ℂ) :
        Matrix (naturalizedModel Y n) (naturalizedModel Y n) ℂ)
      = naturalize Y n (u : Matrix (Y n) (Y n) ℂ) :=
  rfl

end Naturalize

end MatrixReindexHS
end GroupApproximation
