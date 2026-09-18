import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Trace
import GroupApproximation.Analysis.NaturalMatrixCoordinateEquiv
import GroupApproximation.Manuscript.NonMF.TWWLanes.AFQD.Presentation
import GroupApproximation.Meta.AxiomGuard

/-!
# Amplified block representations of a multimatrix algebra (lane nm-tww-03, part 3)

Let `B = ⊕_{i<r} M_{k_i}(ℂ)` and fix multiplicities `m : Fin r → ℕ`. This module builds the
unital ⋆-homomorphism `π_m(b) = ⊕_i (b i ⊗ 1_{m i})` into `M_N(ℂ)`, where
`N = ∑ k i · m i`, and computes its trace. Only algebra happens here, so no norms appear.

* `ampHom m`: `b ↦ blockDiagonal' (i ↦ blockDiagonal (_ : Fin (m i) ↦ b i))`, indexed by
  `Σ i, Fin (k i) × Fin (m i)`.
* `ampRep m`: the same map reindexed onto `Fin (card _)`, using
  `matrixReindexStarAlgEquiv (Fintype.equivFin _)`.
* `trace_ampRep`: `trace (ampRep m b) = ∑ i, m i · trace (b i)`.
* `card_ampIndex`: the matrix size is `∑ i, k i · m i`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace MultimatrixTrace

noncomputable section

variable {r : ℕ} {k : Fin r → ℕ}

/-- The index type of the amplified representation: `Σ i, Fin (k i) × Fin (m i)`. -/
abbrev AmpIndex (k m : Fin r → ℕ) : Type := Σ i : Fin r, Fin (k i) × Fin (m i)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.MultimatrixTrace.AmpIndex

/-- The `i`-th amplified block `b i ⊗ 1_{m i}`. -/
def ampBlocks (m : Fin r → ℕ) (b : AFQD.Multimatrix r k) (i : Fin r) :
    Matrix (Fin (k i) × Fin (m i)) (Fin (k i) × Fin (m i)) ℂ :=
  Matrix.blockDiagonal fun _ : Fin (m i) ↦ b i

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.MultimatrixTrace.ampBlocks

theorem ampBlocks_add (m : Fin r → ℕ) (b c : AFQD.Multimatrix r k) :
    ampBlocks m (b + c) = ampBlocks m b + ampBlocks m c :=
  funext fun i ↦ Matrix.blockDiagonal_add (fun _ : Fin (m i) ↦ b i) (fun _ ↦ c i)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.MultimatrixTrace.ampBlocks_add

theorem ampBlocks_smul (m : Fin r → ℕ) (a : ℂ) (b : AFQD.Multimatrix r k) :
    ampBlocks m (a • b) = a • ampBlocks m b :=
  funext fun i ↦ Matrix.blockDiagonal_smul a (fun _ : Fin (m i) ↦ b i)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.MultimatrixTrace.ampBlocks_smul

theorem ampBlocks_mul (m : Fin r → ℕ) (b c : AFQD.Multimatrix r k) :
    ampBlocks m (b * c) = fun i ↦ ampBlocks m b i * ampBlocks m c i :=
  funext fun i ↦ Matrix.blockDiagonal_mul (fun _ : Fin (m i) ↦ b i) (fun _ ↦ c i)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.MultimatrixTrace.ampBlocks_mul

theorem ampBlocks_one (m : Fin r → ℕ) : ampBlocks m (1 : AFQD.Multimatrix r k) = 1 :=
  funext fun _ ↦ Matrix.blockDiagonal_one

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.MultimatrixTrace.ampBlocks_one

theorem ampBlocks_star (m : Fin r → ℕ) (b : AFQD.Multimatrix r k) :
    ampBlocks m (star b) = fun i ↦ (ampBlocks m b i)ᴴ :=
  funext fun i ↦ (Matrix.blockDiagonal_conjTranspose (fun _ : Fin (m i) ↦ b i)).symm

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.MultimatrixTrace.ampBlocks_star

/-- The amplification `b ↦ ⊕_i (b i ⊗ 1_{m i})` as a linear map. -/
def ampLinear (m : Fin r → ℕ) :
    AFQD.Multimatrix r k →ₗ[ℂ] Matrix (AmpIndex k m) (AmpIndex k m) ℂ where
  toFun b := Matrix.blockDiagonal' (ampBlocks m b)
  map_add' b c := by
    change Matrix.blockDiagonal' (ampBlocks m (b + c)) =
      Matrix.blockDiagonal' (ampBlocks m b) + Matrix.blockDiagonal' (ampBlocks m c)
    rw [ampBlocks_add]
    exact Matrix.blockDiagonal'_add _ _
  map_smul' a b := by
    change Matrix.blockDiagonal' (ampBlocks m (a • b)) =
      a • Matrix.blockDiagonal' (ampBlocks m b)
    rw [ampBlocks_smul]
    exact Matrix.blockDiagonal'_smul a _

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.MultimatrixTrace.ampLinear

/-- The amplification `b ↦ ⊕_i (b i ⊗ 1_{m i})` as a unital ⋆-homomorphism. -/
def ampHom (m : Fin r → ℕ) :
    AFQD.Multimatrix r k →⋆ₐ[ℂ] Matrix (AmpIndex k m) (AmpIndex k m) ℂ :=
  { AlgHom.ofLinearMap (ampLinear m)
      (by
        change Matrix.blockDiagonal' (ampBlocks m (1 : AFQD.Multimatrix r k)) = 1
        rw [ampBlocks_one]
        exact Matrix.blockDiagonal'_one)
      (fun b c ↦ by
        change Matrix.blockDiagonal' (ampBlocks m (b * c)) =
          Matrix.blockDiagonal' (ampBlocks m b) * Matrix.blockDiagonal' (ampBlocks m c)
        rw [ampBlocks_mul]
        exact Matrix.blockDiagonal'_mul _ _) with
    map_star' := fun b ↦ by
      change Matrix.blockDiagonal' (ampBlocks m (star b)) =
        (Matrix.blockDiagonal' (ampBlocks m b))ᴴ
      rw [ampBlocks_star]
      exact (Matrix.blockDiagonal'_conjTranspose _).symm }

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.MultimatrixTrace.ampHom

/-- `trace (⊕_i b i ⊗ 1_{m i}) = ∑ i, m i · trace (b i)`. -/
theorem trace_ampHom (m : Fin r → ℕ) (b : AFQD.Multimatrix r k) :
    Matrix.trace (ampHom m b) = ∑ i, (m i : ℂ) * Matrix.trace (b i) := by
  change Matrix.trace (Matrix.blockDiagonal' (ampBlocks m b)) = _
  simp only [Matrix.trace_blockDiagonal', ampBlocks, Matrix.trace_blockDiagonal,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.MultimatrixTrace.trace_ampHom

/-- Reindexing onto `Fin (card ι)` preserves the trace. -/
theorem trace_matrixReindex_equivFin {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) :
    Matrix.trace (matrixReindexStarAlgEquiv (Fintype.equivFin ι) A) = Matrix.trace A :=
  Equiv.sum_comp (Fintype.equivFin ι).symm (fun x ↦ A x x)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.MultimatrixTrace.trace_matrixReindex_equivFin

/-- The amplified representation on `Fin N` with `N = card (Σ i, Fin (k i) × Fin (m i))`. -/
def ampRep (m : Fin r → ℕ) :
    AFQD.Multimatrix r k →⋆ₐ[ℂ]
      Matrix (Fin (Fintype.card (AmpIndex k m))) (Fin (Fintype.card (AmpIndex k m))) ℂ :=
  (matrixReindexStarAlgEquiv (Fintype.equivFin (AmpIndex k m))).toStarAlgHom.comp (ampHom m)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.MultimatrixTrace.ampRep

/-- `trace (ampRep m b) = ∑ i, m i · trace (b i)`. -/
theorem trace_ampRep (m : Fin r → ℕ) (b : AFQD.Multimatrix r k) :
    Matrix.trace (ampRep m b) = ∑ i, (m i : ℂ) * Matrix.trace (b i) := by
  change Matrix.trace (matrixReindexStarAlgEquiv (Fintype.equivFin (AmpIndex k m))
    (ampHom m b)) = _
  rw [trace_matrixReindex_equivFin, trace_ampHom]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.MultimatrixTrace.trace_ampRep

/-- The size of the amplified representation is `∑ i, k i · m i`. -/
theorem card_ampIndex (m : Fin r → ℕ) :
    Fintype.card (AmpIndex k m) = ∑ i, k i * m i := by
  rw [Fintype.card_sigma]
  exact Finset.sum_congr rfl fun i _ ↦ by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.MultimatrixTrace.card_ampIndex

end

end MultimatrixTrace
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation
