import GroupApproximation.Manuscript.NonMFNotes.Full.TWWKK.StabQGroupOrth
import Mathlib.Analysis.CStarAlgebra.CStarMatrix

/-!
# Diagonal corners of `2 × 2` matrices over a non-unital C⋆-algebra

Cuntz's description of the group structure on `[𝒦 ⊗ qA, 𝒦 ⊗ qB]`
(J. Cuntz, *A new look at KK-theory*, K-Theory 1 (1987) 31--51, §1; Blackadar,
*K-theory for operator algebras*, 17.8) compares a pair of orthogonal
`⋆`-homomorphisms with the two diagonal corner embeddings
`B → M₂(B)`, `b ↦ diag(b, 0)` and `b ↦ diag(0, b)`.

This file is shared by the lanes TWWKK-Stab (the combination map
`𝒦 ⊗ M₂(B) → 𝒦 ⊗ B`) and TWWKK-Qalg (the flip homotopy in `M₂(qA)`).

* `matrixNonUnitalCStarAlgebra`: the C⋆-algebra structure on `CStarMatrix n n B` for an
  arbitrary non-unital C⋆-algebra `B`.  Mathlib's instance
  `CStarMatrix.instNonUnitalCStarAlgebra` asks for a `StarOrderedRing` structure on `B`; we
  supply the canonical one, `CStarAlgebra.spectralOrder`, which is the only
  `StarOrderedRing` order on a C⋆-algebra.  The instance has low priority, so an algebra
  already carrying an order uses Mathlib's instance.
* `corner₁₁ B`, `corner₂₂ B : B →⋆ₙₐ[ℂ] CStarMatrix (Fin 2) (Fin 2) B`: the diagonal corners;
* `nOrth_corner₁₁_corner₂₂`: the two corners are orthogonal.

Manuscript: `non_mf_group_notes.tex`, the UCT hypothesis of Tikuisis--White--Winter
(`thm:fixed-radical-membership`); infrastructure for the concrete Kasparov theory of lane
TWWKK.
-/

namespace GroupApproximation.Full.TWWKK

universe u

noncomputable section

/-- **Matrices over a non-unital C⋆-algebra form a non-unital C⋆-algebra** (for any
non-unital C⋆-algebra `B`, using the spectral order on `B` to access Mathlib's instance). -/
noncomputable instance (priority := 50) matrixNonUnitalCStarAlgebra {B : Type u}
    [NonUnitalCStarAlgebra B] {n : Type*} [Fintype n] :
    NonUnitalCStarAlgebra (CStarMatrix n n B) :=
  letI : PartialOrder B := CStarAlgebra.spectralOrder B
  letI : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  CStarMatrix.instNonUnitalCStarAlgebra

namespace MatrixCorner

variable {B : Type u} [NonUnitalCStarAlgebra B]

theorem ofMatrix_congr {M N : Matrix (Fin 2) (Fin 2) B} (h : M = N) :
    (CStarMatrix.ofMatrix M : CStarMatrix (Fin 2) (Fin 2) B) = CStarMatrix.ofMatrix N := by
  rw [h]

variable (B) in
/-- The diagonal corner embedding `b ↦ b ⊗ e_kk` of `B` into `M₂(B)`. -/
def diagCorner (k : Fin 2) : B →⋆ₙₐ[ℂ] CStarMatrix (Fin 2) (Fin 2) B where
  toFun b := CStarMatrix.ofMatrix (Matrix.single k k b)
  map_smul' r b := ofMatrix_congr (Matrix.smul_single r k k b).symm
  map_zero' := ofMatrix_congr (Matrix.single_zero k k)
  map_add' a b := ofMatrix_congr (Matrix.single_add k k a b)
  map_mul' a b := ofMatrix_congr (Matrix.single_mul_single_same a k k k b).symm
  map_star' b := ofMatrix_congr (Matrix.conjTranspose_single k k b).symm

theorem diagCorner_apply (k : Fin 2) (b : B) :
    diagCorner B k b = CStarMatrix.ofMatrix (Matrix.single k k b) :=
  rfl

theorem diagCorner_mul_diagCorner_of_ne {k l : Fin 2} (h : k ≠ l) (b b' : B) :
    diagCorner B k b * diagCorner B l b' = 0 := by
  have h1 : Matrix.single k k b * Matrix.single l l b' = 0 :=
    Matrix.single_mul_single_of_ne b k k l h b'
  exact ofMatrix_congr h1

end MatrixCorner

open MatrixCorner

variable (B : Type u) [NonUnitalCStarAlgebra B]

/-- **The upper-left corner** `b ↦ diag(b, 0)` of `M₂(B)` (Cuntz 1987, §1). -/
def corner₁₁ : B →⋆ₙₐ[ℂ] CStarMatrix (Fin 2) (Fin 2) B :=
  diagCorner B 0

/-- **The lower-right corner** `b ↦ diag(0, b)` of `M₂(B)` (Cuntz 1987, §1). -/
def corner₂₂ : B →⋆ₙₐ[ℂ] CStarMatrix (Fin 2) (Fin 2) B :=
  diagCorner B 1

variable {B}

theorem corner₁₁_apply (b : B) :
    corner₁₁ B b = CStarMatrix.ofMatrix (Matrix.single 0 0 b) :=
  rfl

theorem corner₂₂_apply (b : B) :
    corner₂₂ B b = CStarMatrix.ofMatrix (Matrix.single 1 1 b) :=
  rfl

theorem corner₁₁_apply_apply (b : B) (i j : Fin 2) :
    corner₁₁ B b i j = if 0 = i ∧ 0 = j then b else 0 :=
  rfl

theorem corner₂₂_apply_apply (b : B) (i j : Fin 2) :
    corner₂₂ B b i j = if 1 = i ∧ 1 = j then b else 0 :=
  rfl

variable (B) in
/-- The two diagonal corners of `M₂(B)` are orthogonal. -/
theorem nOrth_corner₁₁_corner₂₂ : NOrth (corner₁₁ B) (corner₂₂ B) := fun d d' =>
  ⟨diagCorner_mul_diagCorner_of_ne (by decide : (0 : Fin 2) ≠ 1) d d',
    diagCorner_mul_diagCorner_of_ne (by decide : (1 : Fin 2) ≠ 0) d' d⟩

end

end GroupApproximation.Full.TWWKK
