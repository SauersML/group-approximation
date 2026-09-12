import GroupApproximation.Analysis.CStarCorner
import GroupApproximation.Analysis.CStarMatrixTwo

/-!
# The upper-left corner of a two-by-two C-star matrix algebra

The matrix unit `e₀₀` is a self-adjoint idempotent of `M₂(K)`, and
`x ↦ e₀₀ x e₀₀`, which is just `x ↦ cStarMatrixUnitTwo 0 0 x`, identifies `K`
with the corner `e₀₀ M₂(K) e₀₀`.

This is the corner calculus in which an evaluated Ueda representation is read.
An element of the universal C-star HNN algebra is sent into `M₂` of a
coordinate algebra, and the two-by-two picture is faithful exactly because the
identification below is injective, so the corner embedding detects elements of
the universal algebra rather than merely representing them.

The local order instances mirror `CStarMatrixTwo`: Mathlib assembles
`CStarAlgebra (CStarMatrix n n K)` out of the positivity order of `K`, so
`PartialOrder K` and `StarOrderedRing K` have to be in scope here, and they are
kept local so that they do not enter the `Semiring`/`StarRing` paths of `K`
itself downstream.
-/

namespace GroupApproximation

open Matrix
open scoped CStarAlgebra Matrix

noncomputable section

universe u

variable {K : Type u} [CStarAlgebra K]

noncomputable local instance : PartialOrder K := CStarAlgebra.spectralOrder K
local instance : StarOrderedRing K := CStarAlgebra.spectralOrderedRing K

/-! ## The corner projection `e₀₀` -/

/-- The upper-left matrix unit of `M₂(K)`, the projection cutting out the
corner. -/
def cStarUpperLeftCornerUnit : CStarMatrix (Fin 2) (Fin 2) K :=
  cStarMatrixUnitTwo 0 0 (1 : K)

theorem cStarUpperLeftCornerUnit_star :
    star (cStarUpperLeftCornerUnit : CStarMatrix (Fin 2) (Fin 2) K) =
      cStarUpperLeftCornerUnit := by
  show star (cStarMatrixUnitTwo 0 0 (1 : K)) = cStarMatrixUnitTwo 0 0 (1 : K)
  rw [star_cStarMatrixUnitTwo, star_one]

theorem cStarUpperLeftCornerUnit_mul :
    (cStarUpperLeftCornerUnit : CStarMatrix (Fin 2) (Fin 2) K) *
        cStarUpperLeftCornerUnit = cStarUpperLeftCornerUnit := by
  show cStarMatrixUnitTwo 0 0 (1 : K) * cStarMatrixUnitTwo 0 0 (1 : K) =
    cStarMatrixUnitTwo 0 0 (1 : K)
  rw [cStarMatrixUnitTwo_mul]
  simp

/-- Every matrix unit in the upper-left position is supported by `e₀₀`. -/
theorem cStarMatrixUnitTwo_zeroZero_mem_corner (x : K) :
    cStarMatrixUnitTwo 0 0 x ∈
      cStarCornerSubalgebra
        (cStarUpperLeftCornerUnit : CStarMatrix (Fin 2) (Fin 2) K)
        cStarUpperLeftCornerUnit_star := by
  constructor
  · show cStarMatrixUnitTwo 0 0 (1 : K) * cStarMatrixUnitTwo 0 0 x =
      cStarMatrixUnitTwo 0 0 x
    rw [cStarMatrixUnitTwo_mul]
    simp
  · show cStarMatrixUnitTwo 0 0 x * cStarMatrixUnitTwo 0 0 (1 : K) =
      cStarMatrixUnitTwo 0 0 x
    rw [cStarMatrixUnitTwo_mul]
    simp

/-! ## `K` is the upper-left corner -/

/-- The identification of `K` with the corner `e₀₀ M₂(K) e₀₀`. -/
def cStarUpperLeftCornerMap :
    K →⋆ₐ[ℂ]
      CStarCorner (cStarUpperLeftCornerUnit : CStarMatrix (Fin 2) (Fin 2) K)
        cStarUpperLeftCornerUnit_star cStarUpperLeftCornerUnit_mul where
  toFun x := ⟨cStarMatrixUnitTwo 0 0 x, cStarMatrixUnitTwo_zeroZero_mem_corner x⟩
  map_one' := by
    apply Subtype.ext
    rfl
  map_mul' x y := by
    apply Subtype.ext
    show cStarMatrixUnitTwo 0 0 (x * y) =
      cStarMatrixUnitTwo 0 0 x * cStarMatrixUnitTwo 0 0 y
    rw [cStarMatrixUnitTwo_mul]
    simp
  map_zero' := by
    apply Subtype.ext
    show cStarMatrixUnitTwo 0 0 (0 : K) = 0
    ext i j
    fin_cases i <;> fin_cases j <;> simp [cStarMatrixUnitTwo]
  map_add' x y := by
    apply Subtype.ext
    show cStarMatrixUnitTwo 0 0 (x + y) =
      cStarMatrixUnitTwo 0 0 x + cStarMatrixUnitTwo 0 0 y
    ext i j
    fin_cases i <;> fin_cases j <;> simp [cStarMatrixUnitTwo]
  commutes' r := by
    apply Subtype.ext
    change cStarMatrixUnitTwo 0 0 (algebraMap ℂ K r) =
      ((algebraMap ℂ
        (CStarCorner (cStarUpperLeftCornerUnit : CStarMatrix (Fin 2) (Fin 2) K)
          cStarUpperLeftCornerUnit_star cStarUpperLeftCornerUnit_mul) r :
        CStarCorner (cStarUpperLeftCornerUnit : CStarMatrix (Fin 2) (Fin 2) K)
          cStarUpperLeftCornerUnit_star cStarUpperLeftCornerUnit_mul) :
        CStarMatrix (Fin 2) (Fin 2) K)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    show cStarMatrixUnitTwo 0 0 (r • (1 : K)) =
      r • cStarMatrixUnitTwo 0 0 (1 : K)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [cStarMatrixUnitTwo]
  map_star' x := by
    apply Subtype.ext
    show cStarMatrixUnitTwo 0 0 (star x) = star (cStarMatrixUnitTwo 0 0 x)
    rw [star_cStarMatrixUnitTwo]

@[simp] theorem coe_cStarUpperLeftCornerMap (x : K) :
    ((cStarUpperLeftCornerMap x :
      CStarCorner (cStarUpperLeftCornerUnit : CStarMatrix (Fin 2) (Fin 2) K)
        cStarUpperLeftCornerUnit_star cStarUpperLeftCornerUnit_mul) :
      CStarMatrix (Fin 2) (Fin 2) K) = cStarMatrixUnitTwo 0 0 x :=
  rfl

/-- The corner identification is faithful, so the two-by-two picture of the
universal HNN algebra detects elements. -/
theorem cStarUpperLeftCornerMap_injective :
    Function.Injective
      (cStarUpperLeftCornerMap :
        K →⋆ₐ[ℂ]
          CStarCorner (cStarUpperLeftCornerUnit : CStarMatrix (Fin 2) (Fin 2) K)
            cStarUpperLeftCornerUnit_star cStarUpperLeftCornerUnit_mul) := by
  intro x y hxy
  have h : cStarMatrixUnitTwo 0 0 x = cStarMatrixUnitTwo 0 0 y :=
    congrArg Subtype.val hxy
  have hentry :=
    congrArg (fun M : CStarMatrix (Fin 2) (Fin 2) K ↦ M 0 0) h
  simpa using hentry

end

end GroupApproximation
