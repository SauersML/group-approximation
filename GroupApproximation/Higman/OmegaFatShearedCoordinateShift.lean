import GroupApproximation.Higman.OmegaFatShearedCoordinateBase

/-!
# The global alphabet shift for one sheared coordinate

Inside the `(j+1)`-window alphabet, translation by the `j`th basis vector is
a genuine permutation.  Its restriction to the zero slice is exactly the
asymmetric source-to-target map from `OmegaFatShearedCoordinateEdge`.

This is the global-shift ingredient needed to reuse one concrete cutter for
all adjacent coefficient slices; unlike the refuted shear on the semantic
group, it is an honest automorphism of the free block alphabet.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Seq

/-- Translate the last coordinate of the `(j+1)`-window by `n`. -/
noncomputable def shearedCoordinateTranslate (j : ℕ) (n : ℤ) :
    ↥(blockSet (j + 1)) → ↥(blockSet (j + 1)) :=
  fun beta =>
    ⟨beta.1 + Finsupp.single (j : ℤ) n,
      add_single_mem_blockSet beta.2 n⟩

theorem shearedCoordinateTranslate_add
    (j : ℕ) (r s : ℤ) (beta : ↥(blockSet (j + 1))) :
    shearedCoordinateTranslate j r (shearedCoordinateTranslate j s beta) =
      shearedCoordinateTranslate j (s + r) beta := by
  apply Subtype.ext
  ext i
  simp only [shearedCoordinateTranslate, Finsupp.add_apply,
    Finsupp.single_apply]
  by_cases hi : (j : ℤ) = i <;> simp [hi]
  ring

@[simp] theorem shearedCoordinateTranslate_zero
    (j : ℕ) (beta : ↥(blockSet (j + 1))) :
    shearedCoordinateTranslate j 0 beta = beta := by
  apply Subtype.ext
  simp [shearedCoordinateTranslate]

/-- Translation by one is a permutation of the complete coefficient
alphabet, with inverse translation by minus one. -/
noncomputable def shearedCoordinateShiftEquiv (j : ℕ) :
    ↥(blockSet (j + 1)) ≃ ↥(blockSet (j + 1)) where
  toFun := shearedCoordinateTranslate j 1
  invFun := shearedCoordinateTranslate j (-1)
  left_inv beta := by
    rw [shearedCoordinateTranslate_add]
    norm_num
    exact shearedCoordinateTranslate_zero j beta
  right_inv beta := by
    rw [shearedCoordinateTranslate_add]
    norm_num
    exact shearedCoordinateTranslate_zero j beta

/-- Embed the preceding window as the zero last-coordinate slice. -/
def shearedCoordinateZeroSlice (j : ℕ) :
    ↥(blockSet j) → ↥(blockSet (j + 1)) :=
  shearedBlockIncl (Nat.le_succ j)

theorem shearedCoordinateShiftEquiv_zeroSlice
    (j : ℕ) (beta : ↥(blockSet j)) :
    shearedCoordinateShiftEquiv j (shearedCoordinateZeroSlice j beta) =
      shearedBlockStep j beta := by
  apply Subtype.ext
  rfl

/-- The induced automorphism of the complete `(j+1)`-window free group. -/
noncomputable def shearedCoordinateFreeShiftEquiv (j : ℕ) :
    FreeGroup ↥(blockSet (j + 1)) ≃* FreeGroup ↥(blockSet (j + 1)) :=
  FreeGroup.freeGroupCongr (shearedCoordinateShiftEquiv j)

@[simp] theorem shearedCoordinateFreeShiftEquiv_of_zeroSlice
    (j : ℕ) (beta : ↥(blockSet j)) :
    shearedCoordinateFreeShiftEquiv j
        (FreeGroup.of (shearedCoordinateZeroSlice j beta)) =
      FreeGroup.of (shearedBlockStep j beta) := by
  change FreeGroup.of
      (shearedCoordinateShiftEquiv j (shearedCoordinateZeroSlice j beta)) = _
  rw [shearedCoordinateShiftEquiv_zeroSlice]

/-- On the complete preceding-window free group, the global free shift
restricts exactly to the asymmetric coordinate target map. -/
theorem shearedCoordinateFreeShift_restrict
    (j : ℕ) :
    (shearedCoordinateFreeShiftEquiv j).toMonoidHom.comp
        (FreeGroup.map (shearedCoordinateZeroSlice j)) =
      FreeGroup.map (shearedBlockStep j) := by
  refine FreeGroup.ext_hom _ _ fun beta ↦ ?_
  simp

end Omega
end Higman
end GroupApproximation
