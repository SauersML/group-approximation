import GroupApproximation.Algebra.CoprodIAltWord
import GroupApproximation.Higman.OmegaTowerLowStableRetractions

/-!
# Indexed free-product form of the low-row/full-code target

The free group on a sum alphabet is canonically the indexed free product of
the free groups on the two summands.  In this form each projected link letter
has one full-code syllable followed by one inverse low-row syllable, and
Mathlib's reduced `CoprodI.Word` normal form applies directly.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Conj
open GroupApproximation.Higman.Seq
open Monoid Monoid.CoprodI

/-- The low-row and full-code factors. -/
abbrev LowStableFactor (m : ℕ) : Bool → Type
  | false => FreeGroup (LowIndex m)
  | true => F₃

@[reducible] instance lowStableFactorGroup (m : ℕ) (i : Bool) :
    Group (LowStableFactor m i) := by
  cases i <;> simp only [LowStableFactor] <;> infer_instance

abbrev LowStableIndexed (m : ℕ) := CoprodI (LowStableFactor m)

/-- Read the disjoint free alphabet as the two factors of an indexed free
product. -/
def lowStableToIndexed (m : ℕ) :
    LowStableFree m →* LowStableIndexed m :=
  FreeGroup.lift (Sum.elim
    (fun i : LowIndex m => CoprodI.of (i := false) (FreeGroup.of i))
    (fun i : Fin 3 => CoprodI.of (i := true) (FreeGroup.of i)))

/-- The actual low-row word in the left free factor. -/
noncomputable def lowRowFactor (m : ℕ) :
    FreeGroup ℤ →* FreeGroup (LowIndex m) :=
  FreeGroup.lift fun i =>
    if hi : i < (m : ℤ) then FreeGroup.of ⟨i, hi⟩ else 1

theorem lowRowProjection_eq_leftFactor (m : ℕ) :
    lowRowProjection m =
      (FreeGroup.map Sum.inl).comp (lowRowFactor m) := by
  refine FreeGroup.ext_hom _ _ fun i => ?_
  by_cases hi : i < (m : ℤ)
  · simp [lowRowProjection, lowRowFactor, hi]
  · simp [lowRowProjection, lowRowFactor, hi]

@[simp] theorem lowStableToIndexed_lowRowProjection
    (m : ℕ) (w : FreeGroup ℤ) :
    lowStableToIndexed m (lowRowProjection m w) =
      CoprodI.of (i := false) (lowRowFactor m w) := by
  rw [lowRowProjection_eq_leftFactor]
  have hleft :
      (lowStableToIndexed m).comp (FreeGroup.map Sum.inl) =
        (CoprodI.of (M := LowStableFactor m) (i := false)) := by
    refine FreeGroup.ext_hom _ _ fun i => ?_
    change lowStableToIndexed m
        ((FreeGroup.map Sum.inl) (FreeGroup.of i)) = _
    rw [FreeGroup.map.of, lowStableToIndexed, FreeGroup.lift_apply_of]
    rfl
  change ((lowStableToIndexed m).comp (FreeGroup.map Sum.inl))
      (lowRowFactor m w) = _
  exact DFunLike.congr_fun hleft (lowRowFactor m w)

@[simp] theorem lowStableToIndexed_stableFreeHom
    (m : ℕ) (w : F₃) :
    lowStableToIndexed m (stableFreeHom m w) =
      CoprodI.of (i := true) w := by
  change ((lowStableToIndexed m).comp (stableFreeHom m)) w = _
  have hright :
      (lowStableToIndexed m).comp (stableFreeHom m) =
        (CoprodI.of (M := LowStableFactor m) (i := true)) := by
    refine FreeGroup.ext_hom _ _ fun i => ?_
    change lowStableToIndexed m
        ((FreeGroup.map Sum.inr) (FreeGroup.of i)) = _
    rw [FreeGroup.map.of, lowStableToIndexed, FreeGroup.lift_apply_of]
    rfl
  exact DFunLike.congr_fun hright w

@[simp] theorem lowStableToIndexed_indexLinkElem
    (m : ℕ) (beta : E) :
    lowStableToIndexed m
        (lowStableProjection3 m (indexLinkElem m beta)) =
      CoprodI.of (i := true) (aElt beta) *
        (CoprodI.of (i := false) (lowRowFactor m (elt beta)))⁻¹ := by
  simp only [lowStableProjection3_indexLinkElem, map_mul, map_inv,
    lowStableToIndexed_stableFreeHom, lowStableToIndexed_lowRowProjection]

end Omega
end Higman
end GroupApproximation
