import GroupApproximation.Higman.OmegaTowerConjugateBasisPinch
import GroupApproximation.Higman.OmegaTowerSignedShift

/-!
# Coordinate action of the outer Omega shift

The outer scan tracks words in the free conjugate basis.  These lemmas show
that its two basis-index homomorphisms act on the literal sequence coordinate
`bK f` by the same `shiftPow` and `unshift` operations used by the Omega
block calculus.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open Conj Seq

/-- The positive coordinate homomorphism sends `b_f` to `b_(shiftPow m f)`. -/
theorem shiftKPowHom_bK (m : ℕ) (f : E) :
    shiftKPowHom m (bK f) = bK (shiftPow m f) := by
  apply Subtype.ext
  change ((shiftEquiv : MulAut F₃) ^ m) (bElt f) = bElt (shiftPow m f)
  rw [shiftEquiv_pow_apply, shiftAut_iterate_bElt]

/-- The inverse coordinate homomorphism sends `b_f` to `b_(unshift m f)`. -/
theorem unshiftKPowHom_bK (m : ℕ) (f : E) :
    unshiftKPowHom m (bK f) = bK (unshift m f) := by
  apply Subtype.ext
  rw [unshiftKPowHom_coe]
  apply ((shiftEquiv : MulAut F₃) ^ m).injective
  calc
    ((shiftEquiv : MulAut F₃) ^ m) ((shiftAutInv^[m]) (bElt f)) =
        ((shiftEquiv : MulAut F₃) ^ m)
          ((((shiftEquiv : MulAut F₃) ^ m).symm) (bElt f)) := by
            rw [shiftEquiv_pow_symm_apply]
    _ = bElt f := ((shiftEquiv : MulAut F₃) ^ m).apply_symm_apply (bElt f)
    _ = ((shiftEquiv : MulAut F₃) ^ m) (bElt (unshift m f)) := by
      rw [shiftEquiv_pow_apply, shiftAut_iterate_bElt, shiftPow_unshift]

/-- The signed coordinate operation agrees with the signed sequence shift on
one literal free conjugate-basis generator. -/
theorem signedCoordShift_of_bK (m : ℕ) (u : ℤˣ) (f : E) :
    signedCoordShift m u (FreeGroup.of (bK f)) =
      FreeGroup.of (bK (signedBlockShift m u f)) := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · rw [signedCoordShift_one, FreeGroup.map.of, shiftKPowHom_bK,
      signedBlockShift_one]
  · rw [signedCoordShift_negOne, FreeGroup.map.of, unshiftKPowHom_bK,
      signedBlockShift_negOne]

end Omega
end Higman
end GroupApproximation
