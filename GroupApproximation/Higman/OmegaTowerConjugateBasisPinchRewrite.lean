import GroupApproximation.Higman.OmegaTowerConjugateBasisPinch

/-!
# One outer Omega pinch rewrite for a classified conjugate-basis word

This is the word-level version of `prod_outer_aElt_pair`.  It is the local
rewrite needed by the outer Britton scan after the inner classifier has
returned an arbitrary word in the conjugate basis `K`.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open Conj Seq HNNExtension

/-- Collapse one displayed outer pinch whose middle base entry is the image
of an arbitrary conjugate-basis word. -/
theorem prod_outer_cbHom_pair (m : ℕ) (u : ℤˣ) (w : FreeGroup ↥K)
    (g' : SlimPi m) (tail : List (ℤˣ × SlimPi m)) :
    ((((u, slimPiF3Hom m (cbHom w)) :: (-u, g') :: tail).map
        (HNNDescent.letter (slimShiftRangeEquiv m))).prod) =
      of (slimPiF3Hom m (cbHom (signedCoordShift m u w)) * g') *
        ((tail.map (HNNDescent.letter (slimShiftRangeEquiv m))).prod) := by
  exact HNNDescent.prod_cons_cons (slimShiftRangeEquiv m)
    u (-u) (slimPiF3Hom m (cbHom w)) g'
    (slimPiF3Hom m (cbHom (signedCoordShift m u w))) tail
    (by simp) (outer_conj_cbHom_signed m u w)

end Omega
end Higman
end GroupApproximation
