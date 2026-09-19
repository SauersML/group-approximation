import GroupApproximation.Higman.OmegaTowerSignedShift

/-!
# One explicit outer Omega pinch rewrite

This is the local rewrite consumed by the eventual length induction: an
opposite-sign pair whose middle base entry is an embedded `a_l` loses both
stable letters, and the next base entry is multiplied by the exactly shifted
`a`-letter.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open Conj Seq HNNExtension

/-- Collapse one displayed outer pinch whose middle entry is an embedded
conjugate-basis letter. -/
theorem prod_outer_aElt_pair (m : ℕ) (u : ℤˣ) (l : E)
    (g' : SlimPi m) (tail : List (ℤˣ × SlimPi m)) :
    ((((u, slimPiF3Hom m (aElt l)) :: (-u, g') :: tail).map
        (HNNDescent.letter (slimShiftRangeEquiv m))).prod) =
      of (slimPiF3Hom m (aElt (signedBlockShift m u l)) * g') *
        ((tail.map (HNNDescent.letter (slimShiftRangeEquiv m))).prod) := by
  exact HNNDescent.prod_cons_cons (slimShiftRangeEquiv m)
    u (-u) (slimPiF3Hom m (aElt l)) g'
    (slimPiF3Hom m (aElt (signedBlockShift m u l))) tail
    (by simp) (outer_conj_aElt_signed m u l)

end Omega
end Higman
end GroupApproximation
