import GroupApproximation.Sofic.MFCamouflage

/-!
# Sentence-level closure for the camouflage factorization proof

The statements here name the two restrictions which the printed proof takes
before invoking the amalgam's universal property.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

variable {B : Type} [Group B] {Q : Type} [Group Q]
  {T : Type} [Group T]

/-- Under the target hypothesis, the restriction of an amalgam map to the
black-hole vertex is trivial. -/
theorem manuscript_camouflage_restriction_to_blackHole
    (d : B) (f : MFCamouflage.Camouflage d Q →* T)
    (hT : ∀ phi : B →* T, phi = 1) :
    f.comp (MFCamouflage.blackHole d Q) = 1 :=
  hT _

/-- Consequently its further restriction to the amalgamated cyclic edge is
trivial, exactly as asserted in the next printed sentence. -/
theorem manuscript_camouflage_restriction_to_edge
    (d : B) (f : MFCamouflage.Camouflage d Q →* T)
    (hT : ∀ phi : B →* T, phi = 1) :
    (f.comp (MFCamouflage.blackHole d Q)).comp
      (MFCamouflage.leftEdge d) = 1 := by
  rw [manuscript_camouflage_restriction_to_blackHole d f hT]
  rfl

end OneSidedMFRadical
end Manuscript
end GroupApproximation
