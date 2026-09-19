import GroupApproximation.Computability.SoficRecognitionSecondLevel
import GroupApproximation.Sofic.Hyperlinear

/-!
# Hyperlinearity is second-level hard on enumerated presentations, given one counterexample

Hyperlinearity is hereditary, holds for the trivial group, and is a local
approximation property; so as soon as one finite presentation code presents
a non-hyperlinear group, the hereditary switch of
`Computability.SoficRecognitionSecondLevel` makes hyperlinearity of
enumerated presentation codes `Π⁰₂`-hard and non-hyperlinearity
`Σ⁰₂`-hard.  This is the enumerated-presentation half of side (B) of the
research claim `approximation-property-recognition-dichotomy`; the
existence of the counterexample is the program goal `non-hyperlinear-group`.
-/

namespace GroupApproximation
namespace HyperlinearEnumeratedHardness

open PresentationCodes SoficRecognitionSecondLevel

/-- Given one finite presentation code of a non-hyperlinear group,
hyperlinearity of enumerated presentation codes is `Π⁰₂`-hard. -/
theorem hyperlinearCode_pi02Hard_of_exists
    (h : ∃ seed : PresentationCode, ¬ IsHyperlinear (Carrier seed)) :
    ArithmeticalHierarchy.Pi02Hard
      (fun q : EnumeratedPresentationCodes.PresentationCode ↦
        IsHyperlinear (EnumeratedPresentationCodes.Carrier q)) := by
  obtain ⟨seed, hseed⟩ := h
  exact pi02Hard_of_hereditary (fun (H : Type) (_ : Group H) ↦ IsHyperlinear H)
    (fun f hf hK ↦ isHyperlinear_of_injective f hf hK)
    (isHyperlinear_of_isSofic isSofic_punit) seed hseed

/-- The complementary `Σ⁰₂`-hardness of non-hyperlinearity. -/
theorem nonhyperlinearCode_sigma02Hard_of_exists
    (h : ∃ seed : PresentationCode, ¬ IsHyperlinear (Carrier seed)) :
    ArithmeticalHierarchy.Sigma02Hard
      (fun q : EnumeratedPresentationCodes.PresentationCode ↦
        ¬ IsHyperlinear (EnumeratedPresentationCodes.Carrier q)) := by
  obtain ⟨seed, hseed⟩ := h
  exact sigma02Hard_of_hereditary (fun (H : Type) (_ : Group H) ↦ IsHyperlinear H)
    (fun f hf hK ↦ isHyperlinear_of_injective f hf hK)
    (isHyperlinear_of_isSofic isSofic_punit) seed hseed

end HyperlinearEnumeratedHardness
end GroupApproximation
