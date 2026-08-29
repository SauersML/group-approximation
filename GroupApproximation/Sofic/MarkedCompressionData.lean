import GroupApproximation.Sofic.NormMFResidualDetector
import GroupApproximation.Kazhdan.KazhdanProjection

/-!
# The marked Kazhdan-compression data

This file records the endomorphism-based data used to construct the concrete
marked group.  A `MarkedCompressionData Γ E` records a Kazhdan
group `Γ` mapped into `E`, an element `t` conjugating the image of `Γ` onto
the image of an endomorphism `alpha`, a `Γ`-centralizing element `c`, and a
distinguished `a : Γ`, such that the marked compression word

`w = [t c t⁻¹, (iota a) (t c t⁻¹) (iota a)⁻¹]`

is a central involution of `E`.

Deliberately absent: injectivity of `iota`, properness of `alpha`, and
`a ∉ range alpha`.  Those are only needed to construct groups in which the
marked word is nontrivial.  The analytic theorem is stated against the
strictly weaker `MarkedCompressionInclusionData`, because it consumes only
`t · iota(Γ) · t⁻¹ ⊆ iota(Γ)`.  The conversion is defined in
`MarkedCompressionInclusionData.lean`.
-/

namespace GroupApproximation

universe u

end GroupApproximation
