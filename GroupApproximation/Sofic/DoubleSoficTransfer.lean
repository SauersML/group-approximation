import GroupApproximation.Sofic.LineDouble
import GroupApproximation.Sofic.SoficFiniteSemidirect

/-!
# Soficity transfers forced by the double constructions

This file records the unconditional approximation-theoretic content of the
flip construction.  It uses only results proved in this repository:

* the explicit isomorphism from the `C₂` free-lamp amalgam to the finite
  flip extension of the symmetric double;
* the induced finite-semidirect-product permutation model;
* the explicit embedding of the symmetric double in the line double.

In particular, no centralizer-normalization statement occurs as a premise.
-/

namespace GroupApproximation

variable (G : Type) [Group G] (Γ : Subgroup G)

/-- If the symmetric double is sofic, then its `C₂` free-lamp amalgam is
sofic. -/
theorem isSofic_freeLamp_flip_of_isSofic_symmetricDouble
    (hD : IsSofic (SymmetricDouble G Γ)) : IsSofic (FreeLamp G Γ FlipC2) := by
  have hE : IsSofic (SymmetricDoubleFlipExtension G Γ) :=
    isSofic_semidirectProduct_of_finite (doubleFlipAction G Γ) hD
  exact (isSofic_mulEquiv_iff
    (freeLampMulEquivSymmetricDoubleFlip G Γ)).mpr hE

/-- If the infinite line double is sofic, then its two-vertex symmetric
subdouble is sofic. -/
theorem isSofic_symmetricDouble_of_isSofic_lineDouble
    (hline : IsSofic (LineDouble G Γ)) : IsSofic (SymmetricDouble G Γ) :=
  isSofic_of_injective (doubleToLine G Γ) (doubleToLine_injective G Γ) hline

/-- The exact unconditional reduction for Question 1.6: soficity of the
infinite line double forces soficity of the `C₂` free-lamp amalgam. -/
theorem isSofic_freeLamp_flip_of_isSofic_lineDouble
    (hline : IsSofic (LineDouble G Γ)) : IsSofic (FreeLamp G Γ FlipC2) :=
  isSofic_freeLamp_flip_of_isSofic_symmetricDouble G Γ
    (isSofic_symmetricDouble_of_isSofic_lineDouble G Γ hline)

/-- A nonsofic `C₂` free-lamp amalgam forces the two-vertex symmetric double
to be nonsofic. -/
theorem not_isSofic_symmetricDouble_of_not_isSofic_freeLamp_flip
    (hLamp : ¬ IsSofic (FreeLamp G Γ FlipC2)) :
    ¬ IsSofic (SymmetricDouble G Γ) := fun hD ↦
  hLamp (isSofic_freeLamp_flip_of_isSofic_symmetricDouble G Γ hD)

/-- A nonsofic `C₂` free-lamp amalgam forces the exact infinite line double
from Question 1.6 to be nonsofic. -/
theorem not_isSofic_lineDouble_of_not_isSofic_freeLamp_flip
    (hLamp : ¬ IsSofic (FreeLamp G Γ FlipC2)) :
    ¬ IsSofic (LineDouble G Γ) := fun hline ↦
  hLamp (isSofic_freeLamp_flip_of_isSofic_lineDouble G Γ hline)

end GroupApproximation
