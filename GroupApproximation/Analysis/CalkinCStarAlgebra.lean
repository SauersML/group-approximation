import GroupApproximation.Analysis.CStarIdealApproximateUnit
import GroupApproximation.Analysis.CalkinSchauderProof

/-!
# The Calkin algebra is a C-star algebra, unconditionally

`Analysis/CalkinCompactIdeal` and `Analysis/CalkinAlgebra` record that the
Calkin algebra `Q(H) = B(H)/K(H)` is "three theorems away": Schauder's theorem,
a normed-ring structure on the quotient, and the quotient C-star identity, the
last of which "Mathlib has no quotient C-star instance of any kind" to supply.

Two of those three were already available and the record was wrong about them.

* Schauder's theorem is `Analysis/CalkinSchauderProof.compactStarClosed`.
* The quotient's ring, norm, star and C-star structure are **already in the
  root import closure**, in a different vocabulary: `Analysis/CStarIdealQuotient`
  supplies `SeminormedRing`, `NormedRing`, `NormedStarGroup` and
  `NormedAlgebra` on `R ⧸ I`, `Analysis/CStarSeminormQuotient` supplies the
  descended involution for a star-stable ideal, and
  `Analysis/CStarIdealApproximateUnit` constructs the approximate unit and with
  it `CStarTensor.instCStarRingQuotient` and
  `CStarTensor.instCStarAlgebraQuotient` — the C-star identity and the bundled
  C-star algebra, for every closed star-stable two-sided ideal of a C-star
  algebra, with no residual.  Those modules are elaborated; they are imported by
  `GroupApproximation.lean`.

So `Analysis/CStarQuotient`, which rebuilds the same quotient by hand and ends
at the named residual `CStarQuotient.CStarIdentityStatement`, is a duplicate:
its residual is not owed, it is proved, in the other vocabulary.  This module
therefore does not discharge that residual — it routes around it, and builds
the Calkin algebra on the machinery that is already verified.

What is left after this module is that all three of Arveson's extension
theorem, Stinespring's dilation theorem and Voiculescu's theorem are still
missing.  What changes is that they are now *statable*: `Q(H)` is a C-star
algebra, so `Analysis/ShulmanFillTheorem13`'s three atoms can be written as
statements about `*`-homomorphisms and completely positive maps into it, rather
than left in prose.

This module is deliberately not in the root import list: it was authored while
builds were suspended, so it is kept out of the closure until it has been
elaborated, like the `Analysis/Calkin*` modules it extends.
-/

namespace GroupApproximation
namespace CalkinAlgebra

noncomputable section

variable (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- **The compacts are star-stable**, in the class form the root-imported
quotient machinery consumes.  This is Schauder's theorem. -/
instance compactIdeal_isStarStable :
    CStarTensor.IsStarStable (compactIdeal H) where
  star_mem := by
    intro a ha
    exact compactStarClosed H a ha

/-- The compacts are closed, as an instance. -/
instance compactIdeal_isClosed' :
    IsClosed ((compactIdeal H : Ideal (H →L[ℂ] H)) : Set (H →L[ℂ] H)) :=
  isClosed_compactIdeal H

/-- `B(H)` is nontrivial as soon as `H` is: the identity and the zero operator
differ at any nonzero vector. -/
instance nontrivial_continuousLinearMap [Nontrivial H] :
    Nontrivial (H →L[ℂ] H) := by
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  refine ⟨⟨1, 0, fun h ↦ hx ?_⟩⟩
  have hxx : (1 : H →L[ℂ] H) x = (0 : H →L[ℂ] H) x := by rw [h]
  exact hxx

/-- **The Calkin algebra** `Q(H) = B(H)/K(H)`, as the plain ideal quotient.
Unlike `CalkinAlgebra.Calkin` this is not opaque, so the root-imported
instances on `R ⧸ I` apply to it directly. -/
abbrev CalkinQuotient : Type := (H →L[ℂ] H) ⧸ compactIdeal H

variable [Nontrivial H]

/-- **`Q(H)` is a C-star algebra**, with no hypothesis: the compacts are a
closed star-stable two-sided ideal of `B(H)`, and the quotient of a C-star
algebra by such an ideal is a C-star algebra by
`CStarTensor.instCStarAlgebraQuotient`. -/
def calkinCStarAlgebra : CStarAlgebra (CalkinQuotient H) := inferInstance

/-- **The C-star identity in `Q(H)`**, spelled out: the statement
`Analysis/CStarQuotient` records as its one residual, at the Calkin algebra and
in the root-imported vocabulary. -/
theorem calkin_cstar_identity (x : CalkinQuotient H) :
    ‖star x * x‖ = ‖x‖ * ‖x‖ :=
  CStarRing.norm_star_mul_self

/-- The quotient map `B(H) → Q(H)`, the essential image of an operator. -/
def essential : (H →L[ℂ] H) →+* CalkinQuotient H :=
  Ideal.Quotient.mk (compactIdeal H)

/-- An operator has vanishing essential image exactly when it is compact. -/
theorem essential_eq_zero_iff (T : H →L[ℂ] H) :
    essential H T = 0 ↔ IsCompactOperator T :=
  Ideal.Quotient.eq_zero_iff_mem

end

end CalkinAlgebra
end GroupApproximation
