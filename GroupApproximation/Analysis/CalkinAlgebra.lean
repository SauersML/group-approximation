import GroupApproximation.Analysis.CalkinCompactIdeal
import GroupApproximation.Analysis.CStarQuotient

/-!
# The Calkin algebra

`Q(H) = B(H) / K(H)`, assembled from the two pieces built separately:
`Analysis/CalkinCompactIdeal` supplies the closed two-sided ideal of compact
operators, and `Analysis/CStarQuotient` supplies the quotient's ring, norm,
star and complex structure for any closed star-closed two-sided ideal of a
C-star algebra.

The type is opaque, and the instances are installed on it by `unfold` — the
pattern `Analysis/NormMatrixCorona` uses for `NormMatrixCStarCorona`, so that
downstream typeclass search never unfolds the ideal quotient.

## What is unconditional and what is not

Unconditional: the `NormedRing`, `CompleteSpace` and `NormedAlgebra ℂ`
structure.  Nothing about adjoints or the C-star identity enters those.

Conditional on Schauder (`CalkinAlgebra.CompactStarClosedStatement`, that the
adjoint of a compact operator is compact — not in Mathlib): the `Star`,
`StarRing`, `NormedStarGroup` and `StarModule` structure.  These are `def`s
taking `CStarQuotient.IsStarIdeal (compactIdeal H)` as an instance argument, so
a consumer who has Schauder installs it once with `letI` and gets all four.

Still owed after that: the C-star identity,
`CStarQuotient.CStarIdentityStatement`.  Only with it is `Q(H)` a C-star
algebra rather than a normed star algebra, and only then can Arveson,
Stinespring and Voiculescu be stated against it.

Both of those are now discharged, and neither the way this module expected.
Schauder is `Analysis/CalkinSchauderProof.compactStarClosed`, installed as an
instance in `Analysis/CalkinAlgebraStar`.  The C-star identity is not owed at
all: `Analysis/CStarIdealApproximateUnit`, root-imported, proves it for every
closed star-stable two-sided ideal, and `Analysis/CalkinCStarAlgebra` builds
`Q(H)` on that instead of on the hand-built quotient below.

This module is in the root import list.  It was authored while builds were
suspended and has not been elaborated, so the first build after the suspension
is where its names are checked.
-/

namespace GroupApproximation
namespace CalkinAlgebra

noncomputable section

variable (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The ideal of compacts is closed, in the instance form the quotient's
normed structure consumes. -/
instance compactIdeal_isClosed :
    IsClosed ((compactIdeal H : Ideal (H →L[ℂ] H)) : Set (H →L[ℂ] H)) :=
  isClosed_compactIdeal H

/-- **The Calkin algebra** `Q(H) = B(H) / K(H)`, behind an opaque boundary. -/
def Calkin : Type := (H →L[ℂ] H) ⧸ compactIdeal H

/-- The essential-norm ring structure. -/
instance calkinNormedRing : NormedRing (Calkin H) := by
  unfold Calkin
  exact CStarQuotient.normedRing (H →L[ℂ] H) (compactIdeal H)

instance calkinCompleteSpace : CompleteSpace (Calkin H) := by
  unfold Calkin
  exact CStarQuotient.completeSpace (H →L[ℂ] H) (compactIdeal H)

instance calkinNormedAlgebra : NormedAlgebra ℂ (Calkin H) := by
  unfold Calkin
  exact CStarQuotient.normedAlgebra (H →L[ℂ] H) (compactIdeal H)

/-- The quotient map `B(H) → Q(H)`, the *essential* image of an operator. -/
def mk : (H →L[ℂ] H) → Calkin H := Ideal.Quotient.mk (compactIdeal H)

/-! ## The star, on Schauder -/

/-- Schauder in the form the quotient's star consumes.  Supplying this is
exactly supplying `CompactStarClosedStatement`. -/
theorem isStarIdeal_of_compactStarClosed (h : CompactStarClosedStatement) :
    CStarQuotient.IsStarIdeal (compactIdeal H) :=
  ⟨fun ha ↦ h H _ ha⟩

variable [CStarQuotient.IsStarIdeal (compactIdeal H)]

instance calkinStar : Star (Calkin H) := by
  unfold Calkin
  exact CStarQuotient.starInstance (H →L[ℂ] H) (compactIdeal H)

instance calkinStarRing : StarRing (Calkin H) := by
  unfold Calkin
  exact CStarQuotient.starRing (H →L[ℂ] H) (compactIdeal H)

instance calkinStarModule : StarModule ℂ (Calkin H) := by
  unfold Calkin
  exact CStarQuotient.starModule (H →L[ℂ] H) (compactIdeal H)

/-! ## The last residual

`Q(H)` is a normed star algebra above.  It is a *C-star* algebra exactly when
`CStarQuotient.CStarIdentityStatement` holds, and that statement is now
writable because the norm and the star exist.  Until it is proved, Arveson,
Stinespring and Voiculescu cannot be stated against `Q(H)` as maps of C-star
algebras, and `Analysis/ShulmanFillTheorem13`'s three atoms stay in prose. -/

end

end CalkinAlgebra
end GroupApproximation
