import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaCompatibleCorner
import GroupApproximation.Meta.AxiomGuard

/-!
# Ueda corners in compatible representation coordinates

Every same-universe compatible representation of the two matrix factors
contains the Ueda corner, and the corner carries a covariant representation of
the HNN datum.  This coordinate construction avoids the universe increase of
the two concrete universal products.

The corner itself is built once, in `HNNPermanenceUedaCompatibleCorner`, over
an abstract target algebra `E` with the two factor maps and their
compatibility as explicit arguments.  Doing it there rather than here is not a
matter of taste: over `Q.carrier` every instance step has to be found through
the `CStarAmalgamRepresentation` projection rather than through a plain
`[CStarAlgebra E]` binder, and the corner's own `unitary (CStarCorner …)` then
exhausts the instance-synthesis budget.  So this file only instantiates the
abstract corner at a coordinate, which is one such unification instead of one
per lemma.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]
variable (data : CoronaConjugator G S T phi A X)

/-- A compatible representation of the two matrix factors of the Ueda
amalgam. -/
abbrev CoordinateAmalgamRepresentation := CStarAmalgamRepresentation
  (amalgamLeftInclusion data) (amalgamRightInclusion data)

/-- The Ueda corner of a compatible amalgam coordinate, as a covariant
representation of the HNN datum.  A coordinate `Q` supplies exactly the three
arguments the abstract corner asks for: its two factor maps and the
compatibility between them. -/
def coordinateHNNRepresentation (Q : CoordinateAmalgamRepresentation data) :
    CStarHNNRepresentation
      (sourceEdgeAlgebra data) (targetEdgeAlgebra data) (edgeIsomorphism data) :=
  compatibleCornerHNNRepresentation data Q.left Q.right Q.compatible

/-- Closed endpoint: every compatible amalgam coordinate contains the
same-universe Ueda HNN corner. -/
def CompatibleCoordinateCarriesHNNCorner : Prop :=
  ∀ {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
    {A : Type} [CStarAlgebra A]
    {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]
    (data : CoronaConjugator G S T phi A X)
    (_Q : CoordinateAmalgamRepresentation data),
      Nonempty (CStarHNNRepresentation
        (sourceEdgeAlgebra data) (targetEdgeAlgebra data)
        (edgeIsomorphism data))

theorem compatibleCoordinateCarriesHNNCorner :
    CompatibleCoordinateCarriesHNNCorner := by
  intro G _ S T phi A _ X _ data Q
  exact ⟨coordinateHNNRepresentation data Q⟩

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation

#audit_closed_axioms GroupApproximation.Manuscript.MFRecognition.HNNPermanence.compatibleCoordinateCarriesHNNCorner
