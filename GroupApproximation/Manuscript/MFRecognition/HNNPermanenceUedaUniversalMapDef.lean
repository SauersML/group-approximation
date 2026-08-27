import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaCornerCovariance
import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaCornerNontrivial
import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUniversalMapping

/-! # The universal HNN map into Ueda's corner -/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- Printed Step 1: *"the covariant pair `(d ↦ diag(d,0), e₁₂f₂₁)` in `ePe`
induces an injective `*`-homomorphism `U → ePe`"*.

This is a named input rather than a construction, for a reason that is about
universes and not about the mathematics.  `UniversalCStarHNN` is a subalgebra
of `lp (fun R : CStarHNNRepresentation … ↦ R.carrier) ∞`, the bounded product
over the *same-universe* covariant representations, so with the entry algebras
at `Type u` it lands in `Type (u+1)` while
`universalCStarHNN_existsUnique_lift` reaches only `Type u` codomains: its
existence half factors through `CStarHNNRepresentation.ofCovariantPair`, whose
`carrier` field is `Type u` by declaration.  Ueda's corner sits inside
`UniversalCStarAmalgam`, which is `Type (u+1)` for the same `lp` reason, so it
is exactly a codomain the lift cannot see.  For such a codomain there is no
coordinate to evaluate at, and the `lp` norm is a supremum over the small
representations only, so even boundedness of the induced map would need its own
argument; `Shrink`/`ULift` would need `Small.{u}` of the corner, which is not
available.

Discharging this means widening `CStarHNNRepresentation.carrier` to
`Type (u+1)`, which pushes `UniversalCStarHNN` to `Type (u+2)` and touches
every file naming that structure — including the chain carrying the landed
HNN permanence theorem.  That is a universe refactor of landed code and is
tracked as its own lane. -/
def UedaCornerMapStatement : Prop :=
  ∀ {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
    {A : Type} [CStarAlgebra A] {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]
    (data : CoronaConjugator G S T phi A X),
    ∃ f : universalHNN data →⋆ₐ[ℂ]
        CStarCorner (cornerUnit data) (cornerUnit_star data)
          (cornerUnit_mul data),
      (∀ d : baseAlgebra data,
          f (universalBase data d) = cornerBaseMap data d) ∧
        f (universalStable data : universalHNN data) =
          ↑(cornerStableUnitary data) ∧
        Function.Injective f

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- Printed: *"the induced map `U → ePe`"*. -/
def uedaCornerMap (hUeda : UedaCornerMapStatement)
    (data : CoronaConjugator G S T phi A X) :
    universalHNN data →⋆ₐ[ℂ]
      CStarCorner (cornerUnit data) (cornerUnit_star data)
        (cornerUnit_mul data) :=
  (hUeda data).choose

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
