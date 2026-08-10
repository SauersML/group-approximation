import NonsoficGroupsExist.Sofic.Hyperlinear
import NonsoficGroupsExist.Sofic.SoficTransfer

/-!
# One detected sofic-residual element suffices

This file isolates the group-theoretic core of the one-trace strategy.  An
element is `SoficInvisible` when every homomorphism from its group to a sofic
group kills it.  If one homomorphism into a hyperlinear group detects that
element, its range is itself hyperlinear and cannot be sofic.

The conclusion concerns the range, not the whole target.  Thus neither
faithfulness of the detecting homomorphism nor hyperlinearity of a quotient is
needed.
-/

namespace NonsoficGroupsExist

universe u

variable {G H : Type u} [Group G] [Group H]

/-- An element belongs to the sofic residual: every homomorphism to a sofic
group kills it.  Targets are allowed to be arbitrary groups in the ambient
universe; no finiteness or injectivity condition is imposed. -/
def SoficInvisible (x : G) : Prop :=
  ∀ (S : Type u) (_ : Group S), IsSofic S → ∀ f : G →* S, f x = 1

/-- The identity is invisible in every target. -/
theorem soficInvisible_one : SoficInvisible (1 : G) := by
  intro S _ _ f
  exact map_one f

/-- If a sofic-residual element survives under a homomorphism, the range of
that homomorphism is not sofic. -/
theorem not_isSofic_range_of_soficInvisible
    {x : G} (hx : SoficInvisible x) (rho : G →* H) (hdetect : rho x ≠ 1) :
    ¬ IsSofic rho.range := by
  intro hrange
  have hkilled : rho.rangeRestrict x = 1 :=
    hx rho.range inferInstance hrange rho.rangeRestrict
  apply hdetect
  simpa using congrArg Subtype.val hkilled

/-- **One-detector criterion.**  If a homomorphism to a hyperlinear group
detects one element of the sofic residual, its range is a hyperlinear
nonsofic group. -/
theorem hyperlinear_nonsofic_range_of_soficInvisible
    (hH : IsHyperlinear H) {x : G} (hx : SoficInvisible x)
    (rho : G →* H) (hdetect : rho x ≠ 1) :
    IsHyperlinear rho.range ∧ ¬ IsSofic rho.range := by
  constructor
  · exact isHyperlinear_of_injective rho.range.subtype
      Subtype.val_injective hH
  · exact not_isSofic_range_of_soficInvisible hx rho hdetect

/-- Existential form of the one-detector criterion: a single hyperlinear
representation seeing a single sofic-residual element produces a
counterexample to `hyperlinear ⇒ sofic`. -/
theorem exists_hyperlinear_nonsofic_of_soficInvisible_detector
    (hH : IsHyperlinear H) {x : G} (hx : SoficInvisible x)
    (rho : G →* H) (hdetect : rho x ≠ 1) :
    ∃ (Q : Type u) (_ : Group Q), IsHyperlinear Q ∧ ¬ IsSofic Q := by
  refine ⟨rho.range, inferInstance, ?_⟩
  exact hyperlinear_nonsofic_range_of_soficInvisible hH hx rho hdetect

end NonsoficGroupsExist
