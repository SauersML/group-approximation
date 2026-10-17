import GroupApproximation.Sofic.Hyperlinear
import GroupApproximation.Sofic.NormMFResidualDetector
import GroupApproximation.Sofic.SoficInvisible
import GroupApproximation.Sofic.SoficTransfer

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

namespace GroupApproximation

open scoped commutatorElement

universe u

variable {G H : Type u} [Group G] [Group H]

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
theorem hyperlinear_range_and_failureOfSoficity_of_soficInvisible
    (hH : IsHyperlinear H) {x : G} (hx : SoficInvisible x)
    (rho : G →* H) (hdetect : rho x ≠ 1) :
    IsHyperlinear rho.range ∧ ¬ IsSofic rho.range := by
  constructor
  · exact isHyperlinear_of_injective rho.range.subtype
      Subtype.val_injective hH
  · exact not_isSofic_range_of_soficInvisible hx rho hdetect

/-- One detected element which is both sofic-invisible and MF-invisible
produces a range which is simultaneously hyperlinear, nonsofic, and non-MF.
This is the strongest portable form of the marked-wall endpoint. -/
theorem hyperlinear_range_notSofic_notMF_of_jointInvisible
    [Countable G] (hH : IsHyperlinear H) {x : G}
    (hsofic : SoficInvisible x) (hmf : NormMFInvisible x)
    (rho : G →* H) (hdetect : rho x ≠ 1) :
    IsHyperlinear rho.range ∧ ¬ IsSofic rho.range ∧ ¬ IsWeakMF rho.range := by
  refine ⟨isHyperlinear_of_injective rho.range.subtype Subtype.val_injective hH,
    not_isSofic_range_of_soficInvisible hsofic rho hdetect, ?_⟩
  exact not_isWeakMF_range_of_normMFInvisible hmf rho hdetect

/-- Existential form of the one-detector criterion: a single hyperlinear
representation seeing a single sofic-residual element produces a
counterexample to `hyperlinear ⇒ sofic`. -/
theorem exists_hyperlinear_failureOfSoficity_of_soficInvisible_detector
    (hH : IsHyperlinear H) {x : G} (hx : SoficInvisible x)
    (rho : G →* H) (hdetect : rho x ≠ 1) :
    ∃ (Q : Type u) (_ : Group Q), IsHyperlinear Q ∧ ¬ IsSofic Q := by
  refine ⟨rho.range, inferInstance, ?_⟩
  exact hyperlinear_range_and_failureOfSoficity_of_soficInvisible hH hx rho hdetect

end GroupApproximation
