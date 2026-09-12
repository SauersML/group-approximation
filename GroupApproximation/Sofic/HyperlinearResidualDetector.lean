import GroupApproximation.Sofic.Hyperlinear
import GroupApproximation.Sofic.NormMFResidualDetector
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

/-- An element belongs to the sofic residual: every homomorphism to a sofic
group kills it.  Targets are allowed to be arbitrary groups in the ambient
universe; no finiteness or injectivity condition is imposed. -/
def SoficInvisible (x : G) : Prop :=
  ∀ (S : Type u) (_ : Group S), IsSofic S → ∀ f : G →* S, f x = 1

/-- The identity is invisible in every target. -/
theorem soficInvisible_one : SoficInvisible (1 : G) := by
  intro S _ _ f
  exact map_one f

/-- Sofic invisibility is closed under taking a commutator with an arbitrary
group element.  This is the radical-propagation step used by the Kun--Thom
Clifford phase: once `r` is killed by every sofic target, so is `⁅k,r⁆`. -/
theorem SoficInvisible.commutator_left (k r : G) (hr : SoficInvisible r) :
    SoficInvisible ⁅k, r⁆ := by
  intro S _ hS f
  rw [map_commutatorElement, hr S inferInstance hS f]
  simp [commutatorElement_def]

/-- The elements killed by every homomorphism to a sofic group form a
subgroup.  This is the *sofic residual* (as opposed to a largest normal sofic
subgroup, which is a different construction). -/
def soficResidual (G : Type u) [Group G] : Subgroup G where
  carrier := {x | SoficInvisible x}
  one_mem' := soficInvisible_one
  mul_mem' := by
    intro x y hx hy S _ hS f
    rw [map_mul, hx S inferInstance hS f, hy S inferInstance hS f, one_mul]
  inv_mem' := by
    intro x hx S _ hS f
    rw [map_inv, hx S inferInstance hS f, inv_one]

@[simp] theorem mem_soficResidual_iff {x : G} :
    x ∈ soficResidual G ↔ SoficInvisible x :=
  Iff.rfl

/-- Every map to a sofic group kills the full sofic residual. -/
theorem map_eq_one_of_mem_soficResidual {S : Type u} [Group S]
    (hS : IsSofic S) (f : G →* S) {x : G} (hx : x ∈ soficResidual G) :
    f x = 1 :=
  hx S inferInstance hS f

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
