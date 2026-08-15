import GroupApproximation.Analysis.ReducedGroupCStarMFObstruction
import GroupApproximation.Analysis.UniversalKazhdanCStarConsequences
import GroupApproximation.Sofic.MFDefinitions
import GroupApproximation.Sofic.TorsionFreeFullMFRadical

/-!
# Reduced group C-star consequences of the routed full-radical group

For every proof-carrying routed quotient, the protected element belongs to the
full norm-MF residual.  Therefore no faithful reduced-group-C-star embedding
can have an injective unitary restriction into a matrix ultraproduct.  On the
other hand, the canonical faithful trace proves finiteness of every finite
matrix amplification.

The genuine MF C-star-algebra predicate is now available, so the
unitary-restriction obstruction is also packaged as
`not_isReducedGroupCStarMF`.  This file says nothing about the full group
C-star algebra.

The manuscript's further claims of C-star simplicity, unique trace, and stable
rank one depend on external theorems about acylindrically hyperbolic groups.
Those notions and the required theorems are not in the present library, so
they are intentionally not represented by opaque assumptions here.
-/

namespace GroupApproximation

open ReducedGroupCStarTrace

noncomputable section

universe u

namespace DefectRoutingData

variable {P : Type} {E : Type u} [Group P] [Group E]
    {D : FournierFacioDefectData P E}
    (R : DefectRoutingData.{u} D)

local instance routedCStarQuotientGroup : Group R.Quotient := R.groupQuotient

/-- The protected element of the routed quotient is a nontrivial element of
its norm-MF residual. -/
theorem protected_mem_normMFResidual :
    R.quotient D.s ∈ normMFResidual R.Quotient := by
  rw [R.normMFResidual_eq_top]
  exact Subgroup.mem_top _

/-- No faithful reduced-group-C-star matrix-ultraproduct embedding can have
an injective restriction to the canonical group unitaries. -/
theorem no_faithfulReducedCoronaUnitaryRestriction :
    IsEmpty (FaithfulReducedCoronaUnitaryRestriction R.Quotient) :=
  by
    letI : Nontrivial R.Quotient := R.quotientNontrivial
    exact no_faithfulReducedCoronaUnitaryRestriction_of_residual_eq_top
      R.Quotient R.normMFResidual_eq_top

/-- The concrete reduced group C-star algebra of a routed full-radical group
is not an MF C-star algebra. -/
theorem not_isReducedGroupCStarMF :
    ¬ IsReducedGroupCStarMF R.Quotient := by
  letI : Countable R.Quotient := R.quotientCountable
  intro hred
  exact R.not_isOperatorMF hred.isGroupTheoreticMF

/-- Every isometry in every nonempty finite matrix amplification of the
reduced group C-star algebra is unitary.  This is the operational stable-
finiteness statement furnished by the canonical faithful trace. -/
theorem reduced_matrix_isometry_is_unitary
    (n : Type*) [Fintype n] [DecidableEq n] (hn : Nonempty n)
    {v : CStarMatrix n n (ReducedGroupCStar R.Quotient)}
    (hv : star v * v = 1) : v * star v = 1 :=
  reduced_matrix_mul_star_eq_one_of_star_mul_eq_one R.Quotient n hn hv

/-- In particular, the reduced group C-star algebra contains no proper
isometry. -/
theorem reduced_isometry_is_unitary
    {v : ReducedGroupCStar R.Quotient} (hv : star v * v = 1) :
    v * star v = 1 :=
  reduced_mul_star_eq_one_of_star_mul_eq_one R.Quotient hv

end DefectRoutingData

end

end GroupApproximation
