import GroupApproximation.Algebra.FiniteResidual
import GroupApproximation.Higman.PairedReturnFirstRangeVirtualRetract

/-!
# Profinite promotion of the paired first-coordinate range

The first-coordinate range is a closed retract of the even-parity subgroup,
and that subgroup has index two in `F₃`.  These are the two inputs for the
finite-index promotion step from the intrinsic graph to the full paired
ambient.
-/

namespace GroupApproximation
namespace Higman
namespace PairedReturnFirstRangeProfinitePromotion

open Conj
open PairedReturnEdgeProfinite
open PairedReturnFirstRangeVirtualRetract

/-- The even-parity subgroup has finite index, witnessed by the action on
the two Boolean states. -/
instance even_finiteIndex : Even.FiniteIndex := by
  rw [Even]
  exact finiteIndex_comap_of_normal stateAct (⊥ : Subgroup (Equiv.Perm Bool))

/-- Inside the even-parity subgroup, the first-coordinate range is
profinitely closed. -/
theorem profiniteClosure_firstRange_in_even :
    profiniteClosure firstRangeToEven.range = firstRangeToEven.range := by
  letI : Group.ResiduallyFinite Even := inferInstance
  exact profiniteClosure_range_eq_range_of_retraction
    firstRangeToEven evenToFirstRange
      evenToFirstRange_comp_firstRangeToEven

end PairedReturnFirstRangeProfinitePromotion
end Higman
end GroupApproximation
