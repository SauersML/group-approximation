import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingUnconditional
import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingStrictness
import GroupApproximation.Manuscript.OneSidedMFRadical.UnitGroupRankDescent
import GroupApproximation.PropertyT.IntegralColumnPlaneClosure
import GroupApproximation.Meta.AxiomGuard

/-!
# The printed clauses in every characteristic, with nothing assumed

`FullDefectRingUnconditional`, `FullDefectRingStrictness`,
`FullDefectRingRankTwo` and `UnitGroupRankDescent` each state their printed
clause twice: once over a coefficient ring of prime characteristic, where the
repository's own Ershov--Jaikin-Zapirain theorem applies and nothing is
assumed, and once in general characteristic with the coefficient-general
statement `FinitelyGeneratedRingGeneralRankElementaryPropertyT` as the single
leading hypothesis.

That hypothesis is no longer a hypothesis.
`PropertyT/IntegralColumnPlaneClosure` proves it:
`IntegralColumnPlaneClosure.finitelyGeneratedRingGeneralRankElementaryPropertyT`,
property `(T)` for `EL_n` of every finitely generated unital associative ring
and every `n ≥ 3`, in every characteristic.  So this module supplies it once
and restates each printed clause with no hypothesis at all and no restriction
on the characteristic of the coefficient ring.

Nothing is proved here.  Every declaration is an existing `…FromEJZ` theorem
with its one argument supplied, and the reason to name the results separately
is that a badge should point at a declaration whose elaborated type is the
printed sentence and nothing else.  The `…FromEJZ` forms are left in place: a
reader who wants to see which printed clause depends on which input should
still be able to read the dependence off the statement.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace FullDefectRingEJZUnconditional

open GroupApproximation.Manuscript.OneSidedMFRadical

/-- The coefficient-general Ershov--Jaikin-Zapirain input, as a theorem. -/
theorem ejz : FinitelyGeneratedRingGeneralRankElementaryPropertyT :=
  IntegralColumnPlaneClosure.finitelyGeneratedRingGeneralRankElementaryPropertyT

/-! ## `thm:full-defect-ring` and the corollaries of `FullDefectRingUnconditional` -/

/-- **`thm:full-defect-ring` exactly as printed**, in every characteristic,
with nothing assumed. -/
theorem manuscriptFullComplementaryIdempotentsAllCharacteristics :
    FullDefectRing.PrintedFullComplementaryIdempotents :=
  FullDefectRing.manuscriptFullComplementaryIdempotentsFromEJZ ejz

/-- **`cor:simple-infinite-ring`, first sentence**, in every characteristic,
with nothing assumed. -/
theorem manuscriptSimpleInfiniteRingAllCharacteristics :
    FullDefectRing.PrintedSimpleInfiniteRing :=
  FullDefectRing.manuscriptSimpleInfiniteRingFromEJZ ejz

/-- **`cor:simple-infinite-ring`, second sentence**, in every characteristic,
with nothing assumed. -/
theorem manuscriptLeavittAlgebraFullDefectAllCharacteristics :
    FullDefectRing.PrintedLeavittAlgebraFullDefect :=
  FullDefectRing.manuscriptLeavittAlgebraFullDefectFromEJZ ejz

/-- **`cor:one-sided-ring-maximal`, second sentence**, in every
characteristic, with nothing assumed. -/
theorem manuscriptOneSidedRingMaximalReducedCStarAllCharacteristics :
    FullDefectRing.PrintedOneSidedRingMaximalReducedCStar :=
  FullDefectRing.manuscriptOneSidedRingMaximalReducedCStarFromEJZ ejz

/-- **All four printed clauses at once**, in every characteristic, with
nothing assumed. -/
theorem manuscriptPrintedFullDefectRingProgrammeAllCharacteristics :
    FullDefectRing.PrintedFullDefectRingProgramme :=
  FullDefectRing.manuscriptPrintedFullDefectRingProgrammeFromEJZ ejz

/-- **`EL_n(R)` is not MF**, in every characteristic, with nothing assumed. -/
theorem manuscriptElementaryGroupNotMFAllCharacteristics :
    FullDefectRing.PrintedElementaryGroupNotMF :=
  FullDefectRing.manuscriptElementaryGroupNotMFFromEJZ ejz

/-! ## The proper isometry of `cor:one-sided-ring-maximal` -/

/-- **`cor:one-sided-ring-maximal`, first sentence**, in every
characteristic, with nothing assumed. -/
theorem manuscriptOneSidedRingMaximalIsometryAllCharacteristics :
    FullDefectRing.PrintedOneSidedRingMaximalIsometry :=
  FullDefectRing.manuscriptOneSidedRingMaximalIsometryFromEJZ ejz

/-! ## The rank-two descent and the unit group -/

/-- **`thm:full-defect-ring` at `n ≥ 2`**, in every characteristic, with
nothing assumed. -/
theorem manuscriptFullComplementaryIdempotentsRankTwoAllCharacteristics :
    FullDefectRankTwo.PrintedFullComplementaryIdempotentsRankTwo :=
  FullDefectRankTwo.manuscriptFullComplementaryIdempotentsRankTwoFromEJZ ejz

/-- **The unit group `Rˣ` is not MF**, in every characteristic, with nothing
assumed. -/
theorem manuscriptUnitGroupNotMFAllCharacteristics :
    FullDefectRankTwo.PrintedUnitGroupNotMF :=
  FullDefectRankTwo.manuscriptUnitGroupNotMFFromEJZ ejz

end FullDefectRingEJZUnconditional
end OneSidedMFRadical
end Manuscript
end GroupApproximation

open GroupApproximation
open GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingEJZUnconditional

#audit_closed_axioms ejz
#audit_closed_axioms manuscriptFullComplementaryIdempotentsAllCharacteristics
#audit_closed_axioms manuscriptSimpleInfiniteRingAllCharacteristics
#audit_closed_axioms manuscriptLeavittAlgebraFullDefectAllCharacteristics
#audit_closed_axioms
  manuscriptOneSidedRingMaximalReducedCStarAllCharacteristics
#audit_closed_axioms manuscriptPrintedFullDefectRingProgrammeAllCharacteristics
#audit_closed_axioms manuscriptElementaryGroupNotMFAllCharacteristics
#audit_closed_axioms manuscriptOneSidedRingMaximalIsometryAllCharacteristics
#audit_closed_axioms
  manuscriptFullComplementaryIdempotentsRankTwoAllCharacteristics
#audit_closed_axioms manuscriptUnitGroupNotMFAllCharacteristics
