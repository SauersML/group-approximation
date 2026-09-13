import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerTwoGonEitherFollowsCopy
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketRegionInnerFollows
import GroupApproximation.Meta.AxiomGuard

/-!
# The inner-following pocket region, discharged

`PocketRegionOfInnerFollowsStatement` (`Estimating/OsinAppendixEulerTwoGonEitherFollows`) names the
pocket region of a noncrossing walk whose inner cycle follows its boundary, the lake of
Configuration B.  Lane `ms-torsionfree` builds it
(`PocketRegion.ofNoncrossingClosedWalkInner`, `Estimating/OsinPocketRegionInnerFollows`).  Its outer
region comes from the Euler equality of the reversed walk.

* `pocketRegionOfInnerFollowsStatement`: the named Prop holds.
* `twoGonHoldsInput_of_eitherFollowsPocket`: C6′ from `TwoGonEitherFollowsPocketInput` alone.
* `twoGonHoldsInput_of_eitherFollowsCopyPocket`: C6′ from `TwoGonEitherFollowsCopyInput` alone.

## Manuscript status

Infrastructure for `thm:hull` (through Osin's Lemma 9.7(a)); certifies no printed sentence on its
own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

/-- **The pocket region of a noncrossing walk whose inner cycle follows** is
`PocketRegion.ofNoncrossingClosedWalkInner`: its faces are the side of the walk, and its inverse
complement cycle is the walk. -/
theorem pocketRegionOfInnerFollowsStatement : PocketRegionOfInnerFollowsStatement.{u, w, v} :=
  fun hw hout hin =>
    ⟨PocketRegion.ofNoncrossingClosedWalkInner hw hout hin,
      PocketRegion.ofNoncrossingClosedWalkInner_faces hw hout hin,
      PocketRegion.ofNoncrossingClosedWalkInner_invDarts_outer hw hout hin⟩

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **C6′ from a noncrossing pocket walk with either boundary cycle following**, with the
inner-following pocket region discharged. -/
theorem twoGonHoldsInput_of_eitherFollowsPocket {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    {W : Set (List (RelLetter G Lambda))}
    (hpocket : TwoGonEitherFollowsPocketInput.{u, w, v} D lambda c eps W) :
    TwoGonHoldsInput.{u, w, v} D lambda c eps W :=
  twoGonHoldsInput_of_eitherFollows pocketRegionOfInnerFollowsStatement hpocket

/-- **C6′ from a noncrossing pocket on another distinguished family**, with the inner-following
pocket region discharged. -/
theorem twoGonHoldsInput_of_eitherFollowsCopyPocket {D : RelGenSet G Lambda} {lambda c : ℝ}
    {eps : ℕ} {W : Set (List (RelLetter G Lambda))}
    (hcopy : TwoGonEitherFollowsCopyInput.{u, w, v} D lambda c eps W) :
    TwoGonHoldsInput.{u, w, v} D lambda c eps W :=
  twoGonHoldsInput_of_eitherFollowsCopy pocketRegionOfInnerFollowsStatement hcopy

end GroupApproximation.GGT.VanKampen

#audit_closed_axioms GroupApproximation.GGT.VanKampen.pocketRegionOfInnerFollowsStatement
#audit_axioms GroupApproximation.GGT.VanKampen.twoGonHoldsInput_of_eitherFollowsPocket
#audit_axioms GroupApproximation.GGT.VanKampen.twoGonHoldsInput_of_eitherFollowsCopyPocket
