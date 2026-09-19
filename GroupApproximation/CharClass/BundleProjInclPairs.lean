import GroupApproximation.CharClass.BundleProjOver
import GroupApproximation.CharClass.BundleGysinPieces

/-!
# Complex vector bundles in the projection model, XXXV: the restricted
projectivisation as a map of Gysin pairs

`projInclOn` is a map of pairs for both halves of the Gysin cover, and for the
same reason in each case: **both sets are conditions on the matrix coordinate
alone**, and the inclusion carries the matrix unchanged and moves only the base
point.  `chartOpensSet` is a condition on one entry, `notZeroOpensSet` on the
trace of a block, and neither mentions the base.

A leaf module rather than an addition to either neighbour: `projInclOn` lives in
`BundleProjOver`, which has two consumers, and the two sets live in
`BundleGysinPieces`, which has four, so importing either into the other would
rebuild a chain for two `Iff.rfl`s.

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open scoped Matrix
open GroupApproximation.STW59

namespace Bundle

section ProjInclPairs

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The inclusion is a map of pairs for the complement of the zero section.** -/
theorem projInclOn_mem_notZeroOpensSet_iff (p : Bundle X ι) (U : Set X)
    (w : Proj ((p.restrictTo U).plusOne)) :
    projInclOn p.plusOne U w ∈ notZeroOpensSet p
      ↔ w ∈ notZeroOpensSet (p.restrictTo U) := Iff.rfl

omit [DecidableEq ι] in
/-- **And for the affine chart.**  Note this one needs no decidability: the
chart condition is a single entry, where `zTrace` is the trace of a block and
goes through `blockProj`. -/
theorem projInclOn_mem_chartOpensSet_iff (p : Bundle X ι) (U : Set X)
    (w : Proj ((p.restrictTo U).plusOne)) :
    projInclOn p.plusOne U w ∈ chartOpensSet p
      ↔ w ∈ chartOpensSet (p.restrictTo U) := Iff.rfl

theorem projInclOn_preimage_notZeroOpensSet (p : Bundle X ι) (U : Set X) :
    (projInclOn p.plusOne U) ⁻¹' (notZeroOpensSet p)
      = notZeroOpensSet (p.restrictTo U) := rfl

omit [DecidableEq ι] in
theorem projInclOn_preimage_chartOpensSet (p : Bundle X ι) (U : Set X) :
    (projInclOn p.plusOne U) ⁻¹' (chartOpensSet p)
      = chartOpensSet (p.restrictTo U) := rfl

end ProjInclPairs

end Bundle

end CharClass
end GroupApproximation
