import GroupApproximation.CharClass.BundleProjInclPairs
import GroupApproximation.CharClass.BundleChartTotal
import GroupApproximation.CharClass.BundleTotalOver

/-!
# The chart identification is natural in the base

Lane `cc-thom` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

`ThomBridgeTotal` records that `bridgeTotal` was published as a bare isomorphism
with no naturality of any kind, and that both of this lane's remaining
obligations are stuck behind that.  This file is the first piece of the missing
layer: the **space-level** square, from which the cohomological one follows by
`relPullback_comp`, since every step of the bridge is a `relPullback` or the
inverse of one.

The square says that identifying the affine chart with the total space commutes
with restricting the base.  It holds for the reason every comparison in this
layer has held: `cc-bundle`'s inclusions move the **base point** and carry the
padded matrix unchanged, while `chartOpensHomeoTotal` acts on the **matrix** and
carries the base point along.  The two touch different coordinates, so they
commute definitionally.

That pattern has now predicted five statements correctly, four of `cc-bundle`'s
and this one, so it is worth stating as the thing to reach for rather than
rediscovering it each time.

## Main declaration

* `chartOpensHomeoTotal_natural` — the square.
-/

namespace GroupApproximation.CharClass

noncomputable section

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι]

/-- **Identifying the chart with the total space commutes with restricting the
base.**  The inclusions move the base point and leave the matrix alone; the
identification moves the matrix and carries the base point along. -/
theorem chartOpensHomeoTotal_natural (p : Bundle X ι) (U : Set X)
    (w : ↥(Bundle.chartOpensSet (p.restrictTo U))) :
    Bundle.totalInclOn p U (Bundle.chartOpensHomeoTotal (p.restrictTo U) w)
      = Bundle.chartOpensHomeoTotal p
          ⟨Bundle.projInclOn p.plusOne U (w : Bundle.Proj ((p.restrictTo U).plusOne)),
            (Bundle.projInclOn_mem_chartOpensSet_iff p U _).mpr w.2⟩ := rfl

/-! Printed on every build. -/

#print axioms chartOpensHomeoTotal_natural

end

end GroupApproximation.CharClass
