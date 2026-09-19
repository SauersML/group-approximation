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

/-! ## The chart inclusion, and its naturality -/

/-- **The total space, included into the projectivisation as the affine chart.**
This is the single map that `bridgeChart` is a `relPullback` along, once its two
factors are composed: identify the total space with the chart, then include the
chart. -/
noncomputable def bridgeChartIncl (p : Bundle X ι) :
    C(Bundle.Total p, Bundle.Proj p.plusOne) where
  toFun v := ((Bundle.chartOpensHomeoTotal p).symm v : Bundle.Proj p.plusOne)
  continuous_toFun :=
    continuous_subtype_val.comp (Bundle.chartOpensHomeoTotal p).symm.continuous

@[simp] theorem bridgeChartIncl_apply (p : Bundle X ι) (v : Bundle.Total p) :
    bridgeChartIncl p v = ((Bundle.chartOpensHomeoTotal p).symm v : Bundle.Proj p.plusOne) :=
  rfl

/-- **The chart inclusion is natural in the base.**  The square of
`chartOpensHomeoTotal_natural`, read through the inverse and forgotten into the
projectivisation.  This is the space-level content of the first two bridge steps'
naturality; the cohomological statement is `relPullback_comp` on top of it. -/
theorem bridgeChartIncl_natural (p : Bundle X ι) (U : Set X)
    (v : Bundle.Total (p.restrictTo U)) :
    bridgeChartIncl p (Bundle.totalInclOn p U v)
      = Bundle.projInclOn p.plusOne U (bridgeChartIncl (p.restrictTo U) v) := by
  have h := chartOpensHomeoTotal_natural p U
    ((Bundle.chartOpensHomeoTotal (p.restrictTo U)).symm v)
  rw [(Bundle.chartOpensHomeoTotal (p.restrictTo U)).apply_symm_apply] at h
  show ((Bundle.chartOpensHomeoTotal p).symm (Bundle.totalInclOn p U v) :
      Bundle.Proj p.plusOne) = _
  rw [h, (Bundle.chartOpensHomeoTotal p).symm_apply_apply]
  rfl

/-! Printed on every build. -/

#print axioms bridgeChartIncl_natural

end

end GroupApproximation.CharClass
