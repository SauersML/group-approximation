import GroupApproximation.CharClass.LerayHirschChartBundle
import GroupApproximation.CharClass.LerayHirschDiagCover

/-!
# Leray–Hirsch for a projectivised sum, over the class identification

Everything above the class is now assembled.  The diagonal sets cover the base and
are exactly the charts the trivialisation is stated over, the chart step turns each
of them into the local statement, and the cover induction glues them.  What is left
is one family of hypotheses, the identification over each chart of the tautological
class with the pulled-back generator, which cannot even be *stated* until a bundle
can be reindexed from a sum-with-a-point to a standard finite index.

So the class enters exactly once, as a parameter, and everything around it is
green.  When the reindexing lands, the identification slots in and this becomes
Leray–Hirsch for the projectivised sum with no hypotheses.

No compactness of the base is used, because the diagonal cover is finite for free.

## Main declarations

* `restrictTo_trace`, `restrictTo_diag` — the two chart hypotheses, discharged.
* `lerayHirschGraded_plusOne` — **Leray–Hirsch for `P(p ⊕ 1)`**, over the class
  identification.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory TopologicalSpace

noncomputable section

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Trace one survives restriction, on the nose. -/
theorem restrictTo_trace (p : Bundle X ι) (hp : ∀ x, (p x).trace = 1) (A : Set X)
    (x : ↥A) : ((p.restrictTo A) x).trace = 1 := hp (x : X)

/-- On a diagonal chart, cut down by anything, the diagonal entry is nonzero. -/
theorem restrictTo_diag (p : Bundle X ι) (i : ι) (W : Opens (TopCat.of X))
    (x : ↥((diagOpen p i ⊓ W : Opens (TopCat.of X)) : Set X)) :
    (p.restrictTo ((diagOpen p i ⊓ W : Opens (TopCat.of X)) : Set X)) x i i ≠ 0 :=
  x.2.1

/-- **Leray–Hirsch for the projectivised sum of a projection-valued bundle**, over
the identification of the tautological class on each chart.  The identification is
the only hypothesis, and it is the only thing not yet statable. -/
theorem lerayHirschGraded_plusOne [Nonempty ι] (p : Bundle X ι)
    (hp : ∀ x, (p x).trace = 1)
    (ξ : Hmod2 (TopCat.of (Bundle.Proj p.plusOne)) 2)
    (hξ : ∀ (i : ι) (W : Opens (TopCat.of X)),
      pull (chartProdIso p (diagOpen p i ⊓ W)
          (restrictTo_trace p hp _) i (restrictTo_diag p i W)).hom 2
        (KnCP.cpTaut ↥((diagOpen p i ⊓ W : Opens (TopCat.of X)) : Set X))
      = lhClass (projMap p) ξ (diagOpen p i ⊓ W)) :
    LerayHirschGraded (projMap p) ξ 2 := by
  refine lerayHirschGraded_of_diagCover p hp (projMap p) ξ 2 ?_
  intro i W
  exact LHOver_two_chart p (diagOpen p i ⊓ W) (restrictTo_trace p hp _) i
    (restrictTo_diag p i W) ξ (hξ i W)

end

end LH
end CharClass
end GroupApproximation
