import GroupApproximation.CharClass.LemmaTwoStepC
import GroupApproximation.CharClass.LIXStepESphereModel
import GroupApproximation.CharClass.ThomProjectivePunctured

/-!
# Step E, with the projective factor discharged

Lane `cc-lix-odd` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

`CharClass/LIXStepEPunctured.lean` proved the punctured-product vanishing at the LIX base
from four hypotheses: three about the projective factor and one about the two sphere
factors.  `cc-thom` has since landed all three projective ones —
`puncturedAcyclic_CP` and `kunnethFactor_CP_punctured` in
`CharClass/ThomProjectivePunctured.lean`, and `kunnethFactor_CP` in
`CharClass/ThomKunnethProjective.lean` — in exactly the shape those hypotheses take,
including the positivity guard and the truncated subtraction.  So all three discharge by
`exact`.

`CharClass/LIXStepESphereModel.lean` reduced the fourth to two sphere-cohomology
vanishings and one Künneth factor, with the model transport gone.  Composing the two,
the whole of Step E's punctured acyclicity now rests on **four cohomology statements and
nothing else**: the vanishing above degree one on the circle, the vanishing above degree
five on the Euclidean five-sphere, and the Künneth factor of the five-sphere with its
punctured companion.

The earlier, fully-hypothetical forms are kept: per the fleet rule a published signature
does not change, and other lanes may already consume them.

## Main results

* `puncturedAcyclic_lixBase'` — the punctured-product vanishing, projective factor gone.
* `puncturedAcyclic_lixZero'` — the same at the section's zero, in the rank degree.
* `stepC_of_thomChain'` — **Step C** with the projective factor gone as well.
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix
open CategoryTheory Limits
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-! ## 1. The projective factor, discharged -/

/-- **The punctured-product vanishing at the LIX base**, with all three projective
hypotheses discharged from `cc-thom`'s green theorems.  What remains is the sphere side. -/
theorem puncturedAcyclic_lixBase'
    (hbase : ∀ w : ↥sphereOne × ↥(unitVectors (Fin 3)),
      PuncturedAcyclic (↥sphereOne × ↥(unitVectors (Fin 3))) 6 w)
    (hdd : ∀ j, 0 < dd j) (z : ↥sphereOne × baseM dd) :
    PuncturedAcyclic (↥sphereOne × baseM dd) (lixTopDegree dd) z :=
  puncturedAcyclic_lixBase_lixTopDegree puncturedAcyclic_CP (fun d _ => kunnethFactor_CP d)
    kunnethFactor_CP_punctured hbase dd hdd z

/-- The same at the section's single zero, in the degree `LemmaTwoStepC` works in. -/
theorem puncturedAcyclic_lixZero'
    (hbase : ∀ w : ↥sphereOne × ↥(unitVectors (Fin 3)),
      PuncturedAcyclic (↥sphereOne × ↥(unitVectors (Fin 3))) 6 w)
    (hdd : ∀ j, 0 < dd j) :
    PuncturedAcyclic (↥sphereOne × baseM dd) (2 * lixRank dd) (lixZero dd) :=
  puncturedAcyclic_lixZero puncturedAcyclic_CP (fun d _ => kunnethFactor_CP d)
    kunnethFactor_CP_punctured hbase hdd

/-! ## 2. Step C, with the projective factor gone -/

/-- **Step C**, with the projective factor discharged.  The sphere side enters as the two
cohomology vanishings and the Künneth factor of `CharClass/LIXStepESphereModel.lean`, so
every remaining hypothesis is a cohomology statement owned by `cc-cohom-api` or
`cc-projective`, plus `cc-thom`'s chain bundle. -/
theorem stepC_of_thomChain' (chern : LixChernDeg dd)
    (kS : KunnethFactor ↥(unitVectors (Fin 3)) 5)
    (kSpunct : ∀ y : ↥(unitVectors (Fin 3)),
      KunnethFactor ↥({y}ᶜ : Set ↥(unitVectors (Fin 3))) 4)
    (h1 : ∀ k, 1 < k → IsZero (cohomologyZMod2 (TopCat.of ↥sphereOne) k))
    (h5 : ∀ k, 5 < k →
      IsZero (cohomologyZMod2
        (TopCat.of ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 6)) 1)) k))
    (hdd : ∀ j, 0 < dd j)
    (chain : ∀ (G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ) (hGc : Continuous G)
      (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)),
      (∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0) →
      ThomChainData dd
        (chern (mappingTorus Vmat G circHoriz circHeight)
          (continuous_mappingTorus_lix hGc) (isStarProjection_mappingTorus_lix hGu)
          (lixRank dd))) :
    ∀ G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ, Continuous G →
      (∀ m, IsCornerUnitary (Vmat m) (G m)) →
      (∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0) →
      lixTopClass chern (mappingTorus Vmat G circHoriz circHeight) ≠ 0 :=
  stepC_of_chain chern fun G hGc hGu hGe =>
    ne_zero_of_thomChain
      (puncturedAcyclic_lixZero' (hbase_of_vanishing kS kSpunct h1 h5) hdd)
      (chain G hGc hGu hGe)

end GroupApproximation.CharClass
