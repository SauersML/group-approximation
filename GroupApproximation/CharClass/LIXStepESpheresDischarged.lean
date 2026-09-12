import GroupApproximation.CharClass.LIXStepEDischarged
import GroupApproximation.CharClass.ThomKunnethSphere
import GroupApproximation.CharClass.CohomologyShapes

/-!
# Step E, with the sphere factors discharged too

Lane `cc-lix-odd` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

`CharClass/LIXStepEDischarged.lean` reduced the punctured-product vanishing at the LIX
base to four cohomology statements about the two sphere factors.  All four are in the
tree, for the vendored `Sphere n = ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1)`,
and this lane's models land in exactly that:

* `sphereOne` **is** `Sphere 1` — the circle was modelled as the unit sphere of the
  Euclidean plane from the start, so there is nothing to transport;
* `unitVectors (Fin 3)` reaches `Sphere 5` through `unitVectorsThreeHomeo`
  (`CharClass/LIXStepESphereModel.lean`).

So the two vanishings come from `cc-cohom-api`'s `hasSphereCohomology_sphere`, the Künneth
factor from `cc-thom`'s `kunnethFactor_sphere` transported by
`KunnethFactor.congrHomotopy`, and its punctured companion from
`kunnethFactor_sphere_compl` transported by `homeomorphCompl` — which is free in the
degree, since that lemma holds at every degree.

**After this, the odd side of Lemma 2 rests on `cc-thom`'s three open chain fields and
nothing else.**

## Main results

* `isZero_cohomology_sphereOne`, `isZero_cohomology_sphereFive` — the two vanishings.
* `kunnethFactor_unitVectorsThree`, `kunnethFactor_unitVectorsThree_compl` — the Künneth
  factor and its punctured companion, in this lane's model.
* `hbase_lix` — the base case, unconditional.
* `stepC_of_thomChain''` — **Step C**, over `cc-thom`'s chain bundle alone.
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix
open CategoryTheory Limits
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-! ## 1. The two vanishings -/

/-- Cohomology of the circle vanishes above degree one. -/
theorem isZero_cohomology_sphereOne (k : ℕ) (hk : 1 < k) :
    IsZero (cohomologyZMod2 (TopCat.of ↥sphereOne) k) := by
  have h := (hasSphereCohomology_sphere 1 le_rfl).2.2 k (by omega) (by omega)
  haveI : Subsingleton (Hmod2 (TopCat.of (Sphere 1)) k) := ⟨fun a c => by rw [h a, h c]⟩
  exact ModuleCat.isZero_of_subsingleton _

/-- Cohomology of the five-sphere vanishes above degree five. -/
theorem isZero_cohomology_sphereFive (k : ℕ) (hk : 5 < k) :
    IsZero (cohomologyZMod2
      (TopCat.of ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 6)) 1)) k) := by
  have h := (hasSphereCohomology_sphere 5 (by omega)).2.2 k (by omega) (by omega)
  haveI : Subsingleton (Hmod2 (TopCat.of (Sphere 5)) k) := ⟨fun a c => by rw [h a, h c]⟩
  exact ModuleCat.isZero_of_subsingleton _

/-! ## 2. The Künneth factor, in this lane's model -/

/-- The Hermitian five-sphere is a Künneth factor of dimension five, through the model
homeomorphism. -/
theorem kunnethFactor_unitVectorsThree : KunnethFactor ↥(unitVectors (Fin 3)) 5 :=
  KunnethFactor.congrHomotopy unitVectorsThreeHomeo.toHomotopyEquiv (kunnethFactor_sphere 5)

/-- Its punctured companion, at any degree: the puncture is contractible, so no Künneth
theorem is involved and the degree is free. -/
theorem kunnethFactor_unitVectorsThree_compl (y : ↥(unitVectors (Fin 3))) (q : ℕ) :
    KunnethFactor ↥({y}ᶜ : Set ↥(unitVectors (Fin 3))) q :=
  KunnethFactor.congrHomotopy (homeomorphCompl unitVectorsThreeHomeo y).toHomotopyEquiv
    (kunnethFactor_sphere_compl (unitVectorsThreeHomeo y) q)

/-! ## 3. The base case, unconditional -/

/-- **The base case of the punctured-product recursion, with nothing assumed.** -/
theorem hbase_lix (w : ↥sphereOne × ↥(unitVectors (Fin 3))) :
    PuncturedAcyclic (↥sphereOne × ↥(unitVectors (Fin 3))) 6 w :=
  hbase_of_vanishing kunnethFactor_unitVectorsThree
    (fun y => kunnethFactor_unitVectorsThree_compl y 4)
    isZero_cohomology_sphereOne isZero_cohomology_sphereFive w

/-- **The punctured-product vanishing at the LIX base, with nothing assumed but
positivity of the dimensions.** -/
theorem puncturedAcyclic_lixBase_final (hdd : ∀ j, 0 < dd j)
    (z : ↥sphereOne × baseM dd) :
    PuncturedAcyclic (↥sphereOne × baseM dd) (lixTopDegree dd) z :=
  puncturedAcyclic_lixBase' hbase_lix hdd z

/-! ## 4. Step C, over the chain bundle alone -/

/-- **Step C.**  Every hypothesis of the odd side except `cc-thom`'s chain bundle is now
discharged: the punctured acyclicity, the projective factor, the sphere factors and the
model transport are all theorems. -/
theorem stepC_of_thomChain'' (chern : LixChernDeg dd) (hdd : ∀ j, 0 < dd j)
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
  stepC_of_thomChain' chern kunnethFactor_unitVectorsThree
    (fun y => kunnethFactor_unitVectorsThree_compl y 4)
    isZero_cohomology_sphereOne isZero_cohomology_sphereFive hdd chain

end GroupApproximation.CharClass
