import GroupApproximation.CharClass.LIXStepEPunctured

/-!
# Step E, second piece: the two sphere factors of the LIX base

Lane `cc-lix-odd` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

`CharClass/LIXStepEPunctured.lean` reduces the punctured-product vanishing at
`N = S¹ × S⁵ × ∏ⱼ ℂP^{dⱼ}` to four hypotheses, one of which — `hbase` — is about the two
sphere factors in **this lane's** models.  `cc-thom` left it assumed because their green
sphere case is stated for `Metric.sphere (0 : E) 1` in a real inner product space, and
asked whether this lane wants to discharge it.  This file does as much of that as is
possible without a lemma from another lane, and names precisely what is left.

## What comes out, and what is left

* **The circle factor is free.**  `sphereOne` *is* `Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1`,
  so `cc-thom`'s `puncturedAcyclic_sphere'` applies on the nose, with no transport at all.
  `puncturedAcyclic_sphereOne` reduces it to the cohomology vanishing above degree one.
* **The five-sphere factor needs one homeomorphism.**  `unitVectors (Fin 3)` is the
  Hermitian unit sphere of the *sup-normed* function space `Fin 3 → ℂ`, not a metric sphere
  of an inner product space, so somebody must produce
  `↥(unitVectors (Fin 3)) ≃ₜ ↥(Metric.sphere (0 : E) 1)` for a real inner product space `E`
  of dimension six.  That is the same `WithLp` bridge the chart work of
  `CharClass/LIXSectionChart.lean` was designed to avoid, and it is this lane's to write.
  `puncturedAcyclic_unitVectorsThree_of_homeo` takes it as a hypothesis and gives the
  conclusion, so the remaining obligation is exactly one homeomorphism.
* **The join is one application** of `cc-thom`'s binary step: `hbase_of_factors`.

So `hbase` is now four factor-level hypotheses, each of which is either a sphere-cohomology
vanishing owned by `cc-cohom-api` or a Künneth factor owned by `cc-projective`, plus the
one homeomorphism above.

## Main results

* `puncturedAcyclic_sphereOne` — the circle factor, on the nose.
* `puncturedAcyclic_unitVectorsThree_of_homeo` — the five-sphere factor, modulo the model
  homeomorphism.
* `hbase_of_factors` — the `hbase` hypothesis of `puncturedAcyclic_lixBase`, from the
  factors.
-/

noncomputable section

namespace GroupApproximation.CharClass

open GroupApproximation.STW59
open CategoryTheory Limits
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option linter.unusedSectionVars false

/-! ## 1. The circle factor -/

/-- **The circle factor, with no transport.**  `sphereOne` is already the unit sphere of a
real inner product space, so `cc-thom`'s sphere case applies directly. -/
theorem puncturedAcyclic_sphereOne
    (hvanish : ∀ k, 1 < k → IsZero (cohomologyZMod2 (TopCat.of ↥sphereOne) k))
    (x : ↥sphereOne) : PuncturedAcyclic ↥sphereOne 1 x :=
  puncturedAcyclic_sphere' (n := 1) (by norm_num) x hvanish

/-! ## 2. The five-sphere factor -/

/-- **The five-sphere factor, modulo the model homeomorphism.**  `unitVectors (Fin 3)` is
the Hermitian unit sphere of the sup-normed `Fin 3 → ℂ`; `cc-thom`'s sphere case wants the
metric sphere of a real inner product space.  Given the homeomorphism between the two
models, the conclusion transports by `PuncturedAcyclic.congr'`. -/
theorem puncturedAcyclic_unitVectorsThree_of_homeo {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : ↥(unitVectors (Fin 3)) ≃ₜ ↥(Metric.sphere (0 : E) 1))
    (hvanish : ∀ k, 5 < k →
      IsZero (cohomologyZMod2 (TopCat.of ↥(Metric.sphere (0 : E) 1)) k))
    (y : ↥(unitVectors (Fin 3))) : PuncturedAcyclic ↥(unitVectors (Fin 3)) 5 y :=
  PuncturedAcyclic.congr' cohomologyToolkit e rfl
    (puncturedAcyclic_sphere' (n := 5) (by norm_num) (e y) hvanish)

/-! ## 3. The join -/

/-- **`hbase` from its two factors.**  One application of `cc-thom`'s binary step, at
degrees `1` and `5`. -/
theorem hbase_of_factors
    (kS : KunnethFactor ↥(unitVectors (Fin 3)) 5)
    (kSpunct : ∀ y : ↥(unitVectors (Fin 3)),
      KunnethFactor ↥({y}ᶜ : Set ↥(unitVectors (Fin 3))) 4)
    (h1 : ∀ x : ↥sphereOne, PuncturedAcyclic ↥sphereOne 1 x)
    (h5 : ∀ y : ↥(unitVectors (Fin 3)), PuncturedAcyclic ↥(unitVectors (Fin 3)) 5 y)
    (w : ↥sphereOne × ↥(unitVectors (Fin 3))) :
    PuncturedAcyclic (↥sphereOne × ↥(unitVectors (Fin 3))) 6 w := by
  have hprod := puncturedAcyclic_prod (x₀ := w.1) (y₀ := w.2) kS (kSpunct w.2)
    (h1 w.1) (h5 w.2)
  simpa using hprod

end GroupApproximation.CharClass
