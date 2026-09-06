import GroupApproximation.CharClass.LIXStepEBase

/-!
# The five-sphere, in the two models

Lane `cc-lix-odd` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

`CharClass/LIXStepEBase.lean` reduced the base case of the punctured-product vanishing to
one missing object: a homeomorphism between this lane's five-sphere,
`STW59.unitVectors (Fin 3)` — the Hermitian unit sphere of the **sup-normed** function
space `Fin 3 → ℂ` — and a metric sphere of a real inner product space, which is the model
`cc-thom`'s green sphere case and `cc-cohom-api`'s sphere cohomology both speak.

This file supplies it, and with it discharges that base case.  The map is the obvious one,
`(z₀, z₁, z₂) ↦ (re z₀, im z₀, re z₁, im z₁, re z₂, im z₂)`; the only content is that it
carries `∑ᵢ ‖zᵢ‖² = 1` to `‖·‖ = 1`, which is `Complex.sq_norm` six times.

`WithLp` is a structure at this pin, so the two sides are **not** definitionally equal and
the bridge is `PiLp.continuous_toLp` and `PiLp.continuous_ofLp` in the two directions.
This is the same seam the chart work of `CharClass/LIXSectionChart.lean` was designed to
avoid; here it has to be paid, and paying it once discharges an assumption rather than
moving it.

## Main results

* `cxToEuc`, `eucToCx` — the two directions, with `normSq_cxToEuc`.
* `unitVectorsThreeHomeo` — **the homeomorphism**.
* `puncturedAcyclic_unitVectorsThree` — the five-sphere factor, now needing only the
  cohomology vanishing.
* `hbase_of_vanishing` — `hbase` from the two vanishings and the Künneth factor, with the
  model transport gone.
-/

noncomputable section

namespace GroupApproximation.CharClass

open GroupApproximation.STW59
open CategoryTheory Limits
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option linter.unusedSectionVars false

/-! ## 1. The two directions -/

/-- `ℂ³` as `ℝ⁶`, real and imaginary parts interleaved. -/
def cxToEuc (x : Fin 3 → ℂ) : EuclideanSpace ℝ (Fin 6) :=
  WithLp.toLp 2 ![(x 0).re, (x 0).im, (x 1).re, (x 1).im, (x 2).re, (x 2).im]

/-- The inverse direction. -/
def eucToCx (y : EuclideanSpace ℝ (Fin 6)) : Fin 3 → ℂ :=
  ![((y 0 : ℝ) : ℂ) + ((y 1 : ℝ) : ℂ) * Complex.I,
    ((y 2 : ℝ) : ℂ) + ((y 3 : ℝ) : ℂ) * Complex.I,
    ((y 4 : ℝ) : ℂ) + ((y 5 : ℝ) : ℂ) * Complex.I]

theorem eucToCx_cxToEuc (x : Fin 3 → ℂ) : eucToCx (cxToEuc x) = x := by
  funext i
  fin_cases i <;>
    · simp only [eucToCx, cxToEuc, Matrix.cons_val_zero, Matrix.cons_val_one]
      simp [Complex.re_add_im]

theorem cxToEuc_eucToCx (y : EuclideanSpace ℝ (Fin 6)) : cxToEuc (eucToCx y) = y := by
  apply WithLp.ofLp_injective
  funext j
  fin_cases j <;> simp [cxToEuc, eucToCx]

/-- **The norm identity.**  The Euclidean norm of the image is the Hermitian norm of the
source; this is `Complex.sq_norm` in each of the three coordinates. -/
theorem normSq_cxToEuc (x : Fin 3 → ℂ) : ‖cxToEuc x‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_six, Fin.sum_univ_three]
  simp only [cxToEuc]
  have h : ∀ z : ℂ, ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := fun z => by
    rw [Complex.sq_norm, Complex.normSq_apply]
  rw [h (x 0), h (x 1), h (x 2)]
  simp
  ring

theorem norm_cxToEuc_eq_one {x : Fin 3 → ℂ} (hx : x ∈ unitVectors (Fin 3)) :
    ‖cxToEuc x‖ = 1 := by
  have hsq : ‖cxToEuc x‖ ^ 2 = 1 := by
    rw [normSq_cxToEuc]
    exact mem_unitVectors_iff.mp hx
  nlinarith [norm_nonneg (cxToEuc x)]

theorem eucToCx_mem_unitVectors {y : EuclideanSpace ℝ (Fin 6)}
    (hy : y ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 6)) 1) :
    eucToCx y ∈ unitVectors (Fin 3) := by
  rw [mem_unitVectors_iff, ← normSq_cxToEuc, cxToEuc_eucToCx]
  rw [mem_sphere_zero_iff_norm.mp hy]
  norm_num

/-! ## 2. Continuity -/

theorem continuous_cxToEuc : Continuous cxToEuc := by
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j => ?_)
  fin_cases j
  · exact Complex.continuous_re.comp (continuous_apply 0)
  · exact Complex.continuous_im.comp (continuous_apply 0)
  · exact Complex.continuous_re.comp (continuous_apply 1)
  · exact Complex.continuous_im.comp (continuous_apply 1)
  · exact Complex.continuous_re.comp (continuous_apply 2)
  · exact Complex.continuous_im.comp (continuous_apply 2)

theorem continuous_eucToCx : Continuous eucToCx := by
  refine continuous_pi fun i => ?_
  have hc : ∀ j : Fin 6, Continuous fun y : EuclideanSpace ℝ (Fin 6) => ((y j : ℝ) : ℂ) :=
    fun j => Complex.continuous_ofReal.comp (PiLp.continuous_apply 2 _ j)
  fin_cases i
  · exact (hc 0).add ((hc 1).mul continuous_const)
  · exact (hc 2).add ((hc 3).mul continuous_const)
  · exact (hc 4).add ((hc 5).mul continuous_const)

/-! ## 3. The homeomorphism, and the base case discharged -/

/-- **The two five-sphere models are homeomorphic.**  This is the object
`CharClass/LIXStepEBase.lean` left as a hypothesis. -/
def unitVectorsThreeHomeo :
    ↥(unitVectors (Fin 3)) ≃ₜ ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 6)) 1) where
  toFun x := ⟨cxToEuc x.1, mem_sphere_zero_iff_norm.mpr (norm_cxToEuc_eq_one x.2)⟩
  invFun y := ⟨eucToCx y.1, eucToCx_mem_unitVectors y.2⟩
  left_inv x := Subtype.ext (eucToCx_cxToEuc x.1)
  right_inv y := Subtype.ext (cxToEuc_eucToCx y.1)
  continuous_toFun :=
    Continuous.subtype_mk (continuous_cxToEuc.comp continuous_subtype_val) _
  continuous_invFun :=
    Continuous.subtype_mk (continuous_eucToCx.comp continuous_subtype_val) _

/-- **The five-sphere factor, with the model transport discharged.** -/
theorem puncturedAcyclic_unitVectorsThree
    (hvanish : ∀ k, 5 < k →
      IsZero (cohomologyZMod2
        (TopCat.of ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 6)) 1)) k))
    (y : ↥(unitVectors (Fin 3))) : PuncturedAcyclic ↥(unitVectors (Fin 3)) 5 y :=
  puncturedAcyclic_unitVectorsThree_of_homeo unitVectorsThreeHomeo hvanish y

/-- **`hbase` from the cohomology vanishings alone.**  The model mismatch is gone; what
remains is two sphere-cohomology statements and one Künneth factor, all owned by
`cc-cohom-api` and `cc-projective`. -/
theorem hbase_of_vanishing
    (kS : KunnethFactor ↥(unitVectors (Fin 3)) 5)
    (kSpunct : ∀ y : ↥(unitVectors (Fin 3)),
      KunnethFactor ↥({y}ᶜ : Set ↥(unitVectors (Fin 3))) 4)
    (h1 : ∀ k, 1 < k → IsZero (cohomologyZMod2 (TopCat.of ↥sphereOne) k))
    (h5 : ∀ k, 5 < k →
      IsZero (cohomologyZMod2
        (TopCat.of ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 6)) 1)) k))
    (w : ↥sphereOne × ↥(unitVectors (Fin 3))) :
    PuncturedAcyclic (↥sphereOne × ↥(unitVectors (Fin 3))) 6 w :=
  hbase_of_factors kS kSpunct (puncturedAcyclic_sphereOne h1)
    (puncturedAcyclic_unitVectorsThree h5) w

end GroupApproximation.CharClass
