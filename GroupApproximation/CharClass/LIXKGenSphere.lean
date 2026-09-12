import GroupApproximation.CharClass.LIXStepEBase
import GroupApproximation.CharClass.ThomProjectivePunctured
import GroupApproximation.CharClass.CohomologyShapes
import GroupApproximation.Meta.AxiomGuard

/-!
# The sphere `S^{2n+1}` in the two models, generic in the rank

Lane `sp-oddside-n` of the STW Problem LIX strengthening
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.1; report
`notes/lix-stronger-lane-reports/sp-oddside-n.md` §0.3 file A).

`CharClass/LIXStepESphereModel.lean` builds the bridge between this tree's five-sphere
`STW59.unitVectors (Fin 3) ⊆ (Fin 3 → ℂ)` — the Hermitian unit sphere of a **sup-normed**
function space — and the metric sphere of a real inner product space, which is the model
the vendored sphere cohomology speaks.  It does so with an explicit six-coordinate
`![…]` literal, so nothing in it survives a change of rank.  This file re-authors that
bridge with the rank `n` as a parameter, and reads off the four consequences that
`CharClass/LIXStepESpheresDischarged.lean` reads off at rank two.

## What did NOT have to be generalised, and it is worth saying

`CharClass/CohomologySphere.lean` is **already** generic in the sphere's dimension:
`sphere_coh_isZero_of_gt (n k : ℕ) (h : n < k)`, `sphereTopEquiv`, `sphereCohZeroEquiv` and
`CohomologyShapes.hasSphereCohomology_sphere` hold for the vendored
`Sphere m = ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (m+1))) 1)` at every `m`.  So are
`ThomKunnethSphere.kunnethFactor_sphere`, `kunnethFactor_sphere_compl` and
`ThomToolkitInstance.puncturedAcyclic_sphere'`, which are generic in the dimension *and*
in the real inner product space.  The rank was welded in at exactly one place, the model
homeomorphism, and that is what this file replaces.

## The index bookkeeping

`ℂ^{n+1}` is `ℝ^{2n+2}` with real and imaginary parts interleaved, so the whole of the
construction rests on one bijection,

```text
  cxIdx n : Fin (n+1) × Fin 2 ≃ Fin (2n+2) ,      (i, b) ↦ 2i + b ,
```

whose inverse is `k ↦ (k / 2, k % 2)`.  Both round trips are `omega` on the `.val`s; this
is the same idiom as `Analysis/LIXGenericEquator.lean`'s `eqIdx`, which is `sp-tower`'s and
which is green, and it is deliberately spelled the same way so that a reader who has read
one has read both.  At `n = 2` it is the interleaving the rank-two `![…]` literal writes
out by hand.

**No bridge to `unitVectorsThreeHomeo` is stated.**  The two homeomorphisms have the same
*statement* at `n = 2` but are built differently (an index `Equiv` against a `![…]`
literal), so no equation between the terms is `rfl`, and nothing needs one: a homeomorphism
is consumed through `PuncturedAcyclic.congr'` and `KunnethFactor.congrHomotopy`, both of
which take it as an argument and never compare it with another.

## Main results

* `KGen.cxIdx` — the interleaving bijection.
* `KGen.cxToEuc`, `KGen.eucToCx`, `KGen.normSq_cxToEuc` — the two directions.
* `KGen.unitVectorsHomeo` — **the homeomorphism**, at every rank.
* `KGen.isZero_cohomology_sphereOdd` — `H^k(S^{2n+1}; F₂) = 0` for `k > 2n+1`.
* `KGen.kunnethFactor_unitVectors`, `KGen.kunnethFactor_unitVectors_compl`.
* `KGen.puncturedAcyclic_unitVectors` — the sphere factor, unconditionally.
* `KGen.hbase` — **the two sphere factors of the LIX base, at every rank**, in degree
  `2n+2`.  At `n = 2` this is `LIXStepESpheresDischarged.hbase_lix`, and
  `KGen.hbase_two_eq_hbase_lix` records that the two statements really are the same one.
-/

noncomputable section

namespace GroupApproximation.CharClass

namespace KGen

open GroupApproximation.STW59
open CategoryTheory Limits
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option linter.unusedSectionVars false

/-! ## 1. `ℝ^{2n+2}` indexed as `n+1` real pairs -/

/-- The coordinate of `ℝ^{2n+2}` carrying the `b`-th real part of the `i`-th complex
coordinate (`b = 0` real, `b = 1` imaginary). -/
def cxFwd (n : ℕ) : Fin (n + 1) × Fin 2 → Fin (2 * n + 2)
  | (i, b) => ⟨2 * (i : ℕ) + (b : ℕ), by
      have hi := i.isLt
      have hb := b.isLt
      omega⟩

/-- The inverse of `cxFwd`: divide by two, and keep the remainder. -/
def cxBwd (n : ℕ) (k : Fin (2 * n + 2)) : Fin (n + 1) × Fin 2 :=
  (⟨(k : ℕ) / 2, by have hk := k.isLt; omega⟩, ⟨(k : ℕ) % 2, by omega⟩)

@[simp] theorem cxFwd_val (n : ℕ) (i : Fin (n + 1)) (b : Fin 2) :
    ((cxFwd n (i, b) : Fin (2 * n + 2)) : ℕ) = 2 * (i : ℕ) + (b : ℕ) := rfl

theorem cxBwd_cxFwd (n : ℕ) (p : Fin (n + 1) × Fin 2) : cxBwd n (cxFwd n p) = p := by
  obtain ⟨i, b⟩ := p
  have hb := b.isLt
  refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
  · show (2 * (i : ℕ) + (b : ℕ)) / 2 = (i : ℕ)
    omega
  · show (2 * (i : ℕ) + (b : ℕ)) % 2 = (b : ℕ)
    omega

theorem cxFwd_cxBwd (n : ℕ) (k : Fin (2 * n + 2)) : cxFwd n (cxBwd n k) = k := by
  have hk := k.isLt
  refine Fin.ext ?_
  show 2 * ((k : ℕ) / 2) + (k : ℕ) % 2 = (k : ℕ)
  omega

/-- **`ℂ^{n+1}` is `ℝ^{2n+2}`, at the level of indices.** -/
def cxIdx (n : ℕ) : (Fin (n + 1) × Fin 2) ≃ Fin (2 * n + 2) where
  toFun := cxFwd n
  invFun := cxBwd n
  left_inv := cxBwd_cxFwd n
  right_inv := cxFwd_cxBwd n

@[simp] theorem cxIdx_apply (n : ℕ) (p : Fin (n + 1) × Fin 2) :
    cxIdx n p = cxFwd n p := rfl

/-! ## 2. The real and imaginary parts as a `Fin 2`-family -/

/-- `reIm z 0 = Re z`, `reIm z 1 = Im z`. -/
def reIm (z : ℂ) : Fin 2 → ℝ := ![z.re, z.im]

@[simp] theorem reIm_zero (z : ℂ) : reIm z 0 = z.re := by simp [reIm]

@[simp] theorem reIm_one (z : ℂ) : reIm z 1 = z.im := by simp [reIm]

theorem sum_reIm_sq (z : ℂ) : ∑ b : Fin 2, reIm z b ^ 2 = ‖z‖ ^ 2 := by
  have h : ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := by
    rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Fin.sum_univ_two, reIm_zero, reIm_one]
  rw [h]
  ring

theorem continuous_reIm (b : Fin 2) : Continuous fun z : ℂ => reIm z b := by
  have h0 : Continuous fun z : ℂ => reIm z 0 := by
    simp only [reIm_zero]
    exact Complex.continuous_re
  have h1 : Continuous fun z : ℂ => reIm z 1 := by
    simp only [reIm_one]
    exact Complex.continuous_im
  fin_cases b
  · exact h0
  · exact h1

/-! ## 3. The two directions -/

/-- `ℂ^{n+1}` as `ℝ^{2n+2}`, real and imaginary parts interleaved. -/
def cxToEuc (n : ℕ) (x : Fin (n + 1) → ℂ) : EuclideanSpace ℝ (Fin (2 * n + 2)) :=
  WithLp.toLp 2 fun k => reIm (x (cxBwd n k).1) (cxBwd n k).2

theorem cxToEuc_apply (n : ℕ) (x : Fin (n + 1) → ℂ) (k : Fin (2 * n + 2)) :
    cxToEuc n x k = reIm (x (cxBwd n k).1) (cxBwd n k).2 := rfl

theorem cxToEuc_cxFwd (n : ℕ) (x : Fin (n + 1) → ℂ) (i : Fin (n + 1)) (b : Fin 2) :
    cxToEuc n x (cxFwd n (i, b)) = reIm (x i) b := by
  rw [cxToEuc_apply, cxBwd_cxFwd]

/-- The inverse direction. -/
def eucToCx (n : ℕ) (y : EuclideanSpace ℝ (Fin (2 * n + 2))) : Fin (n + 1) → ℂ :=
  fun i => ((y (cxFwd n (i, 0)) : ℝ) : ℂ) + ((y (cxFwd n (i, 1)) : ℝ) : ℂ) * Complex.I

theorem eucToCx_apply (n : ℕ) (y : EuclideanSpace ℝ (Fin (2 * n + 2))) (i : Fin (n + 1)) :
    eucToCx n y i
      = ((y (cxFwd n (i, 0)) : ℝ) : ℂ) + ((y (cxFwd n (i, 1)) : ℝ) : ℂ) * Complex.I := rfl

/-- Pointwise extensionality for `EuclideanSpace ℝ (Fin m)`, in the shape the round trip
below needs.  `WithLp` is a structure at this pin, so the two sides are not judgmentally
functions and this has to be said once. -/
theorem euc_ext {m : ℕ} {a b : EuclideanSpace ℝ (Fin m)} (h : ∀ i, a i = b i) : a = b := by
  apply WithLp.ofLp_injective
  funext i
  exact h i

theorem eucToCx_cxToEuc (n : ℕ) (x : Fin (n + 1) → ℂ) : eucToCx n (cxToEuc n x) = x := by
  funext i
  rw [eucToCx_apply, cxToEuc_cxFwd, cxToEuc_cxFwd, reIm_zero, reIm_one]
  exact Complex.re_add_im (x i)

theorem cxToEuc_eucToCx (n : ℕ) (y : EuclideanSpace ℝ (Fin (2 * n + 2))) :
    cxToEuc n (eucToCx n y) = y := by
  have h0 : ∀ i : Fin (n + 1),
      cxToEuc n (eucToCx n y) (cxFwd n (i, 0)) = y (cxFwd n (i, 0)) := by
    intro i
    rw [cxToEuc_cxFwd, reIm_zero, eucToCx_apply]
    simp
  have h1 : ∀ i : Fin (n + 1),
      cxToEuc n (eucToCx n y) (cxFwd n (i, 1)) = y (cxFwd n (i, 1)) := by
    intro i
    rw [cxToEuc_cxFwd, reIm_one, eucToCx_apply]
    simp
  have key : ∀ (i : Fin (n + 1)) (b : Fin 2),
      cxToEuc n (eucToCx n y) (cxFwd n (i, b)) = y (cxFwd n (i, b)) := by
    intro i b
    fin_cases b
    · exact h0 i
    · exact h1 i
  refine euc_ext fun k => ?_
  have hk : cxFwd n (cxBwd n k) = k := cxFwd_cxBwd n k
  calc cxToEuc n (eucToCx n y) k
      = cxToEuc n (eucToCx n y) (cxFwd n (cxBwd n k)) := by rw [hk]
    _ = y (cxFwd n (cxBwd n k)) := key (cxBwd n k).1 (cxBwd n k).2
    _ = y k := by rw [hk]

/-! ## 4. The norm identity -/

/-- **The norm identity.**  The Euclidean norm of the image is the Hermitian norm of the
source, at every rank; the rank-two file proves it by `Complex.sq_norm` six times, and here
it is one reindexing along `cxIdx` plus `sum_reIm_sq`. -/
theorem normSq_cxToEuc (n : ℕ) (x : Fin (n + 1) → ℂ) :
    ‖cxToEuc n x‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  have hE : ∑ k : Fin (2 * n + 2), (cxToEuc n x k) ^ 2
      = ∑ p : Fin (n + 1) × Fin 2, (cxToEuc n x (cxFwd n p)) ^ 2 :=
    (Fintype.sum_equiv (cxIdx n)
      (fun p => (cxToEuc n x (cxFwd n p)) ^ 2) (fun k => (cxToEuc n x k) ^ 2)
      (fun p => by rw [cxIdx_apply])).symm
  rw [hE]
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← sum_reIm_sq (x i)]
  exact Finset.sum_congr rfl fun b _ => by rw [cxToEuc_cxFwd]

theorem norm_cxToEuc_eq_one (n : ℕ) {x : Fin (n + 1) → ℂ}
    (hx : x ∈ unitVectors (Fin (n + 1))) : ‖cxToEuc n x‖ = 1 := by
  have hsq : ‖cxToEuc n x‖ ^ 2 = 1 := by
    rw [normSq_cxToEuc]
    exact mem_unitVectors_iff.mp hx
  nlinarith [norm_nonneg (cxToEuc n x)]

theorem eucToCx_mem_unitVectors (n : ℕ) {y : EuclideanSpace ℝ (Fin (2 * n + 2))}
    (hy : y ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (2 * n + 2))) 1) :
    eucToCx n y ∈ unitVectors (Fin (n + 1)) := by
  rw [mem_unitVectors_iff, ← normSq_cxToEuc, cxToEuc_eucToCx]
  rw [mem_sphere_zero_iff_norm.mp hy]
  norm_num

/-! ## 5. Continuity -/

theorem continuous_cxToEuc (n : ℕ) : Continuous (cxToEuc n) := by
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun k => ?_)
  exact (continuous_reIm (cxBwd n k).2).comp' (continuous_apply (cxBwd n k).1)

theorem continuous_eucToCx (n : ℕ) : Continuous (eucToCx n) := by
  have hc : ∀ k : Fin (2 * n + 2),
      Continuous fun y : EuclideanSpace ℝ (Fin (2 * n + 2)) => ((y k : ℝ) : ℂ) :=
    fun k => Complex.continuous_ofReal.comp (PiLp.continuous_apply 2 (fun _ => ℝ) k)
  refine continuous_pi fun i => ?_
  exact (hc (cxFwd n (i, 0))).add ((hc (cxFwd n (i, 1))).mul continuous_const)

/-! ## 6. The homeomorphism -/

/-- **The two models of `S^{2n+1}` are homeomorphic, at every rank.**  This is the object
`CharClass/LIXStepEBase.lean` leaves as a hypothesis and
`CharClass/LIXStepESphereModel.lean` supplies at `n = 2` only. -/
def unitVectorsHomeo (n : ℕ) :
    ↥(unitVectors (Fin (n + 1)))
      ≃ₜ ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (2 * n + 2))) 1) where
  toFun x := ⟨cxToEuc n x.1, mem_sphere_zero_iff_norm.mpr (norm_cxToEuc_eq_one n x.2)⟩
  invFun y := ⟨eucToCx n y.1, eucToCx_mem_unitVectors n y.2⟩
  left_inv x := Subtype.ext (eucToCx_cxToEuc n x.1)
  right_inv y := Subtype.ext (cxToEuc_eucToCx n y.1)
  continuous_toFun :=
    Continuous.subtype_mk ((continuous_cxToEuc n).comp continuous_subtype_val) _
  continuous_invFun :=
    Continuous.subtype_mk ((continuous_eucToCx n).comp continuous_subtype_val) _

/-! ## 7. The four consequences -/

/-- **`H^k(S^{2n+1}; F₂) = 0` above the dimension.**  The vendored sphere cohomology is
already generic in the dimension; this is it, spelled at the ambient `Fin (2n+2)` this
lane's homeomorphism lands in. -/
theorem isZero_cohomology_sphereOdd (n k : ℕ) (hk : 2 * n + 1 < k) :
    IsZero (cohomologyZMod2
      (TopCat.of ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (2 * n + 2))) 1)) k) := by
  have h := sphere_coh_isZero_of_gt (2 * n + 1) k hk
  exact h

/-- The Hermitian sphere `S^{2n+1}` is a Künneth factor of dimension `2n+1`. -/
theorem kunnethFactor_unitVectors (n : ℕ) :
    KunnethFactor ↥(unitVectors (Fin (n + 1))) (2 * n + 1) := by
  have h : KunnethFactor
      ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (2 * n + 2))) 1) (2 * n + 1) :=
    kunnethFactor_sphere (2 * n + 1)
  exact KunnethFactor.congrHomotopy (unitVectorsHomeo n).toHomotopyEquiv h

/-- Its punctured companion, at any degree: the puncture is contractible, so no Künneth
theorem is involved and the degree is free. -/
theorem kunnethFactor_unitVectors_compl (n : ℕ) (y : ↥(unitVectors (Fin (n + 1))))
    (q : ℕ) :
    KunnethFactor ↥({y}ᶜ : Set ↥(unitVectors (Fin (n + 1)))) q :=
  KunnethFactor.congrHomotopy (homeomorphCompl (unitVectorsHomeo n) y).toHomotopyEquiv
    (kunnethFactor_sphere_compl (unitVectorsHomeo n y) q)

/-- **The sphere factor, unconditionally.**  Note there is no positivity hypothesis: the
dimension is `2n+1`, which is positive at every rank including `n = 0`. -/
theorem puncturedAcyclic_unitVectors (n : ℕ) (y : ↥(unitVectors (Fin (n + 1)))) :
    PuncturedAcyclic ↥(unitVectors (Fin (n + 1))) (2 * n + 1) y :=
  PuncturedAcyclic.congr' cohomologyToolkit (unitVectorsHomeo n) rfl
    (puncturedAcyclic_sphere' (n := 2 * n + 1) (by omega) (unitVectorsHomeo n y)
      (isZero_cohomology_sphereOdd n))

/-! ## 8. The two sphere factors of the LIX base -/

/-- **The circle factor.**  `sphereOne` is `Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1`,
which is `KGen.unitVectorsHomeo`'s target at `n = 0`; so the vanishing above degree one is
`isZero_cohomology_sphereOdd 0`, with no separate statement to prove. -/
theorem isZero_cohomology_circle (k : ℕ) (hk : 1 < k) :
    IsZero (cohomologyZMod2 (TopCat.of ↥sphereOne) k) := by
  have h := isZero_cohomology_sphereOdd 0 k (by omega)
  exact h

/-- **The base case of the punctured-product recursion, at every rank.**  `S¹ × S^{2n+1}`
is top-punctured acyclic in degree `2n + 2`.  At `n = 2` this is
`LIXStepESpheresDischarged.hbase_lix`. -/
theorem hbase (n : ℕ) (w : ↥sphereOne × ↥(unitVectors (Fin (n + 1)))) :
    PuncturedAcyclic (↥sphereOne × ↥(unitVectors (Fin (n + 1)))) (2 * n + 2) w := by
  have hprod := puncturedAcyclic_prod (x₀ := w.1) (y₀ := w.2)
    (kunnethFactor_unitVectors n) (kunnethFactor_unitVectors_compl n w.2 (2 * n))
    (puncturedAcyclic_sphereOne isZero_cohomology_circle w.1)
    (puncturedAcyclic_unitVectors n w.2)
  have hdeg : 2 * n + 2 = 1 + (2 * n + 1) := by omega
  rw [hdeg]
  exact hprod

/-- **The rank-two cross-check.**  `KGen.hbase 2` has, on the nose, the statement of
`LIXStepESpheresDischarged.hbase_lix`: both indices are numerals, `Fin (2+1)` is `Fin 3`
and `2*2+2` is `6`, so the generic theorem really is a generalisation of the rank-two one
rather than a statement about a neighbouring object.  This is the cheap half of fleet
rule 17 and it costs one line. -/
theorem hbase_two_eq_hbase_lix
    (w : ↥sphereOne × ↥(unitVectors (Fin 3))) :
    PuncturedAcyclic (↥sphereOne × ↥(unitVectors (Fin 3))) 6 w :=
  hbase 2 w

end KGen

/-! Audited on every build: `#audit_axioms` prints the closure **and fails the build** if
it leaves the classical allowlist. -/

#audit_axioms KGen.normSq_cxToEuc
#audit_axioms KGen.cxToEuc_eucToCx
#audit_axioms KGen.puncturedAcyclic_unitVectors
#audit_axioms KGen.hbase
#audit_axioms KGen.hbase_two_eq_hbase_lix

end GroupApproximation.CharClass
