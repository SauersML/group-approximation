-- Re-proved in the `GroupApproximation.CharClass` namespace from the paused fleet's
-- `GroupApproximation/AlgTop/ComplexProjectivePunctureRetract.lean`, which is red at the pin and owned by no
-- lane of the LIX program.  Lane `cc-projective` owns this copy.
import GroupApproximation.CharClass.ProjectiveSpacePuncture

/-!
# `ℂP^{d+1} ∖ {basePoint} ≃ ℂP^d`

The deformation of `GroupApproximation/AlgTop/ComplexProjectivePuncture.lean` is assembled
into an honest homotopy equivalence

```text
CPn.punctureHomotopyEquiv d : ↥(CPn.punctured d) ≃ₕ CP d.
```

The retraction is `x ↦ deincl (scale (1, x))`: push the first homogeneous coordinate to
zero and read off the lower-right block. Its inverse is the hyperplane inclusion
`CPn.incl`. One composite is the identity **on the nose** (`CPn.retract_inclP`), because
`CPn.scale` fixes the hyperplane pointwise; the other is homotopic to the identity by
`CPn.scale` itself, which is legitimate because the deformation never reaches the base
point: `CPn.rad_scale_lt_one`.

This is the input Mayer–Vietoris needs for the open cover of `ℂP^{d+1}` by the affine
chart and the complement of the base point.
-/

noncomputable section

namespace GroupApproximation.CharClass

open Matrix
open GroupApproximation.STW59
open scoped unitInterval

namespace CPn

variable {d : ℕ}

/-! ## 1. The deformation never reaches the base point -/

theorem entry_scale_zero_zero (p : I × ↥(punctured d)) :
    entry (scale p) 0 0
      = ((((1 - (p.1 : ℝ)) ^ 2 * rad (p.2 : CP (d + 1))
            / scaleTrace (p.1 : ℝ) (p.2 : CP (d + 1)) : ℝ)) : ℂ) := by
  rw [scale_entry, scaleMat_apply, scaleVec_zero, entry_zero_zero_eq_rad]
  push_cast
  ring

theorem rad_scale (p : I × ↥(punctured d)) :
    rad (scale p)
      = (1 - (p.1 : ℝ)) ^ 2 * rad (p.2 : CP (d + 1))
          / scaleTrace (p.1 : ℝ) (p.2 : CP (d + 1)) := by
  have h1 := entry_zero_zero_eq_rad (scale p)
  have h2 := entry_scale_zero_zero p
  rw [h1] at h2
  exact_mod_cast h2

theorem rad_scale_lt_one (p : I × ↥(punctured d)) : rad (scale p) < 1 := by
  have hτ : 0 < scaleTrace (p.1 : ℝ) (p.2 : CP (d + 1)) := scaleTrace_pos p.2.2
  have hlt : rad (p.2 : CP (d + 1)) < 1 := rad_lt_one p.2.2
  rw [rad_scale, div_lt_one hτ]
  simp only [scaleTrace]
  linarith

theorem scale_mem_punctured (p : I × ↥(punctured d)) : scale p ∈ punctured d := by
  intro h
  exact absurd (rad_eq_one_iff.mpr h) (ne_of_lt (rad_scale_lt_one p))

/-- The deformation, as a self-map of the punctured space. -/
def scaleP (p : I × ↥(punctured d)) : ↥(punctured d) := ⟨scale p, scale_mem_punctured p⟩

theorem continuous_scaleP : Continuous (scaleP (d := d)) :=
  continuous_scale.subtype_mk _

/-! ## 2. The two maps -/

theorem incl_ne_basePoint (z : CP d) : incl z ≠ basePoint (d + 1) := by
  intro h
  have h1 : entry (incl z) 0 0 = entry (basePoint (d + 1)) 0 0 := by rw [h]
  rw [incl_entry_zero_zero, basePoint_entry_zero_zero] at h1
  exact zero_ne_one h1

/-- The hyperplane inclusion, landing in the punctured space. -/
def inclP (z : CP d) : ↥(punctured d) := ⟨incl z, incl_ne_basePoint z⟩

theorem continuous_inclP : Continuous (inclP (d := d)) := continuous_incl.subtype_mk _

@[simp] theorem inclP_coe (z : CP d) : ((inclP z : ↥(punctured d)) : CP (d + 1)) = incl z := rfl

/-- **The retraction** `ℂP^{d+1} ∖ {basePoint} → ℂP^d`: push the first homogeneous
coordinate to zero, then read off the lower-right block. -/
def retract (x : ↥(punctured d)) : CP d :=
  deincl (scale ((1 : I), x)) (scale_one_entry_zero_zero x)

@[simp] theorem retract_entry (x : ↥(punctured d)) (i j : Fin (d + 1)) :
    entry (retract x) i j = entry (scale ((1 : I), x)) i.succ j.succ := rfl

theorem continuous_retract : Continuous (retract (d := d)) := by
  apply Continuous.subtype_mk
  refine continuous_matrix fun i j => ?_
  exact (continuous_entry i.succ j.succ).comp
    (continuous_scale.comp (Continuous.prodMk_right (1 : I)))

/-! ## 3. The composites -/

theorem retract_inclP (z : CP d) : retract (inclP z) = z := by
  refine ext fun i j => ?_
  rw [retract_entry]
  have hfix : scale ((1 : I), inclP z) = ((inclP z : ↥(punctured d)) : CP (d + 1)) :=
    scale_of_entry_zero_zero_eq_zero ((1 : I), inclP z) (by
      rw [inclP_coe, incl_entry_zero_zero])
  rw [hfix, inclP_coe, incl_entry, inclMat_succ_succ]

theorem inclP_retract (x : ↥(punctured d)) : inclP (retract x) = scaleP ((1 : I), x) := by
  refine Subtype.ext ?_
  exact incl_deincl (scale ((1 : I), x)) (scale_one_entry_zero_zero x)

/-! ## 4. The homotopy equivalence -/

/-- `CPn.retract` as a bundled continuous map. -/
def retractMap (d : ℕ) : C(↥(punctured d), CP d) := ⟨retract, continuous_retract⟩

/-- `CPn.inclP` as a bundled continuous map. -/
def inclPMap (d : ℕ) : C(CP d, ↥(punctured d)) := ⟨inclP, continuous_inclP⟩

/-- The deformation, as a homotopy from the identity of the punctured space to
`incl ∘ retract`. -/
def scaleHomotopy (d : ℕ) :
    ContinuousMap.Homotopy (ContinuousMap.id ↥(punctured d))
      ((inclPMap d).comp (retractMap d)) where
  toFun := scaleP
  continuous_toFun := continuous_scaleP
  map_zero_left x := Subtype.ext (scale_zero x)
  map_one_left x := (inclP_retract x).symm

theorem retractMap_comp_inclPMap (d : ℕ) :
    (retractMap d).comp (inclPMap d) = ContinuousMap.id (CP d) := by
  ext z
  exact retract_inclP z

/-- **`ℂP^{d+1}` with its base point removed is homotopy equivalent to `ℂP^d`.**
One composite is the identity on the nose; the other is homotopic to the identity through
the scaling deformation, which stays inside the punctured space. -/
def punctureHomotopyEquiv (d : ℕ) :
    ContinuousMap.HomotopyEquiv ↥(punctured d) (CP d) where
  toFun := retractMap d
  invFun := inclPMap d
  left_inv := by
    have h : ContinuousMap.Homotopic (ContinuousMap.id ↥(punctured d))
        ((inclPMap d).comp (retractMap d)) := ⟨scaleHomotopy d⟩
    exact h.symm
  right_inv := by
    rw [retractMap_comp_inclPMap d]
    exact ContinuousMap.Homotopic.refl _

@[simp] theorem punctureHomotopyEquiv_apply (d : ℕ) (x : ↥(punctured d)) :
    punctureHomotopyEquiv d x = retract x := rfl

end CPn

end GroupApproximation.CharClass
