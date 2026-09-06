import GroupApproximation.CharClass.LIXSphereChart

/-!
# The five-sphere chart as a partial homeomorphism

Lane `cc-lix-odd`.

`LIXSphereChart` made the chart total by a radial clamp.  Excision needs more: the chart
must be a homeomorphism onto an open neighbourhood of `-e₃`.  This file supplies the
inverse and the structure.

## The inverse, and why it is a formula rather than a construction

The chart's third coordinate is `w₃ i − √(1 − q w)`, purely imaginary plus a nonpositive
real.  So on the image the real part is `−√(1 − q w)`, and recovering `w` is reading off
three coordinates: `w = (z₀, z₁, Im z₂)`.  The identity that closes it is
`1 − q w = (Re z₂)²`, from `‖z₀‖² + ‖z₁‖² + ‖z₂‖² = 1`, so the square root is `|Re z₂|`,
which is `−Re z₂` exactly on the open lower half.

## Main results

* `sphereLower` — the open set `{z | Re z₂ < 0}`, containing `-e₃`.
* `sphereChartInv` — the inverse formula.
* `sphereChartHomeo` — **the chart as an `OpenPartialHomeomorph`**.
-/

noncomputable section

namespace GroupApproximation.CharClass

open Set
open GroupApproximation.STW59

set_option linter.unusedSectionVars false

/-! ## 1. Coordinates of the chart vector -/

theorem sphereChartVec_two_re (w : ℂ × ℂ × ℝ) :
    (sphereChartVec w 2).re = -chartWeight w := by
  simp [sphereChartVec]

theorem sphereChartVec_two_im (w : ℂ × ℂ × ℝ) :
    (sphereChartVec w 2).im = w.2.2 := by
  simp [sphereChartVec]

/-! ## 2. The open lower half -/

/-- The part of the five-sphere where the last coordinate has negative real part. -/
def sphereLower : Set ↥(unitVectors (Fin 3)) :=
  {z | ((z : Fin 3 → ℂ) 2).re < 0}

theorem isOpen_sphereLower : IsOpen sphereLower := by
  refine isOpen_induced_iff.mpr ⟨{v : Fin 3 → ℂ | (v 2).re < 0}, ?_, rfl⟩
  exact isOpen_lt (Complex.continuous_re.comp (continuous_apply 2)) continuous_const

theorem negEThree_mem_sphereLower : negEThree ∈ sphereLower := by
  show ((((negEThree : ↥(unitVectors (Fin 3))) : Fin 3 → ℂ) 2).re) < 0
  simp [negEThree, eThree]

/-! ## 3. The inverse -/

/-- The inverse formula: read off the first two coordinates and the imaginary part of the
third. -/
def sphereChartInv (z : ↥(unitVectors (Fin 3))) : ℂ × ℂ × ℝ :=
  ((z : Fin 3 → ℂ) 0, (z : Fin 3 → ℂ) 1, ((z : Fin 3 → ℂ) 2).im)

theorem continuous_sphereChartInv : Continuous sphereChartInv := by
  refine Continuous.prodMk ?_ (Continuous.prodMk ?_ ?_)
  · exact (continuous_apply 0).comp continuous_subtype_val
  · exact (continuous_apply 1).comp continuous_subtype_val
  · exact Complex.continuous_im.comp ((continuous_apply 2).comp continuous_subtype_val)

/-- **The key identity.**  On the sphere, `1 − q (invFun z) = (Re z₂)²`. -/
theorem one_sub_sphereQ_inv (z : ↥(unitVectors (Fin 3))) :
    1 - sphereQ (sphereChartInv z) = ((z : Fin 3 → ℂ) 2).re ^ 2 := by
  have hz : ∑ i, ‖(z : Fin 3 → ℂ) i‖ ^ 2 = 1 := mem_unitVectors_iff.mp z.2
  rw [Fin.sum_univ_three] at hz
  have h2 : ‖(z : Fin 3 → ℂ) 2‖ ^ 2
      = ((z : Fin 3 → ℂ) 2).re ^ 2 + ((z : Fin 3 → ℂ) 2).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  unfold sphereQ sphereChartInv
  simp only
  nlinarith [hz, h2]

/-! ## 4. The partial homeomorphism -/

/-- **The five-sphere chart, as a partial homeomorphism onto the open lower half.** -/
def sphereChartHomeo : OpenPartialHomeomorph (ℂ × ℂ × ℝ) ↥(unitVectors (Fin 3)) where
  toFun := sphereChartFun
  invFun := sphereChartInv
  source := {w | sphereQ w < 1}
  target := sphereLower
  map_source' := by
    intro w hw
    show (sphereChartVec (sphereClamp w) 2).re < 0
    have hw' : sphereQ w < 1 := hw
    rw [sphereClamp_eq_self (le_of_lt hw'), sphereChartVec_two_re]
    have hpos : 0 < chartWeight w := by
      rw [chartWeight]
      refine Real.sqrt_pos.mpr ?_
      have : sphereQ w = ‖w.1‖ ^ 2 + ‖w.2.1‖ ^ 2 + w.2.2 ^ 2 := rfl
      linarith [hw', this.symm ▸ hw']
    linarith
  map_target' := by
    intro z hz
    show sphereQ (sphereChartInv z) < 1
    have hkey := one_sub_sphereQ_inv z
    have hre : ((z : Fin 3 → ℂ) 2).re < 0 := hz
    nlinarith [hkey, hre]
  left_inv' := by
    intro w hw
    have hw' : sphereQ w < 1 := hw
    have hcl : sphereClamp w = w := sphereClamp_eq_self (le_of_lt hw')
    show (sphereChartVec (sphereClamp w) 0, sphereChartVec (sphereClamp w) 1,
      (sphereChartVec (sphereClamp w) 2).im) = w
    rw [hcl]
    simp [sphereChartVec]
  right_inv' := by
    intro z hz
    have hre : ((z : Fin 3 → ℂ) 2).re < 0 := hz
    have hq : sphereQ (sphereChartInv z) < 1 := by
      have hkey := one_sub_sphereQ_inv z
      nlinarith [hkey, hre]
    refine Subtype.ext ?_
    show sphereChartVec (sphereClamp (sphereChartInv z)) = _
    rw [sphereClamp_eq_self (le_of_lt hq)]
    funext i
    have hw : chartWeight (sphereChartInv z) = -((z : Fin 3 → ℂ) 2).re := by
      show Real.sqrt (1 - sphereQ (sphereChartInv z)) = _
      rw [one_sub_sphereQ_inv, Real.sqrt_sq_eq_abs, abs_of_neg hre]
    fin_cases i
    · simp [sphereChartVec, sphereChartInv]
    · simp [sphereChartVec, sphereChartInv]
    · show ((sphereChartInv z).2.2 : ℂ) * Complex.I - (chartWeight (sphereChartInv z) : ℂ)
        = (z : Fin 3 → ℂ) 2
      rw [hw]
      have : ((sphereChartInv z).2.2 : ℂ) = (((z : Fin 3 → ℂ) 2).im : ℂ) := rfl
      rw [this]
      push_cast
      rw [sub_neg_eq_add, add_comm]
      exact Complex.re_add_im _
  open_source := by
    exact isOpen_lt continuous_sphereQ continuous_const
  open_target := isOpen_sphereLower
  continuousOn_toFun := continuous_sphereChartFun.continuousOn
  continuousOn_invFun := continuous_sphereChartInv.continuousOn

end GroupApproximation.CharClass
