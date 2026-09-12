import GroupApproximation.CharClass.MappingTorusProjection

/-!
# The circle factor of the base chart

Lane `cc-lix-odd`.

`lixFullChart` reads the section in charts and lands in the fibre.  To restrict a relative
class from the pair over `lixN` to that chart, a map the other way is needed: from chart
coordinates **into** the base.  Nothing in the tree had one, so this file builds the first
of its three factors.

The circle is charted at its south pole by the horizontal coordinate.  On the open lower
half `{z ∈ S¹ | z₁ < 0}` the first coordinate is a homeomorphism onto `(-1, 1)`, with
inverse `u ↦ (u, -√(1 - u²))`.  The south pole is the origin of the chart, which matches
`lixZero`.

## Main results

* `circChartVec`, `circChart` — the chart, as an `OpenPartialHomeomorph`.
* `circChart_zero`, `zero_mem_circChart_source`, `southPole_mem_circChart_target`.
-/

noncomputable section

namespace GroupApproximation.CharClass

open Set

set_option linter.unusedSectionVars false

/-! ## 1. The parametrisation -/

/-- The lower half of the circle, parametrised by the horizontal coordinate. -/
def circChartVec (u : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![u, -Real.sqrt (1 - u ^ 2)]

theorem circChartVec_mem {u : ℝ} (h1 : (0 : ℝ) ≤ 1 - u ^ 2) :
    circChartVec u ∈ sphereOne := by
  have hsq : Real.sqrt (1 - u ^ 2) ^ 2 = 1 - u ^ 2 := Real.sq_sqrt h1
  rw [mem_sphere_zero_iff_norm]
  have : ‖circChartVec u‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    simp only [circChartVec, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_one]
    nlinarith [hsq]
  nlinarith [norm_nonneg (circChartVec u), this]

/-- The coordinate clamped into `[-1, 1]`, so that the chart map is **total** and the
`dite` that would otherwise obstruct continuity never appears. -/
def circClamp (u : ℝ) : ℝ := max (-1) (min 1 u)

theorem continuous_circClamp : Continuous circClamp := by
  unfold circClamp; fun_prop

theorem circClamp_sq_le (u : ℝ) : (0 : ℝ) ≤ 1 - circClamp u ^ 2 := by
  have h1 : (-1 : ℝ) ≤ circClamp u := le_max_left _ _
  have h2 : circClamp u ≤ 1 := by
    refine max_le (by norm_num) (min_le_left _ _)
  nlinarith

theorem circClamp_eq_self {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) : circClamp u = u := by
  have h1 : min 1 u = u := min_eq_right (le_of_lt hu.2)
  rw [circClamp, h1, max_eq_right (le_of_lt hu.1)]

theorem continuous_circChartVec : Continuous circChartVec := by
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  fin_cases i
  · exact continuous_id
  · exact (Real.continuous_sqrt.comp (by fun_prop)).neg

/-- The chart map, total by clamping. -/
def circChartFun (u : ℝ) : ↥sphereOne :=
  ⟨circChartVec (circClamp u), circChartVec_mem (circClamp_sq_le u)⟩

theorem continuous_circChartFun : Continuous circChartFun :=
  (continuous_circChartVec.comp continuous_circClamp).subtype_mk _

/-- The set of points of the circle strictly below the equator. -/
def circLower : Set ↥sphereOne :=
  {z | (z : EuclideanSpace ℝ (Fin 2)) 1 < 0}

theorem isOpen_circLower : IsOpen circLower := by
  refine isOpen_induced_iff.mpr ⟨{v : EuclideanSpace ℝ (Fin 2) | v 1 < 0}, ?_, rfl⟩
  exact isOpen_lt (by fun_prop) continuous_const

theorem southPole_mem_circLower : southPole ∈ circLower := by
  show (southPole : EuclideanSpace ℝ (Fin 2)) 1 < 0
  simp [southPole]

/-! ## 2. The chart -/

/-- **The circle chart at the south pole.** -/
def circChart : OpenPartialHomeomorph ℝ ↥sphereOne where
  toFun := circChartFun
  invFun z := (z : EuclideanSpace ℝ (Fin 2)) 0
  source := Ioo (-1 : ℝ) 1
  target := circLower
  map_source' := by
    intro u hu
    show (circChartVec (circClamp u) : EuclideanSpace ℝ (Fin 2)) 1 < 0
    rw [circClamp_eq_self hu]
    have h1 : (0 : ℝ) < 1 - u ^ 2 := by nlinarith [hu.1, hu.2]
    have : Real.sqrt (1 - u ^ 2) > 0 := Real.sqrt_pos.mpr h1
    simpa [circChartVec] using this
  map_target' := by
    intro z hz
    have hnorm : ‖(z : EuclideanSpace ℝ (Fin 2))‖ = 1 := mem_sphere_zero_iff_norm.mp z.2
    have hsq : ((z : EuclideanSpace ℝ (Fin 2)) 0) ^ 2 + ((z : EuclideanSpace ℝ (Fin 2)) 1) ^ 2
        = 1 := by
      have := congrArg (fun r : ℝ => r ^ 2) hnorm
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two] at this
      simpa using this
    have hneg : (z : EuclideanSpace ℝ (Fin 2)) 1 < 0 := hz
    constructor
    · nlinarith [hsq, hneg]
    · nlinarith [hsq, hneg]
  left_inv' := by
    intro u hu
    show (circChartVec (circClamp u) : EuclideanSpace ℝ (Fin 2)) 0 = u
    rw [circClamp_eq_self hu]
    simp [circChartVec]
  right_inv' := by
    intro z hz
    have hnorm : ‖(z : EuclideanSpace ℝ (Fin 2))‖ = 1 := mem_sphere_zero_iff_norm.mp z.2
    have hsq : ((z : EuclideanSpace ℝ (Fin 2)) 0) ^ 2 + ((z : EuclideanSpace ℝ (Fin 2)) 1) ^ 2
        = 1 := by
      have := congrArg (fun r : ℝ => r ^ 2) hnorm
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two] at this
      simpa using this
    have hneg : (z : EuclideanSpace ℝ (Fin 2)) 1 < 0 := hz
    have hmem : (z : EuclideanSpace ℝ (Fin 2)) 0 ∈ Ioo (-1 : ℝ) 1 := by
      constructor
      · nlinarith [hsq, hneg]
      · nlinarith [hsq, hneg]
    refine Subtype.ext ?_
    show circChartVec (circClamp ((z : EuclideanSpace ℝ (Fin 2)) 0)) = _
    rw [circClamp_eq_self hmem]
    apply WithLp.ofLp_injective
    funext i
    fin_cases i
    · simp [circChartVec]
    · show -Real.sqrt (1 - ((z : EuclideanSpace ℝ (Fin 2)) 0) ^ 2)
        = (z : EuclideanSpace ℝ (Fin 2)) 1
      have h1 : 1 - ((z : EuclideanSpace ℝ (Fin 2)) 0) ^ 2
          = ((z : EuclideanSpace ℝ (Fin 2)) 1) ^ 2 := by linarith [hsq]
      rw [h1, Real.sqrt_sq_eq_abs, abs_of_neg hneg, neg_neg]
  open_source := isOpen_Ioo
  open_target := isOpen_circLower
  continuousOn_toFun := continuous_circChartFun.continuousOn
  continuousOn_invFun := by
    exact (continuous_apply 0).comp_continuousOn
      ((PiLp.continuous_ofLp 2 _).comp continuous_subtype_val).continuousOn

end GroupApproximation.CharClass
