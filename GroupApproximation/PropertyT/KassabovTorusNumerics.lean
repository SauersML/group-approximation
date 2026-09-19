import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Numerical core of the rank-zero torus estimate

The geometric part of the torus argument produces two nonnegative masses.
The boundary mass is at most `epsilon ^ 2`, while the core mass satisfies a
single quadratic inequality containing `sqrt (core + epsilon ^ 2)`.  This
module solves that inequality and records the resulting constant exactly.

No measure, action, representation, or external theorem is assumed here.
-/

namespace GroupApproximation

namespace KassabovTorusNumerics

/-- Solving the quadratic inequality for the core mass gives the exact
coefficient `13 + 4 * sqrt 10`. -/
theorem core_mass_le
    {core epsilon : ℝ} (hcore : 0 ≤ core) (hepsilon : 0 ≤ epsilon)
    (hquadratic :
      core ≤ 5 * epsilon ^ 2 +
        4 * epsilon * Real.sqrt (core + epsilon ^ 2)) :
    core ≤ (13 + 4 * Real.sqrt 10) * epsilon ^ 2 := by
  have hsum : 0 ≤ core + epsilon ^ 2 :=
    add_nonneg hcore (sq_nonneg epsilon)
  have hsquare : Real.sqrt (core + epsilon ^ 2) ^ 2 =
      core + epsilon ^ 2 :=
    Real.sq_sqrt hsum
  have hsqrtTen : Real.sqrt 10 ^ 2 = 10 :=
    Real.sq_sqrt (by norm_num)
  have hsqrtTenNonneg : 0 ≤ Real.sqrt 10 := Real.sqrt_nonneg 10
  have hsqrtNonneg : 0 ≤ Real.sqrt (core + epsilon ^ 2) :=
    Real.sqrt_nonneg _
  have hsqrtTenGtTwo : 2 < Real.sqrt 10 := by
    nlinarith
  have hpolynomial :
      Real.sqrt (core + epsilon ^ 2) ^ 2 -
          4 * epsilon * Real.sqrt (core + epsilon ^ 2) -
            6 * epsilon ^ 2 ≤ 0 := by
    nlinarith
  have hroot :
      Real.sqrt (core + epsilon ^ 2) ≤
        (2 + Real.sqrt 10) * epsilon := by
    by_contra hnot
    have hfirst :
        0 < Real.sqrt (core + epsilon ^ 2) -
          (2 + Real.sqrt 10) * epsilon := by
      exact sub_pos.mpr (lt_of_not_ge hnot)
    have hsecond :
        0 < Real.sqrt (core + epsilon ^ 2) -
          (2 - Real.sqrt 10) * epsilon := by
      nlinarith
    have hpositive :
        0 < Real.sqrt (core + epsilon ^ 2) ^ 2 -
          4 * epsilon * Real.sqrt (core + epsilon ^ 2) -
            6 * epsilon ^ 2 := by
      rw [show Real.sqrt (core + epsilon ^ 2) ^ 2 -
          4 * epsilon * Real.sqrt (core + epsilon ^ 2) -
            6 * epsilon ^ 2 =
          (Real.sqrt (core + epsilon ^ 2) -
              (2 + Real.sqrt 10) * epsilon) *
            (Real.sqrt (core + epsilon ^ 2) -
              (2 - Real.sqrt 10) * epsilon) by
        nlinarith]
      positivity
    linarith
  nlinarith

/-- Adding boundary mass at most `epsilon ^ 2` gives the square constant
`(2 + sqrt 10) ^ 2`. -/
theorem total_mass_le
    {core boundary total epsilon : ℝ}
    (hcore : 0 ≤ core) (hepsilon : 0 ≤ epsilon)
    (hboundary : boundary ≤ epsilon ^ 2)
    (htotal : total ≤ core + boundary)
    (hquadratic :
      core ≤ 5 * epsilon ^ 2 +
        4 * epsilon * Real.sqrt (core + epsilon ^ 2)) :
    total ≤ (2 + Real.sqrt 10) ^ 2 * epsilon ^ 2 := by
  have hcoreBound := core_mass_le hcore hepsilon hquadratic
  have hsqrtTen : Real.sqrt 10 ^ 2 = 10 :=
    Real.sq_sqrt (by norm_num)
  nlinarith

end KassabovTorusNumerics

end GroupApproximation
