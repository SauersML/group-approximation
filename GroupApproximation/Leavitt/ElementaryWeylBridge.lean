import GroupApproximation.Leavitt.ElementaryGroup
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.FinCases

/-!
# A scalar Weyl word transports an elementary root in characteristic two

The two-chart Leavitt atlas contains complementary scalar root elements in
its first chart and its aligned rank-three second-chart subgroup.  Their
commutators supply `x₁₂(1)` and `x₂₁(1)`.  The Weyl word
`x₁₂(1)x₂₁(1)x₁₂(1)` swaps the two root directions; in
characteristic two there is no sign correction on the coefficient.
-/

namespace GroupApproximation

open scoped CharTwo

variable {R : Type*} [Ring R] [CharP R 2]

/-- The rank-three scalar Weyl word interchanging coordinates `0` and `1`. -/
def elementaryWeyl01 : (Matrix (Fin 3) (Fin 3) R)ˣ :=
  elementaryUnit 0 1 (by decide) 1 *
  elementaryUnit 1 0 (by decide) 1 *
  elementaryUnit 0 1 (by decide) 1

/-- In characteristic two, conjugation by the scalar Weyl word carries
`x₁₂(a)` to `x₂₁(a)`. -/
theorem elementaryWeyl01_conj (a : R) :
    elementaryWeyl01 * elementaryUnit 0 1 (by decide) a *
      (elementaryWeyl01 : (Matrix (Fin 3) (Fin 3) R)ˣ)⁻¹ =
    elementaryUnit 1 0 (by decide) a := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [elementaryWeyl01, elementaryUnit, Matrix.mul_apply,
      Matrix.one_apply, Fin.sum_univ_succ]

end GroupApproximation
