import GroupApproximation.Steinberg.RootFiltration

/-!
# Generator actions on the Steinberg root filtration

The direct Steinberg finite-control argument uses shears whose coefficients
are either `1` or a free generator.  The following formulas are consequences
of the defining Steinberg relations and do not pass to the elementary
quotient.
-/

namespace GroupApproximation
namespace SteinbergGroup

open scoped commutatorElement
open FreeAlgebraDegree

variable (X : Type*) [Fintype X]
variable (K : Type*) [CommRing K]

omit [Fintype X] in
/-- The adjacent-root conjugation formula for arbitrary coefficients. -/
theorem conjugate_by_coefficient
    (i j k : Fin 3) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b : FreeAlgebra K X) :
    x i j hij a * x j k hjk b * (x i j hij a)⁻¹ =
      x i k hik (a * b) * x j k hjk b := by
  calc
    x i j hij a * x j k hjk b * (x i j hij a)⁻¹ =
      ⁅x i j hij a, x j k hjk b⁆ * x j k hjk b := by
        rw [commutatorElement_def]
        group
    _ = x i k hik (a * b) * x j k hjk b := by
      rw [x_commutator i j k hij hjk hik]

/-- A commutator with a free generator on the right advances the root
filtration by one degree. -/
theorem commutator_generator_right_mem_succ
    (i j k : Fin 3) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (y : X) {a : FreeAlgebra K X} {n : ℕ} (ha : a ∈ degreeLE X K n) :
    ⁅x i j hij a, x j k hjk (FreeAlgebra.ι K y)⁆ ∈
      rootDegreeSubgroup X K i k hik (n + 1) := by
  rw [x_commutator i j k hij hjk hik]
  exact ⟨a * FreeAlgebra.ι K y,
    mul_generator_mem_degreeLE_succ X K y ha, rfl⟩

/-- A commutator with a free generator on the left advances the root
filtration by one degree. -/
theorem commutator_generator_left_mem_succ
    (i j k : Fin 3) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (y : X) {a : FreeAlgebra K X} {n : ℕ} (ha : a ∈ degreeLE X K n) :
    ⁅x i j hij (FreeAlgebra.ι K y), x j k hjk a⁆ ∈
      rootDegreeSubgroup X K i k hik (n + 1) := by
  rw [x_commutator i j k hij hjk hik]
  exact ⟨FreeAlgebra.ι K y * a,
    generator_mul_mem_degreeLE_succ X K y ha, rfl⟩

omit [Fintype X] in
/-- The exact shear formula underlying the generator stage action. -/
theorem conjugate_by_generator
    (i j k : Fin 3) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (y : X) (a : FreeAlgebra K X) :
    x i j hij (FreeAlgebra.ι K y) * x j k hjk a *
        (x i j hij (FreeAlgebra.ι K y))⁻¹ =
      x i k hik (FreeAlgebra.ι K y * a) * x j k hjk a := by
  exact conjugate_by_coefficient X K i j k hij hjk hik _ _

end SteinbergGroup
end GroupApproximation
