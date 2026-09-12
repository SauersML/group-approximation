import GroupApproximation.Sofic.LiteralP13Presentation
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# The exact matrix model of the P13 presentation

The thirteen-relator presentation `P13` is the Steinberg-type presentation
of rank three: six elementary generators, six ordered Steinberg
commutators, six commuting-root commutators, and the relator
`(e₁₂ e₂₁⁻¹ e₁₂)⁴`.  This file realizes it on the actual special linear
group: the assignment `e_ij ↦ 1 + E_ij` kills all thirteen relators by
kernel-checked integer arithmetic, giving the canonical homomorphism

  `toSL3 : P13 →* SL₃(ℤ)`.

The completeness programme built on this map has two halves, recorded
here for orientation only and asserted nowhere: surjectivity is
elementary generation of `SL₃(ℤ)` (Gaussian elimination over a Euclidean
domain), and injectivity is the unstable `K₂(3,ℤ) = ℤ/2` computation,
with the extra relator killing the Steinberg central element
`{-1,-1} = (e₁₂ e₂₁⁻¹ e₁₂)⁴`.  Later files will prove both; nothing in
the present development assumes either.
-/

namespace GroupApproximation
namespace LiteralP13MatrixModel

open LiteralP13Presentation PresentedGroupRelatorReplay

/-- The concrete rank-three special linear group over the integers. -/
abbrev SL3 : Type := Matrix.SpecialLinearGroup (Fin 3) ℤ

/-- The six elementary matrices, in the exact certificate order
`e12, e13, e21, e23, e31, e32`. -/
def elem : Fin 6 → SL3
  | 0 => ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide⟩
  | 1 => ⟨!![1, 0, 1; 0, 1, 0; 0, 0, 1], by decide⟩
  | 2 => ⟨!![1, 0, 0; 1, 1, 0; 0, 0, 1], by decide⟩
  | 3 => ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by decide⟩
  | 4 => ⟨!![1, 0, 0; 0, 1, 0; 1, 0, 1], by decide⟩
  | 5 => ⟨!![1, 0, 0; 0, 1, 0; 0, 1, 1], by decide⟩

/-- Every P13 relator dies under the elementary assignment.  Each instance
is a closed identity of `3 × 3` integer matrices, checked by the kernel. -/
theorem lift_elem_relator_eq_one (i : Fin 13) :
    FreeGroup.lift elem (p13Relator i) = 1 := by
  fin_cases i <;>
    · simp only [p13Relator, p13RelatorLetters, word, FreeGroup.lift_mk]
      decide

theorem lift_elem_eq_one_of_mem {r : FreeGroup P13Generator}
    (hr : r ∈ (p13Relators : Set (FreeGroup P13Generator))) :
    FreeGroup.lift elem r = 1 := by
  obtain ⟨i, rfl⟩ := (mem_p13Relators_iff r).mp hr
  exact lift_elem_relator_eq_one i

/-- The canonical homomorphism from the presented group to the actual
special linear group. -/
noncomputable def toSL3 : P13 →* SL3 :=
  PresentedGroup.toGroup (f := elem) fun _ hr => lift_elem_eq_one_of_mem hr

@[simp] theorem toSL3_of (i : P13Generator) :
    toSL3 (PresentedGroup.of i) = elem i :=
  PresentedGroup.toGroup.of _

end LiteralP13MatrixModel
end GroupApproximation
