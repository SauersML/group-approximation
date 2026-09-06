import GroupApproximation.Analysis.LIXGeneratorUnitary
import GroupApproximation.Analysis.LIXConnectingMap

/-!
# The generator as a `2 × 2` unitary over `X₀`

`Analysis/LIXGeneratorUnitary.lean` builds the seam generator `genU` as a
unitary of `ℂ³` fixing `e₃`, over the equator `{x ∈ S⁵ : Re (x 2) = 0}`.  This
file carries it to the vocabulary the stage algebras use:

* `equatorEmb` identifies `cs-stages`' `S⁴ = Metric.sphere (0 : ℝ⁵) 1` with
  that equator, by the only formula there is,
  `(a₀ + i a₁, a₂ + i a₃, i a₄)`.  This is the ONE place `EuclideanSpace`
  appears; everything upstream of it is stated over the plain product `Fin 3 → ℂ`
  with `dotProduct`, because `Fin 3 → ℂ` carries the sup norm and `‖x‖ = 1`
  would be the wrong condition.
* `genU2` is the `2 × 2` block of `genU`, cut out by the isometry
  `incl : ℂ² → ℂ³` onto `e₃^⊥`.  That `genU` fixes `e₃` makes it
  block-diagonal, which is exactly why the block is again unitary; no rank or
  determinant argument is needed, only that `genU` commutes with the rank-one
  projection onto the pole.

`STW59.blockUnitary 0 · = w₀` then makes a unitary of the stage-zero corner out
of it, which is the `u` of the manuscript's §3.
-/

namespace GroupApproximation
namespace LIX

open scoped Matrix

set_option linter.unusedSectionVars false

noncomputable section

/-! ## The equator of `S⁵` as a copy of `S⁴` -/

/-- The equator embedding `S⁴ ⊆ ℝ⁵ → S⁵ ⊆ ℂ³`, landing in `Re (x 2) = 0`. -/
def equatorEmb (a : EuclideanSpace ℝ (Fin 5)) : Fin 3 → ℂ :=
  ![(a 0 : ℂ) + (a 1 : ℂ) * Complex.I, (a 2 : ℂ) + (a 3 : ℂ) * Complex.I,
    (a 4 : ℂ) * Complex.I]

theorem equatorEmb_zero (a : EuclideanSpace ℝ (Fin 5)) :
    equatorEmb a 0 = (a 0 : ℂ) + (a 1 : ℂ) * Complex.I := rfl

theorem equatorEmb_one (a : EuclideanSpace ℝ (Fin 5)) :
    equatorEmb a 1 = (a 2 : ℂ) + (a 3 : ℂ) * Complex.I := rfl

theorem equatorEmb_two (a : EuclideanSpace ℝ (Fin 5)) :
    equatorEmb a 2 = (a 4 : ℂ) * Complex.I := rfl

/-- The image lies on the equator: the third coordinate is purely imaginary. -/
theorem re_equatorEmb_two (a : EuclideanSpace ℝ (Fin 5)) : (equatorEmb a 2).re = 0 := by
  rw [equatorEmb_two]
  simp [Complex.mul_re]

theorem sum_norm_sq_equatorEmb (a : EuclideanSpace ℝ (Fin 5)) :
    ∑ i, ‖equatorEmb a i‖ ^ 2 = ‖a‖ ^ 2 := by
  have hz : ∀ x y : ℝ, ‖(x : ℂ) + (y : ℂ) * Complex.I‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
    intro x y
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_add_mul_I, Real.norm_eq_abs,
      Real.norm_eq_abs, sq_abs, sq_abs]
  have hi : ∀ y : ℝ, ‖(y : ℂ) * Complex.I‖ ^ 2 = ‖y‖ ^ 2 := by
    intro y
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real]
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, Fin.sum_univ_five,
    equatorEmb_zero, equatorEmb_one, equatorEmb_two, hz, hz, hi]
  ring

theorem equatorEmb_mem {a : EuclideanSpace ℝ (Fin 5)} (ha : a ∈ STW59.sphereFour) :
    equatorEmb a ∈ STW59.unitVectors (Fin 3) := by
  have h1 : ‖a‖ = 1 := mem_sphere_zero_iff_norm.mp ha
  show ∑ i, ‖equatorEmb a i‖ ^ 2 = 1
  rw [sum_norm_sq_equatorEmb, h1, one_pow]

theorem continuous_equatorEmb : Continuous equatorEmb := by
  have h : ∀ k : Fin 5, Continuous fun a : EuclideanSpace ℝ (Fin 5) => ((a k : ℝ) : ℂ) :=
    fun k => Complex.continuous_ofReal.comp (PiLp.continuous_apply 2 (fun _ : Fin 5 => ℝ) k)
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact (h 0).add ((h 1).mul continuous_const)
  · exact (h 2).add ((h 3).mul continuous_const)
  · exact (h 4).mul continuous_const

/-- Both hemisphere frames are defined at every point of the equator. -/
theorem equatorEmb_ne_neg_one (a : EuclideanSpace ℝ (Fin 5)) : equatorEmb a 2 ≠ -1 :=
  ne_neg_one_of_re_eq_zero (re_equatorEmb_two a)

theorem equatorEmb_ne_one (a : EuclideanSpace ℝ (Fin 5)) : equatorEmb a 2 ≠ 1 :=
  ne_one_of_re_eq_zero (re_equatorEmb_two a)

theorem isEquator_equatorEmb {a : EuclideanSpace ℝ (Fin 5)} (ha : a ∈ STW59.sphereFour) :
    IsEquator e3 (equatorEmb a) :=
  isEquator_e3 (equatorEmb_mem ha) (re_equatorEmb_two a)

/-! ## The `2 × 2` block of the generator

`genU x` fixes `e₃`, hence commutes with the rank-one projection onto the
pole, hence is block-diagonal for `ℂ³ = e₃^⊥ ⊕ ℂ e₃`.  Cutting the first block
out with an isometry `incl : ℂ² → ℂ³` therefore lands again on a unitary, and
the proof is four rewrites rather than a rank argument. -/

/-- The isometry of `ℂ²` onto `e₃^⊥ ⊆ ℂ³`. -/
def incl : Matrix (Fin 3) (Fin 2) ℂ :=
  Matrix.of fun i j => if (i : ℕ) = (j : ℕ) then 1 else 0

theorem incl_conjTranspose_mul : inclᴴ * incl = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [incl, Matrix.mul_apply, Fin.sum_univ_three, Matrix.conjTranspose_apply]

theorem incl_mul_conjTranspose : incl * inclᴴ = 1 - rk1 e3 e3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [incl, e3, rk1_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply]

/-- The `2 × 2` block of the seam generator: the manuscript's `u`. -/
def genU2 (x : Fin 3 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ := inclᴴ * genU x * incl

/-- Compressing a unitary that commutes with `incl inclᴴ` by that isometry gives
a unitary.  This is the only content of "`genU` is `diag(u,1)`, so `u` is
unitary": no rank argument, no determinant. -/
theorem conjTranspose_mul_self_of_comm {A : Matrix (Fin 3) (Fin 3) ℂ} (hA : Aᴴ * A = 1)
    (hcomm : A * (incl * inclᴴ) = (incl * inclᴴ) * A) :
    (inclᴴ * A * incl)ᴴ * (inclᴴ * A * incl) = 1 := by
  have h1 : (inclᴴ * A * incl)ᴴ = inclᴴ * Aᴴ * incl := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  rw [h1]
  calc inclᴴ * Aᴴ * incl * (inclᴴ * A * incl)
      = inclᴴ * (Aᴴ * (incl * inclᴴ * A)) * incl := by simp only [Matrix.mul_assoc]
    _ = inclᴴ * (Aᴴ * (A * (incl * inclᴴ))) * incl := by rw [hcomm]
    _ = inclᴴ * (Aᴴ * A * (incl * inclᴴ)) * incl := by simp only [Matrix.mul_assoc]
    _ = inclᴴ * (incl * inclᴴ) * incl := by rw [hA, Matrix.one_mul]
    _ = 1 := by
        simp only [Matrix.mul_assoc]
        rw [incl_conjTranspose_mul, Matrix.mul_one, incl_conjTranspose_mul]

theorem genU2_conjTranspose_mul_self {x : Fin 3 → ℂ}
    (hx : x ∈ STW59.unitVectors (Fin 3)) (hN : x 2 ≠ -1) (hS : x 2 ≠ 1) :
    (genU2 x)ᴴ * genU2 x = 1 := by
  refine conjTranspose_mul_self_of_comm (genU_conjTranspose_mul_self hx hN hS) ?_
  rw [incl_mul_conjTranspose]
  exact genU_comm_compl hx hN hS

theorem genU2_mul_conjTranspose {x : Fin 3 → ℂ}
    (hx : x ∈ STW59.unitVectors (Fin 3)) (hN : x 2 ≠ -1) (hS : x 2 ≠ 1) :
    genU2 x * (genU2 x)ᴴ = 1 :=
  mul_eq_one_comm.mpr (genU2_conjTranspose_mul_self hx hN hS)

theorem continuous_genU2 {X : Type*} [TopologicalSpace X] {ξ : X → Fin 3 → ℂ}
    (hξ : Continuous ξ) (hmem : ∀ s, ξ s ∈ STW59.unitVectors (Fin 3))
    (hN : ∀ s, ξ s 2 ≠ -1) (hS : ∀ s, ξ s 2 ≠ 1) :
    Continuous fun s => genU2 (ξ s) :=
  (continuous_const.matrix_mul (continuous_genU hξ hmem hN hS)).matrix_mul continuous_const

end

end LIX
end GroupApproximation
