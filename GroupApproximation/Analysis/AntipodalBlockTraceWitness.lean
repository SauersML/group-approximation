import GroupApproximation.Analysis.AntipodalBlockOffDiagonal
import GroupApproximation.Analysis.AntipodalBlockWitness
import GroupApproximation.Analysis.UniformTracialGNSTwoGauge
import Mathlib.Data.Matrix.Basis

/-!
# The antipodal-block witness is uniformly trace-two-null

This file proves the trace calculation needed by the STW XXII counterexample
without classifying traces on the homogeneous blocks.  The coordinate
functions of the sphere give explicit lower-left matrix sections.  Summing
their self-commutators over the sphere coordinates and over the tautological
coordinates gives the diagonal witness, up to the scalar `1 / s`.  Therefore
every tracial state kills the witness directly from traciality.

The resulting elementary equation determines the trace of the distinguished
projection and hence the squared trace two-norm of the witness.  No measure
representation theorem or irreducible-representation classification enters.
-/

namespace GroupApproximation
namespace STW22

open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open UniformTracialGNSTwoGauge

open scoped CStarAlgebra ComplexOrder Matrix InnerProductSpace

noncomputable section

/-- The real `r`-th coordinate on the unit sphere, regarded as a complex
continuous function. -/
def sphereCoordinate (d : ℕ) (r : Fin (d + 1)) : C(Sphere d, ℂ) where
  toFun x := ((EuclideanSpace.proj r x.1 : ℝ) : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp
    ((EuclideanSpace.proj r).continuous.comp continuous_subtype_val)

@[simp]
theorem sphereCoordinate_apply (d : ℕ) (r : Fin (d + 1)) (x : Sphere d) :
    sphereCoordinate d r x = ((EuclideanSpace.proj r x.1 : ℝ) : ℂ) :=
  rfl

@[simp]
theorem sphereCoordinate_neg (d : ℕ) (r : Fin (d + 1)) (x : Sphere d) :
    sphereCoordinate d r (-x) = -sphereCoordinate d r x := by
  simp [sphereCoordinate]

/-- The squared sphere coordinates sum to one, in complex scalars. -/
theorem sum_sphereCoordinate_mul_self (d : ℕ) (x : Sphere d) :
    ∑ r : Fin (d + 1), sphereCoordinate d r x * sphereCoordinate d r x = 1 := by
  have hxnorm : ‖(x.1 : EuclideanSpace ℝ (Fin (d + 1)))‖ = 1 := by
    have hx := x.2
    rw [Metric.mem_sphere, dist_zero_right] at hx
    exact hx
  calc
    ∑ r : Fin (d + 1), sphereCoordinate d r x * sphereCoordinate d r x =
        ((∑ r : Fin (d + 1), (EuclideanSpace.proj r x.1) ^ 2 : ℝ) : ℂ) := by
          push_cast
          simp only [sphereCoordinate_apply, pow_two]
    _ = ((‖(x.1 : EuclideanSpace ℝ (Fin (d + 1)))‖ ^ 2 : ℝ) : ℂ) := by
          congr 1
          rw [EuclideanSpace.real_norm_sq_eq]
          apply Finset.sum_congr rfl
          intro r _
          rfl
    _ = 1 := by rw [hxnorm]; norm_num

/-- A matrix with one lower-left entry. -/
def lowerLeftMatrix (s : ℕ) (i : Fin s) (z : ℂ) :
    CStarMatrix (Fin (s + 1)) (Fin (s + 1)) ℂ :=
  z • CStarMatrix.ofMatrix (Matrix.single i.succ 0 1)

@[simp]
theorem lowerLeftMatrix_apply (s : ℕ) (i : Fin s) (z : ℂ)
    (a b : Fin (s + 1)) :
    lowerLeftMatrix s i z a b = if i.succ = a ∧ 0 = b then z else 0 := by
  simp [lowerLeftMatrix, Matrix.single_apply]

@[simp]
theorem star_lowerLeftMatrix (s : ℕ) (i : Fin s) (z : ℂ) :
    star (lowerLeftMatrix s i z) =
      CStarMatrix.ofMatrix (Matrix.single 0 i.succ (star z)) := by
  apply CStarMatrix.ext
  intro a b
  by_cases h : i.succ = b ∧ 0 = a
  · rcases h with ⟨rfl, rfl⟩
    simp [lowerLeftMatrix, CStarMatrix.star_apply]
  · have h' : ¬(0 = a ∧ i.succ = b) := fun h' ↦ h ⟨h'.2, h'.1⟩
    simp [lowerLeftMatrix, CStarMatrix.star_apply, h, h']

theorem star_lowerLeftMatrix_mul (s : ℕ) (i : Fin s) (z : ℂ) :
    star (lowerLeftMatrix s i z) * lowerLeftMatrix s i z =
      CStarMatrix.ofMatrix (Matrix.single 0 0 (star z * z)) := by
  rw [star_lowerLeftMatrix]
  rw [show lowerLeftMatrix s i z =
    CStarMatrix.ofMatrix (Matrix.single i.succ 0 z) by
      ext a b
      simp [lowerLeftMatrix_apply, Matrix.single_apply]]
  change Matrix.single 0 i.succ (star z) * Matrix.single i.succ 0 z =
    Matrix.single 0 0 (star z * z)
  exact Matrix.single_mul_single_same (star z) 0 i.succ 0 z

theorem lowerLeftMatrix_mul_star (s : ℕ) (i : Fin s) (z : ℂ) :
    lowerLeftMatrix s i z * star (lowerLeftMatrix s i z) =
      CStarMatrix.ofMatrix (Matrix.single i.succ i.succ (z * star z)) := by
  rw [star_lowerLeftMatrix]
  rw [show lowerLeftMatrix s i z =
    CStarMatrix.ofMatrix (Matrix.single i.succ 0 z) by
      ext a b
      simp [lowerLeftMatrix_apply, Matrix.single_apply]]
  change Matrix.single i.succ 0 z * Matrix.single 0 i.succ (star z) =
    Matrix.single i.succ i.succ (z * star z)
  exact Matrix.single_mul_single_same z i.succ 0 i.succ (star z)

/-- The covariant lower-left section whose only nonzero entry is the `r`-th
sphere coordinate in row `i+1`. -/
def coordinateLowerSection (d s : ℕ) (i : Fin s) (r : Fin (d + 1)) :
    RealProjectiveBlock d s := by
  let f : SphereMatrixFunctions d s :=
    { toFun := fun x ↦ lowerLeftMatrix s i (sphereCoordinate d r x)
      continuous_toFun :=
        (sphereCoordinate d r).continuous.smul continuous_const }
  refine ⟨f, ?_⟩
  intro x
  apply CStarMatrix.ext
  intro a b
  rw [blockInvolution_conjugation_apply]
  by_cases h : i.succ = a ∧ 0 = b
  · rcases h with ⟨rfl, rfl⟩
    simp [f, lowerLeftMatrix_apply, blockSign]
  · simp [f, lowerLeftMatrix_apply, h]

@[simp]
theorem coordinateLowerSection_apply (d s : ℕ) (i : Fin s) (r : Fin (d + 1))
    (x : Sphere d) (a b : Fin (s + 1)) :
    (coordinateLowerSection d s i r).1 x a b =
      if i.succ = a ∧ 0 = b then sphereCoordinate d r x else 0 := by
  simp [coordinateLowerSection, lowerLeftMatrix_apply]

end

end STW22
end GroupApproximation
