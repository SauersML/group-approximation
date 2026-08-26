import GroupApproximation.PropertyT.IntegralColumnPlaneReduction

/-!
# Root estimates supplied directly by the integral control set

The integral control set contains the unit coefficient and every free
generator coefficient in every elementary root.  The elementary commutator
recursion therefore controls every word-monomial coefficient.  Its constant
grows exponentially with word length, so this estimate does not prove the
uniform `RootCoefficientDisplacementBound` isolated in
`IntegralColumnPlaneReduction`.

This file records that exact boundary without introducing a second definition
of the single-root displacement problem.
-/

namespace GroupApproximation

universe u v

namespace IntegralColumnPlaneRootReduction

open IntegralCharacterMass IntegralColumnPlaneReduction

/-- Near invariance under the integral control set includes near invariance
under the unit coefficient in every elementary root. -/
theorem norm_integral_unitRoot_displacement_lt_of_controlSet_near
    (X : Type u) [Fintype X]
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (rho : elementaryGroup (Fin 3) (FreeAlgebra ℤ X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (delta : ℝ)
    (hnear : ∀ s ∈ integralControlSet X, ‖rho s z - z‖ < delta)
    (i j : Fin 3) (hij : i ≠ j) :
    ‖rho (elementaryRoot i j hij 1) z - z‖ < delta := by
  let a : A2Root := ⟨(i, j), hij⟩
  let p : A2Root × Option X := (a, none)
  have hp := hnear (integralControlElement X p)
    (integralControlElement_mem X p)
  simpa [p, a, integralControlElement, integralControlCoefficient] using hp

/-- Near invariance under the integral control set includes near invariance
under every free-generator coefficient in every elementary root. -/
theorem norm_integral_generatorRoot_displacement_lt_of_controlSet_near
    (X : Type u) [Fintype X]
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (rho : elementaryGroup (Fin 3) (FreeAlgebra ℤ X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (delta : ℝ)
    (hnear : ∀ s ∈ integralControlSet X, ‖rho s z - z‖ < delta)
    (i j : Fin 3) (hij : i ≠ j) (x : X) :
    ‖rho (elementaryRoot i j hij (FreeAlgebra.ι ℤ x)) z - z‖ < delta := by
  let a : A2Root := ⟨(i, j), hij⟩
  let p : A2Root × Option X := (a, some x)
  have hp := hnear (integralControlElement X p)
    (integralControlElement_mem X p)
  simpa [p, a, integralControlElement, integralControlCoefficient] using hp

/-- The commutator recursion applied directly to the integral control set.
It controls a word-monomial root, but its constant grows exponentially with
the word length and therefore does not give
`RootCoefficientDisplacementBound`. -/
theorem norm_integral_wordMonomial_displacement_le_of_controlSet_near
    (X : Type u) [Fintype X]
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (rho : elementaryGroup (Fin 3) (FreeAlgebra ℤ X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (delta : ℝ)
    (hnear : ∀ s ∈ integralControlSet X, ‖rho s z - z‖ < delta)
    (w : FreeMonoid X) (i j : Fin 3) (hij : i ≠ j) :
    ‖rho (elementaryRoot i j hij
        (FreeAlgebraDegree.wordMonomial X ℤ w)) z - z‖ ≤
      (3 * 2 ^ (FreeAlgebraDegree.freeWordLength X w) - 2) * delta := by
  exact norm_displacement_wordMonomial_le X ℤ rho z delta
    (fun i j hij ↦
      (norm_integral_unitRoot_displacement_lt_of_controlSet_near
        X rho z delta hnear i j hij).le)
    (fun i j hij x ↦
      (norm_integral_generatorRoot_displacement_lt_of_controlSet_near
        X rho z delta hnear i j hij x).le)
    w i j hij

end IntegralColumnPlaneRootReduction

end GroupApproximation
