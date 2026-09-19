import GroupApproximation.PropertyT.IntegralColumnPlaneRootReduction

/-!
# Pointwise displacement bounds for integral free polynomials

The unresolved integral column-plane estimate asks for one displacement
constant that is uniform over every coefficient of `ℤ⟨X⟩`.  This file proves
the strongest direct consequence of the elementary commutator calculation:
every *fixed* coefficient has an explicit bound in terms of the integer
coefficients and word lengths in its canonical finite support.

The proof has three elementary parts.  Displacement is subadditive under
addition of root coefficients, an integer multiple costs at most its absolute
value, and the Steinberg commutator recursion supplies the existing word
monomial bound.  The resulting constant is finite for each polynomial, but is
unbounded as the polynomial varies.  Thus this is genuine pointwise control,
not the missing uniform `RootCoefficientDisplacementBound` and not a disguised
literature input.
-/

namespace GroupApproximation

universe u v

namespace IntegralPolynomialDisplacement

open IntegralCharacterMass IntegralColumnPlaneRootReduction
open FreeAlgebraDegree

variable {G : Type u} [Group G]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Displacement length on an additive root -/

/-- Displacement by a positive power is at most the exponent times the
displacement by the original element. -/
theorem norm_pow_displacement_le
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (z : E) (g : G) (n : ℕ) :
    ‖rho (g ^ n) z - z‖ ≤ (n : ℝ) * ‖rho g z - z‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        ‖rho (g ^ (n + 1)) z - z‖ = ‖rho (g ^ n * g) z - z‖ := by
          rw [pow_succ]
        _ ≤ ‖rho (g ^ n) z - z‖ + ‖rho g z - z‖ :=
          A2System.norm_mul_displacement_le rho z (g ^ n) g
        _ ≤ (n : ℝ) * ‖rho g z - z‖ + ‖rho g z - z‖ :=
          add_le_add ih le_rfl
        _ = (n + 1 : ℕ) * ‖rho g z - z‖ := by
          push_cast
          ring

/-- The elementary root of a natural multiple is the corresponding power of
the elementary root. -/
theorem elementaryRoot_nsmul {R : Type u} [Ring R]
    (i j : Fin 3) (hij : i ≠ j) (a : R) (n : ℕ) :
    elementaryRoot i j hij (n • a) = elementaryRoot i j hij a ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [succ_nsmul, ← elementaryRoot_mul i j hij, ih, pow_succ]

/-- An integer multiple of a root coefficient costs at most the absolute
value of the integer. -/
theorem norm_elementaryRoot_zsmul_displacement_le
    {R : Type u} [Ring R]
    (rho : elementaryGroup (Fin 3) R →* (E ≃ₗᵢ[ℝ] E)) (z : E)
    (i j : Fin 3) (hij : i ≠ j) (a : R) (m : ℤ) :
    ‖rho (elementaryRoot i j hij (m • a)) z - z‖ ≤
      (m.natAbs : ℝ) * ‖rho (elementaryRoot i j hij a) z - z‖ := by
  cases m with
  | ofNat n =>
      have h : ‖rho (elementaryRoot i j hij (n • a)) z - z‖ ≤
          (n : ℝ) * ‖rho (elementaryRoot i j hij a) z - z‖ := by
        rw [elementaryRoot_nsmul]
        exact norm_pow_displacement_le rho z (elementaryRoot i j hij a) n
      simpa [Int.natAbs] using h
  | negSucc n =>
      have hpos :
          ‖rho (elementaryRoot i j hij ((n + 1) • a)) z - z‖ ≤
            (n + 1 : ℕ) * ‖rho (elementaryRoot i j hij a) z - z‖ := by
        rw [elementaryRoot_nsmul]
        exact norm_pow_displacement_le rho z
          (elementaryRoot i j hij a) (n + 1)
      have hneg :
          ‖rho (elementaryRoot i j hij (-((n + 1) • a))) z - z‖ ≤
            (n + 1 : ℕ) * ‖rho (elementaryRoot i j hij a) z - z‖ := by
        rw [elementaryRoot_neg,
          IntegralCharacterMass.norm_inv_displacement]
        exact hpos
      have hm : (Int.negSucc n : ℤ) • a = -((n + 1) • a) := by
        exact negSucc_zsmul a n
      rw [hm]
      simpa [Int.natAbs] using hneg

/-- Displacement by the root of a finite sum is at most the sum of the
individual root displacements. -/
theorem norm_elementaryRoot_finset_sum_displacement_le
    {R : Type u} [Ring R] {A : Type*}
    (rho : elementaryGroup (Fin 3) R →* (E ≃ₗᵢ[ℝ] E)) (z : E)
    (i j : Fin 3) (hij : i ≠ j) (s : Finset A) (f : A → R) :
    ‖rho (elementaryRoot i j hij (∑ a ∈ s, f a)) z - z‖ ≤
      ∑ a ∈ s, ‖rho (elementaryRoot i j hij (f a)) z - z‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        ← elementaryRoot_mul i j hij]
      exact (A2System.norm_mul_displacement_le rho z
        (elementaryRoot i j hij (f a))
        (elementaryRoot i j hij (∑ b ∈ s, f b))).trans
          (add_le_add le_rfl ih)

/-! ### Canonical finite-support bound -/

/-- Near invariance under the integral control set gives an explicit
displacement bound for the root of any fixed integral free polynomial.  The
weight of a supported word is its coefficient's absolute value times the
commutator-recursion cost for its length. -/
theorem norm_integral_polynomial_displacement_le_of_controlSet_near
    (X : Type u) [Fintype X]
    (rho : elementaryGroup (Fin 3) (FreeAlgebra ℤ X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (delta : ℝ)
    (hnear : ∀ s ∈ integralControlSet X, ‖rho s z - z‖ < delta)
    (p : FreeAlgebra ℤ X) (i j : Fin 3) (hij : i ≠ j) :
    ‖rho (elementaryRoot i j hij p) z - z‖ ≤
      ∑ w ∈ (FreeAlgebra.equivMonoidAlgebraFreeMonoid
          (R := ℤ) (X := X) p).coeff.support,
        ((FreeAlgebra.equivMonoidAlgebraFreeMonoid
            (R := ℤ) (X := X) p).coeff w).natAbs *
          (3 * 2 ^ freeWordLength X w - 2) * delta := by
  classical
  let c := (FreeAlgebra.equivMonoidAlgebraFreeMonoid
    (R := ℤ) (X := X) p).coeff
  let T := c.support
  have hp : p = ∑ w ∈ T, c w • wordMonomial X ℤ w := by
    exact eq_sum_support_smul_wordMonomial X ℤ p
  conv_lhs => rw [hp]
  refine (norm_elementaryRoot_finset_sum_displacement_le
    rho z i j hij T (fun w ↦ c w • wordMonomial X ℤ w)).trans ?_
  apply Finset.sum_le_sum
  intro w hw
  calc
    ‖rho (elementaryRoot i j hij (c w • wordMonomial X ℤ w)) z - z‖ ≤
        (c w).natAbs *
          ‖rho (elementaryRoot i j hij (wordMonomial X ℤ w)) z - z‖ :=
      norm_elementaryRoot_zsmul_displacement_le rho z i j hij
        (wordMonomial X ℤ w) (c w)
    _ ≤ (c w).natAbs *
        ((3 * 2 ^ freeWordLength X w - 2) * delta) :=
      mul_le_mul_of_nonneg_left
        (norm_integral_wordMonomial_displacement_le_of_controlSet_near
          X rho z delta hnear w i j hij)
        (Nat.cast_nonneg _)
    _ = (c w).natAbs * (3 * 2 ^ freeWordLength X w - 2) * delta := by
      ring

/-- Pointwise form of the preceding result: every fixed integral free
polynomial has a finite displacement constant, uniform in the root indices
and the represented Hilbert space.  The constant still depends on the
polynomial, which is exactly why this does not close the column-plane bound. -/
theorem exists_integral_polynomial_displacement_constant
    (X : Type u) [Fintype X] (p : FreeAlgebra ℤ X) :
    ∃ C : ℝ, ∀ (E : Type v) [NormedAddCommGroup E]
      [InnerProductSpace ℝ E],
      ∀ (rho : elementaryGroup (Fin 3) (FreeAlgebra ℤ X) →* (E ≃ₗᵢ[ℝ] E))
        (z : E) (delta : ℝ),
        (∀ s ∈ integralControlSet X, ‖rho s z - z‖ < delta) →
          ∀ (i j : Fin 3) (hij : i ≠ j),
            ‖rho (elementaryRoot i j hij p) z - z‖ ≤ C * delta := by
  classical
  refine ⟨∑ w ∈ (FreeAlgebra.equivMonoidAlgebraFreeMonoid
      (R := ℤ) (X := X) p).coeff.support,
        ((FreeAlgebra.equivMonoidAlgebraFreeMonoid
          (R := ℤ) (X := X) p).coeff w).natAbs *
            (3 * 2 ^ freeWordLength X w - 2), ?_⟩
  intro E _ _ rho z delta hnear i j hij
  simpa [Finset.sum_mul] using
    norm_integral_polynomial_displacement_le_of_controlSet_near
      X rho z delta hnear p i j hij

end IntegralPolynomialDisplacement

end GroupApproximation
