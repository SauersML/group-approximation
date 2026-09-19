import GroupApproximation.PropertyTT.Basic

/-!
# Elementary unitary displacement inequalities
-/

namespace GroupApproximation

open scoped commutatorElement

universe u v

variable {G : Type u} [Group G]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Displacement by a product is at most the sum of the two displacements. -/
theorem norm_unitary_mul_sub_le
    (rho : G →* (E ≃ₗᵢ[ℂ] E)) (g h : G) (x : E) :
    ‖rho (g * h) x - x‖ ≤ ‖rho g x - x‖ + ‖rho h x - x‖ := by
  rw [map_mul]
  calc
    ‖(rho g) ((rho h) x) - x‖ =
        ‖(rho g) ((rho h) x - x) + ((rho g) x - x)‖ := by
      congr 1
      simp [map_sub]
    _ ≤ ‖(rho g) ((rho h) x - x)‖ + ‖(rho g) x - x‖ :=
      norm_add_le _ _
    _ = ‖rho h x - x‖ + ‖rho g x - x‖ := by
      rw [(rho g).norm_map]
    _ = ‖rho g x - x‖ + ‖rho h x - x‖ := add_comm _ _

/-- A unitary and its inverse have equal displacement. -/
theorem norm_unitary_inv_sub_eq
    (rho : G →* (E ≃ₗᵢ[ℂ] E)) (g : G) (x : E) :
    ‖rho g⁻¹ x - x‖ = ‖rho g x - x‖ := by
  calc
    ‖rho g⁻¹ x - x‖ = ‖rho g (rho g⁻¹ x - x)‖ :=
      ((rho g).norm_map _).symm
    _ = ‖x - rho g x‖ := by simp [map_sub]
    _ = ‖rho g x - x‖ := norm_sub_rev _ _

/-- Displacement by a commutator is bounded by twice the displacement of
each of its two entries. -/
theorem norm_unitary_commutator_sub_le
    (rho : G →* (E ≃ₗᵢ[ℂ] E)) (g h : G) (x : E) :
    ‖rho ⁅g, h⁆ x - x‖ ≤
      2 * ‖rho g x - x‖ + 2 * ‖rho h x - x‖ := by
  rw [commutatorElement_def]
  calc
    ‖rho (g * h * g⁻¹ * h⁻¹) x - x‖ ≤
        ‖rho (g * h * g⁻¹) x - x‖ + ‖rho h⁻¹ x - x‖ :=
      norm_unitary_mul_sub_le rho _ _ x
    _ ≤ (‖rho (g * h) x - x‖ + ‖rho g⁻¹ x - x‖) +
        ‖rho h⁻¹ x - x‖ := by
      gcongr
      exact norm_unitary_mul_sub_le rho _ _ x
    _ ≤ ((‖rho g x - x‖ + ‖rho h x - x‖) +
        ‖rho g⁻¹ x - x‖) + ‖rho h⁻¹ x - x‖ := by
      gcongr
      exact norm_unitary_mul_sub_le rho _ _ x
    _ = 2 * ‖rho g x - x‖ + 2 * ‖rho h x - x‖ := by
      rw [norm_unitary_inv_sub_eq rho g x,
        norm_unitary_inv_sub_eq rho h x]
      ring

end GroupApproximation
