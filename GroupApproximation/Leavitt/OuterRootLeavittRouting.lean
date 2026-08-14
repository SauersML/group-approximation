import GroupApproximation.Leavitt.ElementaryRoots
import GroupApproximation.Leavitt.Leavitt

/-!
# Commuting outer roots retain the binary Leavitt multiplication table

The outer root groups `X₀₁` and `X₂₃` commute.  Inserting the fixed middle
root `x₁₂(1)` nevertheless recovers the coefficient product by a nested
Steinberg commutator.  Specializing the two outer coefficients to
`a tᵢ` and `sⱼ b` gives the complete diagonal-one/cross-zero Leavitt table
while keeping the two measured root packets commuting.
-/

namespace GroupApproximation

open scoped commutatorElement

variable {R : Type*} [Ring R]

/-- The two outer root packets in a four-index chain commute exactly. -/
theorem outerRootPackets_commute (a b : R) :
    Commute
      (elementaryRoot (0 : Fin 4) 1 (by decide) a)
      (elementaryRoot (2 : Fin 4) 3 (by decide) b) :=
  elementaryRoot_commute_of_ne
    (0 : Fin 4) 1 2 3 (by decide) (by decide) (by decide) (by decide) a b

/-- A fixed middle root converts the two commuting outer coefficients into
their product in the long root. -/
theorem outerRoot_middle_nested_commutator (a b c : R) :
    ⁅elementaryRoot (0 : Fin 4) 1 (by decide) a,
      ⁅elementaryRoot (1 : Fin 4) 2 (by decide) b,
        elementaryRoot (2 : Fin 4) 3 (by decide) c⁆⁆ =
      elementaryRoot (0 : Fin 4) 3 (by decide) (a * b * c) := by
  rw [elementaryRoot_commutator, elementaryRoot_commutator]
  simp only [mul_assoc]

/-- The `(t₀,s₀)` outer-root path gives the original coefficient product. -/
theorem leavitt_outerRoot_nested_00 (L : LeavittFamily R) (a b : R) :
    ⁅elementaryRoot (0 : Fin 4) 1 (by decide) (a * L.t0),
      ⁅elementaryRoot (1 : Fin 4) 2 (by decide) 1,
        elementaryRoot (2 : Fin 4) 3 (by decide) (L.s0 * b)⁆⁆ =
      elementaryRoot (0 : Fin 4) 3 (by decide) (a * b) := by
  simpa [mul_assoc] using
    outerRoot_middle_nested_commutator (a * L.t0) (1 : R) (L.s0 * b)

/-- The crossed `(t₀,s₁)` outer-root path vanishes. -/
theorem leavitt_outerRoot_nested_01 (L : LeavittFamily R) (a b : R) :
    ⁅elementaryRoot (0 : Fin 4) 1 (by decide) (a * L.t0),
      ⁅elementaryRoot (1 : Fin 4) 2 (by decide) 1,
        elementaryRoot (2 : Fin 4) 3 (by decide) (L.s1 * b)⁆⁆ = 1 := by
  simpa [mul_assoc] using
    outerRoot_middle_nested_commutator (a * L.t0) (1 : R) (L.s1 * b)

/-- The crossed `(t₁,s₀)` outer-root path vanishes. -/
theorem leavitt_outerRoot_nested_10 (L : LeavittFamily R) (a b : R) :
    ⁅elementaryRoot (0 : Fin 4) 1 (by decide) (a * L.t1),
      ⁅elementaryRoot (1 : Fin 4) 2 (by decide) 1,
        elementaryRoot (2 : Fin 4) 3 (by decide) (L.s0 * b)⁆⁆ = 1 := by
  simpa [mul_assoc] using
    outerRoot_middle_nested_commutator (a * L.t1) (1 : R) (L.s0 * b)

/-- The `(t₁,s₁)` outer-root path gives the original coefficient product. -/
theorem leavitt_outerRoot_nested_11 (L : LeavittFamily R) (a b : R) :
    ⁅elementaryRoot (0 : Fin 4) 1 (by decide) (a * L.t1),
      ⁅elementaryRoot (1 : Fin 4) 2 (by decide) 1,
        elementaryRoot (2 : Fin 4) 3 (by decide) (L.s1 * b)⁆⁆ =
      elementaryRoot (0 : Fin 4) 3 (by decide) (a * b) := by
  simpa [mul_assoc] using
    outerRoot_middle_nested_commutator (a * L.t1) (1 : R) (L.s1 * b)

end GroupApproximation
