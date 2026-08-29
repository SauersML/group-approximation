import GroupApproximation.Sofic.PhaseOrder

/-!
# A near-scalar unitary is exposed by one of its first four powers

`Sofic.HyperlinearScalar` turns a statement about phases into a statement about
distance: `‖U - τ(U)·1‖² = 1 - |τ(U)|²`, so a unitary whose trace is close to
the unit circle is close to a scalar.  `Sofic.PhaseOrder` supplies the
arithmetic that a scalar cannot evade: no point of the unit circle keeps all of
`ζ, ζ², ζ³, ζ⁴` in the left half plane.  This file chains the two.

  **If `|τ(U)|² ≥ 1 - 10⁻⁶` then `Re τ(U^l) ≥ 1/4` for some `1 ≤ l ≤ 4`.**

The chain is four multiplications long, and each step costs a factor `2` from
the crude triangle inequality `‖A + B‖² ≤ 2‖A‖² + 2‖B‖²`.  Four steps is a
fixed number, chosen before the accuracy is, so the factor `2⁵` is harmless and
no square roots are needed anywhere: the propagation identity is

  `U^{l+1} - τ^{l+1}·1 = U^l (U - τ·1) + τ (U^l - τ^l·1)`,

and left multiplication by the unitary `U^l` and scaling by `τ` (of modulus at
most one) are both norm-nonincreasing, giving `a_{l+1} ≤ 2a_1 + 2a_l` and hence
`a_4 ≤ 22 a_1 = 22(1 - |τ(U)|²)`.

The reading for Pestov's Question 3.4 is `not_forall_re_normTrace_pow_lt`: in a
model separated in the sense of `HyperlinearModel`, every `u_{w^l}` with
`w^l ≠ 1` has `Re τ ≤ ε/2`, so once `ε < 1/2` no element with `w, w², w³, w⁴`
all nontrivial can be sent within `10⁻⁶` of a scalar.  Combined with
`re_nonpos_of_pow_three_eq_one` and `re_nonpos_of_pow_four_eq_one`, which say
the scalars that *do* survive are exactly the roots of unity of order at most
four, the phase obstruction is confined to small torsion.
-/

/-! ## Two computations with the normalized trace -/

/-! ## Propagation of the scalar defect through powers -/

/-! ## The perturbed circle bound -/

/-! ## The propagation theorem -/

/-! ## The model-level statement -/

/-! ## The order-two case: two involutions cannot both carry a phase -/
