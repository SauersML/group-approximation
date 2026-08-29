import GroupApproximation.Sofic.HyperlinearScalar

/-!
# A phase cannot hide from its first four powers

`Sofic.HyperlinearScalar` shows that a unitary whose normalized trace has
modulus near `1` is near a scalar, so the phase obstruction of
`Sofic.HyperlinearAmplification` can be propagated through powers.  This file
supplies the arithmetic fact that makes propagation bite.

A model separated in the sense of `HyperlinearModel` has `Re τ(u_g u_h^*) ≤ ε/2`
for distinct `g, h`, so if `u_w` is close to the scalar `ζ` then *every* power
`ζ^l` with `w^l ≠ 1` is confined to the left half plane.  The point is that
**no point of the unit circle can keep its first four powers there**:

  `max (Re ζ, Re ζ², Re ζ³, Re ζ⁴) ≥ 3/10`   (`re_pow_max_ge`).

Writing `x = Re ζ`, the four real parts are the Chebyshev polynomials
`x`, `2x² - 1`, `4x³ - 3x`, `8x⁴ - 8x² + 1`, so this is a statement about one
real variable on `[-1, 1]`.  The minimum of the maximum is `≈ 0.3106`, attained
where the second and third cross at `x ≈ -0.8095`; `3/10` is that value with a
little room.

Four powers are needed and no fewer: `ζ = i` keeps `Re ζ, Re ζ², Re ζ³` all
`≤ 0`, and only the fourth power returns to `1`.  The elements a strong model
*can* send to a scalar are therefore exactly those of order at most `4` --
`-1`, `±i` and the primitive cube roots, whose nontrivial powers all have
nonpositive real part.  So the phase obstruction to Pestov's Question 3.4 is
confined to small torsion.
-/

/-! ## Which scalars remain available -/

/-! ## The constant is essentially optimal -/
