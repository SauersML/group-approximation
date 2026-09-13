---
rg: 2
id: lawrence-krammer-has-a-faithful-algebraic-unit-specialization
kind: claim
title: For every n the Lawrence–Krammer representation of B_n stays faithful at some pair of algebraic units
---

For every `n >= 3` there are a number field `F` and units `r_0, t_0` of `O_F`
at which the Lawrence–Krammer representation is injective. Here that means
the representation in the form of Cohen–Wales, Theorem 1.2, for type
`A_(n-1)`, with coefficients in `Z[r^{±1}, t^{±1}]`; they describe it as their
generalization of the Lawrence–Krammer representation. The substitution is
`r -> r_0`, `t -> t_0`, giving `B_n -> GL_(n(n-1)/2)(O_F)`.

By `faithful-unit-specialization-gives-z-linearity` this implies
`every-braid-group-embeds-in-some-glnz`, via the route
`braid-z-linearity-via-lkb-unit-specialization`.

## Attempts

1. **One parameter is settled.** Cohen–Wales, Theorem 1.2 (verified from the
   source, see `braid-groups-embed-in-gl-over-integer-laurent-polynomials-proof`),
   is faithful after `r -> r_0` for every real `r_0` with `0 < r_0 < 1`. That
   includes the unit `(3 - sqrt 5)/2`. So `B_n` embeds in `GL_N(Z[phi][t^{±1}])`
   and in `GL_(2N)(Z[t^{±1}])`
   (`braid-groups-embed-in-gl-over-integer-laurent-polynomials`). What remains
   is a unit value `t_0` of the last parameter.
2. **The countability gap.** For `g != 1` the entries of `rho(g) - I` are
   Laurent polynomials in `t`, not all zero, so `g` dies at finitely many
   values `t_0`. The non-faithful values form a countable set, and nothing
   prevents it from containing every algebraic unit.
3. **Why the known faithfulness proof cannot reach a unit value.** Cohen–Wales
   §4 (following Krammer): "0 < r_0 < 1 implies that the constant term of each
   of the entries of the matrices σ_i is a nonnegative real number. This will
   be the same for any product of σ_i", so the positive monoid preserves
   `U = ⊕ (R_≥0 ⊕ tR[t]) x_β`. The sets `U_A` are defined by the support modulo
   `t`. The argument therefore uses the quotient `R[t]/(t) = R` and a
   cancellation-free positive cone in it.
   - Specializing `t -> t_0` in a number ring `O_F` only keeps this structure
     through a quotient `O_F -> O_F/𝔭` with `t_0 ∈ 𝔭`. Then `t_0` is not a
     unit, and the residue field `O_F/𝔭` is finite, so it has no
     cancellation-free positive cone, since `1 + ... + 1 = 0`.
   - An archimedean value `t_0` has no quotient at all.
   So a unit specialization needs a different faithfulness mechanism.
4. **Archimedean smallness is not uniform.** For a real `t_0` close to 0 the
   sign of the constant term decides the sign of an entry only when `t_0` is
   below a bound that depends on the braid and tends to 0 with its length.
