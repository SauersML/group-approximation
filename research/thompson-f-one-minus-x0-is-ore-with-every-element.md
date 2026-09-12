---
rg: 2
id: thompson-f-one-minus-x0-is-ore-with-every-element
kind: claim
title: In the group ring of Thompson's group F, 1 - x_0 has a nonzero common right multiple with every nonzero element
distinct_from:
  thompson-f-binomial-pairs-have-common-multiples: that handles 1 - h against binomials, for every h; this handles the single element 1 - x_0 against every element of K[F], using the shift structure of the positive monoid.
  thompson-f-amenable-iff-group-ring-is-ore: that is the Ore condition for all pairs, equivalent to amenability; this is the Ore condition for all pairs with one side equal to 1 - x_0.
---

**ESTABLISHED.** Let `K` be a field, `R = K[F]`, and `x_0, x_1, ...` the standard
generators, with `x_j x_i = x_i x_(j+1)` for `i < j`. For every nonzero `b` in `R`,
`(1 - x_0) R ∩ b R ≠ 0`.

**Source.** V. Guba, *Systems of equations over the group ring of Thompson's group F*,
arXiv:2201.02308 (Comm. Algebra 50:12 (2022)), Theorem 2, verbatim. The survey
arXiv:2305.07113v4 restates it as Theorem 3.18.

> Let R = K[F] be a group ring of F over a field K. Then for any element b∈R, the
> equation (1−x0)u = bv has a non-zero solution in R.

The graph also carries a second proof. It keeps Guba's reduction to `K[M_1]` and his shift
by `x_0`, and replaces his Theorem 3 (non-freeness of `{phi^k(b)}`, proved by induction on
homogeneous components) with a dimension count.

**Consequence.** No non-Ore witness for `thompson-f-is-not-amenable` has `1 - x_0` on one
side. By conjugation invariance (`(1 - g^-1 h g) R = g^-1 (1 - h) R` together with
`b -> g b`), the same holds for every conjugate of `x_0^{+-1}`.

**Scope.**
- The survey statement was read from the extracted PDF of arXiv:2305.07113v4. The 2022
  paper was not read.
- The counting proof on this graph is self-contained apart from the normal form of the
  positive monoid.

Routes: `thompson-f-one-minus-x0-is-ore-with-every-element-citation`,
`thompson-f-one-minus-x0-is-ore-with-every-element-proof`.
