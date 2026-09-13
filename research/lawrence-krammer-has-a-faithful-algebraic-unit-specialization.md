---
rg: 2
id: lawrence-krammer-has-a-faithful-algebraic-unit-specialization
kind: claim
title: For every n the Lawrence–Krammer representation of B_n stays faithful at some pair of algebraic units
---

For every `n >= 3` there are a number field `F` and units `q_0, t_0` of `O_F`
such that the Lawrence–Krammer representation
`B_n -> GL_(n(n-1)/2)(Z[q^{±1}, t^{±1}])`, specialized at `q -> q_0` and
`t -> t_0`, is injective.

By `faithful-unit-specialization-gives-z-linearity` this implies
`every-braid-group-embeds-in-some-glnz`; the route is
`braid-z-linearity-via-lkb-unit-specialization`.

## Attempts

1. **What faithfulness is known for.** Bigelow (2001) and Krammer (2002)
   prove faithfulness over `Z[q^{±1}, t^{±1}]`, equivalently for algebraically
   independent complex values of `q, t`. Krammer's proof specializes one
   parameter to a real number in `(0, 1)` and keeps the other formal, and
   Cohen–Wales record the same shape for spherical Artin groups (graph node
   `spherical-artin-groups-are-linear-over-q-x-y`: faithful after `r -> r_0`,
   `0 < r_0 < 1`). The exact hypothesis on the real parameter is being checked
   from the sources. If an algebraic value is allowed, a unit such as
   `(3 - sqrt 5)/2 ∈ (0, 1)` settles one parameter, and the claim reduces to a
   single formal parameter.
2. **The countability gap.** Fix the first parameter and let `rho` be faithful
   over `O[t^{±1}]`. For `g != 1` the entries of `rho(g) - I` are Laurent
   polynomials in `t`, not all zero, so `rho_(t_0)(g) = I` for only finitely
   many `t_0`. The set of `t_0` where `rho_(t_0)` fails to be faithful is
   therefore countable. The algebraic units are countable too, so this argument
   gives nothing.
3. **Why the known proofs need a transcendental parameter.** Krammer's
   argument orders `R[q^{±1}]` by the sign of the lowest-order coefficient,
   which makes `q` infinitesimal. A number field has only archimedean
   orderings, so there are no infinitesimals. Evaluating at a small real `q_0`
   keeps each needed sign only when `q_0` is smaller than a bound depending on
   the braid, and that bound goes to 0 with braid length.
4. **Idea to test: valuations instead of orderings.** Replace the ordering by
   a `p`-adic valuation with `q -> p`. Even if the cone argument transfers, the
   image lies in `GL(O_F[1/p])`, since `q^{-1} = 1/p` appears in the
   generators' inverses. That is not integral. It would give linearity of `B_n`
   over a number field, which is also not yet recorded in the graph.
