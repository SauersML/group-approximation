---
rg: 2
id: kl-via-magnus-near-identity-fixed-point
kind: route
title: Solve the equation by a fixed point in a complete filtered ring
target: kervaire-laudenbach-nonsingular-conjecture
requires: []
artifacts:
  - research/artifacts/kervaire-laudenbach-audit-2026-08-17.md
---

Embed the coefficient group near the identity of a complete filtered ring —
a Magnus embedding, a power-series algebra, a pro-nilpotent completion — and
solve `w(t) = 1` by successive approximation, the filtration supplying the
contraction.  Nonsingularity is what makes the linearization non-degenerate:
to first order the `t`-dependence of `w` is multiplication by
`deg_t(w) = m != 0`, so there is a correction step to iterate.  This is
the most natural universal construction anyone proposes for this conjecture,
and it works in the cases where it applies.

Dead: it can never apply where the problem lives.  By
`near-identity-embedding-forces-residual-nilpotence` a group faithfully
represented in `1 + I` for a separated multiplicative filtration is
residually nilpotent, and by
`kl-counterexample-can-be-two-generator-simple` every hypothetical
counterexample can be taken simple, hence perfect, hence not residually
nilpotent unless trivial.  The construction and the reduction address
disjoint classes of coefficient group.

**What survives the demolition.**  Everything about the method for
residually nilpotent coefficients, where it remains a genuine proof
technique; and the first-order observation itself, which is why
nonsingularity is the right hypothesis in every approach here.  What dies is
only the claim to universality.
