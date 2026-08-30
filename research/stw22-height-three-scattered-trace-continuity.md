---
rg: 2
id: stw22-height-three-scattered-trace-continuity
kind: claim
title: Two-level damping eliminates every fibre-gap trace over a height-three scattered base
distinct_from:
  stw22-rank-one-scattered-fibre-gaps-are-tracefree: that theorem handles a single discrete punctured neighbourhood; the present theorem passes through a quotient onto the rank-one skeleton and kills its kernel with damped, rather than continuous, fibrewise orthogonalizers.
  stw22-nuclear-convergent-sequence-has-nonzero-tracefree-gap: that theorem treats one sequence of factor coordinates; the present theorem treats a sequence of convergent-sequence blocks and resolves the extra continuity condition at every inner limit point.
artifacts:
  - research/artifacts/stw22-height-three-two-level-damping-audit-2026-08-30.md
---

Let `X` be compact, metrizable, and scattered with

```text
X^(3)=emptyset.
```

Let `U` be an infinite-dimensional UHF algebra with unique trace, and let
`M` be the uniform tracial completion of `C(X) tensor U`.  Then every
norm/`2`-norm fibre gap

```text
K_x/J_x
```

has no nonzero bounded positive trace.  Consequently every tracial state on
`M` is uniquely of the form

```text
a |-> integral_X tau(a(t)) dmu(t)
```

for a probability measure `mu` on `X`, and hence is continuous for the
uniform `2`-norm.

The new case is a point of Cantor--Bendixson rank two.  A clopen
neighbourhood of such a point is a convergent sequence of compact clopen
blocks, each block having at most one nonisolated point.  Evaluation at one
distinguished point in each block maps the rank-two gap onto the rank-one
cofinite corona.  Its kernel is bounded-trace-free: after making a positive
representative vanish at every distinguished point, arbitrary pointwise
orthogonalizers become continuous when multiplied by the square root of a
spectral cut.  Thus both the quotient and kernel are bounded-trace-free.

This is an unconditional height-three result for the trivial UHF field.  It
does not assert the same conclusion for a nontrivial tracial bundle or for
arbitrary Cantor--Bendixson height.
