---
rg: 2
id: stw22-nuclear-type-i-counterexample-trace-problem
kind: claim
title: Problem XXII fails for a separable unital nuclear type I C*-algebra
distinct_from:
  stw22-finite-dimensional-factor-bundles-have-uniform-traces: that theorem is positive over every fixed finite-dimensional base; the counterexample below has compact metrizable Bauer boundary of unbounded covering dimension.
  stw22-fixed-replication-blocks-infinite-dimensional-selection: that claim only obstructs one infinite-dimensional selection strategy; the present claim constructs an actual discontinuous trace and therefore refutes Problem XXII.
artifacts:
  - research/artifacts/stw22-trace-problem-counterexample-audit-2026-08-31.md
---

There exists a separable, unital, nuclear, type I C*-algebra `A` with compact
Bauer trace simplex such that the canonical inclusion

```text
T(A) -> T(overline(A)^{T(A)})
```

is not onto.  Equivalently, the uniform tracial completion of `A` carries a
tracial state that is not continuous for `||.||_(2,T(A))`.

One can take `A` to be the unitization of the `c0`-sum of the homogeneous
algebras

```text
D_s = Gamma(End(1 + L_s^{+s})),       L_s -> CP^(s^2)
```

where `L_s` is the tautological line bundle.  If `p_s` is the trivial rank-one
projection and `q_s` is one tautological rank-one summand, then
`h_s=p_s-q_s` has operator norm one and

```text
||h_s||_2 = sqrt(2/(s+1)) -> 0.
```

For every finite packet in the bounded product of the `D_s`, a top Chern
class forces a late fibre point at which the trivial line reduces every
member of the packet.  The resulting vector state is multiplicative on all
prescribed pairs and takes value one on `(h_s)`.  Weak-star compactness gives
a character of the tail corona that detects `(h_s)` and kills the original
`c0`-sum.  Pulling it back gives a tracial state on the uniform tracial
completion extending the trace at infinity but different from its
uniform-`2`-continuous extension.

Thus STW Problem XXII has a negative answer, already within separable unital
nuclear type I algebras with compact metrizable extreme trace boundary.
