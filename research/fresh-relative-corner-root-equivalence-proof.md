---
rg: 2
id: fresh-relative-corner-root-equivalence-proof
kind: route
title: Compute the free-corner baseline and the pairwise capacity contradiction
target: fresh-relative-corner-contraction-is-root-equivalent
requires: []
artifacts:
  - research/artifacts/fresh-relative-corner-root-equivalence-2026-08-30.md
---

Write `q=sum_(h in H) a_h h`.  Since `q` is a projection,
`a_1=tau(q)=alpha`.  For the fresh reduced word `r=v^(-1)w`,
free-product normal form gives

```text
r^(-1) h r k=1  iff  h=k=1.
```

Consequently, in every group containing the displayed free product embedded,

```text
||q r q||_2^2
 = tau(q r^(-1) q r q)
 = tau(r^(-1) q r q)
 = a_1^2
 = alpha^2.                                           (FRC1)
```

A canonical-profile normalized-HS microstate sequence converges on this
fixed group-ring polynomial, so the left side tends to `alpha^2`.  The
actuator bound instead gives limsup at most `alpha rho^(2L)`.  Since
`rho<1`, choose `L` with `rho^(2L)<alpha`.  The output has no
canonical-profile microstate sequence and is nonhyperlinear.

For the batched target put `Q_i=v_i q v_i^*`.  These are projections of
trace `alpha+o(1)`, and the pairwise bound gives, for `i!=j`,

```text
tau(Q_i Q_j)=||q v_i^*v_j q||_2^2
 <= (alpha+o(1))rho^(2L)+o(1).
```

With `S=sum_i Q_i`, tracial Cauchy--Schwarz gives
`tau(S)^2<=tau(S^2)`.  Passing to the limit yields

```text
M^2 alpha^2 <= M alpha+M(M-1)alpha rho^(2L),
```

or `M(alpha-rho^(2L))<=1-rho^(2L)`.  The choices above contradict this for

```text
M>(1-rho^(2L))/(alpha-rho^(2L)).
```

Conversely, let `N` be an explicit finitely presented nonhyperlinear group.
Given any actuator or pairwise input, take the requested ambient free extension
and free-product it with `N`.  Free-product normal form preserves every input
subgroup and the packet trace.  Map all new free letters and `N` trivially
in the distinguished perfect representation.  Since hyperlinearity passes to
subgroups, the output containing `N` is nonhyperlinear, so every universal
asymptotic microstate inequality holds vacuously.  This is an effective finite
presentation and proves the converse.
