---
rg: 2
id: truncated-weyl-two-chart-boundary-proof
kind: route
title: Compute the two symplectic images, their common core, and elementary covariance
target: truncated-weyl-two-chart-boundary
requires:
  - truncated-polynomial-binary-weyl-expander-tower
---

The calculation proving that `P_n` is symplectic in the parent claim is
symmetric in the two coordinates and proves the same for `Q_n`.

Using degree-below-`n+1` representatives, `P_n(V_n)` is cut out by vanishing
of the constant coefficient in the first coordinate and the top coefficient
in the second. The image `Q_n(V_n)` is cut out by the opposite two
conditions. Their intersection therefore has both the constant and top
coefficients zero in each of the appropriate coordinates and has dimension
`2(n-1)`.

In the `P` chart the omitted boundary vectors are `(u^n,0)` and `(0,1)`;
they pair to one and pair trivially with the intersection. In the `Q` chart
they are `(1,0)` and `(0,u^n)`, with the same property. This proves the
nondegenerate common core and the two hyperbolic complements. Equations
`(TWC2)` and `(TWC3)` follow by substitution into `(TWC1)`.

