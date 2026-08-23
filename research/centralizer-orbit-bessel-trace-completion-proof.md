---
rg: 2
id: centralizer-orbit-bessel-trace-completion-proof
kind: route
title: Apply Bessel to an infinite orthonormal centralizer orbit of each mixed word
target: centralizer-aperiodic-haar-actor-marginals-force-regular-trace
requires: []
---

Fix `a != 0` and `g != e`. By `(CAM1)`, choose `h_n in C_H(g)` such that
the elements `b_n=h_n.a` are pairwise distinct. Traciality and covariance
give one common mixed coefficient

```text
tau(V_(b_n) U_g)
 = tau(U_(h_n) V_a U_g U_(h_n)^*)
 = tau(V_a U_g).                                      (COB1)
```

The vectors `x_n=V_(b_n)U_g` are orthonormal in `L^2(Q,tau)`, because for
`m != n`,

```text
<x_m,x_n>
 = tau(U_g^* V_(b_n-b_m) U_g)
 = tau(V_(g^(-1).(b_n-b_m)))=0.                       (COB2)
```

Here the last equality is the lamp marginal in `(CAM3)`. Each `x_n` has norm
one. Their inner products with the unit vector `1` all equal the scalar in
`(COB1)`, up to the irrelevant choice of inner-product convention. Bessel's
inequality for the first `N` vectors therefore gives

```text
N |tau(V_a U_g)|^2 <= 1
```

for every `N`, so `tau(V_aU_g)=0`. The cases `a=0` or `g=e` are exactly the
two marginal laws `(CAM3)`, proving `(CAM4)`.

The integrated homomorphism from `C[A rtimes H]` into `Q` now preserves the
canonical group trace. Hence it is isometric for the GNS `L^2` norms and
extends injectively and normally to `L(A rtimes H)`, with the asserted
generated range.

For the regular-module specialization, every nonidentity `g` in the
torsion-free group `Gamma(3)` has infinite order. If a nonzero finitely
supported function `a:H->F_p` had a finite orbit under `<g>`, then some
positive power of the left translation by `g` would preserve its finite
nonempty support. Iterating that translation would give an infinite orbit of
any point in the support, a contradiction. Since `<g><=C_H(g)`, `(CAM1)`
follows.
---
