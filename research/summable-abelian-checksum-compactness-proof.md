---
rg: 2
id: summable-abelian-checksum-compactness-proof
kind: route
title: Compactify the weighted restriction labels and swap two nearby characters
target: summable-abelian-checksum-misses-infinite-characters
requires: []
---

Define on `hat M` the pseudometric

```text
d_a(chi,psi)^2=sum_n a_n |chi(m_n)-psi(m_n)|^2.         (1)
```

The map

```text
chi |-> (chi(m_0),chi(m_1),...) in product_n T
```

lands in a compact product.  Because `sum_n a_n<infinity`, the metric in
`(1)` induces a totally bounded metric on its image: choose `N` so that
`4 sum_(n>N)a_n` is small, then cover the finite torus `T^(N+1)` by finitely
many small boxes.  Hence an infinite image contains distinct points at
arbitrarily small `d_a`-distance.  If the image is finite, two distinct
characters in the infinite set have identical images and distance zero.
This proves `(SAC1)` in both cases.

Give `P_chi` and `P_psi` normalized trace `1/2` and choose a unitary `C`
interchanging their ranges.  Both spectral atoms move, so expansion of the
two projection differences gives `(SAC2)`.  On the two off-diagonal blocks,
the commutator has scalar coefficients `psi(m)-chi(m)` and its negative.
The two blocks each have trace `1/2`; therefore

```text
||[C,rho(m)]||_2^2=|chi(m)-psi(m)|^2.                   (2)
```

Multiply `(2)` by `a_n`, sum, and use `(SAC1)` to obtain `(SAC3)`.
