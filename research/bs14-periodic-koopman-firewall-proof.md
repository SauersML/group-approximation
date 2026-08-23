---
rg: 2
id: bs14-periodic-koopman-firewall-proof
kind: route
title: Realize the first cyclic Fourier mode on a fourth-power orbit
target: bs14-periodic-koopman-modes-refute-skeleton-regularity
requires: []
---

The multiplicative order of `4` modulo `N=4^L-1` is exactly `L`: if
`4^k=1 mod N` for `0<k<L`, then the positive integer `N` would divide
`4^k-1<N`, impossible.  Thus the exponents `4^j mod N` are distinct and
`(BKM2)` has simple spectrum.  A direct basis calculation gives

```text
H V H^(-1)e_j=omega^(4^(j+1))e_j=V^4e_j,
```

proving `(BKM3)`.

Conjugating a diagonal matrix by `H` shifts its diagonal entries by one.
The vector of entries in `(BKM4)` is therefore an eigenvector with eigenvalue
`zeta` or `zeta^(-1)`, depending on the shift convention.  It is mean zero,
has normalized `L^2` norm one, and gives `(BKM5)`.  Since `1-psi` is normal,
its minimum-norm inverse on this eigenspace multiplies by
`(1-zeta)^(-1)`, proving `(BKM6)`.  Finally
`|1-zeta|=2 sin(pi/L)<=2 pi/L`, so `(BKM7)` has inverse norm at least
`L/(2 pi)`.

