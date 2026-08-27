---
rg: 2
id: bounded-cycle-coboundary-inverse-proof
kind: route
title: Diagonalize each cyclic shift by the finite Fourier transform
target: bounded-cycle-coboundary-inverse
requires: []
---

On a cyclic summand of length `L`, the finite Fourier transform diagonalizes
`psi` with eigenvalues

```text
zeta_L^j=exp(2 pi i j/L),               0<=j<L.
```

The `j=0` eigenspace is exactly the fixed line.  On its orthogonal complement,

```text
|1-zeta_L^j| >= 2 sin(pi/L) >= 2 sin(pi/K).
```

Hence spectral functional calculus defines the inverse of `1-psi` on the
fixed-space complement and gives the first inequality in `(BCI2)`.  Since
`pi/K<=pi/2` and `sin t>=2t/pi` on `[0,pi/2]`,

```text
2 sin(pi/K) >= 4/K,
```

which gives the second inequality.  Taking the orthogonal direct sum over all
cyclic summands proves the claim.
