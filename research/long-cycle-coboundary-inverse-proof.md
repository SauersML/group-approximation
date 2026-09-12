---
rg: 2
id: long-cycle-coboundary-inverse-proof
kind: route
title: Test the first nontrivial Fourier mode of a cyclic shift
target: long-cycles-have-unbounded-l2-coboundary-inverse
requires: []
---

Put `zeta=exp(2 pi i/L)` and, for an arbitrary `delta>0`, define

```text
phi_j=delta zeta^j,             j in Z/LZ.
```

The geometric sum vanishes, so `phi` lies in `H_L^0`, and normalized
Parseval gives `||phi||_2=delta`.  Up to replacing `zeta` by its inverse
according to the shift convention, the mean-zero solution of
`(1-psi_L)c=phi` is

```text
c_j=delta zeta^j/(1-zeta).
```

Therefore

```text
||c||_2/||phi||_2=1/|1-zeta|.
```

The elementary chord bound

```text
|1-exp(2 pi i/L)| <= 2 pi/L
```

gives `(LCI1)`.  Since the ratio tends to infinity with `L`, `(LCI2)`
cannot hold with a uniform constant.  Relabelling the same `L` coordinates
by one orbit of multiplication by four leaves `psi_L` and its Fourier
eigenvalues unchanged, proving the lacunary-label assertion.
