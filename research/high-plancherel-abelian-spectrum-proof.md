---
rg: 2
id: high-plancherel-abelian-spectrum-proof
kind: route
title: Combine character orthogonality with Fourier inversion on the elementary abelian subgroup
target: high-plancherel-irrep-has-nearly-uniform-fixed-abelian-spectrum
requires: []
---

Character orthogonality gives

```text
sum_(g!=1)|chi(g)|^2=|K|-d^2=|K|(1-alpha).             (HPM3)
```

Fourier inversion on `E` gives

```text
m_psi/d-1/|E|
 =(1/(|E|d))sum_(e in E, e!=1)conjugate(psi(e))chi(e).
```

Cauchy--Schwarz and `(HPM3)`, followed by `d^2=alpha|K|`, yield `(HPM2)`.
Its lower bound is positive for every `psi` when
`alpha>1-1/|E|`.

