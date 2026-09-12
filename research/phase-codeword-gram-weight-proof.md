---
rg: 2
id: phase-codeword-gram-weight-proof
kind: route
title: Sum the Fourier normalizer identity over the phase-code coordinates
target: finite-phase-codewords-weight-type-gram-leakage
requires:
  - fourier-normalizer-words-control-block-gram-leakage
---

Apply `(FNG1)` separately to each spectral tag `D_l`.  A cross block from
type `omega` to type `nu` receives weight

```text
m sum_l |zeta^(c_l(nu))-zeta^(c_l(omega))|^2.
```

At least `h` summands are nonzero, and every nonzero summand is at least
`4 sin^2(pi/m)`.  Hence the total weight is at least
`4mh sin^2(pi/m)`.  Divide the summed Parseval identity by this lower bound
to obtain `(PCG1)`.
