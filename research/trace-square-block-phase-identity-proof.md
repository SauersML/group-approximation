---
rg: 2
id: trace-square-block-phase-identity-proof
kind: route
title: Expand the scalar distance and the weighted variance identity
target: trace-square-energy-splits-into-block-energy-and-phase-variance
requires: []
---

For normalized trace,

```text
||W-zeta I||_2^2=2-2 Re(conj(zeta)tr_d(W)).
```

Optimizing over `zeta` proves the first identity in `(TSE1)`; factoring
`1-|tr(W)|^2` proves the second and `(TSE2)`.

For a block sum, `tr(W)=sum_j alpha_j z_j`.  The weighted variance formula

```text
sum_j alpha_j|z_j|^2-|sum_j alpha_j z_j|^2
 =(1/2)sum_(i,j)alpha_i alpha_j|z_i-z_j|^2
```

gives `(TSE3)` after adding and subtracting
`sum_j alpha_j|z_j|^2`.

After multiplying `W` by a scalar, suppose it equals `I` off a projection
`P` of trace `alpha`.  The trace contribution from `P` has modulus at most
`alpha`, so the reverse triangle inequality gives

```text
|tr(W)|>=max(0,1-2alpha),
```

which is `(TSE4)` and `(TSE5)`.  If the complement differs from its scalar
by normalized Hilbert--Schmidt error `r`, Cauchy--Schwarz changes the lower
bound on the trace modulus by at most `r sqrt(1-alpha)`, proving `(TSE6)`.

