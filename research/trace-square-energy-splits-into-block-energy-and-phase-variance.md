---
rg: 2
id: trace-square-energy-splits-into-block-energy-and-phase-variance
kind: claim
title: Trace-square energy splits exactly into block energy and phase variance
distinct_from:
  projective-commutant-transfer-for-arithmetic-pair: that is an arithmetic transfer inequality for approximate representations; this is the exact dimension-free scalar and block ledger that any such transfer must respect.
  exact-codensity-does-not-imply-matricial-rcc: that supplies an exact approximation-wall counterexample; this identifies the precise phase-spread mechanism by which reducible blocks retain trace-square energy.
---

**ESTABLISHED.**  For a unitary `W in U(d)` put

```text
E(W)=1-|tr_d(W)|^2,
D(W)^2=min_(zeta in T)||W-zeta I||_2^2.
```

Then

```text
D(W)^2=2-2|tr_d(W)|,
E(W)=((1+|tr_d(W)|)/2)D(W)^2,                         (TSE1)
```

and hence

```text
(1/2)D(W)^2 <= E(W) <= D(W)^2.                        (TSE2)
```

If `W=directSum_j W_j`, the block weights are
`alpha_j=d_j/d`, and `z_j=tr_(d_j)(W_j)`, then

```text
E(W)=sum_j alpha_j(1-|z_j|^2)
     +(1/2)sum_(i,j)alpha_i alpha_j|z_i-z_j|^2.       (TSE3)
```

Thus trace-square energy consists of the within-block energies plus the
variance of the block traces.  In particular, making every block nearly
scalar does not make the direct sum nearly scalar unless their phases also
synchronize.

If `W` is scalar off a projection of normalized rank `alpha`, then

```text
E(W) <= 1-max(0,1-2alpha)^2.                           (TSE4)
```

Consequently `E(W)>=epsilon` forces

```text
alpha >= (1-sqrt(1-epsilon))/2.                        (TSE5)
```

The same estimate with residual normalized Hilbert--Schmidt error `r` off
that projection is

```text
E(W) <= 1-max(0,1-2alpha-r sqrt(1-alpha))^2.           (TSE6)
```

DERIVATION
trace-square-block-phase-identity-proof

