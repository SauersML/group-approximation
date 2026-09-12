---
rg: 2
id: regularized-residual-spike-boundary-proof
kind: route
title: Test parity Loewner order on a compressed odd-square cut
target: regularized-anchor-cut-makes-residual-spikes-boundary-heavy
requires:
  - adjoint-parity-cone-lifts-to-loewner-order
  - regularized-anchor-square-function-has-dimension-free-cut
  - spectral-cut-anchor-reset-pays-boundary-in-one-row
---

On `L_2(M)` put `P_k=(I-Ad(Q_k))/2`, `v=Q_ar`, and

```text
 T_k=(Q_a-Q_kQ_aQ_k)r/2.
```

Then `||T_k||_2^2=tau(rR_k)` and

```text
 ||P_kv-T_k||_2=||[r,Q_k]||_2/2.                       (RSP5)
```

Apply `P_i<=(kappa L)^(-1)sum_kP_k` to `v`, use
`||x+y||^2<=2||x||^2+2||y||^2`, and compare `T_i` back to `P_iv`.  This
gives

```text
 tau(rR_i)
 <=(4/(kappa L))sum_k tau(rR_k)
   +D(r)/kappa+||[r,Q_i]||_2^2/2.                      (RSP6)
```

Apply the same Loewner inequality to the Hilbert--Schmidt vector `r`.
Since `||P_kr||_2=||[r,Q_k]||_2/2`, it gives

```text
 ||[r,Q_i]||_2^2<=D(r)/kappa.                          (RSP7)
```

The left side of `(RSP6)` is at least `s tau(r)` by `(RSP2)`.  Since
`r<=q`, `(RSP1)` gives

```text
 (1/L)sum_k tau(rR_k)=tau(rK)=tau(rqKqr)<=eta tau(r).
```

Substitution into `(RSP6)` proves `(RSP3)`, and the stated choices of
parameters prove `(RSP4)`.
