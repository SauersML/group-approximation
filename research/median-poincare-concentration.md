---
rg: 2
id: median-poincare-concentration
kind: claim
title: A median plus a block Poincare gap pins a bounded observable
---

Let `(M,tau)` be a finite tracial von Neumann algebra, let `q` be a nonzero
projection, and write `tau_q = tau(.)/tau(q)`.  Let `(a_s)_(s in S)` be a
finite family in `qMq`; **no unitarity hypothesis is imposed**.  Suppose that
for every self-adjoint `x in qMq`,

```text
sum_(s in S) ||a_s x - x a_s||_(2,q)^2
  >= kappa^2 ||x - tau_q(x) q||_(2,q)^2.
```

If `0 <= f <= q` is self-adjoint and `1/2` is a median of its spectral
distribution for `tau_q`, meaning both

```text
tau_q(1_(-infinity,1/2](f)) >= 1/2,
tau_q(1_[1/2,infinity)(f)) >= 1/2,
```

then

```text
||f - (1/2)q||_(2,q)
 <= ((1 + sqrt(2))/kappa)
    * (sum_(s in S) ||a_s f - f a_s||_(2,q)^2)^(1/2).
```

Consequently the same right-hand side controls the normalized `L^1` distance.
The point of the formulation is the missing hypothesis: this is a direct
Poincare argument, so it remains valid when the `a_s` are compressed
almost-unitaries rather than genuine unitaries.