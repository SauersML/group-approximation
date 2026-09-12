---
rg: 2
id: low-gap-witness-spike-or-balanced-cut
kind: claim
title: Operator-norm clipping isolates the vanishing-rank obstruction
---

Let `(M,tau)` be a finite matrix algebra, let `u_1,...,u_m` be unitaries,
and let `x=x^*` satisfy

```text
tau(x)=0,   ||x||_2=1,
E=sum_s ||[u_s,x]||_2^2.
```

For every `C>=1`, at least one of the following holds.

1. **Balanced-cut alternative.** There is a projection `q in W*(x)` with

```text
1/(64 C^2) <= tau(q) <= 1-1/(64 C^2)
```

and

```text
sum_s ||[u_s,q]||_2^2 <= 16 C sqrt(m E).
```

2. **Spike alternative.** If `f_C(t)=max(-C,min(t,C))` and
   `z=x-f_C(x)`, then

```text
||z||_2 >= 1/4,
```

while `z` is supported on

```text
r=1_{|x|>C},   tau(r)<=1/C^2.
```

Thus a sequence of normalized low-energy witnesses can avoid all balanced
almost-invariant cuts at fixed `C` only by placing a fixed amount of its
`L^2` mass on spectral supports whose trace is `O(C^-2)`.  This is the
precise spike phenomenon exhibited by `rank-one-lift-perturbation-gap-no-go`.
