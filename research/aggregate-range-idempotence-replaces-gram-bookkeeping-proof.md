---
rg: 2
id: aggregate-range-idempotence-replaces-gram-bookkeeping-proof
kind: route
title: Expand the square of the sum of final projections
target: aggregate-range-idempotence-replaces-gram-bookkeeping
requires:
  - partial-isometry-gram-is-range-overlap
---

Each `F_a=T_aT_a^*` is a projection.  Expanding the square of
`F=sum_a F_a` and taking the trace gives

```text
tau(F^2)
 = sum_a tau(F_a)
   + sum_(a!=b) tau(F_aF_b).                            (1)
```

By `partial-isometry-gram-is-range-overlap`,

```text
tau(F_aF_b)=||T_a^*T_b||_2^2.
```

Therefore `(1)` is exactly

```text
tau(F^2)=s+o,
```

which proves `(ARI1)`.  Since the normalized trace is the inner product with
`1` and `||1||_2=1`, Cauchy--Schwarz gives

```text
o = |tau(F^2-F)| <= ||F^2-F||_2,
```

proving `(ARI2)`.

Now let `P` be a projection.  Traciality gives

```text
||(1-P)T_a||_2^2
 = tau(T_a^*(1-P)T_a)
 = tau((1-P)F_a).
```

After summing,

```text
l=s-tau(PF),
```

so `s-l=tau(PF)`.  This number is nonnegative because
`tau(PF)=tau(PFP)` and `PFP>=0`.  Hilbert--Schmidt Cauchy--Schwarz then gives

```text
(s-l)^2 = |tau(PF)|^2
         <= tau(P^2) tau(F^2)
         = tau(P) tau(F^2),
```

which is `(ARI3)`.
