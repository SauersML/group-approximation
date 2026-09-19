---
rg: 2
id: adjoint-reynolds-rank-gap-pays-every-return-proof
kind: route
title: Compare projection ranks and adjoint characters
target: adjoint-reynolds-rank-gap-pays-every-return
requires:
  - predicate-rank-jump-forces-adjoint-reynolds-gap
---

If `P,Q` are orthogonal projections on an `n`-dimensional Hilbert space and
`rank P>=rank Q`, then

```text
Tr((P-Q)^2)=rank P+rank Q-2Tr(PQ)>=rank P-rank Q,     (1)
```

because `Tr(PQ)<=rank Q`.  Apply `(1)` to `P=R_A` and
`Q=V R_B V^*`, divide by `n=d^2`, and invoke `(ARR1)`.  This proves `(ARR2)`.

For `(ARR3)`, put `Z=U^*U'` and evaluate the Hilbert--Schmidt character of the
adjoint representation:

```text
||Ad_U-Ad_(U')||_(HS,d^2)^2
 = 2-2|tau_d(Z)|^2.
```

Since `|z|^2>=2 Re(z)-1` for every complex `z`,

```text
2-2|tau_d(Z)|^2
 <= 4-4 Re tau_d(Z)
 = 2||U-U'||_(2,d)^2.
```

Finally `(ARR4)` and the triangle inequality give

```text
||R_A-Ad_W R_B Ad_W^*||_(HS,d^2)
 <= (1/|H|) sum_h
      ||Ad_(a_h)-Ad_(W rho(h) W^*)||_(HS,d^2).
```

Square and use Jensen, then `(ARR3)`, to bound the left side squared above by
the right side of `(ARR5)`.  Combining with `(ARR2)` proves `(ARR5)`.
