---
rg: 2
id: contraction-branch-capacity-forces-collision-proof
kind: route
title: Cauchy-Schwarz on the aggregate range operator against the corner
target: contraction-branch-capacity-forces-collision
requires: []
---

Put `S = sum_a X_a X_a^*`, a positive element with `S = QSQ` because every
`X_a = Q X_a`.  Then

```text
tau(S) = sum_a tau(X_a X_a^*) = sum_a ||X_a||_2^2 = M_tot.
```

**Lower bound on the second moment.**  Since `S = QSQ`, Cauchy--Schwarz for the
trace gives

```text
M_tot^2 = tau(S)^2 = tau(SQ)^2 <= tau(S^2) tau(Q) = q . tau(S^2),
```

hence `tau(S^2) >= M_tot^2/q`.

**Expanding the second moment.**  Using traciality,

```text
tau(S^2) = sum_(a,b) tau(X_a X_a^* X_b X_b^*)
         = sum_(a,b) ||X_b^* X_a||_2^2,
```

because `||X_b^* X_a||_2^2 = tau(X_a^* X_b X_b^* X_a) = tau(X_a X_a^* X_b X_b^*)`.

**Bounding the diagonal.**  The `a=b` terms are `|| X_a^* X_a ||_2^2 = || |X_a|^2 ||_2^2`.
Since `X_a` is a contraction, `|X_a| <= 1`, so `|X_a|^4 <= |X_a|^2` and

```text
sum_a ||X_a^* X_a||_2^2 = sum_a tau(|X_a|^4) <= sum_a tau(|X_a|^2) = M_tot.
```

Combining the three displays,

```text
sum_(a != b) ||X_b^* X_a||_2^2 = tau(S^2) - sum_a ||X_a^*X_a||_2^2
                               >= M_tot^2/q - M_tot,
```

which is `(CBC1)`.  `(CBC2)` is `(CBC1)` rewritten with `M_tot = Rq`.
