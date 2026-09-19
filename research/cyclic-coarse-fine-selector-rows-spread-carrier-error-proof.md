---
rg: 2
id: cyclic-coarse-fine-selector-rows-spread-carrier-error-proof
kind: route
title: Telescope projection trace deficits around the selector cycle
target: cyclic-coarse-fine-selector-rows-spread-carrier-error
requires: []
---

For projections `p,q` in a finite tracial algebra,

```text
||p-q||_2^2 >= |tau(p)-tau(q)|.                       (CCP1)
```

Indeed, if `tau(p)>=tau(q)`, then

```text
||p-q||_2^2=tau(p)+tau(q)-2 Re tau(pq)
            >=tau(p)-tau(q),
```

because `Re tau(pq)=tau(pqp)<=tau(q)`; interchange `p,q` in the other case.

Apply `(CCP1)` with

```text
p=U_i e_i U_i^*,      q=f_(i+1).
```

Using the prescribed trace ratios gives

```text
delta_i^2 >= |a tau(P_i)-b tau(P_(i+1))|.
```

Summing and using the triangle inequality,

```text
sum_i delta_i^2
 >= |sum_i (a tau(P_i)-b tau(P_(i+1)))|
 =  |a-b| sum_i tau(P_i),
```

because cyclic reindexing leaves `sum_i tau(P_(i+1))` unchanged.  This is
`(CCS3)`.

For the reflection form, put `p'=U_i e_i U_i^*` and `q'=f_(i+1)`.  Since
`1-2p'` and `1-2q'` are self-adjoint unitaries,

```text
||(1-2q')(1-2p')-1||_2^2
 = ||2(p'-q')(1-2p')||_2^2
 = 4||p'-q'||_2^2.
```

This is `(CCS5)`, and the specialization `a=1/2`, `b=1/4` gives the claimed
quarter-trace floor.