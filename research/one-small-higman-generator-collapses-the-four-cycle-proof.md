---
rg: 2
id: one-small-higman-generator-collapses-the-four-cycle-proof
kind: route
title: Compare the doubled chord with the original chord and propagate
target: one-small-higman-generator-collapses-the-four-cycle
requires: []
---

Write `r=||U_j-1||`.  Choose `z` in the spectrum of `U_j` with
`|z-1|=r`.  Since `r<=sqrt(2)`, the point `z` lies in the closed right
semicircle and

```text
|z+1|=sqrt(4-|z-1|^2)>=sqrt(2).
```

Therefore

```text
||U_j^2-1||
 >= |z^2-1|
 = |z-1||z+1|
 >= sqrt(2)r.                                         (1)
```

The preceding Higman relation and unitary invariance give

```text
||U_j^2-1||
 <= ||U_(j-1)U_jU_(j-1)^*-U_j^2||
    +||U_(j-1)U_jU_(j-1)^*-1||
 <= delta+r.                                          (2)
```

Combining `(1)` and `(2)` yields

```text
r <= delta/(sqrt(2)-1)=(sqrt(2)+1)delta.              (3)
```

For arbitrary unitaries `A,V`,

```text
||AVA^*-V|| <= 2||A-1||,
||V-V^2||   = ||V-1||.                                (4)
```

Apply `(4)` to the next Higman relation.  If
`r_k=||U_(j+k)-1||`, then

```text
r_(k+1) <= delta+2r_k.                                (5)
```

Starting from `(3)`, three iterations give respectively

```text
r_1 <= (1+2c)delta,
r_2 <= (3+4c)delta,
r_3 <= (7+8c)delta,          c=sqrt(2)+1.
```

The last coefficient is `7+8(sqrt(2)+1)=15+8sqrt(2)`, proving `(HAC3)`.
