---
rg: 2
id: robust-rank-one-endpoint-marginal-floor-proof
kind: route
title: Use unnormalized Frechet bounds and trace Cauchy--Schwarz
target: robust-rank-one-endpoint-marginal-floor
requires:
  - rank-one-no-signaling-pairing-floor
---

The diagonal success atoms lie inside their first and second endpoint events,
so

```text
p_00 >= q-a_00,                 p_11 >= q-b_11.       (1)
```

The unnormalized Frechet bound in the middle context is

```text
p_01=nu_01(1,1) >= max(0,a_01+b_01-q).               (2)
```

Replace `a_00` by at most `a_01+Delta_X` and `b_11` by at most
`b_01+Delta_Y` in `(1)`, then add `(2)`.  With `s=a_01+b_01`, the result is

```text
p_00+p_01+p_11
 >= 2q-s-Delta_X-Delta_Y+max(0,s-q).
```

If `s>=q`, the right side is `q-Delta_X-Delta_Y`; if `s<q`, it is strictly
larger.  This proves `(RRF1)`.

For normalized trace `tau`, unitary invariance and Cauchy--Schwarz give

```text
|tau(P)-tau(P')|
 = |tau(U P U^*-P')|
 <= ||U P U^*-P'||_2 ||1||_2
 = ||U P U^*-P'||_2.
```

Apply this to both endpoints to obtain `(RRF2)`.  Finally, if the squares of
the two displayed norms sum to at most `E_end`, Cauchy--Schwarz gives their
sum at most `sqrt(2 E_end)`, proving `(RRF3)`.
