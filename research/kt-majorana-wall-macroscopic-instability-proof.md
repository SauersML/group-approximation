---
rg: 2
id: kt-majorana-wall-macroscopic-instability-proof
kind: route
title: Solve the genuine-actor return inequality for the correction distance
target: kt-majorana-wall-certifies-macroscopic-actor-instability
requires:
  - kt-local-actor-correction-pays-majorana-return
---

For any genuine same-dimensional representation `rho:E->U(d)`, set

```text
epsilon=max_(g in K union {h})||u_g-rho(g)||_2.
```

Inequality `(LAC2)` from the prerequisite says

```text
a >= 2-(4/kappa_K)delta-C_K epsilon.
```

Rearrangement, followed by the infimum over `rho`, proves `(MWI3)`.

For the amplified statement, use `(LAC4)` from the same prerequisite:

```text
a >= q^(-1/2)[2-(4/kappa_K)sqrt(q)delta
                 -C_K epsilon-2sqrt(1-q)].
```

Multiplying by `sqrt(q)` and rearranging proves `(MWI4)`.  If `D/d<=A`, then
`q>=1/A`.  Along any sequence with `delta,a->0`, compactness of
`[1/A,1]` and monotonicity of `2-2sqrt(1-q)` give `(MWI5)`.  For
`D=d+o(d)`, one has `q->1`, giving the terminal lower bound `2/C_K`.
