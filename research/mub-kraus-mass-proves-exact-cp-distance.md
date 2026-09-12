---
rg: 2
id: mub-kraus-mass-proves-exact-cp-distance
kind: route
title: Orthogonal Kraus mass gives a sharp one-third separation from the sum-of-masas idempotent
target: mub-sum-idempotents-have-uniform-cp-distance
requires: []
artifacts:
  - research/artifacts/mub-idempotent-exact-cp-distance-2026-09-12.md
---

Choose cyclic orthonormal unitary bases `u_k` of `D` and `v_l` of
`C`, with `u_0=v_0=1`. The idempotent `Q` fixes the `2(d-1)`
nonidentity axis unitaries and kills all `(d-1)^2` products `u_k v_l`
with `k,l!=0`.

For any UCP `P(x)=sum_i a_i* x a_i`, let
`r_kl=Re tau((u_k v_l)*P(u_k v_l))` and write `A` for the sum of
the nonidentity axis entries and `B` for the mixed entries. Cyclic
averaging and `E_C E_D=E_0` give

```text
0 <= sum_i ||(I-E_D-E_C+E_0)(a_i)||_2^2
   = [(d-1)^2-(d-1)A+B]/d^2.
```

If `epsilon=||P-Q||_(infinity->2)`, unitary testing gives
`A>=2(d-1)(1-epsilon)` and `B<=(d-1)^2 epsilon`. Therefore
`0<=(d-1)^2(3epsilon-1)` and `epsilon>=1/3`.

Conversely `P_*=(id+E_D+E_C)/3` is self-adjoint bistochastic UCP.
The operator `3(P_*-Q)` acts by zero on scalars, minus identity on
`(D+ C) minus scalars`, and identity on its orthogonal complement.
It is an `L^2` contraction; `||x||_2<=||x||_op` proves the upper
bound `1/3`, attained on a nonidentity `u_k`. The artifact proves
the averaging identity with the normalized trace and arbitrary Kraus
representation explicitly.
