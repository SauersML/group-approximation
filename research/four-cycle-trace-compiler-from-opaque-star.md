---
rg: 2
id: four-cycle-trace-compiler-from-opaque-star
kind: route
title: Forget the opaque conjugators and retain only their trace consequences
target: atlas-a4-four-cycle-trace-compiler
requires:
  - atlas-a4-normal-certificate-compiler
---

Assume the three opaque transports from
`atlas-a4-normal-certificate-compiler`.  Put `B=V_n(t23)` and
`T_t=V_n(t)` for `t in {t01,t12,t30}`.

For a leaf `t`, unitary invariance of trace and Cauchy--Schwarz give

```text
|Re tau_n(T_t)-Re tau_n(B)|
 = |Re tau_n(T_t)-Re tau_n(A_n(t) B A_n(t)^*)|
 <= ||T_t-A_n(t) B A_n(t)^*||_2
 <= C_star eta_n.
```

Summing the three inequalities yields exactly `(A4-TRACE-1)` with
`C_tr=3 C_star`.

The collision readout of the opaque-star compiler gives

```text
||B-1||_2 <= C_col' d_n,

d_n=||sigma_n(q_19243)-1||_2+eta_n.
```

Since `B` is unitary, `||B-1||_2<=2`, and therefore

```text
1-Re tau_n(B)
 = (1/2)||B-1||_2^2
 <= ||B-1||_2
 <= C_col' d_n.
```

This is `(A4-TRACE-2)`.  Hence the new scalar compiler is formally weaker than
the three-transport compiler: every opaque-star certificate can be erased down
to four real covariance traces and the collision readout.
