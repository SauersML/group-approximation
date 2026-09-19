---
rg: 2
id: dirichlet-compiler-from-four-cycle-traces
kind: route
title: Sum the four trace deficits and discard all individual trace information
target: atlas-a4-four-cycle-dirichlet-compiler
requires:
  - atlas-a4-four-cycle-trace-compiler
---

Put `B_n=V_n(t23)` and let the other three `V_n(t)` be the leaves.  From
`(A4-TRACE-1)`,

```text
sum_(leaf t) (1-Re tau_n(V_n(t)))
 <= 3(1-Re tau_n(B_n)) + C_tr eta_n.
```

Adding the hub deficit gives

```text
sum_(t in {t01,t12,t23,t30}) (1-Re tau_n(V_n(t)))
 <= 4(1-Re tau_n(B_n)) + C_tr eta_n.
```

Now `(A4-TRACE-2)` bounds the first term by

```text
4 C_col (||sigma_n(q_19243)-1||_2+eta_n).
```

Since `eta_n` is itself bounded by the displayed right-hand quantity, this is
`(A4-DIR)` after enlarging the fixed constant.  Thus even the four separate
trace values are unnecessary downstream: their single summed Dirichlet energy
is sufficient.
