---
rg: 2
id: binary-leavitt-unit-group-is-simple-proof
kind: route
title: Identify the unit group with EL_3 through the three-leaf prefix code
target: binary-leavitt-unit-group-is-simple
requires: [binary-leavitt-elementary-group-is-simple, leavitt-gl-equals-el-and-perfect-unit-group]
---

Let `L = L_(F_2)(1,2)` with `t_i s_j = delta_ij` and `s_0 t_0 + s_1 t_1 = 1`.
Put

```text
S_1 = s_0,        S_2 = s_1 s_0,        S_3 = s_1 s_1,
T_1 = t_0,        T_2 = t_0 t_1,        T_3 = t_1 t_1.
```

Then `T_i S_j = delta_ij`: for example `T_2 S_2 = t_0 (t_1 s_1) s_0 = 1`,
`T_2 S_3 = t_0 s_1 = 0` and `T_3 S_2 = t_1 s_0 = 0`.  Also

```text
S_1 T_1 + S_2 T_2 + S_3 T_3 = s_0 t_0 + s_1 (s_0 t_0 + s_1 t_1) t_1 = 1.
```

Hence `Phi : M_3(L) -> L`, `(a_ij) |-> sum_(i,j) S_i a_ij T_j`, is a unital
ring isomorphism with inverse `r |-> (T_i r S_j)`.  Multiplicativity is the
line `Phi(a) Phi(b) = sum S_i a_ij (T_j S_k) b_kl T_l = Phi(ab)`.  Units
correspond to units, so `L^x = GL_3(L)`.

By `leavitt-gl-equals-el-and-perfect-unit-group`, `GL_3(L) = EL_3(L)`.  By
`binary-leavitt-elementary-group-is-simple`, `EL_3(L)` is a nontrivial simple
group.  It is infinite because it contains the infinitely many distinct roots
`x_12(s_0^k)`, and nonabelian because `[x_12(1), x_23(1)] = x_13(1) != 1`.
