---
rg: 2
id: private-middle-swap-gl6-proof
kind: route
title: Fuse the two returned Morita triangles through their private middle indices
target: private-middle-swap-return-has-gl6-model
requires:
  - aggregate-morita-common-opposite-return-has-gl3-square-model
  - cross-branch-partial-whiteheads-have-finite-wreath-gauge-model
  - outer-root-leavitt-table
---

Let `H=w_(9,10)(1)`.  Constant Weyl conjugation gives

```text
HS_0H^(-1)=x_(7,10)(s_0),    HS_1H^(-1)=x_79(s_1),
HU_0H^(-1)=x_(8,10)(s_0),    HU_1H^(-1)=x_89(s_1).
```

Use respectively the unchanged arms

```text
T_1=x_(10,8)(t_1),   T_0=x_98(t_0),
V_1=x_(10,7)(t_1),   V_0=x_97(t_0).
```

The ordinary non-opposite Steinberg commutator law proves the four lines
of `(PMC3)`.  Every coefficient product is literal:

```text
s_0t_1=p,       s_1t_0=r,
pr=s_0(t_1s_1)t_0=q_0,
rp=s_1(t_0s_0)t_1=q_1,
p^2=r^2=0.
```

Hence the three-root words in `(PMC4)` are the standard partial
Whiteheads.  Direct two-by-two multiplication gives their involution,
commutation, product, and parent-exchange equations `(PMC5)`.  This is also
the coefficient calculation already isolated for the two cross partial
Whiteheads, but here both inputs have been typed as commutators of the
literal aggregate-return arms.

For the finite model, let `e_ab=I+E_ab` over `F_2`.  On each of the two
triangles in `(PMC6)`, assign

```text
S_i=e_(7_i,k_i),       T_i=e_(k_i,8_i),
C_i=e_(7_i,8_i),       U_i=e_(8_i,k_i),
V_i=e_(k_i,7_i),       R_i=e_(8_i,7_i).
```

Then `N=C_0C_1`, `D=R_0R_1`, and `H` is the transposition of `k_0,k_1`.
Conjugation by that permutation matrix and

```text
[e_ab,e_bc]=e_ac
```

give `(PMC7)` immediately.  Each partial Whitehead is the permutation
matrix swapping the endpoints of its cross edge, so the two have disjoint
supports and commute.  Their product carries the two summands of `N` to
the two summands of `D` in the opposite order.

The MSI-only executable audit
`experiments/private_middle_swap_returned_morita_gl6_audit.py` checks the
complete fixed table over `F_2`, including the old returned-arm rows, the
parent braid, the four new cross commutators, both partial Whiteheads, and
nontriviality of the marked child.  Finiteness of `GL_6(F_2)` then supplies
the exact regular model claimed.
