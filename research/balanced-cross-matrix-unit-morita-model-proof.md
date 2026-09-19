---
rg: 2
id: balanced-cross-matrix-unit-morita-model-proof
kind: route
title: Realize the balanced cross-action bridge as rectangular matrix units over F2
target: balanced-cross-matrix-unit-actions-have-m3-morita-model
requires:
  - aggregate-morita-common-opposite-return-has-gl3-square-model
  - degree-zero-leavitt-core-has-locally-finite-marked-models
  - outer-root-leavitt-table
  - atomic-leavitt-gap-on-nonzero-matrix-corner
---

Let `E_ab` denote the standard matrix units of `A=M_3(F_2)`, on indices
`0,1,star`.  Matrix-unit multiplication immediately gives

```text
E_(i,star)E_(star,j)=E_(i,j),
E_(i,j)E_(k,star)=delta_(j,k)E_(i,star),
E_(star,k)E_(i,j)=delta_(k,i)E_(star,j),
E_(star,i)E_(j,star)=delta_(i,j)E_(star,star).
```

These are `(BCM1)`, `(BCM2)`, and `(BCM5)`.  The diagonal sum
`p=E_00+E_11` is the identity on the first two coordinates, so

```text
ps_i=s_i,   t_ip=t_i,   pq_i=q_i=q_ip.
```

Consequently the substitution

```text
s_i |-> E_(i,star),   t_i |-> E_(star,i),
e_ij |-> E_(i,j),     displayed 1 |-> p
```

preserves every coefficient product used by the bounded occurrence table.
For distinct Steinberg coordinates, the usual elementary-matrix calculation

```text
[X_ab(r),X_bc(s)]=X_ac(rs)
```

therefore verifies every literal cross-action occurrence.  Root addition
gives `X_ab(q_0)X_ab(q_1)=X_ab(p)`.

For the original aggregate coordinates `(7,8,9,10)`, renamed `(0,1,2,3)`,
use

```text
S_0=X_02(s_0),  S_1=X_03(s_1),
T_0=X_21(t_0),  T_1=X_31(t_1),
N=X_01(p),      D=X_10(p).
```

The returned arms are

```text
U_i=[D,S_i],    V_i=[T_i,D],    R_i=[U_i,V_i].
```

Since `ps_i=s_i`, `t_ip=t_i`, and `s_it_i=q_i`, these are exactly the
required roots, and `R_0R_1=D`.  Inside the unital corner `pAp`, the opposite
transvections `N,D` are the ordinary rank-one `SL_2(F_2)` pair, hence satisfy
`NDN=DND`.

Represent the literal private-middle Whitehead by

```text
H=X_23(1_A)X_32(1_A)X_23(1_A).
```

It swaps root coordinates `2,3` on all three coefficient coordinates.  The
parent occurrences `N,D` still use `p`; the scoped menu does not identify
those roots with the middle-swap roots.  Its conjugates of the four native
arms are exactly the ones in the private-middle-swap table.  Their
cross commutators are `X_01(e_01)`, `X_01(e_10)`, `X_10(e_01)`, and
`X_10(e_10)`.  Matrix-unit multiplication then verifies both complementary
partial Whiteheads and their aggregate-parent exchange.

The executable audit
`experiments/balanced_cross_matrix_unit_morita_escape.py` flattens these block
matrices into `GL_21(F_2)` and checks the complete aggregate/common-opposite
table, the private-middle Whitehead and its four cross commutators, both
complementary partial Whiteheads and their parent exchange, the full sixteen
left and right cross-action cases including their zero commutators, the
parent Whitehead braid, `p!=h`, and survival of `x_78(q_1)`.

Finally, `t_is_i=h=E_(star,star)`, while the already used parent occurrence of
coefficient `1` is represented by `p`.  Thus the proposed extension does not
contain the one same-occurrence equation which would identify the source and
range objects.  This proves both the exact finite model and the stated sharp
boundary.
