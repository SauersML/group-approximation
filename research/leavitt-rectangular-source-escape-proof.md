---
rg: 2
id: leavitt-rectangular-source-escape-proof
kind: route
title: Exhibit a four-target rectangular model for the relative Leavitt decoder
target: common-source-leavitt-cell-inherits-rectangular-root-escape
requires: []
---

Formally, arrows `s_c,t_c` with `t_cs_c=Q` and
`A_(c,x)s_c=s_cZ_x` have one source whenever `t_c=s_c^*`.  The obstruction is
recovering that adjoint/common-reservoir statement from root coordinates.

Let `b:V x W -> F_2` be a nonzero perfect pairing.  Put `V'=V^4`, `W'=W^4`
with coordinate-sum pairing, and let `R_c,L_c` be coordinate inclusions.
Then

```text
b'(R_cv,L_dw)=delta_(c,d)b(v,w)
```

for all four targets.  Hence every diagonal-inverse and crossed-zero table
visible to a fixed one-level root decoder is exact.

If `|V|=|W|=N`, represent the source Weyl packet of dimension `N` with
multiplicity `N^3`, and the target Weyl packet of dimension `N^4` with
multiplicity one.  Both act in total dimension `N^4`.  The apparent
four-fold label enlargement is paid for entirely by multiplicity
contraction, without changing any displayed root table.

Thus those tables cannot force four arrows with one physical source.  The
missing assertion is precisely

```text
sum_c [tau(Q)-tau(QU_c^*p_cU_cQ)]
 =sum_c||(1-p_c)U_cQ||_2^2=o(1),
```

after which spectral intersection and polar rounding do recover the formal
Leavitt arrows.  This proves both the escape and the exact remaining scalar.
