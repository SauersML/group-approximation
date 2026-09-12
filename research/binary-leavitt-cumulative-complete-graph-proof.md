---
rg: 2
id: binary-leavitt-cumulative-complete-graph-proof
kind: route
title: Cancel two included corner coordinates in characteristic two
target: binary-leavitt-cumulative-complete-graph-table
requires:
  - iterated-leavitt-self-similarity-is-dual-prefix-matrix-chart
---

The corner map `r |-> s_1rt_1` is multiplicative because `t_1s_1=1`.
Applying it to the common-depth dual-prefix relation gives

```text
A_rB_s
 =s_1t_(alpha_r)(t_1s_1)s_(alpha_s)t_1
 =delta_(rs)s_1t_1
 =delta_(rs)q.                                             (1)
```

For a vertex `j`, only the `r=j` summand of `C_j` pairs with `H_j`:

```text
C_jH_j
 =sum_(0<=r<=j) A_r(B_j+B_(j+1))
 =q.                                                       (2)
```

The Steinberg commutator relation therefore gives

```text
[c_j,h_j]=x_13(C_jH_j)=x_13(q)=z.                         (3)
```

If `k<j`, neither coordinate `j` nor `j+1` occurs in `C_k`, so the product is
zero.  If `j<k`, both coordinates occur.  All other pairings vanish, and
characteristic two cancels the two survivors:

```text
C_kH_j
 =sum_(0<=r<=k) A_r(B_j+B_(j+1))
 =q+q=0.                                                   (4)
```

Hence `[c_k,h_j]=x_13(0)=1` for every `k!=j`, proving the complete edge
table.  In vector notation the calculation is

```text
(e_0+...+e_k)(e_j+e_(j+1))^T=delta_(kj),                (5)
```

so the cumulative rows and adjacent columns form dual triangular bases after
adjoining the final column.  The graph is `K_(M-1)`, with chromatic number
`M-1`; the disjoint union over unbounded `M` has infinite chromatic number.
