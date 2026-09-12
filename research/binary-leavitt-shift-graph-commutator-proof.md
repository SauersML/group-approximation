---
rg: 2
id: binary-leavitt-shift-graph-commutator-proof
kind: route
title: Fold two orthogonal corner addresses along the finite shift graphs
target: binary-leavitt-shift-graph-has-exact-marked-commutator-table
requires:
  - iterated-leavitt-self-similarity-is-dual-prefix-matrix-chart
---

The corner map

```text
iota:R -> qRq,                    iota(r)=s_1 r t_1
```

is multiplicative because `t_1s_1=1`.  The dual-prefix relation at one
common depth is

```text
t_(alpha_i)s_(alpha_j)=delta_(ij)1.
```

Applying `iota` gives

```text
T_iS_j
 =s_1t_(alpha_i)(t_1s_1)s_(alpha_j)t_1
 =delta_(ij)s_1t_1
 =delta_(ij)q,                                             (1)
```

which proves `(LS2)`.

For `v=(i,j)`, the Steinberg commutator relation and `i<j` give

```text
[c_v,h_v]
 =[x_12(T_j),x_23(S_i+S_j)]
 =x_13(T_j(S_i+S_j))
 =x_13(q)=z.                                               (2)
```

If `v=(i,j)` and `w=(j,k)` with `i<j<k`, then `k` is distinct from both
`i` and `j`, so

```text
[c_w,h_v]
 =[x_12(T_k),x_23(S_i+S_j)]
 =x_13(T_k(S_i+S_j))
 =x_13(0)=1.                                               (3)
```

It remains to check chromatic growth.  Suppose `Sh(M)` has a proper coloring
with `r` colors.  For each `j`, let

```text
A_j={ color(i,j) : i<j }.
```

The `M` subsets `A_j` are pairwise distinct.  Indeed, if `j<k` and
`A_j=A_k`, then `color(j,k)` belongs to `A_k=A_j`; hence it equals
`color(i,j)` for some `i<j`.  But `(i,j)` and `(j,k)` are adjacent, contrary
to properness.  Therefore `M<=2^r`, proving `(LS7)`.  Taking the disjoint
union over unbounded `M` proves infinite chromatic number.
