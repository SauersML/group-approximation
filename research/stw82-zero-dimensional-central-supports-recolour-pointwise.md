---
rg: 2
id: stw82-zero-dimensional-central-supports-recolour-pointwise
kind: claim
title: Zero-dimensional central support geometry admits pointwise-optimal recolouring
artifacts:
  - research/artifacts/stw82-central-support-recolouring-audit-2026-08-30.md
distinct_from:
  stw82-indivisible-order-zero-reuse-is-graph-colouring: that keeps every outgoing map intact and is governed by the global support-overlap graph; this splits maps over common central spectral blocks and can remove odd cycles in that graph.
  stw82-spectral-interval-band-depth-reuses-colours: that assumes prescribed interval localization in the functional calculus of one positive contraction; this treats arbitrary support functions over any compact zero-dimensional common spectrum and proves the optimal label count.
  stw82-minimal-support-coupled-cover-number: that gives a chromatic obstruction when minimal supports have no common central decomposition; this identifies a setting in which central blockwise replacement evades that obstruction.
---

Let `V` be finite, let `F_v` be unital C*-algebras, and let

```text
phi_v:F_v->B
```

be cpc order-zero maps.  Put `h_v=phi_v(1_(F_v))` and discard the zero
maps.  Suppose there is a unital abelian C*-algebra

```text
C subseteq M(B) intersect (union_v phi_v(F_v))'
```

which contains every `h_v` and whose spectrum `X` is zero dimensional.
Define the pointwise support multiplicity

```text
m=max_(x in X) |{v in V:h_v(x)>0}|.                  (Z1)
```

Then, for every `epsilon>0`, there are projections
`c_(v,k) in C`, for `k=1,...,m`, such that

```text
c_(v,k)c_(w,k)=0                         (v!=w),      (Z2)
norm((1-sum_k c_(v,k))h_v)<epsilon.                  (Z3)
```

The maps

```text
psi_(v,k)(a)=c_(v,k)phi_v(a)                        (Z4)
```

are cpc order zero, satisfy

```text
norm(phi_v-sum_k psi_(v,k))<epsilon,                 (Z5)
```

and, for each fixed `k`, their direct sum over `v` is cpc order zero.

The number `m` is optimal among asymptotically exact coupled covers with
cutters in `C`: if `d` labels admit such covers with error tending to zero,
then `d>=m`.

There is a stronger exact form when

```text
C=directSum_(j=1)^N C z_j subseteq Z(M(B))           (Z6)
```

is finite dimensional and central.  Put

```text
m_0=max_j |{v:z_j h_v!=0}|.
```

Then `m_0` is the least number of labels in any exact coupled cover, even
when competing positive cutters may lie anywhere in `M(B)`.  Central
projection cutters attain `m_0`, and (Z3)--(Z5) hold with zero error.

Consequently, if a C*-algebra `A` has arbitrarily accurate
finite-dimensional nuclear approximations whose outgoing order-zero maps
have a common zero-dimensional abelian support algebra as above and
pointwise multiplicity at most `r+1`, then

```text
dim_nuc(A)<=r.                                       (Z7)
```

This criterion can beat indivisible graph colouring.  In `C^3`, let
`e_a,e_b,e_c` be the coordinate projections and take

```text
h_1=(e_a+e_c)/2,   h_2=(e_a+e_b)/2,   h_3=(e_b+e_c)/2.
```

The global support-overlap graph is `K_3`, but the pointwise multiplicity is
two.  Splitting at the three central atoms and changing the two labels from
atom to atom gives an exact two-colour replacement.  Moreover
`h_1+h_2+h_3=1`, so this example has the contractive total support expected
of one outgoing cpc approximation.
