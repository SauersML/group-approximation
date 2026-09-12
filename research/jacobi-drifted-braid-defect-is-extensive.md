---
rg: 2
id: jacobi-drifted-braid-defect-is-extensive
kind: claim
title: The drifted rank-one Jacobi braid defect occupies the whole truncated prefix
distinct_from:
  no-linear-symplectic-splitting-of-truncated-weyl-levels: that obstructs a module-linear symplectic inclusion; this computes the exact finite-word braid obstruction created by combining both elementary charts with the Fourier switch.
  truncated-weyl-two-chart-boundary: that shows each parabolic separately has a one-cell boundary; this shows that closing the two parabolics through the rank-one braid spreads the defect over essentially every prefix coordinate.
  termwise-finite-reynolds-holonomy-has-zero-rank-gap: that is a dimension count for conjugate finite Reynolds tables; this obstruction already occurs in the symplectic Jacobi actor before any Reynolds packet is attached.
---

In `SL_2(F_2[u])`, put

```text
A_s=[[1,s],[0,1]],       B_s=[[1,0],[s,1]],
F=[[0,1],[1,0]].                                            (JBD1)
```

At `s=1`, the rank-one elementary group is `SL_2(F_2)=S_3` and

```text
A_1 B_1 A_1=B_1 A_1 B_1=F.                                (JBD2)
```

After the parameter drift `1 |-> u`, the two braid words differ by

```text
A_u B_u A_u-B_u A_u B_u
 =u(1+u^2)F.                                               (JBD3)
```

On `R_N^2`, where `R_N=F_2[u]/(u^N)`, the right side of `(JBD3)` has
`F_2`-rank

```text
2(N-1).                                                     (JBD4)
```

Thus the defect has only a two-dimensional kernel and is not supported on
the transverse two-dimensional boundary of either truncated-Weyl chart.
It acts nontrivially on their common `2(N-2)`-dimensional core for every
`N>=3`.

Equivalently, if one insists on transporting the first braid expression and
keeps the fixed Fourier word, the uniquely forced correction is

```text
H=F^(-1) A_u B_u A_u
 =[[u,1+u^2],[1+u^2,u^3]],                                (JBD5)
```

and

```text
rank_F2(H-I on R_N^2)=2N-1.                               (JBD6)
```

The correction is indeed one fixed polynomial Jacobi word, independent of
`N`, but it moves all but one dimension of the prefix.  Central/projective
signs cannot repair `(JBD3)`, because they disappear in the symplectic
quotient.

Consequently there is no compressor homomorphism on a group retaining the
exact rank-one braid and satisfying simultaneously

```text
A_1 |-> A_u,             B_1 |-> B_u.                     (JBD7)
```

Nor can a holonomy which is trivial on the common chart core absorb the
failure.  A viable two-chart Jacobi construction must do one of two genuinely
stronger things: keep the upper and lower rank-one actors duplicated so the
braid is never transported, or use the stabilized tail to cancel an
**extensive** cocycle.  The one-cell geometry `(TWC1)--(TWC3)` alone does not
localize the closed two-chart action holonomy.

