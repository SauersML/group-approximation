---
rg: 2
id: leavitt-diagonal-compression-is-elementary-amenable-proof
kind: route
title: Split the diagonal idempotents by first letter and quotient an ascending HNN extension
target: leavitt-diagonal-compression-is-elementary-amenable
requires:
  - amenable-implies-operator-mf
artifacts:
  - notes/PROPERTY_T_FREE_MF_ATTEMPT_2026-08-26.md
  - non_mf_groups_exist.tex
---

For a binary word `w`, put `e_w=s_wt_w`.  Prefix cancellation makes the
depth-`k` family pairwise orthogonal with sum one, and

```text
e_w=e_(w0)+e_(w1).
```

Thus `D_k=directSum_(|w|=k) F_2 e_w` is `F_2^(2^k)`, the inclusions split
cylinders into their children, and the union `D` is the ring of locally
constant `F_2`-valued functions on the binary Cantor set.

Elementary groups commute with finite products here, and
`EL_3(F_2)=GL_3(F_2)`.  Hence

```text
Lambda_k=EL_3(D_k)=GL_3(F_2)^(2^k),
Lambda=union_k Lambda_k,
```

so `Lambda` is locally finite.

The two compressor embeddings satisfy

```text
Psi(x_ij(a)) =x_ij(s_0at_0),
Psi'(x_ij(a))=x_ij(s_1at_1).
```

Their coefficient supports are orthogonal, and splitting depth `k+1` by
first letter gives

```text
Lambda_(k+1)=Psi(Lambda_k) x Psi'(Lambda_k).
```

The branch-exchanged compressor belongs to `EL_12(R)` because the
coefficient automorphism interchanging `0` and `1` preserves the defining
Leavitt relations and acts entrywise on elementary matrices.  Since
`q=e_1`, the mark `x_13(q)` belongs to `Lambda_1`.

Finally, conjugation by `tau` realizes `Psi`, so `<Lambda,tau>` is a quotient
of the ascending HNN extension

```text
Lambda*_Psi=<Lambda,t | t lambda t^(-1)=Psi(lambda)>.
```

The increasing union `union_(k>=0)t^(-k)Lambda t^k` is normal and locally
finite, with cyclic quotient.  The HNN extension and its image are therefore
elementary amenable.  The same argument applies to `tau'`.
`amenable-implies-operator-mf` then gives trivial MF radical, while the mark
is nonidentity in the elementary matrix group.  Hence it is MF-visible.

For a character of the ambient elementary group, conjugacy by `tau` and
`tau'` gives the compatible character tower.  Both trivial and regular
characters satisfy it, so no two-compressor conclusion is asserted.
