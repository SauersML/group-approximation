---
rg: 2
id: simple-kazhdan-full-mf-radical-proof
kind: route
title: Combine MF-to-weak-quasidiagonality with the Ozawa--Thom quotient theorem
target: simple-kazhdan-groups-have-full-mf-radical
requires:
  - dadarlat-matricial-stability-obstruction
---

Suppose first that `K` were MF.  Dadarlat states immediately before Theorem
1.2 that

```text
MF  implies  weakly quasidiagonal.                       (SKM2)
```

His Proposition 3.19, attributed to Ozawa--Thom, would therefore give an
infinite residually finite quotient `K/N`.  Since `K` is simple and the
quotient is nontrivial, `N=1`, so `K` itself would be residually finite.  But
an infinite simple group has no nontrivial finite quotient: the kernel of a
nontrivial map to a finite group would be a proper normal subgroup, hence
trivial, forcing the infinite group to embed in a finite one.  This
contradiction proves that `K` is not MF.

Now let `f:K->M` be a homomorphism to an MF group.  Its kernel is normal in
`K`, hence is either `1` or `K`.  In the first case `K` embeds in the MF group
`M`, and subgroups of MF groups are MF, contradicting the first paragraph.
Thus `ker(f)=K` for every such `f`.  Intersecting these kernels gives
`Rad_MF(K)=K`.

The primary statements were checked in the PDF of arXiv:2007.12655v2: the
implication `(SKM2)` is printed on page 2, and Proposition 3.19 with its proof
is on page 10.  No `gamma`-element, finite presentation, linearity, or
stability hypothesis occurs in this argument.
