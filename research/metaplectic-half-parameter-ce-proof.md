---
rg: 2
id: metaplectic-half-parameter-ce-proof
kind: route
title: Deligne's finite residual theorem makes the metaplectic double cover residually finite
target: metaplectic-half-parameter-is-ce
requires:
  - maslov-ce-subgroup-classifies-finite-deligne-covers
---

Let `E_infinity` be the inverse image of `Sp_4(Z)` in the universal cover of
`Sp_4(R)`, with central kernel `Z<z>`, and put

```text
E_2=E_infinity/<z^2>.
```

Deligne's finite-residual theorem says that the finite residual of the
arithmetic inverse image is exactly the image of `2Z`.  In the degree-two
quotient this subgroup is trivial, so `E_2` is residually finite.  A convenient
current source is Stover, *Residual finiteness and discrete subgroups of Lie
groups*, arXiv:2407.07680v2, Theorem 1.5 and the sentence immediately after it:
for the central deck group `Z`, the intersection of the kernels of all finite
quotients is `2Z`.

Residual finiteness implies hyperlinearity.  The central Fourier decomposition
proved in `maslov-ce-subgroup-classifies-finite-deligne-covers` gives, for every
`q`,

```text
E_q hyperlinear  iff  1/q belongs to E_CE.
```

Taking `q=2` proves `(MHP1)`.  Finally a finite subgroup of `R/Z` containing
`1/2` has even order.

