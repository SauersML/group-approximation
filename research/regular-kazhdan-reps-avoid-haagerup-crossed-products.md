---
rg: 2
id: regular-kazhdan-reps-avoid-haagerup-crossed-products
kind: claim
title: An abelian crossed product by a Haagerup actor has no regular representation of an infinite Kazhdan group
distinct_from:
  haagerup-actors-cannot-host-property-t-algebraic-envelope: that excludes trace-preserving embeddings of property-T II1 factors; this starts from a possibly non-ICC group and proves directly that its regular-character image is a diffuse relatively rigid type-II algebra, so no factoriality assumption is needed.
  kazhdan-finite-cocycles-cannot-enter-haagerup-actions: that closes orthogonal normalizer sums by equivalence-relation Haagerup property; this allows arbitrary nonnormalizing Fourier coefficients and has no support bound.
  three-actor-grades-support-an-exact-hadamard-cell: that constructs one exact nonnormalizing matrix cell without a source multiplication table; this proves that no assembly of such cells can carry the regular representation of an infinite property-T group inside a Haagerup-actor crossed product.
---

Let an infinite countable property-`(T)` group `Q` be represented by unitaries
`(V_q)_(q in Q)` in

```text
M=A rtimes G,
```

where `A` is an abelian finite von Neumann algebra and `G` is Haagerup.  It is
impossible that

```text
V_q V_r=V_(qr),                 tau(V_q)=1_(q=e).       (RKR1)
```

This conclusion imposes no Fourier-support, normalizer, Cartan, or
factoriality hypothesis.  In particular it excludes representations assembled
from finitely many nonnormalizing Hadamard or matrix cells per generator.

Apply this to the Mihailova left-right Bernoulli crossed product

```text
L^infinity({-1,1}^Q) rtimes (F_m times F_m),           (RKR2)
```

choosing `Q` as the infinite property-`(T)`, finitely presented nonsofic
Fournier--Facio group.  Since `F_m times F_m` is Haagerup, no exact
regular-trace image of `Q` exists in `(RKR2)`, even by arbitrary
nonnormalizing finite Fourier sums.  Thus both the orthogonal cocycle branch
and the finite Hadamard-cell branch are closed in the simplified left-right
crossed product.

This does not close the full mixed module over
`Gamma_0 times SL_3(Z)`: that actor is non-Haagerup, and cells using grades
outside the free left-right subgroup are not contained in `(RKR2)`.  The
remaining Mihailova envelope problem must use those genuinely arithmetic
grades (or embed the fixed non-CE factor without first representing `Q`).
