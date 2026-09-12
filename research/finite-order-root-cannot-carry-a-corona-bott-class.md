---
rg: 2
id: finite-order-root-cannot-carry-a-corona-bott-class
kind: claim
title: A commuting pair containing a finite-order root has zero corona Bott class
distinct_from:
  corona-commuting-torsion-lifts: that simultaneously lifts a countable commuting bounded-torsion family; this allows the second unitary to have infinite order and computes the resulting relative Bott class.
  matrix-corona-k0-index-survives: that shows arbitrary almost-commuting lifts can carry nonzero Bott classes in K-zero; this proves those classes vanish when either corona unitary has fixed finite order.
  exel-loring-mark-quantization: that proposes a relative invariant involving an infinite-order central mark and external homological input; this is an internal lifting obstruction for the finite-order binary-Leavitt root itself.
artifacts:
  - research/finite-order-root-corona-bott-proof.md
---

Let

```text
Q_d=prod_n M_(d_n)(C) / direct-sum_n M_(d_n)(C),
```

and let commuting unitaries `u,v in Q_d` satisfy `u^m=1` for one fixed
`m>=1`.  The pair has commuting unitary lifts: there are unitary matrices
`U_n,V_n` representing `u,v` with

```text
U_n^m=1,                    U_nV_n=V_nU_n               (FRB1)
```

at every sufficiently late coordinate.  Consequently the homomorphism

```text
C(T^2) -> Q_d,             z_1 |-> u, z_2 |-> v         (FRB2)
```

sends the reduced Bott generator to zero in `K_0(Q_d)`.

In particular, no ordinary two-unitary Bott or winding argument can use a
binary-Leavitt elementary root as one of its commuting coordinates.  A
genuinely different relative-index route would need two infinite-order
coordinates plus a new internal theorem quantizing their index by the
marked root projection.  The Steinberg and Leavitt relations currently
supply neither that quantization nor a nonzero index.

