---
rg: 2
id: fkop-avitzour-free-product-classification
kind: route
title: Apply the Avitzour complete-selflessness theorem and isolate C2 star C2
target: non-dihedral-free-products-are-completely-selfless
requires:
  - robert-tracial-selfless-regularity
artifacts:
  - research/artifacts/stw91-graph-component-selflessness-audit-2026-08-30.md
---

Suppose first that `G` and `H` are not both cyclic of order two.  After
interchanging the factors, assume that `H` has at least three elements.
Choose

```text
g in G \ {e},
h_1,h_2 in H \ {e},       h_1 != h_2.
```

In the canonical group traces, put

```text
u=lambda_G(g),       v_i=lambda_H(h_i).
```

All three unitaries belong to their trace centralizers, and

```text
tau_G(u)=0,
tau_H(v_1)=tau_H(v_2)=0,
tau_H(v_1^* v_2)=0.
```

The last equality follows from `h_1!=h_2`.  Therefore the hypotheses of
Flores--Klisse--O Cobhthaigh--Pagliero,
*Selfless reduced free products and graph products of C-star-algebras*,
[arXiv:2510.24675v3](https://arxiv.org/abs/2510.24675), Theorem A
(Theorem 2.7), hold for

```text
(C*_r(G),tau_G) star (C*_r(H),tau_H).
```

The canonical reduced-free-product representation identifies this probability
space with `(C*_r(G*H),tau_(G*H))`.  The cited theorem gives complete
selflessness.

Conversely, if `G=H=C_2`, then `G*H=D_infinity`, which is virtually cyclic and
amenable.  Amenability makes the trivial representation descend to a
character

```text
epsilon:C*_r(D_infinity)->C.
```

Its kernel is nonzero and proper, so `C*_r(D_infinity)` is not simple.
Complete selflessness implies selflessness, while
`robert-tracial-selfless-regularity` implies that a tracially selfless algebra
is simple.  Hence the infinite-dihedral case is not selfless.

There is no remaining gap.