---
rg: 2
id: three-bridge-is-cyclic-fiber-product-with-finite-cep
kind: claim
title: The trivial three-generator bridge is a cyclic fiber product with effective finite CEP
artifacts:
  - research/artifacts/three-bridge-finite-cep-rope-route-2026-08-25.md
distinct_from:
  bidirectional-hnn-bridge-trivial-value-is-residually-finite: that proves residual finiteness of both bridge values; this identifies the three-generator value as a normal cyclic fiber product and proves extension of all its finite congruences through the ambient direct product.
  positive-rope-profinite-edge-synchronization: that concerns finite quotients of the later benign rope group; this supplies the finite-CEP input for a particular graph benign witness.
---

Let

```text
H=B3(1)=<x,y,t | [t,x^i y x^-i]=1, i in Z>.
```

Under the embedding

```text
x |-> (x_1,x_2),       y |-> (y,1),       t |-> (1,t)
```

from `bidirectional-hnn-bridge-trivial-value-is-residually-finite`, the image
is exactly

```text
H=ker(chi:F(x_1,y) times F(x_2,t) -> Z),
chi(g_1,g_2)=exp_(x_1)(g_1)-exp_(x_2)(g_2).             (BCF1)
```

Consequently `H` is a finitely generated normal subgroup of
`P=F_2 times F_2`, with `P/H=Z`, and the inclusion has effective finite
congruence extension in the refining form:

```text
for every finite quotient beta:H->B there is a finite quotient r:P->C
with ker(r|H) <= ker(beta).                               (BCF2)
```

The quotient `r|H` may refine rather than equal `beta`; this is the exact
kernel direction required by the rope synchronization argument.
