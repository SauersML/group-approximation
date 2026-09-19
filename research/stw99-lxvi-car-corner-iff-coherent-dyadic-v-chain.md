---
rg: 2
id: stw99-lxvi-car-corner-iff-coherent-dyadic-v-chain
kind: claim
title: A projection corner contains CAR exactly when its V-class starts a coherent dyadic chain
---

Let `B` be a C\*-algebra and let `p in B` be a projection.  There is a unital
embedding

```text
M_(2^infinity) -> pBp
```

if and only if there are elements `x_n in V(B)`, for `n>=0`, such that

```text
x_0=[p],                 x_n=2 x_(n+1)  for every n.
```

Thus a CAR-containing finite corner requires coherent dyadic divisibility in
the projection monoid, not merely divisibility of `[p]` separately by every
power of two in `K_0(B)`.

The abstract monoid axioms do permit this configuration together with a
properly infinite order unit: see
`stw99-lxvi-truncated-dyadic-monoid-has-finite-halving-seed`.  That consistency
model does not assert C-star realizability, but it shows that the implication
above cannot be turned into a contradiction using only simplicity,
conicality, finiteness, and coherent halving.
