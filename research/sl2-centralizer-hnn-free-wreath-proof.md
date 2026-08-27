---
rg: 2
id: sl2-centralizer-hnn-free-wreath-proof
kind: route
title: Identify conjugates of the stable letter with free factors indexed by cosets
target: sl2-centralizer-hnn-is-free-coset-wreath
requires: []
---

Put `W=(*_(x in A/C)<z_x>) rtimes A`, where

```text
a z_x a^(-1)=z_(ax).                                  (FWH2)
```

There is a homomorphism `G->W` which is the identity on `A` and sends
`t` to `z_C`: every `c in C` fixes the base coset, so `z_C` commutes with
`C`.

Conversely, define

```text
z_(aC) |-> a t a^(-1).                                (FWH3)
```

This is well-defined.  If `aC=a'C`, write `a'=ac`; then
`a'ta'^(-1)=actc^(-1)a^(-1)=ata^(-1)`.  The universal property of the free
product extends `(FWH3)` to its base group, and conjugation by `A` satisfies
`(FWH2)`, so it extends to `W->G`.  The two maps are inverse on `A`, on `t`,
and on every free-factor generator.  This proves `(FWH1)`.

