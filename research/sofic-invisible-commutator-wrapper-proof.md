---
rg: 2
id: sofic-invisible-commutator-wrapper-proof
kind: route
title: Turn the Slofstra--Vidick invisible involution into a wandering commutator
target: exact-fd-wandering-reflection-promotion-can-remain-sofic
requires:
  - exact-fd-invisibility-has-no-general-hs-robustification
---

Free-product the Slofstra--Vidick group with one infinite cyclic generator
`t`.  The word `h=[t,c]` is cyclically reduced and therefore has infinite
order, while every exact finite-dimensional representation kills it because
it kills `c`.  Direct-product this group with the already-wordized verifier
base and put `w=vh`.  Exact finite-dimensional representations see `w=v`,
but the regular tensor-product trace gives

```text
||q(w-v)q||_2^2=2 tau(q).
```

Soficity is preserved by both products, so canonical matrix microstates
realize this positive floor.  This simultaneously verifies all algebraic
claims and disproves approximate promotion from exact invisibility alone.

