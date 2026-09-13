---
rg: 2
id: self-twisted-bt-group-of-infinite-group-is-not-fp
kind: claim
title: The twisted Brin-Thompson group of an infinite group acting on itself by translation is not finitely presented
distinct_from:
  twisted-brin-thompson-finite-presentation-criterion: that is Zaremsky's criterion for every faithful action; this applies its pair-orbit condition to the translation action of an infinite group, where the condition always fails.
artifacts:
  - research/artifacts/zp-z3-08-twisted-bt-artin-2026-09-13.md
---

**ESTABLISHED** by `self-twisted-bt-group-of-infinite-group-is-not-fp-proof`.

Let `G` be an infinite group acting on itself by left translation. Then the twisted
Brin–Thompson group `G·V_G` is not finitely presented.

In particular `AV_A` is not finitely presented for any Artin group `A` on a nonempty
generating set. Such an `A` is infinite: sending every standard generator to
`1 ∈ Z` is a homomorphism, because both sides of every braid relation have the same
length.

**Consequence for Zaremsky Problem 3.8.** A finitely presented host of `AV_A` is always
a proper overgroup. This refutes `every-artin-self-twisted-bt-group-is-finitely-presented`
and kills the route `artin-twisted-bt-fp-host-via-own-finite-presentation`.
