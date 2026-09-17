---
rg: 2
id: non-weakly-sofic-via-large-and-fixed-characteristic-witnesses
kind: route
title: Take the free product of a group without large-characteristic rank models and a group linear sofic in no positive characteristic
target: non-weakly-sofic-group-exists
requires: [non-large-characteristic-linear-sofic-group-exists, group-not-linear-sofic-in-any-positive-characteristic-exists, root-splits-into-large-and-fixed-characteristic-witnesses, non-weakly-sofic-iff-non-finite-field-linear-sofic-group]
---

Let `H` be a witness of component (a) and `G` a witness of component (b).
- `S(H * G)` is contained in `S(H) ∩ S(G)`, which is contained in `Primes ∩ {inf}`, so it is empty.
- So `H * G` is not linear sofic over finite fields. By `non-weakly-sofic-iff-non-finite-field-linear-sofic-group`,
  it is not weakly sofic.
- Full argument: §3 of `root-splits-into-large-and-fixed-characteristic-witnesses-proof`.

The converse also holds: a root witness witnesses both components. So this route loses nothing.
