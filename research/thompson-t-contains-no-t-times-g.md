---
rg: 2
id: thompson-t-contains-no-t-times-g
kind: claim
title: For every nontrivial group G, Thompson's group T has no subgroup isomorphic to T x G
distinct_from:
  thompson-t-has-no-subgroup-isomorphic-to-t-times-t: that is the case G = T, obtained from torsion; this covers every nontrivial G, including torsion-free ones such as Z, F, and T x T itself
---

Let `G` be any group. If there is an injective homomorphism `T × G → T`, then
`G = 1`.

In particular `T` contains no copy of `T × Z`, `T × F`, `T × T`, or
`T × Z/q` for `q ≥ 2`. This answers the torsion-free versions of Zaremsky
Problem 2.17 that the Klein-four argument
(`thompson-t-has-no-subgroup-isomorphic-to-t-times-t-proof`) does not reach.

Derivation: route `thompson-t-contains-no-t-times-g-proof`.
