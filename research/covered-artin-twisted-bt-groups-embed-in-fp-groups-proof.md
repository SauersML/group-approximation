---
rg: 2
id: covered-artin-twisted-bt-groups-embed-in-fp-groups-proof
kind: route
title: The assembled word-problem algorithm gives a finitely presented host for AV_A
target: covered-artin-twisted-bt-groups-embed-in-fp-groups
requires:
  - artin-wp-from-covered-maximal-free-of-infinity-subgraphs
  - self-twisted-bt-group-fp-embedding-iff-solvable-wp
---

1. `A` is finitely generated, and by
   `artin-wp-from-covered-maximal-free-of-infinity-subgraphs` it has solvable word
   problem.
2. Apply `self-twisted-bt-group-fp-embedding-iff-solvable-wp` with `G = A`, through the
   chain (4)⇒(3)⇒(2)⇒(1).
   - (4)⇒(3) gives a solvable word problem for `AV_A`.
   - (3)⇒(2) holds because such a group is computably presented.
   - (2)⇒(1) gives a finitely presented group containing `AV_A`.

So `AV_A` embeds in a finitely presented group. ∎

*Remark.* Applying `clapham-fp-embedding-preserves-word-problem` to `AV_A` gives a host
that also has solvable word problem. The claim does not use this.
