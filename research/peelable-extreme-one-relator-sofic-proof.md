---
rg: 2
id: peelable-extreme-one-relator-sofic-proof
kind: route
title: Peel the extreme Magnus letter through cyclic amalgams and HNN extensions
target: peelable-extreme-one-relator-groups-are-sofic
requires: []
artifacts:
  - research/artifacts/peelable-extreme-one-relator-sofic-2026-09-11.md
  - research/artifacts/triangular-bs-chain-proof-2026-09-07.md
  - research/artifacts/mixed-conjugator-one-relator-proof-2026-09-07.md
---

Complete written proof in the first artifact. Its literature inputs are
Magnus' Freiheitssatz, amalgam and HNN normal forms, Elek--Szabo amalgam
permanence over amenable subgroups (arXiv:1010.3424, Theorem 1),
Ciobanu--Holt--Rees HNN permanence (arXiv:1212.2739, Proposition 3.2), and
sofic-by-amenable permanence. Directed-colimit permanence is proved in the
second artifact, and the exact Magnus kernel presentation in the third.

1. `G = K rtimes <t>` with `K = <a_i | W_i>`, so `G` is sofic iff `K` is.
2. `K` is the directed colimit of truncations `T_[p,q]`. Each is the free
   product of a free group with the group `S_q` on letters `a_i`,
   `i <= n+q`, and relators `W_p,...,W_q`.
3. `S_j = S_(j-1) *_(F_j) B_j`. Here `F_j = <a_(m+j),...,a_(n+j-1)>` is free
   in `S_(j-1)` by the inductive invariant and in `B_j` by the Freiheitssatz.
4. Peelability writes `W_j` as `y^e U`, `y^e U y^(-e) V`, or `y^e U y^e V`,
   with `y = a_(n+j)` and `U,V` nontrivial in `F_j`. These give, respectively,
   a root amalgam; a cyclic HNN extension followed by a root amalgam; and a
   square-root amalgam followed by a root amalgam. `U != V` in the last case
   because `W_0` is not a proper power.
5. The invariant passes on: `S_j` stays torsion-free and sofic, and the
   Freiheitssatz in the embedded `B_j` keeps `a_(m+j+1),...,a_(n+j)` free.

The bottom-letter case is the same argument with indices reversed.
