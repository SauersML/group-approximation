---
rg: 2
id: stallings-bieri-sb3-is-finitely-presented-not-f3-proof
kind: route
title: SB_3 is the Bestvina–Brady kernel of the octahedron
target: stallings-bieri-sb3-is-finitely-presented-not-f3
requires:
  - bestvina-brady-kernel-finiteness-theorem
---

1. Let L be the octahedron, the join S^0 * S^0 * S^0 of three pairs of non-adjacent vertices. It is a
   flag complex, since every set of pairwise adjacent vertices uses at most one vertex from each pair
   and so spans a simplex.
2. The right-angled Artin group of a join is the direct product of the RAAGs of the factors, and the
   RAAG of S^0 (two vertices, no edge) is F_2. So A_L = F_2 × F_2 × F_2, with the six vertices as
   standard generators.
3. The Bestvina–Brady kernel BB_L sends every generator to 1, so BB_L = SB_3.
4. L is homeomorphic to S^2. It is 1-connected, and it is not 2-connected, because
   π_2(L) = H_2(L) = Z.
5. By `bestvina-brady-kernel-finiteness-theorem` (item 1), SB_3 is of type F_2, i.e. finitely
   presented, and is not of type F_3. ∎
