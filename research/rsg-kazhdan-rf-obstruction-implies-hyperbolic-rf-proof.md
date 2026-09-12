---
rg: 2
id: rsg-kazhdan-rf-obstruction-implies-hyperbolic-rf-proof
kind: route
title: Kapovich--Wise and an Olshanskii common quotient give a Kazhdan hyperbolic group without finite quotients, which embeds in a contracting rational similarity group
target: rsg-kazhdan-rf-obstruction-implies-hyperbolic-rf
requires:
  - kapovich-wise-rf-iff-finite-quotients
  - torsion-free-hyperbolic-kazhdan-partner-exists
  - olshanskii-g-subgroup-quotient-theorem
  - hyperbolic-groups-embed-in-contracting-rsgs
artifacts:
  - research/artifacts/hyperbolic-quotientless-kazhdan-proof-2026-09-11.md
  - research/artifacts/bh-rational-similarity-hosts-2026-09-12.md
---

Assume some word-hyperbolic group is not residually finite.

1. **A hyperbolic group without finite quotients.** By
   `kapovich-wise-rf-iff-finite-quotients`, some nontrivial hyperbolic group `G_0`
   has no nontrivial finite quotient. It is infinite, since a finite group is its
   own finite quotient.
2. **Adding property (T).** This is Section 4 of
   `research/artifacts/hyperbolic-quotientless-kazhdan-proof-2026-09-11.md`, which
   uses exactly the other two imports.
   - `G_0` is non-elementary, since infinite elementary hyperbolic groups are
     virtually cyclic and so residually finite.
   - Let `G_1` be `G_0` modulo its maximal finite normal subgroup. It is
     non-elementary hyperbolic, has no nontrivial finite quotient, and has trivial
     finite radical.
   - Let `K` be the torsion-free non-elementary hyperbolic Kazhdan group of
     `torsion-free-hyperbolic-kazhdan-partner-exists`, and put `H = G_1 * K`.
   - In the Bass--Serre tree of `H` the edge stabilizers are trivial, so
     `E_H(G_1) = E_H(K) = E(H) = 1`.
   - By `olshanskii-g-subgroup-quotient-theorem` there is a quotient `p: H -> Q`
     onto a non-elementary hyperbolic group with `p(G_1) = p(K) = Q`.
   - `Q` has property (T) as a quotient of `K`. It has no nontrivial finite
     quotient, since any finite quotient of `Q` restricts to one of `G_1`. It is
     infinite, since it is non-elementary.
3. **The host.** By `hyperbolic-groups-embed-in-contracting-rsgs`, `Q` embeds in a
   contracting rational similarity group `S`.
4. **Conclusion.**
   - `Q` is not residually finite: it is infinite, and every nontrivial element
     lies in every finite-index normal subgroup, which is all of `Q`.
   - So `S` contains a subgroup with property (T) that is not residually finite.

Contrapositive: if every Kazhdan subgroup of every contracting rational similarity
group is residually finite, then every word-hyperbolic group is residually finite.
