---
rg: 2
id: stw59-exact-factorial-unitary-component-groups
kind: claim
title: The entire unitary component group of the simple factorial AH algebra is cyclic of order n factorial
distinct_from:
  stw59-simple-ah-factorial-unitary-torsion: This computes the whole component group at every finite stage and in the same simple limit; the earlier theorem only identifies a cyclic subgroup of exact factorial order.
  stw59-simple-ah-non-k1-injective: The n=2 case identifies the whole component group as Z/2, rather than only detecting a nonzero order-two element.
artifacts:
  - research/artifacts/stw59-exact-factorial-component-groups-2026-09-05.md
---

For n>=2 and H=direct-sum_j L_j^(direct-sum d_j) over
Y=product_j CP^(d_j), the bundle E=C^n direct-sum H on S^(2n) times Y
satisfies

    U(Gamma(End E))/U0(Gamma(End E)) ~= Z/(n!).

The canonical characteristic unitary u_n direct-sum 1_H generates
the entire group. In the explicit factorial twisted AH system,
every connecting map takes this generator to the next generator
and induces an isomorphism on the whole component group. Hence

    U(A^(n))/U0(A^(n)) ~= Z/(n!),   K1(A^(n))=0.

The algebra is the same simple unital separable nuclear stably finite
AH algebra already constructed. For n=2 this computes the original
LIX example's entire component group as Z/2. No statement is made
that every finite group is realized as an entire component group.

ROUTES

stw59-gauge-section-euler-image-proof
