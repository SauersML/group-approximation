---
rg: 2
id: stw59-nonabelian-component-groups-limit-proof
kind: route
title: Twisted evaluation towers over circle-sphere bases carry the nonabelian finite-stage groups injectively into a simple limit
target: stw59-nonabelian-unitary-component-groups
requires:
  - gauge-components-over-circle-sphere-towers
  - stw59-exact-factorial-unitary-component-groups
artifacts:
  - research/artifacts/stw59-nonabelian-unitary-component-groups-2026-09-11.md
  - research/artifacts/stw59-unique-trace-and-matrix-stability-2026-09-05.md
---

Take r_i = n 2^i, X_i = S^1 x S^(2n-1) x product_(j<i) CP^(r_j), and
E_i = C^n direct-sum direct-sum_(j<i) L_(j+1)^(direct-sum r_j), with dense-tail
evaluation points and
phi_i(a) = pi_i^* a direct-sum (a(x_i) tensor 1_(L_(i+1))).

Each evaluation matrix contracts in U(r_i). So phi_i acts on components
as extension by the identity on the new tautological block, which the
finite-stage prerequisite shows is injective, an isomorphism on the
central Z/n! kernels, and pr^* on K^1.

Components of the unital injective limit are the direct limit of stage
components, by polar approximation and finite-stage path detection
(factorial prerequisite, Corollary 4). K1 is continuous, and the
evaluation block factors through matrices and so is zero on K1. Direct
limits of exact sequences are exact, which gives the central extension
of K1(B_n) by Z/n!. The stage-zero commutator keeps its exact order n.

Dense tails give simplicity. Equal-rank blocks contract traces to a
unique trace. Nistor's theorem gives sr(A_i) = 2, so sr(B_n) <= 2; stable
rank one would force K1-injectivity, contradicting the commutator, so
sr(B_n) = 2. K1(B_n) is a direct limit of free groups Z^2 tensor K^0(Y_i)
along split injections, hence free of countably infinite rank.
