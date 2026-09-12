---
rg: 2
id: shell-near-index-obstruction-proof
kind: route
title: Near index forces a normal prefix shift to centralize every shell permutation
target: shell-prefix-germ-is-not-normal-or-finite-index
requires:
  - shell-cantor-embeddings-are-finite-germ-extensions
artifacts:
  - research/artifacts/boone-higman-finite-state-and-shell-germ-limits-2026-09-08.md
---

Identify Q=(E_nu)_p with the near permutation group in the required
claim. It contains an embedded copy of P in ker(I), while I(tau)=1.

If <tau> were normal, every q in Q would conjugate tau to tau or
tau^-1. Index is conjugacy invariant and I(tau)=1, so only tau is
possible. In particular every rho_g would commute with tau modulo
finitely many points, giving

    rho_g(n+1)=rho_g(n)+1

for all sufficiently large n. Hence rho_g is eventually a translation.
As proved in the construction route, a permutation of N with this
property is finitary. This contradicts the infinite support of rho_g
for any g!=1.

For the index assertion, each coset of <tau> in Q contains at most
one member of ker(I). Indeed if two index-zero elements differ by
a power tau^k, taking I gives k=0. A finite-index <tau> would
therefore force ker(I) finite. Its embedded infinite subgroup P
rules this out. Both conclusions hold for every choice of nu.

The statement about the finiteness criterion refers specifically
to its finite-index or normal-subgroup alternatives in
[Belk--Hyde--Matucci, Theorem 1.1](https://arxiv.org/html/2407.03149v1#S1.SS1).
It does not declare a quotient Q/<tau>, since that subgroup is
not normal.
