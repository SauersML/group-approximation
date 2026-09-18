---
rg: 2
id: free-products-with-a-finite-factor-are-contracting-rsgs
kind: claim
title: A free product of a nontrivial hyperbolic group with a nontrivial finite group (other than Z/2 * Z/2) is isomorphic to a contracting rational similarity group
distinct_from:
  hyperbolic-groups-embed-in-contracting-rsgs: that is the Belk--Bleak--Matucci--Zaremsky embedding of every hyperbolic group into a contracting RSG, obtained by passing to the free product with Z; this is an isomorphism, for free products whose free factor is finite rather than Z.
  contracting-rsgs-closed-under-products-with-finite-groups: that adds a finite direct factor to a contracting RSG; this handles a finite free factor.
  non-elementary-hyperbolic-groups-are-contracting-rsgs: that is BBMZ-hyperbolic Question 1.1 for all non-elementary hyperbolic groups, which stays OPEN; this settles the free products with a finite free factor.
artifacts:
  - research/artifacts/gq-bh-bh-free-23-rsg-q11.md
---

**ESTABLISHED** by `free-product-finite-factor-contracting-rsg-proof` (lane `bh-free-23`,
lane proof, not independently reviewed). No priority is claimed: the argument is the finite-factor
analogue of Belk--Bleak--Matucci--Zaremsky's treatment of `G * Z`
(arXiv:2309.06224v3, `thrm:FreeProductBoundary`), read at source.

## Statement

Let `G` be a nontrivial hyperbolic group with finite generating set `S_G`, and let `F` be a
nontrivial finite group, with `|G| = |F| = 2` excluded. Give `G * F` the generating set
`S = S_G ∪ (F \ {1})`. Then:

1. the horofunction boundary `∂_h(G * F)` has no isolated points;
2. `G * F` acts faithfully on it;
3. the type graph of `G * F` has an irreducible core;
4. the induced action on the address space `C_r` is a contracting RSG.

Hence `G * F` is isomorphic to a contracting rational similarity group.

## Consequences

- Every free product of two or more nontrivial finite groups, other than `Z/2 * Z/2`, is
  isomorphic to a contracting RSG. Example: `PSL_2(Z) ≅ Z/2 * Z/3`. (Iterate: `A_1 * … * A_k`
  is `(A_1 * … * A_{k-1}) * A_k`, and the first factor is hyperbolic.)
- `G * Z/n` is isomorphic to a contracting RSG for every nontrivial hyperbolic `G` and `n ≥ 2`
  (with `n ≥ 3` when `|G| = 2`).
- With `contracting-rsgs-closed-under-products-with-finite-groups`: `(G * F) × F'` is isomorphic
  to a contracting RSG for every finite `F'`. These groups have nontrivial finite normal
  subgroups when `F' ≠ 1`.

This is a partial answer to BBMZ-hyperbolic Question 1.1
(`non-elementary-hyperbolic-groups-are-contracting-rsgs`).
