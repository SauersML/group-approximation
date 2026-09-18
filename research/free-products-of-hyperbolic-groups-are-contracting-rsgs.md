---
rg: 2
id: free-products-of-hyperbolic-groups-are-contracting-rsgs
kind: claim
title: Every free product A * B of nontrivial hyperbolic groups, other than Z/2 * Z/2, is isomorphic to a contracting rational similarity group
distinct_from:
  free-products-with-a-finite-factor-are-contracting-rsgs: that is the special case of a finite factor; this is every free product of two nontrivial hyperbolic groups.
  hyperbolic-groups-embed-in-contracting-rsgs: that is the BBMZ embedding of every hyperbolic group into a contracting RSG, via G * Z; this is an isomorphism for every freely decomposable hyperbolic group, and generalizes the BBMZ G * Z theorem from a Z factor to an arbitrary one.
  non-elementary-hyperbolic-groups-are-contracting-rsgs: that is BBMZ-hyperbolic Question 1.1, which stays OPEN; this settles its freely decomposable case.
artifacts:
  - research/artifacts/gq-bh-bh-free-23-rsg-q11.md
---

**ESTABLISHED** by `hyperbolic-free-product-contracting-rsg-proof` (lane `bh-free-23`, lane
proof, not independently reviewed). No priority is claimed. The proof extends
Belk--Bleak--Matucci--Zaremsky's argument for `G * Z` (arXiv:2309.06224v3,
`thrm:FreeProductBoundary`, read at source) to an arbitrary second factor.

## Statement

Let `A` and `B` be nontrivial hyperbolic groups with finite generating sets `S_A` and `S_B`,
not both of order 2. Give `A * B` the generating set `S_A ∪ S_B`. Then:

1. `∂_h(A * B)` has no isolated points;
2. `A * B` acts faithfully on it;
3. its type graph has an irreducible core;
4. the induced action is a contracting RSG.

Hence `A * B` is isomorphic to a contracting rational similarity group.

## Consequences

- **Every freely decomposable non-elementary hyperbolic group** is isomorphic to a contracting
  RSG. Examples: `π_1(Σ_g) * π_1(Σ_h)` for closed surfaces of genus `g, h ≥ 2`, `F_n` for `n ≥ 2`,
  and any Kazhdan hyperbolic group `* Z/3`.
- With `contracting-rsgs-closed-under-products-with-finite-groups`, the same holds for
  `(A * B) × F` with `F` finite.
- For BBMZ-hyperbolic Question 1.1 (`non-elementary-hyperbolic-groups-are-contracting-rsgs`),
  the remaining cases are the freely indecomposable groups: one-ended groups, and groups that
  split only over nontrivial finite subgroups. Groups whose finite radical is not a direct
  factor also remain.
