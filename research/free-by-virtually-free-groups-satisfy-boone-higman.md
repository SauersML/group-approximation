---
rg: 2
id: free-by-virtually-free-groups-satisfy-boone-higman
kind: claim
title: Every extension of a finitely generated free group by a finitely generated virtually free group, in particular every free-by-free group, embeds in a simple group of type F_∞
distinct_from:
  baumslag-solitar-and-free-by-cyclic-satisfy-boone-higman: that imports the free-by-cyclic case stated by Bux–Llosa Isenrich–Wu; this draws the free-by-free and free-by-(virtually free) cases from their Theorems 12.2 and 12.5, which the paper does not state.
  free-generalized-bs-groups-have-type-a-overgroups: that imports the permutational form for the class BS_{F_k}; this identifies free-by-(virtually free) groups as members of that class.
artifacts:
  - research/artifacts/gq-bh-bh-free-extensions-bliw-section-11-12.md
---

**ESTABLISHED** (lane proof, not reviewed; route
`free-by-virtually-free-groups-satisfy-boone-higman-proof`). It is a direct corollary of Bux–Llosa
Isenrich–Wu Theorems 12.2 and 12.5 (arXiv:2408.05673v2); no priority claimed.

Let `1 -> F_k -> E -> Q -> 1` be exact with `1 ≤ k < ∞` and `Q` finitely generated virtually free.
Then `E` embeds in a simple group of type `F_∞`, so `E` satisfies `boone-higman-conjecture`.
In particular this covers:
- every free-by-free group `F_k ⋊ F_m`;
- every free-by-cyclic group;
- every `F_k`-by-(finite-by-free) group, e.g. `F_k`-by-`SL_2(Z)` extensions.

For `k ≥ 2`, `E` also satisfies the permutational form: it embeds in a finitely presented group with
an action of type (A), by `free-generalized-bs-groups-have-type-a-overgroups`.
