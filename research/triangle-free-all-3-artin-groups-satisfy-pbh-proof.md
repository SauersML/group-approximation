---
rg: 2
id: triangle-free-all-3-artin-groups-satisfy-pbh-proof
kind: route
title: Cone the graph with hub labels 3; every coned maximal clique is an edge coned to the Euclidean triangle (3,3,3) or a vertex coned to A_2
target: triangle-free-all-3-artin-groups-satisfy-pbh
requires:
  - artin-hub-cones-reduce-pbh-to-coned-cliques
  - aut-free-groups-satisfy-permutational-boone-higman
  - spherical-artin-groups-satisfy-permutational-boone-higman
  - boone-higman-type-a-class-closed-under-finite-extensions
  - type-a-action-gives-boone-higman-for-subgroups
---

**1. The hub labelling.** Put `k_v = 3` for every vertex. Every edge label is 3, and `3 | 3`, so `k` is a hub labelling (`artin-hub-cones-reduce-pbh-to-coned-cliques`).

**2. Maximal cliques.** `Γ` has no triangles, so its maximal cliques are its edges and its isolated vertices.

**3. The coned pieces.**
- An edge `vw` gives the complete graph on `{v, w, e}` with all three labels 3. This is the Artin group of the Euclidean Coxeter group of type Ã_2 (the triangle group `(3,3,3)`, `1/3 + 1/3 + 1/3 = 1`). It lies in `B_A` by BFFHZ Corollary B, types Ã_n, as imported in `aut-free-groups-satisfy-permutational-boone-higman`.
- An isolated vertex `v` gives the edge `v -3- e`, the braid group `A(A_2) = B_3`, in `B_A` by `spherical-artin-groups-satisfy-permutational-boone-higman` (or BFFHZ, type A).

**4. Conclusion.** Part 3 of `artin-hub-cones-reduce-pbh-to-coned-cliques` gives `A_Γ ∈ B_A`. The consequences for products and finite-index overgroups are parts 1--3 of `boone-higman-type-a-class-closed-under-finite-extensions`, and the simple envelope is `type-a-action-gives-boone-higman-for-subgroups`.

**5. The four-cycle, explicitly.** Hub `e` with `m_ea = m_eb = m_ec = m_ed = 3`; the wheel `W_4`.
- Split at `b`: `Λ = {a, c, e}`, `V_1 = {a, b, c, e}`, `V_2 = {a, c, d, e}`. The foldings `b ↦ e` and `d ↦ e` send `aba = bab` to `aea = eae` and `bcb = cbc` to `ece = cec`, relators of `A_Λ = A(a -3- e -3- c)`.
- Split `V_1` at `a`: `Λ' = {b, e}`, pieces `{a, b, e}` and `{b, c, e}`, foldings `a ↦ e` and `c ↦ e`. Likewise `V_2`.
- So `A(W_4)` is an iterated amalgam of four copies of `A(Ã_2)` over copies of `B_3` and `A(a -3- e -3- c)`, each amalgamated subgroup a retract of both sides, and the all-3 four-cycle group is the standard parabolic subgroup on `{a, b, c, d}`.

QED
