---
rg: 2
id: forest-artin-groups-satisfy-permutational-boone-higman-proof
kind: route
title: The blocks of a forest are vertices and edges, whose Artin groups are Z and dihedral Artin groups, all in B_A; apply the block reduction
target: forest-artin-groups-satisfy-permutational-boone-higman
requires:
  - artin-pbh-reduces-along-folding-separators
  - spherical-artin-groups-satisfy-permutational-boone-higman
  - aut-free-groups-satisfy-permutational-boone-higman
  - boone-higman-type-a-class-closed-under-finite-extensions
  - type-a-action-gives-boone-higman-for-subgroups
---

**1. Blocks of a forest.** A forest has no cycles, so its blocks are its isolated vertices and its edges (every edge of a forest is a bridge).

**2. The block groups.**
- An isolated vertex gives `A = Z`. It lies in `B_A`: `Z = A(A_1)` is the braid group on two strands, covered by BFFHZ's braid case in `aut-free-groups-satisfy-permutational-boone-higman`; alternatively `Z ≤ A(I_2(3))`.
- An edge with label `m` gives the dihedral Artin group `A(I_2(m))`. Its Coxeter group is dihedral of order `2m`, so it is of spherical type, and it lies in `B_A` by `spherical-artin-groups-satisfy-permutational-boone-higman`, or directly by BFFHZ Corollary B (types `I_2(m)`), imported in `aut-free-groups-satisfy-permutational-boone-higman`. For `m = 2` it is `Z^2 = Z × Z`, in `B_A` by closure under finite direct products (`boone-higman-type-a-class-closed-under-finite-extensions`).

**3. Assembly.** By Part 2 of `artin-pbh-reduces-along-folding-separators`, `A_Γ ∈ B_A`.

**4. Consequences.** `B_A` is closed under finite direct products and finite-index overgroups (`boone-higman-type-a-class-closed-under-finite-extensions`), and every finitely generated member embeds in a finitely presented simple group (`type-a-action-gives-boone-higman-for-subgroups`, Zaremsky arXiv:2405.18354 Corollary B; or BFFHZ Theorem C).

QED
