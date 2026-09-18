---
rg: 2
id: free-by-virtually-free-groups-satisfy-boone-higman-proof
kind: route
title: Free-by-(virtually free) groups lie in BS_Z or BS_{F_k}, which Bux–Llosa Isenrich–Wu Theorems 12.2 and 12.5 cover
target: free-by-virtually-free-groups-satisfy-boone-higman
requires:
  - virtually-free-extensions-lie-in-generalized-bs-classes
  - bliw-locally-finite-tree-actions-embed-in-fp-simple-groups
  - free-generalized-bs-groups-have-type-a-overgroups
artifacts:
  - research/artifacts/gq-bh-bh-free-extensions-bliw-section-11-12.md
---

1. By `virtually-free-extensions-lie-in-generalized-bs-classes` with
   `N = F_k`, which is finitely generated and infinite, `E ∈ BS_{F_k}`.
2. **k = 1.** BLIW Theorem 12.2: every group in `BS_Z` embeds in a simple group of type `F_∞`.
   Its faithful witness is the HNN extension `BS(1,2)`, via strong scale invariance (Theorem 12.1).
3. **k ≥ 2.** BLIW Theorem 12.5: every group in `BS_{F_k}` embeds in a simple group of type `F_∞`.
   Its faithful witness is a Burger–Mozes amalgam (their Theorem 12.6).
4. **Permutational form, k ≥ 2.** Remark 12.7, imported in `free-generalized-bs-groups-have-type-a-overgroups`.

The statements of 12.1, 12.2, 12.5 and 12.7 were read in §12 of the MSI text extract (see artifact).
`bliw-locally-finite-tree-actions-embed-in-fp-simple-groups` is required for Theorem 11.1, through
which 12.2 and 12.5 are proved. The paper states only the free-by-cyclic consequence. The
free-by-free and free-by-(virtually free) consequences are the membership step 1, recorded here.
