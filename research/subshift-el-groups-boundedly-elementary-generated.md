---
rg: 2
id: subshift-el-groups-boundedly-elementary-generated
kind: claim
title: Every element of EL_3(LC(X,F_2)⋊Z), for a minimal Cantor homeomorphism, is a product of at most 78 elementary matrices, so the group is a product of 78 root subgroups
distinct_from:
  minimal-cantor-crossed-product-has-stable-rank-at-most-two: that asks for the stable rank of the ring, which is open for one; this bounds elementary generation of EL_3 without any stable rank input, by cutting along towers.
artifacts:
  - research/artifacts/sk-free-6-normal-generation-2026-09-13-part3.md
---

**Statement.** Let `(X,T)` be a minimal homeomorphism of an infinite Cantor set, `R = LC(X,F_2) ⋊_T Z` and `G = EL_3(R)`. Every `h ∈ G` is a product of at most `78` elementary matrices `e_ij(r)`, `r ∈ R`, in a fixed sequence of positions. So `G = e_{i_1j_1}(R) ⋯ e_{i_78j_78}(R)`.

**Consequences.**
- Every conjugation-invariant norm on `G` is bounded (Burago–Ivanov–Polterovich), and every element is a product of at most 78 involutions.
- For a nonempty clopen `V`, `1/inf_μ μ(V) ≤ cw(e_12(χ_V)) ≤ 312(⌊1/inf_μ μ(V)⌋ + 1)`.
- So for infinite minimal subshifts, the simple Kazhdan groups `G_X` are boundedly but not uniformly simple, and the defect of uniformity is measured by the invariant measures.

**Key step.**
- **Cut the orbit** into long Kakutani–Rokhlin towers and compress `h` to each tower. The Fredholm index of a half-line compression vanishes on `G`, so kernel and cokernel can be matched at each end separately. That gives a block-diagonal `H_1` with banded inverse.
- **Then `H_1^{-1}h`** is the identity away from the cuts, so it is block-diagonal for the midpoint towers.
- **Finite algebras.** Both factors live in finite products of `M_h(F_2)`, where block Gauss reduction, Whitehead diagonals and Thompson's commutator theorem give at most 39 elementary matrices.

**Status: established** by `subshift-el-groups-boundedly-elementary-generated-proof`. UNREVIEWED; queued with sk-verify-13.
