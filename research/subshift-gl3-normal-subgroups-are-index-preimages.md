---
rg: 2
id: subshift-gl3-normal-subgroups-are-index-preimages
kind: claim
title: The normal subgroups of GL_3 over the binary subshift ring are the trivial group and the index preimages of the subgroups mZ
distinct_from:
  amenable-crossed-product-gl-normal-structure-is-standard: that asserts the sandwich (central or containing E_n) for amenable crossed products through Stepanov's theorem; this gives the complete list over F_2 for Z through the paper's reviewed simplicity proof and the index kernel theorem
  subshift-gl3-index-kernel-is-elementary-group: that identifies the index kernel; this classifies all normal subgroups, including those not contained in G_X
artifacts:
  - research/artifacts/sk-free-10-gl3-index-2026-09-14.md
---

**ESTABLISHED (unreviewed)** by `subshift-gl3-normal-subgroups-are-index-preimages-proof`.

**Statement.** Let (X,T) be an infinite minimal Cantor system, R = LC(X,F_2) ⋊_T Z, and G_X = EL_3(R). Every subgroup K ≤ GL_3(R) normalized by G_X is trivial or contains G_X. So the normal subgroups of GL_3(R) are exactly 1 and ind^{-1}(mZ) = G_X⟨diag(u,1,1)^m⟩, m ≥ 0.

**Model test.** ind^{-1}(2Z) contains diag(u,u,1) and not diag(u,1,1). The center of GL_3(R) is trivial (Z(R) = F_2), so no central alternative occurs.
