---
rg: 2
id: ultramatricial-ideals-have-elementary-congruence-kernels
kind: claim
title: If every finite subset of an ideal lies in a subring isomorphic to a finite product of M_k(F_2), then GL_n(R,I) = E_n(I) for n ≥ 2
distinct_from:
  toeplitz-subshift-kazhdan-group-has-pestov-mf-quotient: that node uses this argument for the Toeplitz ideal J only; this is the general statement for every ultramatricial ideal over F_2
artifacts:
  - research/artifacts/sk-k2-subsystems-2026-09-13-part1.md
---

**ESTABLISHED (unreviewed)** via `ultramatricial-ideals-elementary-congruence-kernels-proof`.

Let R be a ring, I a two-sided ideal and n ≥ 2. Suppose every finite subset of I lies in a subring B ⊆ I that has a unit e_B (possibly e_B ≠ 1) and satisfies B ≅ ∏_i M_{k_i}(F_2). Then:
- GL_n(R,I) = E_n(I). So every invertible matrix congruent to I modulo I is a product of elementary matrices with entries in I.
- GL_n(R,I) is locally finite.

The hypothesis over F_2 is used: over F_q with q > 2 determinants obstruct.
