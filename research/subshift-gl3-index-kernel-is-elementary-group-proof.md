---
rg: 2
id: subshift-gl3-index-kernel-is-elementary-group-proof
kind: route
title: Proof by running Theorem D's tower compression on any element of index zero
target: subshift-gl3-index-kernel-is-elementary-group
requires:
  - crossed-product-gl-n-has-infinite-cyclic-index-quotient
  - subshift-el-groups-boundedly-elementary-generated
  - infinite-simple-kazhdan-hyperlinear-group
---

The full derivation is in `research/artifacts/sk-free-10-gl3-index-2026-09-14.md`, §1–§2.

1. **Constancy (Lemma 1).**
   - Moving the cut by one compresses to a codimension-3 subspace, which preserves the Fredholm index.
   - Replacing x by Tx shifts the cut.
   - The compression defect is supported in a window of size 2w, so the index depends locally constantly on x.
   - A locally constant T-invariant function on a minimal X is constant.
2. **Half-lines.** For invertible g_x the two half-line compressions differ from g_x by finite-rank corners, so their indices are ±ind(g). If ind(h) = 0, both vanish at every cut: dim ker = dim coker. This is (T2) of Theorem D for h.
3. **Theorem D verbatim.** Its proof (sk-free-6 part 3) uses h ∈ G_X only through (T2), in the end correction (T3). Everything else uses only h ∈ GL_3(R) and the band of h^{±1}:
   - the localized inverse;
   - the two-end inverse;
   - towers with refined atoms;
   - the factors H_1 ∈ GL_3(A_𝒫) and H_2 ∈ GL_3(A_𝒫′);
   - block Gauss reduction (T1) for any invertible 3×3 matrix over ∏M_{h_a}(F_2).
   So h = H_1H_2 is a product of ≤ 78 elementary matrices, and ker(ind) ⊆ EL_3(R). The inclusion EL_3(R) ⊆ ker(ind) is the required index node.
4. **Consequences.**
   - k·d^{ind(k)} ∈ G_X, and ⟨d⟩ ∩ G_X = 1.
   - [GL_3, GL_3] ⊆ ker(ind), and G_X = [G_X,G_X] since G_X is simple and nonabelian.
   - ind factors through K_1 (it is stable under diag(M,1)), so GL_3/EL_3 → K_1 is injective.
