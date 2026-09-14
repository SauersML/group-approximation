---
rg: 2
id: subshift-gl3-normal-subgroups-are-index-preimages-proof
kind: route
title: Proof by the paper's tower-commutator argument for subgroups normalized by G_X, then the index quotient
target: subshift-gl3-normal-subgroups-are-index-preimages
requires:
  - subshift-gl3-index-kernel-is-elementary-group
  - topologically-free-matricial-crossed-el-simple-kazhdan-lef
---

The full derivation is in `research/artifacts/sk-free-10-gl3-index-2026-09-14.md` §3.

Let 1 ≠ g ∈ K, with K normalized by G_X.
1. **Small sets.** Choose small clopen V for g^{±1} (aperiodicity).
2. **A noncommuting root.** If g commuted with every e_ij(e_V), the entrywise computation would force g = cI_3 with c ∈ LC(X,F_2)^× = {1}. That computation uses only the entries of g. Fix h = e_ij(e_V) not commuting with g.
3. **Tower group.**
   - k = [g,h] = g·(hg^{-1}h^{-1}) lies in K, since h ∈ G_X normalizes K, and k ≠ 1.
   - The product formula puts k ∈ H_V ≅ GL_d(F_2), d = 3(2w+1).
   - K ∩ H_V is normalized by H_V, which is simple, so H_V ⊆ K and e_pq(e_V) ∈ K.
4. **Level ideal.** J = {r : e_pq(r) ∈ K ∀ p≠q} is additive. Commutators with root elements of G_X keep it two-sided: e_pq(sr) = [e_pl(s), e_lq(r)]. It contains all translates of e_V, so 1 ∈ J by minimality. So K ⊇ EL_3(R) = G_X.
5. **Classification.** A normal K ≠ 1 contains G_X, and K/G_X ≤ GL_3/G_X ≅ Z (the index kernel theorem), so K = ind^{-1}(mZ). Preimages of subgroups of an abelian quotient are normal.
