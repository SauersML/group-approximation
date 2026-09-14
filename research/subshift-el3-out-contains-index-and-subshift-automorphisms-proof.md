---
rg: 2
id: subshift-el3-out-contains-index-and-subshift-automorphisms-proof
kind: route
title: Proof by the trivial centralizer, the centralizer of u, and the index of uI_3
target: subshift-el3-out-contains-index-and-subshift-automorphisms
requires:
  - subshift-gl3-index-kernel-is-elementary-group
  - crossed-product-gl-n-has-infinite-cyclic-index-quotient
---

The full derivation is in `research/artifacts/sk-free-10-gl3-index-2026-09-14.md` §4.

1. **Center and centralizer.**
   - A central Σ c_n u^n has c_n = 0 for n ≠ 0 (aperiodicity) and c_0 constant (minimality), so Z(R) = F_2.
   - An element commuting with every e_ij(1) is scalar cI_3, and commuting with every e_ij(r) forces c ∈ Z(R)^× = 1.
2. **Embedding.** inn(k)|_{G_X} is inner iff g^{-1}k centralizes G_X for some g ∈ G_X, iff k ∈ G_X. With GL_3/G_X ≅ Z this embeds Z in Out(G_X).
3. **Subshift automorphisms.**
   - α_φ is a ring automorphism fixing u, since φT = Tφ. So α_φ(d) = d, α_φ commutes with inn(d), and (m,φ) ↦ inn(d^m)α_φ is a homomorphism.
   - If it is inner, α_φ = inn(k) with k ∈ GL_3(R) fixing every e_ij(1) and e_ij(u). Then k = cI_3 with c a unit centralizing u.
   - The centralizer of u is F_2[u^{±1}] (T-invariant locally constant coefficients are constant), whose units are u^n.
   - So α_φ = α_{T^n} and φ = T^n. Index additivity gives ind(k) = ind(d^{-m}g) = m and ind(k) = ind(u^nI_3) = −3n, so m = −3n.
   - Conversely d^{-3n}u^nI_3 has index 0, so it lies in G_X by the index kernel theorem, and the automorphism is inner.
