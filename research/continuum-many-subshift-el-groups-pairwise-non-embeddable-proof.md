---
rg: 2
id: continuum-many-subshift-el-groups-pairwise-non-embeddable-proof
kind: route
title: Word problems only go up along embeddings; realize an antichain of degrees by Sturmian slopes
target: continuum-many-subshift-el-groups-pairwise-non-embeddable
requires: [subshift-elementary-group-word-problem-degree, turing-degrees-contain-continuum-antichains, finite-model-subshift-elementary-groups-simple-kazhdan-lef]
artifacts:
  - research/artifacts/sk-free-7-non-embeddability-2026-09-13.md
---

**Step 1 (word problems go up).** Let G = ⟨T⟩ and H = ⟨S⟩ be finitely generated, and ι: H → G injective. Fix a T-word w_s for each ι(s), s ∈ S.
- A word v in S^{±1} is trivial in H iff substituting w_s for s gives a T-word trivial in G. The substitution is computable.
- So WP_S(H) ≤_m WP_T(G).
- The Turing degree of the word problem does not depend on the finite generating set, and isomorphisms transport it.

So H ↪ G implies deg WP(H) ≤ deg WP(G).

**Step 2 (slopes of prescribed degree).** Let P ⊆ 2^ω be the perfect set of pairwise Turing incomparable reals of `turing-degrees-contain-continuum-antichains`. Fix a computable sequence c ∈ 2^ω that is not eventually periodic. For x ∈ P, let α_x ∈ (0,1) have binary expansion x ⊕ c (interleaving).
- α_x ≡_T x.
- α_x is irrational, since its expansion is not eventually periodic.

**Step 3 (the groups).** Let X_x be the Sturmian subshift of slope α_x.
- By `subshift-elementary-group-word-problem-degree`, WP(G_{X_x}) ≡_T L(X_x) ≡_T α_x ≡_T x.
- Sturmian subshifts are infinite, minimal and free, with periodic finite models. So `finite-model-subshift-elementary-groups-simple-kazhdan-lef` makes G_{X_x} infinite, finitely generated, simple, Kazhdan and LEF.

**Step 4 (non-embedding).** Suppose G_{X_x} is isomorphic to a subgroup of G_{X_y} with x ≠ y in P. Step 1 gives x ≡_T WP(G_{X_x}) ≤_T WP(G_{X_y}) ≡_T y, which contradicts incomparability. The map x ↦ G_{X_x} is injective on isomorphism classes (distinct degrees), so the family has cardinality 2^{ℵ_0}. ∎

**Model tests.**
- Computable x and y are Turing equivalent. For such X, Y the argument gives nothing, which is consistent, since factor maps can embed one G into another (`lef-growth-of-subshift-el-groups-is-monotone-under-factors`).
- The trivial comparison x ≤_T y does not obstruct embeddings, and none is claimed.
