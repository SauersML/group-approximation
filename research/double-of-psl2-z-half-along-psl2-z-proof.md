---
rg: 2
id: double-of-psl2-z-half-along-psl2-z-proof
kind: route
title: Z/2 wreathed over the vertex cosets is in B_A, so the free permutational product is, and it contains the centralizing amalgam, which contains the double
target: double-of-psl2-z-half-along-psl2-z-lies-in-b-a
requires:
  - lamp-wreaths-over-psl2-tree-vertices-lie-in-b-a
  - free-permutational-products-preserve-pbh
  - type-a-action-gives-boone-higman-for-subgroups
artifacts:
  - research/artifacts/gq-bh-openq-papers-list.md
---

Direct proof (2026-09-18, lane bh-openq-papers). Not independently reviewed. Let `X = W/C`
and `x_0 = C`.

**1.** `Z/2 ∈ B_A` (it embeds in `V`), so `Z/2 wr_X W ∈ B_A` by
`lamp-wreaths-over-psl2-tree-vertices-lie-in-b-a`.

**2.** By part 1 of `free-permutational-products-preserve-pbh`, the free permutational product
`K *_X W = (*_{x ∈ X} K_x) ⋊ W` lies in `B_A` for every `K ∈ B_A`.

**3. `W *_C (C × K)` embeds in `K *_X W`.**
- Define `φ` by the identity on `W` and `k ↦ k_{x_0}` on `K`. It respects the relations
  `c k c^(-1) = k` for `c ∈ C`, since `c k_{x_0} c^(-1) = k_{c x_0} = k_{x_0}`.
- *Injective.* A nontrivial element outside `W` has an amalgam normal form
  `w_0 k_1 w_1 ⋯ k_r w_r` with `r ≥ 1`, all `k_i ≠ 1`, and `w_1, …, w_(r-1) ∉ C`.
  - Its image is `(k_1)_{y_1} (k_2)_{y_2} ⋯ (k_r)_{y_r} · (w_0 w_1 ⋯ w_r)`, where
    `y_i = w_0 ⋯ w_(i-1) x_0`.
  - Consecutive `y_i` differ because `w_i ∉ C = Stab(x_0)`. So the lamp part is a reduced
    word of length `r ≥ 1` in the free product `*_x K_x`, hence nontrivial.
  - Elements of `W` map identically.
- So `W *_C (C × K) ∈ B_A`, as `B_A` is closed under subgroups. This is item 1.

**4. The double.** Take `K = Z = ⟨t⟩`, so `W *_C (C × Z)` is the HNN extension of `W` with
stable letter `t` centralizing `C`. The subgroup `⟨W, tWt^(-1)⟩` is the double `W *_C W`, by
Britton's lemma: `t w t^(-1)` with `w ∉ C` is a reduced HNN word. So `W *_C W ∈ B_A`. This is
item 2.

**5.** Finite presentation holds because `W` is finitely presented (`S`-arithmetic;
Borel–Serre, as imported in `rational-iwahori-group-is-union-of-fp-self-similar-groups`) and `C`
is finitely generated. The simple envelopes come from
`type-a-action-gives-boone-higman-for-subgroups`. ∎
