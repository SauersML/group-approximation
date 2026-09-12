---
rg: 2
id: global-field-soluble-linear-products-proof
kind: route
title: Put each coordinate projection in a finitely presented self-similar group up to finite index, then use permanence of the permutational class
target: global-field-soluble-linear-products-satisfy-boone-higman
requires:
  - fp-self-similar-subgroups-satisfy-permutational-boone-higman
  - function-field-soluble-groups-embed-in-fp-self-similar-groups
  - boone-higman-type-a-class-closed-under-finite-extensions
---

Let `π_i` be the coordinate projections and `G_i = π_i(G) <= GL_(n_i)(K_i)`.
Each `G_i` is finitely generated and soluble, and `G` embeds in `G_1 x ... x G_k`.

1. **Characteristic zero factors.** Part (b) of
   `fp-self-similar-subgroups-satisfy-permutational-boone-higman` says that a
   finitely generated subgroup of `GL_n(K)`, with `K` algebraic over `Q`, lies in
   `B_A`. So `G_i` is in `B_A`.
2. **Positive characteristic factors.**
   - By `function-field-soluble-groups-embed-in-fp-self-similar-groups`, a
     finite-index subgroup of `G_i` embeds in a finitely presented self-similar
     group.
   - By part (a) of `fp-self-similar-subgroups-satisfy-permutational-boone-higman`,
     that subgroup is in `B_A`.
   - By part 2 of `boone-higman-type-a-class-closed-under-finite-extensions`
     (finite-index overgroups), `G_i` is in `B_A`.
3. **Product.** By part 1 of the same claim, `G_1 x ... x G_k` is in `B_A`, and
   so is its subgroup `G`.
4. **Conclusion.** By part 3 of that claim, `G` has solvable word problem and
   embeds in a finitely presented simple group.

**Instances.** `B_p` is covered by step 2 with `G_1 = G`, as the example of
`function-field-soluble-groups-embed-in-fp-self-similar-groups` shows.
`BS(1,6) = Z[1/6] x| Z` is a finitely generated subgroup of `GL_2(Q)`, so step 1
covers it. So `B_2 x B_3 x BS(1,6)` is covered by step 3. ∎
