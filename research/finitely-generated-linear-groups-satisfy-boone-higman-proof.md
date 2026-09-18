---
rg: 2
id: finitely-generated-linear-groups-satisfy-boone-higman-proof
kind: route
title: Split by characteristic and use the reviewed polynomial-host theorems in each
target: finitely-generated-linear-groups-satisfy-boone-higman
requires:
  - char-zero-linear-groups-satisfy-boone-higman
  - char-p-linear-groups-satisfy-permutational-boone-higman
  - fp-self-similar-groups-embed-in-fp-simple-groups
---

Let `H <= GL_n(K)` be finitely generated. A field has characteristic `0` or a
prime `p`.

1. **Characteristic zero.** `char-zero-linear-groups-satisfy-boone-higman` embeds
   `H` in a finitely presented simple group.
2. **Characteristic `p`.** `char-p-linear-groups-satisfy-permutational-boone-higman`
   embeds `H` in the finitely presented self-similar group `G = R^N x| E_N(R)`, with
   `R = F_p[s_1, ..., s_k]` and `N = max(k+4, 2M)`. In that route:
   - step 3 uses `elementary-groups-over-polynomial-f-p-rings-are-fp` at
     `N >= 5`;
   - step 4 is the reviewed self-similarity node.

   By Zaremsky's Theorem 1.1 (`fp-self-similar-groups-embed-in-fp-simple-groups`),
   `G`, and so `H`, embeds in a finitely presented simple group.

**Hypothesis check (lane `bh-linear-fields`, 2026-09-18).** I re-read the three
steps of the characteristic-`p` chain against their node texts.
- **Restriction of scalars.** It goes to `F_p(t)` itself, not to a finitely
  generated domain. So the ring `A = F_p[t][1/f]` is regular, hence Cohen--Macaulay.
  That makes the miracle-flatness step legitimate, and Quillen then frees `A` over
  `F_p[s]`.
- **The affine action.** The action on `F_p[[u]]^n x F_p[[u]]^(k-1)` fixes the
  parameter coordinates. The state at a vertex `(e, α)` is `(σ_α(g), w)`, and
  `σ_α(E_N(R)) ⊆ E_N(R)`. The tree is `p^(N+k-1)`-regular with a finite alphabet, as
  Zaremsky's Definition 2.1 requires.
- **Finite presentation.** `N >= 5`, so `St_N(R)` is finitely presented by the
  refereed rank-five node. `K_2(N,R) = 0` by stability plus homotopy invariance, so
  `E_N(R)` is too. The affine extension is the reviewed
  `affine-extension-of-fp-elementary-group-is-fp`.

I found no gap. ∎
