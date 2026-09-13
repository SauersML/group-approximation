---
rg: 2
id: polynomial-linear-groups-satisfy-boone-higman-via-zaremsky
kind: route
title: Embed in a finitely presented parameter-coordinate affine host and apply Zaremsky's theorem
target: polynomial-linear-groups-satisfy-boone-higman
requires:
  - fp-self-similar-groups-embed-in-fp-simple-groups
  - polynomial-parameter-affine-groups-are-self-similar
  - affine-extension-of-fp-elementary-group-is-fp
  - elementary-groups-over-polynomial-s-integers-are-fp
artifacts:
  - research/artifacts/bh-sl3-zt-host-2026-09-12.md
---

Full details are in §4 of the artifact. Let `R = Z[1/m][t_1..t_k]`,
`n = max(k+4, 2N)` and `G = R^n x| E_n(R)`.

1. **Whitehead embedding.** ~~`g -> diag(g, g^-1)` is an injective homomorphism
   `GL_N(R) -> E_(2N)(R)` (Whitehead's lemma; Weibel, *K-book* III, Ex. 1.2.1).
   Block inclusion gives `E_(2N)(R) <= E_n(R) <= G`.~~
   *Corrected (review lane `bh-poly-linear-review`, 2026-09-12).* That map is not a
   homomorphism. The image of `gh` has second block `h^-1 g^-1`, while the product
   of the images has `g^-1 h^-1`. Ex. 1.2.1 only says that `E_2n(R)` contains each
   such matrix.
   - **The map.** `g -> diag(g, (g^T)^-1, I_(n-2N))` is an injective homomorphism
     `GL_N(R) -> SL_n(R)`.
   - **`SL_n(R) = E_n(R)`, since `n >= k+3`.**
     - `R` is noetherian of Krull dimension `d = k+1`, so its stable range is at
       most `d+1` (Weibel III, Remark 5.5.2).
     - Vaserstein's theorem (Weibel III, Remark 1.2.5) gives
       `GL_n(R)/E_n(R) = K_1(R)` for `n >= d+2`.
     - Weibel III, Thm 3.8, applied `k` times, gives `K_1(R) = K_1(Z[1/m])`.
     - That group is `Z[1/m]^×` through the determinant, because `Z[1/m]` is
       Euclidean (Weibel III, Ex. 1.3.5). So `SK_1(R) = 0`.
   - **So** `GL_N(R) <= E_n(R) <= G`, with the same `n = max(k+4, 2N)`.
2. **`E_n(R)` is finitely presented** by
   `elementary-groups-over-polynomial-s-integers-are-fp`, since `n >= k+4`.
3. **`G` is finitely presented** by `affine-extension-of-fp-elementary-group-is-fp`.
   `R` is generated as a ring by `1/m, t_1, ..., t_k`, and `n >= 4`.
4. **`G` is self-similar** on the rooted `p^(n+k)`-regular tree, for any prime `p`
   not dividing `m`, by `polynomial-parameter-affine-groups-are-self-similar`.
5. **Zaremsky's theorem.** By `fp-self-similar-groups-embed-in-fp-simple-groups`,
   `G` embeds in a finitely presented simple group. Subgroups inherit the
   embedding. ∎
