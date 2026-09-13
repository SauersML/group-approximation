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

1. **Whitehead embedding.** `g -> diag(g, g^-1)` is an injective homomorphism
   `GL_N(R) -> E_(2N)(R)` (Whitehead's lemma; Weibel, *K-book* III, Ex. 1.2.1).
   Block inclusion gives `E_(2N)(R) <= E_n(R) <= G`.
2. **`E_n(R)` is finitely presented** by
   `elementary-groups-over-polynomial-s-integers-are-fp`, since `n >= k+4`.
3. **`G` is finitely presented** by `affine-extension-of-fp-elementary-group-is-fp`.
   `R` is generated as a ring by `1/m, t_1, ..., t_k`, and `n >= 4`.
4. **`G` is self-similar** on the rooted `p^(n+k)`-regular tree, for any prime `p`
   not dividing `m`, by `polynomial-parameter-affine-groups-are-self-similar`.
5. **Zaremsky's theorem.** By `fp-self-similar-groups-embed-in-fp-simple-groups`,
   `G` embeds in a finitely presented simple group. Subgroups inherit the
   embedding. ∎
