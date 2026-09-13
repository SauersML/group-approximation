---
rg: 2
id: char-p-linear-pbh-via-polynomial-self-similar-hosts
kind: route
title: Put the group in the finitely presented affine host over F_p[s_1..s_k], which is self-similar, and apply the self-similar permutational theorem
target: char-p-linear-groups-satisfy-permutational-boone-higman
requires:
  - char-p-linear-groups-embed-in-polynomial-f-p-groups
  - elementary-groups-over-polynomial-f-p-rings-are-fp
  - affine-extension-of-fp-elementary-group-is-fp
  - positive-char-polynomial-affine-groups-are-self-similar
  - fp-self-similar-subgroups-satisfy-permutational-boone-higman
---

Direct proof (2026-09-13, lane `bh-metabelian`). Let `K` be a field of characteristic
`p > 0` and `H <= GL_n(K)` finitely generated. The route mirrors
`char-zero-linear-pbh-via-polynomial-self-similar-hosts`.

1. **Polynomial coordinates.** By
   `char-p-linear-groups-embed-in-polynomial-f-p-groups` there are `k >= 0`,
   `M >= 1` and an injective homomorphism `H -> GL_M(R)` with
   `R = F_p[s_1, ..., s_k]`. If `k = 0`, compose with `GL_M(F_p) <= GL_M(F_p[s_1])`.
   So assume `k >= 1`.
2. **Into elementary matrices.** Let `N = max(k+4, 2M)`.
   - The map `g -> diag(g, (g^T)^-1, I_(N-2M))` is an injective homomorphism
     `GL_M(R) -> SL_N(R)`: `((gh)^T)^-1 = (g^T)^-1 (h^T)^-1`, and the determinant of
     the image is `1`. The Whitehead map `diag(g, g^-1)` is not used; it is not a
     homomorphism (`whitehead-diagonal-map-is-not-multiplicative`).
   - **`SL_N(R) = E_N(R)`.**
     - *Stable range.* `R` is noetherian of Krull dimension `k`, so `sr(R) <= k+1`.
       This is the hypothesis form of Weibel, *K-book* III, Remark 5.5.2 (re-read,
       p. 38: "If R is noetherian of dimension d, or more generally has
       sr(R) = d+1"), cited the same way in the reviewed route
       `polynomial-linear-groups-satisfy-boone-higman-via-zaremsky`.
     - *Vaserstein.* Weibel III, Remark 1.2.5 (re-read, p. 3): "if R has stable
       range d+1 then E_n(R) is a normal subgroup of GL_n(R) for all n ≥ d+2.
       Vaserstein proved [V69] that K_1(R) = GL_n(R)/E_n(R) for all n ≥ d+2." Here
       `N >= k+2`.
     - *`K_1`.* By Weibel V, Theorem 6.3 (re-read, p. 40), applied `k` times to the
       regular rings `F_p[s_1..s_j]`, `K_1(F_p) -> K_1(R)` is an isomorphism (with
       Weibel IV, Cor. 1.7.1 identifying Quillen's `K_1` with Chapter III's). By
       Weibel III, Example 1.1.2 (re-read, p. 2), `K_1(F_p) = F_p^×`. Since
       `R^× = F_p^×` and `K_1(R) = R^× ⊕ SK_1(R)` (Weibel III, Example 1.1.1,
       p. 1--2), the determinant `K_1(R) -> R^×` is an isomorphism, so
       `SK_1(R) = 0`.
     - So every `g in SL_N(R)` has trivial class in `GL_N(R)/E_N(R) = K_1(R)`, and
       `g in E_N(R)`.
   - So `H` embeds in `E_N(R)`.
3. **Finite presentation.**
   - `E_N(R)` is finitely presented by
     `elementary-groups-over-polynomial-f-p-rings-are-fp`, since
     `N >= max(4, k+3)`.
   - `G = R^N x| E_N(R)` is finitely presented by
     `affine-extension-of-fp-elementary-group-is-fp`: `R` is generated as a ring by
     `s_1, ..., s_k`, and `N >= 4`.
4. **Self-similarity.** By `positive-char-polynomial-affine-groups-are-self-similar`
   with `Γ = E_N(R)`, `G` acts faithfully and self-similarly on the rooted
   `p^(N+k-1)`-regular tree. So `G` is a finitely presented self-similar group.
5. **Permutational form.** `E_N(R)` is the subgroup of `G` with zero translation
   part, so `H` embeds in `G`. By part (a) of
   `fp-self-similar-subgroups-satisfy-permutational-boone-higman`, every subgroup
   of `G` lies in `B_A`. ∎
