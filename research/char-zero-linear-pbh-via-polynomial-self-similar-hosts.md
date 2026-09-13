---
rg: 2
id: char-zero-linear-pbh-via-polynomial-self-similar-hosts
kind: route
title: Put the group in a finitely presented parameter-coordinate affine host, which is self-similar, and apply the self-similar permutational theorem
target: char-zero-linear-groups-satisfy-permutational-boone-higman
requires:
  - char-zero-linear-groups-embed-in-polynomial-s-integer-groups
  - elementary-groups-over-polynomial-s-integers-are-fp
  - affine-extension-of-fp-elementary-group-is-fp
  - polynomial-parameter-affine-groups-are-self-similar
  - fp-self-similar-subgroups-satisfy-permutational-boone-higman
---

Let `K` be a field of characteristic zero and let `H <= GL_n(K)` be finitely
generated. The host is the one of `polynomial-linear-groups-satisfy-boone-higman`.
The only change is the last step, which reads off membership in `B_A` instead of
a simple envelope.

1. **Polynomial coordinates.** By
   `char-zero-linear-groups-embed-in-polynomial-s-integer-groups` there are
   `m >= 1`, `k >= 0`, `M >= 1` and an injective homomorphism `H -> GL_M(R)`,
   where `R = Z[1/m][s_1,...,s_k]`.
2. **Into elementary matrices.** Let `N = max(k+4, 2M)`.
   - The map `g -> diag(g, (g^T)^-1, I_(N-2M))` is an injective homomorphism
     `GL_M(R) -> SL_N(R)`. Indeed `((gh)^T)^-1 = (g^T)^-1 (h^T)^-1`, and the
     determinant of the image is `det(g) det(g)^-1 = 1`.
   - `SL_N(R) = E_N(R)`, because `N >= k+3` and `SK_1(R) = 0`. This is step 1 of
     `polynomial-linear-groups-satisfy-boone-higman-via-zaremsky`, as corrected
     by lane `bh-poly-linear-review`, which checked its Weibel citations.
   - So `H` embeds in `E_N(R)`.
3. **Finite presentation.**
   - `E_N(R)` is finitely presented by
     `elementary-groups-over-polynomial-s-integers-are-fp`, since `N >= k+4`.
   - `G = R^N x| E_N(R)` is finitely presented by
     `affine-extension-of-fp-elementary-group-is-fp`: `R` is generated as a ring by
     `1/m, s_1, ..., s_k`, and `N >= 4`.
4. **Self-similarity.** Fix a prime `p` not dividing `m`. By
   `polynomial-parameter-affine-groups-are-self-similar`, with `Γ = E_N(R)`, `G`
   acts faithfully and self-similarly on the rooted `p^(N+k)`-regular tree. So `G`
   is a finitely presented self-similar group.
5. **Permutational form.** `E_N(R)` is the subgroup of `G` with zero translation
   part, so `H` embeds in `G`. By part (a) of
   `fp-self-similar-subgroups-satisfy-permutational-boone-higman`, every subgroup
   of `G` lies in `B_A`. So `H` is in `B_A`. ∎

**What part (a) supplies.** Its route reads Zaremsky's proof (arXiv:2405.09722,
§3): `G` embeds in `[V_(d')(G), V_(d')(G)]`, which is finitely presented and simple.
That commutator subgroup is highly transitive
(`rover-nekrashevych-groups-are-highly-transitive`), and BFFHZ Theorem C gives
`B_A` for its subgroups.

**Source check** (2026-09-13, `/scratch.global/sauer354/bh-reviewer/2503.21882.txt`,
l.168--177). Theorem C: "For a finitely generated group G (with solvable word
problem) the following are equivalent: (i) G satisfies the permutational
Boone–Higman conjecture, i.e., it embeds in a group admitting an action of type
(A). [...] (iii) G embeds in a finitely presented simple group that is highly
transitive. [...] In particular, every finitely presented simple group that is
highly transitive, or more generally MIF, satisfies the permutational Boone–Higman
conjecture, as does every subgroup thereof."
