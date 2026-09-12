---
rg: 2
id: char-p-linear-embedding-corner-swindle-proof
kind: route
title: Realize H over L_p^(⊗d) ⊗ 1, kill its K_1 classes with one more Leavitt factor, and stabilize into E_M
target: char-p-linear-groups-embed-in-projective-leavitt-power-e-groups
requires:
  - leavitt-tensor-kills-k1-of-coefficient-matrices
  - leavitt-center-is-coefficient-field
  - prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre
artifacts:
  - research/artifacts/boone-higman-char-p-all-degrees-2026-09-12.md
---

This repairs the invalidated route `char-p-linear-embedding-projective-leavitt-power-proof`.
It replaces the Whitehead diagonal map, which is not a homomorphism
(`whitehead-diagonal-map-is-not-multiplicative`), by stabilization
`X |-> diag(X, I)`, which is. The cost is one extra tensor factor.

Let `H <= GL_n(K)` be finitely generated, `char K = p`, with entry field of
transcendence degree at most `d`. Put `R_d = L_p^(⊗d)`.

1. **Lemma A (standing).** `H <= GL_N(R_d)` for some `N`: denominators are
   cleared into `F_p[t_1..t_d][1/h]`, which embeds unitally in `R_d`.
2. **One more factor.** Through `R_d = R_d ⊗ 1 ⊆ R_d ⊗ L_p = R_(d+1)`,
   `H <= GL_N(R_d ⊗ 1)`.
3. **Trivial `K_1` classes.** By `leavitt-tensor-kills-k1-of-coefficient-matrices`
   with `B = R_d` and `k = F_p`, each of the finitely many generators `x_i` of `H`
   has `diag(x_i, I_(j_i)) ∈ E_(N+j_i)(R_(d+1))`.
4. **A homomorphic embedding into `E_M`.** Put `M_0 = N + max_i j_i`, and let
   `M >= max(M_0, N+1, 3)`. `X |-> diag(X, I_(M-N))` is an injective homomorphism
   `GL_N(R_(d+1)) -> GL_M(R_(d+1))`. It sends every generator into `E_M`, since
   `E_(N+j) ⊆ E_M`, so it sends `H` into `E_M(R_(d+1))`.
5. **The centre.** `Z(R_(d+1)) = F_p` by `leavitt-center-is-coefficient-field`,
   and a matrix commuting with every `e_ij(r)` is `cI` with `c` central. So
   `Z(E_M(R_(d+1))) <= F_p^x I`. A scalar with a `1` in the last diagonal slot
   is `I`, so `H` meets the centre trivially and embeds in `E_M(R_(d+1)) / Z`.
6. **Simplicity.** `R_d` is central simple over `F_p`, as a tensor product of
   copies of the central simple algebra `L_p`. Part 4 of
   `prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre` with `B = R_d`
   makes `E_M(R_(d+1)) / Z` simple for `M >= 3`.
