---
rg: 2
id: reduced-mf-kazhdan-subgroup-gate-proof
kind: route
title: Coset decomposition embeds the reduced algebra of a subgroup, and MF restricts
target: reduced-mf-kazhdan-subgroup-gate
requires: []
---

## Direct proof

**Part 1.**  Choose right coset representatives, `G = sqcup_i H x_i`.  Then
`l2(G) = direct sum_i l2(H x_i)`, each summand is `lambda_G(H)`-invariant, and
`h delta_(y x_i) -> delta_(h y x_i)` identifies each summand with the left
regular representation of `H`.  So `lambda_G|_H` is a multiple of `lambda_H`,
and for every `c` in `C[H]`, `||lambda_G(c)|| = ||lambda_H(c)||`.  The norm
closure of `lambda_G(C[H])` is therefore isometrically `C*_r(H)`, a
C-star subalgebra of `C*_r(G)`.  Restricting an injective *-homomorphism
`C*_r(G) -> prod M_(d_n) / sum M_(d_n)` to it gives an MF embedding of
`C*_r(H)`.

**Part 2.**  Theorem A takes both `Gamma` and `G` to be infinite Kazhdan groups,
with `Gamma` infranormal and not normal; the wreath and the double both contain
`G`, hence `Gamma`.  The expander-matching criterion requires the infinite
finitely generated Kazhdan group `Gamma <= G`.  Kazhdan groups are finitely
generated.
