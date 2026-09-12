---
rg: 2
id: char-p-linear-groups-embed-in-projective-leavitt-power-e-groups
kind: claim
title: Every finitely generated linear group in characteristic p embeds in a simple projective elementary group of a Leavitt tensor power
distinct_from:
  positive-char-surface-linear-groups-satisfy-boone-higman: that embeds transcendence degree at most two in a finitely presented simple unit group; this embeds every transcendence degree in a simple projective elementary group, whose finite presentation is left open.
  prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre: that is the host theorem over B ⊗ L_p; this is the input class, landed in E_m of a tensor power without any K-theory hypothesis.
artifacts:
  - research/artifacts/boone-higman-char-p-all-degrees-2026-09-12.md
---

**ESTABLISHED (the simplicity input is the paper argument of
`prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre` part 4).** Let `p` be a
prime, `L_p = L_(F_p)(1,2)` and `R_d = L_p^(⊗d)`. Let `K` be a field of
characteristic `p`, and `H <= GL_n(K)` finitely generated, with entry field of
transcendence degree at most `d >= 1`.

There is `N` such that for every `m >= 2N+1` the map
`X |-> diag(X, X^-1, 1, ..., 1)` embeds `H` in `E_m(R_d)` and meets its centre
trivially. So `H` embeds in `E_m(R_d) / Z(E_m(R_d))`, a simple group for `m >= 3`.

No `K`-theory and no hypothesis on `p` is used.

DERIVATION
char-p-linear-embedding-projective-leavitt-power-proof
