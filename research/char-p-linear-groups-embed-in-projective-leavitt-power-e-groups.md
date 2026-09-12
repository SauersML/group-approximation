---
rg: 2
id: char-p-linear-groups-embed-in-projective-leavitt-power-e-groups
kind: claim
title: Every finitely generated linear group in characteristic p embeds in a simple projective elementary group of a Leavitt tensor power
distinct_from:
  positive-char-surface-linear-groups-satisfy-boone-higman: that embeds transcendence degree at most two in a finitely presented simple unit group; this embeds every transcendence degree in a simple projective elementary group, whose finite presentation is left open.
  prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre: that is the host theorem over B ⊗ L_p; this is the input class, an embedding into E_m of a tensor power, whose derivation is currently invalidated.
artifacts:
  - research/artifacts/boone-higman-char-p-all-degrees-2026-09-12.md
---

**OPEN.** The derivation is invalidated by `whitehead-diagonal-map-is-not-multiplicative`
(bh-reviewer, 2026-09-12).

Let `p` be a prime, `L_p = L_(F_p)(1,2)` and `R_d = L_p^(⊗d)`. Let `K` be a
field of characteristic `p`, and `H <= GL_n(K)` finitely generated, with entry
field of transcendence degree at most `d >= 1`. The claim: for some `m >= 3`,
`H` embeds in `E_m(R_d) / Z(E_m(R_d))`, which is simple for `m >= 3`.

The earlier derivation used `X |-> diag(X, X^-1, 1, ..., 1)` as the embedding.
That map is not a homomorphism on nonabelian `H`, so the claim is not
established.

What still stands, from the invalidated route and its artifact:
- Lemma A: `H <= GL_N(R_d)` for some `N`.
- Lemma B: each single `diag(X, X^-1)` lies in `E_(2N)(R_d)`.
- Lemma C: `Z(E_m(R_d)) <= F_p^x I`.
- Simplicity of `E_m(R_d) / Z` for `m >= 3`: part 4 of
  `prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre`, a paper argument.

Invalidated route: `char-p-linear-embedding-projective-leavitt-power-proof`.

## Attempts

- **Whitehead diagonal map (dead).** `X |-> diag(X, X^-1, 1, ..., 1)` is
  multiplicative only on commuting pairs
  (`whitehead-diagonal-map-is-not-multiplicative`). It produces elements of
  `E_m`, not a subgroup isomorphic to `H`.
- **Through `K_1(R_d)` (open).** `X |-> diag(X, 1, ..., 1)` is a homomorphism
  into `GL_m(R_d)`. Its image lies in `E_m(R_d)` for large `m` once every
  generator has trivial class in `K_1(R_d)`, for example from the open
  `prime-field-leavitt-tensor-powers-have-trivial-k-theory`. So `K_1` does enter
  this route.
- **Through the commutative coordinate ring (untested).** Take
  `S = F_p[t_1..t_d][1/h]` from Lemma A. Over a commutative ring
  transpose-inverse is an automorphism, so `X |-> diag(X, (X^T)^-1)` is a
  homomorphism `GL_N(S) -> SL_(2N)(S)`. If each generator's image has trivial
  class in `K_1(S)`, the image lies in some `E_M(S)`, hence in `E_M(R_d)` through
  the unital embedding of Lemma A. This needs `[X^T] = [X]` in `K_1(S)`, or
  `SK_1(S) = 0`, and neither is on main.
