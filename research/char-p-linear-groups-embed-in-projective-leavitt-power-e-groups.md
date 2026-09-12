---
rg: 2
id: char-p-linear-groups-embed-in-projective-leavitt-power-e-groups
kind: claim
title: Every finitely generated linear group in characteristic p embeds in a simple projective elementary group of a Leavitt tensor power
distinct_from:
  positive-char-surface-linear-groups-satisfy-boone-higman: that embeds transcendence degree at most two in a finitely presented simple unit group; this embeds every transcendence degree in a simple projective elementary group, whose finite presentation is left open.
  prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre: that is the host theorem over B ⊗ L_p; this is the input class, an embedding into E_M of a tensor power with no K-theory hypothesis.
artifacts:
  - research/artifacts/boone-higman-char-p-all-degrees-2026-09-12.md
---

**ESTABLISHED (the simplicity input is the paper argument of
`prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre` part 4).** Let `p` be
a prime, `L_p = L_(F_p)(1,2)` and `R_d = L_p^(⊗d)`. Let `K` be a field of
characteristic `p`, and `H <= GL_n(K)` finitely generated, with entry field of
transcendence degree at most `d >= 1`.

There is `M_0` such that for every `M >= M_0`, `X |-> diag(X, I)` embeds `H` in
`E_M(R_(d+1))` and meets its centre trivially. So `H` embeds in
`E_M(R_(d+1)) / Z(E_M(R_(d+1)))`, a simple group.

No `K`-theory hypothesis and no hypothesis on `p` is used.

**History (bh-reviewer, 2026-09-12).** The first derivation used
`X |-> diag(X, X^-1, 1, ..., 1)` into `E_m(R_d)`. That map is not a homomorphism on
nonabelian `H` (`whitehead-diagonal-map-is-not-multiplicative`), so the route
`char-p-linear-embedding-projective-leavitt-power-proof` is invalidated. The
repair `char-p-linear-embedding-corner-swindle-proof` uses the homomorphism
`X |-> diag(X, I)` and one more tensor factor. That factor makes every `K_1`
class of the coefficient matrices vanish
(`leavitt-tensor-kills-k1-of-coefficient-matrices`).

What stands from the first derivation:
- Lemma A: `H <= GL_N(R_d)` for some `N`;
- Lemma C: `Z(E_m(R_d)) <= F_p^x I`;
- simplicity of `E_m(R_d) / Z` for `m >= 3`.

## Attempts

- **Whitehead diagonal map (dead).** `X |-> diag(X, X^-1, 1, ..., 1)` is
  multiplicative only on commuting pairs
  (`whitehead-diagonal-map-is-not-multiplicative`). It produces elements of
  `E_m`, not a subgroup isomorphic to `H`.
- **Corner swindle with one more factor (live, the derivation).**
  `X |-> diag(X, I)` is a homomorphism, and `K_1(R_d) -> K_1(R_(d+1))` is zero.
- **Without the extra factor (open).** Embedding `H` in `E_M(R_d)` itself needs
  trivial classes in `K_1(R_d)`. That follows, for example, from the open
  `prime-field-leavitt-tensor-powers-have-trivial-k-theory`.
- **Through the commutative coordinate ring (untested).** Take
  `S = F_p[t_1..t_d][1/h]`. `X |-> diag(X, (X^T)^-1)` is a homomorphism
  `GL_N(S) -> SL_(2N)(S)`. It lands in `E_M(S)` if `[X^T] = [X]` in `K_1(S)`, or
  if `SK_1(S) = 0`; neither is on main. It is no longer needed.
