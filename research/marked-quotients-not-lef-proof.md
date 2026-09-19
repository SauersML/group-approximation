---
rg: 2
id: marked-quotients-not-lef-proof
kind: route
title: Transport the finite compression collapse into a local embedding
target: marked-quotients-not-lef
requires: [commuting-lamp-defect-survives]
artifacts:
  - notes/COMMUTING_LAMP_QUOTIENT_STRUCTURE_AND_MF_FORK_2026-08-14.md
---

## Direct proof

Take a finite window containing `1`, `u`, `c`, `tau^{\pm 1}`, `tau c tau^{-1}`,
the six base generators, and every prefix of the six words `abar(s_i)` and of
the commutator.  A local embedding `phi` into a finite group `H` is
multiplicative on that window, so it transports the six compression relations
verbatim:  `phi(tau) Gamma^ phi(tau)^{-1} <= Gamma^` for
`Gamma^ = <phi(s_i)>`.  Conjugation is an automorphism of the finite group
`H`, so cardinality forces equality — the `Nat.card` instance of
`invariant-size-collapse`.  The centralizer relations put `phi(c)` in
`C_H(Gamma^)`, hence `phi(tau c tau^{-1})` in
`C_H(phi(tau) Gamma^ phi(tau)^{-1}) = C_H(Gamma^)`, which contains
`phi(s_1)`.  Therefore `phi(u) = 1 = phi(1)`, contradicting injectivity on the
window.

The hypothesis `u != 1` holds in `E` and `W` because `u^2 = w != 1`, and in
`E/<w>` and `W/<zeta>` because `commuting-lamp-defect-survives` makes the
image of `u` a product of two distinct lamp basis elements, so in particular
`u` is not in `{1,w}`.  Residual finiteness implies LEF, so it fails as well.
Section 3 of the cited note is the complete argument.
