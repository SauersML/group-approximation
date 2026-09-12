---
rg: 2
id: commuting-lamp-quotient-sofic-proof
kind: route
title: Abelianize the lamp kernel and replay the witness soficity tower
target: commuting-lamp-quotient-sofic
requires: []
artifacts:
  - GroupApproximation/Sofic/CommutingLampQuotientSofic.lean
---

## Why sufficient

Three layers, none of them new mathematics — the point is that the sign is
the only thing standing between the witness tower and its quotient.

1. **The kernel abelianizes.**  The presented Clifford group modulo its sign
   is the elementary abelian mod-two lamp group `X ->_0 Z/2`.  No normal-form
   theory is needed: the mod-two model is presented by the same generators
   through the universal property, and a section built from
   `Finsupp.liftAddHom` pins the kernel to the sign's powers
   (`ker_toModTwo`).
2. **The quotient is identified.**  Hence
   `W/<zeta> = (X ->_0 Z/2) semidirect V` under the same vertical action
   (`signFreeQuotientEquiv`).
3. **The tower replays.**  Finite site orbits of a telescope level give
   finite invariant mod-two lamp windows, so the local finite-kernel
   criterion applies to `(X ->_0 Z/2) semidirect T`
   (`isSofic_modTwo_telescope`), and the integer shift is adjoined by the
   sofic-by-cyclic extension theorem (`isSofic_int_semidirectProduct`).

The base `Gbar` is sofic because its six generators lie in `GL_4(Z)` and the
resulting integral subgroup is residually finite through its congruence
quotients, which is `gammaBar_isSofic` in the repository.

## What it costs

Nothing external.  Endpoint:
`CommutingLampQuotientSofic.isSofic_signFreeQuotient`, specialized to the
literal instance as `literalSignFreeQuotient_isSofic`.
