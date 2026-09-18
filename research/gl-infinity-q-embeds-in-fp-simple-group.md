---
rg: 2
id: gl-infinity-q-embeds-in-fp-simple-group
kind: claim
title: The finitary group GL_infinity(Q) embeds in a finitely presented simple group
distinct_from:
  gl-n-q-embeds-in-fp-simple-group: that asks for a host for each GL_n(Q) separately, and the hosts may grow with n; this asks for one host for the union GL_infinity(Q) of all GL_n(Q).
  gl-n-q-targets-are-cofinal-in-n: that shows one GL_N(Q) contains every smaller GL_n(Q), SL_n(Q) and PGL_n(Q); this is the union over all N, which no single GL_N(Q) contains.
artifacts:
  - research/artifacts/gq-gq-transfer-consequences.md
---

**OPEN.** The group `GL_∞(Q) = ⋃_N GL_N(Q)` embeds in a finitely presented
simple group. The inclusions are `GL_N(Q) -> GL_(N+1)(Q)`, `g ↦ diag(g,1)`.

- It implies `gl-n-q-embeds-in-fp-simple-group` (route `gl-n-q-via-gl-infinity-q`).
  The converse is not evident, because the hosts in the root may depend on `n`.
- It does not reach `GL_n(Qbar)` by restriction
  (`prufer-groups-do-not-embed-in-gl-infinity-q`).
- For any field `K`, `GL_∞(K)` embeds in the unit group of the Leavitt algebra
  `L_K(1,2)`, through finitary matrix units `e_ij = x_2^i x_1 y_1 y_2^j`; see
  `research/artifacts/gq-gq-transfer-consequences.md` §5. So a finitely
  presented simple subgroup of `L_Q(1,2)^x` containing that copy would prove this
  claim.

## Attempts

None beyond the recorded remarks.
