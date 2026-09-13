---
rg: 2
id: sofic-fp-completeness-from-kazhdan-lamps-on-machine-center
kind: route
title: Switchable machine center plus a finitely presented Kazhdan-lamp amplifier gives sofic completeness with no Higman compiler
target: sofic-recognition-finite-presentations-is-pi2-complete
requires:
  - machine-center-vanishes-exactly-on-inf
  - kazhdan-lamp-amplifier-for-machine-center
  - kun-thom-nonsofic-wreath
  - sofic-recognition-has-a-pi2-upper-bound
artifacts:
  - research/artifacts/sofic-fp-machine-center-amplifier-2026-09-12.md
---

## Why sufficient

Assume the amplifier `K_e` of [[kazhdan-lamp-amplifier-for-machine-center]].

- On `INF`, `K_e` is sofic by that claim.
- On `FIN`, `Phi_e` is nonzero, hence contains an element of order 2
  ([[machine-center-vanishes-exactly-on-inf]]).  `K_e`
  contains `Phi_e wr_(G/Gamma) G`, hence `(Z/2) wr_(G/Gamma) G`, which is
  nonsofic by Theorem A of [[kun-thom-nonsofic-wreath]].  Soficity passes to
  subgroups.

So `INF <=_m SOFIC_fp`, and with [[sofic-recognition-has-a-pi2-upper-bound]]
`SOFIC_fp` is `Pi^0_2`-complete.  The center switch is what makes the amplifier
consume a `Pi^0_2` event: `Phi_e = 1` is not certified by any finite derivation.
