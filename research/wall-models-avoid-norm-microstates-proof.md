---
rg: 2
id: wall-models-avoid-norm-microstates-proof
kind: route
title: Pad the wall, transport in the norm sector, then compress back
target: wall-models-avoid-norm-microstates
requires: [kazhdan-asymptotic-commutant-transport]
artifacts:
  - notes/TRUE_RELATIVE_WALL_IS_COMMUTANT_GROWTH.md
  - notes/FALSE_RELATIVE_WALL_FORCES_FLEXIBLE_HS_INSTABILITY.md
---

Extend the wall by the identity on the padded coordinates.  Unitarity of
`rho_n(g)` and corner agreement make both off-diagonal leakages vanish in
normalized Hilbert--Schmidt norm, so the padded wall asymptotically
centralizes `rho_n(Gamma)`.  Kazhdan transport applies to `rho_n` because it
is an operator-norm asymptotic representation and the padded wall is a
uniformly bounded asymptotic commutant; it forces the padded wall to
centralize `rho_n(h)` as well.  Compression by the old projection is an exact
identity on the commutator, and `d_n/D_n->1` transfers the conclusion back to
`(pi_n,v_n)`, contradicting the wall.  Complete argument in the cited note,
Corollary 8.
