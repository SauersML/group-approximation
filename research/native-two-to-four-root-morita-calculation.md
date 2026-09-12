---
rg: 2
id: native-two-to-four-root-morita-calculation
kind: route
title: Read one two-cycle and one four-cycle in the native parahoric lattice orbit
target: first-root-parahoric-incidence-has-a-two-to-four-morita-lift
requires:
  - native-sl3-edge-parahoric-has-index-forty-two
  - partial-isometry-translate-cancel-charges-first-exit
---

The divisibility description of `D` gives `u notin D`, `u^2 in D`, and
`s_23^(-1)u^2s_23=x_13(2) notin D`.  Since `u^4` is the identity modulo four,
it fixes every lattice in the forty-two-point orbit.  These facts prove the
two- and four-cycle assertions `(RPM4)--(RPM6)` without enumerating the
remaining branches.

The two displayed bases in `(RPM8)` make `(RPM9)` a direct calculation:
both `U|R` and `U^2|Q` exchange their two basis vectors.  Conversely the
trace of a flip on `R` is zero, so its squared distance from `I_R` is
`2 tau(R)`, proving `(RPM10)`.  Hence the relation has a fixed same-carrier
gap and an exact equal-rank rectangular escape, with the source/target sort
being the only distinction.

