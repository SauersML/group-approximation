---
rg: 2
id: heisenberg-solenoid-trace-torsion-dichotomy-proof
kind: route
title: Symmetrizer support plus central Fourier inversion proves the torsion dichotomy
target: heisenberg-solenoid-trace-torsion-dichotomy
requires: []
artifacts:
  - research/artifacts/noncommutative-solenoid-unique-trace-memo-2026-08-22.md
---

Vanishing direction, self-contained.  Fix `(x,y) != 0` and let
`F(z) = phi(a(x)b(y)c(z))`.  Conjugation by `a(s), b(t)` translates the
central coordinate by the nonzero ideal `I = (x,y)Z[1/p] = dZ[1/p]`, so `F`
is `I`-periodic.  Writing `F(z) = int zeta(z) h dmu` with `|h| <= 1` (the
density of `B -> tau_M(E(B) pi(a(x)b(y)))` against `mu`, dominated because
the central spectral projections commute with the group image), periodicity
gives `(1 - zeta(w)) h = 0` in `L^1(mu)` for every `w in I` (characters span
densely in `C(S_p)`), so `h` is supported on the annihilator of `I` = the
dual of the finite group `Z[1/p]/dZ[1/p]` — a finite, hence torsion,
subgroup.  `mu(T_p) = 0` kills `h`.

Fiber form.  A trace with central character `zeta` is a tracial state of the
twisted algebra `A_zeta` with multiplier `sigma_zeta((x,y),(x',y')) =
zeta(-x'y)`; `W(u)W(v)W(u)* = rho_zeta(u,v) W(v)` with
`rho_zeta(u,v) = zeta(x_u y_v - x_v y_u)` forces every trace to vanish off
the symmetrizer `S_zeta`, and `S_zeta != 0` iff `ker zeta` contains a
nonzero ideal iff `zeta` is torsion (then `S_zeta = (mZ[1/p])^2`, `m` the
exact order).  This matches Latremoliere-Packer Thm 2.12 exactly, and their
Thm 3.7 gives the rotation-algebra tower `A_(theta_0) -> A_(theta_2) -> ...`
with `U -> U^p`, `V -> V^p` and `p^2 theta_(2n+2) = theta_(2n) (mod 1)`.

Converse.  Over a torsion atom `zeta` (order `m`), the multiplier is trivial
on `S_zeta = (mZ[1/p])^2`; the dual-action average onto `span W(S_zeta)` is
a conditional expectation, and `eta o E_S` is a tracial state for every
character `eta` of `S_zeta` (traciality: `rho_zeta(u, -u + s) = 1`); choose
`eta` nontrivial.  Full computations: THE MEMO, Section A.
