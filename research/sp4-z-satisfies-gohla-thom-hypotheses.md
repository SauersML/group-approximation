---
rg: 2
id: sp4-z-satisfies-gohla-thom-hypotheses
kind: claim
title: Sp4(Z) is stable in finite actions and satisfies the dimension-two cosystolic inequality with Z/3 coefficients for finite transitive actions
distinct_from:
  gohla-thom-stable-base-nonsofic-extension: that is the theorem consuming these hypotheses; this is the open statement that its base hypotheses hold for `Sp_4(Z)` with `A = Z/3`.
  sl3-z-inverse-3-is-flexibly-p-stable: that is flexible permutation stability of an S-arithmetic group in the summit lane; this is Gohla--Thom's much weaker stability-in-finite-actions for the lattice `Sp_4(Z)`, together with a cosystolic expansion hypothesis that has no counterpart there.
---

OPEN.  Two statements about `Gamma = Sp_4(Z)`: (a) `Gamma` is stable in
finite actions in the sense of Gohla--Thom Definition 3.7 -- the limit action
of every sofic approximation of `Gamma` is weakly contained in the family of
finite `Gamma`-actions; (b) `Gamma` satisfies a cosystolic inequality in
dimension two with coefficients in `Z/3` for all finite transitive
`Gamma`-actions (Gohla--Thom hypothesis (ii)).

Together with residual finiteness of finite type and Deligne's
non-residually-finite triple cover, Theorem 3.13 of arXiv:2403.09582 then
gives `deligne-triple-cover-is-not-sofic`.

## Attempts

- **(b) is known only p-adically.**  The cosystolic inequality is available
  for torsion-free lattices in `PSp_(2d)(Q_p)`, `d >= 4`, `p` large, from the
  high-dimensional expansion of quotients of the Bruhat--Tits building
  (Kaufman--Kazhdan--Lubotzky, Evra--Kaufman); for the real lattice
  `Sp_4(Z)` acting on congruence quotients no such expansion theorem is
  recorded, and the relevant finite complexes (congruence quotients of the
  symmetric space or of a suitable cocompact model) have no proved
  cosystolic expansion.
- **(a) is untested.**  Property (T) plus residual finiteness gives
  `(tau)` and hence non-P-stability (Becker--Lubotzky), which says nothing
  about weak containment of limit actions in finite actions.  No
  computation was attempted.
