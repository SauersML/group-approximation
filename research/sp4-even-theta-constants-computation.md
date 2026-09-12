---
rg: 2
id: sp4-even-theta-constants-computation
kind: route
title: Read the theta transformation phases off numerically and verify the relator scalars against the lift exponents
target: sp4-even-theta-constants-realize-the-metaplectic-class
requires: []
artifacts:
  - experiments/maslov_sector/theta_constants.py
  - experiments/maslov_sector/theta_verify.py
  - experiments/maslov_sector/theta_verify.log
---

Theta constants are evaluated by the lattice sum over `|n_i| <= 7` at three
random points of `H_2` with imaginary part near the identity, where the
series converges to machine precision.  For each generator the `10 x 10`
table of ratios `theta[n](s tau)/theta[m](tau)` is scanned for the unique
monomial pattern whose entries, divided by one reference entry, are
unimodular and agree at all three points to `1e-5`; this determines both
the permutation `s o m` and the phases without any formula.  The eight
unitaries are then multiplied along every recorded relator (batched by
length); every product is scalar to `1e-6` and its phase is `(-1)^{k_r}`
exactly.  Orders modulo scalars are found by powering.  No transformation
formula from the literature is used, so a wrong convention could not have
passed: a non-projective assignment fails scalarity on relators immediately.
