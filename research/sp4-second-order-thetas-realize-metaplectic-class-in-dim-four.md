---
rg: 2
id: sp4-second-order-thetas-realize-metaplectic-class-in-dim-four
kind: claim
title: The second-order theta constants of genus two realize the metaplectic class of Sp4(Z) in dimension four
artifacts:
  - research/artifacts/maslov-mod3-sector-numerics-2026-09-05.md
  - experiments/maslov_sector/theta2b.py
  - experiments/maslov_sector/theta2b.log
  - experiments/maslov_sector/seed_theta_d4.json
distinct_from:
  sp4-even-theta-constants-realize-the-metaplectic-class: that realizes the metaplectic class in dimension ten by monomial matrices on the ten even theta constants, factoring through level eight; this realizes the same class in dimension four by non-monomial matrices on the four second-order theta constants, factoring through level four, so metaplectic models now exist in every dimension 4a + 10b.
  sp4-spin-cover-projective-representation-in-dimension-four: that four-dimensional projective representation carries a non-metaplectic torsion class; this four-dimensional one carries the metaplectic class itself.
---

Let `Theta[a](tau) = theta[a,0](2 tau)` for `a` in `(Z/2)^2` be the four
second-order theta constants on the Siegel upper half space `H_2`.  For each
root generator `s` of `Sp_4(Z)` there is a unique matrix `M(s)`, up to a
scalar, with `Theta(s tau)` proportional to `M(s) Theta(tau)` at every
`tau`; found numerically as the null vector of the `2 x 2`-minor equations at
eight random Siegel points, it is unitary after normalization (residual
`1e-14`).  The eight unitaries multiply along every one of the `304,412`
recorded relators `r` of length at most `13` to a scalar (nonscalar part
`3e-14`), and there are generator phases `theta_s` in `(2 pi / 8) Z` such that
the rescaled generators `e^{-i theta_s} M(s)` satisfy

```text
rho(r) = (-1)^{k_r} I         (maximal defect 8e-8 over all relators),
```

with `k_r` the universal-cover lift exponent of
`sp4-root-relators-below-length-twelve-lift-to-universal-cover`.  No
rescaling brings the scalars to the trivial pattern (residual `2`).  So the
multiplier system of the second-order theta constants is the metaplectic
class, in dimension four.  Modulo scalars the long-root generators have
order `4` and the short-root generators order `2`, so this projective
representation factors through `Sp_4(Z/4)`, one level below the even theta
constants.

Direct sums of copies of this model and of the ten-dimensional one give
exact metaplectic models in every dimension `4a + 10b`, which is what the
seeded control runs of `maslov-mod3-projective-defect-gap` need across
dimensions.

**ESTABLISHED (computational; classical in substance).**  The
transformation theory of second-order theta constants under the full
modular group is classical (they are weight one-half forms with the theta
multiplier system), but no formula is used: the matrices are read off
numerically and checked on every relator, and a wrong assignment would
fail scalarity at once.
