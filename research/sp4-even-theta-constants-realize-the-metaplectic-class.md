---
rg: 2
id: sp4-even-theta-constants-realize-the-metaplectic-class
kind: claim
title: The even theta constants of genus two realize exactly the metaplectic class of Sp4(Z) in dimension ten
artifacts:
  - research/artifacts/maslov-mod3-sector-numerics-2026-09-05.md
  - experiments/maslov_sector/theta_constants.py
  - experiments/maslov_sector/theta_verify.py
  - experiments/maslov_sector/seed_theta_d10.json
distinct_from:
  sp4-metaplectic-class-is-not-inflated-from-level-two: that shows no class pulled back from Sp_4(F_2) is the metaplectic class; this shows the classical theta-constant multiplier system is the metaplectic class, factoring through level eight.
  sp4-spin-cover-projective-representation-in-dimension-four: that realizes a different, non-metaplectic torsion class in dimension four; this realizes the metaplectic class itself in dimension ten.
  sp4-root-relators-below-length-twelve-lift-to-universal-cover: that computes the lift exponents; this identifies a representation whose relator scalars are exactly those exponents mod two.
---

Let `theta[m](tau)`, `m` one of the ten even characteristics of genus two, be
the theta constants on the Siegel upper half space `H_2`, and let
`Sp_4(Z)` act by `tau -> (A tau + B)(C tau + D)^{-1}` and on characteristics
by the affine action of `sp4-spin-cover-projective-representation-in-dimension-four`.
For each root generator `s`, the ratios `theta[s o m](s tau) / theta[m](tau)`
have modulus independent of `m` and, after division by one reference ratio,
are unimodular constants independent of `tau`.  The resulting monomial
unitaries `rho(s) in U(10)` satisfy, for every one of the `304,412` recorded
relators `r` of length at most `13`,

```text
rho(r) = (-1)^{k_r} I,
```

where `k_r` is the exponent of the universal-cover generator in the lift of
`r` (`sp4-root-relators-below-length-twelve-lift-to-universal-cover`), with
no rescaling of the generators.  So the multiplier system of the even theta
constants is exactly the mod-two reduction of the universal-cover class of
`Sp_4(Z)`: the metaplectic double cover `E_2` acts genuinely on the ten even
theta constants with its central element acting as `-1`.  Modulo scalars the
long-root generators have order `8` and the short-root generators order `4`,
so the projective representation factors through `Sp_4(Z/8)`.

**ESTABLISHED (computational; classical in substance).**  That theta
constants transform under `Sp_{2g}(Z)` with a multiplier built from
`det(C tau + D)^{1/2}` and an eighth root of unity is Igusa's transformation
formula; the content here is the exact identification of the class with the
universal-cover class on a fixed generating set, verified relator by relator,
and the explicit matrices.  Together with
`sp4-metaplectic-class-is-not-inflated-from-level-two`, the metaplectic class
is inflated from level eight but not from level two.

## Use

`seed_theta_d10.json` is an exact solution of the metaplectic sector of the
relator-energy problem in dimension ten, the control that the Maslov-sector
numerics lacked: any optimizer meant to probe the mod-three sector can be
calibrated against it.
