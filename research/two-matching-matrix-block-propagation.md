---
rg: 2
id: two-matching-matrix-block-propagation
kind: claim
title: Robustify the two-matching matrix-block affine-orbit propagation
distinct_from:
  two-matchings-force-full-weyl-on-multiplicity-free-spectra: that uses scalar nonzero overlap entries; this must control matrix blocks and arbitrary ranks.
  two-field-matchings-rigidify-linear-weyl-mislabels: that excludes one deterministic linear quotient; this must exclude all nonnormalizing commuting actions.
---

OPEN.  Robustify the complete Weyl conclusion of
`two-matchings-force-exponential-dimension-with-multiplicity` in normalized
Hilbert--Schmidt norm with a success threshold independent of `n`.

The arbitrary-multiplicity **exact** problem is closed in the strongest form:
the two sampled matchings force every Weyl relation and `2^n` divides the
dimension.  Moreover,
`two-untwisted-field-matchings-force-complete-cross-commutation` gives a
normalized-HS modulus `O(n^(1+log_2 3))` after exact same-basis decoding.
Only removal of this rank dependence remains here.

Fourier expansion already gives the exact matrix-block transport laws

```text
P_x Q_y P_x'
 = P_x Q_(y+c_i+T_i^*(x+x')) P_x',                             (MB2)

Q_y P_x Q_y'
 = Q_y P_(x+d_i+T_i^(-*)(y+y')) Q_y'.                          (MB3)
```

The exact bridge-orbit proof gives an independent spectral check that
arbitrary multiplicity is not an algebraic escape.  Its robust form needs an
energy ledger for approximately equal bridges.  If

```text
||PQR-PQ'R||_2^2 <= epsilon
```

with `Q Q'=0`, then either the bridge `PQR` has small squared HS mass or
`QPQ'` has quantitatively positive mass.  Alternating the two approximate
transport laws should push bridge energy along the affine orbit
`d->A d+k`.  The target is a square-function estimate charging any energy
lost at the `2^n-1` orbit steps to the **average sampled relation defect**,
not a telescoping `2^n epsilon` bound.

## Attempts

- **Exact nonzero support propagation.**  This is now complete in
  `two-matching-matrix-bridge-orbit-proof`; it supplies no uniform lower bound
  on the mass of a bridge after many approximate steps.
- **Naive telescoping around the primitive orbit.**  It costs
  `(2^n-1) epsilon` and is useless for a fixed HS threshold.
- **Threshold every bridge separately.**  A model can distribute its mass
  over many tiny spectral blocks.  The proof needs a summed orthogonal
  square-function/first-hit accounting, not a minimum-block cutoff.
