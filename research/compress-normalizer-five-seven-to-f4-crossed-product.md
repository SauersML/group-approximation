---
rg: 2
id: compress-normalizer-five-seven-to-f4-crossed-product
kind: route
title: Compress normalizer cells to F4 coefficients and count quotient monomials
target: normalizer-five-seven-is-three-by-four-f4-crossed-product
requires:
  - constant-c3-normalizer-is-f4-leavitt-semilinear
  - z-fixed-support-five-hecke-normal-form
artifacts:
  - research/artifacts/five-seven-coefficient-and-adjoint-audit-2026-08-21.md
---

The normalizer preserves the nontrivial `C_3` Fourier idempotent, so its
corner is the crossed product of `F_4` by `N/H`.  Three selected base-cell
elements sum to `z` and compress to zero; two selected elements in any other
normalizer cell compress to a nonzero `F_4` coefficient times its quotient
monomial.  Therefore the three-base-term rank-five type becomes one
invertible monomial and dies.  The one-base-term type becomes three
monomials, while the five possible rank-seven incidence types become at
most four.  The quotient and section cocycle remain fixed, so this is not a
field-extension induction.
