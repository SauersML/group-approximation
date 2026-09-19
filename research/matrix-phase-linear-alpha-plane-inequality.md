---
rg: 2
id: matrix-phase-linear-alpha-plane-inequality
kind: claim
title: The matrix alpha-plane energy admits a universal linear bound
root: true
distinct_from:
  matrix-phase-noncommutative-alpha-plane-route: that proves a nonconstructive vanishing modulus; this specifies linear dependence, still with a nonnumerical universal constant.
artifacts:
  - research/artifacts/alpha-plane-affine-tensor-linearization-2026-09-04.md
---

In the notation `(NC1)--(NC3)` of
`matrix-phase-noncommutative-alpha-plane-route`, one has

```text
F(R) <= C (I(R)+A(R))
```

with a universal constant `C`, independent of the field degree and matrix
dimension. The route `matrix-phase-linear-from-affine-tensors-proof`
derives this from the existing qualitative theorem. More precisely, any
uniform epsilon_*>0 for which I+A<=epsilon_* implies F<=1/4 gives
C=1/epsilon_*. The proof uses a bound on every slope, affine
symmetrization, identity dilution, conjugate doubling and tensor powers.
It does not compute a numerical epsilon_* or bypass the separate
same-basis occurrence-decoder gap toward nonhyperlinearity.

## Earlier attempts (before the affine tensor argument, 2026-09-04)

- Polarizing the mean corrector gives `(NC16)--(NC23)`, but the resulting
  perturbation bound is noncontractive. That approach still needs the
  Poincare--Lojasiewicz estimate `(NC24)` or another square-function argument;
  the affine tensor route does not require it.
- Literal replacement of the four full-parallelogram vertices by one
  alpha-corrector each does not cancel: the resulting affine matching system
  is inconsistent even after all unsigned factor permutations.
- The `4 x 4` tensor-square ledger does give the uniform consensus estimate
  `(NC14)`.  Compactness turns that estimate into a common abelian limit, but
  quantitative almost-commuting-to-commuting rounding for the whole corrected
  family is precisely what the linear argument cannot assume.
