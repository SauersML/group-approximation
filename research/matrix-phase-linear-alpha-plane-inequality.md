---
rg: 2
id: matrix-phase-linear-alpha-plane-inequality
kind: claim
title: Upgrade the matrix-phase alpha-plane modulus to a linear energy bound
distinct_from:
  matrix-phase-noncommutative-alpha-plane-route: that proves a nonconstructive uniform modulus by polar consensus and tracial compactness; this asks for an effective linear estimate.
---

OPEN.  In the notation `(NC1)--(NC3)` of
`matrix-phase-noncommutative-alpha-plane-route`, prove or disprove

```text
F(R) <= C (I(R)+A(R))
```

with a universal constant `C`, independent of the field degree and matrix
dimension.  The established compactness theorem rules out a sequence with
`I+A->0` and `F` bounded below, but supplies no rate.

## Attempts

- Polarizing the mean corrector gives `(NC16)--(NC23)`, but the resulting
  perturbation bound is noncontractive.  A linear proof still needs the
  Poincare--Lojasiewicz estimate `(NC24)` or another square-function argument.
- Literal replacement of the four full-parallelogram vertices by one
  alpha-corrector each does not cancel: the resulting affine matching system
  is inconsistent even after all unsigned factor permutations.
- The `4 x 4` tensor-square ledger does give the uniform consensus estimate
  `(NC14)`.  Compactness turns that estimate into a common abelian limit, but
  quantitative almost-commuting-to-commuting rounding for the whole corrected
  family is precisely what the linear argument cannot assume.
