---
rg: 2
id: integer-moment-measure-with-negative-log-determinant
kind: claim
title: A probability measure with all moments integers can have negative log determinant
invalidates:
  - determinant-conjecture-via-integer-trace-moments
distinct_from:
  integral-spectral-limits-satisfy-serre-inequalities: that proves the Serre inequalities for limits of integer matrix spectra; this exhibits a measure with integer moments that fails the simplest one, so integer moments are strictly weaker than being such a limit
artifacts:
  - research/artifacts/determinant-conjecture-serre-class-2026-09-11.md
---

**ESTABLISHED (written proof, artifact Section 3).** With `phi=(1+sqrt5)/2`,
`psi=(1-sqrt5)/2`,

```text
mu = ((1 - 1/sqrt5)/2) delta_(phi^2) + ((1 + 1/sqrt5)/2) delta_(psi^2)
```

is a probability measure on `[0,3]` whose `j`-th moment is
`(L_(2j) - F_(2j))/2`, an integer for every `j` (1, 1, 2, 5, ...), while
`integral log lambda d mu = -(2/sqrt5) log phi < 0`.

So the integrality of `tau((A^*A)^j)` cannot by itself prove the determinant
conjecture. What fails is Galois equidistribution: the conjugate units
`phi^2` and `psi^2` carry unequal mass. The same imbalance, realized as
unequal von Neumann multiplicities with no compensating continuous spectrum,
would violate the conjecture.
