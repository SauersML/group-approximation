---
rg: 2
id: simplex-three-view-vacuity-proof
kind: route
title: Use the dual distance four of the affine simplex code
target: four-local-parallelograms-are-minimal-simplex-operator-views
requires:
  - bounded-cooccurrence-joint-pvms-do-not-round-globally
---

Any three distinct points of an affine space over `F_2` are affinely
independent.  Indeed, a nonzero affine dependence has coefficients summing
to zero, hence has even support; support two would say that two of the points
are equal.  Therefore arbitrary prescribed bits on at most three distinct
points extend to an affine functional.  A predicate accepting all affine
restrictions must accept the whole local cube and is classically vacuous.

For four distinct points, a minimal affine dependence must use all four
coefficients and is exactly

```text
x_1+x_2+x_3+x_4=0.                                        (STV1)
```

The affine evaluations on these points are precisely the even-parity
strings.  Thus the dual distance is four and `(FPM1)` is the unique first
kind of nontrivial local constraint, up to affine relabeling.  Combining the
three-coordinate vacuity with the bounded-co-occurrence Pauli shield proves
the impossibility assertion and the sharp arity claim.

