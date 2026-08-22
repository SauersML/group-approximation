---
rg: 2
id: constant-cochain-collective-codes-lose-distance
kind: claim
title: Constant-coefficient collective cocycle codes lose ordinary distance
distinct_from:
  collective-cofilling-is-common-erasure-cleaning: that identifies and supplies the cleaning property; this proves why its standard explicit examples do not meet the remaining code hypotheses.
  erasure-cleaning-rounds-all-projective-parity-valleys: that assumes ordinary positive distance in ker(H); this shows the direct positive-degree cochain instantiation violates that assumption.
---

Let `(X_n)` be bounded-degree finite simplicial complexes with
`|X_n(i)| -> infinity`, and let

```text
d_i:C^i(X_n;F_2) -> C^(i+1)(X_n;F_2),
C_n=ker(d_i).
```

For every `i>=1`, if some `(i-1)`-face has an `i`-coface, then `C_n`
contains a nonzero word of weight at most the coface degree.  Consequently
the ordinary relative distance of `C_n` tends to zero.  In degree zero, on
a connected complex with constant coefficients, `ker(d_0)` is only the
one-dimensional repetition code.

Therefore the explicit bounded-degree collective cosystolic expanders of
Kaufman--Tessler provide common-support erasure cleaning, but not a direct
positive-rate, linear-ordinary-distance code for the projective rounding
theorem.  Their linear lower bound is cosystolic distance modulo
`im(d_(i-1))`, not ordinary distance in `ker(d_i)`.  A successful use must
either make those coboundaries into a gauge equivalence or obtain collective
cofilling for a nonconstant degree-zero sheaf code.
