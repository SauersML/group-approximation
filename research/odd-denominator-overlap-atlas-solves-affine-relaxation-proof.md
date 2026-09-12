---
rg: 2
id: odd-denominator-overlap-atlas-solves-affine-relaxation-proof
kind: route
title: Reduce compatible context multiplicities modulo two and glue their odd sums
target: odd-denominator-overlap-atlas-solves-affine-relaxation
requires:
  - tracial-bcs-rationalizes-full-overlap-distributions
---

Reduce `(ODA1)` modulo two.  Since `D` is odd,

```text
|T_c| = sum_(a in S_c) m_(c,a) = 1 mod 2.             (ODP1)
```

The affine hull of a nonempty subset of an `F_2`-vector space is precisely
the set of its odd sums.  Hence the point `x_c` in `(ODA3)` belongs to
`Aff_F2(S_c)`.

It remains only to check gluing.  Fix `v in V_c intersect V_d`.  In `F_2`,

```text
(x_c)_v
 = sum_(a in S_c) (m_(c,a) mod 2) a_v
 = sum_(sigma:sigma_v=1)
     sum_(a in S_c:a|_I=sigma) m_(c,a) mod 2.          (ODP2)
```

Apply `(ODA2)` inside the last expression.  The result is `(x_d)_v`.
Thus the local points agree coordinatewise on every overlap.  Assigning a
shared BCS variable their common coordinate produces a global classical
assignment, and its restriction to each context lies in `Aff_F2(S_c)`.
Every defining affine row of the affine-support LCS is therefore satisfied.

A classical solution is in particular an `R^U` solution (use scalar
involutions, with the solution-group central sign represented as `-1`).
This proves `(ODA4)` by contraposition.  Finally, the compatible-weight
polytope is cut out by rational equalities and inequalities and is nonempty
when the supports come from a tracial BCS state.  It has a rational point, as
recorded more explicitly by
`tracial-bcs-rationalizes-full-overlap-distributions`; clearing denominators
produces `(ODA1)--(ODA2)`.
