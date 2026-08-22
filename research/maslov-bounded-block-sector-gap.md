---
rg: 2
id: maslov-bounded-block-sector-gap
kind: claim
title: Every fixed block-size stratum has a dimension-uniform Maslov projective-defect gap
distinct_from:
  maslov-mod3-projective-defect-gap: that asks for one gap on all matrix tuples, including irreducible tuples of unbounded dimension; this proves the gap only when a positive fraction of the tuple is carried by uniformly bounded common invariant blocks.
  maslov-finite-subgroup-atlas-no-go: that shows compatible projective-regular multiplicities exist on every finite subgroup atlas; this uses the absence of a global finite-dimensional Maslov-sector representation and compactness inside each bounded matrix size.
---

Fix a finite lifted presentation of Deligne's triple cover `E_3` and put
`z = omega I`, where `omega` is either nontrivial third root of unity.  For
every integer `K >= 1` there is `c_K > 0` with the following property.

Let a tuple of `d`-dimensional unitaries for the noncentral generators have a
common orthogonal block decomposition.  If `P_{<=K}` is the sum of all blocks
of dimension at most `K`, and `q = rank(P_{<=K})/d`, then

```text
sum_(r in R) ||r(U,z=omega I)-I||_(2,d)^2 >= c_K^2 q.       (BBG1)
```

Here `R` is the fixed finite relator list and the norm is normalized
Hilbert--Schmidt.  The same constants work for the inverse sector after
applying `maslov-inverse-sector-symmetry` (or one can take the minimum of the
two finite lists of constants).

Consequently, in any vanishing-defect sequence in a nontrivial Maslov sector,
the normalized dimension carried by irreducible blocks of size at most `K`
tends to zero for every fixed `K`.  In particular no diagonal, bounded-degree,
or uniformly bounded packet construction can refute
`maslov-mod3-projective-defect-gap`; a countermodel must be genuinely
large-block on asymptotically full matrix mass.

The proof is `maslov-bounded-block-sector-gap-proof`.
