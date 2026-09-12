---
rg: 2
id: atlas-mixed-rank-pencil-proof
kind: route
title: Express mixed intersections as kernels and pass rectangular rank to the ultraproduct
target: atlas-mixed-fixed-spaces-are-rank-pencils
requires:
  - atlas-separate-chart-module-ledger-is-kernel-blind
  - atlas-rank-stability-literature-fence
---

The common kernel of the rows `k_i-I` is `Fix_K(E_n)`, and similarly the
common kernel of the rows `l_j-I` is `Fix_L(E_n)`.  Hence a vector `v`
belongs to

```text
Fix_K(E_n) intersect T^-1 Fix_L(E_n)
```

if and only if

```text
A_K v=0  and  A_L T v=0.
```

This is the kernel of the displayed stacked operator in `(MFP1)`, proving
the nullity formula.  Rectangular rank is compatible with the normalized
rank metric: changing `T` to `T'` changes the bottom block by
`A_L(T-T')`, whose rank is at most `rank(T-T')`.  It follows both that the
normalized ranks define `(MFP2)` and that this recovers the established
one-Lipschitz estimate.

For the non-discreteness example, choose bases

```text
e_1,...,e_m  of F,
f_1,...,f_m  of a complement.
```

For a prescribed `j`, map `e_1,...,e_j` into `F` and
`e_(j+1),...,e_m` into the complement, then map a complementary basis
bijectively onto the unused target basis vectors.  The resulting map is
invertible and has exactly a `j`-dimensional preimage intersection with
`F`.  Thus the normalized coordinate has an unbounded set of denominators
and cannot support a finite-profile pigeonhole argument.

Finally, `(MFP2)` says that a hypothetical augmented rank microstate gives
an exact value of every such pencil in the ultraproduct.  No coordinate of
the representing sequence is thereby made an exact zero of the augmented
relations.  Obtaining one is precisely a lift/correction theorem, and the
audited literature fence establishes that the Atlas amalgams and thirteen
fillings lie outside the published permanence results.

