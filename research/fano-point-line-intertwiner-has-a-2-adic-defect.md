---
rg: 2
id: fano-point-line-intertwiner-has-a-2-adic-defect
kind: claim
title: The Fano point-line intertwiner is complex-invertible but has a nontrivial 2-adic defect
distinct_from:
  fano-points-and-lines-have-the-same-complex-permutation-type: that proves equality of complex permutation characters; this computes why the natural integral intertwiner does not give an integral type identification.
  predicate-rank-gate-doubles-restriction-multiplicity: that manufactures a factor-two restriction jump for an arbitrary Boolean predicate using Schur-Clifford packets; this is the native incidence-lattice defect of the seven point and seven line orbits.
  multiplicity-return-transducer: that asks for a robust recurrent return of an already available integer multiplicity defect; this supplies a small Fano-specific defect but not its normalized-HS return.
---

Index the points and lines of the Fano plane and let `N` be their `7 by 7`
zero-one incidence matrix.  Two equal lines contain three common points and
two distinct lines contain one common point, so

```text
N N^T=2I+J.                                             (FID1)
```

The eigenvalues of the right side are `9` on the constant vector and `2` on
its six-dimensional complement.  Therefore

```text
|det N|=sqrt(9*2^6)=24.                                (FID2)
```

In particular `N` implements the complex point-line equivalence after polar
normalization, but it is not a unimodular change of integral multiplicity
coordinates.

Modulo two, the line indexed by a nonzero covector `a` has indicator

```text
1_(a dot v=0)=1+a dot v.                               (FID3)
```

As `a` varies, these rows span the constant function and the three coordinate
functions on the seven nonzero vectors.  They are independent, so

```text
rank_(F_2)(N)=4.                                       (FID4)
```

Thus the natural point-line return loses three binary lattice directions even
though it is an isomorphism over `C`.  The honest singleton orbit and the bad
Fano-line orbit can therefore be distinguished by integral or 2-primary
multiplicity data, but not by their complex `GL(3,2)` character.

This is not yet a hyperlinearity obstruction.  A finite-dimensional sequence
can absorb any fixed divisibility demand by increasing its multiplicities,
and ordinary normalized Hilbert--Schmidt norm forgets a bounded lattice
index.  To consume `(FID2)--(FID4)`, a compiler must return the defect
recurrently at one fixed packet scale, or otherwise turn it into an extensive
same-matrix rank mismatch.  That is precisely the robustness obligation of
`multiplicity-return-transducer`; the incidence calculation supplies no such
return by itself.

The two standard ways of trying to amplify this defect are ruled out jointly
by `fano-incidence-recurrence-needs-a-nonstationary-two-cell`: finite packet
restriction graphs have a positive regular stationary completion, while any
fixed finite-depth Smith/divisibility test has a bulk-padding sequence with
vanishing normalized-HS defect.  A successful use must therefore be a
source-coupled nonstationary two-cell or proper-corner return.
