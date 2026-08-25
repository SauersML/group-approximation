---
rg: 2
id: bleak-quick-a6-seam-exposes-shared-label-arm-anchor
kind: claim
title: Adjacent Bleak--Quick A5 charts expose a genuinely shared label arm
distinct_from:
  thompson-v-r5-a6-seam-pointwise-synchronization: that asks directly for synchronized contextual three-cycles; this asks for the more structured word certificate which makes synchronization a two-line HS estimate.
  common-pivot-r2-r3-data-preserve-a6-label-swap: that proves a common pivot and equivariant contextual arms are insufficient; this requires the transported output, or the split parent and complementary child, to be literally shared across the seam.
  thompson-v-r5-uniform-common-pivot-centralizers: that false claim fills two long endpoint-centralizer loops separately; this asks for one bounded local two-occurrence certificate before those gauges are separated.
---

Fix the Bleak--Quick presentation and a matrix tuple of relator defect
`delta`.  For every pair of adjacent contextual Carmichael A5 charts and
every shared label `i`, construct contextual unitary swap arms `X_i,X_i'`, a
common pivot arm `R`, and a bounded number of literal conjugates of R1--R5
such that

```text
||Y_i-X_iR||_2+||Y_i'-X_i'R||_2 <= C delta,                     (BQA1)
```

and one of the following holds with the *same* endpoint matrices on the two
lines:

```text
||P^*X_iP-Q||_2+||P^*X_i'P-Q||_2 <= C delta,                    (BQA2)
```

or

```text
||C_0-X_iD||_2+||C_0-X_i'D||_2 <= C delta.                      (BQA3)
```

Here `(BQA2)` is a paired conjugate of the R2 transport relation and
`(BQA3)` is a paired conjugate of the R3 split relation, with `C_0` the
common coarse parent and `D` the common complementary child.  The constant
and the number of cells must be independent of the leaf addresses, matrix
dimension, and ambient packet size.

This is the exact remaining label-sensitive word audit.  Once it is proved,
`shared-endpoint-r2-r3-anchor-has-linear-seam-bound` gives the pointwise
comparison with a universal constant.  A certificate which shares only `R`
does not suffice, and iterating R2/R3 along address depth is not allowed: the
former has the finite permutation countermodel above, while the latter pays
the known proper centralizer-area cost.

## Attempts

The first attempt used the pivot swap as `P` in both charts and transported
each private label arm by its own conjugate of R2.  It fails exactly by
`common-pivot-r2-r3-data-preserve-a6-label-swap`: the permutation exchanging
the two common labels fixes the pivot and moves every private input/output
pair equivariantly.  Splitting the pivot or every private arm by R3 leaves the
same symmetry.

The other obvious construction chooses a global swap word for the label arm
and walks each contextual name to it by successive R2 transports and R3
splits.  Its cell count grows with address depth.  Repackaging the discrepancy
as two endpoint-centralizer loops does not remove that loss:
`finite-mark-centralizer-commutator-area-is-proper` proves their filling areas
are unbounded even in the full R1--R5 presentation.  What remains untried is
a single interacting bounded diagram in which the two contextual occurrences
meet at the label-sensitive endpoint before the private centralizer gauges
are separated.
