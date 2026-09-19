---
rg: 2
id: tag-centralized-successor-corner-proof
kind: route
title: Map the endpoint square into the prefix tag and centralize that tag on the successor
target: tag-centralized-successor-corner
requires:
  - two-bit-tag-routing-splits-s3-exit-and-survivor
  - packet-central-active-complement-reduces-shared-words
  - thompson-free-occurrence-amalgam-preserves-contextuality
  - point-stabilizer-local-hard-share-compiles-bridge-orbit
  - context-local-schur-packet-marked-extension
  - finite-group-shared-overlap-polar-alignment
---

All factors in `C_n` commute with `u_(x_n)` by the off-diagonal part of
`(TSC2)`.  Conjugating the four degree-three endpoint atoms by `(TSC2)`
therefore replaces `K_(x_n),b_(x_n)` by the two current tag bits and leaves
`C_nQ` fixed.  This proves both identities in `(TSC5)`.  Since
`C_(n+1)=C_n(1-E_n)`, the two images are complementary subprojections of
`C_nQ`.  The usual first-hit telescope gives pairwise orthogonality and the
trace budget.

Every factor of `C_(n+1)` is a polynomial in tags at sites different from
`x_(n+1)`.  Relations `(TSC1)` make those tags commute with every shared
generator of `H_(x_(n+1))`; centrality of `J` handles `Q`.  Hence
`C_(n+1)Q` reduces the next shared algebra.  Notice that this is an analytic
corner, not the negative spectral projection of a new scalar word.  No
three-versus-one Boolean predicate has been scalarized.

For `(TSC6)`, exactify at depth `n` the fixed finite endpoint table, the two
tag bits at sites `0,...,n`, and the current bridge covariance table.  Product
telescoping for the four degree-three atoms bounds the two transport errors by
the sum of the three covariance errors and the commutators with the earlier
tags.  For a next-occurrence word `w=y_1...y_l`,

```text
||[C_(n+1)Q,w]||_2
 <=(1/2) sum_(j<=n,i<=2,k<=l)||[T_(x_j,i),y_k]||_2.    (1)
```

The two ordered-pair orbits and the point-stabilizer normal forms derive all
relations in `(1)` with polynomial area in `n`; a van Kampen telescope turns
that area into `p(n)sqrt(E)`.  This proves `(TSC6)`.

The same orbit calculation gives finite presentation: retain one occurrence,
one tag pair, one bridge, finite presentations of their local tables and of
`V`, point-stabilizer commutators, one off-diagonal tag/occurrence commutator
per shared generator, and one off-diagonal bridge/tag commutator.  Conjugation
by prefix transporters generates `(TSC1)--(TSC2)`.

Finally, `packet-central-active-complement-reduces-shared-words` gives exact
endpoint centrality in a marked occurrence.  After the common amplification
from `context-local-schur-packet-marked-extension`, fold all free occurrences
to that representation, set all tag pairs equal to `(K,b)`, all bridges and
`V` equal to the identity, and retain the original action on the shared BCS
words.  This is an exact representation of the augmented presentation and
preserves every marked word.
