---
rg: 2
id: z8-rips-contractible-at-even-scales-38-to-70
kind: claim
title: The Rips complex of Z^8 in the l^1 metric is contractible at every even scale 38 ≤ r ≤ 70
distinct_from:
  z7-rips-contractible-at-scales-20-to-54-even-and-36-to-54: that is the n = 7 consequence of the same partition criterion; this is n = 8, where eight-part partitions must be checked too
  rips-complexes-of-integer-lattices-are-contractible: that is Virk's theorem for r ≥ n^2(2n−1) = 960 at n = 8; this covers the even scales 38..70
---

`VR(Z^8, d_1; r)` is contractible for every even `r` with `38 ≤ r ≤ 70`. A finite set spans a simplex iff its
`l^1` diameter is at most `r`.

Context. Zaremsky's conjecture says `VR(Z^n, d_1; r)` is contractible for all `r ≥ n`. For `n = 8` the published
bound is `r ≥ n(n+1) − 1 = 71`. With this claim, `n = 8` holds at every even `r ≥ 38`. The odd scales below 71 stay
open: at every odd `r` from 37 to 57, between 79 and 186 eight-part partitions are unbalanced, and the criterion says nothing there.

Proof: route `z8-rips-contractible-at-even-scales-38-to-70-proof`. It applies
`zn-rips-sphere-balanced-dominator-criterion` after an exhaustive check of the partitions of `r` into at most 8 parts.
