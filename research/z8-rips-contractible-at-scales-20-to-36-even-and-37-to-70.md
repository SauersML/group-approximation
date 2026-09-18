---
rg: 2
id: z8-rips-contractible-at-scales-20-to-36-even-and-37-to-70
kind: claim
title: The Rips complex of Z^8 in the l^1 metric is contractible at every even scale 20 ≤ r ≤ 36 and every scale 37 ≤ r ≤ 70
distinct_from:
  z8-rips-contractible-at-even-scales-38-to-70: that covers only the even scales 38..70, where no partition is unbalanced; this adds every odd scale 37..69, which have 11 to 186 unbalanced 8-part partitions, and the even scales 20..36, via the slack-one extension
  z7-rips-contractible-at-scales-12-14-16-and-18-to-54: that is the n = 7 consequence of the same slack-one criterion; this is n = 8
  rips-complexes-of-integer-lattices-are-contractible: that is Virk's theorem for r ≥ n^2(2n−1) = 960 at n = 8; this covers 37..70 and the even scales 20..36
---

`VR(Z^8, d_1; r)` is contractible for every even `r` with `20 ≤ r ≤ 36` and for every `r` with `37 ≤ r ≤ 70`. A
finite set spans a simplex iff its `l^1` diameter is at most `r`.

Context. Zaremsky's conjecture says `VR(Z^n, d_1; r)` is contractible for all `r ≥ n`. For `n = 8`, the published
bound is `r ≥ n(n+1) − 1 = 71`. With this claim, `n = 8` holds at every `r ≥ 37` and at every even `r ≥ 20`. The
scales still open are `8 ≤ r ≤ 19` and the odd scales `21 ≤ r ≤ 35`. At each of them, some unbalanced partition of
`r` has fewer than 8 parts, so the slack-one criterion does not apply.

Proof: route `z8-rips-contractible-at-scales-20-to-36-even-and-37-to-70-proof`. It applies
`zn-rips-slack-sphere-criterion` after an exhaustive computation on the partitions of `r` into at most 8 parts.
