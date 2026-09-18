---
rg: 2
id: z7-rips-contractible-at-scales-20-to-54-even-and-36-to-54
kind: claim
title: The Rips complex of Z^7 in the l^1 metric is contractible at every even scale 20 ≤ r ≤ 34 and every scale 36 ≤ r ≤ 54
distinct_from:
  z7-rips-contractible-at-scales-7-and-8: that covers r = 7, 8 by a per-scale certificate on Lmax; this covers r = 20, 22, …, 34 and 36..54 by the partition criterion
  z7-rips-contractible-at-scale-9: that covers r = 9 by a 582 MB certificate; this covers r ≥ 20 (even) and r ≥ 36, where Lmax has 10^7 to 10^9 points and no certificate is needed
  rips-complexes-of-integer-lattices-are-contractible: that is Virk's theorem for r ≥ n^2(2n−1) = 637 at n = 7; this covers 36..54 and the even scales 20..34
---

`VR(Z^7, d_1; r)` is contractible for `r ∈ {20, 22, 24, 26, 28, 30, 32, 34}` and for every `r` with
`36 ≤ r ≤ 54`. A finite set spans a simplex iff its `l^1` diameter is at most `r`.

Context. Zaremsky's conjecture says `VR(Z^n, d_1; r)` is contractible for all `r ≥ n`. For `n = 7`, the previously
covered scales were:
- `r = 7, 8, 9`, by per-scale certificates on the peeling-link set;
- `r ≥ n(n+1) − 1 = 55`, Zaremsky's published bound (also `l1-products-of-trees-have-contractible-rips-complexes`
  with every tree a line).

With that bound, this claim gives contractibility at every `r ≥ 36` and every even `r ≥ 20`. The scales still open
for `n = 7` are `10 ≤ r ≤ 19` and the odd scales `21 ≤ r ≤ 35`.

Proof: route `z7-rips-contractible-at-scales-20-to-54-even-and-36-to-54-proof`. It applies
`zn-rips-sphere-balanced-dominator-criterion` after an exhaustive check of the integer partitions of `r` into at
most 7 parts.
