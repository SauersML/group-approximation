---
rg: 2
id: z7-rips-contractible-at-scale-10
kind: claim
title: The Rips complex of Z^7 in the l^1 metric is contractible at scale 10
distinct_from:
  z7-rips-contractible-at-scale-9: that is scale 9, proved by a 582 MB certificate on the full peeling-link set with hull(0,x) dominators; this is scale 10, where that search does not finish, proved with a lifted reduction (dominators may use e_7) and a 1.4 MB compressed certificate
  z7-rips-contractible-at-scales-12-14-16-and-18-to-54: that is a partition criterion that excludes r = 10 because a 6-part partition of 10 is unbalanced; this handles r = 10 by a point-level certificate
  rips-complexes-of-integer-lattices-are-contractible: that is Virk's theorem for r ≥ n^2(2n−1); this is the single scale r = 10 for n = 7
---

`VR(Z^7, d_1; 10)` is contractible. A finite set spans a simplex iff its `l^1` diameter is at most 10.

Context. Zaremsky's conjecture (`zn-rips-contractible-at-every-scale-r-ge-n`) says that `VR(Z^n, d_1; r)` is
contractible for all `r ≥ n`. Before this claim, `n = 7` was known at `r = 7, 8, 9, 12, 14, 16` and `r ≥ 18`
(`z7-rips-contractible-at-scales-7-and-8`, `z7-rips-contractible-at-scale-9`,
`z7-rips-contractible-at-scales-12-14-16-and-18-to-54`, `z7-rips-contractible-at-scales-20-to-54-even-and-36-to-54`).
With `r = 10`, the scales still open for `n = 7` are `11, 13, 15, 17`.

Proof: route `z7-rips-contractible-at-scale-10-proof`. The route is a computer certificate with two new ingredients.
- **Lift.** A peeling link only sees the coordinates up to the last index `k` with `b_k ≥ 1`. So it is a
  `k`-dimensional link that contains `e_k`, and every dominator may be taken in `hull(0, x, e_k)`, not only in
  `hull(0, x)`.
- **Interleaving and cone collapse.** Balanced and slack-one sphere points go first. The lower norms are then
  deleted against the remaining sphere, and a residual core of 34,040 points is removed by domination and by
  collapsing links to cones.

For each `k = 2, …, 7` the certificate ends at `{e_k}`. An independent exhaustive verifier replays it in about
50 seconds.
