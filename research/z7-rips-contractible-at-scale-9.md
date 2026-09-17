---
rg: 2
id: z7-rips-contractible-at-scale-9
kind: claim
title: The Rips complex of Z^7 in the l^1 metric is contractible at scale 9
distinct_from:
  rips-complexes-of-integer-lattices-are-contractible: that is Virk's theorem for r ≥ n^2(2n−1); this claim covers the single scale r = 9 for n = 7, below every published bound
  z7-rips-contractible-at-scales-7-and-8: that covers r = 7 and r = 8 with certificates checked by two verifiers; this is the next scale, r = 9, which needed a staged search and a 582 MB certificate
---

The Vietoris–Rips complex `VR(Z^7, d_1; 9)` is contractible. A finite set spans a simplex iff its `l^1`
diameter is at most 9.

With `z7-rips-contractible-at-scales-7-and-8`, Zaremsky's conjecture (contractibility for all `r ≥ n`) now
holds for `n = 7` at `r = 7, 8, 9`. The scales `10 ≤ r ≤ 54` remain open; `r ≥ n(n+1) − 1 = 55` is Zaremsky's
published bound.

The proof is a computer certificate on the peeling-link set `Lmax` of the uniform reduction: route
`z7-rips-contractible-at-scale-9-proof`.
