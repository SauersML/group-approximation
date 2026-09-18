---
rg: 2
id: z7-rips-contractible-at-scales-7-and-8
kind: claim
title: The Rips complex of Z^7 in the l^1 metric is contractible at scales 7 and 8
distinct_from:
  z6-rips-contractible-at-scales-6-to-9: that is dimension 6, where with Gupta–Sarkar–Shukla all scales r ≥ 6 are covered; this is dimension 7, where only the two smallest scales are covered and r = 9..54 stay open
  rips-complexes-of-integer-lattices-are-contractible: that is Virk's theorem for r ≥ n^2(2n−1); this claim covers r = 7, 8 for n = 7, below every published bound
---

For `r ∈ {7, 8}`, the Vietoris–Rips complex `VR(Z^7, d_1; r)` is contractible. A finite set spans a simplex
iff its `l^1` diameter is at most `r`.

So Zaremsky's conjecture (contractibility for all `r ≥ n`) holds at the sharp scale `r = n` for `n = 7`. It was
previously open for every `n ≥ 7`, where the best published bound is `r ≥ n(n+1) − 1`.

The proof is a computer certificate, checked by an independent verifier: route
`z7-rips-contractible-at-scales-7-and-8-proof`.
