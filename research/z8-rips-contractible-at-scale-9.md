---
rg: 2
id: z8-rips-contractible-at-scale-9
kind: claim
title: The Rips complex of Z^8 in the l^1 metric is contractible at scale 9
distinct_from:
  zn-rips-contractible-at-every-scale-r-ge-n: that is Zaremsky's conjecture for all n and r ≥ n; this is the single case n = 8, r = 9
  z8-rips-contractible-at-scale-8: that is the sharp scale r = 8; this is the next scale r = 9, with a certificate about six times longer
  z7-rips-contractible-at-scale-9: that is dimension 7 at the same scale; this is dimension 8
  z8-rips-lifted-domination-certificates-fail-at-scale-9: that shows domination moves alone cannot certify (8, 9); this certificate adds link-collapse moves and does certify it
  z8-rips-contractible-at-scales-20-to-36-even-and-37-to-70: that covers large scales r ≥ 20 at n = 8; this is r = 9
---

The Vietoris–Rips complex `VR(Z^8, d_1; 9)` is contractible. A finite set spans a simplex iff its `l^1`
diameter is at most `9`.

With `z8-rips-contractible-at-scale-8`, Zaremsky's conjecture (contractibility for all `r ≥ n`) now holds at
`n = 8` for `r = 8, 9`. It remains open there for `10 ≤ r ≤ 19` and odd `21 ≤ r ≤ 35`. The published bound for
`n = 8` is `r ≥ n(n+1) − 1 = 71`.

The proof is a computer certificate, one per link dimension `k = 2, …, 8`. Each is replayed by a verifier that
shares no code with the search: route `z8-rips-contractible-at-scale-9-proof`.

At `k = 8` the certificate has 299,207 moves. Of these, 185,887 are domination moves down to the 113,321-point
self-blocking set, and 22,634 are link-collapse moves. The link-collapse moves all delete norm-9 points with
`x_8 = 0`. They are interleaved with domination cascades, and a final domination cascade of about 81,000 moves
reaches `{e_8}`.
