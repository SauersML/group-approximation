---
rg: 2
id: z8-rips-contractible-at-scale-8
kind: claim
title: The Rips complex of Z^8 in the l^1 metric is contractible at scale 8
distinct_from:
  zn-rips-contractible-at-every-scale-r-ge-n: that is Zaremsky's conjecture for all n and r ≥ n; this is the single case n = r = 8
  z7-rips-contractible-at-scales-7-and-8: that is dimension 7; this is dimension 8, the next sharp scale r = n
  z8-rips-lifted-domination-certificates-fail-at-scale-8: that shows domination moves alone cannot certify (8, 8); this certificate adds link-collapse moves and does certify it
  z8-rips-contractible-at-scales-20-to-36-even-and-37-to-70: that covers large scales r ≥ 20 at n = 8; this is the sharp scale r = 8
---

The Vietoris–Rips complex `VR(Z^8, d_1; 8)` is contractible. A finite set spans a simplex iff its `l^1`
diameter is at most `8`.

So Zaremsky's conjecture (contractibility for all `r ≥ n`) holds at the sharp scale `r = n` for `n = 8`.
Gupta–Sarkar–Shukla (arXiv:2511.04238) settle `n ≤ 5`. The published bound for `n = 8` is `r ≥ n(n+1) − 1 = 71`.

The proof is a computer certificate, one per link dimension `k = 2, …, 8`, each replayed by a verifier that shares
no code with the search: route `z8-rips-contractible-at-scale-8-proof`.
