---
rg: 2
id: z8-rips-contractible-at-scale-10
kind: claim
title: The Rips complex of Z^8 in the l^1 metric is contractible at scale 10
distinct_from:
  zn-rips-contractible-at-every-scale-r-ge-n: that is Zaremsky's conjecture for all n and r ≥ n; this is the single case n = 8, r = 10
  z8-rips-scale-10-reduces-to-top-shell-link-collapses: that reduces (8, 10) to deleting an explicit 18,816-point set T by (K) moves and leaves the deletion partial; this completes the deletion and so the certificate
  z8-rips-contractible-at-scale-9: that is the scale r = 9; this is the next scale r = 10
  z8-rips-contractible-at-scale-8: that is the sharp scale r = 8; this is r = 10
  z7-rips-contractible-at-scale-10: that is dimension 7 at the same scale, whose k = 2..7 certificates are reused here; this adds the k = 8 certificate
  z8-rips-contractible-at-scales-20-to-36-even-and-37-to-70: that covers large scales r ≥ 20 at n = 8; this is r = 10
---

The Vietoris–Rips complex `VR(Z^8, d_1; 10)` is contractible. A finite set spans a simplex iff its `l^1`
diameter is at most `10`.

With `z8-rips-contractible-at-scale-8` and `z8-rips-contractible-at-scale-9`, Zaremsky's conjecture
(contractibility for all `r ≥ n`) now holds at `n = 8` for `r = 8, 9, 10`. It remains open there for
`11 ≤ r ≤ 19` and odd `21 ≤ r ≤ 35`. The published bound for `n = 8` is `r ≥ n(n+1) − 1 = 71`.

**The certificate.** In the notation of `z8-rips-scale-10-reduces-to-top-shell-link-collapses`, the new piece is a
sequence of 18,816 (K) moves that takes `C = O` to `C = O ∖ T`. It deletes the points of `T` one at a time, and
each (K) move is at a point of `T`. With the two domination pieces of that node, it gives a lifted certificate on
`Lmax_8` at `r = 10` of 628,231 moves ending at `{e_8}`:
- 442,086 (D) moves take `Lmax_8` (628,232 points) to `O` (186,146 points);
- 18,816 (K) moves take `O` to `O ∖ T` (167,330 points);
- 167,329 (D) moves take `O ∖ T` to `{e_8}`.

The certificates for `k = 2, …, 7` at `r = 10` are those of `z7-rips-contractible-at-scale-10-proof`. So the theorem
of that route gives the claim.

**Verification.** All 57 stages of the (K) piece were replayed by the exact verifier `kzv7`, each from its exact
start set, with every line accepted. Seven of them were also replayed by `kzv6`. Every piece ends at exactly the
start set of the next. The 987 (K) lines found by `kzs3` were checked by a verifier that shares its distance code
with that search but not its acceptance test (proof route, §3). The d-prefix and d-tail were replayed by `kzv6`.
The tiers are in §3 of the proof route.

Proof: route `z8-rips-contractible-at-scale-10-proof`.
