---
rg: 2
id: bs12-trivially-padded-opnorm-correction-via-faithful-padding
kind: route
title: Pad by the clock representation to make the trace faithful, correct with Q3_full, then remove the regular padding
target: bs12-trivially-padded-opnorm-correction
requires: [bs12-faithful-trace-opnorm-correction, bs12-regular-padding-is-removable]
---

This proves the stronger statement with `k = 0` (ESS Q3).  That statement
implies the target.

Suppose the target fails.  Then there are `eps > 0` and pairs `(A_n, B_n)`
in `U(n)` with defect `delta_n -> 0` and distance at least `eps` from every
exact pair in `U(n)`.  The dimensions `n` must tend to infinity, since
`U(n)` for bounded `n` is compact.

Let `sigma_n = (W_m, D_m)` be the clock representation, with `m` in
`{n, n+1}` odd.
- `W_m` is the permutation `e_j -> e_(j/2 mod m)`.
- `D_m = diag(zeta_m^j)`.
- These satisfy `W D W* = D^2` exactly.

Consider `(A_n + W_m, B_n + D_m)` in `U(n+m)`.  Its defect is `delta_n`.
Pass to a free ultrafilter `omega`.

**The padded trace is faithful.**  Its limit trace is
`tau' = (tau + tau_reg)/2`, where `tau` is the limit trace of `(A_n, B_n)`.
The trace of `sigma` tends to `tau_reg`, for the following reasons.
- `tr(D_m^r) = 0` for `m` not dividing `r`.
- For `k != 0`, the number of fixed points of `j -> 2^k j` on `Z/m` is at
  most `2^|k| - 1`, so the normalized trace of any word `D^r W^k` tends to
  `0`.
- Alternatively, use item 4 of `bs12-matrix-lift-pairs-have-zero-kl-class`.

`tau_reg` is faithful on `C*(G)`, and `tau` is positive.  Hence `tau'` is
faithful.

**Q3_full applies.**  By `bs12-faithful-trace-opnorm-correction`, the padded
pair is within `o(1)` of exact pairs in `U(n+m)` along `omega`.

**RPR applies.**  By `bs12-regular-padding-is-removable`, `(A_n, B_n)` is
within `o(1)` of exact pairs in `U(n)` along `omega`.  This contradicts the
choice of `eps`.  QED.

**Converse (necessity).**  Q3 implies both prerequisites.
- Q3_full is a special case of Q3.
- For RPR, the `C^n` block of an exact pair near the padded pair is a
  `delta`-near-representation, so Q3 applies to `(A_n, B_n)` directly.

So Q3 is equivalent to Q3_full together with RPR.  Each half can fail
independently of what is currently known.
- The census tests Q3_full.
- RPR is a relative subrepresentation question that is invisible to traces.
