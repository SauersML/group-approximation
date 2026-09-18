---
rg: 2
id: robust-basic-sdp-gaps-from-gaussian-universe
kind: route
title: Robust basic-SDP gaps at perfect completeness from the Gaussian pair-sum universe, whose value vanishes uniformly in the ambient dimension, and its polar-frame discretisation
target: rich-2to1-perfect-completeness-has-robust-basic-sdp-gaps
requires: [gaussian-universe-discretises-to-robust-rich-2to1-sdp-gaps, gaussian-universe-rich-2to1-game-has-vanishing-value]
artifacts:
  - experiments/gaussian-rich-2to1-universe-2026-09-17/check_gaussian_universe.py
---

Given `delta > 0`, the vanishing-value claim gives `n` with
`sup_(d >= 1) val(Gamma_(n,d)) <= delta/2`. The bound is uniform in `d`, and
that uniformity is what makes the quantifiers work.

Now let `eta > 0` be arbitrary and put `eta' = min(eta, delta/2)`. The
discretisation claim, applied with `eta'`, gives some `d >= 2n` and a finite
rich 2-to-1 instance with alphabets `[2n], [n]`. Its basic SDP value is at
least `1 - eta' >= 1 - eta`, and its value is at most
`val(Gamma_(n,d)) + eta' <= delta`. Here `n` depends only on `delta`, and `d`
and the instance depend on `eta`. This is the target's quantifier order.

**How the premises can fail.** Each is established by its own route. The
load-bearing new input is `gaussian-pair-sum-chaos-eigenvalues-halve-every-two-degrees`,
a finite combinatorial bound with an exact numerical check. A falsified
`lambda_D -> 2^-ceil(D/2)` would break the vanishing value, not the reduction.

**Relation to the frame route.** `robust-basic-sdp-gaps-from-rotated-frame-universe`
stays OPEN. This route does not decide whether the Haar-frame universe `U_n` has
vanishing value. It replaces `U_n` by a universe where the pair-resampling walk
is a second quantisation. That universe pays for it by having only an
asymptotically perfect SDP solution: its value tends to 1 as `d` grows, and
the numerics suggest a deficit of order `1/d`. The target's quantifier
order allows exactly that.
