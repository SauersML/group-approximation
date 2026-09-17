---
rg: 2
id: fpbs-perturbative-reuse-removal-fails-proof
kind: route
title: Keep reuse off noise-split labels and count two single-use steps per request
target: fpbs-perturbative-reuse-removal-fails
requires:
  - fpbs-small-defect-reuse-on-high-occupancy-edges
  - fpbs-conditional-traffic-descent-bound
  - fpbs-traffic-defect-is-total-variation-loss
artifacts:
  - research/artifacts/fpbs-perturbative-reuse-removal-fails-2026-09-17.md
  - experiments/fpbs-perturbative-reuse-removal-2026-09-17/parity_plan_verifier.py
---

Section 3 of the artifact counts D's traffic: a +2 copy serves its own request,
the request two steps back and the reversed step of the request one back
(N = 3); a +3 copy serves its own request and the reversed third step of the
request one back (N = 2). The parity is independent of the base, so a = 1/2
for both labels, b = 1 and 1/2, and the prerequisite overlap formula gives
J = 1. The verifier replays this in exact arithmetic.

For D' with d = d(D, D'), apply the high-occupancy lemma with c = 1/4. The
labels +2 and +3 have occupancy 1/2 in D, and all other labels have occupancy 0.
So the heavy occurrences of D' have measure at most 3d + 4 delta, and the
light traffic is at most (B' - r') + delta. The traffic change of variables of
the descent bound turns light traffic into the integral over covered requests
of u(y), the number of light steps on the path of y. A covered request with
u(y) <= 1 has a heavy first step (measure at most 2 eta), or a light first
step with a label other than +2, +3 (measure at most 2d), or a light +-2/+-3
first step followed by a heavy second step. No single +-2/+-3 step equals +1,
so that last case has measure at most 8 eta. Hence the integral of u is at
least 2(1 - r' - 10 eta - 2d). Since the used multiplicities of D' integrate
to at least 1 - d, r' <= beta + d. Combining gives
1 <= 65 d + 2 beta + 81 delta. The triangle inequality gives the ball version,
and the direct generator plan gives the distance-2 upper comparison.
