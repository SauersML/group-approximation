---
rg: 2
id: eleven-term-s0-lift-has-no-radius-four-left-inverse
kind: claim
title: The full-support s0 lifts have no partner in the radius-four ball
distinct_from:
  leavitt-rank-three-lift-has-no-one-sided-inverse: that is an unbounded no-go, and it works because the support of the rank-three lift generates a virtually free group; this is a finite fence around a lift whose support generates all of Q, where no such structural argument is available and only exhaustion is.
  mixed-root-two-packet-radius-four-has-no-solution: that exhausts conjugator pairs for the two-packet correction equation in the corner; this exhausts partner supports for the literal convolution equation BA=1 in the whole group algebra.
  leavitt-cross-atlas-eleven-term-s0-lift: that constructs the lift and bounds its support from below; this reports what the search then failed to find, and is the negative half that must not be promoted to a no-go.
artifacts:
  - experiments/kaplansky_affine_lift_search.py
  - experiments/kaplansky_joint_lift_search.py
  - experiments/kaplansky_asymmetric_atlas_search.py
  - research/artifacts/kaplansky-cross-atlas-affine-lift-2026-09-07.md
---

Three exact exhaustions, all in `F_2[Q]` with `Q = L_(F_2)(1,2)^x` and all in
the reduced binary-prefix normal form.

1. For the eleven-term lift `A` of `leavitt-cross-atlas-eleven-term-s0-lift`,
   there is no `B` supported in the radius-four Cayley ball (`5503` group
   elements) with `BA = 1`.

2. For the mixed-chart five-term lift `B` of `t_0` supported on

   ```text
   (6,2), (0,1,2), (0,2,4), (2,4,7), (6,7,6),
   ```

   the joint system `BA = 1` together with `evaluation(A) = s_0` has no
   solution with `A` in the radius-four ball, and none appeared in two
   deterministic radius-three runs sampling 32 and 256 sparse affine lifts of
   `t_0`.

3. For the superseded 25-term lift, there is no `B` supported in the
   radius-three ball (`795` group elements) with `BA = 1`.

Each is a rank computation: the products `g A`, `g` in the ball, span an
`F_2` subspace of the group algebra, and the question is whether `1` lies in
it.  Gaussian elimination over `F_2` answers it exactly.

**These are finite fences, not obstructions.**  Nothing here excludes a
partner of larger support, and the searches were stopped for cost rather than
completed to any structural boundary.  The contrast with
`leavitt-rank-three-lift-has-no-one-sided-inverse` is the whole point: there
the exclusion is unbounded because the support sits inside a directly finite
virtually free subgroup, and here that argument is unavailable precisely
because the support generates all of `Q`.  Losing the no-go is the price of
escaping it, and it is the right trade.

Enumerating partners by ball radius is also the wrong measurement, for the
same reason support size was: the radius-four ball is `5503` elements while
the relevant structure is which collisions `qp = 1` are available at all.
The next search should grow the partner universe by multiplication-collision
class rather than by word length.
