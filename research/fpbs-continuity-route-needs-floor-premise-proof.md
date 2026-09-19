---
rg: 2
id: fpbs-continuity-route-needs-floor-premise-proof
kind: route
title: Check both requirements on Z^2, where critical l2 fails, and isolate the floor as the missing premise
target: fpbs-continuity-route-needs-floor-premise
requires: []
artifacts:
  - experiments/fpbs-weighted-surface-bomb-2026-09-17/README.txt
---

**Direct proof.** Throughout, `T_q` is the two-point kernel
`tau_q(u,v) = P_q(u <-> v)` on `l2(V)`, and `phi(q) = 1/||T_q||`, with
`1/infinity = 0`.

**Step 0 (a norm fact).** If `0 <= A <= B` entrywise, then `||A|| <= ||B||`.
For any `f`, `|Af| <= A|f| <= B|f|` pointwise, so
`||Af|| <= ||B|f||| <= ||B|| ||f||`.

**Step 1 (item 1 of the floor claim, every finitely generated group).**
Let `gamma(t) <= gamma(1)` coordinatewise, with `gamma(0)` good.

* The standard monotone coupling gives `tau_{gamma(t)} <= tau_{gamma(1)}`
  entrywise. By Step 0, `phi(gamma(t)) >= phi(gamma(1))`.
* If critical l2 holds at `gamma(1)`, then `inf_t phi(gamma(t)) = phi(gamma(1)) > 0`.
* Conversely, `inf_t phi(gamma(t)) > 0` includes `t = 1`, so
  `phi(gamma(1)) > 0`. This direction holds for every path.
* For the existential form, take the straight path `gamma(t) = t gamma(1)`.
  It is monotone and continuous, and `gamma(0) = 0` is good because `T_0 = I`.

So item 1 is valid on every finitely generated group, `Z^2` included. It
never produces the floor; it only restates it.

**Step 2 (the sprinkling lemma is graph-general).**
`fpbs-one-edge-sprinkling-l2-lipschitz` is stated for an arbitrary locally
finite graph (items 1, 2 and 4) or an arbitrary Cayley graph (item 3). Its
proof uses only these, none of which involves amenability or nonamenability:

* the coupling `omega' = omega OR xi`;
* the split at the last sprinkled edge;
* BK on a finite product space, then exhaustion.

So if it holds, it holds on `Z^2`.

Its item 4 says, in its own words, that the good set is all of `[0,1]` iff
`gamma(0)` is good and `inf phi > 0`. The floor is stated there as a
hypothesis, not proved.

**Step 3 (critical l2 fails on `Z^2`).** On `Z^2` with standard generators,
`p_c = 1/2`.

* For a nonnegative convolution kernel on an amenable group, the `l2 -> l2`
  norm equals the `l1` mass. Test it on normalized indicators of Følner sets.
* So `||T_p|| = chi(p)` for `p < p_c`.
* By sharpness (Menshikov; Aizenman–Barsky), `chi(p) >= c/(p_c - p)`, so
  `chi(p) -> infinity` as `p` increases to `p_c`.
* Hence `||T_{p_c}|| >= sup_{p<p_c} ||T_p|| = infinity`.

So on the straight path from the good anchor `0` to `p_c 1_S`, all of the
following hold, while the conclusion fails:

* the anchor is good;
* openness holds, by Step 2;
* Step 1 holds;
* `phi(gamma(1)) = 0`.

**Step 4 (item 2 adds no positive input).** Item 2 of the floor claim says
that the one-step certificate fails for the anchors `{a,t}` and `{b,t}` on
`F_2 x Z` at every `p >= 1/5`. It is a statement about one group, and it
asserts that bounds fail. It supplies no lower bound on `phi` at any point
of any other group's uniform critical surface.

**Conclusion.** Steps 1–4 show:

* The two requirements of `fpbs-dead-weighted-surface-continuity-l2` contain no
  positive assertion about any nonamenable group, apart from the good-anchor
  hypothesis, which `Z^2` also satisfies at `0`.
* The route's open-closed argument, run on `Z^2`, would conclude critical l2
  at `p_c`, and that is false.
* The step that fails is closedness, which is exactly the floor
  `inf phi > 0`. By Step 1 the floor is equivalent to the conclusion at the
  endpoint.

So the route's asserted implication is not justified by its requirements.
This proof uses neither requirement as a premise: Step 1 is proved here, and
Step 2 is a remark about the lemma's statement. So this invalidator stays
established whatever happens to those requirements and to
`fpbs-weighted-surface-continuity-reduces-to-uniform-floor`.
