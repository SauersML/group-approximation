---
rg: 2
id: fpbs-weighted-surface-continuity-reduces-to-uniform-floor-proof
kind: route
title: Evaluate the floor at the endpoint, bound tree norms by a Schur test with the spherical function, and solve the fresh-generator inequality
target: fpbs-weighted-surface-continuity-reduces-to-uniform-floor
requires:
  - fpbs-one-edge-sprinkling-l2-lipschitz
  - fpbs-uniform-floor-equivalence-restricted-to-monotone-paths
artifacts:
  - experiments/fpbs-sprinkling-anchor-2026-09-17/tree_anchor_threshold.py
  - experiments/fpbs-sprinkling-anchor-2026-09-17/output.txt
---

*Demoted 2026-09-17 (referee pass): all three referees voted refuted. Step 1
proves only that a positive floor implies critical l2 at the endpoint. The
"every path" converse is false: on `F_4 x Z`, a path through a supercritical
point has `inf phi = 0` but ends at a certified point. Also, the `{a,t}` and
`{b,t}` anchors are never treated. The route now requires the OPEN gap claim
`fpbs-uniform-floor-equivalence-restricted-to-monotone-paths`, so its target
derives OPEN. The text below is kept as an attempt.*

1. **Floor versus endpoint.** `phi o gamma` is continuous by the Lipschitz item of
   `fpbs-one-edge-sprinkling-l2-lipschitz`.
   * If `inf phi(gamma(t)) > 0`, then `phi(gamma(1)) > 0`.
   * If `phi(gamma(1)) > 0` and the good set is all of `[0,1]`, then `phi o gamma`
     is positive and continuous on a compact interval, so its minimum is positive.
   * If the good set is not all of `[0,1]`, the continuity method has not
     succeeded on that path, whatever happens at the endpoint. For the constant
     path at `gamma(1)`, the floor is `phi(gamma(1))` itself.
   So the closedness input is equivalent to the conclusion. The only
   non-circular use is a single sprinkling step whose cost `||R||` is below an
   explicitly known `phi(anchor)`.
2. **Tree norm.** On the `(q+1)`-regular tree, the radial recursion
   `Xi(n-1) + q Xi(n+1) = 2 sqrt(q) Xi(n)` (for `n >= 1`) and
   `(q+1) Xi(1) = 2 sqrt(q)` hold for `Xi(n) = (1 + n c) q^(-n/2)` with
   `c = (q-1)/(q+1)`. So `A Xi = 2 sqrt(q) Xi`.
   * The sphere operators are polynomials in `A`, `S_n = P_n(A)`, with nonnegative
     entries. Hence `S_n Xi = P_n(2 sqrt q) Xi`.
   * Evaluating at the root gives `P_n(2 sqrt q) = |S_n| Xi(n)`.
   * Since `tau_p(o,v) = p^|v|`, monotone convergence gives
     `T_p Xi = Lambda_q(p) Xi` with `Xi > 0`.
   * The Schur test for a symmetric nonnegative kernel with a positive
     supersolution gives `||T_p|| <= Lambda_q(p)`.
   * In closed form, `Lambda_q(p) = 1 + ((q+1)/q)(x/(1-x) + c x/(1-x)^2)`, with
     `x = sqrt(q) p < 1`.
3. **Fresh-generator transfer.** Take `S' = {a_i^(+-1)}` and `S'' = {t^(+-1)}`.
   * The anchor is a disjoint union of copies of `T_{2k}`.
   * `||A_{S''}|| = 2`.
   * Item 3 of `fpbs-one-edge-sprinkling-l2-lipschitz` gives
     `p < p_{2->2}` whenever `2 p Lambda_q(p) < 1`.
   * The left side increases in `p`. The threshold values come from
     `tree_anchor_threshold.py`, which also checks the eigen-recursion and the
     series identity.
   * `p_c(T_{2k} x Z) <= p_c(T_{2k}) = 1/(2k-1)` because the graph contains the
     tree. For `k >= 4` this is below `p*_k`, so `||T_{p_c}||` is finite directly
     from the sprinkling bound. No criterion needs to be imported.
4. **Other anchors for `F_2 x Z`.**
   * On a subgroup `Z` or `Z^2`, the anchor kernel is a nonnegative convolution
     kernel on an amenable group. So its norm is its `l1` mass, and
     `chi_Z(p) = (1+p)/(1-p)`.
   * Kesten gives `||A_a + A_b|| = 2 sqrt 3`. Also `||A_b + A_t|| = 4` on
     `Z^2`-cosets, and `||A_S|| = 2 sqrt3 + 2`.
   * A `d`-regular graph has at most `d(d-1)^(n-1)` self-avoiding paths of length
     `n`, so `p_c >= 1/(d-1) = 1/5`.
   * Each stated inequality holds at `p = 1/5` and persists for larger `p`, since
     the left sides increase and the right sides decrease.
