---
rg: 2
id: fpbs-kazhdan-hyperfinite-connection-cap
kind: claim
title: On a Kazhdan group a hyperfinite subrelation joins a density-p set to its neighbours with probability at most p(1-kappa^2/2), so hyperfinite stages never certify condensation and hyperfinite-coin condensation is confined to a band of relative width about p kappa^2/8
distinct_from:
  fpbs-kazhdan-ergodic-percolation-disagreement-floor: that floor bounds neighbour disagreement of the open set at scale p(1-p) using ergodicity only; the cap here bounds same-class connection for any hyperfinite subrelation, uses nonamenability through Zimmer's theorem, and holds at every ball scale R.
  fpbs-kazhdan-local-cost-formula: that claim derives condensation and a cost bound from a window defect below kappa^2 p; this claim proves that the defect is at least kappa^2 p whenever the cluster relation is hyperfinite, and it isolates the band where a hyperfinite-coin union step reaches the defect threshold.
  fpbs-hp-condensation-bernoulli-exit: that dichotomy says where exact thinning leaves W_b; here the stages before the exit are shown to be capped at t <= t_*, the first non-hyperfinite stage is bounded by an explicit n_0(p,kappa)+1, and the missing hyperfinite-coin condensation theorem is reduced to reaching the band (t_*, theta].
artifacts:
  - experiments/fpbs-hyperfinite-cap-2026-09-17/band.py
  - experiments/fpbs-hyperfinite-cap-2026-09-17/band-output.txt
---

**PROPOSED ESTABLISHED (written proof over imported theorems; see `fpbs-kazhdan-hyperfinite-connection-cap-proof`).**
Verification tier: class-killing obstruction (Theorem A, Corollary B) together with a one-direction reduction
(Theorem C, Corollary D). The numbers in the band and the stage bound are checked by the linked script.

**Setting.**
- `Gamma` is an infinite group with a Kazhdan pair `(S, kappa)`, and `S` generates `Gamma`. Put `theta = 1 - kappa^2/2`.
- `Gamma` acts freely, preserving a probability measure, on `(X, mu)`; ergodicity is not assumed. `R` is the orbit
  relation, `V` a Borel set with `mu(V) = p > 0`, and `E ⊆ R` a hyperfinite Borel subrelation.
- The *same-class connection* of `E` along `s` is `tau^E(s) = mu{x in V : s^{-1} x in V, (x, s^{-1} x) in E}`.
- For a site percolation `omega`, `tau(s) = P(e and s lie in one open cluster)`, and `t = min_{s in S} tau(s)/p`.
- `W_b`, the exact recursion `mu_i`, and `q = 1/(1 + sqrt(1-p))` are as in `fpbs-hp-condensation-bernoulli-exit`.
  Put `f_p(t) = 2qt - q^2 p t^2` and `t_* = (1 - sqrt(1 - p theta)) / (1 - sqrt(1 - p))`.

**Theorem A (Kazhdan cap).** `min_{s in S} tau^E(s) <= theta p`. More generally, for every radius `R`,
`max_{s in S} E sum_C | |C cap B_R| - |C cap s B_R| | / |B_R| >= kappa^2 p`, where `C` runs over the classes of `E`
restricted to the points of `V` in the orbit of `x`, viewed as subsets of `Gamma`.

**Corollary B (hyperfinite stages never certify).** Let `omega` be an invariant site or bond percolation on
`Cay(Gamma, S)` whose cluster relation, after adjoining independent labels, is hyperfinite. Then every window defect
`D_{R,W}` of `fpbs-kazhdan-local-cost-formula` satisfies `max_s D_{R,W}(s) >= kappa^2 p`. So the condensation
criterion of that claim never fires at a stage with hyperfinite cluster relation, at any scale or window. Every
certificate for its Theorem 1, and every near-optimal subgraph in its Theorem 3, has a non-hyperfinite cluster
relation. The same bound holds for any hyperfinite subrelation of the cluster relation.

**Theorem C (band trigger).** Let `mu` be in `W_b` with marginal `p`, and let `E` be a hyperfinite Borel subrelation of
its cluster relation. Let `tau^E_path(s)` be the probability that `e` and `s` are joined by an open path whose vertices
are all `E`-related to `e`. Let `mu'` be the union of two independent samples of `mu` thinned by coins of bias `q`
that are constant on `E`-classes. Then:
- `mu'` is in `W_b`, has marginal `p`, and `min_s tau_{mu'}(s) >= p f_p(t^E)` with `t^E = min_s tau^E_path(s)/p`;
- if `t^E > t_*`, then `mu'` has a nonempty equivariant finite set of infinite clusters, and
  `C(b_Gamma) <= 1 + |S| p/2`;
- by Theorem A, `t^E <= theta` always, and `t_* < theta`.

So the one-step union engine condenses from hyperfinite coins exactly when `t^E` lies in the band `(t_*, theta]`.
Its relative width is `(theta - t_*)/theta = p kappa^2/8 + O(p^2)`, which the script confirms.

**Corollary D (exact recursion).** Let `j_0` be the first stage of the exact Hutchcroft--Pete recursion whose cluster
relation is not hyperfinite, and `n_0 = min{n : f_p^n(p) > theta}`, which is finite. Then `j_0 <= n_0 + 1`, every
stage `i <= j_0` lies in `W_b`, and exactly one of the following holds.
- **(I')** Some stage `i <= j_0` has `t_i > theta`. It then has a finite equivariant set of infinite clusters, and
  `C(b_Gamma) <= 1 + |S|p/2`.
- **(II')** Every stage `i <= j_0` has `t_i <= theta`, and every stage `i < j_0` (these are the hyperfinite ones)
  has `t_i <= t_*`.
  Stage `j_0` is in `W_b` and non-hyperfinite, with `t_{j_0} <= theta`.

**What this kills.** Any argument for fixed price one that runs the Hutchcroft--Pete growth inequality
`tau' >= 2q tau - q^2 tau^2` on connections certified inside hyperfinite coin classes. Such certified connections are
capped at `theta p` at every stage (Theorem A). The fixed point of the growth map is `p`. So the iteration cannot be
continued past the cap. Exact step where it dies: the retention inequality `P(e ~ s in the thinned copy) >= q tau(s)`.
With `E`-coins it becomes `<= q^2 tau(s) + q(1-q) tau^E(s)`, and for some `s` this is at most
`qp(1 - (1-q) kappa^2/2)`. In other words, condensation from hyperfinite coins must be obtained in a single union step
from the band, or from connections that cross coin classes.

**What remains open (the reduction).** Theorem C proves one direction: fixed price one for `Gamma` follows if, for
arbitrarily small `p`, some `mu` in `W_b` of marginal `p` carries a hyperfinite subrelation `E` of its cluster relation
with `min_s tau^E_path(s) > t_* p`. This is a near-extremal problem for the Kazhdan cap. The converse, whether
`C(b_Gamma) = 1` produces such pairs, is not proved.

**Calibration.**
- `Z`, or any amenable group, with `E = R`: `tau^E(s) = p` breaks the cap. This is consistent, since those groups
  have no Kazhdan pair.
- A finite group with `E = R`: again `tau^E = p`. The proof uses infiniteness exactly once, through Zimmer's theorem,
  and a finite group is amenable.
- The case `V = X` recovers the known statement that a hyperfinite subrelation cannot almost contain the generators
  of a Kazhdan group: `max_s mu{x : (x, s^{-1} x) not in E} >= kappa^2/2`.
- For Bernoulli(`p`) site percolation below `p_c`, the clusters are finite and hyperfinite, and `t_1 = p <= theta`.
