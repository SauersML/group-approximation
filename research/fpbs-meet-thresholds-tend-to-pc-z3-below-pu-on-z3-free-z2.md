---
rg: 2
id: fpbs-meet-thresholds-tend-to-pc-z3-below-pu-on-z3-free-z2
kind: claim
title: On the free product Z^3 * Z/2 the replica meet thresholds increase to p_c(Z^3) <= 1/2 while p_u = 1, so meet thresholds do not recover p_u, yet the meet gap [cap_fin] holds there
distinct_from:
  fpbs-replica-meet-threshold-sandwich: that computes p_cap^(k) = (d-1)^(-1/k) on regular trees, where sup_k p_cap^(k) = p_u = 1; this is a nonamenable Cayley graph with cycles where sup_k p_cap^(k) = p_c(Z^3) is strictly below p_u = 1.
  fpbs-l2-threshold-not-lsc-at-trees: that bounds p_(2->2) on A * Z/2 by p_c(A) and studies local limits; this computes the meet thresholds on Z^3 * Z/2 exactly by a Galton-Watson criterion and their limit, and verifies [cap_fin] there.
  fpbs-free-product-cayley-graphs-have-critical-l2-gap: that proves p_c < p_(2->2) on free products with union generating sets, which implies [cap_fin] through the chain; this proves [cap_fin] on Z^3 * Z/2 directly and locates every p_cap^(k) in (p_c(G), p_c(Z^3)].
artifacts:
  - research/artifacts/fpbs/docs/replica-meet-amenable-caps-2026-09-19.md
---

**ESTABLISHED.** Route `fpbs-meet-thresholds-tend-to-pc-z3-below-pu-on-z3-free-z2-proof`.

Let `G = Cay(Z^3 * Z/2, {±e_1, ±e_2, ±e_3, t})`, with `k` independent
Bernoulli(`p`) replicas, the meet `M_k(o)` and
`p_cap^(k) = sup{p : |M_k(o)| < infinity a.s.}`. Write `tau_p` and `chi(p)`
for the two-point function and susceptibility of `Z^3`. Then:

1. `G` is nonamenable: `|∂_E K| >= |K| + 2` for every finite nonempty `K`.
2. `p_u(G) = 1`: for every `p < 1`, uniqueness fails with positive
   probability, because every t-edge is a bridge.
3. **Exact criterion.** For `0 < p < p_c(Z^3)`:
   `P_p^(k)(|M_k(o)| = infinity) > 0` iff
   `p^k (sum_{x in Z^3} tau_p(0,x)^k - 1) > 1`.
   The meet is a delayed Galton–Watson tree of finite local meets inside the
   `Z^3`-cosets.
4. **Limit.** `p_cap^(k)(G)` is nondecreasing in `k`, and
   `lim_k p_cap^(k)(G) = p_c(Z^3) <= 1/2 < 1 = p_u(G)`. Also
   `p_c(Z^3;G) = p_c(Z^3)`.
5. **[cap_fin] holds on `G`.** `p_c(G) < p_c(Z^3)`, and for every
   `p in (p_c(G), p_c(Z^3))` some `k` has `|M_k(o)| < infinity` a.s. So every
   `p_cap^(k)` lies in `(p_c(G), p_c(Z^3)]` once `k` is large.

**Consequence.** Question [cap_inf] of
`research/artifacts/fpbs/docs/replica-meet-threshold-2026-09-18.md`, Section 4
(is `sup_k p_cap^(k) = p_u` on every nonamenable Cayley graph?), is answered
**negatively**. Replica meets do not characterise nonuniqueness. The gap they
see is capped by the amenable coset threshold
(`fpbs-meet-threshold-capped-by-amenable-relative-threshold`).
