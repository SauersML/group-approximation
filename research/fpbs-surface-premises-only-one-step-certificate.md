---
rg: 2
id: fpbs-surface-premises-only-one-step-certificate
kind: claim
title: The weighted-surface continuity route's prerequisites certify critical l2 at a generating set only through the one-step anchor certificate, so the route is not a derivation of its target
distinct_from:
  fpbs-uniform-floor-equivalence-restricted-to-monotone-paths: that proves the floor-endpoint equivalence on monotone paths and a Z^2 anchor calibration; this shows that every property the route extracts from its prerequisites is satisfied by an explicit weight function vanishing at the endpoint, so the route's inference is invalid.
  fpbs-weighted-surface-continuity-reduces-to-uniform-floor: that records the continuity reduction and the one-step tree certificate as partial results; this proves the one-step certificate is the exact logical content of the route's prerequisites and invalidates the route that treats them as sufficient.
  fpbs-one-edge-sprinkling-l2-lipschitz: that proves a perturbation inequality for the true norm function; this uses only the abstract form of that inequality and builds a function satisfying it that is zero at the endpoint.
  fpbs-fiid-finite-clusters-do-not-imply-dyadic-summability: that separates the dyadic estimate from invariance plus finite clusters by an FIID law; this separates it from the weighted-surface continuity premises by an abstract norm profile.
invalidates:
  - fpbs-dead-weighted-surface-continuity-l2
---

**ESTABLISHED.** Fix a finitely generated `Gamma`, a finite symmetric `U`, and
`G = Cay(Gamma,U)`. Let `W_eps = [0,1-eps]^U` be the per-generator weight
fields. For `p <= p'` in `W_eps` put `r_u = (p'_u - p_u)/(1 - p_u)` and
`R(p,p') = sum_u r_u A_u`, where `A_u` is the adjacency operator of the
`u`-labelled edges. Let `phi(p) = 1/||T_p||` as in
`fpbs-one-edge-sprinkling-l2-lipschitz`. Call a function
`Phi : W_eps -> [0,infinity)` *route-admissible* if it has:

* **(M)** `p <= p'` implies `Phi(p') <= Phi(p)`;
* **(L)** `p <= p'` implies `Phi(p') >= Phi(p) - ||R(p,p')||`;
* **(C)** `Phi` is continuous on `W_eps`.

These are exactly the properties of `phi` that the route
`fpbs-dead-weighted-surface-continuity-l2` draws from its two prerequisites.
(M) is the monotonicity behind item 1 of
`fpbs-uniform-floor-equivalence-restricted-to-monotone-paths`, and (L) and (C)
are items 2 and 4 of `fpbs-one-edge-sprinkling-l2-lipschitz`. Item 2 of the
floor claim is a statement about `Z^2` and places no constraint on `G`.

1. **Floor contains the conclusion.** For every path `gamma` in `W_eps` ending
   at `e = p_c(S) 1_S`, `inf_t phi(gamma(t)) > 0` implies `phi(e) > 0`. So the
   closedness step asserts critical l2 on `Cay(Gamma,S)` among other things.
2. **Minimal admissible profile.** For any anchor `a` in `W_eps` and any
   `c >= 0`, the function
   `Phi_(a,c)(p) = max(0, c - ||R(a, a v p)||)` is route-admissible, where
   `a v p` is the coordinatewise maximum, and `Phi_(a,c)(a) = c`. A pointwise
   maximum of admissible functions is admissible.
3. **Exact content.** Fix anchors `a_1,...,a_k` with prescribed values
   `c_i = phi(a_i)`. The admissible functions with `Phi(a_i) >= c_i` for all `i`
   are all positive at `e` iff
   `max_i (c_i - ||R(a_i, a_i v e)||) > 0`. This is the one-step anchor
   certificate. When it fails, `max_i Phi_(a_i,c_i)` is admissible, matches
   every anchor value, and vanishes at `e`. The same holds for any path through
   the anchors, since the profile vanishes at `e` whatever path is taken.
4. **Consequence.** The route's inference from its prerequisites to
   `fpbs-critical-dyadic-projection-estimate` holds at those generating sets
   where some known anchor passes the one-step certificate, and nowhere else.
   The certificate is not among the route's prerequisites. It is a
   quantitative, generating-set-dependent inequality, and on record it
   certifies `T_(2k) x Z` for `k >= 4` only. So the route is invalid as
   recorded, and closing both of its prerequisites would not establish its
   target.

**Scope.** This is a separation of the proof schema, of the same kind as
`fpbs-fiid-finite-clusters-do-not-imply-dyadic-summability`. It says nothing
about whether `phi(e) > 0` is true. It says only that proving it requires
information about `phi` beyond (M), (L), (C) and the anchor values. The functions
`Phi_(a,c)` are not claimed to be norm profiles of any percolation.

Proof: `fpbs-surface-premises-only-one-step-certificate-proof`.
