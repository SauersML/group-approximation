---
rg: 2
id: fpbs-replica-meet-limit-sandwiched-by-exp-decay-threshold-proof
kind: route
title: Sum the k-th power of an exponentially decaying two-point function against sphere growth, then combine with the sandwich and the amenable caps
target: fpbs-replica-meet-limit-sandwiched-by-exp-decay-threshold
requires:
  - fpbs-replica-meet-threshold-sandwich
  - fpbs-meet-threshold-capped-by-amenable-relative-threshold
  - fpbs-exp-decay-threshold-facts
  - fpbs-hutchcroft-pan-tree-times-amenable-l2-threshold-is-pu
artifacts:
  - research/artifacts/fpbs/docs/replica-meet-exp-decay-threshold-2026-09-19.md
---

The complete proof is in Sections 1 and 2 of the artifact.

1. **Item 1.** Fix `p` with `xi_p > 0` and `k` with `k xi_p > gr`. Pick
   `eps > 0` with `k(xi_p - eps) > gr + eps`.
   - For `d(o,x) = n >= N`: `tau_p(o,x) <= e^{-(xi_p - eps) n}`, by the
     definition of `xi_p`.
   - `|S_n| <= C e^{(gr + eps) n}`, by the definition of `gr`.
   - So `Z_k(p) <= |B_N| + sum_n C e^{(gr+eps)n - k(xi_p-eps)n} < infinity`.
   - On `T_d`: `tau_p = p^{|x|}`, `xi_p = -log p`, `gr = log(d-1)`. This
     matches sandwich item 5.
2. **Item 2.** Every `p < p_exp` has `xi_p > 0`, since `tau_p` is monotone in
   `p`. So `p <= p_k` for `k > gr/xi_p`, which gives `p_exp <= sup_k p_k`. The
   other inequalities are sandwich items 1 and 4
   (`fpbs-replica-meet-threshold-sandwich`).
3. **Item 3.** The middle inequality is item 1 of
   `fpbs-meet-threshold-capped-by-amenable-relative-threshold`, taking the sup
   over `k`.
   - For the last inequality, let `p > p_u` and let `U` be the unique infinite
     cluster.
   - `W = U ∩ H` has `H`-invariant law, and `P(o in W) = theta(p) > 0`.
   - By the invariant-finite-set lemma (Lemma 0 of the amenable-caps proof),
     `W` is infinite on `{o in W}`. So `p >= p_c(H;G)`.
4. **Item 4.** Pick `p` in `(p_c, p_exp)` and apply item 1. The implications
   to the gap and to the relative gap are the finite-mean-to-a.s. step (the
   sandwich, item 1) and item 3 of Lemma A.
5. **Item 5.** The equalities follow from items 2 and 3 once `p_exp = p_u`.
   - (a) `fpbs-exp-decay-threshold-facts` item 4 (Schonmann). The surface-group
     graph is the 1-skeleton of the `{4g,4g}` tiling of the hyperbolic plane,
     which is planar, one-ended and transitive.
   - (b) Hutchcroft–Pan give `p_(2->2) = p_u`, and
     `p_(2->2) <= p_exp <= p_u` holds by facts items 1 and 3.
   - (c) On a tree, `p_exp = 1 = p_u`.
