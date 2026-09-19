---
rg: 2
id: fpbs-intrinsic-l1-rate-criterion-is-equivalent-to-goal
kind: claim
title: Positivity of the intrinsic l1 growth rate at p_u is equivalent to p_c < p_u on every nonamenable Cayley graph, so the intrinsic-rate route is a restatement of the goal
distinct_from:
  fpbs-intrinsic-growth-rate-positive-at-pu: that is the open premise (IL1); this proves it equivalent to p_c < p_u graph by graph, so it stays open exactly as long as the goal does
  fpbs-benjamini-schramm-universal: that is the goal; this shows the route through (IL1) adds no content to it
  fpbs-certificate-budget-premise-is-equivalent-to-goal: that shows the algorithmic certificate-budget premise is the goal restated; this shows the same for the intrinsic l1 rate premise, with a different invariant (the zero set of lambda_1)
  fpbs-intrinsic-growth-rate-positive-above-pc: that computes the zero set of lambda_1 as exactly [0,p_c]; this draws the consequence for the route and for every criterion built on lambda_1
---

**ESTABLISHED.** Proof in `fpbs-intrinsic-l1-rate-criterion-is-equivalent-to-goal-proof`.

**Setting.** `G = Cay(Gamma,S)` with `Gamma` finitely generated and
nonamenable; `lambda_1` as in `fpbs-intrinsic-l2-rate-closed-zero-set`.

**Theorem.**

1. If `p_u(G) < 1`, then (IL1) holds for `G`, that is `lambda_1(p_u) > 0`,
   **if and only if** `p_c(G) < p_u(G)`.
2. If `p_u(G) = 1`, then `p_c(G) < p_u(G)` holds outright, because
   `p_c(G) <= 1/gr(G) < 1`.
3. Hence "(IL1) for every nonamenable Cayley graph with `p_u < 1`" is
   logically equivalent to `fpbs-benjamini-schramm-universal`. The route
   `fpbs-universal-intrinsic-l2-rate-route` is a restatement of the goal, not a
   decomposition: its last hole is the goal itself.
4. **Class kill.** Let `q(G)` be any parameter attached to `G`. Every
   criterion of the form "`lambda_1(q(G)) > 0`", "`E_(q(G))|B^int_R(o)| >=
   e^(delta R)` for all `R`", or "`p_lambda1 < q(G)`" is equivalent to
   `q(G) > p_c(G)`. So no condition on the expected intrinsic l1 growth at a
   single parameter can separate `p_c` from `p_u` except by already knowing
   `p_u > p_c`.
   - Invariant: the zero set of `lambda_1`, which is exactly `[0,p_c]`.
   - Failing step: the implication "(IL1) => `p_c < p_u`" is valid, but any
     proof of (IL1) must be a proof that `p_u` lies in `(p_c,1]`.

**What survives.** The l2 rate `Lambda` sees uniqueness, but the wave-10
node recording `Lambda(p_u) = 0` on `T x Z^d` (where `p_{2->2} = p_u`, by
Hutchcroft--Pan) kills (IL2) and (UCS) as universal premises. Together with
item 4, the entire chain (UCS) => (IL2) => (IL1) => goal is closed off: its
strong links are false on some graphs with a window, and its weak link is the
goal. A useful intrinsic criterion has to be one whose zero set is not
`[0,p_c]` and that does not vanish at `p_u` on `T x Z^d`.
