---
rg: 2
id: fpbs-cost-one-plans-have-heavy-traffic-tails
kind: claim
title: Near-cost-one routing plans of a nonamenable group carry a fixed mass of heavy repeated traffic
distinct_from:
  fpbs-binary-entropy-traffic-tail-bound: that proves the positive criterion J <= T H/(2 log 2) + Tail_T and an odometer countermodel to entropy-only control; this proves a universal lower bound on Tail_T for every near-cost-one plan of a nonamenable group, so the uniformly integrable form of that criterion never applies over cost-one sources
  fpbs-quantitative-routing-tail-bound: that forces long routes in invariant spanning subgraphs of a Cayley graph; this forces congestion, not length, for finite routing plans with arbitrary group labels, using finite cells of the plan's own used graph
  fpbs-cost-one-routes-cannot-be-uniformly-tight: that is the qualitative non-tightness of route lengths; this is a quantitative traffic-tail inequality and a strictness statement about a proposed sufficient condition for cost preservation
  fpbs-sparse-reuse-signal-near-cost-one: that makes reuse flags of a relative plan rare and notes that a hypothetical cost gap would force relative traffic of order Delta/b; this proves, with no gap assumed, that every ordinary near-cost-one plan of a nonamenable group has peak traffic at least h_S/(B-1), and that Tail_T has liminf at least h_S for every T as B -> 1
artifacts:
  - research/artifacts/fpbs-cost-one-plans-have-heavy-traffic-tails-2026-09-16.md
---

Let Gamma be an infinite finitely generated group with finite generating set
S. Let h_S be the right edge Cheeger constant, the infimum over finite F of
|{(g,s) in F x S : gs not in F}|/|F|. It is positive exactly when Gamma is
nonamenable. For every finite routing plan D for S on a free p.m.p. action,
as in the conditional-traffic artifact, and every real T >= 0,

    h_S <= (T+1)(B(D) - 1) + Tail_T(D),    Tail_T(D) = sum_j integral Q_j 1_{Q_j>T},  Q_j = (k_j-1)_+.

Consequences for nonamenable Gamma:

* traffic bounded by M forces B(D) >= 1 + h_S/M;
* if B(D_n) -> 1 then liminf_n Tail_T(D_n) >= h_S for every T;
* sum_j integral Q_j^2 >= (h_S - eps)^2/(4 eps) when eps = B(D) - 1 <= h_S;
* cutoffs with Tail_{T_n}(D_n) -> 0 and B(D_n) -> 1 need
  T_n >= h_S/(4(B(D_n)-1)) eventually, so T_n H_n -> 0 forces
  H_n = o(B(D_n) - 1).

Hence over any free source action of cost one of a nonamenable group, no
source-near-optimal plan sequence has uniformly integrable repeated traffic.
For F_2 x Z, which has fixed price one, every free factor map preserves cost
and has source-near-optimal plans with J_pi -> 0. The fixed-cutoff
uniform-integrability form of `fpbs-binary-entropy-traffic-tail-bound` is
therefore strictly stronger than cost preservation.

Proof idea: first augment uncovered requests by direct copies, which changes
neither B nor the tails. Cut the used graph into finite connected Voronoi
cells of size at least R+1 around a Borel maximal 2R-separated marker set.
Their parent trees use budget 1 - O(1/R), so the crossing copies have measure
at most B - 1 + O(1/R). By mass transport, generator requests leaving the
cells have measure at least h_S. Each of them crosses a crossing copy, and
k <= T + 1 + Q 1_{Q>T}.

This does not prove or refute cost preservation, the target claim or Fixed
Price. It does not address sources of cost above one or the moving-cutoff
criterion beyond the stated rate. Status records a written deduction with a
passing finite replay of the counting steps
(`experiments/fpbs-cost-one-plans-heavy-traffic-2026-09-16/`), not
independent validation.
