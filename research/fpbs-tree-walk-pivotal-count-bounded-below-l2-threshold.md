---
rg: 2
id: fpbs-tree-walk-pivotal-count-bounded-below-l2-threshold
kind: claim
title: On the regular tree the conditional random-walk pivotal count is bounded below the l2 threshold and linear in n above it
distinct_from:
  fpbs-l2-gap-gives-bounded-pivotal-counts: that proves the n-free bound whenever the connectivity operator is bounded; this shows on T_d that the n-free conclusion fails at every p above p_(2->2), so that bound's regime is exactly sharp there.
  fpbs-pivotal-kernels-hold-on-known-gap-test-graphs: that verifies the linear budget on T_d and other gap graphs; this computes the order of the count on T_d at every p off the threshold, including p_(2->2)<p<1 where the operator is unbounded.
  fpbs-hierarchical-pivotal-amplification: that has unbounded counts on nontransitive finite networks at one parameter; here the graph is a Cayley graph, the counts stay linear (the budget holds), and the transition is at p_(2->2), not at a neutral recursion fixed point.
---

Let `d>=3` and `T_d = Cay((Z/2)^(*d), {a_1,...,a_d})`, the `d`-regular tree.
Use the notation of `fpbs-l2-gap-gives-bounded-pivotal-counts`: `X_n` is simple
random walk from `e`, independent of Bernoulli(`p`) bond percolation. For
`R>=n`, `E_(n,R)` is the event that `e` connects to `X_n` inside `B_R`, and
`N_(n,R)` is the number of open pivotal edges for that event. Put
`p_* = 1/sqrt(d-1)`.

**Theorem.**

1. `E_p[N_(n,R) | E_(n,R)]` does not depend on `R>=n`, is at most `n`, and is
   nondecreasing in `p`.
2. If `p<p_*`, write `x = p sqrt(d-1)`. Then `||T_p||_(2->2) <= 3/(2(1-x)^2)`,
   so for all `n>=1` and `R>=n`,
   `E_p[N_(n,R)|E_(n,R)] <= 9d / (2(1-x)^4)`.
3. If `p_*<p<1`, write `x = p sqrt(d-1) > 1`, `delta = min(ln(x)/2, 1/2)` and
   `eps = delta/4`. Then for all `n>=4` and `R>=n`,
   `E_p[N_(n,R)|E_(n,R)] >= eps n (1 - e^3 (d/(d-1)) (n+1)^3 exp(-n delta ln(x)/4))`.
   In particular the count is at least `eps n/2` for all large `n`.

So on `T_d` the random-walk pivotal count is bounded uniformly in `n` exactly
on `p<p_(2->2)(T_d)`, apart from the threshold itself, and it is genuinely
linear on `(p_(2->2),1)`. Throughout `p_c=1/(d-1)<p_*<p_u=1`.

**What this settles.**

* The n-free bound of `fpbs-l2-gap-gives-bounded-pivotal-counts` cannot be
  pushed past `p_(2->2)`, even on the tree, where nothing happens to uniqueness.
* A proof of `fpbs-pivotal-budget-universal` on a Cayley graph with
  `p_c=p_(2->2)` (the only kind where the budget is still open) cannot proceed
  by proving n-free counts.
* On this example, the count grows linearly whenever the connectivity operator
  is unbounded, and the linear budget in PB is attained with constant 1. PB is
  therefore the right order of statement, and uniqueness plays no role in the
  transition.

Proof: `fpbs-tree-walk-pivotal-count-bounded-below-l2-threshold-proof`.
Exact check: `experiments/tree-pivotal-threshold-2026-09-17/tree_pivotal_counts.py`.
It gives counts `5.78, 19.97, 61.18` at `n=320`, `d=3`, for
`p = 0.8 p_*, p_*, 1.2 p_*`. The threshold case `p=p_*` is not proved here;
the numerics suggest order `sqrt(n)`.
