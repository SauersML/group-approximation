---
rg: 2
id: fpbs-binary-entropy-traffic-tail-bound
kind: claim
title: Binary reuse entropy bounds descent defect only with traffic-tail control
distinct_from:
  fpbs-reuse-flag-localization-preserves-cost: that retains the full orbit process of reuse flags to preserve cost; this bounds the cost of forgetting them quantitatively and gives optimal plans with vanishing one-site entropy but fixed defect
  fpbs-finite-fiber-cost-bound: that bounds action costs across finite fibers; this controls the defect of specified plans and gives a fixed diffuse-fiber countermodel to entropy-only control
artifacts:
  - research/artifacts/fpbs/docs/binary-descent-entropy-tail.md
  - research/artifacts/fpbs/binary-descent-entropy-tail-verifier.py
---

For every finite routing plan D over a free factor, let H be the sum of the
integrated conditional binary Shannon entropies (natural logarithms) of every
reuse flag 1_{k_j>=2}, and put Q_j=(k_j-1)_+. Then for every T>=1,

    J_pi(D) <= T H/(2 log 2) + sum_j integral Q_j 1_{Q_j>T}.

Hence source-near-optimal plans with vanishing H and uniformly integrable
repeated traffic give cost preservation whenever the base cost is finite.
It also suffices to choose T_n with T_n H_n->0 and the displayed tails ->0.

These traffic hypotheses cannot be discarded from this criterion: on one
fixed factor Bernoulli Z times its 2-adic odometer onto Bernoulli Z there are
fully covered plans with exactly two fixed labels, B=1, H->0 and J=1. Both
action costs equal one. This rules out an entropy-only inference about specified
plans, not the existence of better plans or any currently named Cairn route.
