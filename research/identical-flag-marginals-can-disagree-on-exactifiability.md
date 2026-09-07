---
rg: 2
id: identical-flag-marginals-can-disagree-on-exactifiability
kind: claim
title: Equal local flag marginals and energy charges can conceal an impossible joint syndrome outcome
artifacts:
  - research/artifacts/qpcp-joint-syndrome-support-2026-09-07.md
  - scripts/check_qpcp_syndrome_support.py
  - research/artifacts/qpcp-syndrome-support-replay-2026-09-07.json
distinct_from:
  nonorthogonal-pair-forbids-single-term-syndrome-ports: that forbids charging flags to individual terms; this permits both-term neighborhoods and exhibits identical marginal charges for one recoverable and one unrecoverable joint measurement.
  joint-syndrome-support-characterizes-exactifiability: that is the all-input characterization for a fixed measurement; this supplies two explicit bounded-size dilations with identical marginals and opposite recovery verdicts.
---

For `N>1`, use the one-qubit terms `P,Q_N` of the paired-projector
obstruction and write `d=N^2+1`. The two isometries
`v -> (|10>+|01>)/sqrt(2) tensor v` and
`v -> (|00>+|11>)/sqrt(2) tensor v`, with the same commuting syndrome
bit tests, have identical marginal effects `F_P=F_Q=I/2` and identical
domination bounds `F_a <= (d/4)(P+Q_N)`.

Only the first is exactifiable outside its sampled fault label. The second
outputs the empty fault set with probability one half, although
`ker P intersection ker Q_N = {0}`. Both leave the data untouched before
recovery. Thus marginal bounds and local commuting flag tests do not prove
the exactness hypothesis. This does not refute a route that separately
proves exactness for the same joint measurement.
