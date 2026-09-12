---
rg: 2
id: power-return-certificates-have-linear-area
kind: claim
title: Every nontrivial free-word power return requires linearly many fixed relator conjugates
distinct_from:
  uniform-power-return-abelianization-barrier: that only detects nonzero exponent vectors; this detects every nontrivial cursor, including commutators, by a signed word count.
  spectral-recurrence-power-return-non-mf-criterion: that gives the analytic conditional endgame; this rules out bounded-area syntactic implementations without ruling out analytic implementations.
artifacts:
  - research/artifacts/power-return-certificates-have-linear-area-2026-09-08.md
---

For every finite free alphabet `S`, finite relator list `R`, and
nonidentity `w in F(S)`, there are explicit constants `D>=1,M>=0`
such that for every `a in F(S)` and positive integer `m`,

```text
Area_R(a w a^-1 w^-m) >= (m-1-3D)/(M+3D).
```

Area counts conjugates of fixed relators or their inverses; it is
infinite outside their normal closure. Thus total terminal
authentication cannot have a uniform area bound, even after adding
finitely many auxiliary generators and relations or using a cursor
with zero free abelianization.

Cyclically reduce `w` to `v`. Take `D=max(1,3(|v|-1))` and
`M=max_(r in R)|q_v(r)|`, including zero in the maximum, where
`q_v` counts overlapping copies of `v` minus copies of `v^-1`.

An isolated one-cell check on a terminal word does not authenticate
its meaning as `w^m`. The theorem only excludes bounded total area,
and does not refute the purely analytic norm-inequality target.
