---
rg: 2
id: rank-conjugacy-overlap-proof
kind: route
title: Compare traces of the two hybrid blocks and match their negative eigenspaces at zero overlap
target: rank-conjugacy-detects-projection-overlap
requires: []
artifacts:
  - research/artifacts/independent-set-rounding-rank-router-2026-08-23.md
---

Direct expansion gives

```text
tau_2(R)=1-tau(P)-tau(Q),
tau_2(S)=1-tau(P)-tau(Q)+2tau(PQ).                    (RCP1)
```

Unitary conjugacy preserves trace and `|tau_2(X)|<=||X||_2`, so `(RCP1)`
proves `(RCD1)` because `tau(PQ)=||PQ||_2^2`.  If `PQ=0`, then `P,Q` are
orthogonal, `AB` is an involution, and the negative spectral projections of
`R` and `S` are

```text
diag(P,Q),               diag(P+Q,0).
```

They and their complements have identical center-valued trace, hence are
unitarily equivalent; this proves `(RCD2)`.  Finally `(RCD1)` and weighted
Cauchy--Schwarz give

```text
delta<=1/2 sum_f alpha_f sqrt(e_f)
     <=1/2 sqrt(sum_f alpha_f e_f),
```

which is `(RCD3)`.

