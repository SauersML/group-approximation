---
rg: 2
id: stw91-finite-subgroup-projection-obstruction
kind: claim
title: Finite-subgroup averaging projections give an ordered-K0 obstruction to strict comparison and selflessness
distinct_from:
  stw99-problem-xci-cstar-simple-selfless: this is a falsifiable necessary condition for one group algebra, not a construction of a violating C*-simple group and not a solution of Problem XCI.
  stw99-problem-xc-cstar-simple-strict-comparison: the root asks for strict comparison of all positive elements for every C*-simple group; this gives a concrete necessary test using a distinguished family of projections for one group.
artifacts:
  - research/artifacts/stw91-selfless-group-frontier-2026-08-30.md
---

Let `G` be a discrete group and, for each finite subgroup `H <= G`, set

```text
e_H = (1/|H|) sum_{h in H} lambda_h in C*_r(G).
```

If `C*_r(G)` has strict comparison with respect to `tau_G`, then for all
finite subgroups `H,K <= G` with `|H|>|K|` one has

```text
e_H Cuntz-subequivalent e_K,                         (1)
[e_K]-[e_H] in K_0(C*_r(G))_+.                       (2)
```

Consequently, a C*-simple group with finite subgroups `H,K` satisfying
`|H|>|K|` but violating either (1) or (2) is a counterexample to STW Problems
XC and XCI.  Failure of (2) is a certificate entirely in ordered `K_0`.
