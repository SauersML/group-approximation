---
rg: 2
id: fixed-depth-canonical-mark-collapse-proof
kind: route
title: Take the microstate limit before the proof-depth limit
target: fixed-depth-canonical-mark-estimates-rule-out-hyperlinearity
requires: []
---

Fix `N` in `(FDM1)` and apply it along a hypothetical canonical-trace
microstate sequence.  Finite presentation makes the defining-relator defect
tend to zero, while the canonical delta condition makes `(FDM2)` tend to zero
on the fixed finite set `F_N`.  Hence the limsup of the marked squared
distance is at most `b_N`.  This holds for every `N`, so `b_N->0` forces that
distance to tend to zero.  The elementary identity

```text
||V-I||_2^2=2-2 Re tr(V)
```

for a unitary word `V=w(U_n)`, together with `w!=1`, makes the same quantity
tend to two.  The contradiction proves the claim.
