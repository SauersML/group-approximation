---
rg: 2
id: free-s3-atom-opnorm-leakage-proof
kind: route
title: Evaluate nonidentity normalizers on the free marked character orbit
target: free-s3-atom-has-unit-opnorm-leakage
requires:
  - arbitrary-profile-selector-type-menu-dichotomy
  - literal-prefix-coupling-of-j1-j2-has-gl7-model
  - active-core-density-keeps-rectangular-capacity-critical
---

By `(ATM9)`, the stabilizer of `chi_*` under simultaneous row/column
permutation is trivial.  Hence for every `1!=u in S_3`,

```text
u e_(chi_*) u^*=e_(chi_*^u) orthogonal to e_(chi_*).  (1)
```

Equation `(1)` gives `eue=0`.  If `0!=P<=e`, then `(1-e)uP=uP`, and a
unitary is isometric on `P`; therefore its operator norm is one.  Every
orbit character is marked, so `z=-I` on the orbit representation and the
active projection is its full identity.  Tensoring with an arbitrary
multiplicity space proves the amplified statement.  The MSI-only artifact
checks freeness of the six-point action and the full marked carrier.
