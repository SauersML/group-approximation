---
rg: 2
id: leavitt-even-relations-through-eight-are-q-visible
kind: claim
title: Every even Leavitt corner identity through length eight is visible in the short group Q
artifacts:
  - research/artifacts/classify-leavitt-even-through-eight.py
  - research/artifacts/leavitt-area-ten-long-residue-2026-08-21.md
distinct_from:
  leavitt-no-odd-nine-corner-relations: that proves an odd-girth statement at length nine; this identifies every even identity through eight with the defining Q relations.
  leavitt-short-atlas-does-not-close-six-cells: that tests whether Q-trivial regions close a six-cell picture; this proves no additional low-length coefficient relation lies outside Q.
---

Let

```text
Q=V_4(h_0,h_2)*V_4(k_0,k_1)*F(h_1,k_2).
```

If a cyclically formally reduced even word of length at most eight in the
six oriented corner labels is nontrivial in `Q`, then it is nontrivial after
the three-gate substitution in `G_0*G_1`.  Equivalently, every actual even
corner identity through length eight is already a `Q`-identity.
