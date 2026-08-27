---
rg: 2
id: atlas-q1920-psl5-double-natural-seam-proof
kind: route
title: Exhaust the full A-centralizer on two natural PSL5(2) blocks
target: atlas-q1920-psl5-double-natural-module-has-no-collision-seam
requires:
  - atlas-q1920-marked-simple-factor-is-at-least-ten-million
artifacts:
  - experiments/atlas_a4_q1920_psl5_repeated_module_seam.g
  - research/artifacts/atlas-a4-q1920-psl5-double-natural-seam.json
---

The verifier reconstructs the two marked `Q1920` classes from their exact
four-generator presentation, quotients each by its center, and enumerates
the two ambient conjugacy classes in `PSL5(2)`.  For each embedding it uses

```text
Aut(Q/Z(Q)) / Aut_PSL5(2)(Q/Z(Q))
```

to obtain all four marked twists.  Hence the `2 x 2 x 4=16` cases are a
complete marked-orbit list.

For each case, take two diagonal copies of the natural module.  Exact MeatAxe
decomposition gives

```text
W^2|A : 2,2,2,2,1,1,
dim_F2 End_A(W^2)=20,
|End_A(W^2)^x|=120960.                                  (Q1920-2W-2)
```

The script enumerates all `120960` invertible centralizer elements and tests
the two equations in `(Q1920-2W-1)`.  Every one of the sixteen marked slices
has zero candidates.  Since a protected collision `S4=<t,s,c>` requires a
nonidentity involution `c`, no doubled-natural slice is a full carrier.
