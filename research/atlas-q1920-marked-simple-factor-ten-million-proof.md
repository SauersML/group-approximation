---
rg: 2
id: atlas-q1920-marked-simple-factor-ten-million-proof
kind: route
title: Filter simple groups by the Q image and exhaust every marked collision centralizer
target: atlas-q1920-marked-simple-factor-is-at-least-ten-million
requires:
  - atlas-full-q1920-completion-is-normally-generated-by-v
  - atlas-any-q1920-completion-must-move-the-module
artifacts:
  - experiments/atlas_a4_full_large_q1920_simple_factor_filter.g
  - experiments/atlas_a4_q1920_simple_overgroup_subgroups.g
  - experiments/atlas_a4_q1920_simple_overgroup_marked_seam.g
  - research/artifacts/atlas-a4-q1920-marked-simple-overgroups-under-ten-million.json
---

By `atlas-full-q1920-completion-is-normally-generated-by-v`, a nontrivial
simple factor `S` retains the binary module and hence contains `Q1920` or its
central quotient of order `960`.  The injected `S3 x S3` margin strengthens
the order divisor to `2880`.

GAP's complete small-simple catalogue has exactly fifteen groups of order
below `10^7` divisible by `2880`.  Exact `IsomorphicSubgroups` calculation
leaves only

```text
S                 Q/Z classes    Q classes
PSL(3,4)               2             0
M22                      2             0
O(7,2)=Sp6(2)           0             1
PSU(4,3)                2             0
PSL(5,2)                2             0.                  (Q1920-10M-1)
```

The other ten simple groups contain neither possible image of `Q`.

For each surviving subgroup class, recover both exact marked Q1920 tuples.
All marked embeddings into `S`, up to ambient conjugacy, are obtained by the
right cosets

```text
Aut(Q_image) / Aut_S(Q_image).
```

The verifier constructs `Aut_S(Q_image)` from the normalizer of the embedded
subgroup, so this is an exact orbit enumeration rather than a random search.
For every coset representative it computes `C_S(A)`, `A=<r,u>`, and tests
each involution `c` against

```text
(c t)^3=1,      t c s c t^-1 c s t c=1.                  (Q1920-10M-2)
```

The number of twists and centralizer-order histograms, for each marking, are

```text
PSL(3,4): 48,  {1:48};
M22:      36,  {2:36};
Sp6(2):    4,  {4:2,12:2};
PSU(4,3): 48,  {3:48};
PSL(5,2):  8,  {6:8}.                                    (Q1920-10M-3)
```

There are zero collision candidates in every row, for both markings.  Thus
the obstruction occurs before adjoining `z` or checking the C144 margin.
No eligible `S` below `10^7` is a marked simple factor, which proves the
claim.
