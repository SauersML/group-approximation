---
rg: 2
id: leavitt-nested-prefix-conjugacy-uniform-area
kind: claim
title: Fill every nested-prefix marked conjugacy difference with one bounded cell budget
---

**OPEN.**  In one fixed finite presentation of

```text
Delta=St_20(L_(F_2)(1,2)),            z=x_13(s_1t_1),
```

choose representatives for the vertex roots `b_m=x_12(e_m)` and for the
conjugators `a_(j,k)` in `(NPC5)`.  Prove that one constant `A` satisfies

```text
Area(b_j^(-1)b_k a_(j,k) z^(-1) a_(j,k)^(-1))<=A       (NPA1)
```

for every `j<k`.

Together with the established infinite clique and the bounded-area
conjugacy-difference criterion, `(NPA1)` kills `z` in every norm matrix
corona.  No projection decoder or trace is then needed.

## Attempts

- **Expand the annulus into prefix leaves.**  The exact proof uses `k-j`
  orthogonal target leaves and a source prefix code of the same size.
  Verifying the partial-equivalence table leaf by leaf gives area growing
  with `k-j`, so exact Murray--von Neumann equivalence is not the required
  quantitative statement.
- **Keep only bounded-width annuli.**  If `k-j` is bounded, the graph on the
  integer vertices has finite chromatic number.  Infinite chromaticity
  necessarily uses unbounded annulus width.
- **Apply the fixed-centralizer properness obstruction.**  The refutations of
  the cumulative and canonical-Morita commutator tables freeze one
  nontrivial root and produce infinitely many elements in its centralizer.
  Here both endpoint roots move and their difference is a conjugate of the
  mark; no fixed centralizer section has been obtained.  Thus the existing
  area-divergence theorem does not refute `(NPA1)`.
- **Live calculation.**  Seek a self-similar Whitehead diagram which folds
  the whole left-comb annulus before expanding its leaves.  A negative result
  would need a new conjugacy-difference area lower bound, not the current
  centralizer theorem.
