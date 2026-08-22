---
rg: 2
id: bounded-degree-partial-matrix-completion-proof
kind: route
title: Make every column neighborhood independent by greedy row labels
target: bounded-degree-partial-matrices-have-constant-completion-rank
requires: []
---

Assign vectors `x_i in F_2^r` greedily.  When assigning `x_i`, for every
neighbor `j` avoid the span of the already assigned vectors
`{x_k:k in N(j), k<i}`.  Each such span has at most `2^(Delta-1)` elements,
and there are at most `Delta` neighboring columns.  By `(BDM1)`,

```text
Delta 2^(Delta-1) < 2^r,
```

so a choice remains.  At the end, the vectors in every `N(j)` are linearly
independent.

For each column `j`, solve the at most `Delta` independent equations

```text
x_i.y_j=s_ij                  (i in N(j))
```

for `y_j in F_2^r`.  The completed matrix

```text
C_ij=x_i.y_j
```

has the prescribed entries and factors through `F_2^r`, so its rank is at
most `r`.
