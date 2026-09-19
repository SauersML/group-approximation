---
rg: 2
id: bounded-degree-partial-matrices-have-constant-completion-rank
kind: claim
title: Bounded-degree binary partial matrices have constant completion rank
distinct_from:
  bounded-neighbor-pauli-needs-growing-equality-components: that constructs a constant-dimensional Pauli realization by strong-coloring one signed graph; this gives a direct bipartite matrix-completion bound and isolates exactly why generator-column additivity is different.
  bounded-incidence-generator-column-minrank-witness: that restricts row and column labels to evaluations of linear maps on prescribed generator columns; this permits arbitrary vectors at the partial-matrix vertices.
---

Let `S subset I times J` be the specified positions of a partial matrix over
`F_2`, let every left and right degree be at most `Delta`, and prescribe
arbitrary values `s_ij in F_2` on `S`.  There is a completion of rank at most

```text
r=Delta+ceil(log_2 Delta)+1.                                (BDM1)
```

Thus no bounded-degree family of ordinary signed bipartite partial matrices
has minimum completion rank tending to infinity.  Treewidth, girth, or
expansion cannot change this conclusion.

The generator-column problem is not an instance of this unrestricted
theorem.  There one must have

```text
x_i=P a_i,       y_j=Q b_j,                                (BDM2)
```

for common linear maps `P,Q`.  Hence every dependency among the `a_i` must
also hold among the `x_i`, and similarly on the right.  The greedy completion
below does not preserve those dependencies.  This is exactly how additive X
and Z laws evade the constant-dimensional sparse-Pauli labeling theorem.
