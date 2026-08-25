---
rg: 2
id: binary-leavitt-shift-graph-has-exact-marked-commutator-table
kind: claim
title: Binary Leavitt corner pairs realize an exact marked shift-graph commutator table
distinct_from:
  leavitt-prefixes-form-exponential-heisenberg-packet: that uses the complete equality/off-diagonal table on single prefix addresses; this folds two addresses into each second commutator entry and realizes the sparse infinite-chromatic shift graph directly over the marked corner.
  dual-prefix-heisenberg-table-has-two-simultaneous-unit-orbits: that classifies individual prefix pairs up to simultaneous unit conjugacy; this gives canonical coefficient formulas for every vertex and proves the entire marked shift-graph table without choosing pair-dependent charts.
  binary-leavitt-bounded-area-chromatic-code: that additionally requires presentation fillings of uniformly bounded area; this establishes the exact group identities and the infinite chromatic number but leaves their uniform filling cost open.
artifacts:
  - research/property-t-free-leavitt-full-mf-radical.md
---

**ESTABLISHED.**  Put

```text
R=L_(F_2)(1,2),             q=s_1t_1,
Delta=St_20(R),             z=x_13(q).
```

For every `M>=2`, choose `M` distinct binary prefixes `alpha_0,...,alpha_(M-1)`
of one common depth and define the relative corner pairs

```text
S_i=s_1 s_(alpha_i) t_1,          T_i=s_1 t_(alpha_i) t_1.       (LS1)
```

They satisfy

```text
T_i S_j=delta_(ij) q.                                        (LS2)
```

Let `Sh(M)` have vertices `(i,j)` with `0<=i<j<M` and an oriented edge

```text
(i,j) -> (j,k)                    whenever i<j<k.              (LS3)
```

For `v=(i,j)`, put

```text
c_v=x_12(T_j),                    h_v=x_23(S_i+S_j).            (LS4)
```

Then every diagonal is the prescribed marked root and every shift edge is
trivial:

```text
[c_v,h_v]=z,                                                    (LS5)
[c_w,h_v]=1                  for every edge v -> w.             (LS6)
```

Moreover

```text
chi(Sh(M)) >= ceil(log_2 M).                                   (LS7)
```

Hence the disjoint union of the graphs `Sh(M)` has infinite chromatic number
and carries an exact commutator table with the *same* mark `z` at every
vertex.  No conjugating word `a_v` is required.

This statement is algebraic.  It does not assert that `(LS5)--(LS6)` have
uniformly bounded filling area in the fixed finite presentation of `Delta`.
That coherence upgrade is exactly the remaining content of
`binary-leavitt-bounded-area-chromatic-code`.
