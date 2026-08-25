---
rg: 2
id: one-column-orbit-bounded-area-codes-have-bounded-chromatic-number
kind: claim
title: One uniformly typed finite-order column orbit cannot support bounded-area graphs of unbounded chromatic number
artifacts:
  - research/binary-leavitt-bounded-area-chromatic-code.md
distinct_from:
  leavitt-chromatic-tables-have-area-divergence: that freezes a visibly persistent column in the nested shift and cumulative tables; this permits disjoint finite graph blocks and proves that normalizing any high-degree column from one uniform conjugacy type recreates the same obstruction.
  fixed-mark-forbids-uniform-clifford-table-area: that treats complete multiplication tables with one fixed central mark; this needs only edge commutators and the elementary bound `chi<=Delta+1`.
  rf-conjugacy-difference-graphs-finitely-colorable: that colors pure conjugacy-difference graphs using a finite quotient of a residually finite actor; this uses finite-order centralizer-area properness and does not assume residual finiteness.
---

**ESTABLISHED ONE-ORBIT CHROMATIC FIREWALL.**  Let
`Gamma=<S|R>` be finitely presented and let `beta` represent a nontrivial
finite-order element.  Suppose a family of finite graphs `G_n` carries words
`c_v,h_v,b_v` and constants `A,B` with the following properties:

1. every column is uniformly typed by the one orbit of `beta`,

   ```text
   Area_R(h_v (b_v beta b_v^(-1))^(-1)) <= B;          (OCF1)
   ```

2. every oriented edge `v -> w` has

   ```text
   Area_R([c_w,h_v]) <= A;                              (OCF2)
   ```

3. for each fixed `v`, the normalized neighbor words

   ```text
   b_v^(-1)c_wb_v,              w in N^+(v),            (OCF3)
   ```

   represent distinct cosets modulo `<beta>`.

Then the out-degrees, and hence the chromatic numbers of the underlying
undirected graphs, are uniformly bounded.

Indeed, conjugate `(OCF2)` by `b_v^(-1)` and replace the normalized column
by `beta` using `(OCF1)`.  A two-sided commutator telescope gives

```text
Area_R([b_v^(-1)c_wb_v,beta]) <= A+2B.                 (OCF4)
```

The properness theorem
`finite-mark-centralizer-commutator-area-is-proper` says that only finitely
many `<beta>`-cosets in `C_Gamma(beta)` admit representatives satisfying the
fixed bound in `(OCF4)`.  Condition `(OCF3)` therefore bounds every
out-degree by one constant `D(A+2B,beta)`.  Every induced subgraph inherits
the restricted orientation and has at most `D` times its number of vertices
many edges, hence average degree at most `2D`.  It therefore has a vertex of
degree at most `2D`; greedy deletion and reinsertion gives

```text
chi(G_n) <= Delta(G_n)+1 <= 2D+1.                       (OCF5)
```

Consequently separating the finite shift graphs into disjoint Leavitt
cylinders does not evade the area obstruction when their column words remain
uniform conjugates of one prototype.  Each graph of large chromatic number
contains a high-degree column; normalizing that one column recreates an
arbitrarily large bounded-area centralizer section inside a single finite
block.  A viable chromatic compiler must therefore use infinitely many
genuinely different column types, allow neighbor collisions modulo the
normalized column, or replace individual edge-area control by a different
finite-coordinate estimate.

No Property `(T)`, Kazhdan projection, trace estimate, or literature theorem
is used.
