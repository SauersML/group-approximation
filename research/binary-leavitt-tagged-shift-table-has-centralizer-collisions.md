---
rg: 2
id: binary-leavitt-tagged-shift-table-has-centralizer-collisions
kind: claim
title: A third-address tagged Leavitt shift table evades the fixed-column centralizer fences algebraically
distinct_from:
  binary-leavitt-shift-graph-has-exact-marked-commutator-table: that puts the two vertex addresses in the column and the terminal address in the row, leaving one fixed column adjacent to infinitely many distinct rows; this puts the initial address and a private third tag in the column, so all outgoing neighbours have exactly the same row.
  finite-prototype-column-codes-force-coset-collisions: that proves unbounded normalized-row collisions are necessary for a finite-prototype bounded-area code; this constructs those collisions in an exact binary-Leavitt marked table but does not yet prove uniform filling area.
artifacts:
  - research/binary-leavitt-bounded-area-chromatic-code.md
---

**ESTABLISHED EXACT TABLE; UNIFORM AREA OPEN.**  Put

```text
R=L_(F_2)(1,2),             q=s_1t_1,
Delta=St_20(R),             z=x_13(q).
```

For each `M`, choose mutually orthogonal corner pairs

```text
A_r B_s=delta_(rs)q                         (0<=r,s<M)
A_r D_(ij)=0                                (0<=r<M, 0<=i<j<M),
```

where every private tag column `D_(ij)` is a further dual-prefix column,
distinct from all the `B_r`.  On the shift graph with vertices `(i,j)`,
`0<=i<j<M`, and edges `(i,j)->(j,k)`, define

```text
c_(ij)=x_12(A_i),
h_(ij)=x_23(B_i+D_(ij)).                                  (TST1)
```

Then

```text
[c_(ij),h_(ij)]=z,
[c_(jk),h_(ij)]=1                    whenever i<j<k.       (TST2)
```

The graphs have chromatic number at least `ceil(log_2 M)`, as for the usual
shift graphs.  Unlike the previous shift table, this table has both of the
features demanded by the finite-prototype collision dichotomy:

1. for a fixed vertex `(i,j)`, every outgoing neighbour `(j,k)` has the
   **same group word value** `c_(jk)=x_12(A_j)`;
2. the private tag makes the column coefficients `B_i+D_(ij)` distinct as
   `(i,j)` varies, so no one literal column is incident to infinitely many
   distinct row values.

Consequently neither the fixed-column argument in
`leavitt-chromatic-tables-have-area-divergence` nor the injective-fibre case
of `finite-prototype-column-codes-force-coset-collisions` refutes this
vertex data.  It is a genuine algebraic escape from the cumulative/tree
centralizer pattern, not a rewording of either old table.

What remains open is exactly the fixed-presentation comparison.  For each
single edge, the three orthogonal addresses `(i,j,(ij))` can be carried to a
fixed three-address prototype, so the coefficient identity has a fixed-cell
description.  But `c_(jk)` is used at all predecessors `(i,j)`.  Choosing
the edgewise three-address transporter separately gives different words for
that one row occurrence.  A proof of uniform `(CCC2)` must show that these
occurrence charts compare with bounded area, or give one canonical word for
`x_12(A_j)` whose commutator with every tagged predecessor column pays one
bounded mixed/opposite-root cell.  Qualitative prefix cancellation does not
provide that comparison.

Thus `(TST1)` supplies the requested new vertex geometry and narrows the
bounded-area leaf to a multi-predecessor chart-coherence cell.  It does not
establish `binary-leavitt-bounded-area-chromatic-code` by itself.

No Property `(T)`, Kazhdan input, matrix approximation, trace, or literature
theorem is used.

DERIVATION
binary-leavitt-tagged-shift-table-proof
