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

The direct stabilizer repair is ruled out by
`tagged-shift-stabilizer-normalization-has-unbounded-row-holonomy`.
Choosing the private tag so one pair transporter fixes `A_i` and
simultaneously normalizes `A_j` and `B_i+D_(ij)` does normalize each
coefficient triple as group elements.  It does not make the canonical target
word for `A_j` equal to its occurrence in every predecessor chart.  Uniform
bounded-area comparisons at both rows would confine the two endpoint
holonomies to finite sets by finite-mark centralizer-area properness, forcing
a uniform bound on the number of successors.  Private tags do not occur in
that row-holonomy equation.

Thus `(TST1)` supplies the requested new vertex geometry and narrows the
bounded-area leaf to a multi-predecessor chart-coherence cell.  It does not
establish `binary-leavitt-bounded-area-chromatic-code` by itself.

## Attempts

* **Source-row stabilizer normalization.**  For each `(i,j)`, use the private
  tag to choose a transporter which fixes `A_i` and normalizes `A_j` and
  `B_i+D_(ij)` to one fixed two-row/one-column cell.  The coefficient-level
  construction succeeds.  Its bounded-area upgrade fails: the source and
  target occurrences differ from their canonical row words by endpoint
  holonomies centralizing nontrivial order-two elementary roots.  The route
  `tagged-shift-stabilizer-holonomy-proof` shows that bounded comparisons at
  both ends would bound every successor fibre.  Literal conjugacy is the
  zero-area special case and is therefore impossible on growing packets.
* **Two-diagonal coefficient shear.**  The explicit unit
  `u_(ij)=1+B_iA_j` fixes `B_i+D_(ij)` and `A_j`, while sending `A_i` to
  `A_i+A_j`.  Consequently the edge commutator is the quotient of the
  ordinary and sheared marked-diagonal discrepancies by the exact identity
  `(TSC5)`.  This is a genuine non-chart algebraic reduction.  Its natural
  fixed-cell implementation is ruled out by
  `tagged-shift-shear-has-unbounded-fixed-mark-area`: every
  shear fixes the same mark `z`, the shears escape in `C_Delta(z)/<z>`, and
  their mark-preservation filling areas are unbounded.  A direct filling of
  the sheared diagonal which does not compare through the shear remains
  open.
* **Direct one-chart sheared diagonal.**  Avoid the shear and normalize the
  whole rank-one Gram block
  `(A_i+A_j)(B_i+D_(ij))=q` to one fixed marked Steinberg prototype, with
  the private third address appearing only in its outer conjugator.  This
  still cannot give a bounded cell.  By
  `tagged-sheared-diagonal-one-chart-hits-mark-area`, returning the
  conjugated prototype mark to the literal common `z` costs a commutator
  with `z`.  The transporters lie in `C_Delta(z)`, and the pairwise-distinct
  sheared rows force them into distinct cosets modulo `<z>`, so those areas
  diverge.  A several-chart diagram whose internal mark seams cancel without
  an individual mark-return filling is not ruled out.
* **Two or three charts with pairwise internal mark cancellation.**  Splitting
  the direct Gram cell does not help if its conjugated `z` occurrences are
  joined by ordinary pairwise seams.  The theorem
  `bounded-tagged-mark-seam-complex-has-finite-row-range` treats any fixed
  number of such charts.  A spanning tree from the outer literal `z` gives
  a bounded `[g_v,z]` filling for every chart gauge; centralizer-area
  properness leaves finitely many gauges, hence finitely many output rows.
  This contradicts the distinct rows `x_12(A_i+A_j)`.  A surviving finite
  complex must contain a genuinely non-pairwise mark-fusion cell rather than
  only cancelling equal conjugated marks along seams.

No Property `(T)`, Kazhdan input, matrix approximation, trace, or literature
theorem is used.

DERIVATION
binary-leavitt-tagged-shift-table-proof
