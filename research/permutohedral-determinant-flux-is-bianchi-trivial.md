---
rg: 2
id: permutohedral-determinant-flux-is-bianchi-trivial
kind: claim
title: Determinant flux of shared edge gauges is Bianchi-trivial on every closed permutohedral surface
distinct_from:
  first-permutohedral-scalar-obstruction-is-rank-three: that identifies the first closed incidence equation which independently prescribed face phases must satisfy; this proves actual face phases extracted from one shared edge family satisfy it identically.
  isolated-regular-a2-hexagon-has-free-external-holonomy: that removes arbitrary full-unitary holonomy on one cell using a free edge; this rules out the determinant of a multi-cell connection even after there are no free edges.
---

**ESTABLISHED.**  Let `W_e in U(d)` be one genuinely shared unitary for each
oriented edge of a finite oriented two-complex, with
`W_(bar e)=W_e^(-1)`.  For a face `f`, define its determinant curvature by

```text
c_f=product_(e in boundary f) det(W_e)^(epsilon_(f,e)).  (PDB1)
```

For every integral closed two-cycle `sum_f n_f f`, one has

```text
product_f c_f^(n_f)=1.                                  (PDB2)
```

Indeed the exponent of `det(W_e)` in the product is the coefficient of `e`
in the cellular boundary of the two-cycle, hence zero.  In particular, on
the boundary of the `S_4` permutohedron the product of the determinant
curvatures of the eight braid hexagons and six commuting squares is always
one.  If the square curvatures are one, the product of the eight hexagonal
determinants is automatically one.

Consequently `(PSC3)` in
`first-permutohedral-scalar-obstruction-is-rank-three` is a compatibility
test for **independently prescribed** face targets, not a quantity that can
be nontrivial when all face data have already been authenticated to one
shared family of edge occurrences.  A determinant, scalar phase, or
abelianized multiplicity cocycle cannot be the genuine shared-cell
obstruction to `leavitt-regular-character-is-not-mf`.

The remaining possibilities are nonabelian and occurrence-typed: for
example an ordered face holonomy acting on a selected packet summand, where
the conjugating transports to a common base point are themselves fixed
native occurrences.  Merely computing six or eight independent face
determinants loses exactly that information.

DERIVATION
permutohedral-determinant-bianchi-proof
