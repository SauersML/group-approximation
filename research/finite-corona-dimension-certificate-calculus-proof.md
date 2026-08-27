---
rg: 2
id: finite-corona-dimension-certificate-calculus-proof
kind: route
title: Reduce projection relations to a rational cone and apply the finite-dimensional alternative theorem
target: finite-corona-dimension-certificate-calculus
requires:
  - matrix-corona-projection-monoid-is-rank-germs
  - finite-root-heisenberg-multiplicity-germs
---

Apply `Dim_Q` to `(FDC1)`.  Additivity and Murray--von Neumann invariance
give

```text
B x=0,    x_i=Dim_Q(p_i).                              (FDP1)
```

Choose simultaneous coordinate projection lifts.  Since the presentation is
finite, on one common cofinite tail their rank vectors `r_n` satisfy

```text
r_n in C_B intersect Z^N.                              (FDP2)
```

Suppose `(FDC3)` holds.  Pair it with an arbitrary `x in C_B`:

```text
-x_i=y.(Bx)+s.x=s.x>=0.
```

Since also `x_i>=0`, one has `x_i=0`.  Applying this to `(FDP2)` makes the
coordinate rank of `p_i` eventually zero, hence `p_i=0` by faithfulness of
the rank-germ dimension.

Conversely, let

```text
C_B^*={u in R^N : u.x>=0 for every x in C_B}
```

be the dual cone.  The standard finite-dimensional alternative theorem gives

```text
C_B^*=im(B^T)+R_(>=0)^N.                               (FDP3)
```

The assertion that every `x in C_B` has `x_i=0` is equivalent, using
`x_i>=0`, to `-e_i in C_B^*`.  Equation `(FDP3)` is then exactly `(FDC3)`.
All input data are rational, so the witnesses may be chosen rational.

If the marked coordinate is not forced to vanish, the rational polyhedral
cone `C_B` meets the open rational half-space `x_i>0`.  It therefore contains
a rational point there.  Multiplication by a common denominator gives the
claimed integer rank assignment.  Diagonal projections realize any finite
nonnegative integer rank vector after a sufficiently large stable
amplification, so this is a literal realization of the dimension
presentation, though it need not extend to any additional group relations.

The four operations follow from elementary operations on rational
polyhedral cones and direct sums.  In a branching substitution, each copy
specified by `A` is decomposed according to `D`; counting the resulting
copies gives the product `AD`.  Iteration gives `A^n`.

For a finite group packet, its central isotypic projections are mutually
orthogonal and sum to the packet identity.  Restriction and induction
multiplicities are nonnegative integers; conjugate packet representations
give Murray--von Neumann equivalent isotypic sums.  Hence all such data have
the form `(FDC1)`.  Killing every nontrivial spectral projection of a
finite-order element makes its image the identity, proving the MF-radical
consequence.
