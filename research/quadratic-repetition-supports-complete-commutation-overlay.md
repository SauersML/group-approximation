---
rg: 2
id: quadratic-repetition-supports-complete-commutation-overlay
kind: claim
title: Quadratic repetition supports a bounded-degree complete commutation overlay
distinct_from:
  disjoint-private-pairs-expand-the-full-exterior-square: that kills central class-two twists with one random degree-one matching; this uses the available quadratic repetition to impose every logical coordinate-pair commutation and kills all exact contextual quotients.
  repeated-good-ldpc-coordinates-give-private-weyl-sampler: that builds the scalar and dimension sampler and only adds an exterior-square matching; this strengthens its same-basis exact layer.
  bounded-degree-clouds-have-logarithmic-root-gauge-leak: that has one distinguished port in a growing cloud; here every cloud vertex is assigned a logical pair test, so the tested ports have density one.
---

Let a base code have `L=Theta(r)` coordinate reflections and repeat every
coordinate `R>=L` times.  Index `L` of the copies of coordinate `i` by
`j in {1,...,L}`.  For every unordered pair `{i,j}`, add the two-coordinate
joint-PVM/commutation context

```text
[Q_(i,j),Q_(j,i)]=1.                                      (QRC1)
```

Connect the copies of each fixed `i` by any bounded-degree connected equality
graph.  Each copy participates in at most one context `(QRC1)`, degrees remain
bounded, and the total number of variables and contexts is
`Theta(L^2)=Theta(r^2)`.

In every exact representation, equality identifies all `Q_(i,j)` with one
reflection `Q_i`, and `(QRC1)` then gives

```text
[Q_i,Q_j]=1 for every i,j.                                (QRC2)
```

Consequently, after the replicated local parity contexts of the LDPC code
are imposed, every exact local-PVM representation is already the coordinate
marginal of one joint scalar-code PVM on the same Hilbert space.  There is no
genuinely nonnilpotent exact contextual quotient: quadratic repetition can
kill it outright rather than only kill its class-two image.

This does not by itself prove a dimension-independent approximate rounding
theorem.  Expander equality gives average synchronization and `(QRC1)` gives
average all-pairs commutator control, but
`sparse-clifford-cycles-refute-average-commutator-rounding` shows that the
latter implication is false without using the LDPC parity structure.  The
remaining analytic lemma must exploit the code checks jointly with the
complete overlay.

At the word-placement level, `(QRC1)` recreates the complete logical
same-basis pair table.  Although each occurrence has bounded degree, the X
and Z code incidences can close short multi-basin contours.  A finite-
presentation compiler must still establish sign-safe placement rather than
infer it from bounded occurrence.

There is nevertheless a new exact interaction with the parity layer.
`unique-neighbor-ldpc-checks-force-dense-noncommutation` proves that every
noncommutation row is a Tanner stopping set.  For a linear-stopping-distance
code, any exact failure of global commutation therefore occupies a constant
fraction of all logical pairs; the sparse Clifford-cycle obstruction cannot
survive the parity contexts.  This does not control the normalized-HS size
of those nonzero commutators.  The remaining quantitative gate is precisely
`operator-unique-neighbor-cosystolic-rounding`.
