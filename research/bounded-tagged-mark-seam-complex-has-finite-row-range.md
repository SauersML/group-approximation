---
rg: 2
id: bounded-tagged-mark-seam-complex-has-finite-row-range
kind: claim
title: Every bounded pairwise mark-seam complex has only finitely many tagged output rows
distinct_from:
  tagged-sheared-diagonal-one-chart-hits-mark-area: that treats one outer-conjugacy Steinberg cell; this treats every uniformly bounded connected complex of two, three, or finitely many chart cells whose conjugated mark seams cancel pairwise.
  finite-prototype-column-codes-force-coset-collisions: that bounds graph chromatic number from normalized neighbour-row fibres around finite-order columns; this works inside one proposed van Kampen diagram and bounds the chart conjugators through their common mark-return seams.
artifacts:
  - research/binary-leavitt-bounded-area-chromatic-code.md
---

**ESTABLISHED FINITE-CHART SEAM NO-GO.**  Let `Gamma=<S|R>` be finitely
presented and let `z` be a word representing a nontrivial finite-order
element.  Fix a finite palette of chart-row words `p_1,...,p_m`.

Consider a family of proposed diagrams with at most `K` chart instances.
After absorbing one fixed normalization word for each prototype type, write
the distinguished mark occurrence in instance `v` as

```text
Z_v=g_v z g_v^(-1).                                      (MSC1)
```

Assume the internal mark seams form a connected graph together with one
outer vertex `o`, where `Z_o=z`, and every seam `vw` has

```text
Area_R(Z_v Z_w^(-1))<=B.                                 (MSC2)
```

Suppose the output row is assembled by a word of length at most `K` in the
chart-carried rows

```text
g_v p_a g_v^(-1)                                         (MSC3)
```

and their inverses, using one of finitely many fixed assembly schemas.
Then only finitely many group elements can occur as output rows, independently
of the diagrams in the family.

Consequently the tagged sheared rows

```text
p_(ij)=c_ic_j=x_12(A_i+A_j)                              (MSC4)
```

cannot be realized by any uniform two-chart, three-chart, or bounded
finite-chart complex of this form: they are pairwise distinct as `j` varies
with `i` fixed.  In particular, splitting the one-chart Gram prototype into
several conjugated marked Steinberg cells does not evade the obstruction
when their conjugated `z` seams merely cancel pairwise before leaving the one
literal `z` on the outer boundary.

The statement is a bounded mark-cocycle obstruction.  Pairwise seam
identifications make the chart gauges a connected `C_Gamma(z)`-valued
cocycle, and the outer literal mark supplies a basepoint.  Bounded diameter
of the seam graph turns all gauges into one bounded commutator-area sublevel,
which is finite modulo `<z>`.

This does not cover a new prototype cell whose boundary imposes a genuinely
non-pairwise relation among three or more conjugated marks, a diagram in
which the number of chart cells grows with the addresses, or a direct
Steinberg filling having no distinguished mark seam decomposition.  One of
those features is necessary for the surviving tagged-table route.

No Property `(T)`, Kazhdan input, matrix approximation, trace, or literature
theorem is used.

DERIVATION
bounded-tagged-mark-seam-finiteness-proof
