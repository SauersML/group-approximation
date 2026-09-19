---
rg: 2
id: flat-morita-three-cycles-do-not-glue-multipath-marginals
kind: claim
title: Even a flat Morita three-cycle does not force equality of multipath marginals
artifacts:
  - research/finite-packet-flat-morita-cycle-countermodel-proof.md
distinct_from:
  finite-projective-sector-groupoids-have-conjugate-absorbers: that gives an abstract doubled stationary model for finite projective arrows; this gives a literal finite group-corner countermodel built from the two-qutrit multipath projection, with flat holonomy and explicit Steinberg swaps.
  two-qutrit-controlled-bases-give-proper-multipath-marginal: that constructs one exact proper shared projection; this proves that transporting three copies of it by Morita arrows does not identify those copies.
  finite-sheet-transport-networks-are-exactly-matricial: that treats bijections of diagonal sheets; this permits genuinely noncentral rank-three projections and arbitrary algebraic partial isometries between them.
---

Let `F`, `q`, and the proper noncentral multipath projection
`P in q C[F]q` be supplied by
`two-qutrit-controlled-bases-give-proper-multipath-marginal`. Let `L`
be an order-`27` Heisenberg group and let `r` be its degree-three marked
central block. Choose matrix units

```text
(E_ij)_(i,j in F_3) in r C[L] r isomorphic to M_3(C).
```

In the one canonical nonzero corner

```text
Q=q tensor r in C[F times L],                           (MTC1)
```

put, with indices modulo three,

```text
P_i=P tensor E_ii,
v_i=P tensor E_(i+1,i).                                 (MTC2)
```

Then

```text
v_i^*v_i=P_i,              v_i v_i^*=P_(i+1),
v_2 v_1 v_0=P_0.                                       (MTC3)
```

Thus the Morita three-cycle is exactly flat. Its Steinberg swaps already
exist in the same scalar corner:

```text
S_i=v_i+v_i^*+(Q-P_i-P_(i+1)),                          (MTC4)
```

and satisfy

```text
S_i=S_i^*,       S_i^2=Q,       S_i P_i S_i=P_(i+1).   (MTC5)
```

Nevertheless,

```text
P_i P_j=0  for i!=j,             P_i!=P_j.              (MTC6)
```

All three projections have the same canonical trace and the same
`K_0` class. The cycle holonomy is the identity on `P_0`, so neither
trace, `K_0`, nor the flat return distinguishes this countermodel from the
desired gluing.

Consequently a finite presentation whose cross-context clauses say only
that the three multipath marginals are connected by partial-isometry or
Steinberg/Morita arrows, including a flat cycle relation, cannot imply
literal marginal equality. It has the displayed finite-dimensional model
with `Q!=0` and three unequal marginals. This remains true if one records
all adjoint, source, range, swap, and inverse-arrow consequences of
`(MTC3)--(MTC5)`.

The scope is exact. A mixed nontransport relation may still force
`P_0=P_1=P_2`, but that relation is additional information; it is not a
Morita or Steinberg consequence. Since `F times L` is finite, the
countermodel is finite-dimensional, hyperlinear, and detects the selected
corner. Pure three-cycle Morita gluing therefore cannot supply the
finite-dimensional-invisible load-bearing chord.
