---
rg: 2
id: commuting-double-commutator-overlap-proof
kind: route
title: Bound anticommuting commutator support by marked support
target: commuting-double-commutator-has-direct-mark-overlap
requires: []
---

Work first on `QH`.  All three involutions `A,B,z` reduce this space.  Put

```text
C=[A,z].                                                (DCP1)
```

The identity `[C,B]=r=-1` on `QH` is equivalent to

```text
C B C^*=-B.                                             (DCP2)
```

Let `E` be the kernel projection of `C-1` inside `Q`.  If
`tau(E)>tau(Q)/2`, then the projection meet `E meet B E B` is nonzero.  A
nonzero vector in that meet and its `B`-translate are both fixed by `C`,
contradicting `(DCP2)`.  Hence

```text
tau(supp_Q(C-1)) >= tau(Q)/2.                           (DCP3)
```

On the other hand

```text
C-1=(A z A-z)z.                                        (DCP4)
```

Inside `Q`, the two involutions `A z A` and `z` have nontrivial spectral
projections `APA` and `P`, each of trace `tau(QP)`.  The support of their
difference is subequivalent to the join of those two projections, so

```text
tau(supp_Q(C-1)) <= 2tau(QP).                           (DCP5)
```

Combining `(DCP3)` and `(DCP5)` proves `(DCO2)`.

For the robust normalized-HS statement, first round the four torsion words
to involutions in `2`-norm and put `Q=(1-r)/2`.  Approximate commutation with
`r` means that the off-diagonal `Q`-blocks of `A,B,z` have `2`-norm `o(1)`.
Replace each by its `Q`-block diagonal part and take the polar sign in each
block.  The resulting exact involutions commute with `Q` and differ from the
originals by `o(1)` in `2`-norm.  This is a local block correction, not an
upgrade from Hilbert--Schmidt norm to operator norm.

For the corrected operators put

```text
C=[A,z],             W=[C,B],             e=||W-r||_2.
```

Let `E=ker(C-1) meet Q`.  On `E meet B E B`, both a vector and its
`B`-translate are fixed by `C`, so `W=1`, whereas `r=-1`.  Therefore

```text
e^2 >= 4 tau(E meet B E B)
    >= 4 max(2tau(E)-tau(Q),0).                       (DCP6)
```

It follows that

```text
tau(supp_Q(C-1))=tau(Q)-tau(E)
 >= tau(Q)/2-e^2/8.                                  (DCP7)
```

The support upper bound `(DCP5)` is still exact for the corrected block
involutions.  Combining it with `(DCP7)` gives

```text
tau(PQ) >= tau(Q)/4-e^2/16.                          (DCP8)
```

Undoing the `o(1)` block and polar-sign corrections proves `(DCO3)`.  This
argument uses only normalized Hilbert--Schmidt control and all three stated
approximate centrality relations.
