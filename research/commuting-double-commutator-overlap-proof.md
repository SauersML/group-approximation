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

For the robust statement in norm microstates, first round the four torsion
words to involutions.  Their operator-norm commutator defects tend to zero.
Block-diagonalize `A,B,z` across the spectral projection `Q` and take the
polar signs of the two diagonal blocks; the resulting commuting-with-`Q`
involutions differ by `o(1)` in operator norm.  On `QH`, `(DCP2)` then holds
within operator norm `o(1)`.  Once that error is below `2`, the same
intersection argument forces `rank(C-1)>=rank(Q)/2`: a vector fixed by `C`
together with its `B`-translate would otherwise see error exactly `2`.
The support bound `(DCP5)` is unchanged for the rounded block involutions,
and their negative projections differ from the original ones by `o(1)` in
operator norm.  Dividing by matrix dimension yields `(DCO3)`.
