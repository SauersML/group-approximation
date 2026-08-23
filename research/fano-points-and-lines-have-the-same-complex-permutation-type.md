---
rg: 2
id: fano-points-and-lines-have-the-same-complex-permutation-type
kind: claim
title: Fano symmetry gives the honest point orbit and the ghost line orbit the same complex type
distinct_from:
  rstar-odd-character-ghost-fiber-is-eight-sectors: that identifies the seven line characters as bad long-code sectors; this proves that their Fano-group multiplicity signature is identical to the seven honest singleton sectors.
  finite-selector-gadget-induction-barrier: that guarantees occurrence of every compatible selector character in some representation of a finite overgroup; this is the sharper character equality for the two relevant seven-element orbits.
  low-dimensional-hyperoctahedral-packet-groupifies-any-predicate: that separates subset weights using the full symmetric group and a dimension threshold; this shows why the smaller geometry-preserving Fano group cannot separate points from lines by complex type.
---

Let

```text
G=GL(3,2),
P=F_2^3 minus {0},
L={two-dimensional linear subspaces of F_2^3}.          (FPL1)
```

Then the two seven-dimensional complex permutation representations

```text
C[P]  and  C[L]                                        (FPL2)
```

are isomorphic.  Their permutation characters agree on every `A in G`.
Indeed, the number of fixed points is

```text
|Fix_P(A)|=2^(dim ker(A-I))-1.                         (FPL3)
```

Lines are kernels of nonzero covectors, so fixed lines are fixed nonzero
vectors for the contragredient action `A^(-T)`.  Since

```text
ker(A^(-T)-I)=ker(A^T-I)
```

and `A^T-I` has the same rank as `A-I`, the right side of `(FPL3)` also
counts `Fix_L(A)`.  Equality of complex characters proves `(FPL2)`.

Both permutation modules decompose as the trivial representation plus the
same six-dimensional augmentation representation.  Under the long-code
mask group, `P` indexes the honest weight-one character orbit, while `L`
indexes the seven weight-three Fano-line characters which decode to the
ghost by `rstar-odd-character-ghost-fiber-is-eight-sectors`.

Consequently a finite packet return which forgets the diagonal mask action
and records only complex `G`-type, dimension, character, or multiplicity
cannot distinguish the honest singleton sector from the bad line sector.
Adding Fano symmetry alone therefore does not eliminate the load-bearing
ghost orbit.  A successful return must retain extra incidence data from the
normal mask subgroup, use a genuinely characteristic-two module invariant,
or consume cross-context information.

