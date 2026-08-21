---
rg: 2
id: iwahori-square-root-odd-mode-is-amalgam-bending
kind: claim
title: The square-root odd mode is exactly the bending coordinate of the Iwahori amalgam
distinct_from:
  positive-density-modular-square-root-mixing-exclusion: that asks matrix ultraproducts to exclude macroscopic bending; this proves every defining modular and edge relation is exactly invariant under the bending operation.
  hnn-over-codense-kazhdan-subgroup-not-hyperlinear: that uses stability and a commutant gap to collapse an HNN stable letter; this identifies the unresolved Iwahori mode before any such matrix-only collapse.
---

Let

```text
A=C_+ *_(B_+=B_-) C_- = SL_2(Z[1/2])                 (ABN1)
```

and let `(pi_+,pi_-)` be any exact compatible unitary representation in an
arbitrary von Neumann algebra.  If `V` commutes with `pi_+(C_+)`, define

```text
pi_-^V(c)=V pi_-(c) V^*.                             (ABN2)
```

Then `(pi_+,pi_-^V)` is another exact compatible representation of `A`.
Indeed `V` commutes with the common edge image, so conjugating the second
vertex does not change its restriction to `B_-`.

In simultaneous square-root coordinates

```text
X=pi_-(u),                 Y=pi_+(l),                 (ABN3)
```

the bent pair is

```text
X^V=VXV^*,                 Y^V=Y.                    (ABN4)
```

Because `X^2=pi_+(u)` and `Y^2=pi_-(l)` lie in the common edge image,

```text
(X^V)^2=X^2,               VY^2V^*=Y^2,              (ABN5)
Z((X^V)^2,Y)=Z(X^V,Y^2)=Z(X^2,Y).                    (ABN6)
```

Thus both modular presentations and the matched central word survive
exactly for every bend.  For an involution `V=2P-1`, the odd mode
`(V-XVX^*)/2` is precisely the nontrivial bending coordinate.

Consequently no algebraic manipulation of the two modular relation sets can
bound this odd mode: all of those relations have zero defect along the whole
bending family.  Finite-dimensional co-density kills bending only because
the two vertex images have the same commutant in every exact finite matrix
representation.  The open problem is to robustify that fact for the relevant
matrix coordinates, not to discover another group relator.
