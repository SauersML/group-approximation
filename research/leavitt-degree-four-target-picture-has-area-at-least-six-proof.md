---
rg: 2
id: leavitt-degree-four-target-picture-has-area-at-least-six-proof
kind: route
title: Enumerate the mixed-valence signed ribbons through area four in exact Bergman normal form
target: leavitt-degree-four-target-picture-has-area-at-least-six
requires:
  - degree-four-kl-source-face-retraction
  - leavitt-omega-has-an-explicit-distorted-target
---

## Exact corners

With `z=t^4`, Reidemeister--Schreier rewriting of the revised word gives

```text
R0=r0 e1 a2 c1 b3 d2 p3 z,
R1=r1 e2 a3 c2 z b0 z^(-1)d3 z p0,
R2=r2 e3 z a0 z^(-1)c3 z b1 d0 p1,
R3=r3 z e0 a1 c0 b2 d1 p2.                         (P4.1)
```

Thus `R0,R3` are monovalent and `R1,R2` trivalent in the `z`-arc graph.
The oriented cyclic corner lists are extracted directly from `(P4.1)`; the
opposite orientation is obtained by reversing and inverting the entire cyclic
word.  Every arc pairs a `z` with a `z^(-1)`.

## Complete ribbon census

For each area, the artifact enumerates multisets of the eight
relator/orientation types, every opposite-sign half-edge pairing, and retains
exactly connected spherical ribbon graphs satisfying

```text
V-E+F=2.                                             (P4.2)
```

It labels each complementary region by its cyclic sequence of coefficient
corners.  A coefficient word is reduced in the free product

```text
G_0 * G_1 * G_2 * G_3,
G_i=EL_20(L_(F_2)(1,2)).                             (P4.3)
```

Inside each factor, equality is decided in the faithful standard Leavitt
module after identifying `M_20(L)` with `L` using the standard twenty-leaf
prefix chart.  Ring entries are kept in terminating Bergman normal form as
XOR-sets of monomials `s_u t_v`.  Therefore an identity region in the census
is an exact identity in the full coefficient group.

The exact output, computed through the permitted MSI wrapper, is

```text
area=2 type_multisets=16 planar=40 exact_target_disks=0 one_copy_disks=0
area=3 type_multisets=0  planar=0  exact_target_disks=0 one_copy_disks=0
area=4 type_multisets=100 planar=5954 exact_target_disks=0 one_copy_disks=0
area=5 type_multisets=0  planar=0  exact_target_disks=0 one_copy_disks=0
```

The stronger `one_copy_disks` test accepts an outer region whenever its exact
free-product normal form is one nonidentity block in any of the four factors;
the other regions must all be identities.  Thus its zero count rules out
*every* coefficient-kernel disk through area four.  The target test separately
permits every rotation at a coefficient-letter boundary and both orientations
of `[c_0,d_0]`.  Odd areas have no admissible relator/orientation multiset: the
total positive and negative `z` occurrences cannot balance.  This proves the
claimed lower bound of six.
