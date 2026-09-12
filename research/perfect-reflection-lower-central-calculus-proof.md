---
rg: 2
id: perfect-reflection-lower-central-calculus-proof
kind: route
title: Pull commutator series through a quotient with perfect kernel
target: perfect-mf-reflection-over-residually-p-actor
requires:
  - amenable-implies-operator-mf
  - universal-mf-quotient
---

Finite `p`-groups are MF, so `(PRP2)` makes every such map from `K` factor
through `T`.  Residual `p`-finiteness of `T` therefore identifies `B` with
the finite-`p` residual.  The same argument applies to all finite groups.
Nilpotent and solvable groups are amenable and hence MF, while a residually
`p` group is residually nilpotent and residually solvable.  Intersecting the
corresponding kernels proves every equality in `(PRP3)`.  Compact targets
also factor through `T` by `(PRP2)`, and finite `p`-quotients already separate
the actor, so the Bohr kernel is `B` as well.  The universal properties of
the five completions give the asserted canonical isomorphisms.

It remains to prove the intrinsic formulas.  Since `B=[B,B]`, one has

```text
B<=derived_j(K),             B<=lowerCentral_j(K)
```

for every finite stage `j`, by induction.  The quotient map carries each
series of `K` onto the corresponding series of `T`.  Conversely, if the
image of `x` belongs to the next derived or lower-central term of `T`, write
that image as a product of the defining commutators and lift the entries to
the preceding terms of `K`.  The lifted product differs from `x` by an
element of `B`, which already lies in the required next term.  This proves
both equalities in `(PRP5)` by induction.

The lower central series of a residually nilpotent group and the derived
series of a residually solvable group have trivial intersection.  Taking
intersections in `(PRP5)` therefore gives `(PRP4)`.
