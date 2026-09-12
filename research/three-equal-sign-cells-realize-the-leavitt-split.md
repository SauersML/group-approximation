---
rg: 2
id: three-equal-sign-cells-realize-the-leavitt-split
kind: route
title: Solve the joint sign dimensions and construct the split inside the fixed parent involution
target: leavitt-rho5-split-multiplicities-are-feasible
requires: []
artifacts:
  - research/artifacts/leavitt-rho5-split-multiplicity-is-not-an-obstruction-2026-09-08.md
---

If involutions `U,V` have involutive product `D`, then `UV=VU`.
Write the dimensions of the joint sign spaces with signs `(-,+)`,
`(+,-)`, `(-,-)` as `x,y,z`. Equality of the three negative
dimensions gives `x+z=y+z=x+y=q`, hence `x=y=z=q/2`.
The remaining dimension is `n-3q/2`, proving necessity.

Conversely, split the negative space of the supplied `D` into two
spaces of dimension `q/2`, and choose a space of dimension `q/2`
inside its positive space. Assign these spaces the three nontrivial
joint signs, with the remaining positive space assigned `(+,+)`.
This constructs commuting `U,V` with product exactly `D`; their
negative dimensions are `q`, so each is unitarily conjugate to `A`.

In the frozen S3 anchor, `A` exchanges the two nonreal eigenspaces
of `C`, contributing exactly `m` negative eigenvalues. Its action
on the `m`-dimensional fixed space contributes `b` more. Therefore
`q=m+b<=2n/3`. The literal compiler identity makes `A` conjugate
to the commutator `d`, so `det A=1` and `q` is even.

The artifact records the two actual rho5 conjugator words and explains
why this construction does not retain them. The conclusion is precisely
the feasibility of the multiplicity data, without a packet realization.
