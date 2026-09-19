---
rg: 2
id: agent-aggregate-escape-global-schur-square-proof
kind: route
title: Cancel the two flip implementers and read the remaining central commutator
target: agent-aggregate-escape-global-schur-square-is-affine-wall
requires:
  - schur-flip-square-exposes-payload-root-word
  - controlled-central-phase-finite-group-barrier
---

Put `r=PQ` and `a=uv`.  The flip relations give

```text
a r a^(-1)=(KP)(KQ)=PQ=r,
```

because `K` is central and `K^2=1`.  Since `u,v` are commuting involutions,
`a^2=1`, and hence

```text
d^2=(ra)(ra)=r^2=(PQ)^2.
```

For involutions `P,Q`, `(PQ)^2` is `[P,Q]` up to replacing the commutator by
its inverse.  The distinction is immaterial because the relevant central
packet commutators are involutions.

In a class-two Schur packet, the commutator pairing descends to a bilinear
map from the elementary-abelian generator quotient to the central
elementary-abelian subgroup.  Thus `[P,Q]` is one fixed product of the
central selector generators and `K`.  Evaluation at a selector character is
an affine Boolean functional.  The relation `[P,Q]=1` retains one affine
wall and deletes its complementary affine wall.

The corner computation from `schur-flip-square-exposes-payload-root-word`
says only that the chosen atom lies in the deleted wall.  It does not say
that the deleted wall consists of that atom.  This proves `(GS2)--(GS5)` and
the completeness boundary.

