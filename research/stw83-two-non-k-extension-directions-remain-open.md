---
rg: 2
id: stw83-two-non-k-extension-directions-remain-open
kind: claim
title: Two opposite-direction circle extension cores remain outside known graph color-reuse theorems
artifacts:
  - research/artifacts/stw83-lxxxiii-graph-nuclear-dimension-audit-2026-08-30.md
---

For a finite graph with exactly one nontrivial gauge-invariant ideal, the two
unresolved entries in Evington--Ng--Sims--White, Remark 5.3, are:

1. a stably commutative circle-type ideal with a Kirchberg quotient;
2. a stably commutative circle-type ideal with a stably commutative circle-type
   quotient.

The minimal graph models are two cyclic components joined in the direction which
makes the circle component the ideal; in the first case the quotient component
has a cycle with an exit, and in the second it is another exitless cycle.  No
nuclear-dimension-one proof for either model is recorded here.  The node
`stw83-circle-circle-boundary-index` now computes the nonzero six-term index
of every genuine two-cycle model with an acyclic connector.  Thus the second
direction is no longer structurally opaque, but the computation is an
obstruction rather than a dimension-one approximation.

Moreover, `stw83-circle-connector-canonical-full-corner` shows that every
finite acyclic connector in the second direction is full-corner equivalent to
the two-vertex graph with two loops and `N` parallel connecting edges.  Thus
the remaining circle-by-circle problem is the explicit canonical family

```text
C*(S^N tensor 1, K tensor C(T)),       N>=1,
```

not the combinatorial complexity of the connector.

The three-colour theorem
`stw83-canonical-circle-toeplitz-dimension-two-bound` now shows that every
member of this canonical family has nuclear dimension at most two (and at
least one).  Thus the unresolved question is exactly whether its third colour
can be reused, rather than whether the family has some finite bound.

## Attempts

The Evington--Ng--Sims--White two-color theorem has the opposite orientation: a
stable Kirchberg ideal and stably commutative quotient.  Passing to the opposite
extension is not a formal operation on Busby invariants and does not preserve its
essential absorption input.  The generic extension inequality only gives an
upper bound larger than one.  The hereditary circle-crown theorem recorded here
deliberately keeps the Kirchberg algebra on the ideal side and therefore does not
decide either minimal model.  A solution needs a new color-reuse theorem for a
stable circle ideal, or an explicit graph approximation of these two models.  In
the circle-by-circle case it cannot be a split or quasidiagonal-extension
argument: the graph defect makes the index map nonzero for every nontrivial
connector.  A coefficient-valued Brake--Winter adaptation gives three colours:
the transition band stays scalar, but the inner corner is
`M_r(C(T))` and needs two coefficient colours.  Only one inner colour is
automatically orthogonal to the transition colour.  The canonical family
still needs a genuinely new recolouring of the other inner piece to obtain a
two-colour approximation.  The reduction
`stw83-plateau-buffer-recolouring-hinge` makes this precise: a finite-set
adaptive colour supported in a deep plateau would suffice, but a uniform
block-diagonal approximation of the whole matrix-over-circle corner is
impossible because it would make a complementary circle corner
zero-dimensional.  The remaining escape is narrower still.  By
`stw83-circle-unitary-order-zero-plus-constants-gap`, there is a uniform
positive distance between the circle generator and the sum of a constant
with one finite-dimensional order-zero range.  Therefore, even if the second
inner colour has arbitrary off-diagonal entries crossing a rank-one plateau,
it cannot leave its plateau diagonal scalar: on the finite set containing the
corner circle generator, the first plateau colour plus that scalar diagonal
has a fixed error floor.  Any successful adaptive colour must transport
coefficient variation as well as matrix entries across the support split.

The cone firewall
`stw83-commuting-cone-two-colour-firewall` also rules out a coupled scalar
functional-calculus repair.  If the coefficient phase is carried throughout
a continuous Toeplitz cutoff, their joint spectrum is
`Cone(T)=D^2`; two commuting support labels would give arbitrarily fine
two-coloured covers of the disk and force its covering dimension to be at
most one.  Thus the viable buffer escape must first extinguish coefficient
variation, and its subsequent support transport must be stage-dependent and
genuinely matrix-valued.  This restriction does not itself construct the
missing maps or decide the nuclear dimension.
