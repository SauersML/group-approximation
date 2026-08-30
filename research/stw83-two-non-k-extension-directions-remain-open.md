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
connector.  The canonical Toeplitz-module family still needs a genuinely new
two-colour approximation; the ordinary Toeplitz theorem has ideal `K`, not
`K tensor C(T)`.
