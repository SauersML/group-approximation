---
rg: 2
id: leavitt-invariant-random-subgroups-are-trivial-mixtures
kind: claim
title: Every invariant random subgroup of the binary Leavitt unit group is a mixture of the two trivial laws
distinct_from:
  leavitt-root-fixed-projections-equal-the-global-fixed-projection: That identifies the trivial weight of every character; this recovers the whole subgroup-valued probability law using return probabilities and the absence of proper finite-index subgroups.
  zero-one-irs-character-is-normal-dirac: That treats characters whose coefficients are already zero or one; this permits every intermediate trivial weight and proves that the underlying IRS is the corresponding mixture of two point masses.
artifacts:
  - research/artifacts/leavitt-irs-rigidity-from-character-simplex-2026-09-08.md
---

Let `H=L_(F_2)(1,2)^x`. Every invariant random subgroup `mu` of `H`
has the form

```text
mu = (1-b) delta_({1}) + b delta_H,       0<=b<=1.
```

The coefficient is exactly `b=mu({H})`. In particular the only
ergodic invariant random subgroups are the point masses at `{1}`
and at `H`.

Consequently, for every measurable probability-preserving action
`H` on a standard probability space, almost every point outside
the global fixed set has trivial stabilizer. Equivalently, the
space is the disjoint union, up to a null set, of its global fixed
set and its free part. For every `g!=1`, the fixed set of `g`
agrees with the global fixed set modulo null sets.

The artifact proves the more general implication for any countably
infinite group with no proper finite-index subgroups whose full
character simplex consists of the trivial/regular mixtures. It
does not assume that the character of an IRS determines that IRS
in general. A lazy random-walk limit identifies the trivial
character weight with the mass at the whole group, after which
countably many membership events determine the remaining support.

This is a written structural theorem about exact actions. It
does not settle hyperlinearity or construct a nonembeddable trace.
