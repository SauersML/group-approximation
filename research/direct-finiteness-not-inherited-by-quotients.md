---
rg: 2
id: direct-finiteness-not-inherited-by-quotients
kind: claim
title: Direct finiteness does not pass to quotients, so the Leavitt surjection proves nothing by itself
distinct_from:
  binary-leavitt-algebra-not-directly-finite: that is the positive defect in the Leavitt algebra; this is the permanence failure that stops the defect from travelling backwards along a surjection, and is a general ring-theoretic fact with a free-algebra witness.
artifacts:
  - research/artifacts/kaplansky-direct-finiteness-audit-2026-08-17.md
---

A directly finite unital ring can have a unital quotient that is not directly
finite.  Witness, complete and elementary: the free associative algebra
`k<X,Y>` is a domain, hence directly finite, and

    B = k<X,Y> / (XY - 1)

is not, since `XY = 1` while `YX != 1`.

**Consequence for this repository.**  Neither
`leavitt-unit-group-algebra-surjects-onto-leavitt` nor its sharpening
`leavitt-corner-idempotent-unital-surjection` shows that `F_2[R^x]` — or the
corner `e F_2[R^x] e` — fails direct finiteness.  Both exhibit the
non-directly-finite ring `R` as a **quotient**, and that is the direction the
property does not travel.  The gap is not a technicality about group algebras;
it is visible already in two free variables.

Any write-up asserting a disproof of Kaplansky's Direct Finiteness Conjecture
from the bare surjection `F_2[R^x] ->> R` contains this gap, and the gap is
fatal.  What has to be supplied instead is
`leavitt-corner-one-sided-lift-exists`, or one of the stronger conditions
recorded there.

**The one direction that does work,** and the reason
`leavitt-corner-kernel-is-jacobson-radical` is stated at all: direct
finiteness *does* descend modulo an ideal contained in the Jacobson radical.
That is the exact hypothesis under which a quotient argument becomes legal,
and it is a hypothesis about `ker(pi_e)`, not a free gift.
