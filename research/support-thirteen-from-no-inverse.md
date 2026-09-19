---
rg: 2
id: support-thirteen-from-no-inverse
kind: route
title: Vacuously — there is no completing factor to measure
target: leavitt-rank-three-lift-inverse-support-thirteen
requires: [leavitt-rank-three-lift-has-no-one-sided-inverse]
artifacts:
  - research/artifacts/leavitt-rank-three-no-inverse-2026-08-18.md
---

## Why sufficient

The target says: if `B in F_2[R^x]` satisfies `t~ B = 1` then
`|supp B| >= 13`.  The prerequisite says no such `B` exists.  The implication
is vacuous and the target holds.

## Why the route is worth adding rather than letting the old one stand alone

The pre-existing route `leavitt-support-thirteen-from-ulie-ranks` derives the
same statement from `dykema-heister-juschenko-bounded-rank-direct-finiteness`,
whose rank range `(3,n)`, `n <= 11`, rests on a refereed **computer
enumeration** that was never replayed here — the node says so, and says the
bound is its only consumer.  This route reaches the same conclusion from a
three-line coset argument and Nagao's theorem, with no machine computation
anywhere in it.  So adding it removes an imported computation from the
derivation of an established claim, and simultaneously records in the graph
that the claim is now superseded: the honest reading of the target is no
longer "the smallest completion is large" but "there is no completion".

Nothing is invalidated.  The ULIE route remains valid and remains the source
of the parity remark (`eps(B) = 1`, so any hypothetical `B` has odd support),
which this route does not reprove because it has no `B` to speak about.
