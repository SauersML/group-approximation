---
rg: 2
id: perfectness-bounded-solvability-proof
kind: route
title: Universal quantifiers over iterated commutator words, and the switch with the seeds Z and F_2
target: perfectness-and-bounded-solvability-are-pi2-complete
requires:
  - arbitrary-forbidden-seed-hereditary-property-switch
---

Membership: each of the three conditions is `forall w, phi(w)` with
`phi(w)` an r.e. word-problem instance about a fixed word built from `w`
(a commutator, an iterated commutator of weight `c + 1`, or an iterated
derived word of depth `d`), so each is `Pi^0_2`.

Hardness: the parametric switch has the two isomorphism types `1` and the
seed.  Perfectness holds for `1` and fails for `Z`; nilpotency of class
`<= c` and derived length `<= d` hold for `1` and fail for `F_2`.  All
three conditions are isomorphism invariant, so
`c |-> switchCode(seed, c)` reduces `INF` to each, and `INF` is
`Pi^0_2`-complete.
