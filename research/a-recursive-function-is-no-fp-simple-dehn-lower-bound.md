---
rg: 2
id: a-recursive-function-is-no-fp-simple-dehn-lower-bound
kind: claim
title: Some recursive function is a lower bound for the Dehn function of no finitely presented simple group
distinct_from:
  fp-simple-dehn-functions-realize-every-recursive-lower-bound: that is the affirmative answer to Zaremsky Problem 1.16 under its strong reading; this is its negation, the negative answer.
---

**OPEN.** There is a recursive `f: N -> N` such that `f ⋠ delta_S` for every
finitely presented simple group `S`.

This is the negative answer to
`zaremsky-1-16-fp-simple-groups-with-large-dehn-functions` under its adopted
reading. It does not follow from Zaremsky's examples, which only show that
`f(n) = 2^n` is not such a function.

A uniform recursive upper bound on the Dehn functions of finitely presented simple
groups would imply this claim. Such a bound is expected to fail: it contradicts
`fp-simple-dehn-functions-have-no-recursive-upper-bound`, which follows from
`boone-higman-conjecture` through `complex-fp-simple-groups-from-boone-higman`
and `fp-simple-unbounded-dehn-via-complex-word-problem`.

## Attempts

1. **Uniform upper bounds.** None is known, and polynomial bounds already fail
   (`fp-simple-group-with-at-least-exponential-dehn-function`). A uniform recursive
   bound would refute the Boone–Higman conjecture, as above. *No attack recorded;
   this side is expected false.*
2. **Oscillation.** This claim could hold while the weak reading holds, if every
   finitely presented simple group had a Dehn function with long plateaus. No
   mechanism forcing plateaus in all finitely presented simple groups is known.
   *Not attempted.*
