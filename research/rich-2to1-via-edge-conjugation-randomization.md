---
rg: 2
id: rich-2to1-via-edge-conjugation-randomization
kind: route
title: Dead -- manufacture richness by conjugating each 2-to-1 constraint
target: rich-2to1-games-conjecture
requires: []
---

**Dead.**  The attack: take an instance produced by the proved 2-to-1
hardness machinery, whose fibers are the structured affine pairs
`{x, x+b}`, and randomize it by replacing each constraint `pi` with
`pi^sigma = pi . sigma^{-1}` for an independently drawn permutation
`sigma` of the left alphabet.  The instance then looks matched at random
rather than affinely, which is what richness seems to ask for.

It is killed by `edge-conjugation-of-2to1-constraints-is-pure-gauge`.
Keeping dictator completeness forces the long-code function to transform as
`F^sigma(X) = F(sigma^{-1} . X)`, and then

```text
(F^sigma)|_{pi^sigma} = F|_pi
```

on the nose.  The folded restriction -- the only thing a dictatorship test
reads -- is literally unchanged, so the randomization is a gauge
transformation and the new instance is analytically the old one.

Scope of the kill, stated because the identity is per-edge: what is closed
is the local move of conjugating constraints one at a time.  A scheme whose
content lives in the *joint* law of the `sigma`'s across edges sharing a
vertex is not addressed by the identity, and would need its own node.
