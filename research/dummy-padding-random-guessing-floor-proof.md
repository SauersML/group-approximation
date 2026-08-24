---
rg: 2
id: dummy-padding-random-guessing-floor-proof
kind: route
title: Compare the core-listing decoder against the uniform random assignment
target: dummy-padding-cannot-beat-the-random-guessing-floor
requires: []
---

Two one-line computations that produce the same number.

**The floor.**  Let the constraint on an edge be a 2-to-1 map
`pi : [K] -> [K/2]`.  Assign the two endpoints independent uniform labels
`a in [K]` and `b in [K/2]`.  Conditioning on `a`, the value `pi(a)` is
determined and `b` is uniform over `K/2` possibilities, so

```text
Pr[ pi(a) = b ] = 2/K
```

for every edge, hence in expectation over the edge distribution.  Averaging
gives an assignment of value at least `2/K`, so `OPT(G) >= 2/K`.  This is
`(F1)`, and it holds for every 2-to-1 game with left alphabet `K`, padded or
not.

**The ceiling of the padding argument.**  Now let the true alphabet of size
`K` be hidden inside a larger, randomly matched dummy alphabet, and suppose
the soundness decoder cannot orient the core fibers analytically.  Its safe
list is then all `K` core labels; picking uniformly from the list and then
from the `<= 2` preimages inside the relevant fiber succeeds with
probability `2/K`.  This is `(F2)`.

**Conclusion.**  `(F2) = (F1)`.  A soundness statement derived this way
asserts only `val >= 2/K`, which is true of every such game by inspection,
so it can never contradict a soundness hypothesis and can never produce a
gap.  The failure is not quantitative slack that a better constant would
close; the two quantities are equal for every `K`.

The design consequence recorded on the claim: richness must come from a
list whose size does not depend on the alphabet.  Any decoder whose list is
`Theta(K)` is, for this purpose, no decoder at all.
