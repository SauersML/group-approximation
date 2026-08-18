---
rg: 2
id: balanced-word-high-return-packing-proof
kind: route
title: Inflate high-return sets by Lipschitz tuple balls
target: balanced-word-high-return-packing
requires:
  - balanced-word-haar-small-ball
artifacts:
  - research/artifacts/random-relator-density-repair-2026-08-18.md
---

Word evaluation for a word of length at most `L` is `L`-Lipschitz in the max
bi-invariant normalized-HS metric on generator tuples, by telescoping.  Hence
for every centre `U` with `p_(n,r)(U)>=q`, every `V` in its tuple-ball of radius
`eta/2` satisfies

```text
p_(n,r+L eta/2)(V)>=q.
```

The `eta/2` balls around an `eta`-separated family are disjoint, each having
product Haar measure `v_n(eta/2)^k`.  Their union lies in the enlarged
high-return locus.  Apply the Markov bound from
`balanced-word-haar-small-ball` at radius `r+L eta/2` and divide by the ball
measure.  This is exactly the claimed inequality.
