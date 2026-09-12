---
rg: 2
id: thin-quasiregular-profile-promotes-to-liftable-charts
kind: claim
title: Every proper intermediate coset action above the thin SL3 subgroup is sofic
root: true
distinct_from:
  thin-selected-leak-amplifies-to-codense-quasiregular-profile: that extracts a proper intermediate stabilizer from a selected leak; this asks whether every such intermediate coset action is sofic.
  stable-finite-actions-blocks-codense-kazhdan-coset-soficity: that conditionally rules out such a sofic action under stability in finite actions; this is the unconditional positive assertion for the explicit thin pair.
---

Let `A=SL_3(Z)` and let `C=<a,b>` be the explicit proper profinitely
dense subgroup. Assert that, for every subgroup `H`,

```text
C<=H<A  implies  A curvearrowright A/H is sofic.       (QPC*)
```

The former formulation additionally assumed normalized-HS asymptotic maps
`beta_n` and unit vectors `xi_n` with
`<beta_n(g)xi_n,xi_n> -> 1_H(g)`. By
[[subgroup-indicators-are-diluted-hs-coefficients]], that hypothesis holds
for every subgroup of every group, uniformly in the multiplication
variables. Consequently the former formulation is logically equivalent to
`(QPC*)`; it was not a unitary-to-permutation promotion hypothesis.

By [[gkp-sofic-action-is-liftable-hamming-chart-family]], `(QPC*)` asks
for a positive-density common-carrier family of injective equivariant
charts. A single vector living on two of `d_n->infinity` coordinates
supplies none of that datum.

## Attempts

- The coefficient condition cannot distinguish any subgroup or action: the
  two-dimensional membership test plus trivial spectators realizes it.
- Tensor powers and global normalized-HS exactification still do not create
  a positive-density chart sector; see
  [[tensor-root-profile-adds-no-chart-coherence]] and
  [[spectator-dilution-hides-root-profile-from-hs-correction]].
- [[stable-finite-actions-blocks-codense-kazhdan-coset-soficity]] gives a
  conditional negative result, but stability in finite actions for this
  actor is not currently available.

**Status: OPEN.**
