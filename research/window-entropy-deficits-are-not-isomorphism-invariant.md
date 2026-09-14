---
rg: 2
id: window-entropy-deficits-are-not-isomorphism-invariant
kind: claim
title: Over a nonamenable group the window entropy of a generating partition of a Bernoulli shift depends on the partition
invalidates: [gottschalk-via-window-entropy-deficit]
artifacts:
  - research/artifacts/gottschalk-rokhlin-entropy-route-2026-09-12.md
---

Let `G` be nonamenable, with a finite `S` containing `1` and `c > 0` such that
`|F S| >= (1 + c)|F|` for every nonempty finite `F`. On the uniform Bernoulli
shift `A^G`, the coordinate partition `beta` and `gamma = join_(s in S) s.beta` are
both generating, and

    inf_F H(beta^F)/|F| = log |A|,        inf_F H(gamma^F)/|F| >= (1 + c) log |A|.

So per-site window entropy is not an isomorphism invariant. Over an amenable
group, the Folner limit of the same quantity is the Kolmogorov--Sinai entropy of
any generating partition.

**ESTABLISHED 2026-09-12** by
[[window-entropy-deficits-are-not-isomorphism-invariant-proof]].
