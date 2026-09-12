---
rg: 2
id: smooth-pairing-designs-of-size-m-to-the-n-exist
kind: claim
title: Smooth t-wise uniform pairing distributions with support about m^n n^O(t) exist
distinct_from:
  pullback-smoothness-needs-exponentially-many-pairings: that is the lower bound, at least about m^n pairings for any smooth family; this is the matching upper bound, an explicit composition achieving t-wise uniformity and smoothness with support m^n n^O(t).
artifacts:
  - research/artifacts/unique-games-smooth-design-richness-2026-09-11.md
---

**ESTABLISHED.** Fix `t >= 1`, `m >= 2` and `K >= 1`. Let `C = C(K,m)` be the
density constant BKM prove for all pairings (ECCC TR19-141, Lemma 4.2). For all
sufficiently large `n` there is a probability distribution with rational weights
on perfect pairings of `[2n]`. It is `t`-wise uniform and `(K,m,2C)`-smooth,
and its support has at most

```text
((2n)_(2t)^2 + 1) * ceil(3 m^n (2n ln m + 1) / C)
```

pairings. That is `m^n n^(O(t))`, which is `o((2n-1)!!)`.

So the smooth-design hypothesis of `smooth-design-rich-2to1-hardness` is met by
families exponentially smaller than the family of all pairings. By
`pullback-smoothness-needs-exponentially-many-pairings`, the factor `m^n` cannot
be removed.
