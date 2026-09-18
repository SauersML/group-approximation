---
rg: 2
id: irs-surjunctivity-via-rank-corrected-co-sofic-split
kind: route
title: Split invariant random subgroups into co-sofic ones, excluded by rank-corrected counting, and the rest
target: free-group-irs-carry-no-strict-design
requires:
  - co-sofic-free-group-irs-carry-no-strict-design
  - non-co-sofic-free-group-irs-carry-no-strict-design
artifacts:
  - research/artifacts/co-sofic-irs-rank-corrected-counting-2026-09-17.md
  - research/artifacts/irs-surjunctivity-heretic-2026-09-17.md
---

Every IRS of `F_m` is either co-sofic or not.
- The co-sofic ones carry no strict design by `co-sofic-free-group-irs-carry-no-strict-design`
  (ESTABLISHED).
- The rest carry none by `non-co-sofic-free-group-irs-carry-no-strict-design` (OPEN).

This differs from `irs-surjunctivity-via-co-sofic-split` only in its first prerequisite. That route needs
`co-sofic-irs-carry-no-strict-design`, whose stated constant both referee lenses refuted.

The split is exhaustive, so the two prerequisites give the target. Only the second is open. It is the
single remaining hole of `gottschalk-via-irs-surjunctivity`, whose other prerequisite
`atomic-irs-strict-designs-are-nonsurjunctive-quotients` is ESTABLISHED.
