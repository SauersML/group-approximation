---
rg: 2
id: irs-surjunctivity-via-co-sofic-split
kind: route
title: Split invariant random subgroups into co-sofic ones, where counting excludes strict designs, and the rest
target: free-group-irs-carry-no-strict-design
requires:
  - co-sofic-irs-carry-no-strict-design
  - non-co-sofic-free-group-irs-carry-no-strict-design
artifacts:
  - research/artifacts/irs-surjunctivity-heretic-2026-09-17.md
---

Every IRS of `F_r` is either co-sofic or not.
- The co-sofic ones carry no strict design by `co-sofic-irs-carry-no-strict-design`.
- The rest carry none by `non-co-sofic-free-group-irs-carry-no-strict-design`.

The split is exhaustive, so the two prerequisites together give the target. Each fails independently of
the other: the first is proved, and the second is open.
