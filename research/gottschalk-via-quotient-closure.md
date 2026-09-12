---
rg: 2
id: gottschalk-via-quotient-closure
kind: route
title: Every group is a quotient of a surjunctive free group
target: gottschalk-surjunctivity-conjecture
requires:
  - surjunctivity-passes-to-quotients
  - residually-finite-groups-are-surjunctive
artifacts:
  - research/artifacts/surjunctivity-closure-properties-2026-09-12.md
---

**The argument.**
1. Free groups are residually finite, so they are surjunctive.
2. Every group `K` is a quotient of a free group.
3. Quotient closure makes `K` surjunctive.

Surjunctivity is a local property, so free groups of any rank suffice.

**Cycle.** With `quotient-closure-from-gottschalk`, this is a deliberate equivalence cycle through the
goal. The route is a reduction marker, not a plan: it records that quotient closure is exactly as hard as
the conjecture.
