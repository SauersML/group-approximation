---
rg: 2
id: leavitt-degree3-direct-pivot-true-inverse-proof
kind: route
title: Replay every degree-three direct pivot with symbolic inverses
target: leavitt-degree3-direct-pivot-screen-is-empty
requires:
  - leavitt-d4-true-inverse-screen-audit
artifacts:
  - research/artifacts/search-leavitt-degree3-direct-pivot-true-inverse.py
---

The corrected verifier enumerates the eleven length-eleven exponent-three
sign paths whose Reidemeister--Schreier stable-letter valences are `(1,1,9)`.
For every path it enumerates all

```text
11!/4! = 1,663,200
```

placements of the full packet `(r,e,a,c,1,b,d,p,1,1,1)` and tries each of
the two unary orbits as the pivot.  The pivot relation is cyclically based at
its unique occurrence of `z=t^3`, solved literally for `z`, and substituted
at all nine stable-letter occurrences of the remaining orbit.

Inverses are never obtained by transposing a Bergman chart.  The solved value
of `z` remains a symbolic generator word; its inverse is formed by reversing
that word and negating the exponents.  Only then does the faithful chart
evaluate the word through the explicit `UNITS` and `INVERSES` tables.  Before
enumeration the verifier asserts both `x*x^-1=1` and `x^-1*x=1` for every
named generator.  Clearing the exact reducer's memo table after every 10,000
layouts is only a memory bound and does not alter the enumeration or reducer.

All eleven shards completed normally.  Each owned one topology and printed

```text
layouts 1663200 pivots 3326400
hits 0
```

Thus the exhaustive corrected census contains

```text
18,295,200 coefficient layouts,
36,590,400 unary-pivot substitutions,
```

with no reduction to `[c,d]` or its inverse in any coefficient copy.  This is
exactly the finite statement of the target claim and replaces the invalidated
transpose-as-inverse route without erasing that audit history.
