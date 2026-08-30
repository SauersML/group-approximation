---
rg: 2
id: leavitt-degree4-five-corner-full-packet-true-inverse-proof
kind: route
title: Replay both degree-four five-corner screens with symbolic inverses
target: leavitt-degree4-five-corner-full-packet-is-absent
requires:
  - leavitt-d4-true-inverse-screen-audit
  - leavitt-degree4-strict-omega-four-cycle-no-go
  - degree4-cyclic-orbit-valence-parity
artifacts:
  - research/artifacts/search-degree4-five-corner-full-packet-true-inverse.py
---

The corrected verifier treats the two displayed length-twelve sign classes as
independent shards and confirms their orbit valences `(1,1,5,5)`.  On each it
enumerates all

```text
12!/5! = 3,991,680
```

placements of `(r,e,a,c,b,d,p,1,1,1,1,1)` and tries both unary orbits as the
pivot.  It cyclically bases the pivot relation at its unique occurrence of
`z=t^4`, solves literally for `z`, and substitutes into the other unary
relation.

The value of `z` and its inverse remain symbolic generator words until the
faithful Bergman chart evaluates them through its explicit `UNITS` and
`INVERSES` tables.  The verifier first asserts both `x*x^-1=1` and
`x^-1*x=1` for every named generator.  It never obtains an inverse by
transposing a chart.  Periodic memo-table clearing only bounds memory and
does not change the exact reducer.

Both shards completed normally and each printed

```text
layouts 3991680 pivots 7983360
compatible_pivots 0
hits 0
```

The corrected aggregate is therefore `7,983,360` coefficient layouts and
`15,966,720` unary-pivot substitutions.  Since not one pivot makes the other
unary relation trivial, no layout reaches the ordered five-corner target
stage.  This proves the target claim and replaces the invalidated
transpose-as-inverse certificate while preserving that failed route as audit
history.
