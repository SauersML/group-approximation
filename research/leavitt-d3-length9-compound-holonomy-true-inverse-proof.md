---
rg: 2
id: leavitt-d3-length9-compound-holonomy-true-inverse-proof
kind: route
title: Replay both length-nine unary pivots with symbolic inverses
target: leavitt-d3-length9-compound-holonomy-is-absent
requires:
  - leavitt-d4-true-inverse-screen-audit
artifacts:
  - research/artifacts/search-degree3-omega-four-cycle-true-inverse.py
---

The corrected verifier enumerates the nine length-nine exponent-three sign
paths with orbit valences `(1,1,7)` and every one of the
`9!/(2!2!)=90,720` placements of

```text
(u,u,v,v,r,e,p,a,c),   u=ab,   v=cd.
```

For each layout it tries both unary orbits as the pivot.  It keeps the solved
value of `z=t^3` as a symbolic generator word, substitutes that word and its
true multiplicative inverse into the other unary orbit and the seven-valent
target, and only then reduces in the faithful free-product Bergman chart.  A
hit requires the other unary relator to be exactly the identity and the
cyclically reduced target to be `[c,d]` or its inverse in one coefficient
copy.

The verifier asserts the two-sided inverse identities for the full generator
library, including `u^-1=u` and `v^-1=dc`, before the census.  All nine shards
completed normally and each printed

```text
layouts 90720 pivots 181440
hits 0
```

The exact aggregate is therefore `816,480` layouts and `1,632,960` pivot
substitutions with no hit.  This establishes the target without using the
retired transpose-as-inverse computation.
