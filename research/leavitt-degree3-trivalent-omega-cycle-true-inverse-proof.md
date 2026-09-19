---
rg: 2
id: leavitt-degree3-trivalent-omega-cycle-true-inverse-proof
kind: route
title: Replay every ordered trivalent Omega screen with symbolic inverses
target: leavitt-degree3-trivalent-omega-cycle-is-absent
requires:
  - leavitt-d4-true-inverse-screen-audit
artifacts:
  - research/artifacts/search-degree3-omega-four-cycle-true-inverse.py
---

The corrected verifier enumerates the fourteen length-seven exponent-three
sign paths with Reidemeister--Schreier stable-letter valences `(1,3,3)` and
all `7!` placements of `(r,e,a,c,b,d,p)` on each path.  For every placement
it solves the unary orbit, substitutes the resulting symbolic word into the
two ordered trivalent relators, and cyclically reduces their quotient in the
free product of the three coefficient copies.

Inverses are never obtained by transposing a Bergman chart.  Each inverse is
formed by reversing the symbolic generator word and changing exponents; only
then does the faithful chart evaluate it through the explicit `UNITS` and
`INVERSES` tables.  Before enumeration the verifier asserts, for every named
generator `x`, both `x*x^-1=1` and `x^-1*x=1`.

All fourteen shards completed normally.  Each owned one topology and printed

```text
layouts 5040 pivots 5040
hits 0
```

Thus the exhaustive total is `14*5,040=70,560` ordered layouts, with no
quotient cyclically conjugate to `[c,d]` or its inverse.  This is the exact
finite statement of the target claim.
