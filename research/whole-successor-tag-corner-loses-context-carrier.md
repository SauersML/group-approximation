---
rg: 2
id: whole-successor-tag-corner-loses-context-carrier
kind: claim
title: Returning the whole marked tag survivor does not retain the Fanizza context carrier
invalidates:
  - tagged-s3-survivor-via-central-successor-corner
distinct_from:
  free-occurrence-hnn-return-does-not-preserve-first-hit-prefix: that shows endpoint-only HNN transport need not enter the survivor prefix; here the prefix inclusion is correct, but the returned carrier has forgotten the context atom whose mass the BFE exit must lower-bound.
  tag-centralized-successor-corner: that correctly proves the analytic identity for the full marked carrier `C_nQ`; this shows why that identity is insufficient for the Fanizza decoder.
---

The identity

```text
u P_live u^*=C_(n+1)Q                                  (WSC1)
```

for `P_live=C_nQ-P_exit` does not establish the Fanizza recurrence.  The
exit lower bound is proportional to one forbidden/context carrier, or to the
native signal mass, not to the whole packet mark `Q`.

Fanizza's nonmember estimate controls its native signal `D`; it does not give
an exit lower bound proportional to the unrelated auxiliary packet mark
`Q`.  The local relations used by the route admit the following exact
falsification model: replace the predicate occurrence by a satisfying
assignment, amplify it, and extend the finite packet and tag tables.  Then
`C_nQ` can have arbitrary positive trace while every forbidden exit is zero.
Thus the displayed local premises cannot make any constant `eta>0` satisfy

```text
tau(P_exit)>=eta tau(C_nQ)                              (WSC2)
```

hold even at zero relator defect.

Consequently `(TSC5)` is a valid prefix/reducing-corner identity but cannot,
by itself, be substituted for `(BFE3)`.  The recurrent projection must retain
the specific Boolean context atom being amplified (or a separately proved
native-signal carrier).  The minimal local repair is
`context-atom-tag-bridge-installs-child-carrier`, which transports that atom
through the same endpoint-to-tag bridge.
