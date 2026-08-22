---
rg: 2
id: leavitt-d3-length9-compound-holonomy-is-absent-proof
kind: route
title: Replay both unary pivots against the seven-valent target
target: leavitt-d3-length9-compound-holonomy-is-absent
requires:
  - leavitt-minimal-cycle-is-hnn-holonomy
  - leavitt-degree3-trivalent-omega-cycle-is-absent
---

There are exactly nine exponent-three length-nine sign paths whose three
Reidemeister--Schreier relators have stable-letter valences `(1,1,7)` up to
orbit order.  A representative is

```text
(-,+,-,+,-,+,+,+,+).
```

This is the first topology with the correct abstract architecture after the
length-seven trivalent fence: one unary relation solves `z=t^3`, the second
can in principle encode the source holonomy `u^2=1`, and the remaining orbit
can carry the target `v^2=h`.

The artifact defines the compound gates in the faithful Bergman chart by

```text
u=ab,     u^(-1)=u,            v=cd,     v^(-1)=dc,
u^2=1,                            v^2=h.
```

For each of the nine topologies and all
`9!/(2!2!)=90,720` packet placements it performs both possible unary pivots.
It solves the chosen unary word exactly for `z`, substitutes into the other
two ordered relators, and requires

```text
other unary relator = 1,
cyclic reduction of target = h_i^(+-1)
```

for one coefficient copy `i`.  These are precisely the two consequences
needed by the sharp order-mismatch holonomy template; a hit would already be
a complete coefficient collapse, not merely an incidence match.

MSI job `16663449` completed all nine shards normally.  Each shard reports
`tested 90720` and `hits 0`, for the exact aggregate 816,480.  The packet has
full support: from `a,u` recover `b=au`, and from `c,v` recover `d=cv`, while
`r,e,p,a,c` are retained explicitly.
