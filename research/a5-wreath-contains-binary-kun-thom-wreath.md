---
rg: 2
id: a5-wreath-contains-binary-kun-thom-wreath
kind: claim
title: The A5 generalized wreath contains the binary Kun-Thom wreath
distinct_from:
  wreath-not-sofic: that establishes nonsoficity of the binary wreath by Kun-Thom's theorem; this embeds that exact group into the A5-lamp variant.
  simple-lamp-hyperlinear-recovery-forces-action-sofic: that seeks a new hyperlinear-to-action implication using simple lamps; this shows the A5 variant is at least as hard to make hyperlinear as the original binary variant.
---

ESTABLISHED.  Fix an involution `t in A5`.  At every site `x in X`, use the
copy of the same subgroup `<t> ~= C2` inside the coordinate lamp `A5_x`.
Different site lamps commute, and the actor only permutes sites, so

```text
(directSum_X C2) semidirect G
  < (directSum_X A5) semidirect G.                        (AWB1)
```

For the pinned Kun--Thom action, the subgroup on the left is precisely the
nonsofic group `W` of `wreath-not-sofic`.  Hence the A5-lamp wreath is also
nonsofic, because subgroups of sofic groups are sofic.

Likewise, hyperlinearity of the A5-lamp wreath would imply hyperlinearity of
the binary Kun--Thom wreath by subgroup closure.  Thus changing to a finite
simple lamp creates additional intrinsic factor structure but does not make
the approximation problem formally easier; any gain must come specifically
from equivariant recovery of those factors.
