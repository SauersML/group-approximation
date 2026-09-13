---
rg: 2
id: grigorchuk-group-is-just-infinite-torsion-not-fp
kind: claim
title: The first Grigorchuk group is an infinite just-infinite 2-group that is not finitely presented
distinct_from:
  grigorchuk-elementary-groups-simple-kazhdan-iff-odd-char: that concerns elementary groups over the Steinberg algebra of the Grigorchuk groupoid; this records group-theoretic properties of the first Grigorchuk group itself.
---

**ESTABLISHED** (literature import, `grigorchuk-group-is-just-infinite-torsion-not-fp-citation`).

The first Grigorchuk group `G = < a, b, c, d >`, acting on the binary rooted
tree with `a` the root swap, `b = (a, c)`, `c = (a, d)`, `d = (1, b)`, is:

1. infinite, finitely generated, and torsion (every element has 2-power order);
2. just-infinite (every nontrivial normal subgroup has finite index);
3. not finitely presented.

Also, `b, c, d` fix both vertices of level one, so they lie in the level-one
stabilizer `St_G(1)`, which is a normal subgroup of index 2 not containing `a`.
