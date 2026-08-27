---
rg: 2
id: rich-2to1-from-glue-lemma-modus-ponens
kind: route
title: Combine the affine orientation-glue lemma with the reduction that consumes it
target: rich-2to1-games-conjecture
requires: [affine-orientation-glue-lemma, glue-lemma-implies-rich-2to1-hardness]
---

Modus ponens, and deliberately nothing more.

The tempting shape for this region is a single-premise route
`affine-orientation-glue-lemma ==> rich-2to1-games-conjecture`.  That would
be false advertising.  The implication is not proved -- the source that
proposed the glue lemma states it as "if established, would give the
missing endgame" -- and in rg:2 writing a route asserts that the route is
valid.  A single-premise arrow here would tell every later reader that the
Unique Games Conjecture has been reduced to one analytic lemma, when what
is true is that it has been reduced to one analytic lemma *plus* an
unwritten reduction.

So the reduction step is carried by its own open claim,
`glue-lemma-implies-rich-2to1-hardness`, and this route just discharges the
two premises.  The effect on the frontier is the honest one: two holes, not
one, and the second is the cheaper of the two to attack.
