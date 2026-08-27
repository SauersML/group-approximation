---
rg: 2
id: random-private-matching-fixed-contour-proof
kind: route
title: Apply the permutation local lemma to the two occurrence metrics
target: random-private-matching-eliminates-fixed-multibasin-contours
requires: []
---

List every pair at distance at most `g` in each bounded-degree occurrence
graph.  Under a uniform perfect matching, forbid mapping any listed X pair
to any listed Z pair.  The permutation local lemma has event probability
`O(N^-2)`, dependency degree `O(N)`, and total charge `O(1)`, yielding both
existence and a positive probability independent of `N`.  Intersect this
event with the exponentially likely private-Weyl sampler event.  Any bounded
contour with at least two mixed edges contains two consecutive mixed edges
whose same-side endpoints violate the forbidden-pair condition.
